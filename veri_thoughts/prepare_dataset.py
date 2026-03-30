"""
Data Preparation Script for SVA-RTL Dataset
============================================
Reads raw dataset, filters into 3 ablation tiers, splits 80/10/10 by module ID,
and uploads to HuggingFace as a single dataset with 3 configs.

Tiers:
  - all:         Every sample, unfiltered (raw rtl.v + sva.sv)
  - syntax_pass: Only samples that compile (not in failing_ids.txt), full sva.sv
  - verified:    Only samples that compile AND have ≥1 passing assertion,
                 sva.sv rebuilt to contain only verified assertions

Usage:
  python prepare_dataset.py                          # dry run, no upload
  python prepare_dataset.py --push                   # upload to HuggingFace
  python prepare_dataset.py --push --repo aarushgoradia/malik25_26
"""

import argparse
import csv
import os
import re
import json
import random
from pathlib import Path
from collections import defaultdict

# ============================================================
# CONFIG — adjust paths if your layout differs
# ============================================================
PROJECT_ROOT = Path(__file__).resolve().parent
DATASET_DIR = PROJECT_ROOT / "dataset"
VERSION_1_DIR = DATASET_DIR / "version_1"
VERSION_2_DIR = DATASET_DIR / "version_2"
FAILING_IDS_FILE = PROJECT_ROOT / "failing_ids.txt"
PASSING_CSV = DATASET_DIR / "dataset_stats" / "version_2" / "passing_assertions.csv"
OUTPUT_DIR = PROJECT_ROOT / "dataset_cleaned"

HF_REPO = "aarushgoradia/malik25_26"
SPLIT_SEED = 42
TRAIN_RATIO = 0.80
VAL_RATIO = 0.10
TEST_RATIO = 0.10


def load_failing_ids(path: Path) -> set:
    """Load IDs that fail syntax check."""
    ids = set()
    with open(path, "r") as f:
        for line in f:
            line = line.strip()
            if line:
                ids.add(line)
    print(f"Loaded {len(ids)} failing IDs from {path}")
    return ids


def load_passing_assertions(path: Path) -> dict:
    """Load passing assertions CSV. Returns {id: [assertion_text, ...]}."""
    passing = defaultdict(list)
    with open(path, "r", newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            sample_id = row["id"].strip()
            assertion_text = row["passing_property"].strip()
            # Remove surrounding quotes if present
            if assertion_text.startswith('"') and assertion_text.endswith('"'):
                assertion_text = assertion_text[1:-1]
            passing[sample_id].append(assertion_text)
    print(f"Loaded passing assertions for {len(passing)} samples from {path}")
    return passing


def load_all_samples() -> dict:
    """Load all raw samples from version_1 and version_2.
    Returns {id: {"rtl": str, "sva": str, "id": str}}
    """
    samples = {}

    for version_dir in [VERSION_1_DIR, VERSION_2_DIR]:
        if not version_dir.exists():
            print(f"WARNING: {version_dir} does not exist, skipping")
            continue
        for sample_dir in sorted(version_dir.iterdir()):
            if not sample_dir.is_dir():
                continue
            sample_id = sample_dir.name
            rtl_path = sample_dir / "module.v"
            sva_path = sample_dir / "sva.sv"

            if not rtl_path.exists() or not sva_path.exists():
                print(f"WARNING: Missing module.v or sva.sv in {sample_dir}, skipping")
                continue

            rtl = rtl_path.read_text(encoding="utf-8", errors="replace")
            sva = sva_path.read_text(encoding="utf-8", errors="replace")
            samples[sample_id] = {"id": sample_id, "rtl": rtl, "sva": sva}

    print(f"Loaded {len(samples)} total samples")
    return samples


def rebuild_sva_with_passing_only(original_sva: str, passing_assertions: list) -> str | None:
    """Rebuild an SVA file keeping only passing assertions.

    Strategy: find each passing assertion in the original text, along with
    the comment line directly above it. Keep the module wrapper and only
    the matched assertions.
    """
    # Extract the module header (everything up to and including the port list)
    # and the endmodule line
    header_match = re.search(
        r"^(module\s+\w+\s*\(.*?\)\s*;)",
        original_sva,
        re.DOTALL | re.MULTILINE,
    )
    if not header_match:
        # Try simpler pattern without ports
        header_match = re.search(
            r"^(module\s+\w+\s*;)",
            original_sva,
            re.DOTALL | re.MULTILINE,
        )

    if not header_match:
        return None

    header = header_match.group(1)

    # Find each passing assertion in the original SVA and grab its comment
    kept_blocks = []
    for assertion in passing_assertions:
        assertion_stripped = assertion.strip()
        # Find the assertion in the original SVA
        idx = original_sva.find(assertion_stripped)
        if idx == -1:
            # Try with normalized whitespace
            normalized = " ".join(assertion_stripped.split())
            normalized_sva = " ".join(original_sva.split())
            if normalized in normalized_sva:
                # Found with normalized whitespace — use original assertion text
                kept_blocks.append(assertion_stripped)
            else:
                print(f"    WARNING: Could not find assertion in SVA, including anyway")
                kept_blocks.append(assertion_stripped)
            continue

        # Look for a comment line directly above the assertion
        preceding = original_sva[:idx]
        preceding_lines = preceding.rstrip().split("\n")
        comment_line = ""
        if preceding_lines:
            last_line = preceding_lines[-1].strip()
            if last_line.startswith("//"):
                comment_line = "    " + last_line + "\n"

        kept_blocks.append(comment_line + assertion_stripped)

    if not kept_blocks:
        return None

    # Reconstruct the file
    rebuilt = header + "\n\n"
    rebuilt += "\n\n".join(kept_blocks)
    rebuilt += "\n\nendmodule\n"

    return rebuilt


def split_ids(all_ids: list, seed: int) -> tuple:
    """Split IDs into train/val/test with fixed seed."""
    rng = random.Random(seed)
    ids = sorted(all_ids)  # sort first for determinism
    rng.shuffle(ids)

    n = len(ids)
    train_end = int(n * TRAIN_RATIO)
    val_end = train_end + int(n * VAL_RATIO)

    train_ids = set(ids[:train_end])
    val_ids = set(ids[train_end:val_end])
    test_ids = set(ids[val_end:])

    return train_ids, val_ids, test_ids


def save_split(samples: list, output_path: Path):
    """Save a list of samples as JSONL."""
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, "w", encoding="utf-8") as f:
        for sample in samples:
            f.write(json.dumps(sample, ensure_ascii=False) + "\n")
    print(f"  Saved {len(samples)} samples to {output_path}")


def build_and_save_tier(
    tier_name: str,
    eligible_samples: dict,
    train_ids: set,
    val_ids: set,
    test_ids: set,
):
    """Filter samples by split and save as JSONL files."""
    tier_dir = OUTPUT_DIR / tier_name

    train_samples = []
    val_samples = []
    test_samples = []

    for sid, sample in sorted(eligible_samples.items()):
        if sid in train_ids:
            train_samples.append(sample)
        elif sid in val_ids:
            val_samples.append(sample)
        elif sid in test_ids:
            test_samples.append(sample)

    print(f"\n[{tier_name}] Total: {len(eligible_samples)} | "
          f"Train: {len(train_samples)} | Val: {len(val_samples)} | Test: {len(test_samples)}")

    save_split(train_samples, tier_dir / "train.jsonl")
    save_split(val_samples, tier_dir / "validation.jsonl")
    save_split(test_samples, tier_dir / "test.jsonl")


def push_to_hub(repo_id: str):
    """Upload all 3 configs to HuggingFace."""
    from datasets import Dataset, DatasetDict

    for tier in ["all", "syntax_pass", "verified"]:
        tier_dir = OUTPUT_DIR / tier
        splits = {}
        for split_name in ["train", "validation", "test"]:
            path = tier_dir / f"{split_name}.jsonl"
            if path.exists():
                splits[split_name] = Dataset.from_json(str(path))

        dd = DatasetDict(splits)
        config_repo = f"{repo_id}"
        print(f"\nPushing [{tier}] to {config_repo} (config={tier})...")
        dd.push_to_hub(config_repo, config_name=tier)
        print(f"  Done!")


def main():
    parser = argparse.ArgumentParser(description="Prepare SVA-RTL dataset for fine-tuning")
    parser.add_argument("--push", action="store_true", help="Push to HuggingFace Hub")
    parser.add_argument("--repo", default=HF_REPO, help="HuggingFace repo (default: %(default)s)")
    args = parser.parse_args()

    print("=" * 60)
    print("SVA-RTL Dataset Preparation")
    print("=" * 60)

    # 1. Load everything
    print("\n--- Loading data ---")
    all_samples = load_all_samples()
    failing_ids = load_failing_ids(FAILING_IDS_FILE)

    passing_assertions = defaultdict(list)
    if PASSING_CSV.exists():
        pa = load_passing_assertions(PASSING_CSV)
        for k, v in pa.items():
            passing_assertions[k].extend(v)
    else:
        print(f"WARNING: {PASSING_CSV} not found")

    # 2. Compute the global split (same IDs for all tiers)
    print("\n--- Computing 80/10/10 split ---")
    all_ids = list(all_samples.keys())
    train_ids, val_ids, test_ids = split_ids(all_ids, SPLIT_SEED)
    print(f"Total IDs: {len(all_ids)} | Train: {len(train_ids)} | Val: {len(val_ids)} | Test: {len(test_ids)}")

    # 3. Build Tier 1: all (unfiltered)
    print("\n--- Building tier: all ---")
    tier_all = dict(all_samples)
    build_and_save_tier("all", tier_all, train_ids, val_ids, test_ids)

    # 4. Build Tier 2: syntax_pass (exclude failing IDs)
    print("\n--- Building tier: syntax_pass ---")
    tier_syntax = {
        sid: sample for sid, sample in all_samples.items()
        if sid not in failing_ids
    }
    print(f"Excluded {len(all_samples) - len(tier_syntax)} samples that fail syntax")
    build_and_save_tier("syntax_pass", tier_syntax, train_ids, val_ids, test_ids)

    # 5. Build Tier 3: verified (syntax_pass + only passing assertions)
    print("\n--- Building tier: verified ---")
    tier_verified = {}
    skipped_no_passing = 0
    skipped_rebuild_fail = 0

    for sid, sample in tier_syntax.items():
        if sid not in passing_assertions or len(passing_assertions[sid]) == 0:
            skipped_no_passing += 1
            continue

        rebuilt_sva = rebuild_sva_with_passing_only(
            sample["sva"], passing_assertions[sid]
        )
        if rebuilt_sva is None:
            skipped_rebuild_fail += 1
            continue

        tier_verified[sid] = {
            "id": sid,
            "rtl": sample["rtl"],
            "sva": rebuilt_sva,
        }

    print(f"Skipped {skipped_no_passing} samples with 0 passing assertions")
    print(f"Skipped {skipped_rebuild_fail} samples where SVA rebuild failed")
    build_and_save_tier("verified", tier_verified, train_ids, val_ids, test_ids)

    # 6. Summary
    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print(f"{'Tier':<15} {'Total':>8} {'Train':>8} {'Val':>8} {'Test':>8}")
    print("-" * 50)
    for tier_name, tier_data in [("all", tier_all), ("syntax_pass", tier_syntax), ("verified", tier_verified)]:
        t = len([s for s in tier_data if s in train_ids])
        v = len([s for s in tier_data if s in val_ids])
        te = len([s for s in tier_data if s in test_ids])
        print(f"{tier_name:<15} {len(tier_data):>8} {t:>8} {v:>8} {te:>8}")

    print(f"\nCleaned data saved to: {OUTPUT_DIR}/")

    # 7. Push to HuggingFace
    if args.push:
        push_to_hub(args.repo)
    else:
        print(f"\nDry run — to upload, run: python {Path(__file__).name} --push")


if __name__ == "__main__":
    main()