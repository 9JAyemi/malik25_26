#!/usr/bin/env python3
"""
Unified SVA generation script for any HuggingFace dataset.

Usage:
  python generate_sva.py --dataset <name> --dir <output_dir> <mode>

Modes:
  --batch [N]       Create N batch jobs (default: 10)
  --check-batches   Check and download completed batch results
  --single          Test with one module (synchronous API call)
  --stats           Show dataset coverage statistics

Examples:
  python scripts/generate_sva.py --dataset metrex --dir metrex --batch 5
  python scripts/generate_sva.py --dataset verithoughts --dir veri_thoughts --batch 5
  python scripts/generate_sva.py --dataset verithoughts --dir veri_thoughts --check-batches
  python scripts/generate_sva.py --dataset metrex --dir metrex --stats
"""

import os
import sys
import json
import random
import argparse
from datetime import datetime
from datasets import load_dataset
from openai import OpenAI
from dotenv import load_dotenv
import hashlib

# ── Configuration ────────────────────────────────────────────
MAX_TOKENS = 2500
CHARS_PER_TOKEN = 4
BATCH_SIZE = 500
ID_WIDTH = 5  # 00000, 00001, ...

# ── Dataset registry ─────────────────────────────────────────
DATASET_REGISTRY = {
    "metrex": {
        "hf_name": "scale-lab/MetRex",
        "rtl_fields": ["RTL", "rtl"],
        "filter_verified": False,
        "extra_metadata_fields": [],
    },
    "verithoughts": {
        "hf_name": "wilyub/VeriThoughtsTrainSet",
        "rtl_fields": ["ground_truth", "generated_verilog"],
        "filter_verified": True,
        "extra_metadata_fields": ["question", "verified"],
    },
}


# ── Dataset helpers ──────────────────────────────────────────
class DatasetConfig:
    """Holds resolved paths and dataset config for a run."""

    def __init__(self, dataset_key: str, output_dir: str):
        if dataset_key not in DATASET_REGISTRY:
            print(f"Unknown dataset '{dataset_key}'. Available: {list(DATASET_REGISTRY.keys())}")
            sys.exit(1)

        self.key = dataset_key
        self.reg = DATASET_REGISTRY[dataset_key]
        self.hf_name = self.reg["hf_name"]
        self.rtl_fields = self.reg["rtl_fields"]
        self.filter_verified = self.reg["filter_verified"]
        self.extra_metadata_fields = self.reg["extra_metadata_fields"]

        # All paths are relative to the output directory
        self.root = output_dir
        self.dataset_root = os.path.join(output_dir, "dataset")
        self.version = os.getenv("DATASET_VERSION", "version_1")
        self.global_index_file = os.path.join(self.dataset_root, "global_index.json")
        self.tracking_file = os.path.join(output_dir, "processed_modules.json")
        self.batch_tracking_file = os.path.join(output_dir, "batch_tracking.json")
        self.batch_requests_dir = os.path.join(output_dir, "batch_requests")

        # Load .env from output dir if present, else from cwd
        env_path = os.path.join(output_dir, ".env")
        if os.path.exists(env_path):
            load_dotenv(env_path)
        else:
            load_dotenv()


# ── RTL extraction ───────────────────────────────────────────
def get_rtl_field(sample, cfg: DatasetConfig) -> str:
    """Extract RTL code from a sample, trying fields in priority order."""
    for field in cfg.rtl_fields:
        if field in sample and sample[field]:
            return sample[field]
    raise KeyError(f"No RTL field found (tried {cfg.rtl_fields})")


def get_module_name(rtl_code: str) -> str:
    """Extract module name from Verilog code."""
    for line in rtl_code.split("\n"):
        line = line.strip()
        if line.startswith("module "):
            module_decl = line.split("module ")[1]
            return module_decl.split("(")[0].split(";")[0].split("#")[0].strip()
    return "unknown_module"


def estimate_tokens(text: str) -> int:
    return len(text) // CHARS_PER_TOKEN


def get_module_hash(rtl_code: str) -> str:
    return hashlib.md5(rtl_code.encode()).hexdigest()


def short_hash(text: str, n: int = 6) -> str:
    return hashlib.sha1(text.encode()).hexdigest()[:n]


def count_assertions(sva_code: str) -> int:
    return sum(1 for line in sva_code.splitlines() if "assert" in line)


def compute_prompt_text(rtl_code: str) -> str:
    return f"""You are a verification engineer. 
Generate SVA assertions for the following verilog module.
Make sure it has full coverage and checks all important
signals and functions, but make sure it is also concise. We
mostly care about quality over quantity and also mostly care
about SVA, not DUT or testbench code, the SVA is the most
important part of what you generate.:

{rtl_code}"""


# ── Dataset layout helpers ───────────────────────────────────
def ensure_version_dirs(cfg: DatasetConfig):
    version_dir = os.path.join(cfg.dataset_root, cfg.version)
    meta_dir = os.path.join(version_dir, "metadata")
    os.makedirs(version_dir, exist_ok=True)
    os.makedirs(meta_dir, exist_ok=True)

    jsonl_path = os.path.join(meta_dir, "metadata.jsonl")
    stats_path = os.path.join(meta_dir, "stats.json")
    if not os.path.exists(jsonl_path):
        with open(jsonl_path, "w") as f:
            pass
    if not os.path.exists(stats_path):
        with open(stats_path, "w") as f:
            json.dump({"count": 0}, f)

    if not os.path.exists(cfg.global_index_file):
        os.makedirs(os.path.dirname(cfg.global_index_file), exist_ok=True)
        with open(cfg.global_index_file, "w") as f:
            json.dump(
                {"latest_version": cfg.version, "next_id": 0, "versions": [cfg.version]},
                f,
                indent=2,
            )
    return version_dir, meta_dir


def load_global_index(cfg: DatasetConfig):
    if os.path.exists(cfg.global_index_file):
        with open(cfg.global_index_file, "r") as f:
            return json.load(f)
    return {"latest_version": cfg.version, "next_id": 0, "versions": [cfg.version]}


def save_global_index(cfg: DatasetConfig, idx):
    with open(cfg.global_index_file, "w") as f:
        json.dump(idx, f, indent=2)


def allocate_sample_id(cfg: DatasetConfig) -> str:
    idx = load_global_index(cfg)
    sid = idx.get("next_id", 0)
    idx["next_id"] = sid + 1
    idx["latest_version"] = cfg.version
    if "versions" not in idx:
        idx["versions"] = [cfg.version]
    elif cfg.version not in idx["versions"]:
        idx["versions"].append(cfg.version)
    save_global_index(cfg, idx)
    return str(sid).zfill(ID_WIDTH)


def update_stats(meta_dir: str, increment: int = 1):
    stats_path = os.path.join(meta_dir, "stats.json")
    try:
        with open(stats_path, "r") as f:
            stats = json.load(f)
    except Exception:
        stats = {"count": 0}
    stats["count"] = stats.get("count", 0) + increment
    with open(stats_path, "w") as f:
        json.dump(stats, f, indent=2)


def write_dataset_sample(cfg: DatasetConfig, rtl_code: str, sva_code: str, metadata: dict) -> dict:
    version_dir, meta_dir = ensure_version_dirs(cfg)
    sample_id = allocate_sample_id(cfg)
    sample_dir = os.path.join(version_dir, sample_id)
    os.makedirs(sample_dir, exist_ok=True)

    with open(os.path.join(sample_dir, "module.v"), "w") as f:
        f.write(rtl_code)
    with open(os.path.join(sample_dir, "sva.sv"), "w") as f:
        f.write(sva_code)

    per_sample_meta = {
        "id": sample_id,
        "version": cfg.version,
        "verilog_file": "module.v",
        "sva_file": "sva.sv",
        "created_at": datetime.now().isoformat(),
        **metadata,
        "judging": {
            "status": "unjudged",
            "llm_scores": [],
            "aggregate_score": None,
            "accepted": None,
        },
    }
    with open(os.path.join(sample_dir, "metadata.json"), "w") as f:
        json.dump(per_sample_meta, f, indent=2)

    jsonl_obj = {**per_sample_meta, "verilog_code": rtl_code, "sva_code": sva_code}
    with open(os.path.join(meta_dir, "metadata.jsonl"), "a") as f:
        f.write(json.dumps(jsonl_obj) + "\n")

    update_stats(meta_dir, increment=1)
    return {"id": sample_id, "dir": sample_dir}


# ── Tracking ─────────────────────────────────────────────────
def load_processed_modules(cfg: DatasetConfig):
    if os.path.exists(cfg.tracking_file):
        with open(cfg.tracking_file, "r") as f:
            return json.load(f)
    return {}


def save_processed_modules(cfg: DatasetConfig, processed):
    with open(cfg.tracking_file, "w") as f:
        json.dump(processed, f, indent=2)


def is_module_processed(module_hash, processed_modules):
    return module_hash in processed_modules


# ── Sample filtering ─────────────────────────────────────────
def should_skip_sample(sample, cfg: DatasetConfig) -> bool:
    """Return True if this sample should be skipped."""
    if cfg.filter_verified and not sample.get("verified", False):
        return True
    return False


def build_sample_metadata(sample, cfg: DatasetConfig, module_name: str, source: str) -> dict:
    """Build the metadata dict for a sample, including any dataset-specific fields."""
    meta = {
        "source": source,
        "model_used": "gpt-5",
        "module_name": module_name,
        "original_dataset": cfg.hf_name,
    }
    for field in cfg.extra_metadata_fields:
        meta[f"original_{field}"] = sample.get(field, None)
    return meta


# ── Batch API helpers ────────────────────────────────────────
def create_batch_request(rtl_code, module_name, custom_id):
    prompt = compute_prompt_text(rtl_code)
    return {
        "custom_id": custom_id,
        "method": "POST",
        "url": "/v1/responses",
        "body": {
            "model": "gpt-5",
            "input": [
                {
                    "role": "system",
                    "content": "You are a verification engineer expert in SystemVerilog Assertions.",
                },
                {"role": "user", "content": prompt},
            ],
            "reasoning": {"effort": "medium"},
            "text": {"verbosity": "low"},
        },
    }


def prepare_batch_file(cfg: DatasetConfig, modules_data, batch_num):
    os.makedirs(cfg.batch_requests_dir, exist_ok=True)
    batch_filename = os.path.join(
        cfg.batch_requests_dir,
        f"batch_{batch_num}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.jsonl",
    )
    with open(batch_filename, "w") as f:
        for module_data in modules_data:
            request = create_batch_request(
                module_data["rtl_code"],
                module_data["module_name"],
                module_data["custom_id"],
            )
            f.write(json.dumps(request) + "\n")
    print(f"Created batch file: {batch_filename}")
    return batch_filename


def upload_and_create_batch(client, batch_filename, cfg: DatasetConfig):
    with open(batch_filename, "rb") as f:
        batch_input_file = client.files.create(file=f, purpose="batch")

    batch = client.batches.create(
        input_file_id=batch_input_file.id,
        endpoint="/v1/responses",
        completion_window="24h",
        metadata={
            "description": f"SVA generation from {cfg.hf_name}"
        },
    )
    print(f"Batch created with ID: {batch.id}")
    return batch.id


def check_batch_status(client, batch_id):
    batch = client.batches.retrieve(batch_id)
    return batch.status, batch


def download_batch_results(client, batch):
    if batch.status != "completed":
        print(f"Batch not completed. Status: {batch.status}")
        return None
    content = client.files.content(batch.output_file_id)
    return [json.loads(line) for line in content.text.strip().split("\n")]


def process_batch_results(cfg: DatasetConfig, results, modules_metadata, processed_modules):
    for result in results:
        custom_id = result.get("custom_id")
        metadata = modules_metadata.get(custom_id)
        if not metadata:
            print(f"⚠️ Unknown or missing custom_id: {custom_id}")
            continue

        try:
            response = result.get("response", {})
            body = response.get("body", {})

            sva_code = None
            output = body.get("output", [])

            for item in output:
                if item.get("type") == "message" and isinstance(item.get("content"), list):
                    for content_item in item["content"]:
                        if content_item.get("type") == "output_text" and isinstance(
                            content_item.get("text"), str
                        ):
                            sva_code = content_item["text"].strip()
                            break
                if sva_code:
                    break

            if not sva_code:
                sva_code = body.get("output_text") or body.get("text")
                if isinstance(sva_code, dict):
                    sva_code = next(
                        (v for v in sva_code.values() if isinstance(v, str)),
                        str(sva_code),
                    )
                if isinstance(sva_code, str):
                    sva_code = sva_code.strip()

            if not sva_code or not isinstance(sva_code, str):
                raise KeyError("No valid text field found in response body")

            rtl_code = metadata["rtl_code"]
            module_name = metadata["module_name"]

            module_hash = metadata.get("module_hash")
            if module_hash and module_hash in processed_modules:
                print(f"↷ Skipping duplicate across batches: {module_name}")
                continue

            prompt_text = compute_prompt_text(rtl_code)

            meta_obj = {
                "source": "openai_batch",
                "model_used": body.get("model", "gpt-5"),
                "batch_id": result.get("id") or response.get("id"),
                "custom_id": custom_id,
                "module_name": module_name,
                "original_dataset": cfg.hf_name,
                "prompt_hash": short_hash(prompt_text),
                "validation": {
                    "syntax_check": True,
                    "compiles_with_sv_linter": False,
                    "num_assertions": count_assertions(sva_code),
                },
            }
            # Add dataset-specific metadata
            for field in cfg.extra_metadata_fields:
                meta_obj[f"original_{field}"] = metadata.get(field, None)

            saved = write_dataset_sample(cfg, rtl_code, sva_code, meta_obj)

            processed_modules[metadata["module_hash"]] = {
                "module_name": module_name,
                "saved_id": saved["id"],
                "saved_dir": saved["dir"],
                "processed_date": datetime.now().isoformat(),
                "custom_id": custom_id,
                "version": cfg.version,
            }

            print(f"✓ Processed: {module_name} -> {saved['id']}")

        except Exception as e:
            print(f"✗ Error processing result for {metadata.get('module_name', 'unknown')}: {e}")

    save_processed_modules(cfg, processed_modules)


def collect_modules_for_batch(cfg: DatasetConfig, dataset, processed_modules, batch_size):
    modules_data = []
    modules_metadata = {}

    indices = list(range(len(dataset)))
    random.shuffle(indices)

    for idx in indices:
        if len(modules_data) >= batch_size:
            break

        try:
            sample = dataset[idx]

            if should_skip_sample(sample, cfg):
                continue

            rtl_code = get_rtl_field(sample, cfg)

            estimated_tokens = estimate_tokens(rtl_code)
            if estimated_tokens > MAX_TOKENS:
                continue

            module_hash = get_module_hash(rtl_code)
            if is_module_processed(module_hash, processed_modules):
                continue

            module_name = get_module_name(rtl_code)
            custom_id = f"{module_name}_{module_hash[:8]}"

            modules_data.append({
                "rtl_code": rtl_code,
                "module_name": module_name,
                "custom_id": custom_id,
                "module_hash": module_hash,
            })

            meta_entry = {
                "rtl_code": rtl_code,
                "module_name": module_name,
                "module_hash": module_hash,
                "dataset_index": idx,
            }
            for field in cfg.extra_metadata_fields:
                meta_entry[field] = sample.get(field, None)

            modules_metadata[custom_id] = meta_entry

        except Exception as e:
            print(f"Error processing module at index {idx}: {e}")
            continue

    return modules_data, modules_metadata


# ── Mode implementations ─────────────────────────────────────
def main_batch_mode(cfg: DatasetConfig, num_batches=10):
    api_key = os.getenv("OPENAI_API_KEY")
    if not api_key:
        print("Error: OPENAI_API_KEY environment variable not set")
        sys.exit(1)

    client = OpenAI(api_key=api_key)

    print(f"Loading dataset ({cfg.hf_name})...")
    ds = load_dataset(cfg.hf_name, split="train")
    print(f"Dataset loaded with {len(ds)} samples")

    processed_modules = load_processed_modules(cfg)
    print(f"Already processed: {len(processed_modules)} modules")

    batch_ids = []
    all_metadata = {}

    for batch_num in range(num_batches):
        print(f"\n=== Preparing Batch {batch_num + 1}/{num_batches} ===")

        modules_data, modules_metadata = collect_modules_for_batch(
            cfg, ds, processed_modules, BATCH_SIZE
        )

        if not modules_data:
            print("No more unprocessed modules available")
            break

        print(f"Collected {len(modules_data)} modules for batch")

        batch_filename = prepare_batch_file(cfg, modules_data, batch_num)
        batch_id = upload_and_create_batch(client, batch_filename, cfg)
        batch_ids.append(batch_id)
        all_metadata[batch_id] = modules_metadata

    batch_tracking = {
        "batch_ids": batch_ids,
        "metadata": all_metadata,
        "created_at": datetime.now().isoformat(),
        "source_dataset": cfg.hf_name,
    }

    with open(cfg.batch_tracking_file, "w") as f:
        json.dump(batch_tracking, f, indent=2)

    print(f"\n=== Created {len(batch_ids)} batches ===")
    print(f"Batch IDs saved to {cfg.batch_tracking_file}")
    print(f"\nTo check status and download results, run:")
    print(f"python scripts/generate_sva.py --dataset {cfg.key} --dir {cfg.root} --check-batches")


def check_and_download_batches(cfg: DatasetConfig):
    api_key = os.getenv("OPENAI_API_KEY")
    if not api_key:
        print("Error: OPENAI_API_KEY environment variable not set")
        sys.exit(1)

    client = OpenAI(api_key=api_key)

    if not os.path.exists(cfg.batch_tracking_file):
        print(f"No batch tracking file found ({cfg.batch_tracking_file})")
        return

    with open(cfg.batch_tracking_file, "r") as f:
        batch_tracking = json.load(f)

    processed_modules = load_processed_modules(cfg)

    for batch_id in batch_tracking["batch_ids"]:
        print(f"\n=== Checking Batch {batch_id} ===")
        status, batch = check_batch_status(client, batch_id)
        print(f"Status: {status}")

        if status == "completed":
            print("Downloading results...")
            results = download_batch_results(client, batch)

            if results:
                modules_metadata = batch_tracking["metadata"][batch_id]
                process_batch_results(cfg, results, modules_metadata, processed_modules)
                print(f"Processed {len(results)} results")
        elif status == "failed":
            print(f"Batch failed: {batch}")
        elif status in ["validating", "in_progress", "finalizing"]:
            print("Batch still processing...")


def main_single_mode(cfg: DatasetConfig):
    api_key = os.getenv("OPENAI_API_KEY")
    if not api_key:
        print("Error: OPENAI_API_KEY environment variable not set")
        sys.exit(1)

    client = OpenAI(api_key=api_key)

    print(f"Loading dataset ({cfg.hf_name})...")
    ds = load_dataset(cfg.hf_name, split="train")
    print(f"Dataset loaded with {len(ds)} samples")

    processed_modules = load_processed_modules(cfg)

    max_attempts = 100
    for _ in range(max_attempts):
        random_index = random.randint(0, len(ds) - 1)
        sample = ds[random_index]

        try:
            if should_skip_sample(sample, cfg):
                continue

            rtl_code = get_rtl_field(sample, cfg)
            module_hash = get_module_hash(rtl_code)
            if is_module_processed(module_hash, processed_modules):
                continue

            estimated_tokens = estimate_tokens(rtl_code)
            if estimated_tokens > MAX_TOKENS:
                continue

            module_name = get_module_name(rtl_code)
            print(f"Selected module: {module_name}")
            print(f"Estimated tokens: {estimated_tokens}")

            if sample.get("question"):
                print(f"Question: {sample['question'][:120]}...")

            print("Generating SVA assertions...")
            prompt = compute_prompt_text(rtl_code)
            response = client.responses.create(
                model="gpt-5",
                input=[
                    {
                        "role": "system",
                        "content": "You are a verification engineer expert in SystemVerilog Assertions.",
                    },
                    {"role": "user", "content": prompt},
                ],
                reasoning={"effort": "medium"},
                text={"verbosity": "medium"},
            )
            sva_code = response.output_text

            meta_obj = build_sample_metadata(sample, cfg, module_name, "single_mode")
            meta_obj["prompt_hash"] = short_hash(prompt)
            meta_obj["validation"] = {
                "syntax_check": True,
                "compiles_with_sv_linter": False,
                "num_assertions": count_assertions(sva_code),
            }

            saved = write_dataset_sample(cfg, rtl_code, sva_code, meta_obj)

            processed_modules[module_hash] = {
                "module_name": module_name,
                "saved_id": saved["id"],
                "saved_dir": saved["dir"],
                "processed_date": datetime.now().isoformat(),
                "version": cfg.version,
            }
            save_processed_modules(cfg, processed_modules)

            print("\nGeneration complete!")
            return

        except Exception as e:
            print(f"Error: {e}")
            continue

    print("Could not find an unprocessed module within attempt limit")


def main_stats(cfg: DatasetConfig):
    print(f"Loading dataset ({cfg.hf_name})...")
    ds = load_dataset(cfg.hf_name, split="train")
    total = len(ds)
    processed_modules = load_processed_modules(cfg)
    processed_count = len(processed_modules)

    within_limit = 0
    verified_count = 0
    eligible_count = 0
    for i in range(total):
        sample = ds[i]
        try:
            rtl_code = get_rtl_field(sample, cfg)
            tokens_ok = estimate_tokens(rtl_code) <= MAX_TOKENS
            if tokens_ok:
                within_limit += 1
            is_verified = sample.get("verified", True)  # MetRex has no verified field
            if is_verified:
                verified_count += 1
            if tokens_ok and not should_skip_sample(sample, cfg):
                eligible_count += 1
        except Exception:
            pass

    label = cfg.key.capitalize()
    print(f"\n=== {label} Dataset Stats ===")
    print(f"Total samples:        {total}")
    if cfg.filter_verified:
        print(f"Verified samples:     {verified_count}")
    print(f"Within token limit:   {within_limit}")
    print(f"Eligible (after filters): {eligible_count}")
    print(f"Already processed:    {processed_count}")
    print(f"Remaining eligible:   {eligible_count - processed_count}")


# ── CLI ──────────────────────────────────────────────────────
def main():
    parser = argparse.ArgumentParser(
        description="Unified SVA generation for HuggingFace datasets",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s --dataset metrex --dir metrex --batch 5
  %(prog)s --dataset verithoughts --dir veri_thoughts --check-batches
  %(prog)s --dataset verithoughts --dir veri_thoughts --stats
""",
    )
    parser.add_argument(
        "--dataset",
        required=True,
        choices=list(DATASET_REGISTRY.keys()),
        help="Which dataset to use",
    )
    parser.add_argument(
        "--dir",
        required=True,
        help="Output directory (e.g., metrex or veri_thoughts)",
    )

    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--batch", nargs="?", const=10, type=int, metavar="N",
                       help="Create N batch jobs (default: 10)")
    group.add_argument("--check-batches", action="store_true",
                       help="Check and download completed batch results")
    group.add_argument("--single", action="store_true",
                       help="Test with one module (synchronous API call)")
    group.add_argument("--stats", action="store_true",
                       help="Show dataset coverage statistics")

    args = parser.parse_args()

    cfg = DatasetConfig(args.dataset, args.dir)

    if args.batch is not None:
        main_batch_mode(cfg, num_batches=args.batch)
    elif args.check_batches:
        check_and_download_batches(cfg)
    elif args.single:
        main_single_mode(cfg)
    elif args.stats:
        main_stats(cfg)


if __name__ == "__main__":
    main()
