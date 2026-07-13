import json
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
PREPARED_DIR = REPO_ROOT / "data" / "veri_thoughts" / "prepared"

for tier in ["all", "syntax_pass", "verified"]:
    print(f"\n{'='*50}")
    print(f"Tier: {tier}")
    print(f"{'='*50}")
    for split in ["train", "validation", "test"]:
        path = PREPARED_DIR / tier / f"{split}.jsonl"
        modules = 0
        total_assert = 0
        total_assume = 0
        with open(path) as f:
            for line in f:
                row = json.loads(line)
                sva = row["sva"]
                total_assert += sva.count("assert property")
                total_assume += sva.count("assume property")
                modules += 1
        total = total_assert + total_assume
        print(f"  {split:<12} {modules:>5} modules | {total:>6} assertions ({total_assert} assert + {total_assume} assume)")
