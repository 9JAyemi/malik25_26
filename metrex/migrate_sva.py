import os
import json
from datetime import datetime

DATASET_ROOT = "dataset"
CURRENT_VERSION = os.getenv("DATASET_VERSION", "version_1")
ID_WIDTH = 5  # 00000, 00001, ...
GLOBAL_INDEX_FILE = os.path.join(DATASET_ROOT, "global_index.json")
SOURCE_DIR = "generated_modules"

def ensure_version_dirs():
    version_dir = os.path.join(DATASET_ROOT, CURRENT_VERSION)
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
    if not os.path.exists(GLOBAL_INDEX_FILE):
        with open(GLOBAL_INDEX_FILE, "w") as f:
            json.dump({"latest_version": CURRENT_VERSION, "next_id": 0, "versions": [CURRENT_VERSION]}, f, indent=2)
    return version_dir, meta_dir

def load_global_index():
    if os.path.exists(GLOBAL_INDEX_FILE):
        with open(GLOBAL_INDEX_FILE, "r") as f:
            return json.load(f)
    return {"latest_version": CURRENT_VERSION, "next_id": 0, "versions": [CURRENT_VERSION]}

def save_global_index(idx):
    with open(GLOBAL_INDEX_FILE, "w") as f:
        json.dump(idx, f, indent=2)

def allocate_sample_id():
    idx = load_global_index()
    sid = idx.get("next_id", 0)
    idx["next_id"] = sid + 1
    idx["latest_version"] = CURRENT_VERSION
    if "versions" not in idx:
        idx["versions"] = [CURRENT_VERSION]
    elif CURRENT_VERSION not in idx["versions"]:
        idx["versions"].append(CURRENT_VERSION)
    save_global_index(idx)
    return str(sid).zfill(ID_WIDTH)

def count_assertions(sva_code: str) -> int:
    return sum(1 for line in sva_code.splitlines() if "assert" in line)

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

def main():
    if not os.path.isdir(SOURCE_DIR):
        print(f"No '{SOURCE_DIR}' directory found. Nothing to migrate.")
        return

    version_dir, meta_dir = ensure_version_dirs()

    files = os.listdir(SOURCE_DIR)
    bases = {}
    for fn in files:
        root, ext = os.path.splitext(fn)
        if ext.lower() in [".v", ".sv"]:
            bases.setdefault(root, set()).add(ext.lower())

    migrated = 0
    for base, exts in sorted(bases.items()):
        if ".v" not in exts or ".sv" not in exts:
            continue
        v_path = os.path.join(SOURCE_DIR, base + ".v")
        sv_path = os.path.join(SOURCE_DIR, base + ".sv")
        try:
            with open(v_path, "r") as f:
                rtl = f.read()
            with open(sv_path, "r") as f:
                sva = f.read()
        except Exception as e:
            print(f"Skipping {base}: {e}")
            continue

        sample_id = allocate_sample_id()
        sample_dir = os.path.join(version_dir, sample_id)
        os.makedirs(sample_dir, exist_ok=True)

        with open(os.path.join(sample_dir, "module.v"), "w") as f:
            f.write(rtl)
        with open(os.path.join(sample_dir, "properties.sv"), "w") as f:
            f.write(sva)

        meta = {
            "id": sample_id,
            "version": CURRENT_VERSION,
            "verilog_file": "module.v",
            "sva_file": "properties.sv",
            "created_at": datetime.now().isoformat(),
            "source": "preexisting_generated",
            "model_used": None,
            "module_name": base,
            "original_dataset": None,
            "prompt_hash": None,
            "validation": {
                "syntax_check": True,
                "compiles_with_sv_linter": False,
                "num_assertions": count_assertions(sva),
            },
            "judging": {
                "status": "unjudged",
                "llm_scores": [],
                "aggregate_score": None,
                "accepted": None
            }
        }
        with open(os.path.join(sample_dir, "metadata.json"), "w") as f:
            json.dump(meta, f, indent=2)

        jsonl_obj = {**meta, "verilog_code": rtl, "sva_code": sva}
        with open(os.path.join(meta_dir, "metadata.jsonl"), "a") as f:
            f.write(json.dumps(jsonl_obj) + "\n")

        migrated += 1
        update_stats(meta_dir, increment=1)
        print(f"Migrated {base} -> {sample_id}")

    print(f"\nDone. Migrated {migrated} pairs to {os.path.join(DATASET_ROOT, CURRENT_VERSION)}")

if __name__ == "__main__":
    main()