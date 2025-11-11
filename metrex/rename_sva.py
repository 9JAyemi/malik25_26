import os
import json
import argparse
from datetime import datetime
from typing import Tuple

DATASET_ROOT = "dataset"

def is_version_dir(path: str) -> bool:
    return os.path.isdir(path) and os.path.basename(path).startswith("version_")

def rename_file(old_path: str, new_path: str, dry_run: bool):
    if dry_run:
        print(f"[DRY] rename {old_path} -> {new_path}")
    else:
        os.rename(old_path, new_path)

def remove_file(path: str, dry_run: bool):
    if dry_run:
        print(f"[DRY] remove {path}")
    else:
        os.remove(path)

def load_json(path: str):
    try:
        with open(path, "r") as f:
            return json.load(f)
    except Exception as e:
        print(f"  ! Failed to read {path}: {e}")
        return None

def save_json(path: str, obj, dry_run: bool):
    if dry_run:
        print(f"[DRY] write {path}")
    else:
        with open(path, "w") as f:
            json.dump(obj, f, indent=2)

def process_sample_dir(sample_dir: str, delete_duplicate: bool, dry_run: bool) -> Tuple[bool, bool]:
    """
    Returns: (renamed, metadata_updated)
    """
    properties_path = os.path.join(sample_dir, "properties.sv")
    sva_path = os.path.join(sample_dir, "sva.sv")
    renamed = False
    metadata_changed = False

    if not os.path.isdir(sample_dir):
        return renamed, metadata_changed

    has_properties = os.path.isfile(properties_path)
    has_sva = os.path.isfile(sva_path)

    if not has_properties and not has_sva:
        return renamed, metadata_changed

    # Rename properties.sv -> sva.sv if only the old name exists
    if has_properties and not has_sva:
        rename_file(properties_path, sva_path, dry_run)
        renamed = True
    elif has_properties and has_sva:
        # Decide what to do if both exist
        if delete_duplicate:
            # Assume sva.sv is canonical; remove properties.sv
            remove_file(properties_path, dry_run)
        else:
            print(f"  ! Both properties.sv and sva.sv exist in {sample_dir}. Skipping removal (use --delete-duplicates).")

    # Update metadata.json if present
    meta_path = os.path.join(sample_dir, "metadata.json")
    if os.path.isfile(meta_path):
        meta = load_json(meta_path)
        if meta and meta.get("sva_file") == "properties.sv":
            meta["sva_file"] = "sva.sv"
            save_json(meta_path, meta, dry_run)
            metadata_changed = True

    return renamed, metadata_changed

def rewrite_metadata_jsonl(version_dir: str, dry_run: bool) -> Tuple[int, bool]:
    """
    Rewrites metadata/metadata.jsonl lines that reference properties.sv in the "sva_file" field.
    Returns: (lines_modified, rewritten_flag)
    """
    meta_dir = os.path.join(version_dir, "metadata")
    jsonl_path = os.path.join(meta_dir, "metadata.jsonl")
    if not os.path.isfile(jsonl_path):
        return 0, False

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    backup_path = f"{jsonl_path}.bak_{timestamp}"
    temp_path = f"{jsonl_path}.tmp"

    lines_modified = 0
    rewritten = False

    try:
        with open(jsonl_path, "r") as src, open(temp_path, "w") as dst:
            for line in src:
                stripped = line.strip()
                if not stripped:
                    dst.write(line)
                    continue
                try:
                    obj = json.loads(stripped)
                except Exception:
                    # Pass through unmodified if not valid JSON
                    dst.write(line)
                    continue
                if obj.get("sva_file") == "properties.sv":
                    obj["sva_file"] = "sva.sv"
                    lines_modified += 1
                    rewritten = True
                dst.write(json.dumps(obj) + "\n")
    except Exception as e:
        print(f"  ! Error processing {jsonl_path}: {e}")
        if os.path.exists(temp_path):
            os.remove(temp_path)
        return 0, False

    if lines_modified == 0:
        # Nothing changed; clean up temp
        os.remove(temp_path)
        return 0, False

    if dry_run:
        print(f"[DRY] Would rewrite {jsonl_path} (modified {lines_modified} lines) and create backup {backup_path}")
        os.remove(temp_path)
    else:
        os.rename(jsonl_path, backup_path)
        os.rename(temp_path, jsonl_path)

    return lines_modified, True

def main():
    parser = argparse.ArgumentParser(description="Rename properties.sv to sva.sv and update metadata.")
    parser.add_argument("--dataset-root", default=DATASET_ROOT, help="Root dataset directory (default: dataset)")
    parser.add_argument("--delete-duplicates", action="store_true",
                        help="If both properties.sv and sva.sv exist, delete properties.sv (keep sva.sv).")
    parser.add_argument("--dry-run", action="store_true", help="Show actions without modifying files.")
    args = parser.parse_args()

    root = args.dataset_root
    if not os.path.isdir(root):
        print(f"No dataset directory found at {root}")
        return

    total_samples = 0
    total_renamed = 0
    total_meta_updated = 0
    total_jsonl_lines = 0
    versions_rewritten = 0

    version_dirs = [os.path.join(root, d) for d in os.listdir(root) if is_version_dir(os.path.join(root, d))]
    if not version_dirs:
        print("No version_* directories found; nothing to do.")
        return

    for version_dir in sorted(version_dirs):
        print(f"\nProcessing version: {os.path.basename(version_dir)}")
        # Sample dirs = numeric zero-padded directories
        sample_dirs = [os.path.join(version_dir, d) for d in os.listdir(version_dir)
                       if os.path.isdir(os.path.join(version_dir, d)) and d.isdigit()]
        sample_dirs.sort()
        for sd in sample_dirs:
            renamed, meta_updated = process_sample_dir(sd, args.delete_duplicates, args.dry_run)
            if renamed:
                total_renamed += 1
            if meta_updated:
                total_meta_updated += 1
            total_samples += 1

        # Rewrite metadata.jsonl
        lines_modified, rewritten = rewrite_metadata_jsonl(version_dir, args.dry_run)
        if rewritten:
            versions_rewritten += 1
            total_jsonl_lines += lines_modified

    print("\n=== Summary ===")
    print(f"Versions scanned:            {len(version_dirs)}")
    print(f"Sample directories scanned:  {total_samples}")
    print(f"Files renamed (properties->sva): {total_renamed}")
    print(f"metadata.json updated:       {total_meta_updated}")
    print(f"metadata.jsonl lines changed:{total_jsonl_lines}")
    print(f"Versions with JSONL rewrite: {versions_rewritten}")
    print(f"Dry run: {args.dry_run}")

    if args.dry_run:
        print("\nRe-run without --dry-run to apply changes.")

if __name__ == "__main__":
    main()