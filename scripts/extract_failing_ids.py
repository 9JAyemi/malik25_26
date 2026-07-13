"""Extract failing IDs from syntax check CSVs into failing_ids.txt"""
import csv
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
SUMMARY = REPO_ROOT / "runs" / "formal" / "veri_thoughts" / "syntax" / "visual_data" / "summary.csv"
OUTPUT = REPO_ROOT / "data" / "veri_thoughts" / "filters" / "failing_ids.txt"

failing = []
with SUMMARY.open("r", newline="") as f:
    reader = csv.DictReader(f)
    for row in reader:
        if row["status"].strip() == "fail":
            failing.append(row["id"].strip())

OUTPUT.parent.mkdir(parents=True, exist_ok=True)
with OUTPUT.open("w") as f:
    f.write("\n".join(sorted(failing)) + "\n")

print(f"Wrote {len(failing)} failing IDs to {OUTPUT}")
