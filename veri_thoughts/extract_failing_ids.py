"""Extract failing IDs from syntax check CSVs into failing_ids.txt"""
import csv

failing = []
for path in ["summary_version_1.csv", "summary_version_2.csv"]:
    with open(path, "r") as f:
        reader = csv.DictReader(f)
        for row in reader:
            if row["status"].strip() == "fail":
                failing.append(row["id"].strip())

with open("failing_ids.txt", "w") as f:
    f.write("\n".join(sorted(failing)) + "\n")

print(f"Wrote {len(failing)} failing IDs to failing_ids.txt")