#!/usr/bin/env python3
"""Count RTL-SVA pairs and assertions in JSONL splits. Read-only."""

import json
import re
from pathlib import Path

FILES = ["train.jsonl", "validation.jsonl", "test.jsonl"]

ASSERT_RE = re.compile(r"\bassert\s+property\b", re.IGNORECASE)
ASSUME_RE = re.compile(r"\bassume\s+property\b", re.IGNORECASE)
COVER_RE  = re.compile(r"\bcover\s+property\b", re.IGNORECASE)
PROPERTY_BLOCK_RE = re.compile(r"\bproperty\b\s+\w+", re.IGNORECASE)


def count_in_sva(sva: str) -> dict:
    return {
        "assert":   len(ASSERT_RE.findall(sva)),
        "assume":   len(ASSUME_RE.findall(sva)),
        "cover":    len(COVER_RE.findall(sva)),
        "property": len(PROPERTY_BLOCK_RE.findall(sva)),
    }


def count_file(path: Path) -> dict:
    totals = {"pairs": 0, "assert": 0, "assume": 0, "cover": 0, "property": 0}
    with path.open() as f:
        for i, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
            try:
                rec = json.loads(line)
            except json.JSONDecodeError as e:
                print(f"  [warn] {path.name}:{i} bad JSON: {e}")
                continue
            if "rtl" not in rec or "sva" not in rec or not rec["sva"]:
                print(f"  [warn] {path.name}:{i} missing rtl/sva")
                continue
            totals["pairs"] += 1
            for k, v in count_in_sva(rec["sva"]).items():
                totals[k] += v
    return totals


def main() -> None:
    grand = {"pairs": 0, "assert": 0, "assume": 0, "cover": 0, "property": 0}
    header = f"{'File':<20}{'Pairs':>8}{'assert':>10}{'assume':>10}{'cover':>10}{'property':>12}"
    print(header)
    print("-" * len(header))
    for name in FILES:
        path = Path(name)
        if not path.exists():
            print(f"{name:<20}{'MISSING':>8}")
            continue
        t = count_file(path)
        for k in grand:
            grand[k] += t[k]
        print(f"{name:<20}{t['pairs']:>8,}{t['assert']:>10,}"
              f"{t['assume']:>10,}{t['cover']:>10,}{t['property']:>12,}")
    print("-" * len(header))
    print(f"{'TOTAL':<20}{grand['pairs']:>8,}{grand['assert']:>10,}"
          f"{grand['assume']:>10,}{grand['cover']:>10,}{grand['property']:>12,}")
    print(f"\nTotal assert+assume+cover: "
          f"{grand['assert'] + grand['assume'] + grand['cover']:,}")


if __name__ == "__main__":
    main()