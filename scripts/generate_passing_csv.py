#!/usr/bin/env python3
"""
Parse verification results for each ID and generate a CSV of passing assertions.
Reads property_list.txt, cex_details.txt, and summary.txt for each ID.
Outputs one row per passing assertion (no counter-example).

Usage:
  python generate_passing_csv.py --dataset veri_thoughts --version 2
  python generate_passing_csv.py --dataset metrex --version 1
"""

import argparse
import csv
import os
import re

BASE_DIR = "/home/ab2113/malik25_26"

DATASET_CONFIGS = {
    "veri_thoughts": {
        "results_dir": "{base}/veri_thoughts/dataset/verification_results/version_{ver}/ids",
        "sva_dir": "{base}/veri_thoughts/dataset/version_{ver}",
        "output_csv": "{base}/veri_thoughts/dataset/dataset_stats/version_{ver}/passing_assertions.csv",
    },
    "metrex": {
        "results_dir": "{base}/metrex/dataset/verification_results/version_{ver}/ids",
        "sva_dir": "{base}/metrex/dataset/version_{ver}",
        "output_csv": "{base}/metrex/dataset/dataset_stats/version_{ver}/passing_assertions.csv",
    },
}


def parse_summary(summary_path):
    """Extract DESIGN_ID and TOP from summary.txt."""
    design_id = None
    top = None
    with open(summary_path, "r") as f:
        for line in f:
            line = line.strip()
            if line.startswith("DESIGN_ID="):
                design_id = line.split("=", 1)[1]
            elif line.startswith("TOP="):
                top = line.split("=", 1)[1]
    return design_id, top


def parse_properties(prop_path):
    """Extract assert and cover property names from property_list.txt."""
    asserts = []
    covers = []
    current_section = None
    with open(prop_path, "r") as f:
        for line in f:
            line = line.strip()
            if line == "ASSERT PROPERTIES:":
                current_section = "assert"
                continue
            elif line == "COVER PROPERTIES:":
                current_section = "cover"
                continue
            if current_section == "assert" and line:
                asserts.append(line)
            elif current_section == "cover" and line:
                covers.append(line)
    return asserts, covers


def parse_cex_properties(cex_path):
    """Extract property names that have counter-examples from cex_details.txt."""
    cex_props = set()
    with open(cex_path, "r") as f:
        for line in f:
            line = line.strip()
            if line.startswith("#") or not line:
                continue
            # Format: <embedded>::module.auto_sva_inst.prop_name | cex |
            parts = line.split("|")
            if len(parts) >= 2:
                prop_name = parts[0].strip()
                # Remove <embedded>:: prefix if present
                prop_name = re.sub(r"^<embedded>::", "", prop_name)
                cex_props.add(prop_name)
    return cex_props


def parse_sva_assertions(sva_path):
    """Parse SVA file and return dict mapping label -> full assertion code."""
    assertions = {}
    with open(sva_path, "r") as f:
        content = f.read()

    # Pattern 1: label: assert property ( ... );
    pattern1 = re.compile(
        r'((?:^\s*//[^\n]*\n)*)'   # optional preceding comment lines
        r'^\s*(\w+)\s*:\s*assert\s+property\s*\(',
        re.MULTILINE
    )
    for m in pattern1.finditer(content):
        label = m.group(2)
        start = m.start()
        paren_start = m.end() - 1
        depth = 1
        pos = paren_start + 1
        while pos < len(content) and depth > 0:
            if content[pos] == '(':
                depth += 1
            elif content[pos] == ')':
                depth -= 1
            pos += 1
        while pos < len(content) and content[pos] != ';':
            pos += 1
        assertions[label] = content[start:pos + 1].strip()

    # Pattern 2: label: assert (...); inside always_comb blocks
    pattern2 = re.compile(
        r'((?:^\s*//[^\n]*\n)*)'
        r'^\s*(\w+)\s*:\s*assert\s*\((?!.*property)',
        re.MULTILINE
    )
    for m in pattern2.finditer(content):
        label = m.group(2)
        if label in assertions:
            continue
        start = m.start()
        paren_start = content.index('(', m.start(2) + len(m.group(2)))
        depth = 1
        pos = paren_start + 1
        while pos < len(content) and depth > 0:
            if content[pos] == '(':
                depth += 1
            elif content[pos] == ')':
                depth -= 1
            pos += 1
        while pos < len(content) and content[pos] != ';':
            pos += 1
        assertions[label] = content[start:pos + 1].strip()

    # Pattern 3: label: cover property ( ... );
    pattern3 = re.compile(
        r'((?:^\s*//[^\n]*\n)*)'
        r'^\s*(\w+)\s*:\s*cover\s+property\s*\(',
        re.MULTILINE
    )
    for m in pattern3.finditer(content):
        label = m.group(2)
        if label in assertions:
            continue
        start = m.start()
        paren_start = m.end() - 1
        depth = 1
        pos = paren_start + 1
        while pos < len(content) and depth > 0:
            if content[pos] == '(':
                depth += 1
            elif content[pos] == ')':
                depth -= 1
            pos += 1
        while pos < len(content) and content[pos] != ';':
            pos += 1
        assertions[label] = content[start:pos + 1].strip()

    return assertions


def get_label_from_property(prop_name):
    """Extract the short assertion label from a full property path.
    e.g. 'sky130_fd_sc_hd__fa.auto_sva_inst.check_cout_majority' -> 'check_cout_majority'
    """
    parts = prop_name.split(".")
    return parts[-1] if parts else prop_name


def main():
    parser = argparse.ArgumentParser(description="Generate CSV of passing assertions")
    parser.add_argument("--dataset", required=True, choices=DATASET_CONFIGS.keys(),
                        help="Dataset to process (veri_thoughts or metrex)")
    parser.add_argument("--version", required=True, type=int,
                        help="Dataset version number (e.g. 1, 2)")
    args = parser.parse_args()

    cfg = DATASET_CONFIGS[args.dataset]
    results_dir = cfg["results_dir"].format(base=BASE_DIR, ver=args.version)
    sva_dir = cfg["sva_dir"].format(base=BASE_DIR, ver=args.version)
    output_csv = cfg["output_csv"].format(base=BASE_DIR, ver=args.version)

    if not os.path.isdir(results_dir):
        print(f"ERROR: Results directory not found: {results_dir}")
        return

    os.makedirs(os.path.dirname(output_csv), exist_ok=True)

    rows = []
    id_dirs = sorted(os.listdir(results_dir))

    for id_name in id_dirs:
        id_path = os.path.join(results_dir, id_name)
        if not os.path.isdir(id_path):
            continue

        summary_path = os.path.join(id_path, "summary.txt")
        prop_path = os.path.join(id_path, "property_list.txt")
        cex_path = os.path.join(id_path, "cex_details.txt")

        if not all(os.path.exists(p) for p in [summary_path, prop_path, cex_path]):
            continue

        design_id, top = parse_summary(summary_path)
        if not design_id or not top:
            continue

        all_asserts, all_covers = parse_properties(prop_path)
        cex_props = parse_cex_properties(cex_path)

        passing_asserts = [a for a in all_asserts if a not in cex_props]
        passing_covers = [c for c in all_covers if c not in cex_props]

        if not passing_asserts and not passing_covers:
            continue

        # Load SVA source code
        sva_path = os.path.join(sva_dir, id_name, "sva.sv")
        sva_map = {}
        if os.path.exists(sva_path):
            sva_map = parse_sva_assertions(sva_path)

        for assertion in passing_asserts:
            label = get_label_from_property(assertion)
            sva_code = sva_map.get(label, "")
            if sva_code:
                rows.append((design_id, top, "assert", sva_code))

        for cover in passing_covers:
            label = get_label_from_property(cover)
            sva_code = sva_map.get(label, "")
            if sva_code:
                rows.append((design_id, top, "cover", sva_code))

    with open(output_csv, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["id", "original_rtl_design", "property_type", "passing_property"])
        writer.writerows(rows)

    print(f"Wrote {len(rows)} rows across {len(set(r[0] for r in rows))} IDs to {output_csv}")


if __name__ == "__main__":
    main()
