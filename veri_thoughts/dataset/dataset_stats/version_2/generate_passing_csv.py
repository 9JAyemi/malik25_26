#!/usr/bin/env python3
"""
Parse verification results for each ID and generate a CSV of passing assertions.
Reads property_list.txt, cex_details.txt, and summary.txt for each ID.
Outputs one row per passing assertion (no counter-example).
"""

import csv
import os
import re

RESULTS_DIR = "/home/ab2113/malik25_26/veri_thoughts/dataset/verification_results/version_2/ids"
SVA_DIR = "/home/ab2113/malik25_26/veri_thoughts/dataset/version_2"
OUTPUT_CSV = "/home/ab2113/malik25_26/veri_thoughts/dataset/dataset_stats/version_2/passing_assertions.csv"


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


def parse_assert_properties(prop_path):
    """Extract assert property names from property_list.txt."""
    asserts = []
    in_assert_section = False
    with open(prop_path, "r") as f:
        for line in f:
            line = line.strip()
            if line == "ASSERT PROPERTIES:":
                in_assert_section = True
                continue
            elif line == "COVER PROPERTIES:":
                in_assert_section = False
                continue
            if in_assert_section and line:
                asserts.append(line)
    return asserts


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

    return assertions


def get_label_from_property(prop_name):
    """Extract the short assertion label from a full property path.
    e.g. 'sky130_fd_sc_hd__fa.auto_sva_inst.check_cout_majority' -> 'check_cout_majority'
    """
    parts = prop_name.split(".")
    # The label is the last part after auto_sva_inst.
    return parts[-1] if parts else prop_name


def main():
    rows = []
    id_dirs = sorted(os.listdir(RESULTS_DIR))

    for id_name in id_dirs:
        id_path = os.path.join(RESULTS_DIR, id_name)
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

        all_asserts = parse_assert_properties(prop_path)
        cex_props = parse_cex_properties(cex_path)

        passing = [a for a in all_asserts if a not in cex_props]

        if not passing:
            continue

        # Load SVA source code
        sva_path = os.path.join(SVA_DIR, id_name, "sva.sv")
        sva_map = {}
        if os.path.exists(sva_path):
            sva_map = parse_sva_assertions(sva_path)

        for assertion in passing:
            label = get_label_from_property(assertion)
            sva_code = sva_map.get(label, "")
            rows.append((design_id, top, sva_code))

    with open(OUTPUT_CSV, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["id", "original_rtl_design", "passing_assertion"])
        writer.writerows(rows)

    print(f"Wrote {len(rows)} rows across {len(set(r[0] for r in rows))} IDs to {OUTPUT_CSV}")


if __name__ == "__main__":
    main()
