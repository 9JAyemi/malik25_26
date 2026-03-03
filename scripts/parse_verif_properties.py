#!/usr/bin/env python3
"""
Parse JasperGold run.log files for all IDs that completed verification
(status = pass or cex in verif_summary.csv), extract per-property results,
and generate:

  1. property_results.csv        – one row per (ID, property, type, result)
  2. id_summary.csv              – one row per ID with assertion/cover counts
  3. assertion_results.png       – bar chart of proven vs cex across all assertions
  4. cover_results.png           – bar chart of covered vs unreachable across all covers
  5. avg_assertions_comparison.png – avg proven/cex per "all-pass" vs "has-cex" IDs

Usage:
    python scripts/parse_verif_properties.py <results_dir>

    <results_dir> should contain verif_summary.csv and per-ID subdirectories
    with run.log files (e.g., metrex/dataset/verification_results).
"""

import argparse
import csv
import os
import re
import sys
from collections import defaultdict

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


# ── Regex patterns for per-property results in run.log ──────────────────────
# IPF057 = proven, IPF055 = cex, IPF047 = covered, IPF051 = unreachable
RE_PROVEN = re.compile(
    r'INFO \(IPF057\):.*The property "([^"]+)" was proven'
)
RE_CEX = re.compile(
    r'INFO \(IPF055\):.*counterexample.*property "([^"]+)"'
)
RE_COVERED = re.compile(
    r'INFO \(IPF047\):.*cover property "([^"]+)" was covered'
)
RE_UNREACHABLE = re.compile(
    r'INFO \(IPF051\):.*cover property "([^"]+)" was proven unreachable'
)

# Summary block patterns (aggregate counts as cross-check)
RE_SUMMARY_PROVEN = re.compile(r'- proven\s+:\s+(\d+)')
RE_SUMMARY_CEX = re.compile(r'- cex\s+:\s+(\d+)')
RE_SUMMARY_COVERED = re.compile(r'- covered\s+:\s+(\d+)')
RE_SUMMARY_UNREACHABLE = re.compile(r'- unreachable\s+:\s+(\d+)')
RE_SUMMARY_UNDETERMINED = re.compile(r'^\s+- undetermined\s+:\s+(\d+)')
RE_SUMMARY_UNKNOWN = re.compile(r'^\s+- unknown\s+:\s+(\d+)')
RE_SUMMARY_ERROR = re.compile(r'^\s+- error\s+:\s+(\d+)')

# Internal/system properties to exclude
INTERNAL_PROPS = {":noDeadEnd", ":noConflict", ":live"}


def is_internal(prop_name: str) -> bool:
    """Return True if property is a Jasper internal/system property."""
    return prop_name in INTERNAL_PROPS or prop_name.startswith(":")


def parse_run_log(log_path: str) -> dict:
    """
    Parse a JasperGold run.log and extract per-property results.

    Returns dict with:
        assertions: list of (name, result)   result in {proven, cex}
        covers:     list of (name, result)   result in {covered, unreachable}
        summary:    dict with aggregate counts from SUMMARY block
    """
    assertions = []
    covers = []
    seen_assert = set()
    seen_cover = set()

    summary = {
        "proven": 0, "cex": 0,
        "covered": 0, "unreachable": 0,
        "undetermined": 0, "unknown": 0, "error": 0,
    }

    try:
        with open(log_path, "r", encoding="utf-8", errors="replace") as f:
            lines = f.readlines()
    except (OSError, IOError):
        return {"assertions": [], "covers": [], "summary": summary}

    in_summary = False
    in_asserts_section = False
    in_covers_section = False

    for line in lines:
        # ── Per-property extraction ──
        m = RE_PROVEN.search(line)
        if m:
            name = m.group(1)
            if not is_internal(name) and name not in seen_assert:
                seen_assert.add(name)
                assertions.append((name, "proven"))

        m = RE_CEX.search(line)
        if m:
            name = m.group(1)
            if not is_internal(name) and name not in seen_assert:
                seen_assert.add(name)
                assertions.append((name, "cex"))

        m = RE_COVERED.search(line)
        if m:
            name = m.group(1)
            if not is_internal(name) and name not in seen_cover:
                seen_cover.add(name)
                covers.append((name, "covered"))

        m = RE_UNREACHABLE.search(line)
        if m:
            name = m.group(1)
            if not is_internal(name) and name not in seen_cover:
                seen_cover.add(name)
                covers.append((name, "unreachable"))

        # ── Summary block extraction (aggregate counts) ──
        if "SUMMARY" in line and "====" in line:
            in_summary = True
            continue

        if in_summary:
            if "assertions" in line and ":" in line and "proven" not in line:
                in_asserts_section = True
                in_covers_section = False
                continue
            if "covers" in line and ":" in line and "covered" not in line:
                in_covers_section = True
                in_asserts_section = False
                continue

            if in_asserts_section:
                for key, pat in [("proven", RE_SUMMARY_PROVEN),
                                 ("cex", RE_SUMMARY_CEX)]:
                    m2 = pat.search(line)
                    if m2:
                        summary[key] = int(m2.group(1))

            if in_covers_section:
                for key, pat in [("covered", RE_SUMMARY_COVERED),
                                 ("unreachable", RE_SUMMARY_UNREACHABLE)]:
                    m2 = pat.search(line)
                    if m2:
                        summary[key] = int(m2.group(1))

            # Also grab undetermined/unknown/error from either section
            for key, pat in [("undetermined", RE_SUMMARY_UNDETERMINED),
                             ("unknown", RE_SUMMARY_UNKNOWN),
                             ("error", RE_SUMMARY_ERROR)]:
                m2 = pat.search(line)
                if m2:
                    summary[key] += int(m2.group(1))

            if "====" in line and in_summary:
                in_summary = False

    return {"assertions": assertions, "covers": covers, "summary": summary}


def main():
    parser = argparse.ArgumentParser(
        description="Parse JasperGold run.logs and generate property-level reports."
    )
    parser.add_argument(
        "results_dir",
        help="Path to verification_results directory containing verif_summary.csv and ID subdirs",
    )
    parser.add_argument(
        "--out", "-o",
        default=None,
        help="Output directory for CSVs and PNGs (default: same as results_dir)",
    )
    args = parser.parse_args()

    results_dir = os.path.abspath(args.results_dir)
    out_dir = os.path.abspath(args.out) if args.out else results_dir

    csv_path = os.path.join(results_dir, "verif_summary.csv")
    if not os.path.isfile(csv_path):
        print(f"ERROR: {csv_path} not found.")
        sys.exit(1)

    os.makedirs(out_dir, exist_ok=True)

    # ── Step 1: Read verif_summary.csv and collect IDs that completed verification ──
    EXCLUDE_IDS = {"jgproject", "metadata", "myenv"}
    completed_ids = []  # (id, status)  status in {pass, cex}

    with open(csv_path, newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            sid = row["id"].strip()
            if sid in EXCLUDE_IDS:
                continue
            status = row["status"].strip().lower()
            if status in ("pass", "cex"):
                completed_ids.append((sid, status))

    print(f"Found {len(completed_ids)} IDs with completed verification (pass or cex)")

    # ── Step 2: Parse each run.log ──
    property_rows = []       # (id, prop_name, type, result)
    id_summary_rows = []     # (id, csv_status, n_assert, n_proven, n_cex, n_cover, n_covered, n_unreachable)
    all_pass_ids = []        # IDs with zero CEX
    has_cex_ids = []         # IDs with at least one CEX

    total_proven_global = 0
    total_cex_global = 0
    total_covered_global = 0
    total_unreachable_global = 0

    skipped = 0
    for sid, csv_status in completed_ids:
        log_path = os.path.join(results_dir, sid, "run.log")
        if not os.path.isfile(log_path):
            skipped += 1
            continue

        result = parse_run_log(log_path)
        assertions = result["assertions"]
        covers = result["covers"]

        n_proven = sum(1 for _, r in assertions if r == "proven")
        n_cex = sum(1 for _, r in assertions if r == "cex")
        n_covered = sum(1 for _, r in covers if r == "covered")
        n_unreachable = sum(1 for _, r in covers if r == "unreachable")

        total_proven_global += n_proven
        total_cex_global += n_cex
        total_covered_global += n_covered
        total_unreachable_global += n_unreachable

        for name, res in assertions:
            property_rows.append((sid, name, "assertion", res))
        for name, res in covers:
            property_rows.append((sid, name, "cover", res))

        id_summary_rows.append((
            sid, csv_status,
            len(assertions), n_proven, n_cex,
            len(covers), n_covered, n_unreachable,
        ))

        if n_cex == 0:
            all_pass_ids.append((sid, n_proven, n_cex, len(assertions)))
        else:
            has_cex_ids.append((sid, n_proven, n_cex, len(assertions)))

    if skipped:
        print(f"  (skipped {skipped} IDs with missing run.log)")

    # ── Step 3: Write property_results.csv ──
    prop_csv = os.path.join(out_dir, "property_results.csv")
    with open(prop_csv, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["id", "property_name", "type", "result"])
        for row in sorted(property_rows, key=lambda r: (r[0], r[2], r[1])):
            w.writerow(row)
    print(f"Wrote {len(property_rows)} rows to {prop_csv}")

    # ── Step 4: Write id_summary.csv ──
    id_csv = os.path.join(out_dir, "id_summary.csv")
    with open(id_csv, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow([
            "id", "csv_status",
            "total_assertions", "proven", "cex",
            "total_covers", "covered", "unreachable",
        ])
        for row in sorted(id_summary_rows, key=lambda r: r[0]):
            w.writerow(row)
    print(f"Wrote {len(id_summary_rows)} rows to {id_csv}")

    # ── Step 5: Print statistics ──
    n_all_pass = len(all_pass_ids)
    n_has_cex = len(has_cex_ids)

    avg_proven_pass = (
        np.mean([p for _, p, _, _ in all_pass_ids]) if all_pass_ids else 0
    )
    avg_total_pass = (
        np.mean([t for _, _, _, t in all_pass_ids]) if all_pass_ids else 0
    )
    avg_proven_cex = (
        np.mean([p for _, p, _, _ in has_cex_ids]) if has_cex_ids else 0
    )
    avg_cex_cex = (
        np.mean([c for _, _, c, _ in has_cex_ids]) if has_cex_ids else 0
    )
    avg_total_cex = (
        np.mean([t for _, _, _, t in has_cex_ids]) if has_cex_ids else 0
    )

    print()
    print("=" * 60)
    print("PROPERTY-LEVEL STATISTICS")
    print("=" * 60)
    print(f"Total assertions parsed : {total_proven_global + total_cex_global}")
    print(f"  Proven                : {total_proven_global}")
    print(f"  CEX                   : {total_cex_global}")
    print(f"Total covers parsed     : {total_covered_global + total_unreachable_global}")
    print(f"  Covered               : {total_covered_global}")
    print(f"  Unreachable           : {total_unreachable_global}")
    print()
    print("=" * 60)
    print("PER-ID STATISTICS")
    print("=" * 60)
    print(f"IDs with all assertions proven (all-pass) : {n_all_pass}")
    print(f"  Avg proven assertions per ID            : {avg_proven_pass:.2f}")
    print(f"  Avg total assertions per ID             : {avg_total_pass:.2f}")
    print()
    print(f"IDs with at least one CEX (has-cex)       : {n_has_cex}")
    print(f"  Avg proven assertions per ID            : {avg_proven_cex:.2f}")
    print(f"  Avg CEX assertions per ID               : {avg_cex_cex:.2f}")
    print(f"  Avg total assertions per ID             : {avg_total_cex:.2f}")

    # ── Step 6: Generate plots ──

    # --- Figure 1: Assertion results (proven vs cex) ---
    fig1, ax1 = plt.subplots(figsize=(7, 5))
    labels1 = ["Proven", "CEX"]
    counts1 = [total_proven_global, total_cex_global]
    total_assert = sum(counts1) or 1
    colors1 = ["#4CAF50", "#F44336"]
    bars1 = ax1.bar(labels1, counts1, color=colors1, edgecolor="black", width=0.5)
    for bar, cnt in zip(bars1, counts1):
        pct = cnt / total_assert * 100
        ax1.text(
            bar.get_x() + bar.get_width() / 2,
            bar.get_height() + total_assert * 0.01,
            f"{cnt}\n({pct:.1f}%)",
            ha="center", va="bottom", fontsize=12, fontweight="bold",
        )
    ax1.set_ylabel("Number of Assertions", fontsize=12)
    ax1.set_title("Assertion Results: Proven vs CEX", fontsize=14, fontweight="bold")
    ax1.set_ylim(0, max(counts1) * 1.2)
    fig1.tight_layout()
    path1 = os.path.join(out_dir, "assertion_results.png")
    fig1.savefig(path1, dpi=150)
    plt.close(fig1)
    print(f"\nSaved {path1}")

    # --- Figure 2: Cover results (covered vs unreachable) ---
    fig2, ax2 = plt.subplots(figsize=(7, 5))
    labels2 = ["Covered", "Unreachable"]
    counts2 = [total_covered_global, total_unreachable_global]
    total_cover = sum(counts2) or 1
    colors2 = ["#2196F3", "#FF9800"]
    bars2 = ax2.bar(labels2, counts2, color=colors2, edgecolor="black", width=0.5)
    for bar, cnt in zip(bars2, counts2):
        pct = cnt / total_cover * 100
        ax2.text(
            bar.get_x() + bar.get_width() / 2,
            bar.get_height() + total_cover * 0.01,
            f"{cnt}\n({pct:.1f}%)",
            ha="center", va="bottom", fontsize=12, fontweight="bold",
        )
    ax2.set_ylabel("Number of Covers", fontsize=12)
    ax2.set_title("Cover Results: Covered vs Unreachable", fontsize=14, fontweight="bold")
    ax2.set_ylim(0, max(counts2) * 1.2)
    fig2.tight_layout()
    path2 = os.path.join(out_dir, "cover_results.png")
    fig2.savefig(path2, dpi=150)
    plt.close(fig2)
    print(f"Saved {path2}")

    # --- Figure 3: Average assertions comparison ---
    fig3, ax3 = plt.subplots(figsize=(8, 5))
    x = np.arange(2)
    width = 0.3

    proven_vals = [avg_proven_pass, avg_proven_cex]
    cex_vals = [0, avg_cex_cex]  # all-pass group has 0 cex by definition

    bars_p = ax3.bar(x - width / 2, proven_vals, width, label="Avg Proven",
                     color="#4CAF50", edgecolor="black")
    bars_c = ax3.bar(x + width / 2, cex_vals, width, label="Avg CEX",
                     color="#F44336", edgecolor="black")

    for bars in [bars_p, bars_c]:
        for bar in bars:
            h = bar.get_height()
            if h > 0:
                ax3.text(
                    bar.get_x() + bar.get_width() / 2,
                    h + 0.1,
                    f"{h:.2f}",
                    ha="center", va="bottom", fontsize=11, fontweight="bold",
                )

    ax3.set_xticks(x)
    ax3.set_xticklabels([
        f"All-Pass IDs\n(n={n_all_pass})",
        f"Has-CEX IDs\n(n={n_has_cex})",
    ], fontsize=11)
    ax3.set_ylabel("Avg Assertions per ID", fontsize=12)
    ax3.set_title("Avg Proven vs CEX Assertions:\nAll-Pass IDs vs Has-CEX IDs",
                  fontsize=14, fontweight="bold")
    ax3.legend(fontsize=11)
    ax3.set_ylim(0, max(max(proven_vals), max(cex_vals)) * 1.35)
    fig3.tight_layout()
    path3 = os.path.join(out_dir, "avg_assertions_comparison.png")
    fig3.savefig(path3, dpi=150)
    plt.close(fig3)
    print(f"Saved {path3}")

    # --- Figure 4: Distribution of assertion counts per ID (histogram) ---
    fig4, (ax4a, ax4b) = plt.subplots(1, 2, figsize=(14, 5))

    if all_pass_ids:
        proven_counts_pass = [p for _, p, _, _ in all_pass_ids]
        ax4a.hist(proven_counts_pass, bins=range(0, max(proven_counts_pass) + 2),
                  color="#4CAF50", edgecolor="black", alpha=0.8)
        ax4a.set_xlabel("Number of Proven Assertions", fontsize=11)
        ax4a.set_ylabel("Number of IDs", fontsize=11)
        ax4a.set_title(f"All-Pass IDs (n={n_all_pass})\nProven Assertion Distribution",
                      fontsize=12, fontweight="bold")

    if has_cex_ids:
        proven_counts_cex = [p for _, p, _, _ in has_cex_ids]
        cex_counts_cex = [c for _, _, c, _ in has_cex_ids]
        ax4b.hist([proven_counts_cex, cex_counts_cex],
                  bins=range(0, max(max(proven_counts_cex, default=0),
                                    max(cex_counts_cex, default=0)) + 2),
                  color=["#4CAF50", "#F44336"], edgecolor="black", alpha=0.8,
                  label=["Proven", "CEX"])
        ax4b.set_xlabel("Number of Assertions", fontsize=11)
        ax4b.set_ylabel("Number of IDs", fontsize=11)
        ax4b.set_title(f"Has-CEX IDs (n={n_has_cex})\nAssertion Distribution",
                      fontsize=12, fontweight="bold")
        ax4b.legend(fontsize=10)

    fig4.tight_layout()
    path4 = os.path.join(out_dir, "assertion_distribution.png")
    fig4.savefig(path4, dpi=150)
    plt.close(fig4)
    print(f"Saved {path4}")

    print("\nDone!")


if __name__ == "__main__":
    main()
