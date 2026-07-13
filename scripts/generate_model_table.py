#!/usr/bin/env python3
"""Parse inference syntax and verification results to fill the model comparison table."""

import os
import csv
import sys

BASE_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# Map: table row label -> inference-run subdirectory name
MODELS = {
    "Qwen2.5 (untrained)":         "base_qwen",
    "Adapter: All Data":            "adapter_all",
    "Adapter: Syntax Passing":      "adapter_syntax_pass",
    "Adapter: Verified Assertions": "adapter_verified",
}


def parse_syntax(model_dir):
    """Return (total, pass_count, fail_count) from syntax summary.csv."""
    csv_path = os.path.join(
        BASE_DIR, "runs", "inference", "syntax_results", model_dir, "visual_data", "summary.csv"
    )
    if not os.path.isfile(csv_path):
        return 0, 0, 0
    ok = fail = 0
    with open(csv_path, newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            if row["status"] == "ok":
                ok += 1
            else:
                fail += 1
    return ok + fail, ok, fail


def parse_verification(model_dir):
    """Return (total_properties, proven, cex) from verification summary.txt files."""
    ids_dir = os.path.join(
        BASE_DIR, "runs", "inference", "verification_results", model_dir, "ids"
    )
    if not os.path.isdir(ids_dir):
        return 0, 0, 0
    total_assert = 0
    total_cex = 0
    total_ar_cex = 0
    for id_name in os.listdir(ids_dir):
        summary = os.path.join(ids_dir, id_name, "summary.txt")
        if not os.path.isfile(summary):
            continue
        vals = {}
        with open(summary) as f:
            for line in f:
                if "=" in line:
                    k, v = line.strip().split("=", 1)
                    vals[k] = v
        try:
            total_assert += int(vals.get("ASSERT_COUNT", 0))
            total_cex += int(vals.get("CEX_COUNT", 0))
            total_ar_cex += int(vals.get("AR_CEX_COUNT", 0))
        except ValueError:
            pass
    cex = total_cex + total_ar_cex
    proven = total_assert - cex
    return total_assert, proven, cex


def fmt(n):
    """Format number with commas."""
    return f"{n:,}"


def pct(part, total):
    """Format percentage."""
    if total == 0:
        return "0.0"
    return f"{100.0 * part / total:.1f}"


def main():
    print(f"{'Model':<30} {'Designs':>8} {'Syn Pass':>14} {'Syn Fail':>14} {'Properties':>12} {'Proven':>18} {'CEX':>18}")
    print("-" * 120)

    for label, model_dir in MODELS.items():
        total, ok, fail = parse_syntax(model_dir)
        props, proven, cex = parse_verification(model_dir)

        syn_pass_str = f"{fmt(ok)} ({pct(ok, total)}%)"
        syn_fail_str = f"{fmt(fail)} ({pct(fail, total)}%)"
        proven_str   = f"{fmt(proven)} ({pct(proven, props)}%)"
        cex_str      = f"{fmt(cex)} ({pct(cex, props)}%)"

        print(f"{label:<30} {fmt(total):>8} {syn_pass_str:>14} {syn_fail_str:>14} {fmt(props):>12} {proven_str:>18} {cex_str:>18}")

    # Also print LaTeX-ready rows
    print("\n\n% === LaTeX rows (paste into your table) ===\n")
    for label, model_dir in MODELS.items():
        total, ok, fail = parse_syntax(model_dir)
        props, proven, cex = parse_verification(model_dir)

        row = (
            f"{label:<35} & {fmt(total)} "
            f"& {fmt(ok)} ({pct(ok, total)}\\%) "
            f"& {fmt(fail)} ({pct(fail, total)}\\%) "
            f"& {fmt(props)} "
            f"& {fmt(proven)} ({pct(proven, props)}\\%) "
            f"& {fmt(cex)} ({pct(cex, props)}\\%) \\\\"
        )
        print(row)


if __name__ == "__main__":
    main()
