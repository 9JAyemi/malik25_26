#!/usr/bin/env python3
"""
Parse verification results for each ID and generate a CSV of passing assertions.
Reads property_list.txt, cex_details.txt, and summary.txt for each ID.
Outputs one row per passing assertion (no counter-example).

Usage:
  python generate_passing_csv.py --dataset veri_thoughts --version 2
  python generate_passing_csv.py --dataset metrex --version 1
  python generate_passing_csv.py --dataset inference_outputs
"""

import argparse
import csv
import os
import re

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

BASE_DIR = "/home/ab2113/malik25_26"

# Regex to count SVA properties
RE_ASSERT = re.compile(r'\bassert\s+property\b', re.IGNORECASE)
RE_COVER  = re.compile(r'\bcover\s+property\b',  re.IGNORECASE)
RE_ASSUME = re.compile(r'\bassume\s+property\b',  re.IGNORECASE)

DATASET_CONFIGS = {
    "veri_thoughts": {
        "results_dir": "{base}/veri_thoughts/dataset/verification_results/version_{ver}/ids",
        "sva_dir": "{base}/veri_thoughts/dataset/version_{ver}",
        "output_csv": "{base}/veri_thoughts/dataset/verification_results/version_{ver}/visual_data/passing_assertions.csv",
    },
    "metrex": {
        "results_dir": "{base}/metrex/dataset/verification_results/version_{ver}/ids",
        "sva_dir": "{base}/metrex/dataset/version_{ver}",
        "output_csv": "{base}/metrex/dataset/verification_results/version_{ver}/visual_data/passing_assertions.csv",
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


def generate_pass_fail_chart(total_passing, total_failing, label, out_dir,
                             compile_fail_ids=0, total_ids=0):
    """Generate a PNG with two subplots: raw counts bar and percentage pie.
    compile_fail_ids: number of IDs that failed at compile (no property data).
    """
    os.makedirs(out_dir, exist_ok=True)
    total_props = total_passing + total_failing
    if total_props == 0 and compile_fail_ids == 0:
        return

    # Bar chart
    fig1, ax1 = plt.subplots(figsize=(7, 5))
    if total_props > 0:
        bars = ax1.bar(["Passing", "Failing (CEX)"], [total_passing, total_failing],
                       color=["#4CAF50", "#F44336"], edgecolor="black", linewidth=0.5)
        for bar, val in zip(bars, [total_passing, total_failing]):
            ax1.text(bar.get_x() + bar.get_width() / 2, bar.get_height() + total_props * 0.01,
                     f"{val:,}", ha="center", va="bottom", fontweight="bold", fontsize=12)
        subtitle = f"(Total Properties: {total_props:,})"
        if compile_fail_ids > 0:
            subtitle += f"\n{compile_fail_ids} of {total_ids} IDs failed at compile (no properties)"
        ax1.set_ylabel("Number of Assertions", fontsize=12)
        ax1.set_title(f"Passing vs Failing Assertions — {label}\n{subtitle}",
                      fontsize=12, fontweight="bold")
    else:
        bars = ax1.bar(["Compile-Failed IDs"], [compile_fail_ids],
                       color=["#9E9E9E"], edgecolor="black", linewidth=0.5)
        ax1.text(0, compile_fail_ids + 0.5, f"{compile_fail_ids:,}",
                 ha="center", va="bottom", fontweight="bold", fontsize=12)
        ax1.set_ylabel("Number of IDs", fontsize=12)
        ax1.set_title(f"All {compile_fail_ids} IDs Failed at Compile — {label}\n(0 properties extracted)",
                      fontsize=12, fontweight="bold")
    fig1.tight_layout()
    bar_path = os.path.join(out_dir, "pass_fail_assertions_bar.png")
    fig1.savefig(bar_path, dpi=150)
    plt.close(fig1)
    print(f"  Saved {bar_path}")

    # Pie chart
    fig2, ax2 = plt.subplots(figsize=(7, 5))
    if total_props > 0:
        sizes = [total_passing, total_failing]
        labels_pie = [f"Passing\n({total_passing:,})", f"Failing\n({total_failing:,})"]
        colors = ["#4CAF50", "#F44336"]
    else:
        sizes = [compile_fail_ids]
        labels_pie = [f"Compile Failed\n({compile_fail_ids:,} IDs)"]
        colors = ["#9E9E9E"]
    filtered = [(s, l, c) for s, l, c in zip(sizes, labels_pie, colors) if s > 0]
    if filtered:
        sizes, labels_pie, colors = zip(*filtered)
        wedges, texts, autotexts = ax2.pie(
            sizes, labels=labels_pie, colors=colors, autopct="%1.1f%%",
            startangle=90, pctdistance=0.6,
            wedgeprops=dict(edgecolor="black", linewidth=0.5),
        )
        for t in autotexts:
            t.set_fontsize(12)
            t.set_fontweight("bold")
    ax2.set_title(f"Assertion Pass Rate — {label}", fontsize=13, fontweight="bold")
    fig2.tight_layout()
    pie_path = os.path.join(out_dir, "pass_fail_assertions_pie.png")
    fig2.savefig(pie_path, dpi=150)
    plt.close(fig2)
    print(f"  Saved {pie_path}")


def generate_auto_bind_chart(results_dir, label, out_dir):
    """Generate a PNG showing IDs that needed auto_bind vs those that did not."""
    visual_data_dir = os.path.join(os.path.dirname(results_dir), "visual_data")
    csv_path = os.path.join(visual_data_dir, "verif_summary.csv")
    if not os.path.isfile(csv_path):
        return

    auto_bind_count = 0
    no_auto_bind_count = 0
    with open(csv_path, "r", newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            status = row.get("status", "").strip().lower()
            if status == "skip":
                continue
            ab = row.get("auto_bind", "").strip()
            if ab == "1":
                auto_bind_count += 1
            else:
                no_auto_bind_count += 1

    total = auto_bind_count + no_auto_bind_count
    if total == 0:
        return

    os.makedirs(out_dir, exist_ok=True)

    # Bar chart
    fig1, ax1 = plt.subplots(figsize=(7, 5))
    bars = ax1.bar(["Auto-Bind", "No Auto-Bind"],
                   [auto_bind_count, no_auto_bind_count],
                   color=["#FF9800", "#2196F3"], edgecolor="black", linewidth=0.5)
    for bar, val in zip(bars, [auto_bind_count, no_auto_bind_count]):
        ax1.text(bar.get_x() + bar.get_width() / 2, bar.get_height() + total * 0.01,
                 f"{val:,}", ha="center", va="bottom", fontweight="bold", fontsize=12)
    ax1.set_ylabel("Number of IDs", fontsize=12)
    ax1.set_title(f"Auto-Bind Usage — {label}\n(Total IDs: {total:,})",
                  fontsize=12, fontweight="bold")
    fig1.tight_layout()
    bar_path = os.path.join(out_dir, "auto_bind_usage_bar.png")
    fig1.savefig(bar_path, dpi=150)
    plt.close(fig1)
    print(f"  Saved {bar_path}")

    # Pie chart
    fig2, ax2 = plt.subplots(figsize=(7, 5))
    sizes = [auto_bind_count, no_auto_bind_count]
    labels_pie = [f"Auto-Bind\n({auto_bind_count:,})",
                  f"No Auto-Bind\n({no_auto_bind_count:,})"]
    colors = ["#FF9800", "#2196F3"]
    filtered = [(s, l, c) for s, l, c in zip(sizes, labels_pie, colors) if s > 0]
    if filtered:
        sizes, labels_pie, colors = zip(*filtered)
        wedges, texts, autotexts = ax2.pie(
            sizes, labels=labels_pie, colors=colors, autopct="%1.1f%%",
            startangle=90, pctdistance=0.6,
            wedgeprops=dict(edgecolor="black", linewidth=0.5),
        )
        for t in autotexts:
            t.set_fontsize(12)
            t.set_fontweight("bold")
    ax2.set_title(f"Auto-Bind Rate — {label}", fontsize=13, fontweight="bold")
    fig2.tight_layout()
    pie_path = os.path.join(out_dir, "auto_bind_usage_pie.png")
    fig2.savefig(pie_path, dpi=150)
    plt.close(fig2)
    print(f"  Saved {pie_path}")


def parse_vacuity_results(vacuity_path):
    """Parse vacuity_results.txt and return (vacuous_count, non_vacuous_count, error_count)."""
    vacuous = 0
    non_vacuous = 0
    errors = 0
    if not os.path.isfile(vacuity_path):
        return vacuous, non_vacuous, errors
    with open(vacuity_path, "r", encoding="utf-8", errors="replace") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = [p.strip() for p in line.split("|")]
            if len(parts) >= 2:
                result = parts[1].lower()
                if result == "yes":
                    vacuous += 1
                elif result == "no":
                    non_vacuous += 1
                elif result == "error":
                    errors += 1
    return vacuous, non_vacuous, errors


def generate_vacuity_chart(results_dir, label, out_dir):
    """Generate a PNG showing vacuous (false positive) vs non-vacuous proven assertions."""
    total_vacuous = 0
    total_non_vacuous = 0
    total_errors = 0

    ids_dir = results_dir
    if not os.path.isdir(ids_dir):
        return

    for id_name in sorted(os.listdir(ids_dir)):
        id_path = os.path.join(ids_dir, id_name)
        if not os.path.isdir(id_path):
            continue
        vacuity_path = os.path.join(id_path, "vacuity_results.txt")
        v, nv, e = parse_vacuity_results(vacuity_path)
        total_vacuous += v
        total_non_vacuous += nv
        total_errors += e

    total_checked = total_vacuous + total_non_vacuous
    if total_checked == 0:
        print(f"  No vacuity data found for {label}, skipping vacuity chart")
        return

    os.makedirs(out_dir, exist_ok=True)

    # Bar chart
    fig1, ax1 = plt.subplots(figsize=(7, 5))
    bar_labels = ["Non-Vacuous\n(Genuine)", "Vacuous\n(False Positive)"]
    bar_vals = [total_non_vacuous, total_vacuous]
    bar_colors = ["#4CAF50", "#FF9800"]
    bars = ax1.bar(bar_labels, bar_vals, color=bar_colors, edgecolor="black", linewidth=0.5)
    for bar, val in zip(bars, bar_vals):
        pct = val / total_checked * 100
        ax1.text(bar.get_x() + bar.get_width() / 2, bar.get_height() + total_checked * 0.01,
                 f"{val:,}\n({pct:.1f}%)", ha="center", va="bottom", fontweight="bold", fontsize=12)
    ax1.set_ylabel("Number of Proven Assertions", fontsize=12)
    subtitle = f"(Total Proven: {total_checked:,})"
    if total_errors > 0:
        subtitle += f"  ({total_errors} vacuity check errors)"
    ax1.set_title(f"Vacuity of Proven Assertions — {label}\n{subtitle}",
                  fontsize=12, fontweight="bold")
    ax1.set_ylim(0, max(bar_vals) * 1.25)
    fig1.tight_layout()
    bar_path = os.path.join(out_dir, "vacuity_results_bar.png")
    fig1.savefig(bar_path, dpi=150)
    plt.close(fig1)
    print(f"  Saved {bar_path}")

    # Pie chart
    fig2, ax2 = plt.subplots(figsize=(7, 5))
    sizes = [total_non_vacuous, total_vacuous]
    labels_pie = [f"Non-Vacuous\n({total_non_vacuous:,})",
                  f"Vacuous\n({total_vacuous:,})"]
    colors = ["#4CAF50", "#FF9800"]
    filtered = [(s, l, c) for s, l, c in zip(sizes, labels_pie, colors) if s > 0]
    if filtered:
        sizes, labels_pie, colors = zip(*filtered)
        wedges, texts, autotexts = ax2.pie(
            sizes, labels=labels_pie, colors=colors, autopct="%1.1f%%",
            startangle=90, pctdistance=0.6,
            wedgeprops=dict(edgecolor="black", linewidth=0.5),
        )
        for t in autotexts:
            t.set_fontsize(12)
            t.set_fontweight("bold")
    ax2.set_title(f"Vacuity Rate — {label}", fontsize=13, fontweight="bold")
    fig2.tight_layout()
    pie_path = os.path.join(out_dir, "vacuity_results_pie.png")
    fig2.savefig(pie_path, dpi=150)
    plt.close(fig2)
    print(f"  Saved {pie_path}")


def count_verif_failures(results_dir):
    """Count IDs that failed verification entirely (no property data) from verif_summary.csv."""
    # verif_summary.csv is at ../visual_data/verif_summary.csv relative to ids/
    visual_data_dir = os.path.join(os.path.dirname(results_dir), "visual_data")
    csv_path = os.path.join(visual_data_dir, "verif_summary.csv")
    total_ids = 0
    fail_ids = 0
    if not os.path.isfile(csv_path):
        return 0, 0
    with open(csv_path, "r", newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            total_ids += 1
            status = row.get("status", "").strip().lower()
            if status == "fail":
                fail_ids += 1
    return total_ids, fail_ids


def run_for_dirs(results_dir, sva_dir, output_csv, chart_label="",
                 syntax_dir=None):
    """Process a single results_dir/sva_dir pair and write output_csv.

    If syntax_dir is provided, also generate syntax assertion charts and
    write assertion_totals.txt alongside the output_csv.
    """
    if not os.path.isdir(results_dir):
        print(f"ERROR: Results directory not found: {results_dir}")
        return

    os.makedirs(os.path.dirname(output_csv), exist_ok=True)

    rows = []
    total_passing = 0
    total_failing = 0
    ids_all_pass = set()   # IDs where every property is proven
    ids_with_cex = set()   # IDs where at least one property has CEX
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
        # Filter JasperGold auto-generated vacuity precondition covers
        # (e.g. "module.inst.prop_name:precondition1") — not user-written cover properties
        all_covers = [c for c in all_covers if ":precondition" not in c]
        cex_props = parse_cex_properties(cex_path)

        passing_asserts = [a for a in all_asserts if a not in cex_props]
        passing_covers = [c for c in all_covers if c not in cex_props]
        failing_asserts = [a for a in all_asserts if a in cex_props]
        failing_covers = [c for c in all_covers if c in cex_props]

        total_passing += len(passing_asserts) + len(passing_covers)
        total_failing += len(failing_asserts) + len(failing_covers)

        # Track per-ID verification outcome
        id_has_cex = len(failing_asserts) + len(failing_covers) > 0
        if id_has_cex:
            ids_with_cex.add(id_name)
        else:
            ids_all_pass.add(id_name)

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

    # Count IDs that failed verification entirely (compile errors etc.)
    # These never produced property_list.txt so aren't counted above
    total_verif_ids, verif_fail_ids = count_verif_failures(results_dir)
    # IDs that had property data were already counted in total_passing/total_failing
    # The remaining fail IDs had no properties at all
    ids_with_properties = set()
    for id_name in sorted(os.listdir(results_dir)):
        id_path = os.path.join(results_dir, id_name)
        if os.path.isdir(id_path) and os.path.exists(os.path.join(id_path, "property_list.txt")):
            ids_with_properties.add(id_name)
    ids_without_properties = total_verif_ids - len(ids_with_properties)

    # Generate pass/fail chart in the same visual_data directory
    visual_data_dir = os.path.dirname(output_csv)
    generate_pass_fail_chart(
        total_passing, total_failing, chart_label, visual_data_dir,
        compile_fail_ids=ids_without_properties,
        total_ids=total_verif_ids,
    )

    # Generate verification pass/fail by ID count chart
    generate_verif_id_chart(
        len(ids_all_pass), len(ids_with_cex), ids_without_properties,
        chart_label, visual_data_dir,
    )

    # Generate auto-bind usage chart
    generate_auto_bind_chart(results_dir, chart_label, visual_data_dir)

    # Generate vacuity (false positive) chart
    generate_vacuity_chart(results_dir, chart_label, visual_data_dir)

    # Syntax assertion charts
    if syntax_dir and os.path.isdir(syntax_dir):
        generate_syntax_assertion_chart(syntax_dir, sva_dir, chart_label)


def generate_verif_id_chart(all_pass_count, cex_count, compile_fail_count,
                            label, out_dir):
    """Generate bar chart: verification outcome by ID count."""
    total = all_pass_count + cex_count + compile_fail_count
    if total == 0:
        return
    os.makedirs(out_dir, exist_ok=True)

    fig, ax = plt.subplots(figsize=(8, 5))
    categories = ["All Proven", "Has CEX", "Compile Failed"]
    values = [all_pass_count, cex_count, compile_fail_count]
    colors = ["#4CAF50", "#F44336", "#9E9E9E"]
    bars = ax.bar(categories, values, color=colors, edgecolor="black", linewidth=0.5)
    for bar, val in zip(bars, values):
        if val > 0:
            pct = val / total * 100
            ax.text(bar.get_x() + bar.get_width() / 2,
                    bar.get_height() + total * 0.01,
                    f"{val:,}\n({pct:.1f}%)", ha="center", va="bottom",
                    fontweight="bold", fontsize=11)
    ax.set_ylabel("Number of IDs", fontsize=12)
    ax.set_title(f"Verification Outcome by ID Count — {label}\n(Total: {total:,} IDs)",
                 fontsize=12, fontweight="bold")
    ax.set_ylim(0, max(values + [1]) * 1.25)
    fig.tight_layout()
    path = os.path.join(out_dir, "verif_pass_fail_ids_bar.png")
    fig.savefig(path, dpi=150)
    plt.close(fig)
    print(f"  Saved {path}")


def generate_syntax_assertion_chart(syntax_dir, sva_dir, label):
    """Generate bar chart of assertions in syntax-passing vs syntax-failing files.

    syntax_dir: e.g. inference_outputs/syntax_results/{model}
    sva_dir:    e.g. inference_outputs/{model}  (contains {id}/sva.sv)
    """
    csv_path = os.path.join(syntax_dir, "visual_data", "summary.csv")
    if not os.path.isfile(csv_path):
        print(f"  No syntax summary.csv found for {label}, skipping syntax assertion chart")
        return

    passing_ids = set()
    failing_ids = set()
    with open(csv_path, newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            sid = row["id"].strip()
            status = row["status"].strip().lower()
            if status == "ok":
                passing_ids.add(sid)
            elif status == "fail":
                failing_ids.add(sid)

    pass_assertions = 0
    fail_assertions = 0
    pass_props = 0
    fail_props = 0

    all_ids = passing_ids | failing_ids
    for sid in all_ids:
        sva_path = os.path.join(sva_dir, sid, "sva.sv")
        if not os.path.isfile(sva_path):
            continue
        try:
            with open(sva_path, "r", encoding="utf-8", errors="replace") as f:
                text = f.read()
        except (OSError, IOError):
            continue
        n_assert = len(RE_ASSERT.findall(text))
        n_cover  = len(RE_COVER.findall(text))
        n_assume = len(RE_ASSUME.findall(text))
        n_total  = n_assert + n_cover + n_assume
        if sid in passing_ids:
            pass_assertions += n_assert
            pass_props += n_total
        else:
            fail_assertions += n_assert
            fail_props += n_total

    total_assertions = pass_assertions + fail_assertions
    total_props = pass_props + fail_props
    if total_assertions == 0 and total_props == 0:
        return

    out_dir = os.path.join(syntax_dir, "visual_data")
    os.makedirs(out_dir, exist_ok=True)

    # Bar chart — assertions
    fig, ax = plt.subplots(figsize=(7, 5))
    bars = ax.bar(
        ["Passing", "Failing"],
        [pass_assertions, fail_assertions],
        color=["#4CAF50", "#F44336"], edgecolor="black", linewidth=0.5,
    )
    for bar, val in zip(bars, [pass_assertions, fail_assertions]):
        ax.text(bar.get_x() + bar.get_width() / 2,
                bar.get_height() + total_assertions * 0.01,
                f"{val:,}", ha="center", va="bottom", fontweight="bold", fontsize=12)
    subtitle = (f"(Total: {total_assertions:,} assertions)\n"
                f"{len(failing_ids)} of {len(all_ids)} IDs failed syntax")
    ax.set_ylabel("Number of Assertions", fontsize=12)
    ax.set_title(f"Syntax Pass/Fail by Assertion Count — {label}\n{subtitle}",
                 fontsize=12, fontweight="bold")
    ax.set_ylim(0, max(pass_assertions, fail_assertions, 1) * 1.25)
    fig.tight_layout()
    path = os.path.join(out_dir, "syntax_pass_fail_assertions_bar.png")
    fig.savefig(path, dpi=150)
    plt.close(fig)
    print(f"  Saved {path}")

    # Bar chart — all properties (assert+cover+assume)
    if total_props > 0 and total_props != total_assertions:
        fig2, ax2 = plt.subplots(figsize=(7, 5))
        bars2 = ax2.bar(
            ["Passing", "Failing"],
            [pass_props, fail_props],
            color=["#4CAF50", "#F44336"], edgecolor="black", linewidth=0.5,
        )
        for bar, val in zip(bars2, [pass_props, fail_props]):
            ax2.text(bar.get_x() + bar.get_width() / 2,
                     bar.get_height() + total_props * 0.01,
                     f"{val:,}", ha="center", va="bottom", fontweight="bold", fontsize=12)
        subtitle2 = (f"(Total: {total_props:,} properties)\n"
                     f"{len(failing_ids)} of {len(all_ids)} IDs failed syntax")
        ax2.set_ylabel("Number of Properties", fontsize=12)
        ax2.set_title(f"Syntax Pass/Fail by Property Count — {label}\n{subtitle2}",
                      fontsize=12, fontweight="bold")
        ax2.set_ylim(0, max(pass_props, fail_props, 1) * 1.25)
        fig2.tight_layout()
        path2 = os.path.join(out_dir, "syntax_pass_fail_properties_bar.png")
        fig2.savefig(path2, dpi=150)
        plt.close(fig2)
        print(f"  Saved {path2}")

    # Bar chart — IDs
    n_pass_ids = len(passing_ids)
    n_fail_ids = len(failing_ids)
    total_ids = n_pass_ids + n_fail_ids
    if total_ids > 0:
        fig3, ax3 = plt.subplots(figsize=(7, 5))
        bars3 = ax3.bar(
            ["Passing", "Failing"],
            [n_pass_ids, n_fail_ids],
            color=["#4CAF50", "#F44336"], edgecolor="black", linewidth=0.5,
        )
        for bar, val in zip(bars3, [n_pass_ids, n_fail_ids]):
            pct = val / total_ids * 100
            ax3.text(bar.get_x() + bar.get_width() / 2,
                     bar.get_height() + total_ids * 0.01,
                     f"{val:,}\n({pct:.1f}%)", ha="center", va="bottom",
                     fontweight="bold", fontsize=12)
        ax3.set_ylabel("Number of IDs", fontsize=12)
        ax3.set_title(f"Syntax Pass/Fail by ID Count — {label}\n(Total: {total_ids:,} IDs)",
                      fontsize=12, fontweight="bold")
        ax3.set_ylim(0, max(n_pass_ids, n_fail_ids, 1) * 1.25)
        fig3.tight_layout()
        path3 = os.path.join(out_dir, "syntax_pass_fail_ids_bar.png")
        fig3.savefig(path3, dpi=150)
        plt.close(fig3)
        print(f"  Saved {path3}")


def main():
    parser = argparse.ArgumentParser(description="Generate CSV of passing assertions")
    parser.add_argument("--dataset", required=True,
                        choices=list(DATASET_CONFIGS.keys()) + ["inference_outputs"],
                        help="Dataset to process")
    parser.add_argument("--version", type=int,
                        help="Dataset version number (required for veri_thoughts/metrex)")
    args = parser.parse_args()

    if args.dataset == "inference_outputs":
        io_base = os.path.join(BASE_DIR, "inference_outputs")
        verif_base = os.path.join(io_base, "verification_results")
        syntax_base = os.path.join(io_base, "syntax_results")
        if not os.path.isdir(verif_base):
            print(f"ERROR: {verif_base} not found")
            return
        for model_name in sorted(os.listdir(verif_base)):
            model_verif = os.path.join(verif_base, model_name)
            if not os.path.isdir(model_verif):
                continue
            results_dir = os.path.join(model_verif, "ids")
            sva_dir = os.path.join(io_base, model_name)
            output_csv = os.path.join(model_verif, "visual_data", "passing_assertions.csv")
            print(f"\n=== Processing {model_name} ===")
            model_syntax_dir = os.path.join(syntax_base, model_name)
            run_for_dirs(results_dir, sva_dir, output_csv, chart_label=model_name,
                         syntax_dir=model_syntax_dir if os.path.isdir(model_syntax_dir) else None)
    else:
        if args.version is None:
            parser.error("--version is required for veri_thoughts/metrex")
        cfg = DATASET_CONFIGS[args.dataset]
        results_dir = cfg["results_dir"].format(base=BASE_DIR, ver=args.version)
        sva_dir = cfg["sva_dir"].format(base=BASE_DIR, ver=args.version)
        output_csv = cfg["output_csv"].format(base=BASE_DIR, ver=args.version)
        # Detect syntax_results dir
        syntax_dir = os.path.join(
            BASE_DIR, args.dataset, "dataset", "syntax_results",
            f"version_{args.version}",
        )
        run_for_dirs(results_dir, sva_dir, output_csv,
                     chart_label=f"{args.dataset} v{args.version}",
                     syntax_dir=syntax_dir if os.path.isdir(syntax_dir) else None)


if __name__ == "__main__":
    main()
