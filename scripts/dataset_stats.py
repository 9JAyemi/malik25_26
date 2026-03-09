#!/usr/bin/env python3
"""
Parse metrex and veri_thoughts datasets to produce statistical charts.

Usage:
    python scripts/dataset_stats.py [--base-dir <workspace_root>] [--out <output_dir>]

    Defaults:
        --base-dir  .                (expects metrex/ and veri_thoughts/ subdirs)
        --out       dataset_stats    (created inside base-dir)

Customisation:
    Edit the CHART_CONFIG dict below to control which chart types are
    generated for each data metric.  Each key is a metric name and its
    value is either:

      - A list of chart types to produce (pick from the VALID_CHART_TYPES
        set below), OR
      - False / an empty list to skip that metric entirely.

    The same configuration drives **both** the combined (comparison) charts
    and the per-dataset individual charts.
"""

import argparse
import glob
import json
import os
import re
import sys
from collections import defaultdict
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.ticker as mticker
import numpy as np

# ── Regex to count SVA properties ────────────────────────────────────────────
RE_ASSERT = re.compile(r'\bassert\s+property\b', re.IGNORECASE)
RE_COVER  = re.compile(r'\bcover\s+property\b',  re.IGNORECASE)
RE_ASSUME = re.compile(r'\bassume\s+property\b',  re.IGNORECASE)


# ── Chart configuration ──────────────────────────────────────────────────────
# Valid chart types you can choose from:
#   "histogram"       – frequency histogram
#   "histogram_log"   – frequency histogram with log-y axis
#   "boxplot"         – box-and-whisker plot
#   "cdf"             – cumulative distribution function curve
#   "scatter"         – scatter plot  (only for paired metrics)
#   "stacked_bar"     – stacked bar of assert/cover/assume breakdown
#
# Edit the lists below to add or remove chart types for each metric.
# Set a metric to [] or False to skip it entirely.

CHART_CONFIG = {
    # ── Distribution metrics (support: histogram, histogram_log, boxplot, strip, cdf) ──
    "module_loc": ["histogram", "histogram_log", "strip", "cdf"],
    "sva_loc":    ["histogram", "strip", "cdf"],
    "sva_properties":  ["histogram", "strip", "cdf"],
    "sva_assertions":  ["histogram"],

    # ── Relationship metrics (support: scatter) ──
    "module_loc_vs_sva_loc":    ["scatter"],
    "module_loc_vs_sva_props":  ["scatter"],

    # ── Breakdown metrics (support: stacked_bar) ──
    "property_breakdown": ["stacked_bar"],
}

VALID_CHART_TYPES = {"histogram", "histogram_log", "boxplot", "strip", "cdf",
                     "scatter", "stacked_bar"}


def _enabled(metric: str, chart_type: str) -> bool:
    """Return True if chart_type is enabled for metric in CHART_CONFIG."""
    types = CHART_CONFIG.get(metric)
    if not types:
        return False
    return chart_type in types


# ── Helpers ──────────────────────────────────────────────────────────────────
def count_lines(filepath: str) -> int:
    """Return the number of non-empty, non-comment-only lines in a file."""
    try:
        with open(filepath, "r", encoding="utf-8", errors="replace") as f:
            lines = f.readlines()
    except (OSError, IOError):
        return 0
    count = 0
    in_block_comment = False
    for line in lines:
        stripped = line.strip()
        if not stripped:
            continue
        # Handle block comments
        if in_block_comment:
            if "*/" in stripped:
                in_block_comment = False
            continue
        if stripped.startswith("/*"):
            if "*/" not in stripped[2:]:
                in_block_comment = True
            continue
        if stripped.startswith("//"):
            continue
        count += 1
    return count


def count_total_lines(filepath: str) -> int:
    """Return raw line count of a file."""
    try:
        with open(filepath, "r", encoding="utf-8", errors="replace") as f:
            return sum(1 for _ in f)
    except (OSError, IOError):
        return 0


def count_sva_properties(filepath: str) -> dict:
    """Count assert property, cover property, assume property in an SVA file."""
    try:
        with open(filepath, "r", encoding="utf-8", errors="replace") as f:
            text = f.read()
    except (OSError, IOError):
        return {"assert": 0, "cover": 0, "assume": 0, "total": 0}
    n_assert = len(RE_ASSERT.findall(text))
    n_cover  = len(RE_COVER.findall(text))
    n_assume = len(RE_ASSUME.findall(text))
    return {
        "assert": n_assert,
        "cover": n_cover,
        "assume": n_assume,
        "total": n_assert + n_cover + n_assume,
    }


def file_size_bytes(filepath: str) -> int:
    try:
        return os.path.getsize(filepath)
    except OSError:
        return 0


def scan_dataset(dataset_dir: str, label: str) -> list[dict]:
    """
    Scan a dataset's version_1 directory and collect per-ID stats.
    Returns list of dicts with keys:
        id, label, module_name, module_loc, module_total_lines, module_bytes,
        sva_loc, sva_total_lines, sva_bytes, sva_asserts, sva_covers,
        sva_assumes, sva_total_props
    """
    version_dir = os.path.join(dataset_dir, "version_1")
    if not os.path.isdir(version_dir):
        print(f"WARNING: {version_dir} not found, skipping {label}")
        return []

    entries = sorted(os.listdir(version_dir))
    records = []
    for entry in entries:
        entry_path = os.path.join(version_dir, entry)
        if not os.path.isdir(entry_path):
            continue
        # Skip non-numeric directories
        if not entry.isdigit():
            continue

        module_path = os.path.join(entry_path, "module.v")
        sva_path = os.path.join(entry_path, "sva.sv")
        meta_path = os.path.join(entry_path, "metadata.json")

        module_name = entry  # fallback
        if os.path.isfile(meta_path):
            try:
                with open(meta_path, "r", encoding="utf-8") as f:
                    meta = json.load(f)
                module_name = meta.get("module_name", entry)
            except (json.JSONDecodeError, OSError):
                pass

        module_loc = count_lines(module_path) if os.path.isfile(module_path) else 0
        module_total = count_total_lines(module_path) if os.path.isfile(module_path) else 0
        module_bytes = file_size_bytes(module_path) if os.path.isfile(module_path) else 0

        sva_loc = count_lines(sva_path) if os.path.isfile(sva_path) else 0
        sva_total = count_total_lines(sva_path) if os.path.isfile(sva_path) else 0
        sva_bytes = file_size_bytes(sva_path) if os.path.isfile(sva_path) else 0
        sva_props = count_sva_properties(sva_path) if os.path.isfile(sva_path) else {
            "assert": 0, "cover": 0, "assume": 0, "total": 0
        }

        records.append({
            "id": entry,
            "label": label,
            "module_name": module_name,
            "module_loc": module_loc,
            "module_total_lines": module_total,
            "module_bytes": module_bytes,
            "sva_loc": sva_loc,
            "sva_total_lines": sva_total,
            "sva_bytes": sva_bytes,
            "sva_asserts": sva_props["assert"],
            "sva_covers": sva_props["cover"],
            "sva_assumes": sva_props["assume"],
            "sva_total_props": sva_props["total"],
        })

    return records


def print_summary(records: list[dict], label: str):
    """Print a textual summary of dataset stats."""
    if not records:
        print(f"\n  {label}: no records found\n")
        return

    mod_locs = [r["module_loc"] for r in records if r["module_loc"] > 0]
    sva_locs = [r["sva_loc"] for r in records if r["sva_loc"] > 0]
    sva_props = [r["sva_total_props"] for r in records if r["sva_total_props"] > 0]
    sva_asserts = [r["sva_asserts"] for r in records if r["sva_asserts"] > 0]

    print(f"\n{'=' * 60}")
    print(f"  {label} — {len(records)} design IDs")
    print(f"{'=' * 60}")
    print(f"  Module LOC (non-blank, non-comment):")
    if mod_locs:
        print(f"    count={len(mod_locs)}  min={min(mod_locs)}  "
              f"median={int(np.median(mod_locs))}  mean={np.mean(mod_locs):.1f}  "
              f"max={max(mod_locs)}")
    print(f"  SVA LOC (non-blank, non-comment):")
    if sva_locs:
        print(f"    count={len(sva_locs)}  min={min(sva_locs)}  "
              f"median={int(np.median(sva_locs))}  mean={np.mean(sva_locs):.1f}  "
              f"max={max(sva_locs)}")
    print(f"  SVA total properties (assert+cover+assume):")
    if sva_props:
        print(f"    count={len(sva_props)}  min={min(sva_props)}  "
              f"median={int(np.median(sva_props))}  mean={np.mean(sva_props):.1f}  "
              f"max={max(sva_props)}")
    print(f"  SVA assertions only:")
    if sva_asserts:
        print(f"    count={len(sva_asserts)}  min={min(sva_asserts)}  "
              f"median={int(np.median(sva_asserts))}  mean={np.mean(sva_asserts):.1f}  "
              f"max={max(sva_asserts)}")


# ── Plotting helpers ─────────────────────────────────────────────────────────
COLORS = {
    "metrex": "#2196F3",
    "veri_thoughts": "#FF9800",
    "assert": "#4CAF50",
    "cover": "#9C27B0",
    "assume": "#F44336",
}


def plot_histogram_comparison(data_a, data_b, label_a, label_b,
                              xlabel, title, out_path, bins=50, log_y=False):
    """Side-by-side overlapping histogram for two datasets."""
    fig, ax = plt.subplots(figsize=(10, 5))
    all_vals = list(data_a) + list(data_b)
    if not all_vals:
        plt.close(fig)
        return
    lo, hi = 0, np.percentile(all_vals, 99) if len(all_vals) > 10 else max(all_vals)
    bins_arr = np.linspace(lo, hi, bins + 1)
    ax.hist(data_a, bins=bins_arr, alpha=0.6, color=COLORS.get(label_a, "#2196F3"),
            edgecolor="black", linewidth=0.4, label=f"{label_a} (n={len(data_a)})")
    ax.hist(data_b, bins=bins_arr, alpha=0.6, color=COLORS.get(label_b, "#FF9800"),
            edgecolor="black", linewidth=0.4, label=f"{label_b} (n={len(data_b)})")
    ax.set_xlabel(xlabel, fontsize=12)
    ax.set_ylabel("Number of Design IDs", fontsize=12)
    ax.set_title(title, fontsize=14, fontweight="bold")
    if log_y:
        ax.set_yscale("log")
    ax.legend(fontsize=11)
    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    print(f"  Saved {out_path}")


def plot_boxplot_comparison(data_dict, ylabel, title, out_path):
    """Side-by-side box plots."""
    fig, ax = plt.subplots(figsize=(8, 5))
    labels = list(data_dict.keys())
    data = [data_dict[k] for k in labels]
    bp = ax.boxplot(data, labels=labels, patch_artist=True, showmeans=True,
                    meanprops=dict(marker='D', markerfacecolor='red', markersize=6))
    colors = [COLORS.get(k, "#888888") for k in labels]
    for patch, c in zip(bp["boxes"], colors):
        patch.set_facecolor(c)
        patch.set_alpha(0.5)
    ax.set_ylabel(ylabel, fontsize=12)
    ax.set_title(title, fontsize=14, fontweight="bold")
    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    print(f"  Saved {out_path}")


def plot_strip_comparison(data_dict, ylabel, title, out_path):
    """Scatter-strip plot: each design as a dot, one column per dataset."""
    fig, ax = plt.subplots(figsize=(10, 6))
    labels = list(data_dict.keys())
    for i, lbl in enumerate(labels):
        vals = data_dict[lbl]
        if not vals:
            continue
        color = COLORS.get(lbl, "#888888")
        # Jitter x-positions for visibility
        jitter = np.random.default_rng(42).uniform(-0.15, 0.15, size=len(vals))
        xs = np.full(len(vals), i) + jitter
        ax.scatter(xs, vals, alpha=0.25, s=10, color=color,
                   label=f"{lbl} (n={len(vals)})")
        # Overlay median & mean markers
        med = np.median(vals)
        avg = np.mean(vals)
        ax.plot(i, med, marker="_", color="black", markersize=20, markeredgewidth=2.5,
                zorder=5)
        ax.plot(i, avg, marker="D", color="red", markersize=6, zorder=5)
    ax.set_xticks(range(len(labels)))
    ax.set_xticklabels(labels, fontsize=12)
    ax.set_ylabel(ylabel, fontsize=12)
    ax.set_title(title, fontsize=14, fontweight="bold")
    ax.legend(fontsize=10, markerscale=3)
    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    print(f"  Saved {out_path}")


def plot_stacked_bar_comparison(metrex_vals, vt_vals, title, out_path):
    """Stacked bar chart: asserts, covers, assumes per dataset."""
    fig, ax = plt.subplots(figsize=(8, 5))
    labels = ["metrex", "veri_thoughts"]
    asserts = [np.mean([r["sva_asserts"] for r in metrex_vals]) if metrex_vals else 0,
               np.mean([r["sva_asserts"] for r in vt_vals]) if vt_vals else 0]
    covers = [np.mean([r["sva_covers"] for r in metrex_vals]) if metrex_vals else 0,
              np.mean([r["sva_covers"] for r in vt_vals]) if vt_vals else 0]
    assumes = [np.mean([r["sva_assumes"] for r in metrex_vals]) if metrex_vals else 0,
               np.mean([r["sva_assumes"] for r in vt_vals]) if vt_vals else 0]

    x = np.arange(len(labels))
    width = 0.4
    b1 = ax.bar(x, asserts, width, label="Assertions", color=COLORS["assert"],
                edgecolor="black", linewidth=0.5)
    b2 = ax.bar(x, covers, width, bottom=asserts, label="Covers", color=COLORS["cover"],
                edgecolor="black", linewidth=0.5)
    bottom2 = [a + c for a, c in zip(asserts, covers)]
    b3 = ax.bar(x, assumes, width, bottom=bottom2, label="Assumes", color=COLORS["assume"],
                edgecolor="black", linewidth=0.5)

    # Annotate totals
    for i, (a, c, s) in enumerate(zip(asserts, covers, assumes)):
        total = a + c + s
        ax.text(i, total + 0.2, f"{total:.1f}", ha="center", fontweight="bold", fontsize=11)

    ax.set_xticks(x)
    ax.set_xticklabels(labels, fontsize=12)
    ax.set_ylabel("Avg SVA Properties per File", fontsize=12)
    ax.set_title(title, fontsize=14, fontweight="bold")
    ax.legend(fontsize=10)
    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    print(f"  Saved {out_path}")


def plot_scatter(records, x_key, y_key, xlabel, ylabel, title, out_path, label_key="label"):
    """Scatter plot colored by dataset label."""
    fig, ax = plt.subplots(figsize=(10, 6))
    for lbl, color in COLORS.items():
        if lbl not in ("metrex", "veri_thoughts"):
            continue
        subset = [r for r in records if r[label_key] == lbl]
        if not subset:
            continue
        xs = [r[x_key] for r in subset]
        ys = [r[y_key] for r in subset]
        ax.scatter(xs, ys, alpha=0.25, s=12, color=color, label=f"{lbl} (n={len(subset)})")
    ax.set_xlabel(xlabel, fontsize=12)
    ax.set_ylabel(ylabel, fontsize=12)
    ax.set_title(title, fontsize=14, fontweight="bold")
    ax.legend(fontsize=11, markerscale=3)
    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    print(f"  Saved {out_path}")


# ── Single-dataset plotting helpers ──────────────────────────────────────────

def plot_histogram_single(data, label, xlabel, title, out_path, bins=50, log_y=False):
    """Histogram for a single dataset."""
    fig, ax = plt.subplots(figsize=(10, 5))
    if not data:
        plt.close(fig)
        return
    lo, hi = 0, np.percentile(data, 99) if len(data) > 10 else max(data)
    bins_arr = np.linspace(lo, hi, bins + 1)
    ax.hist(data, bins=bins_arr, alpha=0.75, color=COLORS.get(label, "#2196F3"),
            edgecolor="black", linewidth=0.4, label=f"{label} (n={len(data)})")
    ax.set_xlabel(xlabel, fontsize=12)
    ax.set_ylabel("Number of Design IDs", fontsize=12)
    ax.set_title(title, fontsize=14, fontweight="bold")
    if log_y:
        ax.set_yscale("log")
    ax.legend(fontsize=11)
    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    print(f"  Saved {out_path}")


def plot_boxplot_single(data, label, ylabel, title, out_path):
    """Box plot for a single dataset."""
    fig, ax = plt.subplots(figsize=(6, 5))
    if not data:
        plt.close(fig)
        return
    bp = ax.boxplot([data], labels=[label], patch_artist=True, showmeans=True,
                    meanprops=dict(marker='D', markerfacecolor='red', markersize=6))
    bp["boxes"][0].set_facecolor(COLORS.get(label, "#888888"))
    bp["boxes"][0].set_alpha(0.5)
    ax.set_ylabel(ylabel, fontsize=12)
    ax.set_title(title, fontsize=14, fontweight="bold")
    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    print(f"  Saved {out_path}")


def plot_strip_single(data, label, ylabel, title, out_path):
    """Scatter-strip plot for a single dataset: each design as a dot."""
    fig, ax = plt.subplots(figsize=(10, 5))
    if not data:
        plt.close(fig)
        return
    color = COLORS.get(label, "#2196F3")
    xs = np.arange(len(data))
    ax.scatter(xs, sorted(data), alpha=0.35, s=10, color=color,
              label=f"{label} (n={len(data)})")
    # Overlay median & mean lines
    med = np.median(data)
    avg = np.mean(data)
    ax.axhline(med, color="black", linewidth=1.2, linestyle="--", label=f"median={med:.0f}")
    ax.axhline(avg, color="red", linewidth=1.2, linestyle=":", label=f"mean={avg:.1f}")
    ax.set_xlabel("Designs (sorted by value)", fontsize=12)
    ax.set_ylabel(ylabel, fontsize=12)
    ax.set_title(title, fontsize=14, fontweight="bold")
    ax.legend(fontsize=10, markerscale=3)
    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    print(f"  Saved {out_path}")


def _annotate_cdf_cutoffs(ax, sorted_d, cdf, color, percentiles=(0.90, 0.95, 0.99)):
    """Add vertical dashed lines at key percentile cutoffs on a CDF axis."""
    line_styles = {0.90: ":", 0.95: "--", 0.99: "-."}
    for p in percentiles:
        idx = np.searchsorted(cdf, p)
        if idx >= len(sorted_d):
            idx = len(sorted_d) - 1
        x_val = sorted_d[idx]
        y_val = cdf[idx]
        ax.axvline(x_val, color=color, linestyle=line_styles.get(p, "--"),
                   linewidth=0.9, alpha=0.7)
        ax.annotate(f"{p:.0%} @ {x_val:.0f}",
                    xy=(x_val, y_val), fontsize=8, color=color,
                    textcoords="offset points", xytext=(6, -12),
                    arrowprops=dict(arrowstyle="->", color=color, lw=0.7))
    # Mark the max value
    max_val = sorted_d[-1]
    second_last_y = cdf[-2] if len(cdf) > 1 else 0.0
    ax.axvline(max_val, color=color, linestyle="-", linewidth=1.0, alpha=0.5)
    ax.plot(max_val, 1.0, marker="o", color=color, markersize=5, zorder=5)
    ax.annotate(f"max={max_val:.0f}\n({second_last_y:.1%} before)",
                xy=(max_val, 1.0), fontsize=8, color=color,
                textcoords="offset points", xytext=(6, -18),
                arrowprops=dict(arrowstyle="->", color=color, lw=0.7))


def plot_cdf_single(data, label, xlabel, title, out_path):
    """CDF curve for a single dataset with percentile cutoff annotations."""
    fig, ax = plt.subplots(figsize=(10, 5))
    if not data:
        plt.close(fig)
        return
    sorted_d = np.sort(data)
    cdf = np.arange(1, len(sorted_d) + 1) / len(sorted_d)
    color = COLORS.get(label, "#2196F3")
    ax.plot(sorted_d, cdf, linewidth=2, color=color,
            label=f"{label} (n={len(data)})")
    _annotate_cdf_cutoffs(ax, sorted_d, cdf, color)
    ax.set_xlabel(xlabel, fontsize=12)
    ax.set_ylabel("Cumulative Proportion", fontsize=12)
    ax.set_title(title, fontsize=14, fontweight="bold")
    ax.legend(fontsize=11)
    ax.grid(True, alpha=0.3)
    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    print(f"  Saved {out_path}")


def plot_scatter_single(records, label, x_key, y_key, xlabel, ylabel, title, out_path):
    """Scatter plot for a single dataset."""
    fig, ax = plt.subplots(figsize=(10, 6))
    if not records:
        plt.close(fig)
        return
    xs = [r[x_key] for r in records]
    ys = [r[y_key] for r in records]
    ax.scatter(xs, ys, alpha=0.25, s=12, color=COLORS.get(label, "#2196F3"),
              label=f"{label} (n={len(records)})")
    ax.set_xlabel(xlabel, fontsize=12)
    ax.set_ylabel(ylabel, fontsize=12)
    ax.set_title(title, fontsize=14, fontweight="bold")
    ax.legend(fontsize=11, markerscale=3)
    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    print(f"  Saved {out_path}")


def plot_stacked_bar_single(records, label, title, out_path):
    """Stacked bar chart: asserts, covers, assumes for one dataset."""
    fig, ax = plt.subplots(figsize=(6, 5))
    if not records:
        plt.close(fig)
        return
    avg_asserts = np.mean([r["sva_asserts"] for r in records])
    avg_covers = np.mean([r["sva_covers"] for r in records])
    avg_assumes = np.mean([r["sva_assumes"] for r in records])

    x = np.array([0])
    width = 0.4
    ax.bar(x, [avg_asserts], width, label="Assertions", color=COLORS["assert"],
           edgecolor="black", linewidth=0.5)
    ax.bar(x, [avg_covers], width, bottom=[avg_asserts], label="Covers", color=COLORS["cover"],
           edgecolor="black", linewidth=0.5)
    ax.bar(x, [avg_assumes], width, bottom=[avg_asserts + avg_covers], label="Assumes",
           color=COLORS["assume"], edgecolor="black", linewidth=0.5)

    total = avg_asserts + avg_covers + avg_assumes
    ax.text(0, total + 0.2, f"{total:.1f}", ha="center", fontweight="bold", fontsize=11)

    ax.set_xticks(x)
    ax.set_xticklabels([label], fontsize=12)
    ax.set_ylabel("Avg SVA Properties per File", fontsize=12)
    ax.set_title(title, fontsize=14, fontweight="bold")
    ax.legend(fontsize=10)
    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    print(f"  Saved {out_path}")


def generate_charts_for_dataset(records, label, out_dir):
    """Generate chart types for a single dataset, driven by CHART_CONFIG."""
    os.makedirs(out_dir, exist_ok=True)

    mod_loc = [r["module_loc"] for r in records if r["module_loc"] > 0]
    sva_loc = [r["sva_loc"] for r in records if r["sva_loc"] > 0]
    sva_props = [r["sva_total_props"] for r in records if r["sva_total_props"] > 0]
    sva_asserts = [r["sva_asserts"] for r in records if r["sva_asserts"] > 0]

    print(f"\nGenerating individual charts for {label} …")

    # ── Distribution metrics ──
    dist_metrics = [
        ("module_loc",     mod_loc,     "Module Lines of Code (non-blank, non-comment)",  "Module LOC"),
        ("sva_loc",        sva_loc,     "SVA Lines of Code (non-blank, non-comment)",     "SVA LOC"),
        ("sva_properties", sva_props,   "Number of SVA Properties (assert + cover + assume)", "SVA Properties per File"),
        ("sva_assertions", sva_asserts, "Number of Assertions (assert property)",         "Assertions per SVA File"),
    ]

    for metric_key, data, xlabel_long, ylabel_short in dist_metrics:
        if _enabled(metric_key, "histogram"):
            plot_histogram_single(
                data, label,
                xlabel=xlabel_long,
                title=f"{ylabel_short} Distribution — {label}",
                out_path=os.path.join(out_dir, f"hist_{metric_key}.png"),
            )
        if _enabled(metric_key, "histogram_log"):
            plot_histogram_single(
                data, label,
                xlabel=ylabel_short,
                title=f"{ylabel_short} Distribution (log scale) — {label}",
                out_path=os.path.join(out_dir, f"hist_{metric_key}_log.png"),
                log_y=True,
            )
        if _enabled(metric_key, "boxplot"):
            plot_boxplot_single(
                data, label,
                ylabel=ylabel_short,
                title=f"{ylabel_short} Box Plot — {label}",
                out_path=os.path.join(out_dir, f"boxplot_{metric_key}.png"),
            )
        if _enabled(metric_key, "strip"):
            plot_strip_single(
                data, label,
                ylabel=ylabel_short,
                title=f"{ylabel_short} per Design — {label}",
                out_path=os.path.join(out_dir, f"strip_{metric_key}.png"),
            )
        if _enabled(metric_key, "cdf"):
            plot_cdf_single(
                data, label,
                xlabel=ylabel_short,
                title=f"CDF of {ylabel_short} — {label}",
                out_path=os.path.join(out_dir, f"cdf_{metric_key}.png"),
            )

    # ── Scatter metrics ──
    if _enabled("module_loc_vs_sva_loc", "scatter"):
        scatter_recs = [r for r in records if r["module_loc"] > 0 and r["sva_loc"] > 0]
        plot_scatter_single(
            scatter_recs, label,
            x_key="module_loc", y_key="sva_loc",
            xlabel="Module LOC", ylabel="SVA LOC",
            title=f"Module LOC vs SVA LOC — {label}",
            out_path=os.path.join(out_dir, "scatter_module_vs_sva_loc.png"),
        )
    if _enabled("module_loc_vs_sva_props", "scatter"):
        scatter_recs2 = [r for r in records if r["module_loc"] > 0 and r["sva_total_props"] > 0]
        plot_scatter_single(
            scatter_recs2, label,
            x_key="module_loc", y_key="sva_total_props",
            xlabel="Module LOC", ylabel="Number of SVA Properties",
            title=f"Module LOC vs Number of SVA Properties — {label}",
            out_path=os.path.join(out_dir, "scatter_module_loc_vs_props.png"),
        )

    # ── Stacked bar: property breakdown ──
    if _enabled("property_breakdown", "stacked_bar"):
        plot_stacked_bar_single(
            records, label,
            title=f"Avg SVA Property Breakdown per File — {label}\n(Assertions / Covers / Assumes)",
            out_path=os.path.join(out_dir, "bar_avg_property_breakdown.png"),
        )

    print(f"  All {label} charts saved to {out_dir}")


def plot_cdf_comparison(data_a, data_b, label_a, label_b,
                        xlabel, title, out_path):
    """Overlapping CDF curves for two datasets with percentile cutoff annotations."""
    fig, ax = plt.subplots(figsize=(11, 5))
    for data, lbl, c in [(data_a, label_a, COLORS.get(label_a, "#2196F3")),
                          (data_b, label_b, COLORS.get(label_b, "#FF9800"))]:
        if not data:
            continue
        sorted_d = np.sort(data)
        cdf = np.arange(1, len(sorted_d) + 1) / len(sorted_d)
        ax.plot(sorted_d, cdf, linewidth=2, color=c, label=f"{lbl} (n={len(data)})")
        _annotate_cdf_cutoffs(ax, sorted_d, cdf, c)
    ax.set_xlabel(xlabel, fontsize=12)
    ax.set_ylabel("Cumulative Proportion", fontsize=12)
    ax.set_title(title, fontsize=14, fontweight="bold")
    ax.legend(fontsize=11)
    ax.grid(True, alpha=0.3)
    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    print(f"  Saved {out_path}")


# ── Main ─────────────────────────────────────────────────────────────────────
def main():
    parser = argparse.ArgumentParser(
        description="Generate statistical charts for metrex and veri_thoughts datasets."
    )
    # Default base-dir to the parent of this script's directory (i.e. malik25_26/)
    _script_dir = os.path.dirname(os.path.abspath(__file__))
    _default_base = os.path.dirname(_script_dir)

    parser.add_argument(
        "--base-dir", "-b", default=_default_base,
        help="Workspace root containing metrex/ and veri_thoughts/ subdirs "
             f"(default: {_default_base})",
    )
    parser.add_argument(
        "--out", "-o", default=None,
        help="Output directory for PNGs and CSVs (default: <base-dir>/dataset_stats)",
    )
    args = parser.parse_args()

    base = os.path.abspath(args.base_dir)
    out_dir = os.path.abspath(args.out) if args.out else os.path.join(base, "dataset_stats")
    os.makedirs(out_dir, exist_ok=True)

    metrex_dir = os.path.join(base, "metrex", "dataset")
    vt_dir = os.path.join(base, "veri_thoughts", "dataset")

    print("Scanning metrex dataset …")
    metrex_records = scan_dataset(metrex_dir, "metrex")
    print(f"  Found {len(metrex_records)} design IDs")

    print("Scanning veri_thoughts dataset …")
    vt_records = scan_dataset(vt_dir, "veri_thoughts")
    print(f"  Found {len(vt_records)} design IDs")

    all_records = metrex_records + vt_records

    # ── Print summaries ──
    print_summary(metrex_records, "metrex")
    print_summary(vt_records, "veri_thoughts")

    # ── Write CSV ──
    import csv
    csv_path = os.path.join(out_dir, "dataset_stats.csv")
    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=[
            "dataset", "id", "module_name",
            "module_loc", "module_total_lines", "module_bytes",
            "sva_loc", "sva_total_lines", "sva_bytes",
            "sva_asserts", "sva_covers", "sva_assumes", "sva_total_props",
        ])
        w.writeheader()
        for r in sorted(all_records, key=lambda x: (x["label"], x["id"])):
            w.writerow({
                "dataset": r["label"],
                "id": r["id"],
                "module_name": r["module_name"],
                "module_loc": r["module_loc"],
                "module_total_lines": r["module_total_lines"],
                "module_bytes": r["module_bytes"],
                "sva_loc": r["sva_loc"],
                "sva_total_lines": r["sva_total_lines"],
                "sva_bytes": r["sva_bytes"],
                "sva_asserts": r["sva_asserts"],
                "sva_covers": r["sva_covers"],
                "sva_assumes": r["sva_assumes"],
                "sva_total_props": r["sva_total_props"],
            })
    print(f"\nWrote {len(all_records)} rows to {csv_path}")

    # ── Extract arrays for plotting ──
    m_mod_loc = [r["module_loc"] for r in metrex_records if r["module_loc"] > 0]
    v_mod_loc = [r["module_loc"] for r in vt_records if r["module_loc"] > 0]

    m_sva_loc = [r["sva_loc"] for r in metrex_records if r["sva_loc"] > 0]
    v_sva_loc = [r["sva_loc"] for r in vt_records if r["sva_loc"] > 0]

    m_sva_props = [r["sva_total_props"] for r in metrex_records if r["sva_total_props"] > 0]
    v_sva_props = [r["sva_total_props"] for r in vt_records if r["sva_total_props"] > 0]

    m_sva_asserts = [r["sva_asserts"] for r in metrex_records if r["sva_asserts"] > 0]
    v_sva_asserts = [r["sva_asserts"] for r in vt_records if r["sva_asserts"] > 0]

    print("\nGenerating charts (driven by CHART_CONFIG) …")

    # ── Distribution metrics: comparison charts ──
    dist_metrics = [
        ("module_loc",     m_mod_loc,     v_mod_loc,     "Module Lines of Code (non-blank, non-comment)",  "Module LOC"),
        ("sva_loc",        m_sva_loc,     v_sva_loc,     "SVA Lines of Code (non-blank, non-comment)",     "SVA LOC"),
        ("sva_properties", m_sva_props,   v_sva_props,   "Number of SVA Properties (assert + cover + assume)", "SVA Properties per File"),
        ("sva_assertions", m_sva_asserts, v_sva_asserts, "Number of Assertions (assert property)",         "Assertions per SVA File"),
    ]

    for metric_key, m_data, v_data, xlabel_long, ylabel_short in dist_metrics:
        if _enabled(metric_key, "histogram"):
            plot_histogram_comparison(
                m_data, v_data, "metrex", "veri_thoughts",
                xlabel=xlabel_long,
                title=f"{ylabel_short} Distribution — metrex vs veri_thoughts",
                out_path=os.path.join(out_dir, f"hist_{metric_key}.png"),
            )
        if _enabled(metric_key, "histogram_log"):
            plot_histogram_comparison(
                m_data, v_data, "metrex", "veri_thoughts",
                xlabel=ylabel_short,
                title=f"{ylabel_short} Distribution (log scale) — metrex vs veri_thoughts",
                out_path=os.path.join(out_dir, f"hist_{metric_key}_log.png"),
                log_y=True,
            )
        if _enabled(metric_key, "boxplot"):
            plot_boxplot_comparison(
                {"metrex": m_data, "veri_thoughts": v_data},
                ylabel=ylabel_short,
                title=f"{ylabel_short} Box Plot — metrex vs veri_thoughts",
                out_path=os.path.join(out_dir, f"boxplot_{metric_key}.png"),
            )
        if _enabled(metric_key, "strip"):
            plot_strip_comparison(
                {"metrex": m_data, "veri_thoughts": v_data},
                ylabel=ylabel_short,
                title=f"{ylabel_short} per Design — metrex vs veri_thoughts",
                out_path=os.path.join(out_dir, f"strip_{metric_key}.png"),
            )
        if _enabled(metric_key, "cdf"):
            plot_cdf_comparison(
                m_data, v_data, "metrex", "veri_thoughts",
                xlabel=ylabel_short,
                title=f"CDF of {ylabel_short} — metrex vs veri_thoughts",
                out_path=os.path.join(out_dir, f"cdf_{metric_key}.png"),
            )

    # ── Scatter metrics: comparison charts ──
    if _enabled("module_loc_vs_sva_loc", "scatter"):
        plot_scatter(
            [r for r in all_records if r["module_loc"] > 0 and r["sva_loc"] > 0],
            x_key="module_loc", y_key="sva_loc",
            xlabel="Module LOC", ylabel="SVA LOC",
            title="Module LOC vs SVA LOC",
            out_path=os.path.join(out_dir, "scatter_module_vs_sva_loc.png"),
        )
    if _enabled("module_loc_vs_sva_props", "scatter"):
        plot_scatter(
            [r for r in all_records if r["module_loc"] > 0 and r["sva_total_props"] > 0],
            x_key="module_loc", y_key="sva_total_props",
            xlabel="Module LOC", ylabel="Number of SVA Properties",
            title="Module LOC vs Number of SVA Properties",
            out_path=os.path.join(out_dir, "scatter_module_loc_vs_props.png"),
        )

    # ── Stacked bar: property breakdown comparison ──
    if _enabled("property_breakdown", "stacked_bar"):
        plot_stacked_bar_comparison(
            metrex_records, vt_records,
            title="Avg SVA Property Breakdown per File\n(Assertions / Covers / Assumes)",
            out_path=os.path.join(out_dir, "bar_avg_property_breakdown.png"),
        )

    # ── Per-dataset individual charts ──
    generate_charts_for_dataset(metrex_records, "metrex",
                                os.path.join(out_dir, "metrex"))
    generate_charts_for_dataset(vt_records, "veri_thoughts",
                                os.path.join(out_dir, "veri_thoughts"))

    print(f"\nAll outputs saved to {out_dir}")
    print("Done!")


if __name__ == "__main__":
    main()
