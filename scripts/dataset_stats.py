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
import csv
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
RE_BIND   = re.compile(r'(?m)^\s*bind\s+', re.IGNORECASE)


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

    # ── Breakdown metrics (support: pie, stacked_bar) ──
    "property_breakdown": ["pie"],

    # ── Bind status (support: pie) ──
    "bind_status": ["pie"],
}

VALID_CHART_TYPES = {"histogram", "histogram_log", "boxplot", "strip", "cdf",
                     "scatter", "stacked_bar", "pie"}


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


def sva_has_bind(filepath: str) -> bool:
    """Return True if the SVA file contains a bind statement."""
    try:
        with open(filepath, "r", encoding="utf-8", errors="replace") as f:
            text = f.read()
    except (OSError, IOError):
        return False
    return bool(RE_BIND.search(text))


def _parse_summary_txt(summary_path: str) -> dict:
    """Parse a per-ID summary.txt and return key=value pairs."""
    data = {}
    try:
        with open(summary_path, "r", encoding="utf-8", errors="replace") as f:
            for line in f:
                if "=" in line:
                    k, _, v = line.strip().partition("=")
                    data[k.strip()] = v.strip()
    except (OSError, IOError):
        pass
    return data


def parse_verif_summary(verif_version_dir: str) -> dict:
    """Parse verif_summary.csv (with or without header) and enrich with per-ID data.

    verif_version_dir: e.g. metrex/dataset/verification_results/version_1
    Looks for verif_summary.csv in visual_data/ subfolder only.
    Per-ID data from ids/{ID}/summary.txt and ids/{ID}/cex_details.txt.
    """
    # Find verif_summary.csv — canonical location is visual_data/
    ids_dir = os.path.join(verif_version_dir, "ids")
    candidates = [
        os.path.join(verif_version_dir, "visual_data", "verif_summary.csv"),
    ]
    summary_path = None
    for c in candidates:
        if os.path.isfile(c):
            summary_path = c
            break
    if summary_path is None or not os.path.isdir(ids_dir):
        return {}

    results = {}
    with open(summary_path, newline="", encoding="utf-8") as f:
        first_line = f.readline()
        f.seek(0)
        # Detect header: if first field is 'id' it has a header
        if first_line.startswith("id,"):
            reader = csv.DictReader(f)
            rows = [(row["id"].strip(), row["status"].strip().lower(),
                     row.get("reason", "").strip()) for row in reader]
        else:
            reader = csv.reader(f)
            rows = []
            for parts in reader:
                if len(parts) >= 2:
                    rows.append((parts[0].strip(), parts[1].strip().lower(),
                                 parts[2].strip() if len(parts) > 2 else ""))

    for sid, status, reason in rows:
        # Read per-ID summary.txt for assertion/cover counts
        id_dir = os.path.join(ids_dir, sid)
        summary_kv = _parse_summary_txt(os.path.join(id_dir, "summary.txt"))
        assert_count = int(summary_kv.get("ASSERT_COUNT", 0))
        cover_count = int(summary_kv.get("COVER_COUNT", 0))

        entry = {
            "status": status,
            "reason": reason,
            "assert_count": assert_count,
            "cover_count": cover_count,
            "timeout": "timeout" in reason.lower(),
            "cex_details": [],
        }

        # Parse cex_details.txt if present
        cex_path = os.path.join(id_dir, "cex_details.txt")
        if os.path.isfile(cex_path):
            with open(cex_path, "r", encoding="utf-8", errors="replace") as cf:
                for line in cf:
                    if line.strip() and not line.startswith("#"):
                        parts = [x.strip() for x in line.split("|")]
                        if len(parts) == 3:
                            entry["cex_details"].append({
                                "property": parts[0],
                                "cex_type": parts[1],
                                "cex_length": int(parts[2]) if parts[2].isdigit() else None,
                            })

        results[sid] = entry
    return results


def collect_all_verif_stats(dataset_dir: str) -> dict:
    """Collect verification stats across all version_X dirs under dataset_dir/verification_results/.
    Returns a dict keyed by ID, using the latest version if an ID appears in multiple.
    """
    verif_base = os.path.join(dataset_dir, "verification_results")
    if not os.path.isdir(verif_base):
        return {}
    merged = {}
    version_dirs = sorted(
        [d for d in os.listdir(verif_base) if d.startswith("version_") and
         os.path.isdir(os.path.join(verif_base, d))]
    )
    for vdir in version_dirs:
        vpath = os.path.join(verif_base, vdir)
        stats = parse_verif_summary(vpath)
        merged.update(stats)  # later versions overwrite earlier
    return merged


def scan_dataset(version_dir: str, label: str, verif_stats: dict) -> list[dict]:
    """
    Scan a single version_X directory and collect per-ID stats.
    verif_stats is a pre-collected dict keyed by ID from collect_all_verif_stats.
    Returns list of dicts with keys:
        id, label, module_name, module_loc, module_total_lines, module_bytes,
        sva_loc, sva_total_lines, sva_bytes, sva_asserts, sva_covers,
        sva_assumes, sva_total_props, verif_status, verif_reason,
        verif_assert_count, verif_cover_count, verif_timeout,
        verif_cex_details, verif_cex_cycles
    """
    if not os.path.isdir(version_dir):
        print(f"WARNING: {version_dir} not found, skipping")
        return []

    records = []
    for entry in sorted(os.listdir(version_dir)):
        entry_path = os.path.join(version_dir, entry)
        if not os.path.isdir(entry_path) or not entry.isdigit():
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
        has_bind = sva_has_bind(sva_path) if os.path.isfile(sva_path) else False

        record = {
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
            "has_bind": has_bind,
        }
        # Add verification stats if available
        if entry in verif_stats:
            v = verif_stats[entry]
            record["verif_status"] = v["status"]
            record["verif_reason"] = v["reason"]
            record["verif_assert_count"] = v["assert_count"]
            record["verif_cover_count"] = v["cover_count"]
            record["verif_timeout"] = v["timeout"]
            record["verif_cex_details"] = v["cex_details"]
            record["verif_cex_cycles"] = [d["cex_length"] for d in v["cex_details"] if d["cex_length"] is not None]
        else:
            record["verif_status"] = None
            record["verif_reason"] = None
            record["verif_assert_count"] = 0
            record["verif_cover_count"] = 0
            record["verif_timeout"] = False
            record["verif_cex_details"] = []
            record["verif_cex_cycles"] = []
        records.append(record)
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
    n_with_bind = sum(1 for r in records if r["has_bind"])
    n_without_bind = len(records) - n_with_bind

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
    print(f"  Bind statement in SVA:")
    print(f"    with_bind={n_with_bind}  without_bind={n_without_bind}")


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
    if log_y:
        ax.hist(data, bins=bins_arr, alpha=0.75, color=COLORS.get(label, "#2196F3"),
                edgecolor="black", linewidth=0.4, label=f"{label} (n={len(data)})",
                orientation="horizontal")
        ax.set_xscale("log")
        ax.set_xlabel("Number of Design IDs", fontsize=12)
        ax.set_ylabel(xlabel, fontsize=12)
    else:
        ax.hist(data, bins=bins_arr, alpha=0.75, color=COLORS.get(label, "#2196F3"),
                edgecolor="black", linewidth=0.4, label=f"{label} (n={len(data)})")
        ax.set_xlabel(xlabel, fontsize=12)
        ax.set_ylabel("Number of Design IDs", fontsize=12)
    ax.set_title(title, fontsize=14, fontweight="bold")
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


def plot_scatter_single(records, label, x_key, y_key, xlabel, ylabel, title, out_path,
                        outlier_std=2.5):
    """Scatter plot for a single dataset with line of best fit and outlier labels."""
    fig, ax = plt.subplots(figsize=(12, 7))
    if not records:
        plt.close(fig)
        return
    xs = np.array([r[x_key] for r in records], dtype=float)
    ys = np.array([r[y_key] for r in records], dtype=float)
    ids = [r["id"] for r in records]

    ax.scatter(xs, ys, alpha=0.25, s=12, color=COLORS.get(label, "#2196F3"),
              label=f"{label} (n={len(records)})")

    # Line of best fit
    if len(xs) >= 2:
        coeffs = np.polyfit(xs, ys, 1)
        poly = np.poly1d(coeffs)
        x_sorted = np.sort(xs)
        ax.plot(x_sorted, poly(x_sorted), color="red", linewidth=1.5, linestyle="--",
                label=f"fit: y={coeffs[0]:.2f}x + {coeffs[1]:.1f}")

        # Label outliers: points whose residual exceeds outlier_std * std(residuals)
        residuals = ys - poly(xs)
        res_std = np.std(residuals)
        if res_std > 0:
            for i, (x, y, rid) in enumerate(zip(xs, ys, ids)):
                if abs(residuals[i]) > outlier_std * res_std:
                    ax.annotate(rid, (x, y), fontsize=7, alpha=0.8,
                                textcoords="offset points", xytext=(4, 4))

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


def plot_property_breakdown_pie(records, label, title, out_path):
    """Pie chart of total assert / cover / assume counts across the dataset."""
    fig, ax = plt.subplots(figsize=(8, 6))
    total_asserts = sum(r["sva_asserts"] for r in records)
    total_covers  = sum(r["sva_covers"]  for r in records)
    total_assumes = sum(r["sva_assumes"] for r in records)
    sizes  = [total_asserts, total_covers, total_assumes]
    labels = [f"Assertions\n({total_asserts:,})",
              f"Covers\n({total_covers:,})",
              f"Assumes\n({total_assumes:,})"]
    colors = [COLORS["assert"], COLORS["cover"], COLORS["assume"]]
    # Filter out zero slices
    filtered = [(s, l, c) for s, l, c in zip(sizes, labels, colors) if s > 0]
    if not filtered:
        plt.close(fig)
        return
    sizes, labels, colors = zip(*filtered)
    wedges, texts, autotexts = ax.pie(
        sizes, labels=labels, colors=colors, autopct="%1.1f%%",
        startangle=90, pctdistance=0.6,
        wedgeprops=dict(edgecolor="black", linewidth=0.5),
    )
    for t in autotexts:
        t.set_fontsize(11)
        t.set_fontweight("bold")
    ax.set_title(title, fontsize=14, fontweight="bold")
    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    print(f"  Saved {out_path}")


def print_verification_summary(records, label, out_dir):
    """Print verification/counterexample summary and save PNGs to out_dir."""
    os.makedirs(out_dir, exist_ok=True)

    verified = [r for r in records if r.get("verif_status") is not None]
    n_total = len(verified)
    if n_total == 0:
        print(f"\n  {label}: no verification results found, skipping verification summary.\n")
        return

    n_pass = sum(1 for r in verified if r["verif_status"] == "pass")
    n_fail = sum(1 for r in verified if r["verif_status"] == "fail")
    n_timeout = sum(1 for r in verified if r.get("verif_timeout"))
    n_has_cex = sum(1 for r in verified if len(r.get("verif_cex_details", [])) > 0)

    # Assertion counts from summary.txt ASSERT_COUNT
    assert_counts = [r["verif_assert_count"] for r in verified if r.get("verif_assert_count", 0) > 0]
    avg_assert_count = np.mean(assert_counts) if assert_counts else 0

    cex_cycles = [c for r in verified for c in r.get("verif_cex_cycles", []) if c is not None]
    n_counterexamples = sum(len(r.get("verif_cex_details", [])) for r in verified)

    # Categorize failure reasons
    fail_reasons = defaultdict(int)
    for r in verified:
        if r["verif_status"] == "fail":
            reason = r.get("verif_reason", "")
            if "No properties found" in reason:
                fail_reasons["No properties found (bind issue)"] += 1
            elif "compile/elab errors" in reason:
                fail_reasons["Compile/elaboration errors"] += 1
            elif "timeout" in reason.lower():
                fail_reasons["Timeout"] += 1
            else:
                fail_reasons["Other"] += 1

    print(f"\n{'=' * 60}")
    print(f"  {label} — Verification Results Summary")
    print(f"{'=' * 60}")
    print(f"  Total modules with verification results : {n_total}")
    print(f"  Pass                                    : {n_pass}")
    print(f"  Fail                                    : {n_fail}")
    print(f"  Timeout                                 : {n_timeout}")
    print(f"  Modules with counter-examples           : {n_has_cex}")
    print(f"  Avg assertions per passing module       : {avg_assert_count:.2f}")
    print(f"  Total counter-examples                  : {n_counterexamples}")
    if cex_cycles:
        print(f"  CEX cycles — avg: {np.mean(cex_cycles):.2f}  "
              f"median: {np.median(cex_cycles):.1f}  max: {max(cex_cycles)}")
    else:
        print(f"  No CEX cycle data available.")

    if fail_reasons:
        print(f"\n  Failure Reason Breakdown:")
        for reason, count in sorted(fail_reasons.items(), key=lambda x: -x[1]):
            print(f"    {reason:40s} : {count}")

    # ── Pie chart: verification outcomes (pass vs fail) ──
    pie_labels = []
    pie_sizes = []
    pie_colors_list = []
    for lbl, sz, clr in [("Pass", n_pass, "#4CAF50"),
                          ("Fail", n_fail, "#F44336")]:
        if sz > 0:
            pie_labels.append(f"{lbl}\n({sz})")
            pie_sizes.append(sz)
            pie_colors_list.append(clr)

    if pie_sizes:
        fig, ax = plt.subplots(figsize=(7, 7))
        ax.pie(pie_sizes, labels=pie_labels, colors=pie_colors_list,
               autopct="%1.1f%%", startangle=90, pctdistance=0.7,
               wedgeprops=dict(edgecolor="black", linewidth=0.5))
        ax.set_title(f"Verification Outcome — {label}\n(n={n_total})",
                     fontsize=14, fontweight="bold")
        fig.tight_layout()
        path = os.path.join(out_dir, "pie_verification_outcomes.png")
        fig.savefig(path, dpi=150)
        plt.close(fig)
        print(f"  Saved {path}")

    # ── Pie chart: failure reason breakdown ──
    if fail_reasons:
        fr_labels = []
        fr_sizes = []
        fr_colors = ["#F44336", "#FF9800", "#9E9E9E", "#795548"]
        for (reason, count), clr in zip(
            sorted(fail_reasons.items(), key=lambda x: -x[1]),
            fr_colors,
        ):
            fr_labels.append(f"{reason}\n({count})")
            fr_sizes.append(count)
        fig_fr, ax_fr = plt.subplots(figsize=(8, 8))
        ax_fr.pie(fr_sizes, labels=fr_labels, colors=fr_colors[:len(fr_sizes)],
                  autopct="%1.1f%%", startangle=90, pctdistance=0.7,
                  wedgeprops=dict(edgecolor="black", linewidth=0.5))
        ax_fr.set_title(f"Failure Reason Breakdown — {label}\n(n={n_fail})",
                        fontsize=14, fontweight="bold")
        fig_fr.tight_layout()
        path_fr = os.path.join(out_dir, "pie_failure_reasons.png")
        fig_fr.savefig(path_fr, dpi=150)
        plt.close(fig_fr)
        print(f"  Saved {path_fr}")

    # ── Histogram: assertion count per passing module ──
    if assert_counts:
        fig2, ax2 = plt.subplots(figsize=(10, 5))
        max_val = max(assert_counts)
        bins = min(30, max_val + 1) if max_val > 0 else 1
        ax2.hist(assert_counts, bins=bins, color="#4CAF50", edgecolor="black", alpha=0.75)
        ax2.set_xlabel("Number of Assertions (from ASSERT_COUNT)", fontsize=12)
        ax2.set_ylabel("Number of Modules", fontsize=12)
        ax2.set_title(f"Distribution of Assertion Counts per Module — {label}",
                      fontsize=14, fontweight="bold")
        fig2.tight_layout()
        path2 = os.path.join(out_dir, "hist_assertion_counts.png")
        fig2.savefig(path2, dpi=150)
        plt.close(fig2)
        print(f"  Saved {path2}")

    # ── Histogram: CEX cycle lengths ──
    if cex_cycles:
        fig3, ax3 = plt.subplots(figsize=(10, 5))
        ax3.hist(cex_cycles, bins=30, color="#F44336", edgecolor="black", alpha=0.75)
        ax3.set_xlabel("CEX Cycle Length", fontsize=12)
        ax3.set_ylabel("Number of Counter-Examples", fontsize=12)
        ax3.set_title(f"Distribution of CEX Cycles — {label}",
                      fontsize=14, fontweight="bold")
        fig3.tight_layout()
        path3 = os.path.join(out_dir, "hist_cex_cycles.png")
        fig3.savefig(path3, dpi=150)
        plt.close(fig3)
        print(f"  Saved {path3}")


def generate_charts_for_dataset(records, label, out_dir):
    """Generate chart types for a single dataset, driven by CHART_CONFIG."""
    os.makedirs(out_dir, exist_ok=True)

    # Remove stale PNGs from previous runs so disabled charts don't linger
    for old_png in glob.glob(os.path.join(out_dir, "*.png")):
        os.remove(old_png)

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

    # ── Property breakdown ──
    if _enabled("property_breakdown", "pie"):
        plot_property_breakdown_pie(
            records, label,
            title=f"SVA Property Breakdown — {label}\n(Assertions / Covers / Assumes)",
            out_path=os.path.join(out_dir, "pie_property_breakdown.png"),
        )
    if _enabled("property_breakdown", "stacked_bar"):
        plot_stacked_bar_single(
            records, label,
            title=f"Avg SVA Property Breakdown per File — {label}\n(Assertions / Covers / Assumes)",
            out_path=os.path.join(out_dir, "bar_avg_property_breakdown.png"),
        )

    # ── Bind status pie chart ──
    if _enabled("bind_status", "pie"):
        n_bind = sum(1 for r in records if r["has_bind"])
        n_no_bind = len(records) - n_bind
        if n_bind > 0 or n_no_bind > 0:
            fig_bs, ax_bs = plt.subplots(figsize=(7, 7))
            sizes = [n_bind, n_no_bind]
            labels_bs = [
                f"Has Bind\n({n_bind})",
                f"No Bind (needs auto-bind)\n({n_no_bind})",
            ]
            colors_bs = ["#4CAF50", "#FF9800"]
            wedges, texts, autotexts = ax_bs.pie(
                sizes, labels=labels_bs, colors=colors_bs,
                autopct="%1.1f%%", startangle=140,
                textprops={"fontsize": 12},
            )
            for at in autotexts:
                at.set_fontweight("bold")
            ax_bs.set_title(
                f"Bind Statement Status — {label}\n(n={len(records)})",
                fontsize=14, fontweight="bold",
            )
            fig_bs.tight_layout()
            path_bs = os.path.join(out_dir, "pie_bind_status.png")
            fig_bs.savefig(path_bs, dpi=150)
            plt.close(fig_bs)
            print(f"  Saved {path_bs}")

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


# ── Per-dataset CSV + charts helper ──────────────────────────────────────────
def _process_version(version_dir, dataset_dir, label, version_name, verif_stats):
    """Process a single version_X: scan, write CSV, print summary, generate charts.
    Output goes to <dataset_dir>/dataset_stats/<version_name>/.
    """
    import csv

    out_dir = os.path.join(dataset_dir, "dataset_stats", version_name)
    os.makedirs(out_dir, exist_ok=True)

    version_label = f"{label} {version_name}"
    print(f"\nScanning {version_label} …")
    records = scan_dataset(version_dir, label, verif_stats)
    print(f"  Found {len(records)} design IDs")

    if not records:
        print(f"  Nothing to do for {version_label}.\n")
        return

    print_summary(records, version_label)

    # ── Write CSV ──
    csv_path = os.path.join(out_dir, "dataset_stats.csv")
    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=[
            "id", "module_name",
            "module_loc", "module_total_lines", "module_bytes",
            "sva_loc", "sva_total_lines", "sva_bytes",
            "sva_asserts", "sva_covers", "sva_assumes", "sva_total_props",
            "has_bind",
        ])
        w.writeheader()
        for r in sorted(records, key=lambda x: x["id"]):
            w.writerow({
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
                "has_bind": r["has_bind"],
            })
    print(f"\nWrote {len(records)} rows to {csv_path}")

    # ── Generate charts ──
    generate_charts_for_dataset(records, version_label, out_dir)

    # ── Verification/counterexample summary and plots ──
    print_verification_summary(records, version_label, out_dir)

    print(f"\nAll {version_label} outputs saved to {out_dir}")


def process_single_dataset(dataset_dir, label):
    """Process each version_X in a dataset separately.
    Output goes to <dataset_dir>/dataset_stats/<version_X>/.
    """
    version_dirs = sorted(
        [d for d in os.listdir(dataset_dir)
         if d.startswith("version_") and os.path.isdir(os.path.join(dataset_dir, d))]
    )
    if not version_dirs:
        print(f"WARNING: no version_X dirs found in {dataset_dir}, skipping {label}")
        return

    # Collect verification stats once (across all verif version_X dirs)
    verif_stats = collect_all_verif_stats(dataset_dir)

    for vdir in version_dirs:
        vpath = os.path.join(dataset_dir, vdir)
        _process_version(vpath, dataset_dir, label, vdir, verif_stats)


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
    args = parser.parse_args()

    base = os.path.abspath(args.base_dir)

    metrex_dir = os.path.join(base, "metrex", "dataset")
    vt_dir = os.path.join(base, "veri_thoughts", "dataset")

    process_single_dataset(metrex_dir, "metrex")
    process_single_dataset(vt_dir, "veri_thoughts")

    print("Done!")


if __name__ == "__main__":
    main()
