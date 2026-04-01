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

try:
    import plotly.graph_objects as go
    HAS_PLOTLY = True
except ImportError:
    HAS_PLOTLY = False

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


def parse_id_summary_csv(csv_path: str) -> list[dict]:
    """Parse an id_summary.csv file and return a list of row dicts.

    Handles both formats (with and without auto_bind column).
    """
    rows = []
    if not os.path.isfile(csv_path):
        return rows
    with open(csv_path, newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            entry = {
                "id": row["id"].strip(),
                "csv_status": row.get("csv_status", "").strip(),
                "total_assertions": int(row.get("total_assertions", 0)),
                "proven": int(row.get("proven", 0)),
                "cex": int(row.get("cex", 0)),
                "total_covers": int(row.get("total_covers", 0)),
                "covered": int(row.get("covered", 0)),
                "unreachable": int(row.get("unreachable", 0)),
            }
            rows.append(entry)
    return rows


def collect_id_summaries(dataset_dir: str) -> list[dict]:
    """Collect id_summary.csv rows across all version_X dirs, latest wins."""
    verif_base = os.path.join(dataset_dir, "verification_results")
    if not os.path.isdir(verif_base):
        return []
    merged = {}  # keyed by id
    version_dirs = sorted(
        [d for d in os.listdir(verif_base) if d.startswith("version_") and
         os.path.isdir(os.path.join(verif_base, d))]
    )
    for vdir in version_dirs:
        csv_path = os.path.join(verif_base, vdir, "visual_data", "id_summary.csv")
        for row in parse_id_summary_csv(csv_path):
            merged[row["id"]] = row
    return sorted(merged.values(), key=lambda r: r["id"])


def generate_interactive_pie_html(all_rows: list[dict], label: str, out_path: str):
    """Generate an interactive HTML page with a dropdown to select an ID
    and view a pie chart of proven vs CEX assertions (and covered vs unreachable covers).

    Requires plotly.  Falls back to a warning message if plotly is unavailable.
    """
    if not HAS_PLOTLY:
        print(f"  WARNING: plotly not installed, skipping interactive pie chart for {label}")
        return

    # Filter to IDs that have at least one assertion or cover
    rows = [r for r in all_rows if r["total_assertions"] > 0 or r["total_covers"] > 0]
    if not rows:
        print(f"  No IDs with assertions/covers found for {label}, skipping interactive pie.")
        return

    ids = [r["id"] for r in rows]

    # Build one figure with two pie subcharts per ID, using dropdown visibility
    from plotly.subplots import make_subplots

    fig = make_subplots(
        rows=1, cols=2,
        specs=[[{"type": "pie"}, {"type": "pie"}]],
        subplot_titles=["Assertions: Proven vs CEX", "Covers: Covered vs Unreachable"],
    )

    # Add two pie traces per ID (all hidden except the first)
    for i, r in enumerate(rows):
        visible = (i == 0)
        # Assertions pie
        fig.add_trace(
            go.Pie(
                labels=["Proven", "CEX"],
                values=[r["proven"], r["cex"]],
                marker=dict(colors=["#4CAF50", "#F44336"]),
                textinfo="label+value+percent",
                name=f"Assertions – {r['id']}",
                visible=visible,
                hole=0.3,
            ),
            row=1, col=1,
        )
        # Covers pie
        fig.add_trace(
            go.Pie(
                labels=["Covered", "Unreachable"],
                values=[r["covered"], r["unreachable"]],
                marker=dict(colors=["#2196F3", "#FF9800"]),
                textinfo="label+value+percent",
                name=f"Covers – {r['id']}",
                visible=visible,
                hole=0.3,
            ),
            row=1, col=2,
        )

    # Build dropdown buttons — each button makes exactly 2 traces visible
    n_ids = len(rows)
    buttons = []
    for i, r in enumerate(rows):
        vis = [False] * (2 * n_ids)
        vis[2 * i] = True      # assertions pie for this ID
        vis[2 * i + 1] = True  # covers pie for this ID
        summary = (f"ID {r['id']}  —  Assertions: {r['proven']} proven, {r['cex']} cex"
                   f"  |  Covers: {r['covered']} covered, {r['unreachable']} unreachable")
        buttons.append(dict(
            label=r["id"],
            method="update",
            args=[{"visible": vis},
                  {"title": f"{label} — {summary}"}],
        ))

    fig.update_layout(
        updatemenus=[dict(
            active=0,
            buttons=buttons,
            x=0.5, xanchor="center",
            y=1.15, yanchor="top",
            bgcolor="#e0e0e0",
            font=dict(size=13),
        )],
        title=dict(
            text=(f"{label} — ID {rows[0]['id']}  —  "
                  f"Assertions: {rows[0]['proven']} proven, {rows[0]['cex']} cex  |  "
                  f"Covers: {rows[0]['covered']} covered, {rows[0]['unreachable']} unreachable"),
            x=0.5,
        ),
        height=550,
        width=1000,
        showlegend=True,
    )

    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    fig.write_html(out_path)
    print(f"  Saved interactive pie chart: {out_path}")


def parse_property_results_csv(csv_path: str) -> dict:
    """Parse a property_results.csv and return data grouped by ID.

    Returns dict[id] = list of {property_name, type, result}.
    """
    by_id = defaultdict(list)
    if not os.path.isfile(csv_path):
        return by_id
    with open(csv_path, newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            by_id[row["id"].strip()].append({
                "property_name": row["property_name"].strip(),
                "type": row["type"].strip(),
                "result": row["result"].strip(),
            })
    return dict(by_id)


def parse_cex_details(cex_path: str) -> dict:
    """Parse a cex_details.txt file.

    Returns dict[property_name] = {cex_type, cex_length}.
    """
    details = {}
    if not os.path.isfile(cex_path):
        return details
    try:
        with open(cex_path, "r", encoding="utf-8", errors="replace") as f:
            for line in f:
                stripped = line.strip()
                if not stripped or stripped.startswith("#"):
                    continue
                parts = [p.strip() for p in stripped.split("|")]
                if len(parts) >= 2:
                    prop = parts[0]
                    cex_type = parts[1] if len(parts) > 1 else ""
                    cex_len = parts[2] if len(parts) > 2 else ""
                    details[prop] = {
                        "cex_type": cex_type,
                        "cex_length": cex_len if cex_len else "N/A",
                    }
    except (OSError, IOError):
        pass
    return details


def collect_property_data(dataset_dir: str) -> tuple:
    """Collect property_results.csv and cex_details across all version_X dirs.

    Returns (by_id, cex_by_id) where:
        by_id[id]     = list of {property_name, type, result}
        cex_by_id[id] = dict[property_name] = {cex_type, cex_length}
    Latest version wins for each ID.
    """
    verif_base = os.path.join(dataset_dir, "verification_results")
    if not os.path.isdir(verif_base):
        return {}, {}
    by_id = {}
    cex_by_id = {}
    version_dirs = sorted(
        [d for d in os.listdir(verif_base) if d.startswith("version_") and
         os.path.isdir(os.path.join(verif_base, d))]
    )
    for vdir in version_dirs:
        vpath = os.path.join(verif_base, vdir)
        # Property results
        prop_csv = os.path.join(vpath, "visual_data", "property_results.csv")
        for sid, props in parse_property_results_csv(prop_csv).items():
            by_id[sid] = props
        # CEX details per ID
        ids_dir = os.path.join(vpath, "ids")
        if os.path.isdir(ids_dir):
            for sid_dir in os.listdir(ids_dir):
                cex_path = os.path.join(ids_dir, sid_dir, "cex_details.txt")
                cex = parse_cex_details(cex_path)
                if cex:
                    cex_by_id[sid_dir] = cex
    return by_id, cex_by_id


def generate_interactive_assertion_detail_html(
    by_id: dict, cex_by_id: dict, label: str, out_path: str
):
    """Generate an interactive HTML page with a dropdown to select an ID and see
    a horizontal bar chart of each assertion/cover property, colored by result
    (proven=green, cex=red, covered=blue, unreachable=orange), with hover text
    showing counterexample details when available.
    """
    if not HAS_PLOTLY:
        print(f"  WARNING: plotly not installed, skipping assertion detail chart for {label}")
        return

    # Only include IDs that have at least one property
    ids_sorted = sorted(sid for sid, props in by_id.items() if props)
    if not ids_sorted:
        print(f"  No IDs with property results found for {label}, skipping assertion detail chart.")
        return

    result_colors = {
        "proven": "#4CAF50",
        "cex": "#F44336",
        "covered": "#2196F3",
        "unreachable": "#FF9800",
    }

    # Build all traces (one bar trace per ID, all hidden except first)
    fig = go.Figure()

    for i, sid in enumerate(ids_sorted):
        props = by_id[sid]
        cex_info = cex_by_id.get(sid, {})

        # Separate assertions and covers
        assertions = [p for p in props if p["type"] == "assertion"]
        covers = [p for p in props if p["type"] == "cover"]
        all_props = assertions + covers

        if not all_props:
            # Add an empty invisible trace as placeholder
            fig.add_trace(go.Bar(
                x=[0], y=["(no properties)"], orientation="h",
                visible=(i == 0),
                showlegend=False,
            ))
            continue

        names = []
        colors = []
        hover_texts = []
        values = []

        for p in all_props:
            pname = p["property_name"]
            result = p["result"]
            ptype = p["type"]

            # Shorten the display name: take the last part after the last dot
            short_name = pname.rsplit(".", 1)[-1] if "." in pname else pname
            display = f"[{ptype[0].upper()}] {short_name}"
            names.append(display)
            colors.append(result_colors.get(result, "#9E9E9E"))
            values.append(1)

            # Build hover text
            hover = f"<b>{pname}</b><br>Type: {ptype}<br>Result: {result}"
            if result == "cex":
                # Look up cex details — try full name and also the embedded format
                cex = cex_info.get(pname)
                if not cex:
                    # Try matching by suffix (cex_details often has embedded:: prefix)
                    for cex_key, cex_val in cex_info.items():
                        if pname.endswith(cex_key.rsplit("::", 1)[-1].rsplit(".", 1)[-1]):
                            cex = cex_val
                            break
                        if cex_key.endswith(short_name):
                            cex = cex_val
                            break
                if cex:
                    hover += (f"<br><br><b>Counter-Example:</b>"
                              f"<br>CEX Type: {cex['cex_type']}"
                              f"<br>CEX Length: {cex['cex_length']}")
                else:
                    hover += "<br><br><i>(no CEX details available)</i>"
            hover_texts.append(hover)

        fig.add_trace(go.Bar(
            y=names,
            x=values,
            orientation="h",
            marker=dict(color=colors, line=dict(color="black", width=0.5)),
            hovertext=hover_texts,
            hoverinfo="text",
            visible=(i == 0),
            showlegend=False,
        ))

    # Build dropdown buttons
    buttons = []
    for i, sid in enumerate(ids_sorted):
        vis = [False] * len(ids_sorted)
        vis[i] = True
        props = by_id[sid]
        n_assert = sum(1 for p in props if p["type"] == "assertion")
        n_cex = sum(1 for p in props if p["type"] == "assertion" and p["result"] == "cex")
        n_proven = sum(1 for p in props if p["type"] == "assertion" and p["result"] == "proven")
        n_cover = sum(1 for p in props if p["type"] == "cover")
        subtitle = (f"ID {sid}  —  {n_assert} assertions "
                    f"({n_proven} proven, {n_cex} cex), {n_cover} covers")
        buttons.append(dict(
            label=sid,
            method="update",
            args=[{"visible": vis},
                  {"title": f"{label} — {subtitle}"}],
        ))

    # Initial title
    first_props = by_id[ids_sorted[0]]
    n0_a = sum(1 for p in first_props if p["type"] == "assertion")
    n0_p = sum(1 for p in first_props if p["type"] == "assertion" and p["result"] == "proven")
    n0_c = sum(1 for p in first_props if p["type"] == "assertion" and p["result"] == "cex")
    n0_cv = sum(1 for p in first_props if p["type"] == "cover")
    init_title = (f"{label} — ID {ids_sorted[0]}  —  {n0_a} assertions "
                  f"({n0_p} proven, {n0_c} cex), {n0_cv} covers")

    # Compute max bar count across all IDs for consistent height
    max_props = max(len(by_id[sid]) for sid in ids_sorted) if ids_sorted else 10
    fig_height = max(500, min(1200, 50 + max_props * 25))

    fig.update_layout(
        updatemenus=[dict(
            active=0,
            buttons=buttons,
            x=0.5, xanchor="center",
            y=1.12, yanchor="top",
            bgcolor="#e0e0e0",
            font=dict(size=12),
        )],
        title=dict(text=init_title, x=0.5),
        xaxis=dict(title="", showticklabels=False),
        yaxis=dict(title="", automargin=True),
        height=fig_height,
        width=1100,
        margin=dict(l=350, r=40, t=100, b=40),
        annotations=[
            dict(text="<b>Legend:</b>  "
                      '<span style="color:#4CAF50">■</span> Proven  '
                      '<span style="color:#F44336">■</span> CEX  '
                      '<span style="color:#2196F3">■</span> Covered  '
                      '<span style="color:#FF9800">■</span> Unreachable',
                 xref="paper", yref="paper", x=0.5, y=-0.02,
                 showarrow=False, font=dict(size=12)),
        ],
    )

    os.makedirs(os.path.dirname(out_path) or ".", exist_ok=True)
    fig.write_html(out_path)
    print(f"  Saved interactive assertion detail chart: {out_path}")


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

    # ── Interactive pie chart from id_summary.csv ──
    id_summary_csv = os.path.join(
        dataset_dir, "verification_results", version_name, "visual_data", "id_summary.csv"
    )
    id_rows = parse_id_summary_csv(id_summary_csv)
    if id_rows:
        html_path = os.path.join(out_dir, "interactive_pie_per_id.html")
        generate_interactive_pie_html(id_rows, version_label, html_path)

    # ── Interactive assertion detail chart from property_results.csv ──
    prop_csv = os.path.join(
        dataset_dir, "verification_results", version_name, "visual_data", "property_results.csv"
    )
    prop_by_id = parse_property_results_csv(prop_csv)
    if prop_by_id:
        ids_dir = os.path.join(dataset_dir, "verification_results", version_name, "ids")
        cex_by_id = {}
        if os.path.isdir(ids_dir):
            for sid_dir in os.listdir(ids_dir):
                cex = parse_cex_details(os.path.join(ids_dir, sid_dir, "cex_details.txt"))
                if cex:
                    cex_by_id[sid_dir] = cex
        html_path2 = os.path.join(out_dir, "interactive_assertion_detail.html")
        generate_interactive_assertion_detail_html(prop_by_id, cex_by_id, version_label, html_path2)

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


def process_inference_outputs(io_dir):
    """Process inference_outputs/ directory where subdirs are model names.
    Structure:
        io_dir/{model}/{id}/module.v, sva.sv
        io_dir/verification_results/{model}/ids/{id}/...
        io_dir/verification_results/{model}/visual_data/
    """
    verif_base = os.path.join(io_dir, "verification_results")

    # Find model dirs: everything in io_dir that isn't syntax_results/verification_results
    model_dirs = sorted(
        d for d in os.listdir(io_dir)
        if os.path.isdir(os.path.join(io_dir, d))
        and d not in ("syntax_results", "verification_results")
    )
    if not model_dirs:
        print(f"WARNING: no model subdirectories found in {io_dir}")
        return

    for model_name in model_dirs:
        data_dir = os.path.join(io_dir, model_name)
        label = model_name

        # Collect verification stats for this model
        verif_stats = {}
        model_verif_dir = os.path.join(verif_base, model_name)
        if os.path.isdir(model_verif_dir):
            verif_stats = parse_verif_summary(model_verif_dir)

        print(f"\nScanning {label} …")
        records = scan_dataset(data_dir, label, verif_stats)
        print(f"  Found {len(records)} design IDs")

        if not records:
            print(f"  Nothing to do for {label}.\n")
            continue

        print_summary(records, label)

        # Output to io_dir/dataset_stats/{model_name}/
        out_dir = os.path.join(io_dir, "dataset_stats", model_name)
        os.makedirs(out_dir, exist_ok=True)

        # Write CSV
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

        # Generate charts
        generate_charts_for_dataset(records, label, out_dir)

        # Verification summary and plots
        print_verification_summary(records, label, out_dir)

        # Interactive pie chart from id_summary.csv
        if os.path.isdir(model_verif_dir):
            id_summary_csv = os.path.join(model_verif_dir, "visual_data", "id_summary.csv")
            id_rows = parse_id_summary_csv(id_summary_csv)
            if id_rows:
                html_path = os.path.join(out_dir, "interactive_pie_per_id.html")
                generate_interactive_pie_html(id_rows, label, html_path)

            # Interactive assertion detail chart from property_results.csv
            prop_csv = os.path.join(model_verif_dir, "visual_data", "property_results.csv")
            prop_by_id = parse_property_results_csv(prop_csv)
            if prop_by_id:
                ids_dir = os.path.join(model_verif_dir, "ids")
                cex_by_id = {}
                if os.path.isdir(ids_dir):
                    for sid_dir in os.listdir(ids_dir):
                        cex = parse_cex_details(os.path.join(ids_dir, sid_dir, "cex_details.txt"))
                        if cex:
                            cex_by_id[sid_dir] = cex
                html_path2 = os.path.join(out_dir, "interactive_assertion_detail.html")
                generate_interactive_assertion_detail_html(prop_by_id, cex_by_id, label, html_path2)

        print(f"\nAll {label} outputs saved to {out_dir}")


# ── Main ─────────────────────────────────────────────────────────────────────
def main():
    parser = argparse.ArgumentParser(
        description="Generate statistical charts for metrex and veri_thoughts datasets."
    )
    # Default base-dir to the parent of this script's directory (i.e. malik25_26/)
    _script_dir = os.path.dirname(os.path.abspath(__file__))
    _default_base = os.path.dirname(_script_dir)

    parser.add_argument(
        "target", nargs="?", default=None,
        help="Optional path to a directory like inference_outputs/ to process directly. "
             "If omitted, processes metrex and veri_thoughts under --base-dir.",
    )
    parser.add_argument(
        "--base-dir", "-b", default=_default_base,
        help="Workspace root containing metrex/ and veri_thoughts/ subdirs "
             f"(default: {_default_base})",
    )
    args = parser.parse_args()

    base = os.path.abspath(args.base_dir)

    if args.target:
        target = os.path.abspath(args.target)
        if not os.path.isdir(target):
            print(f"ERROR: {target} is not a directory")
            sys.exit(1)
        process_inference_outputs(target)
    else:
        metrex_dir = os.path.join(base, "metrex", "dataset")
        vt_dir = os.path.join(base, "veri_thoughts", "dataset")

        process_single_dataset(metrex_dir, "metrex")
        process_single_dataset(vt_dir, "veri_thoughts")

        # ── Combined interactive pie charts (all versions merged, one per dataset) ──
        for ddir, lbl in [(metrex_dir, "metrex"), (vt_dir, "veri_thoughts")]:
            combined_rows = collect_id_summaries(ddir)
            if combined_rows:
                html_out = os.path.join(ddir, "dataset_stats",
                                        f"interactive_pie_per_id_{lbl}.html")
                generate_interactive_pie_html(combined_rows, lbl, html_out)

        # ── Combined interactive assertion detail charts ──
        for ddir, lbl in [(metrex_dir, "metrex"), (vt_dir, "veri_thoughts")]:
            prop_by_id, cex_by_id = collect_property_data(ddir)
            if prop_by_id:
                html_out = os.path.join(ddir, "dataset_stats",
                                        f"interactive_assertion_detail_{lbl}.html")
                generate_interactive_assertion_detail_html(prop_by_id, cex_by_id, lbl, html_out)

    print("Done!")


if __name__ == "__main__":
    main()
