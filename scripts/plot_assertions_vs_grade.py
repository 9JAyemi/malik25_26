#!/usr/bin/env python3
"""
Plot the relationship between assertion count and quality grade
across all five models in runs/inference/.

For each model, reads:
  - verification_results/{model}/ids/{id}/summary.txt  → ASSERT_COUNT, QUALITY_GRADE
  - dataset_stats/{model}/dataset_stats.csv             → sva_asserts (regex-counted)

Produces per-model and combined figures in reports/inference/.
"""

import csv
import os
import sys
from collections import defaultdict
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

# ── Constants ────────────────────────────────────────────────────────────────
GRADE_ORDER = ["A", "B", "C", "D", "F"]
GRADE_COLORS = {"A": "#4CAF50", "B": "#8BC34A", "C": "#FF9800", "D": "#FF5722", "F": "#F44336"}
GRADE_NUM = {"A": 5, "B": 4, "C": 3, "D": 2, "F": 1}

MODEL_LABELS = {
    "adapter_verified":    "Adapter (Verified)",
    "adapter_syntax_pass": "Adapter (Syntax)",
    "adapter_all":         "Adapter (All)",
    "chatgpt_baseline":    "GPT-4o",
    "base_qwen":           "Qwen-7B (Base)",
}
MODEL_ORDER = ["base_qwen", "adapter_all", "adapter_syntax_pass", "adapter_verified", "chatgpt_baseline"]


def parse_summary_txt(path):
    """Parse a per-ID summary.txt → dict of key=value pairs."""
    data = {}
    try:
        with open(path, encoding="utf-8", errors="replace") as f:
            for line in f:
                if "=" in line:
                    k, _, v = line.strip().partition("=")
                    data[k.strip()] = v.strip()
    except (OSError, IOError):
        pass
    return data


def load_model_data(io_dir, model):
    """Return list of dicts with assert_count and quality_grade per design."""
    verif_ids = os.path.join(io_dir, "verification_results", model, "ids")
    rows = []
    if not os.path.isdir(verif_ids):
        return rows
    for did in sorted(os.listdir(verif_ids)):
        summary = os.path.join(verif_ids, did, "summary.txt")
        if not os.path.isfile(summary):
            continue
        d = parse_summary_txt(summary)
        grade = d.get("QUALITY_GRADE", "")
        try:
            ac = int(d.get("ASSERT_COUNT", 0))
        except ValueError:
            continue
        try:
            qs = float(d.get("QUALITY_SCORE", ""))
        except (ValueError, TypeError):
            qs = None
        if grade in GRADE_ORDER and ac > 0:
            rows.append({"id": did, "assert_count": ac, "grade": grade, "quality_score": qs})
    return rows


def plot_box_per_model(model_data, out_dir):
    """One box plot per model: x = quality grade, y = assertion count."""
    for model, rows in model_data.items():
        label = MODEL_LABELS.get(model, model)
        fig, ax = plt.subplots(figsize=(8, 5))

        box_data = []
        box_labels = []
        for g in GRADE_ORDER:
            vals = [r["assert_count"] for r in rows if r["grade"] == g]
            if vals:
                box_data.append(vals)
                box_labels.append(f"{g}\n(n={len(vals)})")
            else:
                box_data.append([])
                box_labels.append(f"{g}\n(n=0)")

        bp = ax.boxplot(box_data, labels=box_labels, patch_artist=True,
                        showmeans=True, meanprops=dict(marker="D", markerfacecolor="black", markersize=5))
        for patch, g in zip(bp["boxes"], GRADE_ORDER):
            patch.set_facecolor(GRADE_COLORS[g])
            patch.set_alpha(0.7)

        ax.set_xlabel("Quality Grade", fontsize=12)
        ax.set_ylabel("Assertion Count", fontsize=12)
        ax.set_title(f"Assertion Count vs Quality Grade — {label}", fontsize=13, fontweight="bold")
        ax.grid(axis="y", alpha=0.3)
        fig.tight_layout()
        out = os.path.join(out_dir, model, f"box_assertions_vs_grade.png")
        os.makedirs(os.path.dirname(out), exist_ok=True)
        fig.savefig(out, dpi=150)
        plt.close(fig)
        print(f"  Saved {out}")


def plot_violin_per_model(model_data, out_dir):
    """One violin plot per model: x = quality grade, y = assertion count."""
    for model, rows in model_data.items():
        label = MODEL_LABELS.get(model, model)
        fig, ax = plt.subplots(figsize=(8, 5))

        data_for_violin = []
        positions = []
        tick_labels = []
        for i, g in enumerate(GRADE_ORDER):
            vals = [r["assert_count"] for r in rows if r["grade"] == g]
            tick_labels.append(f"{g}\n(n={len(vals)})")
            if len(vals) >= 2:
                data_for_violin.append(vals)
                positions.append(i)
            elif len(vals) == 1:
                ax.scatter([i], vals, color=GRADE_COLORS[g], s=60, zorder=5, edgecolors="black")

        if data_for_violin:
            parts = ax.violinplot(data_for_violin, positions=positions,
                                  showmeans=True, showmedians=True, showextrema=True)
            for i, pc in enumerate(parts["bodies"]):
                g_idx = positions[i]
                pc.set_facecolor(GRADE_COLORS[GRADE_ORDER[g_idx]])
                pc.set_alpha(0.6)

        ax.set_xticks(range(len(GRADE_ORDER)))
        ax.set_xticklabels(tick_labels, fontsize=11)
        ax.set_xlabel("Quality Grade", fontsize=12)
        ax.set_ylabel("Assertion Count", fontsize=12)
        ax.set_title(f"Assertion Count vs Quality Grade — {label}", fontsize=13, fontweight="bold")
        ax.grid(axis="y", alpha=0.3)
        fig.tight_layout()
        out = os.path.join(out_dir, model, f"violin_assertions_vs_grade.png")
        os.makedirs(os.path.dirname(out), exist_ok=True)
        fig.savefig(out, dpi=150)
        plt.close(fig)
        print(f"  Saved {out}")


def plot_combined_box(model_data, out_path):
    """All models in one figure, vertical subplots: box plots."""
    ordered = [m for m in MODEL_ORDER if m in model_data]
    n = len(ordered)
    fig, axes = plt.subplots(n, 1, figsize=(7, 4 * n), sharex=True)
    if n == 1:
        axes = [axes]

    for idx, model in enumerate(ordered):
        ax = axes[idx]
        rows = model_data[model]
        label = MODEL_LABELS.get(model, model)

        box_data = []
        box_labels = []
        for g in GRADE_ORDER:
            vals = [r["assert_count"] for r in rows if r["grade"] == g]
            box_data.append(vals if vals else [])
            box_labels.append(f"{g} ({len(vals)})")

        bp = ax.boxplot(box_data, tick_labels=box_labels, patch_artist=True,
                        showmeans=True, meanprops=dict(marker="D", markerfacecolor="black", markersize=4))
        for patch, g in zip(bp["boxes"], GRADE_ORDER):
            patch.set_facecolor(GRADE_COLORS[g])
            patch.set_alpha(0.7)

        ax.set_title(label, fontsize=11, fontweight="bold")
        ax.set_ylabel("Assertion Count", fontsize=10)
        ax.grid(axis="y", alpha=0.3)

    axes[-1].set_xlabel("Quality Grade", fontsize=11)
    fig.suptitle("Assertion Count vs Quality Grade — All Models",
                 fontsize=14, fontweight="bold")
    fig.tight_layout()
    fig.savefig(out_path, dpi=150, bbox_inches="tight")
    plt.close(fig)
    print(f"  Saved {out_path}")


def plot_combined_mean_line(model_data, out_path):
    """Line plot: mean assertion count per grade for each model."""
    fig, ax = plt.subplots(figsize=(7, 8))
    markers = ["o", "s", "^", "D", "v"]
    colors_list = ["#1f77b4", "#ff7f0e", "#2ca02c", "#d62728", "#9467bd"]

    ordered = [m for m in MODEL_ORDER if m in model_data]
    for i, model in enumerate(ordered):
        rows = model_data[model]
        label = MODEL_LABELS.get(model, model)
        means = []
        medians = []
        x_pos = []
        for gi, g in enumerate(GRADE_ORDER):
            vals = [r["assert_count"] for r in rows if r["grade"] == g]
            if vals:
                means.append(np.mean(vals))
                medians.append(np.median(vals))
                x_pos.append(gi)

        ax.plot(x_pos, means, marker=markers[i % len(markers)],
                color=colors_list[i % len(colors_list)],
                linewidth=2, markersize=8, label=label)

    ax.set_xticks(range(len(GRADE_ORDER)))
    ax.set_xticklabels(GRADE_ORDER, fontsize=13, fontweight="bold")
    ax.set_xlabel("Quality Grade", fontsize=12)
    ax.set_ylabel("Mean Assertion Count", fontsize=12)
    ax.set_title("Mean Assertion Count by Quality Grade — All Models",
                 fontsize=14, fontweight="bold")
    ax.legend(fontsize=10)
    ax.grid(alpha=0.3)
    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    print(f"  Saved {out_path}")


def plot_combined_scatter(model_data, out_path):
    """Scatter: assertion count (x) vs quality score 0-100 (y) for all models, vertical."""
    fig, ax = plt.subplots(figsize=(7, 9))
    markers = ["o", "s", "^", "D", "v"]
    colors_list = ["#1f77b4", "#ff7f0e", "#2ca02c", "#d62728", "#9467bd"]

    ordered = [m for m in MODEL_ORDER if m in model_data]
    for i, model in enumerate(ordered):
        rows = model_data[model]
        label = MODEL_LABELS.get(model, model)
        pts = [(r["assert_count"], r["quality_score"]) for r in rows
               if r.get("quality_score") is not None]
        if not pts:
            continue
        x, y = zip(*pts)
        ax.scatter(x, y, alpha=0.4, s=22, label=label,
                   marker=markers[i % len(markers)],
                   color=colors_list[i % len(colors_list)],
                   edgecolors="none")

    # Grade threshold lines
    xmax = ax.get_xlim()[1]
    for score, grade, color in [(90, "A", GRADE_COLORS["A"]),
                                 (75, "B", GRADE_COLORS["B"]),
                                 (60, "C", GRADE_COLORS["C"]),
                                 (40, "D", GRADE_COLORS["D"])]:
        ax.axhline(y=score, color=color, linestyle="--", alpha=0.5, linewidth=1)
        ax.text(xmax * 0.95, score + 1,
                f"{grade} ≥ {score}", fontsize=8, color=color, va="bottom", ha="right")

    ax.set_xlabel("Assertion Count", fontsize=12)
    ax.set_ylabel("Quality Score", fontsize=12)
    ax.set_title("Assertion Count vs Quality Score — All Models",
                 fontsize=14, fontweight="bold")
    ax.legend(fontsize=9, loc="best")
    ax.grid(alpha=0.3)
    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    print(f"  Saved {out_path}")


def plot_scatter_score(model_data, out_path):
    """Scatter: x = assertion count, y = quality score (continuous), colored by model."""
    fig, ax = plt.subplots(figsize=(8, 10))
    markers = ["o", "s", "^", "D", "v"]
    colors_list = ["#1f77b4", "#ff7f0e", "#2ca02c", "#d62728", "#9467bd"]

    ordered = [m for m in MODEL_ORDER if m in model_data]
    for i, model in enumerate(ordered):
        rows = model_data[model]
        label = MODEL_LABELS.get(model, model)
        pts = [(r["assert_count"], r["quality_score"]) for r in rows
               if r.get("quality_score") is not None]
        if not pts:
            continue
        x, y = zip(*pts)
        ax.scatter(x, y, alpha=0.4, s=22, label=label,
                   marker=markers[i % len(markers)],
                   color=colors_list[i % len(colors_list)],
                   edgecolors="none")

    # Grade threshold lines
    xmax = ax.get_xlim()[1]
    for score, grade, color in [(90, "A", GRADE_COLORS["A"]),
                                 (75, "B", GRADE_COLORS["B"]),
                                 (60, "C", GRADE_COLORS["C"]),
                                 (40, "D", GRADE_COLORS["D"])]:
        ax.axhline(y=score, color=color, linestyle="--", alpha=0.5, linewidth=1)
        ax.text(xmax * 0.95, score + 1,
                f"{grade} ≥ {score}", fontsize=8, color=color, va="bottom", ha="right")

    ax.set_xlabel("Assertion Count", fontsize=12)
    ax.set_ylabel("Quality Score", fontsize=12)
    ax.set_title("Assertion Count vs Quality Score — All Models",
                 fontsize=14, fontweight="bold")
    ax.legend(fontsize=9, loc="best")
    ax.grid(alpha=0.3)
    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    print(f"  Saved {out_path}")


def plot_heatmap_per_model(model_data, out_dir):
    """Heatmap per model: x = assertion count bins, y = grade, color = count."""
    for model, rows in model_data.items():
        label = MODEL_LABELS.get(model, model)
        acs = [r["assert_count"] for r in rows]
        max_a = max(acs)
        n_bins = 8
        bin_edges = list(np.linspace(1, max_a + 1, n_bins + 1, dtype=int))
        bin_edges = sorted(set(bin_edges))
        bin_labels = []
        for i in range(len(bin_edges) - 1):
            lo, hi = bin_edges[i], bin_edges[i + 1] - 1
            bin_labels.append(f"{lo}-{hi}" if hi > lo else f"{lo}")

        matrix = np.zeros((len(GRADE_ORDER), len(bin_labels)))
        for r in rows:
            ac = r["assert_count"]
            g_idx = GRADE_ORDER.index(r["grade"])
            for bi in range(len(bin_edges) - 1):
                if bin_edges[bi] <= ac < bin_edges[bi + 1] or (bi == len(bin_edges) - 2 and ac >= bin_edges[bi]):
                    matrix[g_idx, bi] += 1
                    break

        fig, ax = plt.subplots(figsize=(10, 4))
        im = ax.imshow(matrix, aspect="auto", cmap="YlOrRd", origin="upper")
        ax.set_xticks(range(len(bin_labels)))
        ax.set_xticklabels(bin_labels, fontsize=9, rotation=45)
        ax.set_yticks(range(len(GRADE_ORDER)))
        ax.set_yticklabels(GRADE_ORDER, fontsize=12, fontweight="bold")
        ax.set_xlabel("Assertion Count", fontsize=11)
        ax.set_ylabel("Quality Grade", fontsize=11)
        ax.set_title(f"Assertion Count vs Grade Heatmap — {label}", fontsize=13, fontweight="bold")

        # Annotate cells
        for i in range(matrix.shape[0]):
            for j in range(matrix.shape[1]):
                v = int(matrix[i, j])
                if v > 0:
                    ax.text(j, i, str(v), ha="center", va="center", fontsize=9,
                            color="white" if v > matrix.max() * 0.5 else "black")

        fig.colorbar(im, ax=ax, label="Count")
        fig.tight_layout()
        out = os.path.join(out_dir, model, f"heatmap_assertions_vs_grade.png")
        os.makedirs(os.path.dirname(out), exist_ok=True)
        fig.savefig(out, dpi=150)
        plt.close(fig)
        print(f"  Saved {out}")


def main():
    script_dir = os.path.dirname(os.path.abspath(__file__))
    base_dir = os.path.dirname(script_dir)
    io_dir = os.path.join(base_dir, "runs", "inference")

    if not os.path.isdir(io_dir):
        print(f"ERROR: {io_dir} not found")
        sys.exit(1)

    # Discover models
    models = [d for d in sorted(os.listdir(io_dir))
              if os.path.isdir(os.path.join(io_dir, d))
              and d not in ("syntax_results", "verification_results", "dataset_stats")]

    print(f"Models found: {models}")

    model_data = {}
    for model in models:
        rows = load_model_data(io_dir, model)
        if rows:
            model_data[model] = rows
            print(f"  {model}: {len(rows)} designs with grade + assertions")
        else:
            print(f"  {model}: no graded data found, skipping")

    if not model_data:
        print("No graded data found for any model.")
        sys.exit(1)

    stats_dir = os.path.join(base_dir, "reports", "inference")
    comp_dir = os.path.join(stats_dir, "_comparison")
    os.makedirs(comp_dir, exist_ok=True)

    # Per-model plots (saved in dataset_stats/{model}/)
    plot_box_per_model(model_data, stats_dir)
    plot_violin_per_model(model_data, stats_dir)
    plot_heatmap_per_model(model_data, stats_dir)

    # Combined comparison plots
    plot_combined_box(model_data, os.path.join(comp_dir, "box_assertions_vs_grade_all.png"))
    plot_combined_mean_line(model_data, os.path.join(comp_dir, "mean_assertions_vs_grade_all.png"))
    plot_combined_scatter(model_data, os.path.join(comp_dir, "scatter_assertions_vs_grade_all.png"))
    plot_scatter_score(model_data, os.path.join(comp_dir, "scatter_assertions_vs_score_all.png"))

    print("\nDone.")


if __name__ == "__main__":
    main()
