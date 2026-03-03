#!/usr/bin/env python3
"""
Plot verification result statistics from verif_summary.csv.

Generates two figures:
  1. Pie chart of pass vs fail percentages.
  2. Bar chart breaking down failure reasons into categories:
     - Bind Error            (bind likely didn't attach / wrong TOP)
     - Syntax Error          (syntax error)
     - Missing Signal Error  (is not declared)
     - Compile/Elab Error    (compile/elab errors, VERI-* codes)
     - Unknown Error         (unclassifiable failures)
"""

import csv
import re
import os
import matplotlib.pyplot as plt

# ── Paths ────────────────────────────────────────────────────────────────────
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
CSV_PATH = os.path.join(SCRIPT_DIR, "verif_summary.csv")
OUT_DIR = SCRIPT_DIR  # save PNGs next to the CSV

# ── Exclude non-sample rows that snuck into the CSV ─────────────────────────
EXCLUDE_IDS = {"jgproject", "metadata", "myenv"}

# ── Read & classify ─────────────────────────────────────────────────────────
total = 0
passes = 0
fails = 0

bind_errors = 0
syntax_errors = 0
missing_signal_errors = 0
compile_elab_errors = 0
unknown_errors = 0

with open(CSV_PATH, newline="", encoding="utf-8") as f:
    reader = csv.DictReader(f)
    for row in reader:
        sample_id = row["id"].strip()
        if sample_id in EXCLUDE_IDS:
            continue

        total += 1
        status = row["status"].strip().lower()
        reason = row.get("reason", "") or ""

        if status == "pass":
            passes += 1
            continue

        # It's a failure
        fails += 1
        reason_lower = reason.lower()

        if "bind likely didn" in reason_lower or "wrong top" in reason_lower:
            bind_errors += 1
        elif "syntax error" in reason_lower:
            syntax_errors += 1
        elif "is not declared" in reason_lower:
            missing_signal_errors += 1
        elif "compile/elab errors" in reason_lower or "error (veri-" in reason_lower:
            compile_elab_errors += 1
        else:
            unknown_errors += 1

# ── Sanity print ─────────────────────────────────────────────────────────────
print(f"Total IDs:              {total}")
print(f"  Passes:               {passes}  ({passes/total*100:.1f}%)")
print(f"  Fails:                {fails}  ({fails/total*100:.1f}%)")
print(f"    Bind Error:         {bind_errors}  ({bind_errors/total*100:.1f}%)")
print(f"    Syntax Error:       {syntax_errors}  ({syntax_errors/total*100:.1f}%)")
print(f"    Missing Signal:     {missing_signal_errors}  ({missing_signal_errors/total*100:.1f}%)")
print(f"    Compile/Elab Error: {compile_elab_errors}  ({compile_elab_errors/total*100:.1f}%)")
print(f"    Unknown Error:      {unknown_errors}  ({unknown_errors/total*100:.1f}%)")

# ── Figure 1: Pass vs Fail bar chart ─────────────────────────────────────────
fig1, ax1 = plt.subplots(figsize=(6, 5))
labels_pf = ["Pass", "Fail"]
counts_pf = [passes, fails]
pcts_pf = [c / total * 100 for c in counts_pf]
colors_pf = ["#4CAF50", "#F44336"]

bars_pf = ax1.bar(labels_pf, counts_pf, color=colors_pf, edgecolor="black", linewidth=0.6, width=0.5)

for bar, cnt, pct in zip(bars_pf, counts_pf, pcts_pf):
    ax1.text(
        bar.get_x() + bar.get_width() / 2,
        bar.get_height() + total * 0.01,
        f"{cnt}\n({pct:.1f}%)",
        ha="center",
        va="bottom",
        fontsize=13,
        fontweight="bold",
    )

ax1.set_ylabel("Number of IDs", fontsize=12)
ax1.set_ylim(0, total)
ax1.set_title("Verification: Pass vs Fail", fontsize=15, fontweight="bold")
ax1.spines["top"].set_visible(False)
ax1.spines["right"].set_visible(False)
fig1.tight_layout()
fig1.savefig(os.path.join(OUT_DIR, "pass_vs_fail.png"), dpi=200)
print(f"\nSaved  {os.path.join(OUT_DIR, 'pass_vs_fail.png')}")

# ── Figure 2: Error category pie chart ───────────────────────────────────────
fig2, ax2 = plt.subplots(figsize=(8, 7))
categories = ["Bind Error", "Syntax Error", "Missing Signal\nError", "Compile/Elab\nError", "Unknown Error"]
counts = [bind_errors, syntax_errors, missing_signal_errors, compile_elab_errors, unknown_errors]
pie_colors = ["#FF9800", "#E91E63", "#9C27B0", "#2196F3", "#607D8B"]

wedges, texts, autotexts = ax2.pie(
    counts,
    labels=categories,
    colors=pie_colors,
    autopct=lambda p: f"{p:.1f}%\n({int(round(p * fails / 100))})",
    startangle=140,
    textprops={"fontsize": 11},
    pctdistance=0.75,
)
for at in autotexts:
    at.set_fontweight("bold")
ax2.set_title("Failure Breakdown by Error Category", fontsize=14, fontweight="bold")
fig2.tight_layout()
fig2.savefig(os.path.join(OUT_DIR, "error_breakdown.png"), dpi=200)
print(f"Saved  {os.path.join(OUT_DIR, 'error_breakdown.png')}")

plt.show()
