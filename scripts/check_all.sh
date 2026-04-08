#!/usr/bin/env bash
set -euo pipefail

# ============================================================
# Unified JasperGold checker for any dataset directory.
#
# Usage:
#   ./check_all.sh [--force] <mode> <dataset_dir>
#
# Options:
#   --force   Re-run all IDs even if DONE marker exists
#
# Modes:
#   syntax  – compile/syntax check only     (uses jasper_syntax_check.tcl)
#   verif   – full assertion verification    (uses jasper_verif_check.tcl)
#
# Results are placed under <dataset_dir>/../ (the "dataset" folder):
#   metrex/dataset/syntax_results/
#   metrex/dataset/verification_results/
#
# Examples:
#   ./scripts/check_all.sh syntax metrex/dataset/version_1
#   ./scripts/check_all.sh verif  veri_thoughts/dataset/version_1
#   ./scripts/check_all.sh --force verif veri_thoughts/dataset/version_2
# ============================================================

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# ── Parse args ───────────────────────────────────────────────
FORCE=0
if [[ "${1:-}" == "--force" ]]; then
  FORCE=1
  shift
fi

if [[ $# -lt 2 ]]; then
  echo "Usage: $0 [--force] <syntax|verif> <dataset_dir>"
  echo ""
  echo "  --force  Re-run all IDs even if DONE marker exists"
  echo "  syntax   Compile/syntax check only"
  echo "  verif    Full assertion verification"
  exit 1
fi

MODE="$1"
DATASET_DIR="$(cd "$2" && pwd)"

case "$MODE" in
  syntax)
    TCL_FILE="$SCRIPT_DIR/jasper_syntax_check.tcl"
    ;;
  verif)
    TCL_FILE="$SCRIPT_DIR/jasper_verif_check.tcl"
    ;;
  *)
    echo "❌ Unknown mode '$MODE'. Use 'syntax' or 'verif'."
    exit 1
    ;;
esac

if [[ ! -f "$TCL_FILE" ]]; then
  echo "❌ TCL file not found: $TCL_FILE"
  exit 1
fi

# ── Common setup ─────────────────────────────────────────────
export TMPDIR="${TMPDIR:-/tmp}/${USER}/jg_${SLURM_JOB_ID:-$$}"
mkdir -p "$TMPDIR"
trap 'rm -rf "$TMPDIR"' EXIT
export OMP_NUM_THREADS="${SLURM_CPUS_PER_TASK:-4}"

# Results go under the parent of the version dir (i.e., dataset/), namespaced by version
RESULTS_BASE="$(cd "$DATASET_DIR/.." && pwd)"
VERSION_NAME="$(basename "$DATASET_DIR")"

cd "$DATASET_DIR"

# ── Read AUTO_BIND from summary.txt ──────────────────────────
get_auto_bind() {
  local out_dir="$1"
  local summary="$out_dir/summary.txt"
  if [[ -f "$summary" ]]; then
    grep -oP '(?<=AUTO_BIND=)\d+' "$summary" 2>/dev/null || echo ""
  else
    echo ""
  fi
}

# ── Read vacuity counts from summary.txt ─────────────────────
get_vacuous_count() {
  local out_dir="$1"
  local summary="$out_dir/summary.txt"
  if [[ -f "$summary" ]]; then
    grep -oP '(?<=VACUOUS_COUNT=)\d+' "$summary" 2>/dev/null || echo "0"
  else
    echo "0"
  fi
}

get_non_vacuous_count() {
  local out_dir="$1"
  local summary="$out_dir/summary.txt"
  if [[ -f "$summary" ]]; then
    grep -oP '(?<=NON_VACUOUS_COUNT=)\d+' "$summary" 2>/dev/null || echo "0"
  else
    echo "0"
  fi
}

# ── Failure reason extractor (verif mode) ────────────────────
extract_reason() {
  local log="$1"
  local reason=""

  if grep -q "FAILED: compile/elab errors" "$log" 2>/dev/null; then
    reason="❌ FAILED: compile/elab errors | $(grep -m1 '\[ERROR' "$log" | sed 's/,/;/g' | head -c 200)"
  elif grep -q "FAILED: No properties found" "$log" 2>/dev/null; then
    reason="❌ FAILED: No properties found (bind likely didn't attach; or wrong TOP)"
  elif grep -q "Could not infer TOP" "$log" 2>/dev/null; then
    reason="❌ FAILED: could not infer TOP module"
  elif grep -q "analyze design failed" "$log" 2>/dev/null; then
    reason="❌ FAILED: analyze design failed | $(grep -m1 '\[ERROR' "$log" | sed 's/,/;/g' | head -c 200)"
  elif grep -q "analyze SVA failed" "$log" 2>/dev/null; then
    reason="❌ FAILED: analyze SVA failed | $(grep -m1 '\[ERROR' "$log" | sed 's/,/;/g' | head -c 200)"
  elif grep -q "elaborate failed" "$log" 2>/dev/null; then
    reason="❌ FAILED: elaborate failed | $(grep -m1 '\[ERROR' "$log" | sed 's/,/;/g' | head -c 200)"
  elif grep -q "prove command failed" "$log" 2>/dev/null; then
    reason="❌ FAILED: prove command failed"
  elif grep -q '\- cex' "$log" 2>/dev/null; then
    local cex_count
    cex_count=$(grep -oP '(?<=- cex\s{1,20}: )\d+' "$log" 2>/dev/null || echo "?")
    reason="proof completed with $cex_count counter-example(s)"
  else
    reason="❌ FAILED: unknown failure (check run.log)"
  fi

  echo "$reason"
}

# ============================================================
#  SYNTAX MODE
# ============================================================
run_syntax() {
  mkdir -p "$RESULTS_BASE/syntax_results/$VERSION_NAME/visual_data"
  local SUMMARY_CSV="$RESULTS_BASE/syntax_results/$VERSION_NAME/visual_data/summary.csv"
  echo "id,status" > "$SUMMARY_CSV"

  echo "=============================="
  echo "Running Jasper syntax checks..."
  echo "TCL    : $TCL_FILE"
  echo "Dataset: $DATASET_DIR"
  echo "=============================="

  shopt -s nullglob
  for dir in ./*/; do
    local id="$(basename "$dir")"
    [[ "$id" == "syntax_results" || "$id" == "verification_results" || "$id" == "metadata" ]] && continue

    local module_file="$dir/module.v"
    local sva_file="$dir/sva.sv"

    if [[ -f "$module_file" && -f "$sva_file" ]]; then
      echo "🔍 Checking $id ..."
      local out_dir="$RESULTS_BASE/syntax_results/$VERSION_NAME/ids/$id"
      mkdir -p "$out_dir"

      JG_DIR="$dir" \
      JG_STD="${JG_STD:-sv12}" \
      JG_HALT_ON_WARN="${JG_HALT_ON_WARN:-1}" \
      JG_INCDIRS="${JG_INCDIRS:-}" \
      JG_DEFINES="${JG_DEFINES:-}" \
      JG_TOP="${JG_TOP:-}" \
      jaspergold -batch -allow_unsupported_OS -proj "$out_dir/jgproject" -tcl "$TCL_FILE" \
        >"$out_dir/log.txt" 2>&1 && {
          echo "✅ $id PASSED"
          echo "$id,ok" >> "$SUMMARY_CSV"
        } || {
          echo "❌ $id FAILED"
          echo "$id,fail" >> "$SUMMARY_CSV"
        }
    else
      echo "⚠️  Skipping $id (missing module.v or sva.sv)"
    fi
  done

  echo "=============================="
  echo "Summary written to $SUMMARY_CSV"

  # Generate syntax pass/fail pie chart
  python3 - "$SUMMARY_CSV" <<'PYEOF'
import csv, sys, os
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

csv_path = sys.argv[1]
out_dir = os.path.dirname(csv_path)

n_pass = 0
n_fail = 0
with open(csv_path, newline="") as f:
    reader = csv.DictReader(f)
    for row in reader:
        status = row["status"].strip().lower()
        if status == "ok":
            n_pass += 1
        elif status == "fail":
            n_fail += 1

total = n_pass + n_fail
if total == 0:
    sys.exit(0)

# Bar chart
fig1, ax1 = plt.subplots(figsize=(7, 5))
bars = ax1.bar(["Pass", "Fail"], [n_pass, n_fail],
               color=["#4CAF50", "#F44336"], edgecolor="black", linewidth=0.5)
for bar, val in zip(bars, [n_pass, n_fail]):
    pct = val / total * 100
    ax1.text(bar.get_x() + bar.get_width() / 2, bar.get_height() + total * 0.01,
             f"{val:,}\n({pct:.1f}%)", ha="center", va="bottom", fontweight="bold", fontsize=12)
ax1.set_ylabel("Number of IDs", fontsize=12)
ax1.set_title(f"Syntax Check Results\n(Total: {total:,} IDs)", fontsize=13, fontweight="bold")
ax1.set_ylim(0, max(n_pass, n_fail) * 1.25)
fig1.tight_layout()
bar_path = os.path.join(out_dir, "syntax_pass_fail_bar.png")
fig1.savefig(bar_path, dpi=150)
plt.close(fig1)
print(f"Saved {bar_path}")

# Pie chart
fig2, ax2 = plt.subplots(figsize=(7, 5))
sizes, labels, colors = [], [], []
if n_pass > 0:
    sizes.append(n_pass); labels.append(f"Pass\n({n_pass:,})"); colors.append("#4CAF50")
if n_fail > 0:
    sizes.append(n_fail); labels.append(f"Fail\n({n_fail:,})"); colors.append("#F44336")
wedges, texts, autotexts = ax2.pie(
    sizes, labels=labels, colors=colors, autopct="%1.1f%%",
    startangle=90, pctdistance=0.6,
    wedgeprops=dict(edgecolor="black", linewidth=0.5))
for t in autotexts:
    t.set_fontsize(12); t.set_fontweight("bold")
ax2.set_title("Syntax Pass Rate", fontsize=13, fontweight="bold")
fig2.tight_layout()
pie_path = os.path.join(out_dir, "syntax_pass_fail_pie.png")
fig2.savefig(pie_path, dpi=150)
plt.close(fig2)
print(f"Saved {pie_path}")

# ── Error distribution chart ──
import re
from collections import Counter

ids_dir = os.path.join(os.path.dirname(out_dir), "ids")

# Map error codes to short human-readable descriptions
ERROR_LABELS = {
    "VERI-1137": "syntax error",
    "VERI-1072": "module ignored (prior errors)",
    "VERI-1128": "undeclared identifier",
    "VERI-1138": "unexpected EOF",
    "VERI-9023": "unterminated design unit",
    "VERI-9011": "duplicate block id",
    "VERI-1967": "type mismatch",
    "VERI-2344": "keyword in wrong context",
    "VERI-1482": "analyze failed",
    "VERI-1116": "already declared",
    "VERI-1130": "invalid in expression",
    "VERI-1140": "wrong number of args",
    "VERI-1384": "illegal assignment pattern",
    "VERI-1905": "unsupported construct",
    "VERI-1976": "invalid clocking argument",
    "VERI-1208": "port connection error",
    "VERI-1321": "event expr not allowed here",
    "VERI-1243": "operator only in property",
}

# Count unique error codes per failing ID
error_counts = Counter()
with open(csv_path, newline="") as f:
    reader = csv.DictReader(f)
    for row in reader:
        if row["status"].strip().lower() != "fail":
            continue
        log_path = os.path.join(ids_dir, row["id"], "log.txt")
        if not os.path.isfile(log_path):
            continue
        with open(log_path, errors="replace") as lf:
            codes = set(re.findall(r"VERI-\d+", lf.read()))
            error_counts.update(codes)

if error_counts:
    top = error_counts.most_common(10)
    codes = [c for c, _ in top]
    counts = [n for _, n in top]
    labels = [f"{c}\n{ERROR_LABELS.get(c, '?')}" for c in codes]

    fig2, ax = plt.subplots(figsize=(10, 6))
    x_pos = range(len(codes))
    bars = ax.bar(x_pos, counts, color="#2196F3", edgecolor="black", linewidth=0.4)
    ax.set_xticks(list(x_pos))
    ax.set_xticklabels(labels, fontsize=7.5, ha="center", linespacing=1.2)
    for bar, val in zip(bars, counts):
        ax.text(bar.get_x() + bar.get_width() / 2, bar.get_height() + max(counts) * 0.01,
                f"{val}", ha="center", va="bottom", fontsize=10, fontweight="bold")
    ax.set_ylabel("Number of IDs with Error", fontsize=11)
    ax.set_title(f"Top Syntax Error Codes — {n_fail} Failing IDs", fontsize=13, fontweight="bold")
    ax.set_ylim(0, max(counts) * 1.15)
    fig2.tight_layout()
    err_path = os.path.join(out_dir, "syntax_error_distribution.png")
    fig2.savefig(err_path, dpi=150)
    plt.close(fig2)
    print(f"Saved {err_path}")
PYEOF
}

# ============================================================
#  VERIF MODE
# ============================================================
run_verif() {
  mkdir -p "$RESULTS_BASE/verification_results/$VERSION_NAME/ids"
  mkdir -p "$RESULTS_BASE/verification_results/$VERSION_NAME/visual_data"

  local VERIF_CSV="$RESULTS_BASE/verification_results/$VERSION_NAME/visual_data/verif_summary.csv"

  echo "id,status,reason,auto_bind,vacuous,non_vacuous" > "$VERIF_CSV"

  echo "=============================="
  echo "Running Jasper verification..."
  echo "TCL    : $TCL_FILE"
  echo "Dataset: $DATASET_DIR"
  echo "=============================="

  shopt -s nullglob
  for dir in ./*/; do
    local id="$(basename "$dir")"
    [[ "$id" == "verification_results" || "$id" == "syntax_results" || "$id" == "metadata" ]] && continue

    local module_file="${dir%/}/module.v"
    local sva_file="${dir%/}/sva.sv"

    if [[ -f "$module_file" && -f "$sva_file" ]]; then
      local out_dir="$RESULTS_BASE/verification_results/$VERSION_NAME/ids/$id"
      mkdir -p "$out_dir"
      local done_marker="$out_dir/DONE"
      local proj_dir="$out_dir/jgproject"

      # Resume: skip if already attempted (unless --force)
      if [[ "$FORCE" -eq 0 && -f "$done_marker" ]]; then
        echo "⏭️  Skipping $id (already attempted)"
        local existing_log="$out_dir/run.log"
        local ab
        ab=$(get_auto_bind "$out_dir")
        local vac
        vac=$(get_vacuous_count "$out_dir")
        local nvac
        nvac=$(get_non_vacuous_count "$out_dir")
        if [[ -f "$existing_log" ]]; then
          if grep -q '\- cex' "$existing_log" 2>/dev/null; then
            local cex_count
            cex_count=$(grep -oP '(?<=- cex\s{1,20}: )\d+' "$existing_log" 2>/dev/null || echo "0")
            if [[ "$cex_count" != "0" ]]; then
              echo "$id,cex,proof completed with $cex_count counter-example(s),$ab,$vac,$nvac" >> "$VERIF_CSV"
            else
              echo "$id,pass,,$ab,$vac,$nvac" >> "$VERIF_CSV"
            fi
          elif grep -q "FAILED" "$existing_log" 2>/dev/null; then
            local reason
            reason=$(extract_reason "$existing_log")
            echo "$id,fail,\"$reason\",$ab,$vac,$nvac" >> "$VERIF_CSV"
          else
            echo "$id,pass,,$ab,$vac,$nvac" >> "$VERIF_CSV"
          fi
        fi
        continue
      fi

      echo "🔍 Verifying $id ..."
      rm -rf "$proj_dir"

      DESIGN_ID="$id" \
      JG_TOP="${JG_TOP:-}" \
      JG_DESIGN="$module_file" \
      JG_SVA="$sva_file" \
      JG_STD="${JG_STD:-sv12}" \
      JG_INCDIRS="${JG_INCDIRS:-}" \
      JG_DEFINES="${JG_DEFINES:-}" \
      JG_NO_CLOCK="${JG_NO_CLOCK:-1}" \
      JG_DUMP_VCD="${JG_DUMP_VCD:-0}" \
      JG_OUT_DIR="$out_dir" \
      jaspergold -batch -allow_unsupported_OS \
        -proj "$proj_dir" \
        -tcl "$TCL_FILE" \
        >"$out_dir/run.log" 2>&1 && {

        echo "✅ $id VERIF RUN OK"
        local ab
        ab=$(get_auto_bind "$out_dir")
        local vac
        vac=$(get_vacuous_count "$out_dir")
        local nvac
        nvac=$(get_non_vacuous_count "$out_dir")

        if grep -q '\- cex' "$out_dir/run.log" 2>/dev/null; then
          local cex_count
          cex_count=$(grep -oP '(?<=- cex\s{1,20}: )\d+' "$out_dir/run.log" 2>/dev/null || echo "0")
          if [[ "$cex_count" != "0" ]]; then
            echo "$id,cex,proof completed with $cex_count counter-example(s),$ab,$vac,$nvac" >> "$VERIF_CSV"
          else
            echo "$id,pass,,$ab,$vac,$nvac" >> "$VERIF_CSV"
          fi
        else
          echo "$id,pass,,$ab,$vac,$nvac" >> "$VERIF_CSV"
        fi

        touch "$done_marker"

      } || {

        echo "❌ $id VERIF RUN FAIL"
        local reason
        reason=$(extract_reason "$out_dir/run.log")
        local ab
        ab=$(get_auto_bind "$out_dir")
        local vac
        vac=$(get_vacuous_count "$out_dir")
        local nvac
        nvac=$(get_non_vacuous_count "$out_dir")
        echo "$id,fail,\"$reason\",$ab,$vac,$nvac" >> "$VERIF_CSV"

        touch "$done_marker"
      }

    else
      echo "⚠️  Skipping $id (missing module.v or sva.sv)"
      echo "$id,skip,missing module.v or sva.sv,,0,0" >> "$VERIF_CSV"
    fi
  done

  echo "=============================="
  echo "Verification complete."
  echo "Verif CSV : $VERIF_CSV"
}

# ── Dispatch ─────────────────────────────────────────────────
case "$MODE" in
  syntax) run_syntax ;;
  verif)  run_verif  ;;
esac
