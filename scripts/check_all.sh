#!/usr/bin/env bash
set -euo pipefail

# ============================================================
# Unified JasperGold checker for any dataset directory.
#
# Usage:
#   ./check_all.sh <mode> <dataset_dir>
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
# ============================================================

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# ── Parse args ───────────────────────────────────────────────
if [[ $# -lt 2 ]]; then
  echo "Usage: $0 <syntax|verif> <dataset_dir>"
  echo ""
  echo "  syntax  Compile/syntax check only"
  echo "  verif   Full assertion verification"
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
  mkdir -p "$RESULTS_BASE/syntax_results/$VERSION_NAME"
  local SUMMARY_CSV="$RESULTS_BASE/syntax_results/$VERSION_NAME/summary.csv"
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
      local out_dir="$RESULTS_BASE/syntax_results/$VERSION_NAME/$id"
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
}

# ============================================================
#  VERIF MODE
# ============================================================
run_verif() {
  mkdir -p "$RESULTS_BASE/verification_results/$VERSION_NAME"

  local SUMMARY_CSV="$RESULTS_BASE/verification_results/$VERSION_NAME/summary.csv"
  local VERIF_CSV="$RESULTS_BASE/verification_results/$VERSION_NAME/verif_summary.csv"

  echo "id,status" > "$SUMMARY_CSV"
  echo "id,status,reason" > "$VERIF_CSV"

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
      local out_dir="$RESULTS_BASE/verification_results/$VERSION_NAME/$id"
      mkdir -p "$out_dir"
      local done_marker="$out_dir/DONE"
      local proj_dir="$out_dir/jgproject"

      # Resume: skip if already attempted
      if [[ -f "$done_marker" ]]; then
        echo "⏭️  Skipping $id (already attempted)"
        local existing_log="$out_dir/run.log"
        if [[ -f "$existing_log" ]]; then
          if grep -q '\- cex' "$existing_log" 2>/dev/null; then
            local cex_count
            cex_count=$(grep -oP '(?<=- cex\s{1,20}: )\d+' "$existing_log" 2>/dev/null || echo "0")
            if [[ "$cex_count" != "0" ]]; then
              echo "$id,cex,proof completed with $cex_count counter-example(s)" >> "$VERIF_CSV"
            else
              echo "$id,pass," >> "$VERIF_CSV"
            fi
          elif grep -q "FAILED" "$existing_log" 2>/dev/null; then
            local reason
            reason=$(extract_reason "$existing_log")
            echo "$id,fail,\"$reason\"" >> "$VERIF_CSV"
          else
            echo "$id,pass," >> "$VERIF_CSV"
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
      JG_OUT_DIR="$out_dir" \
      jaspergold -batch -allow_unsupported_OS \
        -proj "$proj_dir" \
        -tcl "$TCL_FILE" \
        >"$out_dir/run.log" 2>&1 && {

        echo "✅ $id VERIF RUN OK"
        echo "$id,ok" >> "$SUMMARY_CSV"

        if grep -q '\- cex' "$out_dir/run.log" 2>/dev/null; then
          local cex_count
          cex_count=$(grep -oP '(?<=- cex\s{1,20}: )\d+' "$out_dir/run.log" 2>/dev/null || echo "0")
          if [[ "$cex_count" != "0" ]]; then
            echo "$id,cex,proof completed with $cex_count counter-example(s)" >> "$VERIF_CSV"
          else
            echo "$id,pass," >> "$VERIF_CSV"
          fi
        else
          echo "$id,pass," >> "$VERIF_CSV"
        fi

        touch "$done_marker"

      } || {

        echo "❌ $id VERIF RUN FAIL"
        echo "$id,fail" >> "$SUMMARY_CSV"
        local reason
        reason=$(extract_reason "$out_dir/run.log")
        echo "$id,fail,\"$reason\"" >> "$VERIF_CSV"

        touch "$done_marker"
      }

    else
      echo "⚠️  Skipping $id (missing module.v or sva.sv)"
      echo "$id,skip,missing module.v or sva.sv" >> "$VERIF_CSV"
    fi
  done

  echo "=============================="
  echo "Verification complete."
  echo "Summary CSV : $SUMMARY_CSV"
  echo "Detail CSV  : $VERIF_CSV"
}

# ── Dispatch ─────────────────────────────────────────────────
case "$MODE" in
  syntax) run_syntax ;;
  verif)  run_verif  ;;
esac
