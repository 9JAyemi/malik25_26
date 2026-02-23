#!/usr/bin/env bash
set -euo pipefail

ROOT="${ROOT:-.}"
# Use a job-specific temp dir if running under Slurm
export TMPDIR="${TMPDIR:-/tmp}/${USER}/jg_${SLURM_JOB_ID:-$$}"
mkdir -p "$TMPDIR"
trap 'rm -rf "$TMPDIR"' EXIT
# Find the verification TCL
if [[ -f "./jasper_verif_check.tcl" ]]; then
  JASPER_TCL="./jasper_verif_check.tcl"
elif [[ -f "../jasper_verif_check.tcl" ]]; then
  JASPER_TCL="../jasper_verif_check.tcl"
else
  echo "❌ jasper_verif_check.tcl not found!"
  exit 1
fi

mkdir -p verification_results
: > verification_results/summary.csv
echo "id,status" >> verification_results/summary.csv

VERIF_CSV="verification_results/verif_summary.csv"
: > "$VERIF_CSV"
echo "id,status,reason" >> "$VERIF_CSV"

# Extract a one-line failure reason from a Jasper run log
extract_reason() {
  local log="$1"
  local reason=""

  # Priority order: compile/elab errors, no-properties, cex failures, then generic
  if grep -q "FAILED: compile/elab errors" "$log" 2>/dev/null; then
    # Grab the first ERROR line for detail
    reason="compile/elab error: $(grep -m1 '\[ERROR' "$log" | sed 's/,/;/g' | head -c 200)"
  elif grep -q "No properties found" "$log" 2>/dev/null; then
    reason="no properties found (bind did not attach or wrong TOP)"
  elif grep -q "Could not infer TOP" "$log" 2>/dev/null; then
    reason="could not infer TOP module"
  elif grep -q "analyze design failed" "$log" 2>/dev/null; then
    reason="analyze design failed: $(grep -m1 '\[ERROR' "$log" | sed 's/,/;/g' | head -c 200)"
  elif grep -q "analyze SVA failed" "$log" 2>/dev/null; then
    reason="analyze SVA failed: $(grep -m1 '\[ERROR' "$log" | sed 's/,/;/g' | head -c 200)"
  elif grep -q "elaborate failed" "$log" 2>/dev/null; then
    reason="elaborate failed: $(grep -m1 '\[ERROR' "$log" | sed 's/,/;/g' | head -c 200)"
  elif grep -q "prove command failed" "$log" 2>/dev/null; then
    reason="prove command failed"
  elif grep -q '\- cex' "$log" 2>/dev/null; then
    # Ran to completion but had counter-examples
    local cex_count
    cex_count=$(grep -oP '(?<=- cex\s{1,20}: )\d+' "$log" 2>/dev/null || echo "?")
    reason="proof completed with $cex_count counter-example(s)"
  else
    reason="unknown failure (check run.log)"
  fi

  echo "$reason"
}

echo "=============================="
echo "Running Jasper verification..."
echo "TCL : $JASPER_TCL"
echo "Root: $ROOT"
echo "=============================="

shopt -s nullglob
for dir in "$ROOT"/*/; do
  id="$(basename "$dir")"
  [[ "$id" == "verification_results" ]] && continue
  [[ "$id" == "syntax_results" ]] && continue

  module_file="${dir%/}/module.v"
  sva_file="${dir%/}/sva.sv"

  if [[ -f "$module_file" && -f "$sva_file" ]]; then
    echo "🔍 Verifying $id ..."
    out_dir="verification_results/$id"
    mkdir -p "$out_dir"
    proj_dir="$out_dir/jgproject"

    # (Optional) clean stale project dir to avoid lock issues
    rm -rf "$proj_dir"

    # Env → Tcl; unique project dir; log via shell redirection
    DESIGN_ID="$id" \
    JG_TOP="${JG_TOP:-}" \
    JG_DESIGN="$module_file" \
    JG_SVA="$sva_file" \
    JG_STD="${JG_STD:-sv12}" \
    JG_INCDIRS="${JG_INCDIRS:-}" \
    JG_DEFINES="${JG_DEFINES:-}" \
    JG_NO_CLOCK="${JG_NO_CLOCK:-1}" \
    srun --exclusive -N1 -n1 -c ${SLURM_CPUS_PER_TASK:-4} \
    jaspergold -batch -allow_unsupported_OS \
    -proj "$proj_dir" \
    -tcl "$JASPER_TCL" \
    >"$out_dir/run.log" 2>&1 && {
        echo "✅ $id VERIF RUN OK"
        echo "$id,ok" >> verification_results/summary.csv
        # Still check for cex in passing runs
        if grep -q '\- cex' "$out_dir/run.log" 2>/dev/null; then
          cex_count=$(grep -oP '(?<=- cex\s{1,20}: )\d+' "$out_dir/run.log" 2>/dev/null || echo "0")
          if [[ "$cex_count" != "0" ]]; then
            echo "$id,cex,proof completed with $cex_count counter-example(s)" >> "$VERIF_CSV"
          else
            echo "$id,pass," >> "$VERIF_CSV"
          fi
        else
          echo "$id,pass," >> "$VERIF_CSV"
        fi
      } || {
        echo "❌ $id VERIF RUN FAIL"
        echo "$id,fail" >> verification_results/summary.csv
        reason=$(extract_reason "$out_dir/run.log")
        echo "$id,fail,\"$reason\"" >> "$VERIF_CSV"
      }
  else
    echo "⚠️  Skipping $id (missing module.v or sva.sv)"
    echo "$id,skip,missing module.v or sva.sv" >> "$VERIF_CSV"
  fi
done

echo "=============================="
echo "Summary written to verification_results/summary.csv"
cat verification_results/summary.csv
echo ""
echo "Detailed summary written to $VERIF_CSV"
cat "$VERIF_CSV"
