#!/usr/bin/env bash
set -euo pipefail

ID="${1:?Usage: $0 <ID>}"
ROOT="${ROOT:-.}"

# temp dir isolation
export TMPDIR="${TMPDIR:-/tmp}/${USER}/jg_${SLURM_JOB_ID:-$$}_${SLURM_ARRAY_TASK_ID:-0}"
mkdir -p "$TMPDIR"
trap 'rm -rf "$TMPDIR"' EXIT

# optional thread hint
export OMP_NUM_THREADS="${SLURM_CPUS_PER_TASK:-1}"

# Locate verification TCL
if [[ -f "$ROOT/jasper_verif_check.tcl" ]]; then
  JASPER_TCL="$ROOT/jasper_verif_check.tcl"
elif [[ -f "$ROOT/../jasper_verif_check.tcl" ]]; then
  JASPER_TCL="$ROOT/../jasper_verif_check.tcl"
else
  echo "❌ jasper_verif_check.tcl not found!"
  exit 1
fi

dir="$ROOT/$ID"
module_file="$dir/module.v"
sva_file="$dir/sva.sv"

out_dir="$ROOT/verification_results/$ID"
proj_dir="$out_dir/jgproject"
done_marker="$out_dir/DONE"
run_log="$out_dir/run.log"

mkdir -p "$out_dir"

# Resume: skip if already attempted
if [[ -f "$done_marker" ]]; then
  echo "⏭️  Skipping $ID (already attempted)"
  exit 0
fi

# Validate inputs
if [[ ! -f "$module_file" || ! -f "$sva_file" ]]; then
  echo "⚠️  Skipping $ID (missing module.v or sva.sv)"
  echo "$ID,skip,missing module.v or sva.sv" >> "$ROOT/verification_results/verif_summary.csv" || true
  touch "$done_marker"
  exit 0
fi

# clean stale project
rm -rf "$proj_dir"

echo "🔍 Verifying $ID ..."
echo "  module: $module_file"
echo "  sva   : $sva_file"
echo "  tcl   : $JASPER_TCL"

# Run Jasper (single invocation per array task)
set +e
DESIGN_ID="$ID" \
JG_TOP="${JG_TOP:-}" \
JG_DESIGN="$module_file" \
JG_SVA="$sva_file" \
JG_STD="${JG_STD:-sv12}" \
JG_INCDIRS="${JG_INCDIRS:-}" \
JG_DEFINES="${JG_DEFINES:-}" \
JG_NO_CLOCK="${JG_NO_CLOCK:-1}" \
jaspergold -batch -allow_unsupported_OS \
  -proj "$proj_dir" \
  -tcl "$JASPER_TCL" \
  >"$run_log" 2>&1
rc=$?
set -e

# Append CSV headers if missing (safe if multiple tasks start at once)
mkdir -p "$ROOT/verification_results"
SUMMARY_CSV="$ROOT/verification_results/summary.csv"
VERIF_CSV="$ROOT/verification_results/verif_summary.csv"
[[ -f "$SUMMARY_CSV" ]] || echo "id,status" > "$SUMMARY_CSV"
[[ -f "$VERIF_CSV"   ]] || echo "id,status,reason" > "$VERIF_CSV"

# Minimal result parsing (reuse your earlier logic pattern)
if [[ $rc -eq 0 ]]; then
  echo "✅ $ID VERIF RUN OK"
  echo "$ID,ok" >> "$SUMMARY_CSV"

  if grep -q '\- cex' "$run_log" 2>/dev/null; then
    cex_count=$(grep -oP '(?<=- cex\s{1,20}: )\d+' "$run_log" 2>/dev/null || echo "0")
    if [[ "$cex_count" != "0" ]]; then
      echo "$ID,cex,proof completed with $cex_count counter-example(s)" >> "$VERIF_CSV"
    else
      echo "$ID,pass," >> "$VERIF_CSV"
    fi
  else
    echo "$ID,pass," >> "$VERIF_CSV"
  fi
else
  echo "❌ $ID VERIF RUN FAIL (rc=$rc)"
  echo "$ID,fail" >> "$SUMMARY_CSV"
  # lightweight reason
  if grep -q "FAILED: compile/elab errors" "$run_log" 2>/dev/null; then
    reason="compile/elab errors"
  elif grep -q "No properties found" "$run_log" 2>/dev/null; then
    reason="no properties found (bind/top)"
  elif grep -q "prove command failed" "$run_log" 2>/dev/null; then
    reason="prove command failed"
  else
    reason="unknown failure (check run.log)"
  fi
  # quote reason for CSV safety
  echo "$ID,fail,\"$reason\"" >> "$VERIF_CSV"
fi

touch "$done_marker"
exit $rc