#!/usr/bin/env bash
set -euo pipefail

ROOT="${ROOT:-.}"

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

  module_file="$dir/module.v"
  sva_file="$dir/sva.sv"

  if [[ -f "$module_file" && -f "$sva_file" ]]; then
    echo "🔍 Verifying $id ..."
    out_dir="verification_results/$id"
    mkdir -p "$out_dir"
    proj_dir="$out_dir/jgproject"

    # (Optional) clean stale project dir to avoid lock issues
    rm -rf "$proj_dir"

    # Env → Tcl; unique project dir; log via shell redirection
    DESIGN_ID="$id" \
    JG_TOP="${JG_TOP:-binary_to_gray_converter}" \
    JG_DESIGN="$module_file" \
    JG_SVA="$sva_file" \
    JG_STD="${JG_STD:-sv12}" \
    JG_INCDIRS="${JG_INCDIRS:-}" \
    JG_DEFINES="${JG_DEFINES:-}" \
    JG_NO_CLOCK="${JG_NO_CLOCK:-1}" \
    jaspergold -batch -allow_unsupported_OS \
      -proj "$proj_dir" \
      -tcl "$JASPER_TCL" \
      >"$out_dir/run.log" 2>&1 && {
        echo "✅ $id VERIF RUN OK"
        echo "$id,ok" >> verification_results/summary.csv
      } || {
        echo "❌ $id VERIF RUN FAIL"
        echo "$id,fail" >> verification_results/summary.csv
      }
  else
    echo "⚠️  Skipping $id (missing module.v or sva.sv)"
  fi
done

echo "=============================="
echo "Summary written to verification_results/summary.csv"
cat verification_results/summary.csv
