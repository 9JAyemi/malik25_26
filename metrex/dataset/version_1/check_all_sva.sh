#!/usr/bin/env bash
set -euo pipefail

# ============================================================
# Batch JasperGold Syntax Checker for all dataset entries
# ============================================================

# Root where numbered subdirectories (00000, 00001, …) live
ROOT="."
# Path to jasper_syntax_check.tcl (same dir or one level up)
if [[ -f "./jasper_syntax_check.tcl" ]]; then
  JASPER_TCL="./jasper_syntax_check.tcl"
elif [[ -f "../jasper_syntax_check.tcl" ]]; then
  JASPER_TCL="../jasper_syntax_check.tcl"
else
  echo "❌ jasper_syntax_check.tcl not found!"
  exit 1
fi

mkdir -p syntax_results

echo "=============================="
echo "Running Jasper syntax checks..."
echo "=============================="

for dir in "$ROOT"/*/; do
  id=$(basename "$dir")
  module_file="$dir/module.v"
  sva_file="$dir/sva.sv"

  if [[ -f "$module_file" && -f "$sva_file" ]]; then
    echo "🔍 Checking $id ..."
    out_dir="syntax_results/$id"
    mkdir -p "$out_dir"

    # Run Jasper syntax check
    if jaspergold -batch -tcl "$JASPER_TCL" -- -dir "$dir" -std sv12 -halt_on_warn \
        >"$out_dir/log.txt" 2>&1; then
      echo "✅ $id PASSED"
      echo "$id,ok" >> syntax_results/summary.csv
    else
      echo "❌ $id FAILED"
      echo "$id,fail" >> syntax_results/summary.csv
    fi
  else
    echo "⚠️  Skipping $id (missing module.v or sva.sv)"
  fi
done

echo "=============================="
echo "Summary written to syntax_results/summary.csv"
cat syntax_results/summary.csv
