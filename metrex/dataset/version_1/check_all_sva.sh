#!/usr/bin/env bash
set -euo pipefail

# ============================================================
# Batch JasperGold Syntax Checker for all dataset subdirs
# - Runs from INSIDE each subdir to avoid jgproject collisions
# - Cleans stale jgproject/work/transcript per run
# - Writes per-case logs and a summary CSV
# - Relies on 'jaspergold' in PATH (sourced via ~/.bashrc)
#
# Env overrides (optional):
#   ROOT=path/to/dataset/root
#   JG_STD=sv12|sv11|sv09      (default sv12)
#   JG_HALT_ON_WARN=0|1        (default 1)
#   JG_INCDIRS="inc:third/inc" (optional)
#   JG_DEFINES="SIM=1 DEBUG"   (optional)
#   JG_TOP=top_module          (optional elaboration)
# ============================================================

ROOT="${ROOT:-.}"

# Locate TCL script
if [[ -f "./jasper_syntax_check.tcl" ]]; then
  JASPER_TCL="./jasper_syntax_check.tcl"
elif [[ -f "../jasper_syntax_check.tcl" ]]; then
  JASPER_TCL="../jasper_syntax_check.tcl"
else
  echo "❌ jasper_syntax_check.tcl not found!"
  exit 1
fi

# Absolute path to the TCL (so it works after pushd)
JASPER_TCL_ABS="$(cd "$(dirname "$JASPER_TCL")" && pwd)/$(basename "$JASPER_TCL")"

mkdir -p syntax_results
: > syntax_results/summary.csv
echo "id,status" >> syntax_results/summary.csv

echo "=============================="
echo "Running Jasper syntax checks..."
echo "TCL : $JASPER_TCL_ABS"
echo "Root: $ROOT"
echo "=============================="

shopt -s nullglob
for dir in "$ROOT"/*/; do
  id="$(basename "$dir")"
  [[ "$id" == "syntax_results" ]] && continue

  module_file="$dir/module.v"
  sva_file="$dir/sva.sv"

  if [[ -f "$module_file" && -f "$sva_file" ]]; then
    echo "🔍 Checking $id ..."
    out_dir="syntax_results/$id"
    mkdir -p "$out_dir"

    # Run inside the dataset folder to isolate jgproject/work
    pushd "$dir" >/dev/null

    # Clean stale project dirs (safe between runs)
    rm -rf jgproject work transcript

    # Export env → Tcl; log to parent results dir
    JG_DIR="." \
    JG_STD="${JG_STD:-sv12}" \
    JG_HALT_ON_WARN="${JG_HALT_ON_WARN:-1}" \
    JG_INCDIRS="${JG_INCDIRS:-}" \
    JG_DEFINES="${JG_DEFINES:-}" \
    JG_TOP="${JG_TOP:-}" \
    jaspergold -batch -allow_unsupported_OS -tcl "$JASPER_TCL_ABS" \
      >"../$out_dir/log.txt" 2>&1
    rc=$?

    popd >/dev/null

    if [[ $rc -eq 0 ]]; then
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
