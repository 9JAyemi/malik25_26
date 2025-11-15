#!/usr/bin/env bash
set -euo pipefail

# ============================================================
# Batch JasperGold Syntax Checker for all dataset subdirs
# Relies on jaspergold being in PATH via your ~/.bashrc
# ============================================================

ROOT="${ROOT:-.}"

if [[ -f "./jasper_syntax_check.tcl" ]]; then
  JASPER_TCL="./jasper_syntax_check.tcl"
elif [[ -f "../jasper_syntax_check.tcl" ]]; then
  JASPER_TCL="../jasper_syntax_check.tcl"
else
  echo "❌ jasper_syntax_check.tcl not found!"
  exit 1
fi

mkdir -p syntax_results
: > syntax_results/summary.csv
echo "id,status" >> syntax_results/summary.csv

echo "=============================="
echo "Running Jasper syntax checks..."
echo "TCL : $JASPER_TCL"
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

    # Env → Tcl; log via shell redirection
    JG_DIR="$dir" \
    JG_STD="${JG_STD:-sv12}" \
    JG_HALT_ON_WARN="${JG_HALT_ON_WARN:-1}" \
    JG_INCDIRS="${JG_INCDIRS:-}" \
    JG_DEFINES="${JG_DEFINES:-}" \
    JG_TOP="${JG_TOP:-}" \
    jaspergold -batch -allow_unsupported_OS -tcl "$JASPER_TCL" \
      >"$out_dir/log.txt" 2>&1 && {
        echo "✅ $id PASSED"
        echo "$id,ok" >> syntax_results/summary.csv
      } || {
        echo "❌ $id FAILED"
        echo "$id,fail" >> syntax_results/summary.csv
      }
  else
    echo "⚠️  Skipping $id (missing module.v or sva.sv)"
  fi
done

echo "=============================="
echo "Summary written to syntax_results/summary.csv"
cat syntax_results/summary.csv
