#!/usr/bin/env bash
set -euo pipefail

# ============================================================
# Run Jasper helpmsg collection for VERI-* errors (no GUI)
# Uses same PATH assumptions as your syntax checker (jaspergold in PATH)
# ============================================================

TCL_SCRIPT="${TCL_SCRIPT:-collect_veri_helpmsg.tcl}"
CODES_FILE="${CODES_FILE:-syntax_results/veri_codes.txt}"
OUT_FILE="${OUT_FILE:-syntax_results/veri_helpmsg_dump.txt}"
RUN_LOG="${RUN_LOG:-syntax_results/helpmsg_run.log}"

[[ -f "$TCL_SCRIPT" ]] || { echo "❌ Missing $TCL_SCRIPT"; exit 1; }
[[ -f "$CODES_FILE" ]] || { echo "❌ Missing $CODES_FILE"; exit 1; }

mkdir -p syntax_results

# Use jaspergold to run the TCL script
if ! command -v jaspergold >/dev/null 2>&1; then
  echo "❌ jaspergold not found in PATH."
  echo "   Try: which jaspergold"
  exit 1
fi
ENGINE=(jaspergold -batch -allow_unsupported_OS -tcl "$TCL_SCRIPT" -codes_file "$CODES_FILE" -out_file "$OUT_FILE")

echo "============================================"
echo "Running Jasper helpmsg collection"
echo "TCL:    $TCL_SCRIPT"
echo "Codes:  $CODES_FILE"
echo "Output: $OUT_FILE"
echo "Log:    $RUN_LOG"
echo "Cmd:    ${ENGINE[*]}"
echo "============================================"

"${ENGINE[@]}" >"$RUN_LOG" 2>&1

echo "============================================"
echo "DONE"
echo "Raw help output: $OUT_FILE"
echo "Run log:         $RUN_LOG"
echo "============================================"
