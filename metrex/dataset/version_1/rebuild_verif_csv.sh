#!/bin/bash
# Rebuild verif_summary.csv from existing run.logs using improved error extraction.
# Backs up old CSV first, then re-parses every verification_results/<ID>/run.log.
set -euo pipefail
cd "$(dirname "$0")"

VERIF_CSV="verification_results/verif_summary.csv"
BACKUP="${VERIF_CSV}.bak.$(date +%Y%m%d_%H%M%S)"

if [[ -f "$VERIF_CSV" ]]; then
  cp "$VERIF_CSV" "$BACKUP"
  echo "Backed up old CSV to $BACKUP"
fi

echo "id,status,reason" > "$VERIF_CSV"

count=0
for done_marker in verification_results/*/DONE; do
  dir="$(dirname "$done_marker")"
  ID="$(basename "$dir")"
  run_log="$dir/run.log"

  if [[ ! -f "$run_log" ]]; then
    # No run.log but DONE marker exists — was a skip (missing files)
    echo "$ID,pass,already completed (no run.log)" >> "$VERIF_CSV"
    ((count++)) || true
    continue
  fi

  # Check exit status from the log
  exit_status=$(grep -oP 'Tcl-thread exited with status \K\d+' "$run_log" 2>/dev/null | tail -1 || echo "")

  if [[ "$exit_status" == "0" ]]; then
    # Success path — check for counterexamples
    if grep -q '\- cex' "$run_log" 2>/dev/null; then
      cex_count=$(grep -oP '(?<=- cex\s{1,20}: )\d+' "$run_log" 2>/dev/null || echo "0")
      if [[ "$cex_count" != "0" ]]; then
        echo "$ID,cex,\"proof completed with $cex_count counter-example(s)\"" >> "$VERIF_CSV"
      else
        echo "$ID,pass," >> "$VERIF_CSV"
      fi
    else
      echo "$ID,pass," >> "$VERIF_CSV"
    fi
  else
    # Failure path — extract the exact ❌ FAILED line + any [ERROR] detail
    fail_line=$(grep '❌ FAILED:' "$run_log" 2>/dev/null | grep -v 'puts' | tail -1 || true)
    first_error=$(grep -oP '\[ERROR \([A-Z]+-\d+\)\].*' "$run_log" 2>/dev/null | head -1 || true)

    if [[ -n "$fail_line" && -n "$first_error" ]]; then
      reason="${fail_line} | ${first_error}"
    elif [[ -n "$fail_line" ]]; then
      reason="$fail_line"
    elif [[ -n "$first_error" ]]; then
      reason="$first_error"
    else
      reason="unknown failure (check run.log)"
    fi

    # Sanitise for CSV
    reason="${reason//\"/\'}"
    reason="${reason//,/;}"
    echo "$ID,fail,\"$reason\"" >> "$VERIF_CSV"
  fi

  ((count++)) || true
done

echo "Rebuilt $VERIF_CSV with $count entries."
echo "Status distribution:"
awk -F, '{print $2}' "$VERIF_CSV" | sort | uniq -c | sort -rn
