#!/usr/bin/env bash
set -euo pipefail

SUMMARY="syntax_results/summary.csv"
OUTDIR="syntax_results"

if [[ ! -f "$SUMMARY" ]]; then
  echo "❌ Missing $SUMMARY"
  exit 1
fi

mkdir -p "$OUTDIR"

FAILS="$OUTDIR/fails.txt"
CATALOG="$OUTDIR/error_catalog.csv"
CODE_HIST="$OUTDIR/error_code_hist.txt"
ROOTCAUSE="$OUTDIR/error_rootcause_counts.txt"

echo "==> Collecting failing IDs..."
awk -F, 'NR>1 && $2=="fail"{print $1}' "$SUMMARY" | sort > "$FAILS"
echo "Wrote: $FAILS  (count: $(wc -l < "$FAILS"))"

echo "==> Building per-ID error catalog CSV (multiline error_block)..."
echo "id,error_codes,primary_code,secondary_code,tertiary_code,error_count,error_block" > "$CATALOG"

# CSV-escape a multiline string (keep newlines; double quotes inside)
csv_escape_multiline() { sed 's/"/""/g'; }

while read -r id; do
  log="$OUTDIR/$id/log.txt"
  if [[ ! -f "$log" ]]; then
    printf '%s,%s,%s,%s,%s,%s,"%s"\n' "$id" "" "" "" "" "0" "MISSING_LOG_FILE" >> "$CATALOG"
    continue
  fi

  # ------------------------------------------------------------
  # Extract summary block as MULTI-LINE (no flattening)
  # ------------------------------------------------------------
  block="$(
    awk '
      /^Summary of errors detected:/ {print; grab=1; next}
      grab {
        if ($0 ~ /^[[:space:]]*\[ERROR \(/) {print; next}
        if ($0 ~ /^ERROR: analyze failed:/) {print; next}
        if ($0 ~ /^ERROR \(ENL[0-9]+\):/) {print; exit}
        # stop once we hit a non-empty line not part of this block
        if ($0 !~ /^[[:space:]]*$/) exit
      }
    ' "$log"
  )"

  # Fallback: if no summary block, grab first bracket error line
  if [[ -z "$block" ]]; then
    block="$(grep -m1 -E '^\[ERROR \([A-Z]+-[0-9]+\)\]' "$log" || true)"
  fi
  [[ -z "$block" ]] && block="NO_ERROR_BLOCK_FOUND"

  # ------------------------------------------------------------
  # Extract codes in order of appearance (unique, ordered)
  # ------------------------------------------------------------
  codes_ordered="$(
    printf '%s\n' "$block" |
      grep -oE '\[ERROR \([A-Z]+-[0-9]+\)\]' |
      sed -E 's/\[ERROR \(|\)\]//g' |
      awk '!seen[$0]++' || true
  )"

  codes="$(printf '%s\n' "$codes_ordered" | paste -sd ';' - 2>/dev/null || true)"
  primary_code="$(printf '%s\n' "$codes_ordered" | sed -n '1p' || true)"
  secondary_code="$(printf '%s\n' "$codes_ordered" | sed -n '2p' || true)"
  tertiary_code="$(printf '%s\n' "$codes_ordered" | sed -n '3p' || true)"

  # ------------------------------------------------------------
  # Error count: prefer ENLxxx "N errors detected", else count [ERROR(...)] lines
  # ------------------------------------------------------------
  errcount="$(
    printf '%s\n' "$block" |
      grep -oE 'ERROR \(ENL[0-9]+\): [0-9]+ errors detected' |
      head -n1 | grep -oE '[0-9]+' | tail -n1 || true
  )"
  if [[ -z "$errcount" ]]; then
    errcount="$(printf '%s\n' "$block" | grep -cE '^[[:space:]]*\[ERROR \(' || true)"
  fi
  [[ -z "$errcount" ]] && errcount="0"

  # ------------------------------------------------------------
  # Write CSV row with multiline quoted block
  # ------------------------------------------------------------
  esc_block="$(printf '%s\n' "$block" | csv_escape_multiline)"

  printf '%s,%s,%s,%s,%s,%s,"%s"\n' \
    "$id" \
    "${codes:-}" \
    "${primary_code:-}" \
    "${secondary_code:-}" \
    "${tertiary_code:-}" \
    "$errcount" \
    "$esc_block" >> "$CATALOG"

done < "$FAILS"

echo "Wrote: $CATALOG"

echo "==> Building histogram of error code sets..."
cut -d, -f2 "$CATALOG" | tail -n +2 | sort | uniq -c | sort -nr > "$CODE_HIST"
echo "Wrote: $CODE_HIST"

echo "==> Root-cause bucketing..."
{
  echo "count,category"
  awk -F, 'NR>1 && $2=="fail"{print $1}' "$SUMMARY" |
  while read -r id; do
    log="$OUTDIR/$id/log.txt"
    if [[ ! -f "$log" ]]; then
      echo "MISSING_LOG"
      continue
    fi
    if grep -qiE 'cannot open include|include file.*not found' "$log"; then
      echo "MISSING_INCLUDE"
    elif grep -qiE 'undefined macro|is not defined' "$log"; then
      echo "UNDEFINED_MACRO"
    elif grep -qiE 'Cannot obtain ownership of project directory|\.nfs' "$log"; then
      echo "PROJECT_LOCK"
    elif grep -qiE 'FLEX|license|Checkout' "$log"; then
      echo "LICENSE"
    elif grep -qiE '^ERROR: elaborate failed:|elaborate|ELAB' "$log"; then
      echo "ELAB_FAILURE"
    elif grep -qiE 'syntax error|SystemVerilog keyword|parse|PARSE' "$log"; then
      echo "PARSE_FAILURE"
    elif grep -qiE 'Summary of errors detected:' "$log"; then
      echo "ANALYZE_FAILURE"
    else
      echo "OTHER"
    fi
  done | sort | uniq -c | sort -nr | awk '{print $1","$2}'
} > "$ROOTCAUSE"
echo "Wrote: $ROOTCAUSE"

echo
echo "================ DONE ================"
echo "Top files to open:"
echo "  - $CATALOG"
echo "  - $CODE_HIST"
echo "  - $ROOTCAUSE"
echo "======================================"
