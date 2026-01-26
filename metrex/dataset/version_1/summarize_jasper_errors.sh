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

VERI_TOTAL="$OUTDIR/veri_counts_total.txt"
VERI_BY_ID_LONG="$OUTDIR/veri_counts_by_id_long.csv"
VERI_BY_ID_SUMMARY="$OUTDIR/veri_counts_by_id_summary.csv"
VERI_IDS_DIR="$OUTDIR/veri_ids_by_code"

echo "==> Collecting failing IDs..."
awk -F, 'NR>1 && $2=="fail"{print $1}' "$SUMMARY" | sort > "$FAILS"
echo "Wrote: $FAILS  (count: $(wc -l < "$FAILS"))"

echo "==> Building per-ID error catalog CSV (multiline error_block)..."
echo "id,error_codes,primary_code,secondary_code,tertiary_code,error_count,error_block" > "$CATALOG"

csv_escape_multiline() { sed 's/"/""/g'; }

while read -r id; do
  log="$OUTDIR/$id/log.txt"
  if [[ ! -f "$log" ]]; then
    printf '%s,%s,%s,%s,%s,%s,"%s"\n' "$id" "" "" "" "" "0" "MISSING_LOG_FILE" >> "$CATALOG"
    continue
  fi

  block="$(
    awk '
      /^Summary of errors detected:/ {print; grab=1; next}
      grab {
        if ($0 ~ /^[[:space:]]*\[ERROR \(/) {print; next}
        if ($0 ~ /^ERROR: analyze failed:/) {print; next}
        if ($0 ~ /^ERROR \(ENL[0-9]+\):/) {print; exit}
        if ($0 !~ /^[[:space:]]*$/) exit
      }
    ' "$log"
  )"
  if [[ -z "$block" ]]; then
    block="$(grep -m1 -E '^\[ERROR \([A-Z]+-[0-9]+\)\]' "$log" || true)"
  fi
  [[ -z "$block" ]] && block="NO_ERROR_BLOCK_FOUND"

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

  errcount="$(
    printf '%s\n' "$block" |
      grep -oE 'ERROR \(ENL[0-9]+\): [0-9]+ errors detected' |
      head -n1 | grep -oE '[0-9]+' | tail -n1 || true
  )"
  if [[ -z "$errcount" ]]; then
    errcount="$(printf '%s\n' "$block" | grep -cE '^[[:space:]]*\[ERROR \(' || true)"
  fi
  [[ -z "$errcount" ]] && errcount="0"

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

# ============================================================
# ALL VERI CODES PER ID (LONG FORMAT) + TOTALS + IDS PER CODE
# ============================================================

echo "==> Computing total VERI-* histogram across failing IDs..."
awk -F, 'NR>1 && $2=="fail"{print $1}' "$SUMMARY" |
while read -r id; do
  log="$OUTDIR/$id/log.txt"
  [[ -f "$log" ]] || continue
  awk '
    /^Summary of errors detected:/ {grab=1; next}
    grab && /^[[:space:]]*\[ERROR \(/ {
      if (match($0, /\[ERROR \((VERI-[0-9]+)\)\]/, m)) print m[1]
      next
    }
    grab && /^ERROR: analyze failed:/ {exit}
  ' "$log"
done | sort | uniq -c | sort -nr > "$VERI_TOTAL"
echo "Wrote: $VERI_TOTAL"

echo "==> Computing ALL VERI-* counts per ID (long format)..."
echo "id,veri_code,count" > "$VERI_BY_ID_LONG"

echo "==> Computing per-ID VERI summary..."
echo "id,total_veri_errors,distinct_veri_codes" > "$VERI_BY_ID_SUMMARY"

while read -r id; do
  log="$OUTDIR/$id/log.txt"
  if [[ ! -f "$log" ]]; then
    echo "$id,0,0" >> "$VERI_BY_ID_SUMMARY"
    continue
  fi

  codes_list="$(
    awk '
      /^Summary of errors detected:/ {grab=1; next}
      grab && /^[[:space:]]*\[ERROR \(/ {
        if (match($0, /\[ERROR \((VERI-[0-9]+)\)\]/, m)) print m[1]
        next
      }
      grab && /^ERROR: analyze failed:/ {exit}
    ' "$log"
  )"

  if [[ -z "$codes_list" ]]; then
    echo "$id,0,0" >> "$VERI_BY_ID_SUMMARY"
    continue
  fi

  total_veri="$(printf '%s\n' "$codes_list" | wc -l | tr -d ' ')"
  distinct_veri="$(printf '%s\n' "$codes_list" | sort -u | wc -l | tr -d ' ')"
  echo "$id,$total_veri,$distinct_veri" >> "$VERI_BY_ID_SUMMARY"

  printf '%s\n' "$codes_list" | sort | uniq -c | while read -r cnt code; do
    echo "$id,$code,$cnt" >> "$VERI_BY_ID_LONG"
  done

done < "$FAILS"

echo "Wrote: $VERI_BY_ID_LONG"
echo "Wrote: $VERI_BY_ID_SUMMARY"

echo "==> Creating per-VERI-code ID lists..."
rm -rf "$VERI_IDS_DIR"
mkdir -p "$VERI_IDS_DIR"

# Each file contains: id,count  (only for ids that hit that VERI code)
# This will create files like syntax_results/veri_ids_by_code/VERI-1137.txt
tail -n +2 "$VERI_BY_ID_LONG" | awk -F, '
  { print $1","$3 >> (dir "/" $2 ".csv") }
' dir="$VERI_IDS_DIR"

# Optional: also create .txt versions (space-separated) for quick grepping
for f in "$VERI_IDS_DIR"/*.csv; do
  base="$(basename "$f" .csv)"
  {
    echo "id,count"
    cat "$f" | sort -t, -k2,2nr
  } > "$VERI_IDS_DIR/$base.csv.tmp"
  mv "$VERI_IDS_DIR/$base.csv.tmp" "$VERI_IDS_DIR/$base.csv"

  # .txt (just ids, sorted by count desc)
  tail -n +2 "$VERI_IDS_DIR/$base.csv" | sort -t, -k2,2nr | awk -F, '{print $1" "$2}' > "$VERI_IDS_DIR/$base.txt"
done

echo "Wrote: $VERI_IDS_DIR/VERI-*.csv and .txt"

echo
echo "================ DONE ================"
echo "Top files to open:"
echo "  - $CATALOG"
echo "  - $VERI_TOTAL"
echo "  - $VERI_BY_ID_SUMMARY"
echo "  - $VERI_BY_ID_LONG"
echo "  - $VERI_IDS_DIR/VERI-*.txt"
echo "  - $ROOTCAUSE"
echo "======================================"
