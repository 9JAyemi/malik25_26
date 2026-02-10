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
VERI_COUNTS_TOTAL_CSV="$OUTDIR/veri_error_counts_total.csv"

# NEW: definitions file (copy the one I generated into this location)
VERI_DEFS="${VERI_DEFS:-$OUTDIR/veri_error_definitions_present.csv}"
DEF_MAP_TSV="$OUTDIR/.veri_def_map.tsv"   # internal

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

# ============================================================
# NEW: Load VERI definitions (CSV) into a simple TSV map
# ============================================================

if [[ -f "$VERI_DEFS" ]]; then
  echo "==> Loading VERI definitions from: $VERI_DEFS"
  # expects columns including: error_code,definition  (like the file I generated)
  # build TSV: VERI-xxxx<TAB>definition
  awk -F, '
    NR==1 { for(i=1;i<=NF;i++){h[$i]=i} }
    NR>1  {
      code=$(h["error_code"])
      def=$(h["definition"])
      if(code=="") next
      # strip surrounding quotes if any (basic)
      gsub(/^"/,"",def); gsub(/"$/,"",def); gsub(/""/,"\"",def)
      print code "\t" def
    }
  ' "$VERI_DEFS" > "$DEF_MAP_TSV"
else
  echo "⚠️  VERI definitions file not found: $VERI_DEFS"
  echo "    Per-code CSVs will include definition=UNKNOWN."
  : > "$DEF_MAP_TSV"
fi

get_def() {
  local code="$1"
  local def
  def="$(awk -F'\t' -v c="$code" '$1==c{print $2; exit}' "$DEF_MAP_TSV" 2>/dev/null || true)"
  if [[ -z "${def:-}" ]]; then
    echo "UNKNOWN"
  else
    echo "$def"
  fi
}

# ============================================================
# Create per-VERI-code CSVs with definitions embedded
# ============================================================

echo "==> Creating per-VERI-code ID lists (with definitions)..."
rm -rf "$VERI_IDS_DIR"
mkdir -p "$VERI_IDS_DIR"

# Build raw per-code CSVs from the long format (id,count)
tail -n +2 "$VERI_BY_ID_LONG" | awk -F, '{ print $1","$3 >> (dir "/" $2 ".raw.csv") }' dir="$VERI_IDS_DIR"

# Convert each *.raw.csv → final *.csv and *.txt, adding definitions
shopt -s nullglob
for raw in "$VERI_IDS_DIR"/*.raw.csv; do
  code="$(basename "$raw" .raw.csv)"      # e.g., VERI-1137
  def="$(get_def "$code")"

  final_csv="$VERI_IDS_DIR/$code.csv"
  final_txt="$VERI_IDS_DIR/$code.txt"

  # CSV-escape definition once
  esc_def="$(printf '%s' "$def" | sed 's/"/""/g')"

  # ✅ SINGLE TABLE CSV (Excel-friendly)
  {
    echo "id,count,veri_code,definition"
    sort -t, -k2,2nr "$raw" \
      | awk -F, -v c="$code" -v d="$esc_def" \
          '{print $1","$2","c",\""d"\""}'
  } > "$final_csv"

  # Keep txt for quick grepping
  {
    echo "$code"
    echo "$def"
    echo "----------------"
    sort -t, -k2,2nr "$raw" | awk -F, '{print $1" "$2}'
  } > "$final_txt"

  rm -f "$raw"
done
# ============================================================
# NEW: Simple total count per VERI code (CSV for plotting)
# ============================================================

echo "==> Writing total VERI error counts CSV for plotting..."
echo "veri_code,total_count,definition" > "$VERI_COUNTS_TOTAL_CSV"

# VERI_TOTAL format: "<count> <VERI-####>"
# Example line: "18234 VERI-1137"
while read -r cnt code; do
  [[ -z "${code:-}" ]] && continue
  def="$(get_def "$code")"
  esc_def="$(printf '%s' "$def" | sed 's/"/""/g')"
  echo "$code,$cnt,\"$esc_def\"" >> "$VERI_COUNTS_TOTAL_CSV"
done < "$VERI_TOTAL"

echo "Wrote: $VERI_COUNTS_TOTAL_CSV"


echo "Wrote: $VERI_IDS_DIR/VERI-*.csv and .txt"

echo
echo "================ DONE ================"
echo "Top files to open:"
echo "  - $CATALOG"
echo "  - $VERI_TOTAL"
echo "  - $VERI_BY_ID_SUMMARY"
echo "  - $VERI_BY_ID_LONG"
echo "  - $VERI_IDS_DIR/VERI-*.csv"
echo "  - $ROOTCAUSE"
echo "======================================"
