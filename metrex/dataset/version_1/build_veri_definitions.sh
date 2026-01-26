#!/usr/bin/env bash
set -euo pipefail

DUMP="${DUMP:-syntax_results/veri_helpmsg_dump.txt}"
CODES="${CODES:-syntax_results/veri_codes.txt}"

OUTCSV="${OUTCSV:-syntax_results/veri_definitions_present.csv}"
OUTTXT="${OUTTXT:-syntax_results/veri_definitions_present.txt}"

[[ -f "$DUMP" ]]  || { echo "❌ Missing $DUMP"; exit 1; }
[[ -f "$CODES" ]] || { echo "❌ Missing $CODES"; exit 1; }

tmp_blocks="$(mktemp)"
tmp_defs="$(mktemp)"
trap 'rm -f "$tmp_blocks" "$tmp_defs"' EXIT

# ------------------------------------------------------------
# Step A: Parse dump into (code, status, definition, detail)
# ------------------------------------------------------------
# We treat each section like:
#   ==== VERI-1137 =====
#   ... help output ...
# or failures like:
#   ERROR: helpmsg failed for VERI-1011
#   DETAIL: ...
#
# "definition" heuristic:
#   - first non-empty line that is NOT a banner/LOOKUP_OK/ERROR/DETAIL/TRIED
#   - trimmed and truncated for CSV friendliness
#
awk '
  function trim(s){ sub(/^[ \t\r\n]+/,"",s); sub(/[ \t\r\n]+$/,"",s); return s }
  function emit(){
    if(code=="") return
    # If no def extracted, fill from error/detail
    if(def=="") def = (detail!="" ? detail : "NO_DEFINITION_EXTRACTED")
    # sanitize quotes for csv
    gsub(/"/, "\"\"", def)
    gsub(/"/, "\"\"", detail)
    print code "," status ",\"" def "\",\"" detail "\""
  }

  BEGIN{
    code=""; status="UNKNOWN"; def=""; detail=""
    inblock=0
    print "veri_code,status,definition,detail"
  }

  # Start of a new block
  /^====[ \t]+VERI-[0-9]+/{
    emit()
    code=$2
    status="OK"
    def=""
    detail=""
    inblock=1
    next
  }

  # Failure line (outside or inside a block)
  /^ERROR: helpmsg failed for VERI-[0-9]+/{
    # if we were in a prior block, close it first
    if(inblock){ emit() }
    match($0, /(VERI-[0-9]+)/, m)
    code=m[1]
    status="NO_HELP"
    def=""
    detail=$0
    inblock=1
    next
  }

  /^DETAIL:/{
    if(detail=="") detail=$0
    else detail=detail " | " $0
    next
  }

  /^TRIED:/{
    if(detail=="") detail=$0
    else detail=detail " | " $0
    next
  }

  /^LOOKUP_OK:/{
    # ignore (we just need definition)
    next
  }

  # Extract the first “good” line as definition
  {
    if(!inblock) next
    line=trim($0)
    if(line=="") next
    if(line ~ /^====/) next
    if(line ~ /^Jasper helpmsg dump/) next
    if(line ~ /^Generated:/) next
    if(line ~ /^Codes file:/) next
    if(line ~ /^=+$/) next
    if(line ~ /^ERROR:/) next
    if(line ~ /^DETAIL:/) next
    if(line ~ /^TRIED:/) next
    if(line ~ /^INFO /) next

    # first usable line becomes definition
    if(def==""){
      def=line
      # keep definition short-ish for CSV; detail can hold more
      if(length(def)>220) def=substr(def,1,220) "..."
    }
  }

  END{ emit() }
' "$DUMP" > "$tmp_defs"

# ------------------------------------------------------------
# Step B: Filter to ONLY codes that exist in veri_codes.txt
#         (and preserve codes list order)
# ------------------------------------------------------------
# Build a quick lookup set from parsed defs
awk -F, 'NR>1{seen[$1]=1; line[$1]=$0} END{for(k in seen){} }' "$tmp_defs" >/dev/null

{
  echo "veri_code,status,definition,detail"
  while read -r code; do
    [[ -z "$code" ]] && continue
    # find exact row for this code (if missing, mark it)
    row="$(awk -F, -v c="$code" 'NR>1 && $1==c{print; found=1; exit} END{if(!found) exit 1}' "$tmp_defs" 2>/dev/null || true)"
    if [[ -n "$row" ]]; then
      echo "$row"
    else
      echo "$code,NOT_IN_DUMP,\"MISSING_FROM_HELPMSG_DUMP\",\"(No block found in dump)\""
    fi
  done < "$CODES"
} > "$OUTCSV"

# ------------------------------------------------------------
# Step C: Make a readable TXT summary
# ------------------------------------------------------------
{
  echo "VERI definitions present (from Jasper helpmsg dump)"
  echo "Dump:  $DUMP"
  echo "Codes: $CODES"
  echo "------------------------------------------------------------"
  awk -F, 'NR>1{
    code=$1; status=$2
    # strip surrounding quotes for display
    def=$3; gsub(/^"|"$/,"",def); gsub(/""/,"\"",def)
    print code " [" status "]: " def
  }' "$OUTCSV"
} > "$OUTTXT"

echo "✅ Wrote: $OUTCSV"
echo "✅ Wrote: $OUTTXT"
