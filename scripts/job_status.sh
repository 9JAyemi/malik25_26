#!/usr/bin/env bash
# Quick job status viewer
# Usage: ./scripts/job_status.sh <job_id>

set -euo pipefail

if [[ $# -lt 1 ]]; then
  echo "Usage: $0 <job_id>"
  exit 1
fi

JOB_ID="$1"

echo "=============================="
echo "Job $JOB_ID"
echo "=============================="

# Check if still running
echo ""
echo "── Queue Status ──"
squeue -j "$JOB_ID" 2>/dev/null || echo "(not in queue — likely completed or failed)"

# Accounting info
echo ""
echo "── Accounting ──"
sacct -j "$JOB_ID" --format=JobID,JobName,State,ExitCode,Elapsed,MaxRSS,Start,End 2>/dev/null || true

# Show logs if they exist
STDOUT="jg_check.${JOB_ID}.out"
STDERR="jg_check.${JOB_ID}.err"

if [[ -f "$STDOUT" ]]; then
  echo ""
  echo "── stdout (last 40 lines): $STDOUT ──"
  tail -n 40 "$STDOUT"
else
  echo ""
  echo "(no stdout log found: $STDOUT)"
fi

if [[ -f "$STDERR" ]]; then
  ERRSIZE=$(wc -c < "$STDERR")
  if [[ "$ERRSIZE" -gt 0 ]]; then
    echo ""
    echo "── stderr (last 20 lines): $STDERR ──"
    tail -n 20 "$STDERR"
  fi
fi
