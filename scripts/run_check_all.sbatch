#!/bin/bash
#SBATCH --job-name=jg_check
#SBATCH --output=jg_check.%j.out
#SBATCH --error=jg_check.%j.err
#SBATCH --time=24:00:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=64G

# ============================================================
# Generic SLURM wrapper for check_all.sh
#
# Usage:
#   sbatch scripts/run_check_all.sbatch [--force] <syntax|verif> <parent_dir>
#
# Iterates over every subdirectory in <parent_dir> and runs
# check_all.sh on each one as a separate dataset.
#
# Examples:
#   sbatch scripts/run_check_all.sbatch verif  inference_outputs
#   sbatch scripts/run_check_all.sbatch syntax inference_outputs
#   sbatch scripts/run_check_all.sbatch --force verif inference_outputs
# ============================================================

set -euo pipefail

# ── Validate arguments ───────────────────────────────────────
FORCE_FLAG=""
if [[ "${1:-}" == "--force" ]]; then
  FORCE_FLAG="--force"
  shift
fi

if [[ $# -lt 2 ]]; then
  echo "Usage: sbatch scripts/run_check_all.sbatch [--force] <syntax|verif> <parent_dir>"
  echo ""
  echo "  --force      Re-run all IDs even if DONE marker exists"
  echo "  syntax       Compile/syntax check only"
  echo "  verif        Full assertion verification"
  echo "  parent_dir   Directory containing dataset subdirectories"
  echo ""
  echo "Examples:"
  echo "  sbatch scripts/run_check_all.sbatch verif  inference_outputs"
  echo "  sbatch scripts/run_check_all.sbatch syntax inference_outputs"
  exit 1
fi

MODE="$1"
PARENT_DIR="$2"

# ── Info ─────────────────────────────────────────────────────
echo "Host: $(hostname)"
echo "Start: $(date)"
echo "PWD: $(pwd)"
echo "JobID: ${SLURM_JOB_ID:-unknown}"
echo "Mode: $MODE"
echo "Force: ${FORCE_FLAG:-off}"
echo "Parent dir: $PARENT_DIR"

# ── Environment setup ────────────────────────────────────────
module purge
module load cadence/cadence_license

export JASPER_HOME=/usr/licensed/cadence-20210126/jasper_2021.03
export PATH="$PATH:$JASPER_HOME/bin"

# Sanity checks
command -v jaspergold || { echo "ERROR: jaspergold not found on PATH"; exit 1; }
jaspergold -version || true

# ── Periodic resource snapshot (every 5 min) ─────────────────
( while true; do
    echo "=== RESOURCE SNAPSHOT $(date) ==="
    free -h || true
    top -b -n 1 | head -n 15 || true
    sleep 300
  done
) &

# ── Run ──────────────────────────────────────────────────────
# SLURM copies the batch script to a spool dir, so BASH_SOURCE
# won't point back to scripts/.  Use SLURM_SUBMIT_DIR instead.
SCRIPT_DIR="${SLURM_SUBMIT_DIR:-$(pwd)}/scripts"

PARENT_ABS="$(cd "$PARENT_DIR" && pwd)"
echo "Resolved parent dir: $PARENT_ABS"

FAIL_COUNT=0
TOTAL_COUNT=0

for DATASET_DIR in "$PARENT_ABS"/*/; do
  [[ -d "$DATASET_DIR" ]] || continue
  SUBDIR_NAME="$(basename "$DATASET_DIR")"

  # Skip result directories that may have been created by previous runs
  [[ "$SUBDIR_NAME" == "syntax_results" || "$SUBDIR_NAME" == "verification_results" ]] && continue

  TOTAL_COUNT=$((TOTAL_COUNT + 1))
  echo ""
  echo "=========================================="
  echo "  Processing: $SUBDIR_NAME"
  echo "=========================================="

  stdbuf -oL -eL bash "$SCRIPT_DIR/check_all.sh" $FORCE_FLAG "$MODE" "$DATASET_DIR" || {
    echo "⚠️  check_all.sh returned non-zero for $SUBDIR_NAME"
    FAIL_COUNT=$((FAIL_COUNT + 1))
  }
done

echo ""
echo "=========================================="
echo "All subdirectories processed: $TOTAL_COUNT total, $FAIL_COUNT had errors"
echo "End: $(date)"
