#!/bin/bash
#SBATCH --job-name=jg_check
#SBATCH --output=jg_check.%j.out
#SBATCH --error=jg_check.%j.err
#SBATCH --time=12:00:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=64G

# ============================================================
# Generic SLURM wrapper for check_all.sh
#
# Usage:
#   sbatch scripts/run_check_all.sbatch <syntax|verif> <dataset_dir>
#
# Examples:
#   sbatch scripts/run_check_all.sbatch verif  metrex/dataset/version_1
#   sbatch scripts/run_check_all.sbatch syntax metrex/dataset/version_1
#   sbatch scripts/run_check_all.sbatch verif  veri_thoughts/dataset/version_1
# ============================================================

set -euo pipefail

# ── Validate arguments ───────────────────────────────────────
if [[ $# -lt 2 ]]; then
  echo "Usage: sbatch scripts/run_check_all.sbatch <syntax|verif> <dataset_dir>"
  echo ""
  echo "  syntax  Compile/syntax check only"
  echo "  verif   Full assertion verification"
  echo ""
  echo "Examples:"
  echo "  sbatch scripts/run_check_all.sbatch verif  metrex/dataset/version_1"
  echo "  sbatch scripts/run_check_all.sbatch verif  veri_thoughts/dataset/version_1"
  exit 1
fi

MODE="$1"
DATASET_DIR="$2"

# ── Info ─────────────────────────────────────────────────────
echo "Host: $(hostname)"
echo "Start: $(date)"
echo "PWD: $(pwd)"
echo "JobID: ${SLURM_JOB_ID:-unknown}"
echo "Mode: $MODE"
echo "Dataset: $DATASET_DIR"

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
stdbuf -oL -eL bash "$SCRIPT_DIR/check_all.sh" "$MODE" "$DATASET_DIR"

echo "End: $(date)"
