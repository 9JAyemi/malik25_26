#!/bin/bash
#SBATCH --job-name=jg_check
#SBATCH --output=jg_check.%j.out
#SBATCH --error=jg_check.%j.err
#SBATCH --time=12:00:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=64G

set -euo pipefail

echo "Host: $(hostname)"
echo "Start: $(date)"
echo "PWD: $(pwd)"
echo "JobID: ${SLURM_JOB_ID:-unknown}"

module purge
module load cadence/cadence_license

export JASPER_HOME=/usr/licensed/cadence-20210126/jasper_2021.03
export PATH="$PATH:$JASPER_HOME/bin"

# Sanity checks
command -v jaspergold || { echo "ERROR: jaspergold not found on PATH"; exit 1; }
jaspergold -version || true

# Periodic resource snapshot (every 5 min)
( while true; do
    echo "=== RESOURCE SNAPSHOT $(date) ==="
    free -h || true
    top -b -n 1 | head -n 15 || true
    sleep 300
  done
) &

chmod +x ./check_all_verif.sh
stdbuf -oL -eL ./check_all_verif.sh

echo "End: $(date)"