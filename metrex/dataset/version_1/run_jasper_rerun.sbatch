#!/bin/bash
#SBATCH --job-name=jg_rerun
#SBATCH --output=slurm_logs/jg_rerun.%A_%a.out
#SBATCH --error=slurm_logs/jg_rerun.%A_%a.err
#SBATCH --partition=cpu
#SBATCH --qos=short
#SBATCH --time=02:00:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=16G
#SBATCH --array=1-2200%25

set -euo pipefail

module purge
module load cadence/cadence_license

export JASPER_HOME=/usr/licensed/cadence-20210126/jasper_2021.03
export PATH="$PATH:$JASPER_HOME/bin"

cd "${SLURM_SUBMIT_DIR}"

# Read from rerun list instead of id_list.txt
ID="$(sed -n "${SLURM_ARRAY_TASK_ID}p" rerun_id_list.txt)"

if [[ -z "${ID}" ]]; then
  echo "No ID found for task ${SLURM_ARRAY_TASK_ID}"
  exit 0
fi

echo "Job ${SLURM_JOB_ID} Task ${SLURM_ARRAY_TASK_ID} -> ID=${ID}"
./run_one_id.sh "${ID}"
