#!/bin/bash
#SBATCH --job-name=jg_array
#SBATCH --output=slurm_logs/jg_array.%A_%a.out
#SBATCH --error=slurm_logs/jg_array.%A_%a.err
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

# Workdir should be version_1 (where id_list.txt lives)
cd "${SLURM_SUBMIT_DIR}"

# Grab ID for this array index (1-based)
ID="$(sed -n "${SLURM_ARRAY_TASK_ID}p" id_list.txt)"

if [[ -z "${ID}" ]]; then
  echo "No ID found for task ${SLURM_ARRAY_TASK_ID}"
  exit 0
fi

echo "Job ${SLURM_JOB_ID} Task ${SLURM_ARRAY_TASK_ID} -> ID=${ID}"
./run_one_id.sh "${ID}"