#!/bin/bash
#SBATCH --job-name=jg_chunk
#SBATCH --output=slurm_logs/jg_chunk.%A_%a.out
#SBATCH --error=slurm_logs/jg_chunk.%A_%a.err
#SBATCH --partition=cpu
#SBATCH --qos=short
#SBATCH --time=02:00:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=16G
#SBATCH --array=1-88%25

set -euo pipefail

module purge
module load cadence/cadence_license

export JASPER_HOME=/usr/licensed/cadence-20210126/jasper_2021.03
export PATH="$PATH:$JASPER_HOME/bin"

cd "${SLURM_SUBMIT_DIR}"

ID_LIST="still_todo.txt"
CHUNK=50
START=$(( (SLURM_ARRAY_TASK_ID - 1) * CHUNK + 1 ))
END=$(( START + CHUNK - 1 ))

echo "Job ${SLURM_JOB_ID} Task ${SLURM_ARRAY_TASK_ID} -> IDs ${START}-${END}"

for i in $(seq "$START" "$END"); do
  ID="$(sed -n "${i}p" "$ID_LIST")"
  [[ -z "$ID" ]] && break

  # Skip if already done
  if [[ -f "verification_results/ids/${ID}/DONE" ]]; then
    echo "⏭️  Skipping $ID (already done)"
    continue
  fi

  echo "▶️  Processing $ID ..."
  ./run_one_id.sh "$ID" || true
done

echo "✅ Chunk ${SLURM_ARRAY_TASK_ID} finished"
