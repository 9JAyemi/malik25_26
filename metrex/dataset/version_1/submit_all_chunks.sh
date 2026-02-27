#!/bin/bash
# Auto-chained submission of all remaining tasks (136-4808)
# Uses malik partition (3 idle dedicated nodes) and BASE_ID offset
# QoS limit: 1 job at a time; MaxArraySize: 2500
set -euo pipefail
cd "$(dirname "$0")"

PARTITION="malik"
THROTTLE=25

echo "=== Chunk 1: lines 136-2200 (array 136-2200) ==="
JID1=$(sbatch --partition=$PARTITION --qos=short --array=136-2200%${THROTTLE} run_jasper_array.sbatch | awk '{print $4}')
echo "Submitted job $JID1"

echo "Waiting for chunk 1 ($JID1) to clear..."
while squeue -j "$JID1" -h 2>/dev/null | grep -q .; do sleep 60; done
echo "Chunk 1 done."

echo "=== Chunk 2: lines 2201-4700 (BASE_ID=2200, array 1-2500) ==="
JID2=$(BASE_ID=2200 sbatch --partition=$PARTITION --qos=short --array=1-2500%${THROTTLE} run_jasper_array.sbatch | awk '{print $4}')
echo "Submitted job $JID2"

echo "Waiting for chunk 2 ($JID2) to clear..."
while squeue -j "$JID2" -h 2>/dev/null | grep -q .; do sleep 60; done
echo "Chunk 2 done."

echo "=== Chunk 3: lines 4701-4808 (BASE_ID=4700, array 1-108) ==="
JID3=$(BASE_ID=4700 sbatch --partition=$PARTITION --qos=short --array=1-108%${THROTTLE} run_jasper_array.sbatch | awk '{print $4}')
echo "Submitted job $JID3"

echo "Waiting for chunk 3 ($JID3) to clear..."
while squeue -j "$JID3" -h 2>/dev/null | grep -q .; do sleep 60; done
echo "Chunk 3 done."

echo "=== All 4808 tasks submitted and completed ==="
