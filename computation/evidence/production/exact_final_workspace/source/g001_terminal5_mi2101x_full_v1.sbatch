#!/usr/bin/env bash
#SBATCH --job-name=g001-t5-full
#SBATCH --partition=mi2101x
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=16
#SBATCH --time=4-00:00:00
#SBATCH --array=0-191%24
#SBATCH --output=g001_terminal5_full_%A_%a.stdout.txt
#SBATCH --error=g001_terminal5_full_%A_%a.stderr.txt

set -euo pipefail
umask 077
export PYTHONDONTWRITEBYTECODE=1
: "${G001_TERMINAL5_PLAN_DIR:?required}"
: "${G001_TERMINAL5_WORKSPACE:?required}"
: "${G001_TERMINAL5_SOURCE_DIR:?required}"
: "${G001_TERMINAL5_RUN_ROOT:?required}"
: "${SLURM_ARRAY_TASK_ID:?required}"
[[ "${SLURM_CPUS_PER_TASK:-}" == "16" ]] || { echo "expected 16 CPUs" >&2; exit 64; }
python3 -B "${G001_TERMINAL5_SOURCE_DIR}/verify_g001_terminal5_plan_v1.py" \
  --plan-dir "${G001_TERMINAL5_PLAN_DIR}" \
  --workspace "${G001_TERMINAL5_WORKSPACE}" \
  --source-dir "${G001_TERMINAL5_SOURCE_DIR}"
set +e
python3 -B "${G001_TERMINAL5_SOURCE_DIR}/run_g001_terminal5_bundle_v1.py" \
  --plan-dir "${G001_TERMINAL5_PLAN_DIR}" \
  --workspace "${G001_TERMINAL5_WORKSPACE}" \
  --source-dir "${G001_TERMINAL5_SOURCE_DIR}" \
  --run-root "${G001_TERMINAL5_RUN_ROOT}" \
  --mode production --bundle-index "${SLURM_ARRAY_TASK_ID}" --workers 15
rc=$?
set -e
if [[ "${rc}" == "2" ]]; then
  echo "G001_TERMINAL5_FULL_VERIFIED_FOUND_IMMEDIATE bundle=${SLURM_ARRAY_TASK_ID} global_complete=0"
  exit 0
fi
[[ "${rc}" == "0" ]] || exit "${rc}"
echo "G001_TERMINAL5_FULL_BUNDLE_V1_OK bundle=${SLURM_ARRAY_TASK_ID} allocated_cpus=16 solver_workers=15"
