#!/usr/bin/env bash
# Recompute all 39,030 Terminal5 records for Configurations 1, 4, 5, 6, and 7.
set -euo pipefail
umask 077
export PYTHONDONTWRITEBYTECODE=1

usage() {
  cat <<'EOF'
Usage: recompute_terminal5_full.sh --run-root NEW_EMPTY_DIRECTORY [--cxx CXX] [--python PYTHON]

The complete evidence archive must first be installed with
scripts/install_evidence_archive.py. The run root must not already exist.
This POSIX/Linux driver runs 30 fresh supplemental searches for Config4 records
retained by the canonical plan as CERTIFIED_ZERO, the four-task smoke gate, the
two-task canary gate, and all 192 canonical production bundles sequentially.
For the recorded 24-way Slurm launch, use the frozen
g001_terminal5_mi2101x_full_v1.sbatch in the authoritative source directory
after the runtime, plan, supplemental-search, and gate steps below.
EOF
}

RUN_ROOT=""
CXX="g++"
PYTHON="python3"
while [[ $# -gt 0 ]]; do
  case "$1" in
    --run-root) [[ $# -ge 2 ]] || { usage >&2; exit 64; }; RUN_ROOT="$2"; shift 2 ;;
    --cxx) [[ $# -ge 2 ]] || { usage >&2; exit 64; }; CXX="$2"; shift 2 ;;
    --python) [[ $# -ge 2 ]] || { usage >&2; exit 64; }; PYTHON="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown argument: $1" >&2; usage >&2; exit 64 ;;
  esac
done
[[ -n "${RUN_ROOT}" ]] || { usage >&2; exit 64; }
[[ "$(uname -s)" == "Linux" ]] || { echo "Linux is required" >&2; exit 64; }
PYTHON_PATH="$(command -v -- "${PYTHON}")" || { echo "Python executable not found: ${PYTHON}" >&2; exit 69; }
"${PYTHON_PATH}" -E -s -S -B -c \
  'import sys; raise SystemExit(0 if sys.version_info >= (3, 12) else 1)' \
  || { echo "Python 3.12 or newer is required" >&2; exit 69; }
PYTHON="${PYTHON_PATH}"

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
REPO_ROOT="$(cd -- "${SCRIPT_DIR}/.." && pwd -P)"
FULL_ROOT="${REPO_ROOT}/computation/evidence/full"
TRANSFER_SOURCE="${REPO_ROOT}/computation/evidence/production/exact_final_workspace/source"
FROZEN_PLAN="${REPO_ROOT}/computation/evidence/production/exact_final_workspace/plan/terminal5_plan_v1/terminal_plan_v1.json"
C157_ARCHIVE="${FULL_ROOT}/results/c157_resume861_collect_compat_v2r1_20260818T160902Z_publication3_archive_20260818T175225Z/AMD_G001_C157_JOB376839_RESUME861_V1_SLURM377219_COLLECTED_20260818T175225Z.tar.gz"
C157_PACKAGE="${FULL_ROOT}/results/c157_resume861_collect_compat_v2r1_20260818T160902Z_publication3/G001_C157_JOB376839_RESUME861_V1_SLURM377219_COLLECTED"
CONFIG4_ARCHIVE="${FULL_ROOT}/results/config4_job377045_recovery_v1_20260818T131100Z_workspace/AMD_G001_CONFIG4_P2_HEAVY16_V1_SLURM377045_RECOVERED_COLLECTED.tar.gz"
CONFIG4_PACKAGE="${FULL_ROOT}/results/config4_job377045_recovery_v1_20260818T131100Z_workspace/G001_CONFIG4_P2_HEAVY16_V1_SLURM377045_RECOVERED_COLLECTED"

for required in "${TRANSFER_SOURCE}" "${FROZEN_PLAN}" "${C157_ARCHIVE}" "${C157_PACKAGE}" "${CONFIG4_ARCHIVE}" "${CONFIG4_PACKAGE}"; do
  [[ -e "${required}" ]] || { echo "missing required input: ${required}" >&2; exit 66; }
done
[[ ! -e "${RUN_ROOT}" ]] || { echo "run root already exists: ${RUN_ROOT}" >&2; exit 73; }
mkdir -p -- \
  "${RUN_ROOT}/workspace/source" \
  "${RUN_ROOT}/workspace/runtime" \
  "${RUN_ROOT}/workspace/plan" \
  "${RUN_ROOT}/smoke_run" \
  "${RUN_ROOT}/production_run/production_v1"
cp -a -- "${TRANSFER_SOURCE}/." "${RUN_ROOT}/workspace/source/"

WORKSPACE="${RUN_ROOT}/workspace"
SOURCE="${WORKSPACE}/source"
RUNTIME="${WORKSPACE}/runtime/terminal5_runtime_v1"
PLAN="${WORKSPACE}/plan/terminal5_plan_v1"
SMOKE_RUN="${RUN_ROOT}/smoke_run"
PRODUCTION_RUN="${RUN_ROOT}/production_run/production_v1"
CONFIG4_CERTIFIED_ZERO_RUN="${RUN_ROOT}/config4_certified_zero_run"

"${PYTHON}" -E -s -S -B "${SOURCE}/verify_g001_terminal5_source_freeze_v1.py" --source-dir "${SOURCE}"
"${PYTHON}" -E -s -S -B "${SOURCE}/test_g001_terminal5_v1.py"
"${PYTHON}" -E -s -S -B "${SOURCE}/test_g001_remaining_leaf_pipeline.py"
"${PYTHON}" -E -s -S -B "${SOURCE}/g001_terminal5_build_runtime_v1.py" \
  --source-dir "${SOURCE}" --workspace-root "${WORKSPACE}" \
  --output "${RUNTIME}" --cxx "${CXX}"
"${PYTHON}" -E -s -S -B "${SOURCE}/make_g001_terminal5_plan_v1.py" \
  --c157-archive "${C157_ARCHIVE}" --c157-package "${C157_PACKAGE}" \
  --config4-archive "${CONFIG4_ARCHIVE}" --config4-package "${CONFIG4_PACKAGE}" \
  --workspace "${WORKSPACE}" --source-dir "${SOURCE}" \
  --runtime-dir "${RUNTIME}" --output "${PLAN}" \
  --plan-id g001-terminal5-v1-candidate4
"${PYTHON}" -E -s -S -B "${SOURCE}/verify_g001_terminal5_plan_v1.py" \
  --plan-dir "${PLAN}" --workspace "${WORKSPACE}" --source-dir "${SOURCE}"
"${PYTHON}" -E -s -S -B - "${PLAN}/terminal_plan_v1.json" "${FROZEN_PLAN}" <<'PY'
import hashlib
import json
import pathlib
import sys

fresh_path = pathlib.Path(sys.argv[1])
frozen_path = pathlib.Path(sys.argv[2])
frozen_raw = frozen_path.read_bytes()
expected_frozen_sha256 = "b317a3b7cef71e11fea762ce5e70322f168e06c6e04b97293f066cb2e313bdae"
actual_frozen_sha256 = hashlib.sha256(frozen_raw).hexdigest()
if actual_frozen_sha256 != expected_frozen_sha256:
    raise SystemExit(f"frozen terminal plan SHA-256 mismatch: {actual_frozen_sha256}")
fresh = json.loads(fresh_path.read_text(encoding="utf-8"))
frozen = json.loads(frozen_raw)
# A fresh compiler necessarily changes executable/runtime hashes.  Every
# mathematical/search field must nevertheless reproduce as the exact same
# structured JSON value.
roster_fields = (
    "schema", "plan_id", "inputs", "invariants", "claim_boundary",
    "records", "bundles",
)
for field in roster_fields:
    if fresh.get(field) != frozen.get(field):
        raise SystemExit(f"fresh terminal plan roster differs in field: {field}")
if set(fresh) != set(frozen) or set(fresh) != set(roster_fields) | {"runtime"}:
    raise SystemExit("terminal plan top-level field set mismatch")
print(
    "LEECH18_TERMINAL5_PLAN_ROSTER_MATCH "
    "records=39030 search=39000 certified_zero=30 bundles=192 "
    f"frozen_plan_sha256={actual_frozen_sha256}"
)
PY

"${PYTHON}" -E -s -S -B "${SCRIPT_DIR}/validate_terminal5_preflight.py" \
  --plan-dir "${PLAN}" --workspace "${WORKSPACE}" --source-dir "${SOURCE}" \
  --frozen-plan "${FROZEN_PLAN}"

set +e
"${PYTHON}" -E -s -S -B "${SCRIPT_DIR}/recompute_config4_certified_zero.py" \
  --plan "${PLAN}/terminal_plan_v1.json" --frozen-plan "${FROZEN_PLAN}" \
  --workspace "${WORKSPACE}" --source-dir "${SOURCE}" \
  --run-root "${CONFIG4_CERTIFIED_ZERO_RUN}" --workers 15
rc=$?
set -e
if [[ "${rc}" == "2" ]]; then
  echo "LEECH18_TERMINAL5_CONFIG4_SUPPLEMENTAL_VERIFIED_FOUND global_complete=0" >&2
  exit 2
fi
[[ "${rc}" == "0" ]] || exit "${rc}"

for task in $(seq 0 3); do
  set +e
  "${PYTHON}" -E -s -S -B "${SOURCE}/run_g001_terminal5_bundle_v1.py" \
    --plan-dir "${PLAN}" --workspace "${WORKSPACE}" --source-dir "${SOURCE}" \
    --run-root "${SMOKE_RUN}" --mode smoke --gate-task "${task}" --workers 15
  rc=$?
  set -e
  if [[ "${rc}" == "2" ]]; then
    echo "LEECH18_TERMINAL5_SMOKE_VERIFIED_FOUND task=${task} global_complete=0" >&2
    exit 2
  fi
  [[ "${rc}" == "0" ]] || exit "${rc}"
done
"${PYTHON}" -E -s -S -B "${SOURCE}/verify_g001_terminal5_gate_v1.py" \
  --plan-dir "${PLAN}" --workspace "${WORKSPACE}" --source-dir "${SOURCE}" \
  --run-root "${SMOKE_RUN}" --mode smoke --output "${RUN_ROOT}/SMOKE_GATE_AUDIT.json"

for task in $(seq 0 1); do
  set +e
  "${PYTHON}" -E -s -S -B "${SOURCE}/run_g001_terminal5_bundle_v1.py" \
    --plan-dir "${PLAN}" --workspace "${WORKSPACE}" --source-dir "${SOURCE}" \
    --run-root "${PRODUCTION_RUN}" --mode canary --gate-task "${task}" --workers 15
  rc=$?
  set -e
  if [[ "${rc}" == "2" ]]; then
    echo "LEECH18_TERMINAL5_CANARY_VERIFIED_FOUND task=${task} global_complete=0" >&2
    exit 2
  fi
  [[ "${rc}" == "0" ]] || exit "${rc}"
done
"${PYTHON}" -E -s -S -B "${SOURCE}/verify_g001_terminal5_gate_v1.py" \
  --plan-dir "${PLAN}" --workspace "${WORKSPACE}" --source-dir "${SOURCE}" \
  --run-root "${PRODUCTION_RUN}" --mode canary --output "${RUN_ROOT}/CANARY_GATE_AUDIT.json"

for bundle in $(seq 0 191); do
  set +e
  "${PYTHON}" -E -s -S -B "${SOURCE}/run_g001_terminal5_bundle_v1.py" \
    --plan-dir "${PLAN}" --workspace "${WORKSPACE}" --source-dir "${SOURCE}" \
    --run-root "${PRODUCTION_RUN}" --mode production --bundle-index "${bundle}" --workers 15
  rc=$?
  set -e
  if [[ "${rc}" == "2" ]]; then
    echo "LEECH18_TERMINAL5_PRODUCTION_VERIFIED_FOUND bundle=${bundle} global_complete=0" >&2
    exit 2
  fi
  [[ "${rc}" == "0" ]] || exit "${rc}"
done

"${PYTHON}" -E -s -S -B "${SOURCE}/collect_g001_terminal5_results_v1.py" \
  --plan-dir "${PLAN}" --workspace "${WORKSPACE}" --source-dir "${SOURCE}" \
  --run-root "${PRODUCTION_RUN}" --all --output "${RUN_ROOT}/GLOBAL_REPRODUCTION.json"
"${PYTHON}" -E -s -S -B "${SCRIPT_DIR}/validate_terminal5_preflight.py" \
  --plan-dir "${PLAN}" --workspace "${WORKSPACE}" --source-dir "${SOURCE}" \
  --frozen-plan "${FROZEN_PLAN}" \
  --run-root "${PRODUCTION_RUN}" \
  --output-json "${RUN_ROOT}/TERMINAL5_PREFLIGHT.json"
"${PYTHON}" -E -s -S -B - \
  "${RUN_ROOT}/GLOBAL_REPRODUCTION.json" \
  "${PLAN}/terminal_plan_v1.json" \
  "${CONFIG4_CERTIFIED_ZERO_RUN}/RECOMPUTATION_SUMMARY.json" \
  "${CONFIG4_CERTIFIED_ZERO_RUN}/logs/authoritative_plan_verifier.stdout.txt" \
  "${CONFIG4_CERTIFIED_ZERO_RUN}/logs/authoritative_plan_verifier.stderr.txt" <<'PY'
import hashlib, json, pathlib, sys
path = pathlib.Path(sys.argv[1])
value = json.loads(path.read_text(encoding="utf-8"))
fresh_plan_sha256 = hashlib.sha256(pathlib.Path(sys.argv[2]).read_bytes()).hexdigest()
supplemental = json.loads(pathlib.Path(sys.argv[3]).read_text(encoding="utf-8"))
verifier_stdout = pathlib.Path(sys.argv[4]).read_bytes()
verifier_stderr = pathlib.Path(sys.argv[5]).read_bytes()
expected_verifier_stdout = (
    "G001_TERMINAL5_PLAN_V1_VERIFIED records=39030 search=39000 zero=30 "
    f"bundles=192 sha256={fresh_plan_sha256}\n"
).encode("ascii")
if verifier_stdout != expected_verifier_stdout:
    raise SystemExit("persisted authoritative plan verifier stdout mismatch")
if verifier_stderr != b"":
    raise SystemExit("persisted authoritative plan verifier stderr is not empty")
expected_envelope = {
    "schema": "G001_TERMINAL5_COLLECTION_V1",
    "plan_id": "g001-terminal5-v1-candidate4",
    "scope": "global",
    "status": "GLOBAL_ZERO_COMPLETE",
    "search_receipts": 39000,
    "certified_zero_records": 30,
    "displayed_partition_records": 39030,
    "terminal_search_complete": True,
    "global_nonexistence": True,
    "configuration_nonexistence": False,
    "timeouts_are_non_evidence": True,
    "claim": "all 39,000 terminal search receipts plus 30 prior certified zeros are exact",
}
for key, expected in expected_envelope.items():
    if value.get(key) != expected:
        raise SystemExit(f"unexpected global field {key}: {value.get(key)!r}")
if value.get("plan_sha256") != fresh_plan_sha256:
    raise SystemExit("global result is not bound to the fresh terminal plan")
expected_supplemental = {
    "schema": "LEECH18_CONFIG4_CERTIFIED_ZERO_FRESH_RECOMPUTATION_V1",
    "status": "ZERO_COMPLETE",
    "configuration": 4,
    "mode": "g001_row3",
    "prior_classification": "CERTIFIED_ZERO",
    "fresh_terminal_searches": 30,
    "fresh_zero_results": 30,
    "workers": 15,
    "terminal_plan_id": "g001-terminal5-v1-candidate4",
    "frozen_terminal_plan_sha256": "b317a3b7cef71e11fea762ce5e70322f168e06c6e04b97293f066cb2e313bdae",
    "non_runtime_plan_fields_match_frozen": True,
    "authoritative_plan_runtime_verified": True,
    "derived_roster_bytes": 12402,
    "derived_roster_sha256": "ead047bedce8674ce516172919846873531b82932a4533a57ac88f7b3fea5de9",
    "reported_terminal5_nodes_excluding_supplemental": 7964472779,
    "authoritative_plan_verifier_stdout_sha256": hashlib.sha256(verifier_stdout).hexdigest(),
    "authoritative_plan_verifier_stderr_sha256": hashlib.sha256(verifier_stderr).hexdigest(),
}
for key, expected in expected_supplemental.items():
    if supplemental.get(key) != expected:
        raise SystemExit(f"unexpected Config4 supplemental field {key}: {supplemental.get(key)!r}")
if supplemental.get("terminal_plan_sha256") != fresh_plan_sha256:
    raise SystemExit("Config4 supplemental result is not bound to the fresh terminal plan")
supplemental_nodes = supplemental.get("supplemental_nodes")
if isinstance(supplemental_nodes, bool) or not isinstance(supplemental_nodes, int) or supplemental_nodes < 0:
    raise SystemExit("invalid Config4 supplemental node count")
supplemental_records = supplemental.get("records")
if not isinstance(supplemental_records, list) or len(supplemental_records) != 30:
    raise SystemExit("Config4 supplemental record count mismatch")
if len({item.get("record_id") for item in supplemental_records if isinstance(item, dict)}) != 30:
    raise SystemExit("Config4 supplemental record identities are not exact")
expected_by_configuration = {
    "1": (5176, 0, 5176, 1321606123),
    "4": (1294, 30, 1324, 225016655),
    "5": (25254, 0, 25254, 4242081806),
    "6": (3977, 0, 3977, 1165724514),
    "7": (3299, 0, 3299, 1010043681),
}
observed = value.get("by_configuration")
if not isinstance(observed, dict) or set(observed) != set(expected_by_configuration):
    raise SystemExit("unexpected global configuration roster")
for configuration, expected in expected_by_configuration.items():
    item = observed[configuration]
    actual = (
        item.get("search_receipts"), item.get("certified_zero_records"),
        item.get("displayed_partition_records"), item.get("nodes_sum"),
    )
    if actual != expected or item.get("terminal_zero") is not True:
        raise SystemExit(f"unexpected Configuration {configuration} result: {actual!r}")
nodes = sum(item[3] for item in expected_by_configuration.values())
if nodes != 7_964_472_779:
    raise SystemExit(f"internal expected-node total mismatch: {nodes}")
print(
    "LEECH18_TERMINAL5_FULL_RECOMPUTATION_OK "
    "fresh_search=39030 canonical_search_receipts=39000 "
    "supplemental_reclassified=30 canonical_certified_zero_records=30 "
    "displayed_records=39030 reported_nodes=7964472779 "
    f"supplemental_nodes={supplemental_nodes}"
)
PY
