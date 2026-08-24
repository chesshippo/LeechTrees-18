#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage: preflight_linux.sh [--cxx CXX] [--python PYTHON] [--skip-rosters]

Read-only host and frozen-input preflight for the Linux C157 and Terminal5
recomputation stages. It compiles one temporary C++20 probe below /tmp and
deletes it. It does not launch a production search.
EOF
}

CXX="g++"
PYTHON="python3"
SKIP_ROSTERS=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    --cxx) [[ $# -ge 2 ]] || { usage >&2; exit 64; }; CXX="$2"; shift 2 ;;
    --python) [[ $# -ge 2 ]] || { usage >&2; exit 64; }; PYTHON="$2"; shift 2 ;;
    --skip-rosters) SKIP_ROSTERS=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "LEECH18_LINUX_PREFLIGHT_FAIL: unknown argument: $1" >&2; usage >&2; exit 64 ;;
  esac
done

fail() {
  echo "LEECH18_LINUX_PREFLIGHT_FAIL: $*" >&2
  exit 1
}

[[ "$(uname -s)" == "Linux" ]] || fail "Linux is required"
SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
REPO_ROOT="$(cd -- "${SCRIPT_DIR}/.." && pwd -P)"

for command in awk bash find gzip mktemp seq sha256sum tar uname; do
  command -v "${command}" >/dev/null 2>&1 || fail "missing command: ${command}"
done
PYTHON_PATH="$(command -v "${PYTHON}")" || fail "Python executable not found: ${PYTHON}"
CXX_PATH="$(command -v "${CXX}")" || fail "C++ compiler not found: ${CXX}"

PYTHON_VERSION="$("${PYTHON_PATH}" -E -s -S -B -c 'import sys; print(".".join(map(str, sys.version_info[:3])))')" \
  || fail "could not query Python version"
"${PYTHON_PATH}" -E -s -S -B -c 'import sys; raise SystemExit(0 if sys.version_info >= (3, 12) else 1)' \
  || fail "Python 3.12 or newer is required; found ${PYTHON_VERSION}"

PROBE="$(mktemp -d "${TMPDIR:-/tmp}/leech18-cxx20-probe.XXXXXXXX")"
trap 'rm -rf -- "${PROBE}"' EXIT
printf '%s\n' '#include <bit>' '#include <cstdint>' 'int main(){ return std::popcount(std::uint32_t{7}) == 3 ? 0 : 1; }' >"${PROBE}/probe.cpp"
"${CXX_PATH}" -O2 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  "${PROBE}/probe.cpp" -o "${PROBE}/probe" || fail "C++20 probe compilation failed"
"${PROBE}/probe" || fail "C++20 probe executable failed"

PLAN="${REPO_ROOT}/computation/evidence/production/exact_final_workspace/plan/terminal5_plan_v1/terminal_plan_v1.json"
[[ -f "${PLAN}" && ! -L "${PLAN}" ]] || fail "frozen terminal plan is missing"
EXPECTED_PLAN_SHA256="b317a3b7cef71e11fea762ce5e70322f168e06c6e04b97293f066cb2e313bdae"
ACTUAL_PLAN_SHA256="$(sha256sum -- "${PLAN}" | awk '{print $1}')"
[[ "${ACTUAL_PLAN_SHA256}" == "${EXPECTED_PLAN_SHA256}" ]] \
  || fail "frozen terminal plan SHA-256 mismatch: ${ACTUAL_PLAN_SHA256}"

EVIDENCE_ROOT="${REPO_ROOT}/computation/evidence/full"
[[ -d "${EVIDENCE_ROOT}" && ! -L "${EVIDENCE_ROOT}" ]] \
  || fail "complete evidence asset is not installed at computation/evidence/full"

echo "LINUX_KERNEL=$(uname -srmo)"
echo "BASH_VERSION=${BASH_VERSION}"
echo "PYTHON_EXECUTABLE=${PYTHON_PATH}"
echo "PYTHON_VERSION=${PYTHON_VERSION}"
echo "CXX_EXECUTABLE=${CXX_PATH}"
"${CXX_PATH}" --version
echo "LOGICAL_CPUS=$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo UNKNOWN)"
df -Pk -- "${REPO_ROOT}"
echo "FROZEN_PLAN_SHA256=${ACTUAL_PLAN_SHA256}"

if [[ "${SKIP_ROSTERS}" == 0 ]]; then
  "${PYTHON_PATH}" -E -s -S -B "${REPO_ROOT}/scripts/recompute_config4_certified_zero.py" --list-only
  if [[ -f "${REPO_ROOT}/scripts/recompute_c157_full.py" ]]; then
    "${PYTHON_PATH}" -E -s -S -B "${REPO_ROOT}/scripts/recompute_c157_full.py" \
      --preflight --compiler "${CXX_PATH}"
  else
    fail "scripts/recompute_c157_full.py is missing"
  fi
fi

echo "LEECH18_LINUX_PREFLIGHT_OK python=${PYTHON_VERSION} plan_sha256=${ACTUAL_PLAN_SHA256} rosters_checked=$((1 - SKIP_ROSTERS))"
