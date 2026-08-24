#!/usr/bin/env python3
"""Fail-closed fresh rerun harness for the historical Configuration 3 / A2 census.

The historical ledger is used only as a hash-pinned expected-result oracle.
Every fresh process has raw stdout/stderr plus a canonical JSON receipt and
SHA-256 sidecar.  A completed receipt is revalidated from raw bytes on resume.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import csv
import ctypes
import datetime as dt
import decimal
import hashlib
import io
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Iterable


SCHEMA = "config3-a2-fresh-rerun-v1"
RECEIPT_SCHEMA = "config3-a2-partition-receipt-v1"
BUILD_SCHEMA = "config3-a2-build-receipt-v1"
FULL_RUN_CONFIRMATION = "RUN_ALL_47_CONFIG3_A2"
MAX_JOBS = 8
HARD_MEMORY_LIMIT_PERCENT = 92.0
FIXTURE_KEY = "a2_separate|path_7_4"

INPUT_PINS = {
    "source": (
        "computation/evidence/production/"
        "prior_three_configurations/work/a2_solver/a2_topology_free_search.cpp",
        "e8dedc62323152ba586f9c8607d119440c8be9927ec4d38e546ba11de9100e9c",
    ),
    "exact_cover_header": (
        "computation/evidence/production/"
        "prior_three_configurations/work/a2_solver/a2_multi_edge_exact_cover.hpp",
        "c156eae52bceef28db0df1a38d10dea253de09e5f627d0952a6bb1b9356cd813",
    ),
    "optimized_header": (
        "computation/evidence/production/"
        "prior_three_configurations/work/a2_solver/a2_multi_edge_exact_cover_optimized.hpp",
        "5320c920e800ce2f9e2348b90d672e26cddd748b43bc02bc24b9146dedb5e48b",
    ),
    "stronger_header": (
        "computation/evidence/production/"
        "prior_three_configurations/work/a2_solver/a2_multi_edge_stronger_relaxation.hpp",
        "e58f917a631c48f2419835d41c2b0ee164f0d24f44ba489c152b9c00cddbbd5c",
    ),
    "expected_ledger": (
        "computation/evidence/production/"
        "prior_three_configurations/outputs/A2_MULTI_EDGE_PARTITION_RESULTS.csv",
        "bc6a5909d2de7b0cbc0e1a886a03c675b92419c8c4e553ad944e1a123dbc93ac",
    ),
}

EXPECTED_HEADER = [
    "mode",
    "partition",
    "status",
    "nodes",
    "wall_seconds",
    "exit_code",
    "notes",
]

COMMON_FLAGS = [
    "--multi-edge-cover",
    "--multi-edge-cover-no-hall",
    "--multi-edge-cover-budget",
    "100",
    "--multi-edge-cover-no-exact-hall",
]

EXPECTED_TOTALS = {
    "a2_attached": {
        "partitions": 7,
        "nodes": 17_650_190,
        "wall_seconds": decimal.Decimal("2269.8161381"),
    },
    "a2_separate": {
        "partitions": 40,
        "nodes": 150_092_642,
        "wall_seconds": decimal.Decimal("43265.2712488"),
    },
}


class HarnessError(RuntimeError):
    pass


def expected_keys() -> list[str]:
    result = ["a2_attached|root_0"]
    result.extend(f"a2_attached|path_1_{i}" for i in range(6))
    result.extend(f"a2_separate|root_{i}" for i in range(4))
    result.extend(f"a2_separate|path_4_{i}" for i in range(6))
    result.extend(f"a2_separate|path_5_{i}" for i in range(5))
    result.extend(f"a2_separate|path_6_{i}" for i in range(2))
    result.extend(f"a2_separate|path_7_{i}" for i in range(8))
    result.extend(f"a2_separate|path_8_{i}" for i in range(15))
    if len(result) != 47 or len(set(result)) != 47:
        raise AssertionError("internal partition roster is not exactly 47 unique keys")
    return result


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while True:
            block = stream.read(1024 * 1024)
            if not block:
                return digest.hexdigest()
            digest.update(block)


def file_ref(path: Path) -> dict[str, Any]:
    return {
        "path": str(path.resolve()),
        "bytes": path.stat().st_size,
        "sha256": sha256_file(path),
    }


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat().replace("+00:00", "Z")


def canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode(
        "utf-8"
    )


def atomic_write_new(path: Path, raw: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    if path.exists() or temporary.exists():
        raise HarnessError(f"refusing to overwrite existing artifact: {path}")
    with temporary.open("xb") as stream:
        stream.write(raw)
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, path)


def write_receipt_new(path: Path, value: Any) -> dict[str, Any]:
    raw = canonical_json_bytes(value)
    atomic_write_new(path, raw)
    digest = sha256_bytes(raw)
    atomic_write_new(
        path.with_name(path.name + ".sha256"),
        f"{digest}  {path.name}\n".encode("ascii"),
    )
    return {"path": str(path.resolve()), "bytes": len(raw), "sha256": digest}


def verify_receipt_file(path: Path) -> tuple[dict[str, Any], dict[str, Any]]:
    if not path.is_file():
        raise HarnessError(f"missing receipt: {path}")
    sidecar = path.with_name(path.name + ".sha256")
    if not sidecar.is_file():
        raise HarnessError(f"missing receipt sidecar: {sidecar}")
    raw = path.read_bytes()
    digest = sha256_bytes(raw)
    expected_sidecar = f"{digest}  {path.name}\n".encode("ascii")
    if sidecar.read_bytes() != expected_sidecar:
        raise HarnessError(f"bad receipt SHA-256 sidecar: {sidecar}")
    try:
        value = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise HarnessError(f"invalid JSON receipt {path}: {exc}") from exc
    return value, {"path": str(path.resolve()), "bytes": len(raw), "sha256": digest}


def memory_load_percent() -> float | None:
    if os.name == "nt":
        class MemoryStatus(ctypes.Structure):
            _fields_ = [
                ("dwLength", ctypes.c_ulong),
                ("dwMemoryLoad", ctypes.c_ulong),
                ("ullTotalPhys", ctypes.c_ulonglong),
                ("ullAvailPhys", ctypes.c_ulonglong),
                ("ullTotalPageFile", ctypes.c_ulonglong),
                ("ullAvailPageFile", ctypes.c_ulonglong),
                ("ullTotalVirtual", ctypes.c_ulonglong),
                ("ullAvailVirtual", ctypes.c_ulonglong),
                ("ullAvailExtendedVirtual", ctypes.c_ulonglong),
            ]

        status = MemoryStatus()
        status.dwLength = ctypes.sizeof(MemoryStatus)
        if not ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(status)):
            return None
        return float(status.dwMemoryLoad)
    meminfo = Path("/proc/meminfo")
    if meminfo.is_file():
        fields: dict[str, int] = {}
        for line in meminfo.read_text(encoding="ascii").splitlines():
            name, value = line.split(":", 1)
            fields[name] = int(value.strip().split()[0])
        if fields.get("MemTotal"):
            return 100.0 * (1.0 - fields.get("MemAvailable", 0) / fields["MemTotal"])
    return None


def enforce_memory_limit(context: str) -> float | None:
    load = memory_load_percent()
    if load is not None and load > HARD_MEMORY_LIMIT_PERCENT:
        raise HarnessError(
            f"memory guard tripped before {context}: {load:.1f}% > "
            f"{HARD_MEMORY_LIMIT_PERCENT:.1f}%"
        )
    return load


def resolve_inputs(workspace: Path) -> dict[str, dict[str, Any]]:
    resolved: dict[str, dict[str, Any]] = {}
    for name, (relative, expected_hash) in INPUT_PINS.items():
        path = workspace / relative
        if not path.is_file():
            raise HarnessError(f"missing pinned input {name}: {path}")
        actual = sha256_file(path)
        if actual != expected_hash:
            raise HarnessError(
                f"pinned input mismatch {name}: expected={expected_hash} actual={actual}"
            )
        resolved[name] = {
            "relative_path": relative,
            "path": str(path.resolve()),
            "bytes": path.stat().st_size,
            "sha256": actual,
        }
    return resolved


def selector_args(partition: str) -> list[str]:
    root_match = re.fullmatch(r"root_(\d+)", partition)
    if root_match:
        return ["--root-branch", root_match.group(1)]
    path_match = re.fullmatch(r"path_(\d+)_(\d+)", partition)
    if path_match:
        return ["--branch-path", f"{path_match.group(1)},{path_match.group(2)}"]
    raise HarnessError(f"invalid canonical partition selector: {partition}")


def load_expected_plan(
    workspace: Path, inputs: dict[str, dict[str, Any]]
) -> list[dict[str, Any]]:
    ledger_path = Path(inputs["expected_ledger"]["path"])
    raw = ledger_path.read_bytes()
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise HarnessError(f"ledger is not strict UTF-8: {exc}") from exc
    reader = csv.DictReader(io.StringIO(text, newline=""))
    if reader.fieldnames != EXPECTED_HEADER:
        raise HarnessError(
            f"ledger header mismatch: expected={EXPECTED_HEADER!r} actual={reader.fieldnames!r}"
        )
    rows = list(reader)
    keys = [f"{row['mode']}|{row['partition']}" for row in rows]
    canonical_keys = expected_keys()
    if keys != canonical_keys:
        missing = sorted(set(canonical_keys) - set(keys))
        extra = sorted(set(keys) - set(canonical_keys))
        raise HarnessError(
            "ledger is not the exact ordered 47-partition roster: "
            f"missing={missing} extra={extra} ordered_equal={keys == canonical_keys}"
        )
    if len(set(keys)) != 47:
        raise HarnessError("ledger contains duplicate partition keys")

    totals = {
        mode: {"partitions": 0, "nodes": 0, "wall_seconds": decimal.Decimal(0)}
        for mode in EXPECTED_TOTALS
    }
    plan: list[dict[str, Any]] = []
    for row in rows:
        key = f"{row['mode']}|{row['partition']}"
        if row["status"] != "ZERO":
            raise HarnessError(f"historical expected status is not ZERO: {key}")
        if row["exit_code"] != "0":
            raise HarnessError(f"historical expected exit field is not 0: {key}")
        try:
            nodes = int(row["nodes"])
            wall = decimal.Decimal(row["wall_seconds"])
        except (ValueError, decimal.InvalidOperation) as exc:
            raise HarnessError(f"invalid ledger numeric field for {key}: {exc}") from exc
        if nodes <= 0 or wall <= 0:
            raise HarnessError(f"nonpositive ledger metric for {key}")
        totals[row["mode"]]["partitions"] += 1
        totals[row["mode"]]["nodes"] += nodes
        totals[row["mode"]]["wall_seconds"] += wall
        plan.append(
            {
                "key": key,
                "mode": row["mode"],
                "partition": row["partition"],
                "expected_status": "ZERO",
                "expected_nodes": nodes,
                "historical_wall_seconds": row["wall_seconds"],
                "historical_exit_field": row["exit_code"],
                "historical_note": row["notes"],
                "argv_tail": [
                    "--mode",
                    row["mode"],
                    *selector_args(row["partition"]),
                    *COMMON_FLAGS,
                ],
            }
        )
    if totals != EXPECTED_TOTALS:
        raise HarnessError(f"ledger totals mismatch: expected={EXPECTED_TOTALS} actual={totals}")
    return plan


def plan_document(
    workspace: Path,
    inputs: dict[str, dict[str, Any]],
    plan: list[dict[str, Any]],
) -> dict[str, Any]:
    return {
        "schema": SCHEMA,
        "workspace": str(workspace.resolve()),
        "harness": file_ref(Path(__file__).resolve()),
        "inputs": inputs,
        "common_flags": COMMON_FLAGS,
        "partition_count": len(plan),
        "fixture_key": FIXTURE_KEY,
        "full_run_confirmation": FULL_RUN_CONFIRMATION,
        "partitions": plan,
        "historical_evidence_caveat": {
            "inferred_exit_key": "a2_separate|path_6_1",
            "ledger_is_expected_oracle_only": True,
            "fresh_process_exit_required": True,
        },
    }


def ensure_plan_file(run_dir: Path, document: dict[str, Any]) -> dict[str, Any]:
    path = run_dir / "PLAN.json"
    raw = canonical_json_bytes(document)
    if path.exists():
        value, ref = verify_receipt_file(path)
        if value != document or path.read_bytes() != raw:
            raise HarnessError(f"existing run plan differs from current pinned plan: {path}")
        return ref
    return write_receipt_new(path, document)


def compiler_identity(compiler: Path) -> dict[str, Any]:
    version = subprocess.run(
        [str(compiler), "--version"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if version.returncode != 0 or version.stderr:
        raise HarnessError(
            f"compiler --version failed or wrote stderr: exit={version.returncode} "
            f"stderr={version.stderr!r}"
        )
    return {
        **file_ref(compiler),
        "version_stdout_sha256": sha256_bytes(version.stdout),
        "version_stdout": version.stdout.decode("utf-8", errors="strict"),
    }


def build_solver(
    run_dir: Path,
    inputs: dict[str, dict[str, Any]],
    plan_ref: dict[str, Any],
    compiler_arg: str | None,
) -> tuple[Path, dict[str, Any]]:
    build_dir = run_dir / "build"
    executable = build_dir / (
        "a2_topology_free_search_config3.exe"
        if os.name == "nt"
        else "a2_topology_free_search_config3"
    )
    receipt_path = build_dir / "BUILD_RECEIPT.json"
    if receipt_path.exists():
        receipt, receipt_ref = verify_receipt_file(receipt_path)
        if receipt.get("schema") != BUILD_SCHEMA or receipt.get("status") != "PASS":
            raise HarnessError("existing build receipt is not a passing v1 receipt")
        if receipt.get("plan_sha256") != plan_ref["sha256"]:
            raise HarnessError("existing build receipt binds a different plan")
        if not executable.is_file():
            raise HarnessError(f"build receipt exists but executable is missing: {executable}")
        current_ref = file_ref(executable)
        if current_ref != receipt.get("executable"):
            raise HarnessError("built executable no longer matches its receipt")
        return executable, receipt_ref

    enforce_memory_limit("compile")
    compiler_text = compiler_arg or shutil.which("g++")
    if not compiler_text:
        raise HarnessError("g++ not found; pass --compiler with a C++20 compiler")
    compiler = Path(compiler_text).resolve(strict=True)
    identity = compiler_identity(compiler)
    build_dir.mkdir(parents=True, exist_ok=True)
    stdout_path = build_dir / "compiler.stdout.txt"
    stderr_path = build_dir / "compiler.stderr.txt"
    staging = build_dir / (executable.name + ".staging")
    for path in (stdout_path, stderr_path, staging):
        if path.exists():
            raise HarnessError(f"partial build artifact already exists; use a new run dir: {path}")
    command = [
        str(compiler),
        "-std=c++20",
        "-O2",
        "-DNDEBUG",
        "-Wall",
        "-Wextra",
        "-Wpedantic",
        "-Werror",
        "-fdiagnostics-color=never",
        inputs["source"]["path"],
        "-o",
        str(staging.resolve()),
    ]
    started = utc_now()
    start_clock = time.perf_counter()
    with stdout_path.open("xb") as out, stderr_path.open("xb") as err:
        completed = subprocess.run(command, stdout=out, stderr=err, check=False)
    elapsed = time.perf_counter() - start_clock
    finished = utc_now()
    if completed.returncode != 0:
        raise HarnessError(
            f"compile failed with exit {completed.returncode}; see {stderr_path}"
        )
    if stderr_path.stat().st_size != 0:
        raise HarnessError(f"strict compile produced nonempty stderr: {stderr_path}")
    if not staging.is_file() or staging.stat().st_size == 0:
        raise HarnessError("compiler returned 0 without a nonempty staging executable")
    os.replace(staging, executable)
    receipt = {
        "schema": BUILD_SCHEMA,
        "status": "PASS",
        "plan_sha256": plan_ref["sha256"],
        "compiler": identity,
        "command": command,
        "started_utc": started,
        "finished_utc": finished,
        "elapsed_seconds": elapsed,
        "exit_code": completed.returncode,
        "compiler_stdout": file_ref(stdout_path),
        "compiler_stderr": file_ref(stderr_path),
        "executable": file_ref(executable),
        "inputs": inputs,
    }
    receipt_ref = write_receipt_new(receipt_path, receipt)
    return executable, receipt_ref


def parse_result(raw: bytes) -> dict[str, str]:
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise HarnessError(f"stdout is not UTF-8: {exc}") from exc
    lines = [line for line in text.splitlines() if line]
    if len(lines) != 1 or not lines[0].startswith("RESULT "):
        raise HarnessError(f"expected exactly one nonempty RESULT line, got {lines!r}")
    fields: dict[str, str] = {}
    for token in lines[0].split()[1:]:
        if "=" not in token:
            raise HarnessError(f"malformed RESULT token: {token!r}")
        name, value = token.split("=", 1)
        if name in fields:
            raise HarnessError(f"duplicate RESULT field: {name}")
        fields[name] = value
    return fields


def validate_observation(
    item: dict[str, Any], exit_code: int, stdout_path: Path, stderr_path: Path
) -> tuple[dict[str, str] | None, list[str]]:
    errors: list[str] = []
    fields: dict[str, str] | None = None
    if exit_code != 0:
        errors.append(f"observed exit_code={exit_code}, expected 0")
    if stderr_path.stat().st_size != 0:
        errors.append(f"stderr is nonempty ({stderr_path.stat().st_size} bytes)")
    try:
        fields = parse_result(stdout_path.read_bytes())
    except HarnessError as exc:
        errors.append(str(exc))
    if fields is not None:
        required = {
            "mode": item["mode"],
            "status": "ZERO",
            "nodes": str(item["expected_nodes"]),
            "solution_topologies": "0",
            "frontier": "0",
        }
        for name, expected in required.items():
            actual = fields.get(name)
            if actual != expected:
                errors.append(f"RESULT {name}={actual!r}, expected {expected!r}")
    return fields, errors


def partition_dir_name(key: str) -> str:
    return key.replace("|", "__")


def verify_completed_partition(
    item: dict[str, Any], executable: Path, plan_ref: dict[str, Any], run_dir: Path
) -> dict[str, Any]:
    directory = run_dir / "partitions" / partition_dir_name(item["key"])
    receipt_path = directory / "RECEIPT.json"
    receipt, receipt_ref = verify_receipt_file(receipt_path)
    if receipt.get("schema") != RECEIPT_SCHEMA or receipt.get("status") != "PASS":
        raise HarnessError(f"nonpassing partition receipt: {receipt_path}")
    if receipt.get("key") != item["key"]:
        raise HarnessError(f"partition receipt key mismatch: {receipt_path}")
    if receipt.get("plan_sha256") != plan_ref["sha256"]:
        raise HarnessError(f"partition receipt plan mismatch: {receipt_path}")
    if receipt.get("executable_sha256") != sha256_file(executable):
        raise HarnessError(f"partition receipt executable mismatch: {receipt_path}")
    expected_command = [str(executable.resolve()), *item["argv_tail"]]
    if receipt.get("command") != expected_command:
        raise HarnessError(f"partition receipt command mismatch: {receipt_path}")
    stdout_path = directory / "stdout.txt"
    stderr_path = directory / "stderr.txt"
    for name, path in (("stdout", stdout_path), ("stderr", stderr_path)):
        if not path.is_file() or file_ref(path) != receipt.get(name):
            raise HarnessError(f"partition raw {name} mismatch: {path}")
    fields, errors = validate_observation(
        item, int(receipt.get("exit_code", -999999)), stdout_path, stderr_path
    )
    if errors or fields != receipt.get("result_fields"):
        raise HarnessError(
            f"partition raw observation failed revalidation: {item['key']} errors={errors}"
        )
    return {"key": item["key"], "receipt": receipt_ref, "nodes": item["expected_nodes"]}


def terminate_process(process: subprocess.Popen[bytes]) -> None:
    process.terminate()
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        process.kill()
        process.wait(timeout=5)


def run_one_partition(
    item: dict[str, Any],
    executable: Path,
    plan_ref: dict[str, Any],
    run_dir: Path,
    timeout_seconds: float,
) -> dict[str, Any]:
    directory = run_dir / "partitions" / partition_dir_name(item["key"])
    receipt_path = directory / "RECEIPT.json"
    if receipt_path.exists():
        verified = verify_completed_partition(item, executable, plan_ref, run_dir)
        print(f"RESUME_OK key={item['key']} nodes={item['expected_nodes']}", flush=True)
        return verified
    directory.mkdir(parents=True, exist_ok=True)
    stdout_path = directory / "stdout.txt"
    stderr_path = directory / "stderr.txt"
    if stdout_path.exists() or stderr_path.exists():
        raise HarnessError(
            f"incomplete prior attempt for {item['key']}; preserve it and use a new run dir"
        )
    load_before = enforce_memory_limit(f"launch {item['key']}")
    command = [str(executable.resolve()), *item["argv_tail"]]
    started = utc_now()
    start_clock = time.perf_counter()
    aborted_reason: str | None = None
    peak_memory_load = load_before
    with stdout_path.open("xb") as out, stderr_path.open("xb") as err:
        process = subprocess.Popen(command, stdout=out, stderr=err)
        while process.poll() is None:
            elapsed = time.perf_counter() - start_clock
            load = memory_load_percent()
            if load is not None:
                peak_memory_load = max(peak_memory_load or load, load)
                if load > HARD_MEMORY_LIMIT_PERCENT:
                    aborted_reason = (
                        f"memory guard: {load:.1f}% > {HARD_MEMORY_LIMIT_PERCENT:.1f}%"
                    )
                    terminate_process(process)
                    break
            if timeout_seconds > 0 and elapsed > timeout_seconds:
                aborted_reason = f"timeout after {timeout_seconds} seconds"
                terminate_process(process)
                break
            time.sleep(0.25)
        exit_code = process.wait()
    elapsed = time.perf_counter() - start_clock
    finished = utc_now()
    fields, errors = validate_observation(item, exit_code, stdout_path, stderr_path)
    if aborted_reason:
        errors.insert(0, aborted_reason)
    status = "PASS" if not errors else "FAIL"
    receipt = {
        "schema": RECEIPT_SCHEMA,
        "status": status,
        "key": item["key"],
        "mode": item["mode"],
        "partition": item["partition"],
        "expected_status": item["expected_status"],
        "expected_nodes": item["expected_nodes"],
        "plan_sha256": plan_ref["sha256"],
        "executable_sha256": sha256_file(executable),
        "command": command,
        "started_utc": started,
        "finished_utc": finished,
        "elapsed_seconds": elapsed,
        "memory_load_percent_before": load_before,
        "peak_observed_system_memory_load_percent": peak_memory_load,
        "exit_code": exit_code,
        "stdout": file_ref(stdout_path),
        "stderr": file_ref(stderr_path),
        "result_fields": fields,
        "validation_errors": errors,
    }
    receipt_ref = write_receipt_new(receipt_path, receipt)
    if errors:
        raise HarnessError(f"fresh partition failed: {item['key']} errors={errors}")
    print(
        f"FRESH_OK key={item['key']} nodes={item['expected_nodes']} "
        f"elapsed_seconds={elapsed:.6f} receipt_sha256={receipt_ref['sha256']}",
        flush=True,
    )
    return {"key": item["key"], "receipt": receipt_ref, "nodes": item["expected_nodes"]}


def reject_unknown_partition_directories(run_dir: Path, plan: list[dict[str, Any]]) -> None:
    root = run_dir / "partitions"
    if not root.exists():
        return
    expected_names = {partition_dir_name(item["key"]) for item in plan}
    extras = sorted(path.name for path in root.iterdir() if path.name not in expected_names)
    if extras:
        raise HarnessError(f"unexpected partition artifacts/directories: {extras}")


def selection_receipt_name(keys: list[str]) -> str:
    if keys == [FIXTURE_KEY]:
        return "FIXTURE_RECEIPT.json"
    if keys == expected_keys():
        return "FULL_47_RECEIPT.json"
    digest = sha256_bytes("\n".join(keys).encode("utf-8"))[:16]
    return f"SELECTION_{digest}_RECEIPT.json"


def write_or_verify_aggregate(
    run_dir: Path,
    keys: list[str],
    results: list[dict[str, Any]],
    plan_ref: dict[str, Any],
    build_ref: dict[str, Any],
) -> dict[str, Any]:
    by_key = {result["key"]: result for result in results}
    if set(by_key) != set(keys) or len(results) != len(keys):
        raise HarnessError("aggregate selection is missing, duplicated, or has extra results")
    document = {
        "schema": "config3-a2-aggregate-receipt-v1",
        "status": "PASS",
        "scope": "fixture" if keys == [FIXTURE_KEY] else "full_47" if keys == expected_keys() else "selection",
        "plan": plan_ref,
        "build": build_ref,
        "partition_count": len(keys),
        "node_sum": sum(by_key[key]["nodes"] for key in keys),
        "partition_receipts": [by_key[key] for key in keys],
    }
    path = run_dir / selection_receipt_name(keys)
    if path.exists():
        existing, ref = verify_receipt_file(path)
        if existing != document:
            raise HarnessError(f"existing aggregate receipt differs: {path}")
        return ref
    return write_receipt_new(path, document)


def choose_items(
    plan: list[dict[str, Any]], args: argparse.Namespace
) -> tuple[list[dict[str, Any]], bool]:
    by_key = {item["key"]: item for item in plan}
    if args.command == "fixture":
        return [by_key[FIXTURE_KEY]], False
    if args.all:
        if args.partition:
            raise HarnessError("choose either --all or --partition, not both")
        if args.confirm_full_run != FULL_RUN_CONFIRMATION:
            raise HarnessError(
                f"full run requires --confirm-full-run {FULL_RUN_CONFIRMATION}"
            )
        return plan, True
    if not args.partition:
        raise HarnessError("run requires at least one --partition, or explicit guarded --all")
    if args.confirm_full_run:
        raise HarnessError("--confirm-full-run is valid only with --all")
    unknown = sorted(set(args.partition) - set(by_key))
    if unknown:
        raise HarnessError(f"unknown partition key(s): {unknown}")
    if len(set(args.partition)) != len(args.partition):
        raise HarnessError("duplicate --partition selection")
    ordered = [item for item in plan if item["key"] in set(args.partition)]
    return ordered, False


def execute(args: argparse.Namespace) -> int:
    workspace = Path(args.workspace).resolve() if args.workspace else Path(__file__).resolve().parents[2]
    inputs = resolve_inputs(workspace)
    plan = load_expected_plan(workspace, inputs)
    document = plan_document(workspace, inputs, plan)

    if args.command == "plan":
        print(f"CONFIG3_A2_PLAN_STRICT_OK partitions={len(plan)}")
        for index, item in enumerate(plan, 1):
            print(
                f"{index:02d} key={item['key']} expected_nodes={item['expected_nodes']} "
                f"argv={' '.join(item['argv_tail'])}"
            )
        print(
            "FULL_RUN_GUARD="
            f"--all --confirm-full-run {FULL_RUN_CONFIRMATION}; full run not launched"
        )
        return 0

    if not (1 <= args.jobs <= MAX_JOBS):
        raise HarnessError(f"--jobs must be in 1..{MAX_JOBS}")
    run_dir = Path(args.run_dir).resolve()
    run_dir.mkdir(parents=True, exist_ok=True)
    plan_ref = ensure_plan_file(run_dir, document)
    executable, build_ref = build_solver(run_dir, inputs, plan_ref, args.compiler)
    if args.command == "compile":
        print(
            f"CONFIG3_A2_BUILD_STRICT_OK executable_sha256={sha256_file(executable)} "
            f"build_receipt_sha256={build_ref['sha256']}"
        )
        return 0

    items, is_full = choose_items(plan, args)
    if is_full and len(items) != 47:
        raise HarnessError("internal full-run guard did not expand exactly 47 partitions")
    reject_unknown_partition_directories(run_dir, plan)
    results: list[dict[str, Any]] = []
    errors: list[str] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = {
            pool.submit(
                run_one_partition,
                item,
                executable,
                plan_ref,
                run_dir,
                args.timeout_seconds,
            ): item["key"]
            for item in items
        }
        for future in concurrent.futures.as_completed(futures):
            key = futures[future]
            try:
                results.append(future.result())
            except Exception as exc:  # preserve every independent failure
                errors.append(f"{key}: {exc}")
    if errors:
        raise HarnessError("one or more partitions failed:\n" + "\n".join(errors))
    aggregate_ref = write_or_verify_aggregate(
        run_dir, [item["key"] for item in items], results, plan_ref, build_ref
    )
    if is_full:
        print(
            "CONFIG3_A2_FRESH_47_STRICT_OK "
            f"partitions=47 nodes={sum(item['expected_nodes'] for item in plan)} "
            f"aggregate_receipt_sha256={aggregate_ref['sha256']}"
        )
    elif [item["key"] for item in items] == [FIXTURE_KEY]:
        print(
            "CONFIG3_A2_FIXTURE_STRICT_OK partitions=1 nodes=217 "
            f"aggregate_receipt_sha256={aggregate_ref['sha256']}"
        )
    else:
        print(
            f"CONFIG3_A2_SELECTION_STRICT_OK partitions={len(items)} "
            f"nodes={sum(item['expected_nodes'] for item in items)} "
            f"aggregate_receipt_sha256={aggregate_ref['sha256']}"
        )
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--workspace",
        help="LTG workspace root (default: derived from this script location)",
    )
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("plan", help="validate pins/ledger and print all 47 commands")

    def execution_parser(name: str, help_text: str) -> argparse.ArgumentParser:
        child = subparsers.add_parser(name, help=help_text)
        child.add_argument("--run-dir", required=True, help="new or resumable isolated run directory")
        child.add_argument("--compiler", help="path to g++ (default: g++ from PATH)")
        child.add_argument("--jobs", type=int, default=1, help=f"bounded parallelism, 1..{MAX_JOBS}")
        child.add_argument(
            "--timeout-seconds",
            type=float,
            default=0.0,
            help="per-partition timeout; 0 means uncapped",
        )
        return child

    execution_parser("compile", "compile the pinned source and write a build receipt")
    execution_parser("fixture", f"compile/resume and run only {FIXTURE_KEY}")
    run = execution_parser("run", "run an explicit selection, or the doubly guarded full roster")
    run.add_argument("--partition", action="append", help="exact mode|partition key; repeatable")
    run.add_argument("--all", action="store_true", help="request all 47 partitions")
    run.add_argument("--confirm-full-run", help="required literal confirmation for --all")
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    try:
        return execute(args)
    except (HarnessError, OSError, subprocess.SubprocessError, ValueError) as exc:
        print(f"CONFIG3_A2_HARNESS_FAIL: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
