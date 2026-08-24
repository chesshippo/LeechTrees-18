#!/usr/bin/env python3
"""Fail-closed split replacement for Configuration 3 A2 path_8_14.

This harness never edits the original 47-partition run.  It first performs a
bounded frontier census at ``--branch-path 8,14 --stop-edges 7``.  The census
derives an exact contiguous child roster ``8,14,k`` for ``0 <= k < M``.  A
separately guarded command can then run those children sequentially and write
a replacement receipt whose node accounting is normalized for the three
prefix calls repeated by every child process.

The historical node count is not imposed on individual children.  Completion
requires the source-proved identity

    parent_nodes = sum(child_nodes) - 3 * (M - 1).

The census and child commands retain raw stdout/stderr, an immutable receipt,
and a SHA-256 sidecar for every attempt.  Recorded RAM-guard/timeout attempts
remain in place; a later invocation may create a new numbered attempt.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Callable

import rerun_config3_a2 as base
import run_config3_a2_engines as engines


PLAN_SCHEMA = "config3-a2-path8-14-split-plan-v1"
ATTEMPT_SCHEMA = "config3-a2-path8-14-split-attempt-v1"
REPLACEMENT_SCHEMA = "config3-a2-path8-14-split-replacement-v1"
TARGET_KEY = "a2_separate|path_8_14"
TARGET_MODE = "a2_separate"
TARGET_PARTITION = "path_8_14"
TARGET_EXPECTED_NODES = 42_848_909
EXPECTED_FULL_NODE_SUM = 167_742_832
REPEATED_PREFIX_CALLS = 3
MAX_CHILDREN = 153
START_MEMORY_LIMIT_PERCENT = 90.0
CHILD_CONFIRMATION = "RUN_PATH8_14_SPLIT_CHILDREN"
FRONTIER_KEY = "frontier_8_14_depth7"

FRONTIER_ARGV_TAIL = [
    "--mode",
    TARGET_MODE,
    "--branch-path",
    "8,14",
    "--stop-edges",
    "7",
    *base.COMMON_FLAGS,
]

ATTEMPT_FIELDS = {
    "schema",
    "status",
    "kind",
    "key",
    "split_plan_sha256",
    "engine_sha256",
    "argv_tail",
    "started_utc",
    "finished_utc",
    "elapsed_seconds",
    "memory_load_percent_before",
    "peak_observed_system_memory_load_percent",
    "exit_code",
    "stdout",
    "stderr",
    "result_fields",
    "abort_reason",
    "validation_errors",
}


def fail(message: str) -> None:
    raise base.HarnessError(message)


def strict_json_load(raw: bytes, label: str) -> Any:
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        fail(f"{label} is not strict UTF-8: {exc}")

    def no_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        value: dict[str, Any] = {}
        for key, item in pairs:
            if key in value:
                fail(f"duplicate JSON key in {label}: {key!r}")
            value[key] = item
        return value

    try:
        value = json.loads(text, object_pairs_hook=no_duplicates)
    except json.JSONDecodeError as exc:
        fail(f"invalid JSON in {label}: {exc}")
    if base.canonical_json_bytes(value) != raw:
        fail(f"noncanonical JSON bytes in {label}")
    return value


def local_ref(path: Path, anchor: Path) -> dict[str, Any]:
    resolved = path.resolve(strict=True)
    try:
        relative = resolved.relative_to(anchor.resolve(strict=True)).as_posix()
    except ValueError:
        fail(f"artifact escapes its anchor: {path}")
    return {
        "path": relative,
        "bytes": resolved.stat().st_size,
        "sha256": base.sha256_file(resolved),
    }


def content_ref(path: Path) -> dict[str, Any]:
    return {"bytes": path.stat().st_size, "sha256": base.sha256_file(path)}


def write_document(path: Path, value: dict[str, Any], anchor: Path) -> dict[str, Any]:
    raw = base.canonical_json_bytes(value)
    base.atomic_write_new(path, raw)
    digest = base.sha256_bytes(raw)
    base.atomic_write_new(
        path.with_name(path.name + ".sha256"),
        f"{digest}  {path.name}\n".encode("ascii"),
    )
    return local_ref(path, anchor)


def read_document(path: Path, anchor: Path) -> tuple[dict[str, Any], dict[str, Any]]:
    if not path.is_file():
        fail(f"missing JSON document: {path}")
    if path.is_symlink():
        fail(f"JSON document is a link: {path}")
    sidecar = path.with_name(path.name + ".sha256")
    if not sidecar.is_file() or sidecar.is_symlink():
        fail(f"missing/plain-file SHA-256 sidecar: {sidecar}")
    raw = path.read_bytes()
    digest = base.sha256_bytes(raw)
    expected = f"{digest}  {path.name}\n".encode("ascii")
    if sidecar.read_bytes() != expected:
        fail(f"bad SHA-256 sidecar: {sidecar}")
    value = strict_json_load(raw, str(path))
    if not isinstance(value, dict):
        fail(f"JSON root is not an object: {path}")
    return value, local_ref(path, anchor)


def portable_input_refs(inputs: dict[str, dict[str, Any]]) -> dict[str, dict[str, Any]]:
    return {
        name: {
            "relative_path": item["relative_path"],
            "bytes": item["bytes"],
            "sha256": item["sha256"],
        }
        for name, item in sorted(inputs.items())
    }


def child_argv_tail(index: int) -> list[str]:
    if not (0 <= index < MAX_CHILDREN):
        fail(f"child index outside static 0..{MAX_CHILDREN - 1} bound: {index}")
    return [
        "--mode",
        TARGET_MODE,
        "--branch-path",
        f"8,14,{index}",
        *base.COMMON_FLAGS,
    ]


def load_context(
    workspace: Path, parent_run_dir: Path
) -> tuple[
    dict[str, dict[str, Any]],
    list[dict[str, Any]],
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
]:
    inputs = base.resolve_inputs(workspace)
    partitions = base.load_expected_plan(workspace, inputs)
    by_key = {item["key"]: item for item in partitions}
    target = by_key.get(TARGET_KEY)
    if target is None:
        fail(f"pinned 47-row plan lacks {TARGET_KEY}")
    expected_target_tail = [
        "--mode",
        TARGET_MODE,
        "--branch-path",
        "8,14",
        *base.COMMON_FLAGS,
    ]
    if target != {
        **target,
        "key": TARGET_KEY,
        "mode": TARGET_MODE,
        "partition": TARGET_PARTITION,
        "expected_status": "ZERO",
        "expected_nodes": TARGET_EXPECTED_NODES,
        "argv_tail": expected_target_tail,
    }:
        fail("target row does not have the pinned key/mode/partition/status/nodes/argv")
    if len(partitions) != 47 or sum(item["expected_nodes"] for item in partitions) != EXPECTED_FULL_NODE_SUM:
        fail("pinned parent plan does not have 47 rows and the expected full node sum")

    engine = engines.load_preserved_engine(workspace)
    expected_parent_plan = engines.make_plan_document(
        workspace, inputs, partitions, {"preserved": engine}
    )
    parent_plan_path = parent_run_dir / "PLAN.json"
    parent_plan, parent_plan_ref = read_document(parent_plan_path, parent_run_dir)
    if parent_plan != expected_parent_plan:
        fail("original run PLAN.json differs from the current hash-pinned 47-row plan")
    return inputs, partitions, target, engine, parent_plan_ref


def make_split_plan(
    workspace: Path,
    inputs: dict[str, dict[str, Any]],
    target: dict[str, Any],
    engine: dict[str, Any],
    parent_plan_ref: dict[str, Any],
) -> dict[str, Any]:
    executable = Path(engine["executable"]["path"])
    harness = Path(__file__).resolve()
    return {
        "schema": PLAN_SCHEMA,
        "status": "PINNED",
        "scope": "target-only replacement for a2_separate|path_8_14",
        "parent_plan": {
            "bytes": parent_plan_ref["bytes"],
            "sha256": parent_plan_ref["sha256"],
        },
        "target": target,
        "expected_full_partition_count": 47,
        "expected_full_node_sum": EXPECTED_FULL_NODE_SUM,
        "engine": {
            "name": "preserved",
            "kind": engine["kind"],
            "relative_path": engines.PRESERVED_BINARY_RELATIVE,
            "bytes": executable.stat().st_size,
            "sha256": engines.PRESERVED_BINARY_SHA256,
        },
        "source_inputs": portable_input_refs(inputs),
        "split_harness": {
            "relative_path": harness.relative_to(workspace).as_posix(),
            "bytes": harness.stat().st_size,
            "sha256": base.sha256_file(harness),
        },
        "frontier_census": {
            "argv_tail": FRONTIER_ARGV_TAIL,
            "stop_edges": 7,
            "derived_child_max_depth": 6,
            "child_count_min": 1,
            "child_count_max": MAX_CHILDREN,
            "required_child_roster": "exact contiguous integers 0..M-1",
        },
        "child_command_template": {
            "argv_tail": [
                "--mode",
                TARGET_MODE,
                "--branch-path",
                "8,14,{k}",
                *base.COMMON_FLAGS,
            ],
            "execution": "strictly sequential",
            "confirmation": CHILD_CONFIRMATION,
        },
        "memory_policy": {
            "fresh_launch_must_be_below_percent": START_MEMORY_LIMIT_PERCENT,
            "running_process_killed_above_percent": base.HARD_MEMORY_LIMIT_PERCENT,
        },
        "source_semantics_audit": {
            "source_sha256": inputs["source"]["sha256"],
            "branch_path_parser_lines": "693-700",
            "deterministic_candidate_sort_lines": "536-538",
            "contiguous_branch_counter_lines": "540-552",
            "child_max_before_selector_filter_lines": "553-557",
            "recursion_after_selector_filter_lines": "564-566",
            "nodes_first_in_rec_lines": "411-414",
            "ordinary_separate_branch_path_base_depth_lines": "881-882",
            "seed_depth_four_lines": "900-904",
            "candidate_static_upper_bound": "C(18,2)=153",
        },
        "node_accounting": {
            "repeated_prefix_calls_per_child": REPEATED_PREFIX_CALLS,
            "identity": "parent_nodes=sum(child_nodes)-3*(M-1)",
            "required_normalized_parent_nodes": TARGET_EXPECTED_NODES,
            "census_identity": "census_nodes=3+M",
        },
        "strict_rules": {
            "original_parent_plan_and_46_receipts_immutable": True,
            "frontier_exit_zero_and_stderr_empty": True,
            "frontier_single_result_status_frontier": True,
            "children_exit_zero_and_stderr_empty": True,
            "children_single_result_status_zero": True,
            "children_exact_contiguous_roster_no_extras": True,
            "child_execution_sequential": True,
            "raw_bytes_reparsed_on_every_resume": True,
            "node_identity_required_before_replacement_marker": True,
        },
    }


def ensure_split_plan(run_dir: Path, document: dict[str, Any]) -> dict[str, Any]:
    path = run_dir / "SPLIT_PLAN.json"
    if path.exists():
        existing, ref = read_document(path, run_dir)
        if existing != document:
            fail("existing split plan differs from current hash-pinned split plan")
        return ref
    run_dir.mkdir(parents=True, exist_ok=True)
    return write_document(path, document, run_dir)


def parse_nonnegative(value: str | None, field: str) -> int:
    if value is None or re.fullmatch(r"0|[1-9][0-9]*", value) is None:
        fail(f"RESULT {field} is not a canonical nonnegative integer: {value!r}")
    return int(value)


def parse_count_map(value: str | None, field: str) -> dict[int, int]:
    if value is None or not value.endswith(","):
        fail(f"RESULT {field} is missing or lacks its canonical trailing comma")
    result: dict[int, int] = {}
    for item in value[:-1].split(",") if value[:-1] else []:
        match = re.fullmatch(r"(0|[1-9][0-9]*):(0|[1-9][0-9]*)", item)
        if match is None:
            fail(f"malformed RESULT {field} entry: {item!r}")
        key, count = int(match.group(1)), int(match.group(2))
        if key in result:
            fail(f"duplicate RESULT {field} key: {key}")
        result[key] = count
    return result


def validate_frontier_fields(fields: dict[str, str]) -> int:
    required = {
        "mode": TARGET_MODE,
        "status": "FRONTIER",
        "solution_topologies": "0",
        "root_valid": "9",
    }
    for name, expected in required.items():
        if fields.get(name) != expected:
            fail(f"frontier RESULT {name}={fields.get(name)!r}, expected {expected!r}")
    child_max = parse_count_map(fields.get("child_max"), "child_max")
    if set(child_max) != {4, 5, 6} or child_max[4] != 9 or child_max[5] != 15:
        fail(f"frontier child_max does not have exact prefix shape: {child_max}")
    child_count = child_max[6]
    if not (1 <= child_count <= MAX_CHILDREN):
        fail(f"derived child count outside 1..{MAX_CHILDREN}: {child_count}")
    depth = parse_count_map(fields.get("depth"), "depth")
    expected_depth = {4: 1, 5: 1, 6: 1, 7: child_count}
    if depth != expected_depth:
        fail(f"frontier depth map mismatch: expected={expected_depth} actual={depth}")
    nodes = parse_nonnegative(fields.get("nodes"), "nodes")
    if nodes != REPEATED_PREFIX_CALLS + child_count:
        fail(f"frontier nodes={nodes}, expected 3+M={3 + child_count}")
    frontier = parse_nonnegative(fields.get("frontier"), "frontier")
    if frontier > child_count:
        fail(f"frontier accepted count exceeds M: frontier={frontier} M={child_count}")
    return child_count


def validate_child_fields(fields: dict[str, str], child_count: int) -> int:
    required = {
        "mode": TARGET_MODE,
        "status": "ZERO",
        "solution_topologies": "0",
        "root_valid": "9",
        "frontier": "0",
    }
    for name, expected in required.items():
        if fields.get(name) != expected:
            fail(f"child RESULT {name}={fields.get(name)!r}, expected {expected!r}")
    child_max = parse_count_map(fields.get("child_max"), "child_max")
    for depth, expected in ((4, 9), (5, 15), (6, child_count)):
        if child_max.get(depth) != expected:
            fail(
                f"child RESULT child_max[{depth}]={child_max.get(depth)!r}, "
                f"expected {expected}"
            )
    depth_nodes = parse_count_map(fields.get("depth"), "depth")
    for depth in (4, 5, 6, 7):
        if depth_nodes.get(depth) != 1:
            fail(f"child RESULT depth[{depth}]={depth_nodes.get(depth)!r}, expected 1")
    nodes = parse_nonnegative(fields.get("nodes"), "nodes")
    if nodes < 4:
        fail(f"child RESULT nodes={nodes}, expected at least four rec calls")
    return nodes


def observation(
    kind: str,
    exit_code: int,
    stdout_raw: bytes,
    stderr_raw: bytes,
    child_count: int | None,
) -> tuple[dict[str, str] | None, int | None, list[str]]:
    errors: list[str] = []
    fields: dict[str, str] | None = None
    metric: int | None = None
    if exit_code != 0:
        errors.append(f"observed exit_code={exit_code}, expected 0")
    if stderr_raw:
        errors.append(f"stderr is nonempty ({len(stderr_raw)} bytes)")
    try:
        fields = base.parse_result(stdout_raw)
        if kind == "frontier":
            metric = validate_frontier_fields(fields)
        elif kind == "child":
            if child_count is None:
                fail("internal child validation lacks census-derived M")
            metric = validate_child_fields(fields, child_count)
        else:
            fail(f"unknown observation kind: {kind}")
    except base.HarnessError as exc:
        errors.append(str(exc))
    return fields, metric, errors


def attempt_container(run_dir: Path, kind: str, index: int | None = None) -> Path:
    if kind == "frontier":
        return run_dir / "frontier"
    if index is None:
        fail("internal child attempt lacks an index")
    return run_dir / "children" / f"k_{index:03d}"


def numbered_attempts(container: Path) -> list[Path]:
    if not container.exists():
        return []
    if not container.is_dir() or container.is_symlink():
        fail(f"attempt container is not a plain directory: {container}")
    attempts: list[tuple[int, Path]] = []
    for entry in container.iterdir():
        match = re.fullmatch(r"attempt_([0-9]{4})", entry.name)
        if match is None or not entry.is_dir() or entry.is_symlink():
            fail(f"unexpected entry in attempt container: {entry}")
        attempts.append((int(match.group(1)), entry))
    attempts.sort()
    if [number for number, _ in attempts] != list(range(1, len(attempts) + 1)):
        fail(f"attempt numbers are not exact contiguous 1..N in {container}")
    return [path for _, path in attempts]


def verify_attempt(
    attempt: Path,
    run_dir: Path,
    kind: str,
    key: str,
    argv_tail: list[str],
    split_plan_sha256: str,
    engine_sha256: str,
    child_count: int | None,
) -> tuple[dict[str, Any], dict[str, Any], int | None]:
    expected_names = {"RECEIPT.json", "RECEIPT.json.sha256", "stdout.txt", "stderr.txt"}
    actual_names = {entry.name for entry in attempt.iterdir()}
    if actual_names != expected_names:
        fail(f"attempt tree mismatch in {attempt}: expected={sorted(expected_names)} actual={sorted(actual_names)}")
    receipt, receipt_ref = read_document(attempt / "RECEIPT.json", run_dir)
    if set(receipt) != ATTEMPT_FIELDS:
        fail(f"attempt receipt field set mismatch in {attempt}")
    required = {
        "schema": ATTEMPT_SCHEMA,
        "kind": kind,
        "key": key,
        "split_plan_sha256": split_plan_sha256,
        "engine_sha256": engine_sha256,
        "argv_tail": argv_tail,
    }
    for name, expected in required.items():
        if receipt.get(name) != expected:
            fail(f"attempt receipt {name} mismatch in {attempt}")
    for name in ("stdout", "stderr"):
        raw_path = attempt / f"{name}.txt"
        if not raw_path.is_file() or raw_path.is_symlink():
            fail(f"missing/plain raw {name}: {raw_path}")
        expected_ref = {
            "path": f"{name}.txt",
            "bytes": raw_path.stat().st_size,
            "sha256": base.sha256_file(raw_path),
        }
        if receipt.get(name) != expected_ref:
            fail(f"raw {name} reference mismatch in {attempt}")
    exit_code = receipt.get("exit_code")
    if not isinstance(exit_code, int) or isinstance(exit_code, bool):
        fail(f"attempt exit_code is not an integer in {attempt}")
    fields, metric, errors = observation(
        kind,
        exit_code,
        (attempt / "stdout.txt").read_bytes(),
        (attempt / "stderr.txt").read_bytes(),
        child_count,
    )
    abort_reason = receipt.get("abort_reason")
    if abort_reason is not None:
        if not isinstance(abort_reason, str) or not (
            abort_reason.startswith("memory guard:") or abort_reason.startswith("timeout after ")
        ):
            fail(f"attempt has a noncanonical abort reason in {attempt}")
        errors.insert(0, abort_reason)
    expected_status = "PASS" if not errors else "FAIL"
    if receipt.get("status") != expected_status:
        fail(f"attempt status mismatch in {attempt}: expected {expected_status}")
    if receipt.get("result_fields") != fields or receipt.get("validation_errors") != errors:
        fail(f"attempt observation fields/errors mismatch in {attempt}")
    for name in ("elapsed_seconds", "memory_load_percent_before", "peak_observed_system_memory_load_percent"):
        value = receipt.get(name)
        if value is not None and (not isinstance(value, (int, float)) or isinstance(value, bool) or value < 0):
            fail(f"attempt receipt has invalid numeric {name} in {attempt}")
    return receipt, receipt_ref, metric


def find_passing_attempt(
    run_dir: Path,
    kind: str,
    key: str,
    argv_tail: list[str],
    split_plan_sha256: str,
    engine_sha256: str,
    child_count: int | None,
) -> tuple[dict[str, Any], dict[str, Any], int] | None:
    container = attempt_container(
        run_dir, kind, None if kind == "frontier" else int(key.rsplit("_", 1)[1])
    )
    passing: tuple[dict[str, Any], dict[str, Any], int] | None = None
    attempts = numbered_attempts(container)
    for position, attempt in enumerate(attempts):
        receipt, receipt_ref, metric = verify_attempt(
            attempt,
            run_dir,
            kind,
            key,
            argv_tail,
            split_plan_sha256,
            engine_sha256,
            child_count,
        )
        if receipt["status"] == "PASS":
            if passing is not None or position != len(attempts) - 1 or metric is None:
                fail(f"passing attempt is duplicated or not final in {container}")
            passing = (receipt, receipt_ref, metric)
        elif receipt.get("abort_reason") is None:
            fail(f"nonretryable failed attempt blocks resume: {attempt}")
    return passing


def enforce_start_gate(context: str) -> float | None:
    load = base.memory_load_percent()
    if load is not None and load >= START_MEMORY_LIMIT_PERCENT:
        fail(
            f"fresh start gate closed before {context}: {load:.1f}% is not below "
            f"{START_MEMORY_LIMIT_PERCENT:.1f}%"
        )
    return load


def run_attempt(
    run_dir: Path,
    executable: Path,
    kind: str,
    key: str,
    argv_tail: list[str],
    split_plan_sha256: str,
    child_count: int | None,
    timeout_seconds: float,
) -> tuple[dict[str, Any], dict[str, Any], int]:
    existing = find_passing_attempt(
        run_dir,
        kind,
        key,
        argv_tail,
        split_plan_sha256,
        engines.PRESERVED_BINARY_SHA256,
        child_count,
    )
    if existing is not None:
        return existing
    container = attempt_container(
        run_dir, kind, None if kind == "frontier" else int(key.rsplit("_", 1)[1])
    )
    attempt_number = len(numbered_attempts(container)) + 1
    load_before = enforce_start_gate(f"{kind} {key}")
    attempt = container / f"attempt_{attempt_number:04d}"
    attempt.mkdir(parents=True, exist_ok=False)
    stdout_path = attempt / "stdout.txt"
    stderr_path = attempt / "stderr.txt"
    command = [str(executable.resolve()), *argv_tail]
    started = base.utc_now()
    start_clock = time.perf_counter()
    peak_load = load_before
    abort_reason: str | None = None
    with stdout_path.open("xb") as out, stderr_path.open("xb") as err:
        process = subprocess.Popen(command, stdout=out, stderr=err)
        while process.poll() is None:
            elapsed = time.perf_counter() - start_clock
            load = base.memory_load_percent()
            if load is not None:
                peak_load = max(peak_load or load, load)
                if load > base.HARD_MEMORY_LIMIT_PERCENT:
                    abort_reason = (
                        f"memory guard: {load:.1f}% > "
                        f"{base.HARD_MEMORY_LIMIT_PERCENT:.1f}%"
                    )
                    base.terminate_process(process)
                    break
            if timeout_seconds > 0 and elapsed > timeout_seconds:
                abort_reason = f"timeout after {timeout_seconds} seconds"
                base.terminate_process(process)
                break
            time.sleep(0.25)
        exit_code = process.wait()
    elapsed = time.perf_counter() - start_clock
    fields, metric, errors = observation(
        kind,
        exit_code,
        stdout_path.read_bytes(),
        stderr_path.read_bytes(),
        child_count,
    )
    if abort_reason is not None:
        errors.insert(0, abort_reason)
    document = {
        "schema": ATTEMPT_SCHEMA,
        "status": "PASS" if not errors else "FAIL",
        "kind": kind,
        "key": key,
        "split_plan_sha256": split_plan_sha256,
        "engine_sha256": engines.PRESERVED_BINARY_SHA256,
        "argv_tail": argv_tail,
        "started_utc": started,
        "finished_utc": base.utc_now(),
        "elapsed_seconds": elapsed,
        "memory_load_percent_before": load_before,
        "peak_observed_system_memory_load_percent": peak_load,
        "exit_code": exit_code,
        "stdout": {
            "path": "stdout.txt",
            "bytes": stdout_path.stat().st_size,
            "sha256": base.sha256_file(stdout_path),
        },
        "stderr": {
            "path": "stderr.txt",
            "bytes": stderr_path.stat().st_size,
            "sha256": base.sha256_file(stderr_path),
        },
        "result_fields": fields,
        "abort_reason": abort_reason,
        "validation_errors": errors,
    }
    receipt_ref = write_document(attempt / "RECEIPT.json", document, run_dir)
    if errors or metric is None:
        fail(f"{kind} attempt failed and was preserved at {attempt}: {errors}")
    return document, receipt_ref, metric


def verify_frontier(
    run_dir: Path, split_plan_ref: dict[str, Any]
) -> tuple[dict[str, Any], dict[str, Any], int]:
    result = find_passing_attempt(
        run_dir,
        "frontier",
        FRONTIER_KEY,
        FRONTIER_ARGV_TAIL,
        split_plan_ref["sha256"],
        engines.PRESERVED_BINARY_SHA256,
        None,
    )
    if result is None:
        fail("no passing frontier census attempt")
    return result


def verify_parent_46(
    parent_run_dir: Path,
    partitions: list[dict[str, Any]],
    engine: dict[str, Any],
    parent_plan_ref: dict[str, Any],
) -> list[dict[str, Any]]:
    engines.reject_extras(parent_run_dir, partitions, {"preserved"})
    full_receipt = parent_run_dir / "FULL_47_RECEIPT.json"
    if full_receipt.exists():
        fail("direct FULL_47_RECEIPT exists; split replacement would be ambiguous")
    verified: list[dict[str, Any]] = []
    for item in partitions:
        if item["key"] == TARGET_KEY:
            continue
        verified.append(
            engines.verify_engine_partition(
                item, engine, parent_plan_ref, parent_run_dir
            )
        )
    if len(verified) != 46:
        fail("parent verification did not produce exactly 46 direct receipts")
    return verified


def exact_child_containers(run_dir: Path, child_count: int) -> None:
    children = run_dir / "children"
    if not children.is_dir() or children.is_symlink():
        fail("missing/plain children directory")
    expected = {f"k_{index:03d}" for index in range(child_count)}
    actual = {entry.name for entry in children.iterdir()}
    if actual != expected:
        fail(f"child directory roster mismatch: missing={sorted(expected - actual)} extras={sorted(actual - expected)}")


def verify_all_children(
    run_dir: Path,
    split_plan_ref: dict[str, Any],
    child_count: int,
) -> list[dict[str, Any]]:
    exact_child_containers(run_dir, child_count)
    results: list[dict[str, Any]] = []
    for index in range(child_count):
        key = f"child_{index}"
        passing = find_passing_attempt(
            run_dir,
            "child",
            key,
            child_argv_tail(index),
            split_plan_ref["sha256"],
            engines.PRESERVED_BINARY_SHA256,
            child_count,
        )
        if passing is None:
            fail(f"no passing child attempt for k={index}")
        receipt, receipt_ref, nodes = passing
        results.append(
            {
                "index": index,
                "key": key,
                "argv_tail": child_argv_tail(index),
                "nodes": nodes,
                "result_fields": receipt["result_fields"],
                "receipt": receipt_ref,
            }
        )
    return results


def replacement_document(
    split_plan_ref: dict[str, Any],
    parent_plan_ref: dict[str, Any],
    frontier: tuple[dict[str, Any], dict[str, Any], int],
    children: list[dict[str, Any]],
    parent_46: list[dict[str, Any]],
) -> dict[str, Any]:
    frontier_receipt, frontier_ref, child_count = frontier
    if [child["index"] for child in children] != list(range(child_count)):
        fail("replacement child roster is not exact ordered 0..M-1")
    child_reported_node_sum = sum(child["nodes"] for child in children)
    normalization_subtraction = REPEATED_PREFIX_CALLS * (child_count - 1)
    normalized_parent_nodes = child_reported_node_sum - normalization_subtraction
    if normalized_parent_nodes != TARGET_EXPECTED_NODES:
        fail(
            "split node identity failed: "
            f"sum={child_reported_node_sum} subtraction={normalization_subtraction} "
            f"normalized={normalized_parent_nodes} expected={TARGET_EXPECTED_NODES}"
        )
    direct_node_sum = sum(item["nodes"] for item in parent_46)
    if direct_node_sum + normalized_parent_nodes != EXPECTED_FULL_NODE_SUM:
        fail("46 direct nodes plus normalized replacement do not equal full node sum")
    return {
        "schema": REPLACEMENT_SCHEMA,
        "status": "PASS",
        "scope": "46 direct parent receipts plus exact split replacement for path_8_14",
        "split_plan": split_plan_ref,
        "parent_plan": {
            "bytes": parent_plan_ref["bytes"],
            "sha256": parent_plan_ref["sha256"],
        },
        "engine_sha256": engines.PRESERVED_BINARY_SHA256,
        "logical_partition_count": 47,
        "logical_node_sum": EXPECTED_FULL_NODE_SUM,
        "direct_partition_count": 46,
        "direct_node_sum": direct_node_sum,
        "direct_partition_receipts": parent_46,
        "replacement": {
            "logical_key": TARGET_KEY,
            "historical_expected_nodes": TARGET_EXPECTED_NODES,
            "frontier_receipt": frontier_ref,
            "frontier_result_fields": frontier_receipt["result_fields"],
            "child_count": child_count,
            "child_indices": list(range(child_count)),
            "child_receipts": children,
            "child_reported_node_sum": child_reported_node_sum,
            "repeated_prefix_calls_per_child": REPEATED_PREFIX_CALLS,
            "normalization_subtraction": normalization_subtraction,
            "normalized_parent_nodes": normalized_parent_nodes,
            "node_identity": "parent_nodes=sum(child_nodes)-3*(M-1)",
        },
        "physical_zero_process_count": 46 + child_count,
        "frontier_census_process_count": 1,
    }


def write_or_verify_replacement(
    run_dir: Path, document: dict[str, Any]
) -> dict[str, Any]:
    path = run_dir / "SPLIT_REPLACEMENT_RECEIPT.json"
    if path.exists():
        existing, ref = read_document(path, run_dir)
        if existing != document:
            fail("existing split replacement receipt differs from strict recomputation")
        return ref
    return write_document(path, document, run_dir)


def execute(args: argparse.Namespace) -> int:
    workspace = (
        Path(args.workspace).resolve()
        if args.workspace
        else Path(__file__).resolve().parents[2]
    )
    parent_run_dir = Path(args.parent_run_dir).resolve()
    inputs, partitions, target, engine, parent_plan_ref = load_context(
        workspace, parent_run_dir
    )
    split_plan = make_split_plan(
        workspace, inputs, target, engine, parent_plan_ref
    )

    if args.command == "plan":
        raw = base.canonical_json_bytes(split_plan)
        print(
            "CONFIG3_A2_PATH8_14_SPLIT_PLAN_STRICT_OK "
            f"target={TARGET_KEY} parent_nodes={TARGET_EXPECTED_NODES} "
            f"plan_sha256={base.sha256_bytes(raw)}"
        )
        print("FRONTIER_ARGV_TAIL=" + json.dumps(FRONTIER_ARGV_TAIL, separators=(",", ":")))
        print(
            "CHILD_RUN_HELD="
            f"--confirm-child-run {CHILD_CONFIRMATION}; no child launched"
        )
        return 0

    run_dir = Path(args.run_dir).resolve()
    if run_dir == parent_run_dir or parent_run_dir in run_dir.parents:
        fail("split run directory must be isolated from the immutable parent run")
    split_plan_ref = ensure_split_plan(run_dir, split_plan)
    executable = Path(engine["executable"]["path"])

    if args.command == "census":
        receipt, receipt_ref, child_count = run_attempt(
            run_dir,
            executable,
            "frontier",
            FRONTIER_KEY,
            FRONTIER_ARGV_TAIL,
            split_plan_ref["sha256"],
            None,
            args.timeout_seconds,
        )
        print(
            "CONFIG3_A2_PATH8_14_FRONTIER_STRICT_OK "
            f"M={child_count} nodes={receipt['result_fields']['nodes']} "
            f"frontier={receipt['result_fields']['frontier']} "
            f"receipt_sha256={receipt_ref['sha256']}"
        )
        return 0

    frontier = verify_frontier(run_dir, split_plan_ref)
    child_count = frontier[2]

    if args.command == "child":
        if not (0 <= args.index < child_count):
            fail(f"--index must be in census-derived range 0..{child_count - 1}")
        receipt, receipt_ref, nodes = run_attempt(
            run_dir,
            executable,
            "child",
            f"child_{args.index}",
            child_argv_tail(args.index),
            split_plan_ref["sha256"],
            child_count,
            args.timeout_seconds,
        )
        print(
            "CONFIG3_A2_PATH8_14_CHILD_STRICT_OK "
            f"k={args.index} M={child_count} nodes={nodes} "
            f"receipt_sha256={receipt_ref['sha256']}"
        )
        return 0

    if args.command == "children":
        if args.confirm_child_run != CHILD_CONFIRMATION:
            fail(f"all-child run requires --confirm-child-run {CHILD_CONFIRMATION}")
        for index in range(child_count):
            _, receipt_ref, nodes = run_attempt(
                run_dir,
                executable,
                "child",
                f"child_{index}",
                child_argv_tail(index),
                split_plan_ref["sha256"],
                child_count,
                args.timeout_seconds,
            )
            print(
                f"SPLIT_CHILD_OK k={index} M={child_count} nodes={nodes} "
                f"receipt_sha256={receipt_ref['sha256']}",
                flush=True,
            )
        print(f"CONFIG3_A2_PATH8_14_ALL_CHILDREN_STRICT_OK M={child_count}")
        return 0

    children = verify_all_children(run_dir, split_plan_ref, child_count)
    parent_46 = verify_parent_46(
        parent_run_dir, partitions, engine, parent_plan_ref
    )
    document = replacement_document(
        split_plan_ref, parent_plan_ref, frontier, children, parent_46
    )
    replacement_path = run_dir / "SPLIT_REPLACEMENT_RECEIPT.json"
    if args.command == "verify":
        existing, receipt_ref = read_document(replacement_path, run_dir)
        if existing != document:
            fail("split replacement receipt differs from strict recomputation")
    else:
        receipt_ref = write_or_verify_replacement(run_dir, document)
    print(
        "CONFIG3_A2_PATH8_14_SPLIT_REPLACEMENT_STRICT_OK "
        f"M={child_count} child_reported_nodes={document['replacement']['child_reported_node_sum']} "
        f"normalized_parent_nodes={TARGET_EXPECTED_NODES} logical_full_nodes={EXPECTED_FULL_NODE_SUM} "
        f"receipt_sha256={receipt_ref['sha256']}"
    )
    return 0


def add_run_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--run-dir", required=True)
    parser.add_argument(
        "--timeout-seconds",
        type=float,
        default=0.0,
        help="per-process timeout; 0 means uncapped",
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace")
    parser.add_argument(
        "--parent-run-dir",
        required=True,
        help="immutable original full_preserved_v1 run directory",
    )
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("plan", help="static pin/plan audit; launches no solver")
    census = subparsers.add_parser("census", help="run/resume only the bounded fan-out census")
    add_run_args(census)
    child = subparsers.add_parser("child", help="run/resume one census-derived child")
    add_run_args(child)
    child.add_argument("--index", type=int, required=True)
    children = subparsers.add_parser("children", help="run/resume every child sequentially")
    add_run_args(children)
    children.add_argument("--confirm-child-run")
    finalize = subparsers.add_parser("finalize", help="verify all evidence and write replacement receipt")
    add_run_args(finalize)
    verify = subparsers.add_parser("verify", help="read-only strict replacement verification")
    add_run_args(verify)
    return parser


def main() -> int:
    args = build_parser().parse_args()
    try:
        if getattr(args, "timeout_seconds", 0.0) < 0:
            fail("--timeout-seconds must be nonnegative")
        return execute(args)
    except (base.HarnessError, OSError, subprocess.SubprocessError, ValueError) as exc:
        print(f"CONFIG3_A2_PATH8_14_SPLIT_FAIL: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
