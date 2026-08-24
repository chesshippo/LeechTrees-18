#!/usr/bin/env python3
"""Selectable/differential engine runner for the Configuration 3 / A2 repair.

This wrapper preserves ``rerun_config3_a2.py`` and its first fresh-build
fixture byte-for-byte.  It adds the historical production executable as a
separately pinned engine and can compare production and fresh-build RESULT
fields on identical selectors.  The full 47-partition path remains doubly
guarded and is never selected by default.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

import rerun_config3_a2 as base


SCHEMA = "config3-a2-multi-engine-run-v1"
RECEIPT_SCHEMA = "config3-a2-engine-partition-receipt-v1"
AGGREGATE_SCHEMA = "config3-a2-engine-aggregate-receipt-v1"
DIFFERENTIAL_SCHEMA = "config3-a2-differential-receipt-v1"
PRESERVED_BINARY_RELATIVE = (
    "computation/evidence/production/"
    "prior_three_configurations/work/a2_solver/a2_topology_free_search_multicover.exe"
)
PRESERVED_BINARY_SHA256 = (
    "65bbaa57e5b462663b3656bc77499cc5956053f4137878c21072c99a327483f3"
)
DIFFERENTIAL_KEYS = [
    "a2_separate|path_7_4",  # 217 nodes
    "a2_separate|path_6_0",  # 199,150 nodes
]


def load_preserved_engine(workspace: Path) -> dict[str, Any]:
    executable = workspace / PRESERVED_BINARY_RELATIVE
    if not executable.is_file():
        raise base.HarnessError(f"missing preserved production executable: {executable}")
    ref = base.file_ref(executable)
    if ref["sha256"] != PRESERVED_BINARY_SHA256:
        raise base.HarnessError(
            "preserved production executable hash mismatch: "
            f"expected={PRESERVED_BINARY_SHA256} actual={ref['sha256']}"
        )
    return {
        "name": "preserved",
        "kind": "hash-pinned-historical-production-binary",
        "executable": ref,
        "source_claim": "historical package binding; not a reproducible-build proof",
    }


def load_fresh_engine(
    fresh_build_run_dir: Path,
    expected_inputs: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    receipt_path = fresh_build_run_dir / "build" / "BUILD_RECEIPT.json"
    receipt, receipt_ref = base.verify_receipt_file(receipt_path)
    if receipt.get("schema") != base.BUILD_SCHEMA or receipt.get("status") != "PASS":
        raise base.HarnessError(f"fresh build receipt is not passing: {receipt_path}")
    if receipt.get("inputs") != expected_inputs:
        raise base.HarnessError("fresh build receipt does not bind the current pinned inputs")
    historical_executable_ref = receipt.get("executable")
    if not isinstance(historical_executable_ref, dict) or "path" not in historical_executable_ref:
        raise base.HarnessError("fresh build receipt has no executable reference")
    # Fixture evidence may be relocated as one intact tree under .run.  Bind
    # the relocated executable by bytes/hash while retaining the receipt's
    # original absolute path as explicit historical metadata.
    executable = fresh_build_run_dir / "build" / Path(historical_executable_ref["path"]).name
    if not executable.is_file():
        raise base.HarnessError(f"fresh executable is absent after relocation: {executable}")
    executable_ref = base.file_ref(executable)
    if (
        executable_ref["bytes"] != historical_executable_ref.get("bytes")
        or executable_ref["sha256"] != historical_executable_ref.get("sha256")
    ):
        raise base.HarnessError("relocated fresh executable bytes/hash differ from build receipt")
    return {
        "name": "fresh",
        "kind": "fresh-GCC-build-from-four-hash-pinned-source-inputs",
        "executable": executable_ref,
        "historical_executable_ref_before_packaging_move": historical_executable_ref,
        "build_receipt": receipt_ref,
        "compiler": receipt.get("compiler"),
        "source_inputs": expected_inputs,
    }


def make_plan_document(
    workspace: Path,
    inputs: dict[str, dict[str, Any]],
    partitions: list[dict[str, Any]],
    engines: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    return {
        "schema": SCHEMA,
        "workspace": str(workspace.resolve()),
        "wrapper": base.file_ref(Path(__file__).resolve()),
        "base_harness": base.file_ref(Path(base.__file__).resolve()),
        "inputs": inputs,
        "engines": engines,
        "common_flags": base.COMMON_FLAGS,
        "partition_count": 47,
        "partitions": partitions,
        "differential_keys": DIFFERENTIAL_KEYS,
        "full_run_confirmation": base.FULL_RUN_CONFIRMATION,
        "strict_rules": {
            "exact_partition_set_no_extras": True,
            "fresh_observed_exit_zero_required": True,
            "stderr_must_be_empty": True,
            "single_result_line_required": True,
            "status_zero_required": True,
            "exact_historical_node_count_required": True,
            "resume_revalidates_raw_bytes": True,
        },
    }


def engine_executable(engine: dict[str, Any]) -> Path:
    executable = Path(engine["executable"]["path"])
    if base.file_ref(executable) != engine["executable"]:
        raise base.HarnessError(f"engine executable changed: {engine['name']}")
    return executable


def artifact_directory(run_dir: Path, engine_name: str, key: str) -> Path:
    return run_dir / "partitions" / engine_name / base.partition_dir_name(key)


def verify_engine_partition(
    item: dict[str, Any],
    engine: dict[str, Any],
    plan_ref: dict[str, Any],
    run_dir: Path,
) -> dict[str, Any]:
    executable = engine_executable(engine)
    directory = artifact_directory(run_dir, engine["name"], item["key"])
    receipt_path = directory / "RECEIPT.json"
    receipt, receipt_ref = base.verify_receipt_file(receipt_path)
    expected_command = [str(executable.resolve()), *item["argv_tail"]]
    required = {
        "schema": RECEIPT_SCHEMA,
        "status": "PASS",
        "engine": engine["name"],
        "key": item["key"],
        "plan_sha256": plan_ref["sha256"],
        "command": expected_command,
        "executable": engine["executable"],
        "expected_nodes": item["expected_nodes"],
    }
    for name, expected in required.items():
        if receipt.get(name) != expected:
            raise base.HarnessError(
                f"engine receipt field mismatch {engine['name']} {item['key']} "
                f"field={name}"
            )
    stdout_path = directory / "stdout.txt"
    stderr_path = directory / "stderr.txt"
    for name, path in (("stdout", stdout_path), ("stderr", stderr_path)):
        if not path.is_file() or base.file_ref(path) != receipt.get(name):
            raise base.HarnessError(
                f"raw {name} mismatch for {engine['name']} {item['key']}"
            )
    fields, errors = base.validate_observation(
        item, int(receipt.get("exit_code", -999999)), stdout_path, stderr_path
    )
    if errors or fields != receipt.get("result_fields"):
        raise base.HarnessError(
            f"raw revalidation failed for {engine['name']} {item['key']}: {errors}"
        )
    return {
        "engine": engine["name"],
        "key": item["key"],
        "nodes": item["expected_nodes"],
        "result_fields": fields,
        "stdout": receipt["stdout"],
        "stderr": receipt["stderr"],
        "exit_code": receipt["exit_code"],
        "elapsed_seconds": receipt["elapsed_seconds"],
        "receipt": receipt_ref,
    }


def run_engine_partition(
    item: dict[str, Any],
    engine: dict[str, Any],
    plan_ref: dict[str, Any],
    run_dir: Path,
    timeout_seconds: float,
) -> dict[str, Any]:
    directory = artifact_directory(run_dir, engine["name"], item["key"])
    receipt_path = directory / "RECEIPT.json"
    if receipt_path.exists():
        result = verify_engine_partition(item, engine, plan_ref, run_dir)
        print(
            f"RESUME_OK engine={engine['name']} key={item['key']} "
            f"nodes={item['expected_nodes']}",
            flush=True,
        )
        return result
    directory.mkdir(parents=True, exist_ok=True)
    stdout_path = directory / "stdout.txt"
    stderr_path = directory / "stderr.txt"
    if stdout_path.exists() or stderr_path.exists():
        raise base.HarnessError(
            f"incomplete attempt for {engine['name']} {item['key']}; use a new run dir"
        )
    executable = engine_executable(engine)
    load_before = base.enforce_memory_limit(
        f"launch {engine['name']} {item['key']}"
    )
    command = [str(executable.resolve()), *item["argv_tail"]]
    started = base.utc_now()
    start_clock = time.perf_counter()
    peak_memory_load = load_before
    abort_reason: str | None = None
    with stdout_path.open("xb") as stdout_stream, stderr_path.open("xb") as stderr_stream:
        process = subprocess.Popen(command, stdout=stdout_stream, stderr=stderr_stream)
        while process.poll() is None:
            elapsed = time.perf_counter() - start_clock
            load = base.memory_load_percent()
            if load is not None:
                peak_memory_load = max(peak_memory_load or load, load)
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
    fields, errors = base.validate_observation(
        item, exit_code, stdout_path, stderr_path
    )
    if abort_reason:
        errors.insert(0, abort_reason)
    receipt = {
        "schema": RECEIPT_SCHEMA,
        "status": "PASS" if not errors else "FAIL",
        "engine": engine["name"],
        "engine_kind": engine["kind"],
        "key": item["key"],
        "mode": item["mode"],
        "partition": item["partition"],
        "expected_nodes": item["expected_nodes"],
        "expected_status": "ZERO",
        "plan_sha256": plan_ref["sha256"],
        "executable": engine["executable"],
        "command": command,
        "started_utc": started,
        "finished_utc": base.utc_now(),
        "elapsed_seconds": elapsed,
        "memory_load_percent_before": load_before,
        "peak_observed_system_memory_load_percent": peak_memory_load,
        "exit_code": exit_code,
        "stdout": base.file_ref(stdout_path),
        "stderr": base.file_ref(stderr_path),
        "result_fields": fields,
        "validation_errors": errors,
    }
    receipt_ref = base.write_receipt_new(receipt_path, receipt)
    if errors:
        raise base.HarnessError(
            f"engine partition failed {engine['name']} {item['key']}: {errors}"
        )
    print(
        f"ENGINE_FRESH_OK engine={engine['name']} key={item['key']} "
        f"nodes={item['expected_nodes']} elapsed_seconds={elapsed:.6f} "
        f"receipt_sha256={receipt_ref['sha256']}",
        flush=True,
    )
    return {
        "engine": engine["name"],
        "key": item["key"],
        "nodes": item["expected_nodes"],
        "result_fields": fields,
        "stdout": receipt["stdout"],
        "stderr": receipt["stderr"],
        "exit_code": exit_code,
        "elapsed_seconds": elapsed,
        "receipt": receipt_ref,
    }


def reject_extras(
    run_dir: Path,
    plan: list[dict[str, Any]],
    allowed_engines: set[str],
) -> None:
    root = run_dir / "partitions"
    if not root.exists():
        return
    actual_engines = {path.name for path in root.iterdir()}
    unexpected_engines = sorted(actual_engines - allowed_engines)
    if unexpected_engines:
        raise base.HarnessError(f"unexpected engine artifact directories: {unexpected_engines}")
    expected_partitions = {base.partition_dir_name(item["key"]) for item in plan}
    for engine_dir in root.iterdir():
        extras = sorted(
            path.name for path in engine_dir.iterdir() if path.name not in expected_partitions
        )
        if extras:
            raise base.HarnessError(
                f"unexpected partition artifacts for {engine_dir.name}: {extras}"
            )


def write_or_verify(path: Path, document: dict[str, Any]) -> dict[str, Any]:
    if path.exists():
        existing, ref = base.verify_receipt_file(path)
        if existing != document:
            raise base.HarnessError(f"existing receipt differs: {path}")
        return ref
    return base.write_receipt_new(path, document)


def run_tasks(
    tasks: list[tuple[dict[str, Any], dict[str, Any]]],
    plan_ref: dict[str, Any],
    run_dir: Path,
    jobs: int,
    timeout_seconds: float,
) -> list[dict[str, Any]]:
    if not (1 <= jobs <= base.MAX_JOBS):
        raise base.HarnessError(f"--jobs must be in 1..{base.MAX_JOBS}")
    results: list[dict[str, Any]] = []
    errors: list[str] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
        futures = {
            pool.submit(
                run_engine_partition,
                item,
                engine,
                plan_ref,
                run_dir,
                timeout_seconds,
            ): f"{engine['name']} {item['key']}"
            for item, engine in tasks
        }
        for future in concurrent.futures.as_completed(futures):
            label = futures[future]
            try:
                results.append(future.result())
            except Exception as exc:
                errors.append(f"{label}: {exc}")
    if errors:
        raise base.HarnessError("one or more engine runs failed:\n" + "\n".join(errors))
    return results


def choose_run_items(
    args: argparse.Namespace, plan: list[dict[str, Any]]
) -> tuple[list[dict[str, Any]], bool]:
    by_key = {item["key"]: item for item in plan}
    if args.all:
        if args.partition:
            raise base.HarnessError("choose either --all or --partition, not both")
        if args.confirm_full_run != base.FULL_RUN_CONFIRMATION:
            raise base.HarnessError(
                f"full run requires --confirm-full-run {base.FULL_RUN_CONFIRMATION}"
            )
        return plan, True
    if not args.partition:
        raise base.HarnessError("run requires --partition or doubly guarded --all")
    if args.confirm_full_run:
        raise base.HarnessError("--confirm-full-run is valid only with --all")
    if len(args.partition) != len(set(args.partition)):
        raise base.HarnessError("duplicate partition selection")
    unknown = sorted(set(args.partition) - set(by_key))
    if unknown:
        raise base.HarnessError(f"unknown partition(s): {unknown}")
    selected = set(args.partition)
    return [item for item in plan if item["key"] in selected], False


def execute(args: argparse.Namespace) -> int:
    workspace = (
        Path(args.workspace).resolve()
        if args.workspace
        else Path(__file__).resolve().parents[2]
    )
    inputs = base.resolve_inputs(workspace)
    partitions = base.load_expected_plan(workspace, inputs)
    preserved = load_preserved_engine(workspace)
    engines: dict[str, dict[str, Any]] = {"preserved": preserved}
    if getattr(args, "fresh_build_run_dir", None):
        engines["fresh"] = load_fresh_engine(
            Path(args.fresh_build_run_dir).resolve(), inputs
        )

    if args.command == "plan":
        print(
            "CONFIG3_A2_ENGINE_PLAN_STRICT_OK partitions=47 "
            f"preserved_sha256={PRESERVED_BINARY_SHA256}"
        )
        print(
            "DIFFERENTIAL_KEYS=" + ",".join(DIFFERENTIAL_KEYS)
        )
        print(
            "FULL_RUN_GUARD="
            f"--all --confirm-full-run {base.FULL_RUN_CONFIRMATION}; full run not launched"
        )
        return 0

    if args.command in {"differential", "verify-differential"} and "fresh" not in engines:
        raise base.HarnessError("differential mode requires --fresh-build-run-dir")
    if args.command == "run" and args.engine not in engines:
        raise base.HarnessError(
            f"engine {args.engine!r} unavailable; fresh requires --fresh-build-run-dir"
        )

    document = make_plan_document(workspace, inputs, partitions, engines)
    run_dir = Path(args.run_dir).resolve()
    if args.command.startswith("verify"):
        plan_path = run_dir / "PLAN.json"
        existing, plan_ref = base.verify_receipt_file(plan_path)
        if existing != document:
            raise base.HarnessError("existing plan differs from current engine plan")
    else:
        run_dir.mkdir(parents=True, exist_ok=True)
        plan_ref = write_or_verify(run_dir / "PLAN.json", document)
    reject_extras(run_dir, partitions, set(engines))
    by_key = {item["key"]: item for item in partitions}

    if args.command in {"differential", "verify-differential"}:
        items = [by_key[key] for key in DIFFERENTIAL_KEYS]
        tasks = [(item, engines[name]) for item in items for name in ("preserved", "fresh")]
        if args.command == "differential":
            results = run_tasks(
                tasks, plan_ref, run_dir, args.jobs, args.timeout_seconds
            )
        else:
            results = [
                verify_engine_partition(item, engine, plan_ref, run_dir)
                for item, engine in tasks
            ]
        indexed = {(result["engine"], result["key"]): result for result in results}
        comparisons = []
        for key in DIFFERENTIAL_KEYS:
            old = indexed[("preserved", key)]
            new = indexed[("fresh", key)]
            if old["result_fields"] != new["result_fields"]:
                differing = sorted(
                    field
                    for field in set(old["result_fields"]) | set(new["result_fields"])
                    if old["result_fields"].get(field) != new["result_fields"].get(field)
                )
                raise base.HarnessError(
                    f"differential RESULT mismatch for {key}: fields={differing}"
                )
            comparisons.append(
                {
                    "key": key,
                    "status": "EXACT_RESULT_FIELDS_MATCH",
                    "nodes": old["nodes"],
                    "preserved": old,
                    "fresh": new,
                    "stdout_bytes_identical": old["stdout"]["sha256"]
                    == new["stdout"]["sha256"],
                }
            )
        differential = {
            "schema": DIFFERENTIAL_SCHEMA,
            "status": "PASS",
            "plan": plan_ref,
            "comparisons": comparisons,
        }
        ref = write_or_verify(run_dir / "DIFFERENTIAL_RECEIPT.json", differential)
        print(
            "CONFIG3_A2_DUAL_ENGINE_DIFFERENTIAL_OK partitions=2 engines=2 "
            "nodes=217,199150 exact_result_fields=true "
            f"receipt_sha256={ref['sha256']}"
        )
        return 0

    items, full = choose_run_items(args, partitions)
    engine = engines[args.engine]
    tasks = [(item, engine) for item in items]
    if args.command == "run":
        results = run_tasks(tasks, plan_ref, run_dir, args.jobs, args.timeout_seconds)
    else:
        results = [
            verify_engine_partition(item, engine, plan_ref, run_dir) for item in items
        ]
    indexed = {result["key"]: result for result in results}
    if set(indexed) != {item["key"] for item in items}:
        raise base.HarnessError("aggregate has missing, duplicate, or extra partition results")
    aggregate = {
        "schema": AGGREGATE_SCHEMA,
        "status": "PASS",
        "engine": engine,
        "scope": "full_47" if full else "selection",
        "plan": plan_ref,
        "partition_count": len(items),
        "node_sum": sum(item["expected_nodes"] for item in items),
        "partition_receipts": [indexed[item["key"]] for item in items],
    }
    name = "FULL_47_RECEIPT.json" if full else "SELECTION_RECEIPT.json"
    ref = write_or_verify(run_dir / name, aggregate)
    marker = "CONFIG3_A2_ENGINE_FULL_47_STRICT_OK" if full else "CONFIG3_A2_ENGINE_SELECTION_STRICT_OK"
    print(
        f"{marker} engine={engine['name']} partitions={len(items)} "
        f"nodes={aggregate['node_sum']} receipt_sha256={ref['sha256']}"
    )
    return 0


def add_common_execution(child: argparse.ArgumentParser) -> None:
    child.add_argument("--run-dir", required=True)
    child.add_argument("--fresh-build-run-dir")
    child.add_argument("--jobs", type=int, default=1)
    child.add_argument("--timeout-seconds", type=float, default=0.0)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace")
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("plan")
    differential = subparsers.add_parser("differential")
    add_common_execution(differential)
    verify_differential = subparsers.add_parser("verify-differential")
    add_common_execution(verify_differential)
    for name in ("run", "verify"):
        child = subparsers.add_parser(name)
        add_common_execution(child)
        child.add_argument("--engine", choices=("preserved", "fresh"), required=True)
        child.add_argument("--partition", action="append")
        child.add_argument("--all", action="store_true")
        child.add_argument("--confirm-full-run")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    try:
        return execute(args)
    except (base.HarnessError, OSError, subprocess.SubprocessError, ValueError) as exc:
        print(f"CONFIG3_A2_ENGINE_HARNESS_FAIL: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
