#!/usr/bin/env python3
"""Re-collect every devel-smoke or mi2101x-canary leaf and audit the gate."""

from __future__ import annotations

import argparse
import importlib.util
import os
import sys
from pathlib import Path
from typing import Any, Dict, Optional, Sequence

sys.dont_write_bytecode = True

import g001_terminal5_common_v1 as common


def load(path: Path, name: str) -> Any:
    specification = importlib.util.spec_from_file_location(name, str(path))
    if specification is None or specification.loader is None:
        raise common.TerminalError(f"cannot load {path}")
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


def write_new(path: Path, raw: bytes) -> None:
    descriptor = os.open(str(path), os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o444)
    try:
        with os.fdopen(descriptor, "wb", closefd=False) as stream:
            stream.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
    finally:
        os.close(descriptor)


def verify(plan_dir: Path, workspace: Path, source_dir: Path,
           run_root: Path, mode: str) -> Dict[str, Any]:
    plan_dir = common.require_directory(plan_dir, "plan directory")
    workspace = common.require_directory(workspace, "workspace")
    source_dir = common.require_directory(source_dir, "source directory")
    run_root = common.require_directory(run_root, "gate run root")
    plan, plan_hash = common.load_plan(plan_dir / "terminal_plan_v1.json", production=True)
    runner = load(source_dir / "run_g001_terminal5_bundle_v1.py", "_terminal5_gate_runner")
    result_collector = load(source_dir / "collect_g001_terminal5_results_v1.py",
                            "_terminal5_gate_collector")
    selected = runner.deterministic_gate_records(plan, mode)
    task_count = 4 if mode == "smoke" else 2
    expected_count = 60 if mode == "smoke" else 30
    if len(selected) != expected_count:
        raise common.TerminalError("deterministic gate selection mismatch")
    observed_ids = set()
    for task in range(task_count):
        path = run_root / "gate_receipts" / f"{mode}_task_{task:02d}.json"
        receipt = common.read_json(path, "gate task receipt")
        task_records = [item for index, item in enumerate(selected) if index % task_count == task]
        if (not isinstance(receipt, dict) or receipt.get("schema") != common.PARTIAL_RECEIPT_SCHEMA or
                receipt.get("plan_id") != plan["plan_id"] or
                receipt.get("plan_sha256") != plan_hash or receipt.get("mode") != mode or
                receipt.get("bundle_index") is not None or receipt.get("gate_task") != task or
                receipt.get("workers") != common.WORKERS_PER_BUNDLE or
                receipt.get("expected_records") != 15 or receipt.get("exact_records") != 15 or
                receipt.get("incomplete") != 0 or receipt.get("signal") is not None or
                receipt.get("global_search_complete") is not False):
            raise common.TerminalError(f"{mode} gate receipt envelope mismatch task={task}")
        results = receipt.get("results")
        expected_ids = {item["record_id"] for item in task_records}
        if not isinstance(results, list) or {item.get("record_id") for item in results} != expected_ids:
            raise common.TerminalError(f"{mode} gate task union mismatch task={task}")
        observed_ids.update(expected_ids)
    if observed_ids != {item["record_id"] for item in selected}:
        raise common.TerminalError("gate receipt union is not exact")
    leaf_common, collector = result_collector.load_leaf_modules(source_dir)
    cache: Dict[int, Any] = {}
    records = [result_collector.collect_record(
        plan_dir, workspace, run_root, plan, record,
        leaf_common, collector, cache) for record in selected]
    found = [item for item in records if item["outcome"] == "VERIFIED_FOUND"]
    if any(item["outcome"] not in ("ZERO", "VERIFIED_FOUND") for item in records):
        raise common.TerminalError("gate contains nonterminal evidence")
    by_configuration = {}
    for configuration in (1, 4, 5, 6, 7):
        group = [item for item in records if item["configuration"] == configuration]
        by_configuration[str(configuration)] = {
            "leaves": len(group),
            "solver_wall_seconds_sum": sum(float(item["solver_wall_seconds"]) for item in group),
            "nodes_sum": sum(item["nodes"] for item in group),
            "verified_found": sum(item["outcome"] == "VERIFIED_FOUND" for item in group),
        }
    return {
        "schema": "G001_TERMINAL5_GATE_AUDIT_V1",
        "plan_id": plan["plan_id"], "plan_sha256": plan_hash,
        "mode": mode, "tasks": task_count,
        "allocated_cpus": task_count * common.CPUS_PER_BUNDLE,
        "active_solver_workers": task_count * common.WORKERS_PER_BUNDLE,
        "records": len(records), "exact": True,
        "verified_found": len(found),
        "by_configuration": by_configuration,
        "terminal_search_complete": False,
        "global_nonexistence": False,
        "gate_pass": True,
    }


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan-dir", required=True, type=Path)
    parser.add_argument("--workspace", required=True, type=Path)
    parser.add_argument("--source-dir", required=True, type=Path)
    parser.add_argument("--run-root", required=True, type=Path)
    parser.add_argument("--mode", choices=("smoke", "canary"), required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    try:
        report = verify(args.plan_dir, args.workspace, args.source_dir,
                        args.run_root, args.mode)
        raw = common.canonical_json(report)
        if args.output is not None:
            write_new(Path(os.path.abspath(os.fspath(args.output))), raw)
        else:
            sys.stdout.buffer.write(raw)
        print("G001_TERMINAL5_GATE_V1_OK mode={} records={} allocated_cpus={} solver_workers={} found={}".format(
            args.mode, report["records"], report["allocated_cpus"],
            report["active_solver_workers"], report["verified_found"]))
        return 2 if report["verified_found"] else 0
    except (common.TerminalError, OSError, ValueError, KeyError) as error:
        print(f"G001_TERMINAL5_GATE_V1_FAILED: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
