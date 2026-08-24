#!/usr/bin/env python3
"""Run one 15-solver terminal bundle or a deterministic smoke/canary gate."""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import signal
import stat
import subprocess
import sys
import threading
from pathlib import Path
from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple

sys.dont_write_bytecode = True
os.environ["PYTHONDONTWRITEBYTECODE"] = "1"

import g001_terminal5_common_v1 as common


NO_EVIDENCE_EXIT = 75
ACTIVE: Dict[int, subprocess.Popen[bytes]] = {}
ACTIVE_LOCK = threading.Lock()
STOP = threading.Event()
STOP_SIGNAL: Optional[int] = None


def write_new(path: Path, raw: bytes, mode: int = 0o444) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor = os.open(str(path), os.O_WRONLY | os.O_CREAT | os.O_EXCL, mode)
    try:
        with os.fdopen(descriptor, "wb", closefd=False) as stream:
            stream.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
    finally:
        os.close(descriptor)


def install_handlers() -> None:
    def handler(signum: int, _frame: Any) -> None:
        global STOP_SIGNAL
        STOP_SIGNAL = signum
        STOP.set()
        with ACTIVE_LOCK:
            processes = list(ACTIVE.values())
        for process in processes:
            try:
                process.terminate()
            except OSError:
                pass
    for name in ("SIGTERM", "SIGINT", "SIGHUP"):
        if hasattr(signal, name):
            signal.signal(getattr(signal, name), handler)


def run_process(command: Sequence[str]) -> subprocess.CompletedProcess[bytes]:
    if STOP.is_set():
        return subprocess.CompletedProcess(list(command), NO_EVIDENCE_EXIT, b"", b"stopped\n")
    process = subprocess.Popen(
        list(command), stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        start_new_session=False)
    with ACTIVE_LOCK:
        ACTIVE[process.pid] = process
    try:
        stdout, stderr = process.communicate()
    finally:
        with ACTIVE_LOCK:
            ACTIVE.pop(process.pid, None)
    return subprocess.CompletedProcess(list(command), process.returncode, stdout, stderr)


def deterministic_gate_records(plan: Mapping[str, Any], mode: str) -> List[Mapping[str, Any]]:
    per_configuration = 12 if mode == "smoke" else 6
    selected: List[Mapping[str, Any]] = []
    for configuration in (1, 4, 5, 6, 7):
        candidates = [item for item in plan["records"]
                      if item["configuration"] == configuration and
                      item["classification"] == "SEARCH"]
        candidates.sort(key=lambda item: (max(1, item["weight"]), tuple(item["path"])))
        if mode == "smoke":
            chosen = candidates[:per_configuration]
        else:
            # Six deterministic quantiles exercise light, middle, and heavy
            # leaves without treating cross-depth frontier values as equal.
            count = len(candidates)
            positions = [0, count // 5, (2 * count) // 5,
                         (3 * count) // 5, (4 * count) // 5, count - 1]
            chosen = [candidates[index] for index in positions]
        if len({item["record_id"] for item in chosen}) != per_configuration:
            raise common.TerminalError("gate selection contains a duplicate")
        selected.extend(chosen)
    selected.sort(key=lambda item: (item["configuration"], tuple(item["path"])))
    expected = 60 if mode == "smoke" else 30
    if len(selected) != expected:
        raise common.TerminalError("gate selection size mismatch")
    return selected


def locate_leaf(plan_dir: Path, plan: Mapping[str, Any], record: Mapping[str, Any]) -> Tuple[Path, int]:
    bundle_index = int(record["bundle_index"])
    bundle = plan["bundles"][bundle_index]
    try:
        local_index = bundle["record_ids"].index(record["record_id"])
    except ValueError as error:
        raise common.TerminalError("record is absent from declared bundle") from error
    return plan_dir / f"bundle_plans/bundle_{bundle_index:03d}.json", local_index


def verify_existing_receipt(path: Path, raw: bytes) -> None:
    if common.read_regular(path, "existing leaf receipt") != raw:
        raise common.TerminalError("existing leaf receipt differs from fresh verification")


def run_one(plan_dir: Path, workspace: Path, source_dir: Path, run_root: Path,
            plan: Mapping[str, Any], record: Mapping[str, Any]) -> Dict[str, Any]:
    if STOP.is_set():
        return {"record_id": record["record_id"], "outcome": "NO_EVIDENCE",
                "reason": "bundle stop requested"}
    bundle_index = int(record["bundle_index"])
    leaf_plan, local_index = locate_leaf(plan_dir, plan, record)
    bundle_run = run_root / f"bundle_{bundle_index:03d}"
    bundle_run.mkdir(mode=0o700, parents=True, exist_ok=True)
    leaf_dir = bundle_run / record["record_id"]
    worker = source_dir / "g001_remaining_leaf_worker.py"
    collector = source_dir / "g001_remaining_leaf_collect.py"
    worker_result: Optional[subprocess.CompletedProcess[bytes]] = None
    if not leaf_dir.exists() and not leaf_dir.is_symlink():
        worker_result = run_process([
            sys.executable, "-B", str(worker), "--plan", str(leaf_plan),
            "--workspace", str(workspace), "--run-dir", str(bundle_run),
            "--index", str(local_index), "--kill-grace-seconds", "30",
        ])
        if worker_result.returncode not in (0, 2):
            return {
                "record_id": record["record_id"], "configuration": record["configuration"],
                "bundle_index": bundle_index, "outcome": "NO_EVIDENCE",
                "worker_exit": worker_result.returncode,
                "worker_stdout": worker_result.stdout.decode("utf-8", errors="replace"),
                "worker_stderr": worker_result.stderr.decode("utf-8", errors="replace"),
            }
    collected = run_process([
        sys.executable, "-B", str(collector), "--plan", str(leaf_plan),
        "--workspace", str(workspace), "--run-dir", str(bundle_run),
        "--index", str(local_index),
    ])
    if collected.returncode not in (0, 2):
        return {
            "record_id": record["record_id"], "configuration": record["configuration"],
            "bundle_index": bundle_index, "outcome": "NO_EVIDENCE",
            "collector_exit": collected.returncode,
            "collector_stderr": collected.stderr.decode("utf-8", errors="replace"),
        }
    evidence = common.strict_json(collected.stdout, "leaf collector output")
    if (not isinstance(evidence, dict) or evidence.get("leaf_id") != record["record_id"] or
            evidence.get("configuration") != record["configuration"] or
            evidence.get("selector") != {"kind": "path", "indices": record["path"]} or
            evidence.get("outcome") not in ("ZERO", "VERIFIED_FOUND")):
        raise common.TerminalError("leaf collector identity/outcome mismatch")
    receipt = {
        "schema": "G001_TERMINAL5_LEAF_RECEIPT_V1",
        "terminal_plan_id": plan["plan_id"],
        "record_id": record["record_id"],
        "configuration": record["configuration"],
        "path": record["path"],
        "bundle_index": bundle_index,
        "leaf_plan": leaf_plan.relative_to(plan_dir).as_posix(),
        "leaf_plan_sha256": common.sha256_file(leaf_plan),
        "outcome": evidence["outcome"],
        "evidence": evidence,
    }
    raw = common.canonical_json(receipt)
    receipt_path = run_root / "leaf_receipts" / f"{record['record_id']}.json"
    try:
        write_new(receipt_path, raw)
    except FileExistsError:
        verify_existing_receipt(receipt_path, raw)
    if evidence["outcome"] == "VERIFIED_FOUND":
        alert = {
            "schema": "G001_TERMINAL5_IMMEDIATE_FOUND_ALERT_V1",
            "plan_id": plan["plan_id"],
            "record_id": record["record_id"],
            "configuration": record["configuration"],
            "path": record["path"],
            "independently_checked": True,
            "global_search_complete": False,
            "leaf_receipt_sha256": common.sha256_bytes(raw),
        }
        alert_path = run_root / "alerts" / f"VERIFIED_FOUND_{record['record_id']}.json"
        alert_raw = common.canonical_json(alert)
        try:
            write_new(alert_path, alert_raw)
        except FileExistsError:
            if common.read_regular(alert_path, "existing FOUND alert") != alert_raw:
                raise common.TerminalError("existing FOUND alert mismatch")
        print("G001_TERMINAL5_VERIFIED_FOUND_IMMEDIATE configuration={} path={} receipt={}".format(
            record["configuration"], record["path_text"], receipt_path), flush=True)
        STOP.set()
        with ACTIVE_LOCK:
            processes = list(ACTIVE.values())
        for process in processes:
            try:
                process.terminate()
            except OSError:
                pass
    return {"record_id": record["record_id"], "configuration": record["configuration"],
            "bundle_index": bundle_index, "outcome": evidence["outcome"],
            "receipt_sha256": common.sha256_bytes(raw)}


def execute(plan_dir: Path, workspace: Path, source_dir: Path, run_root: Path,
            mode: str, bundle_index: Optional[int], gate_task: Optional[int],
            workers: int) -> Dict[str, Any]:
    if os.name != "posix":
        raise common.TerminalError("terminal execution is supported only on POSIX/Linux")
    if workers != common.WORKERS_PER_BUNDLE:
        raise common.TerminalError("terminal runner requires exactly 15 solver workers")
    slurm_cpus = os.environ.get("SLURM_CPUS_PER_TASK")
    if slurm_cpus is not None and (not slurm_cpus.isdigit() or int(slurm_cpus) < common.CPUS_PER_BUNDLE):
        raise common.TerminalError("Slurm task has fewer than 16 allocated CPUs")
    plan_dir = common.require_directory(plan_dir, "plan directory")
    workspace = common.require_directory(workspace, "workspace")
    source_dir = common.require_directory(source_dir, "source directory")
    run_root = common.require_directory(run_root, "run root")
    plan, plan_hash = common.load_plan(plan_dir / "terminal_plan_v1.json", production=True)
    if mode == "production":
        if bundle_index is None or gate_task is not None or not 0 <= bundle_index < common.TOTAL_BUNDLES:
            raise common.TerminalError("production requires one valid --bundle-index")
        bundle = plan["bundles"][bundle_index]
        by_id = {item["record_id"]: item for item in plan["records"]}
        records = [by_id[item] for item in bundle["record_ids"]]
        receipt_name = f"bundle_{bundle_index:03d}.json"
        receipt_dir = run_root / "bundle_receipts"
    else:
        task_count = 4 if mode == "smoke" else 2
        if gate_task is None or bundle_index is not None or not 0 <= gate_task < task_count:
            raise common.TerminalError(f"{mode} requires --gate-task in 0..{task_count-1}")
        selected = deterministic_gate_records(plan, mode)
        records = [item for index, item in enumerate(selected) if index % task_count == gate_task]
        if len(records) != 15:
            raise common.TerminalError("gate task must contain exactly 15 leaves")
        receipt_name = f"{mode}_task_{gate_task:02d}.json"
        receipt_dir = run_root / "gate_receipts"
    install_handlers()
    results: List[Dict[str, Any]] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        future_map = {pool.submit(run_one, plan_dir, workspace, source_dir, run_root,
                                  plan, record): record for record in records}
        for future in concurrent.futures.as_completed(future_map):
            try:
                result = future.result()
            except BaseException as error:
                STOP.set()
                result = {"record_id": future_map[future]["record_id"],
                          "outcome": "NO_EVIDENCE", "reason": str(error)}
            results.append(result)
    results.sort(key=lambda item: item["record_id"])
    found = [item for item in results if item.get("outcome") == "VERIFIED_FOUND"]
    incomplete = [item for item in results if item.get("outcome") not in ("ZERO", "VERIFIED_FOUND")]
    receipt = {
        "schema": common.BUNDLE_RECEIPT_SCHEMA if mode == "production" else common.PARTIAL_RECEIPT_SCHEMA,
        "plan_id": plan["plan_id"], "plan_sha256": plan_hash,
        "mode": mode, "bundle_index": bundle_index, "gate_task": gate_task,
        "workers": workers, "expected_records": len(records),
        "exact_records": len(results) - len(incomplete),
        "verified_found": len(found), "incomplete": len(incomplete),
        "global_search_complete": False,
        "signal": STOP_SIGNAL,
        "results": results,
    }
    raw = common.canonical_json(receipt)
    receipt_path = receipt_dir / receipt_name
    try:
        write_new(receipt_path, raw)
    except FileExistsError:
        verify_existing_receipt(receipt_path, raw)
    if found:
        return {**receipt, "exit_code": 2}
    if incomplete or STOP_SIGNAL is not None:
        return {**receipt, "exit_code": NO_EVIDENCE_EXIT}
    return {**receipt, "exit_code": 0}


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan-dir", required=True, type=Path)
    parser.add_argument("--workspace", required=True, type=Path)
    parser.add_argument("--source-dir", required=True, type=Path)
    parser.add_argument("--run-root", required=True, type=Path)
    parser.add_argument("--mode", choices=("production", "smoke", "canary"), required=True)
    parser.add_argument("--bundle-index", type=int)
    parser.add_argument("--gate-task", type=int)
    parser.add_argument("--workers", type=int, default=common.WORKERS_PER_BUNDLE)
    args = parser.parse_args(argv)
    try:
        report = execute(args.plan_dir, args.workspace, args.source_dir, args.run_root,
                         args.mode, args.bundle_index, args.gate_task, args.workers)
        print("G001_TERMINAL5_RUN_V1 mode={} exact={} found={} incomplete={} receipt_global_complete=0".format(
            args.mode, report["exact_records"], report["verified_found"], report["incomplete"]),
            flush=True)
        return int(report["exit_code"])
    except (common.TerminalError, OSError, ValueError, KeyError) as error:
        print(f"G001_TERMINAL5_RUN_V1_FAILED: {error}", file=sys.stderr, flush=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
