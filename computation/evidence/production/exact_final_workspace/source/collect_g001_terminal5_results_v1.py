#!/usr/bin/env python3
"""Independently verify terminal leaf evidence and make fail-closed summaries."""

from __future__ import annotations

import argparse
import importlib.util
import os
import stat
import sys
from pathlib import Path
from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple

sys.dont_write_bytecode = True

import g001_terminal5_common_v1 as common


def load_leaf_modules(source_dir: Path) -> Tuple[Any, Any]:
    saved_common = sys.modules.pop("g001_remaining_leaf_common", None)
    saved_path = list(sys.path)
    try:
        sys.path.insert(0, str(source_dir))
        common_spec = importlib.util.spec_from_file_location(
            "g001_remaining_leaf_common", str(source_dir / "g001_remaining_leaf_common.py"))
        if common_spec is None or common_spec.loader is None:
            raise common.TerminalError("cannot load leaf common")
        leaf_common = importlib.util.module_from_spec(common_spec)
        sys.modules["g001_remaining_leaf_common"] = leaf_common
        common_spec.loader.exec_module(leaf_common)
        collector_spec = importlib.util.spec_from_file_location(
            "_terminal5_leaf_collector", str(source_dir / "g001_remaining_leaf_collect.py"))
        if collector_spec is None or collector_spec.loader is None:
            raise common.TerminalError("cannot load leaf collector")
        collector = importlib.util.module_from_spec(collector_spec)
        collector_spec.loader.exec_module(collector)
        if (Path(leaf_common.__file__).resolve() != (source_dir / "g001_remaining_leaf_common.py").resolve() or
                Path(collector.__file__).resolve() != (source_dir / "g001_remaining_leaf_collect.py").resolve()):
            raise common.TerminalError("leaf verifier import path mismatch")
        return leaf_common, collector
    finally:
        sys.path[:] = saved_path
        if saved_common is None:
            sys.modules.pop("g001_remaining_leaf_common", None)
        else:
            sys.modules["g001_remaining_leaf_common"] = saved_common


def write_new(path: Path, raw: bytes) -> None:
    descriptor = os.open(str(path), os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o444)
    try:
        with os.fdopen(descriptor, "wb", closefd=False) as stream:
            stream.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
    finally:
        os.close(descriptor)


def verify_runner_receipt(receipt_path: Path, terminal_plan: Mapping[str, Any],
                          record: Mapping[str, Any], bundle_index: int,
                          leaf_plan_path: Path, evidence: Mapping[str, Any]) -> str:
    receipt_raw = common.read_regular(receipt_path, "terminal leaf receipt")
    receipt = common.strict_json(receipt_raw, "terminal leaf receipt")
    expected = {
        "schema": "G001_TERMINAL5_LEAF_RECEIPT_V1",
        "terminal_plan_id": terminal_plan["plan_id"],
        "record_id": record["record_id"],
        "configuration": record["configuration"],
        "path": record["path"],
        "bundle_index": bundle_index,
        "leaf_plan": f"bundle_plans/bundle_{bundle_index:03d}.json",
        "leaf_plan_sha256": common.sha256_file(leaf_plan_path),
        "outcome": evidence["outcome"],
        "evidence": evidence,
    }
    if receipt != expected:
        raise common.TerminalError(f"runner receipt mismatch: {record['record_id']}")
    return common.sha256_bytes(receipt_raw)


def collect_record(plan_dir: Path, workspace: Path, run_root: Path,
                   terminal_plan: Mapping[str, Any], record: Mapping[str, Any],
                   leaf_common: Any, collector: Any,
                   cache: Dict[int, Tuple[Mapping[str, Any], str, Mapping[str, Any]]]) -> Dict[str, Any]:
    bundle_index = int(record["bundle_index"])
    if bundle_index not in cache:
        leaf_plan_path = plan_dir / f"bundle_plans/bundle_{bundle_index:03d}.json"
        leaf_plan, leaf_hash = leaf_common.load_plan(leaf_plan_path)
        pipeline = leaf_common.verify_pipeline_artifacts(leaf_plan, workspace)
        leaf_common.verify_executing_pipeline(
            pipeline,
            {"leaf_collector": Path(collector.__file__),
             "leaf_common": Path(leaf_common.__file__)})
        cache[bundle_index] = (leaf_plan, leaf_hash, pipeline)
    leaf_plan, leaf_hash, pipeline = cache[bundle_index]
    bundle = terminal_plan["bundles"][bundle_index]
    local_index = bundle["record_ids"].index(record["record_id"])
    evidence = collector.collect_leaf(
        leaf_plan, leaf_hash, workspace,
        run_root / f"bundle_{bundle_index:03d}", local_index, pipeline)
    receipt_path = run_root / "leaf_receipts" / f"{record['record_id']}.json"
    receipt_hash = verify_runner_receipt(
        receipt_path, terminal_plan, record, bundle_index,
        plan_dir / f"bundle_plans/bundle_{bundle_index:03d}.json", evidence)
    return {
        "record_id": record["record_id"],
        "configuration": record["configuration"],
        "path": record["path"],
        "bundle_index": bundle_index,
        "outcome": evidence["outcome"],
        "leaf_receipt_sha256": receipt_hash,
        "solver_wall_seconds": evidence["solver_wall_seconds"],
        "nodes": int(evidence["solver_result"]["nodes"]),
    }


def verify_bundle_receipt(run_root: Path, terminal_plan: Mapping[str, Any],
                          plan_hash: str, bundle: Mapping[str, Any],
                          records: Mapping[str, Mapping[str, Any]]) -> None:
    path = run_root / "bundle_receipts" / f"bundle_{bundle['bundle_index']:03d}.json"
    receipt = common.read_json(path, "bundle receipt")
    if (not isinstance(receipt, dict) or receipt.get("schema") != common.BUNDLE_RECEIPT_SCHEMA or
            receipt.get("plan_id") != terminal_plan["plan_id"] or
            receipt.get("plan_sha256") != plan_hash or receipt.get("mode") != "production" or
            receipt.get("bundle_index") != bundle["bundle_index"] or
            receipt.get("gate_task") is not None or receipt.get("workers") != common.WORKERS_PER_BUNDLE or
            receipt.get("expected_records") != bundle["search_count"] or
            receipt.get("exact_records") != bundle["search_count"] or
            receipt.get("incomplete") != 0 or receipt.get("signal") is not None or
            receipt.get("global_search_complete") is not False):
        raise common.TerminalError(f"bundle receipt envelope mismatch: {bundle['bundle_index']}")
    results = receipt.get("results")
    if not isinstance(results, list) or {item.get("record_id") for item in results} != set(bundle["record_ids"]):
        raise common.TerminalError(f"bundle receipt result union mismatch: {bundle['bundle_index']}")
    for result in results:
        record = records[result["record_id"]]
        if (result.get("configuration") != record["configuration"] or
                result.get("bundle_index") != bundle["bundle_index"] or
                result.get("outcome") not in ("ZERO", "VERIFIED_FOUND")):
            raise common.TerminalError("bundle receipt record mismatch")


def scan_verified_found(run_root: Path, records: Mapping[str, Mapping[str, Any]]) -> List[str]:
    receipt_dir = run_root / "leaf_receipts"
    if not receipt_dir.exists():
        return []
    found: List[str] = []
    for path in receipt_dir.glob("*.json"):
        if path.is_symlink() or not path.is_file():
            raise common.TerminalError("leaf receipt directory contains unsafe entry")
        value = common.read_json(path, "leaf receipt scan")
        record_id = value.get("record_id") if isinstance(value, dict) else None
        if record_id not in records or path.name != f"{record_id}.json":
            raise common.TerminalError("leaf receipt scan identity mismatch")
        if value.get("outcome") == "VERIFIED_FOUND":
            found.append(record_id)
    return sorted(found)


def collect(plan_dir: Path, workspace: Path, source_dir: Path, run_root: Path,
            configuration: Optional[int]) -> Dict[str, Any]:
    plan_dir = common.require_directory(plan_dir, "plan directory")
    workspace = common.require_directory(workspace, "workspace")
    source_dir = common.require_directory(source_dir, "source directory")
    run_root = common.require_directory(run_root, "run root")
    terminal_plan, plan_hash = common.load_plan(plan_dir / "terminal_plan_v1.json", production=True)
    records = {item["record_id"]: item for item in terminal_plan["records"]}
    found_ids = scan_verified_found(run_root, records)
    selected_search = [item for item in terminal_plan["records"]
                       if item["classification"] == "SEARCH" and
                       (configuration is None or item["configuration"] == configuration)]
    selected_zero = [item for item in terminal_plan["records"]
                     if item["classification"] == "CERTIFIED_ZERO" and
                     (configuration is None or item["configuration"] == configuration)]
    leaf_common, collector = load_leaf_modules(source_dir)
    cache: Dict[int, Tuple[Mapping[str, Any], str, Mapping[str, Any]]] = {}
    # A FOUND claim may be reported immediately without pretending the census
    # is complete. Re-run only those independently checked receipts first.
    if found_ids:
        verified_found = []
        for record_id in found_ids:
            record = records[record_id]
            if configuration is None or record["configuration"] == configuration:
                result = collect_record(plan_dir, workspace, run_root, terminal_plan,
                                        record, leaf_common, collector, cache)
                if result["outcome"] != "VERIFIED_FOUND":
                    raise common.TerminalError("FOUND scan did not replay as VERIFIED_FOUND")
                verified_found.append(result)
        if verified_found:
            return {
                "schema": common.COLLECTION_SCHEMA,
                "plan_id": terminal_plan["plan_id"], "plan_sha256": plan_hash,
                "scope": "global" if configuration is None else f"configuration_{configuration}",
                "status": "VERIFIED_FOUND",
                "verified_found": verified_found,
                "terminal_search_complete": False,
                "global_nonexistence": False,
                "configuration_nonexistence": False,
                "claim": "existence witness independently checked; remaining search may be incomplete",
            }
    results: List[Dict[str, Any]] = []
    for record in selected_search:
        try:
            results.append(collect_record(
                plan_dir, workspace, run_root, terminal_plan, record,
                leaf_common, collector, cache))
        except collector.NoEvidence as error:
            raise common.TerminalError(
                f"missing/incomplete evidence for {record['record_id']}: {error}") from error
    if any(item["outcome"] != "ZERO" for item in results):
        raise common.TerminalError("non-ZERO terminal outcome escaped FOUND handling")
    required_bundles = [item for item in terminal_plan["bundles"]
                        if configuration is None or item["configuration"] == configuration]
    for bundle in required_bundles:
        verify_bundle_receipt(run_root, terminal_plan, plan_hash, bundle, records)
    by_configuration: Dict[str, Any] = {}
    configs = (configuration,) if configuration is not None else (1, 4, 5, 6, 7)
    for config in configs:
        config_results = [item for item in results if item["configuration"] == config]
        config_zeros = [item for item in selected_zero if item["configuration"] == config]
        by_configuration[str(config)] = {
            "search_receipts": len(config_results),
            "certified_zero_records": len(config_zeros),
            "displayed_partition_records": len(config_results) + len(config_zeros),
            "solver_wall_seconds_sum": sum(float(item["solver_wall_seconds"]) for item in config_results),
            "nodes_sum": sum(item["nodes"] for item in config_results),
            "terminal_zero": True,
        }
    complete_global = configuration is None and len(results) == common.TOTAL_SEARCH
    return {
        "schema": common.COLLECTION_SCHEMA,
        "plan_id": terminal_plan["plan_id"], "plan_sha256": plan_hash,
        "scope": "global" if configuration is None else f"configuration_{configuration}",
        "status": "GLOBAL_ZERO_COMPLETE" if complete_global else "CONFIGURATION_ZERO_COMPLETE",
        "search_receipts": len(results),
        "certified_zero_records": len(selected_zero),
        "displayed_partition_records": len(results) + len(selected_zero),
        "by_configuration": by_configuration,
        "terminal_search_complete": complete_global,
        "global_nonexistence": complete_global,
        "configuration_nonexistence": configuration is not None,
        "timeouts_are_non_evidence": True,
        "claim": ("all 39,000 terminal search receipts plus 30 prior certified zeros are exact"
                  if complete_global else "this configuration alone has exact terminal ZERO coverage"),
    }


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan-dir", required=True, type=Path)
    parser.add_argument("--workspace", required=True, type=Path)
    parser.add_argument("--source-dir", required=True, type=Path)
    parser.add_argument("--run-root", required=True, type=Path)
    selection = parser.add_mutually_exclusive_group(required=True)
    selection.add_argument("--all", action="store_true")
    selection.add_argument("--configuration", type=int, choices=(1, 4, 5, 6, 7))
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    try:
        report = collect(args.plan_dir, args.workspace, args.source_dir,
                         args.run_root, args.configuration)
        raw = common.canonical_json(report)
        if args.output is not None:
            output = Path(os.path.abspath(os.fspath(args.output)))
            write_new(output, raw)
            print(f"G001_TERMINAL5_COLLECTION_WRITTEN {output}")
        else:
            sys.stdout.buffer.write(raw)
        return 2 if report["status"] == "VERIFIED_FOUND" else 0
    except (common.TerminalError, OSError, ValueError, KeyError) as error:
        print(f"G001_TERMINAL5_COLLECTION_FAILED: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
