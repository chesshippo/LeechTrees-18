#!/usr/bin/env python3
"""Independent exact-set verifier for the 39,030-record terminal plan."""

from __future__ import annotations

import argparse
import importlib.util
import os
import stat
import sys
from pathlib import Path
from typing import Any, Dict, Mapping, Optional, Sequence, Set

sys.dont_write_bytecode = True

import g001_terminal5_common_v1 as common


def load_leaf_common(source_dir: Path) -> Any:
    path = source_dir / "g001_remaining_leaf_common.py"
    specification = importlib.util.spec_from_file_location("_terminal5_leaf_common", str(path))
    if specification is None or specification.loader is None:
        raise common.TerminalError("cannot load frozen leaf common")
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    if Path(module.__file__).resolve() != path.resolve():
        raise common.TerminalError("leaf common import path mismatch")
    return module


def exact_directory(path: Path, files: Set[str], directories: Set[str], label: str) -> None:
    path = common.require_directory(path, label)
    actual_files: Set[str] = set()
    actual_directories: Set[str] = set()
    for item in path.iterdir():
        info = item.lstat()
        if stat.S_ISLNK(info.st_mode):
            raise common.TerminalError(f"{label} contains a symlink")
        if stat.S_ISREG(info.st_mode):
            if info.st_nlink != 1:
                raise common.TerminalError(f"{label} contains a hard-linked file")
            actual_files.add(item.name)
        elif stat.S_ISDIR(info.st_mode):
            actual_directories.add(item.name)
        else:
            raise common.TerminalError(f"{label} contains a special entry")
    if actual_files != files or actual_directories != directories:
        raise common.TerminalError(
            f"{label} exact-set mismatch files={sorted(actual_files)} dirs={sorted(actual_directories)}")


def parse_manifest(raw: bytes) -> Dict[str, str]:
    result: Dict[str, str] = {}
    try:
        text = raw.decode("ascii", errors="strict")
    except UnicodeError as error:
        raise common.TerminalError("plan manifest is not ASCII") from error
    for line in text.splitlines():
        parts = line.split("  ")
        if len(parts) != 2 or not common.HEX64.fullmatch(parts[0]) or parts[1] in result:
            raise common.TerminalError("malformed/duplicate plan manifest line")
        relative = Path(parts[1])
        if relative.is_absolute() or ".." in relative.parts:
            raise common.TerminalError("unsafe plan manifest path")
        result[relative.as_posix()] = parts[0]
    return result


def expected_leaf(record: Mapping[str, Any], plan: Mapping[str, Any]) -> Dict[str, Any]:
    bindings = plan["runtime"]["bindings"]
    path = list(record["path"])
    return {
        "leaf_id": record["record_id"],
        "configuration": record["configuration"],
        "mode": record["mode"],
        "selector": {"kind": "path", "indices": path},
        "argv_template": common.solver_argv(record["configuration"], path),
        "timeout_seconds": 0,
        "artifacts": {
            "solver_source": bindings["solver_source"],
            "solver_executable": bindings["solver_executable"],
            "checker_source": bindings["checker_source"],
            "checker_executable": bindings["checker_executable"],
            "dependencies": [{"role": "terminal5_runtime_freeze",
                              "path": bindings["runtime_freeze"]["path"],
                              "sha256": bindings["runtime_freeze"]["sha256"]}],
        },
    }


def verify(plan_dir: Path, workspace: Path, source_dir: Path) -> Dict[str, Any]:
    plan_dir = common.require_directory(plan_dir, "plan directory")
    workspace = common.require_directory(workspace, "workspace")
    source_dir = common.require_directory(source_dir, "frozen source")
    exact_directory(plan_dir,
                    {"terminal_plan_v1.json", "plan_artifacts.sha256", "plan_receipt.json"},
                    {"bundle_plans"}, "plan directory")
    bundle_dir = plan_dir / "bundle_plans"
    expected_bundle_names = {f"bundle_{index:03d}.json" for index in range(common.TOTAL_BUNDLES)}
    exact_directory(bundle_dir, expected_bundle_names, set(), "bundle-plan directory")
    plan, plan_hash = common.load_plan(plan_dir / "terminal_plan_v1.json", production=True)
    manifest_raw = common.read_regular(plan_dir / "plan_artifacts.sha256", "plan manifest")
    manifest = parse_manifest(manifest_raw)
    expected_manifest_paths = {"terminal_plan_v1.json"} | {
        f"bundle_plans/bundle_{index:03d}.json" for index in range(common.TOTAL_BUNDLES)}
    if set(manifest) != expected_manifest_paths:
        raise common.TerminalError("plan manifest exact-set mismatch")
    for relative, digest in manifest.items():
        if common.sha256_file(plan_dir / relative) != digest:
            raise common.TerminalError(f"plan manifest hash mismatch: {relative}")
    receipt = common.read_json(plan_dir / "plan_receipt.json", "plan receipt")
    if not isinstance(receipt, dict):
        raise common.TerminalError("plan receipt must be an object")
    common.require_keys(receipt, ("schema", "plan_id", "plan_sha256", "manifest_sha256",
                                  "record_count", "search_count", "certified_zero_count",
                                  "bundle_count", "archive_package_identity_audited",
                                  "package_replay_exact", "terminal_search_performed"),
                        "plan receipt")
    if receipt != {
        "schema": common.PLAN_RECEIPT_SCHEMA,
        "plan_id": plan["plan_id"],
        "plan_sha256": plan_hash,
        "manifest_sha256": common.sha256_bytes(manifest_raw),
        "record_count": common.TOTAL_RECORDS,
        "search_count": common.TOTAL_SEARCH,
        "certified_zero_count": common.TOTAL_ZERO,
        "bundle_count": common.TOTAL_BUNDLES,
        "archive_package_identity_audited": True,
        "package_replay_exact": True,
        "terminal_search_performed": False,
    }:
        raise common.TerminalError("plan receipt mismatch")
    for role, binding in {**plan["runtime"]["bindings"],
                          **plan["runtime"]["pipeline_artifacts"]}.items():
        target = (workspace / binding["path"]).resolve(strict=True)
        try:
            target.relative_to(workspace)
        except ValueError as error:
            raise common.TerminalError(f"{role} resolves outside workspace") from error
        if common.sha256_file(target) != binding["sha256"]:
            raise common.TerminalError(f"runtime/pipeline binding mismatch: {role}")
    runtime_freeze = common.read_json(
        workspace / plan["runtime"]["bindings"]["runtime_freeze"]["path"], "runtime freeze")
    policy = runtime_freeze.get("terminal_policy", {})
    if (policy.get("node_cap", "bad") is not None or
            policy.get("depth_cap", "bad") is not None or
            policy.get("stop_depth", "bad") is not None or
            policy.get("witness_required_before_found_exit") is not True or
            policy.get("independent_checker_required") is not True):
        raise common.TerminalError("runtime freeze is not uncapped witness-safe terminal search")
    leaf_common = load_leaf_common(source_dir)
    by_id = {record["record_id"]: record for record in plan["records"]}
    for bundle in plan["bundles"]:
        path = bundle_dir / f"bundle_{bundle['bundle_index']:03d}.json"
        leaf_plan, _leaf_hash = leaf_common.load_plan(path)
        if (leaf_plan["plan_id"] != f"{plan['plan_id']}.{bundle['bundle_id']}" or
                leaf_plan["pipeline_artifacts"] != plan["runtime"]["pipeline_artifacts"] or
                len(leaf_plan["leaves"]) != bundle["search_count"]):
            raise common.TerminalError("derived leaf plan envelope mismatch")
        expected = [expected_leaf(by_id[record_id], plan) for record_id in bundle["record_ids"]]
        if leaf_plan["leaves"] != expected:
            raise common.TerminalError(
                f"derived leaf plan mismatch for bundle {bundle['bundle_index']}")
        leaf_common.verify_pipeline_artifacts(leaf_plan, workspace)
    # An explicit regression for the subtle C4 rule: depth-15 calibration
    # frontier zero remains in the SEARCH set unless separately discharged.
    depth15_zero = [item for item in plan["records"]
                    if item["evidence"]["kind"] == "config4_depth15_descendant" and
                    item["evidence"]["calibration_frontier"] == 0]
    if len(depth15_zero) != 470 or any(item["classification"] != "SEARCH" for item in depth15_zero):
        raise common.TerminalError("Config4 depth-15 zero-frontier search invariant mismatch")
    return {
        "schema": "G001_TERMINAL5_PLAN_AUDIT_V1",
        "plan_id": plan["plan_id"],
        "plan_sha256": plan_hash,
        "records": common.TOTAL_RECORDS,
        "search": common.TOTAL_SEARCH,
        "certified_zero": common.TOTAL_ZERO,
        "bundles": common.TOTAL_BUNDLES,
        "workers_per_bundle": common.WORKERS_PER_BUNDLE,
        "prefix_free": True,
        "bundle_union_exact": True,
        "c4_depth15_frontier0_search_records": len(depth15_zero),
        "terminal_search_performed": False,
    }


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan-dir", required=True, type=Path)
    parser.add_argument("--workspace", required=True, type=Path)
    parser.add_argument("--source-dir", required=True, type=Path)
    parser.add_argument("--print-json", action="store_true")
    args = parser.parse_args(argv)
    try:
        report = verify(args.plan_dir, args.workspace, args.source_dir)
        if args.print_json:
            print(common.canonical_json(report).decode("utf-8"), end="")
        print("G001_TERMINAL5_PLAN_V1_VERIFIED records=39030 search=39000 zero=30 bundles=192 "
              f"sha256={report['plan_sha256']}")
        return 0
    except (common.TerminalError, OSError, ValueError, KeyError) as error:
        print(f"G001_TERMINAL5_PLAN_V1_VERIFY_FAILED: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
