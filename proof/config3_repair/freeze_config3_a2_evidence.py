#!/usr/bin/env python3
"""Export the verified Config3/A2 split run as relocatable frozen evidence.

The exporter is deliberately separate from the solver harness.  It launches no
solver or compiler, revalidates the transient parent/split evidence, rewrites
all receipts with release-root-relative paths, copies raw streams byte for
byte, builds a complete manifest, and stages the tree atomically.  The
independent frozen verifier must pass on the staged tree before publication.
"""

from __future__ import annotations

import argparse
import os
import shutil
import sys
from pathlib import Path
from typing import Any

import rerun_config3_a2 as base
import run_config3_a2_engines as engines
import run_config3_a2_path8_14_split as split
import verify_config3_a2_frozen as frozen


EXPORT_MARKER = "CONFIG3_A2_FROZEN_SPLIT_EXPORT_OK"


def fail(message: str) -> None:
    raise base.HarnessError(message)


def write_bytes_new(path: Path, raw: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    base.atomic_write_new(path, raw)


def write_json_new(root: Path, relative: str, value: dict[str, Any]) -> dict[str, Any]:
    path = root / relative
    raw = frozen.canonical_json_bytes(value)
    write_bytes_new(path, raw)
    digest = frozen.sha256_bytes(raw)
    write_bytes_new(
        path.with_name(path.name + ".sha256"),
        f"{digest}  {path.name}\n".encode("ascii"),
    )
    return frozen.portable_ref(path, relative)


def copy_raw_new(source: Path, root: Path, relative: str) -> dict[str, Any]:
    if not source.is_file() or source.is_symlink():
        fail(f"missing/plain transient raw source: {source}")
    target = root / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists():
        fail(f"refusing to overwrite staged raw file: {target}")
    with source.open("rb") as incoming, target.open("xb") as outgoing:
        shutil.copyfileobj(incoming, outgoing, length=1024 * 1024)
        outgoing.flush()
        os.fsync(outgoing.fileno())
    if target.stat().st_size != source.stat().st_size or frozen.sha256_file(target) != frozen.sha256_file(source):
        fail(f"raw copy differs from transient source: {source}")
    return frozen.portable_ref(target, relative)


def provenance(ref: dict[str, Any]) -> dict[str, Any]:
    return {"bytes": ref["bytes"], "sha256": ref["sha256"]}


def bindings(include_split: bool) -> dict[str, str]:
    value = {
        "engine_sha256": frozen.ENGINE_SHA256,
        "parent_plan_sha256": frozen.PARENT_PLAN["sha256"],
        "source_sha256": frozen.SOURCE_PINS["source"][1],
        "ledger_sha256": frozen.SOURCE_PINS["expected_ledger"][1],
    }
    if include_split:
        value["split_plan_sha256"] = frozen.SPLIT_PLAN["sha256"]
    return value


def release_receipt_ref(root: Path, relative: str) -> dict[str, Any]:
    return frozen.portable_ref(root / relative, relative)


def load_transient(
    workspace: Path,
    parent_run_dir: Path,
    split_run_dir: Path,
) -> dict[str, Any]:
    inputs, partitions, target, engine, parent_plan_ref = split.load_context(
        workspace, parent_run_dir
    )
    split_plan_document = split.make_split_plan(
        workspace, inputs, target, engine, parent_plan_ref
    )
    actual_split_plan, split_plan_ref = split.read_document(
        split_run_dir / "SPLIT_PLAN.json", split_run_dir
    )
    if actual_split_plan != split_plan_document:
        fail("transient SPLIT_PLAN differs from the current hash-pinned split plan")
    frontier = split.verify_frontier(split_run_dir, split_plan_ref)
    if frontier[2] != frozen.M:
        fail(f"transient census M={frontier[2]}, expected frozen M={frozen.M}")
    children = split.verify_all_children(split_run_dir, split_plan_ref, frozen.M)
    parent_46 = split.verify_parent_46(
        parent_run_dir, partitions, engine, parent_plan_ref
    )
    replacement_document = split.replacement_document(
        split_plan_ref, parent_plan_ref, frontier, children, parent_46
    )
    actual_replacement, replacement_ref = split.read_document(
        split_run_dir / "SPLIT_REPLACEMENT_RECEIPT.json", split_run_dir
    )
    if actual_replacement != replacement_document:
        fail("transient replacement receipt differs from strict recomputation")
    if provenance(parent_plan_ref) != frozen.PARENT_PLAN:
        fail("parent PLAN provenance differs from frozen pin")
    if provenance(split_plan_ref) != frozen.SPLIT_PLAN:
        fail("split PLAN provenance differs from frozen pin")
    if provenance(replacement_ref) != frozen.TRANSIENT_REPLACEMENT:
        fail("transient replacement provenance differs from frozen pin")
    if [item["nodes"] for item in children] != frozen.CHILD_NODES:
        fail("transient child node vector differs from frozen vector")
    return {
        "inputs": inputs,
        "partitions": partitions,
        "engine": engine,
        "parent_plan_ref": parent_plan_ref,
        "split_plan_ref": split_plan_ref,
        "frontier": frontier,
        "children": children,
        "parent_46": parent_46,
        "replacement_ref": replacement_ref,
    }


def export_direct(
    stage: Path,
    parent_run_dir: Path,
    partitions: list[dict[str, Any]],
    parent_46: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    indexed = {item["key"]: item for item in parent_46}
    entries: list[dict[str, Any]] = []
    for logical_index, item in enumerate(partitions):
        if item["key"] == split.TARGET_KEY:
            continue
        result = indexed.get(item["key"])
        if result is None:
            fail(f"missing verified direct result for {item['key']}")
        transient_receipt_path = Path(result["receipt"]["path"])
        transient_receipt, transient_ref = base.verify_receipt_file(
            transient_receipt_path
        )
        source_dir = transient_receipt_path.parent
        directory = f"direct/{item['mode']}__{item['partition']}"
        stdout_ref = copy_raw_new(source_dir / "stdout.txt", stage, f"{directory}/stdout.txt")
        stderr_ref = copy_raw_new(source_dir / "stderr.txt", stage, f"{directory}/stderr.txt")
        fields = frozen.parse_result(stage.joinpath(stdout_ref["path"]).read_bytes(), item["key"])
        if fields != transient_receipt.get("result_fields"):
            fail(f"transient/reparsed RESULT mismatch for {item['key']}")
        receipt = {
            "schema": frozen.DIRECT_SCHEMA,
            "status": "PASS",
            "kind": "direct",
            "logical_index": logical_index,
            "key": item["key"],
            "mode": item["mode"],
            "partition": item["partition"],
            "argv_tail": item["argv_tail"],
            "expected": {
                "exit_code": 0,
                "status": "ZERO",
                "nodes": item["expected_nodes"],
                "solution_topologies": 0,
                "frontier": 0,
            },
            "observed": {"exit_code": transient_receipt["exit_code"], "result_fields": fields},
            "bindings": bindings(False),
            "transient_receipt_provenance": provenance(transient_ref),
            "stdout": stdout_ref,
            "stderr": stderr_ref,
        }
        receipt_relative = f"{directory}/RECEIPT.json"
        receipt_ref = write_json_new(stage, receipt_relative, receipt)
        entries.append(
            {
                "logical_index": logical_index,
                "key": item["key"],
                "expected_nodes": item["expected_nodes"],
                "receipt": receipt_ref,
            }
        )
    if len(entries) != 46 or sum(item["expected_nodes"] for item in entries) != frozen.DIRECT_NODE_SUM:
        fail("released direct roster/count/node sum mismatch")
    return entries


def export_frontier(
    stage: Path,
    split_run_dir: Path,
    frontier: tuple[dict[str, Any], dict[str, Any], int],
) -> dict[str, Any]:
    transient, transient_ref, child_count = frontier
    if child_count != frozen.M:
        fail("frontier child count changed before export")
    transient_receipt_path = split_run_dir / transient_ref["path"]
    source_dir = transient_receipt_path.parent
    stdout_ref = copy_raw_new(source_dir / "stdout.txt", stage, "split/frontier/stdout.txt")
    stderr_ref = copy_raw_new(source_dir / "stderr.txt", stage, "split/frontier/stderr.txt")
    fields = frozen.parse_result(stage.joinpath(stdout_ref["path"]).read_bytes(), "split frontier")
    if fields != transient["result_fields"]:
        fail("frontier transient/reparsed RESULT mismatch")
    receipt = {
        "schema": frozen.FRONTIER_SCHEMA,
        "status": "PASS",
        "kind": "frontier_census",
        "logical_key": split.TARGET_KEY,
        "argv_tail": split.FRONTIER_ARGV_TAIL,
        "expected": {
            "exit_code": 0,
            "status": "FRONTIER",
            "nodes": 25,
            "solution_topologies": 0,
            "child_count": frozen.M,
        },
        "observed": {"exit_code": transient["exit_code"], "result_fields": fields},
        "bindings": bindings(True),
        "transient_receipt_provenance": provenance(transient_ref),
        "stdout": stdout_ref,
        "stderr": stderr_ref,
    }
    return write_json_new(stage, "split/frontier/RECEIPT.json", receipt)


def export_children(
    stage: Path,
    split_run_dir: Path,
    children: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    entries: list[dict[str, Any]] = []
    for index, child in enumerate(children):
        if child["index"] != index or child["nodes"] != frozen.CHILD_NODES[index]:
            fail(f"verified child roster/node mismatch at k={index}")
        transient_receipt_path = split_run_dir / child["receipt"]["path"]
        transient, transient_ref = split.read_document(
            transient_receipt_path, split_run_dir
        )
        source_dir = transient_receipt_path.parent
        directory = f"split/children/k_{index:03d}"
        stdout_ref = copy_raw_new(source_dir / "stdout.txt", stage, f"{directory}/stdout.txt")
        stderr_ref = copy_raw_new(source_dir / "stderr.txt", stage, f"{directory}/stderr.txt")
        fields = frozen.parse_result(stage.joinpath(stdout_ref["path"]).read_bytes(), f"split child {index}")
        if fields != transient["result_fields"] or fields != child["result_fields"]:
            fail(f"child transient/reparsed RESULT mismatch at k={index}")
        receipt = {
            "schema": frozen.CHILD_SCHEMA,
            "status": "PASS",
            "kind": "split_child",
            "logical_key": split.TARGET_KEY,
            "child_index": index,
            "argv_tail": split.child_argv_tail(index),
            "expected": {
                "exit_code": 0,
                "status": "ZERO",
                "nodes": child["nodes"],
                "solution_topologies": 0,
                "frontier": 0,
            },
            "observed": {"exit_code": transient["exit_code"], "result_fields": fields},
            "bindings": bindings(True),
            "transient_receipt_provenance": provenance(transient_ref),
            "stdout": stdout_ref,
            "stderr": stderr_ref,
        }
        receipt_relative = f"{directory}/RECEIPT.json"
        receipt_ref = write_json_new(stage, receipt_relative, receipt)
        entries.append({"index": index, "nodes": child["nodes"], "receipt": receipt_ref})
    if [item["nodes"] for item in entries] != frozen.CHILD_NODES:
        fail("released child node vector mismatch")
    return entries


def build_run_result(
    direct: list[dict[str, Any]],
    census_ref: dict[str, Any],
    children: list[dict[str, Any]],
) -> dict[str, Any]:
    return {
        "schema": frozen.RUN_RESULT_SCHEMA,
        "status": "PASS",
        "release_schema": frozen.RELEASE_SCHEMA,
        "engine_sha256": frozen.ENGINE_SHA256,
        "logical_partition_count": 47,
        "logical_node_sum": frozen.LOGICAL_NODE_SUM,
        "logical_roster": frozen.roster(),
        "direct_partition_count": 46,
        "direct_node_sum": frozen.DIRECT_NODE_SUM,
        "direct_receipts": direct,
        "split_replacement": {
            "logical_index": 46,
            "key": split.TARGET_KEY,
            "expected_nodes": frozen.TARGET_NODES,
            "census_receipt": census_ref,
            "child_count": frozen.M,
            "child_indices": list(range(frozen.M)),
            "children": children,
            "child_reported_node_sum": frozen.CHILD_NODE_SUM,
            "repeated_prefix_calls_per_child": 3,
            "normalization_subtraction": frozen.NORMALIZATION_SUBTRACTION,
            "normalized_parent_nodes": frozen.TARGET_NODES,
            "node_identity": "parent_nodes=sum(child_nodes)-3*(M-1)",
        },
        "physical_zero_process_count": 46 + frozen.M,
        "frontier_census_process_count": 1,
    }


def build_release(workspace: Path, run_result_ref: dict[str, Any]) -> dict[str, Any]:
    source_inputs = frozen.expected_sources(workspace)
    tooling = frozen.expected_tooling(workspace)
    executable = frozen.workspace_ref(workspace, frozen.ENGINE_RELATIVE)
    if executable["sha256"] != frozen.ENGINE_SHA256:
        fail("preserved executable changed before release construction")
    return {
        "schema": frozen.RELEASE_SCHEMA,
        "status": "PASS",
        "scope": "fresh Config3/A2 evidence: 46 direct logical partitions plus a split replacement for a2_separate|path_8_14",
        "evidence_origin": "freshly generated for this proof; not the missing original raw archive",
        "engine": {
            "name": "preserved",
            "kind": "hash-pinned-historical-production-binary",
            "executable": executable,
            "source_claim": "historical package binding; not a reproducible-build proof",
        },
        "source_inputs": source_inputs,
        "tooling": tooling,
        "parent_plan_provenance": frozen.PARENT_PLAN,
        "split_plan_provenance": frozen.SPLIT_PLAN,
        "transient_replacement_provenance": frozen.TRANSIENT_REPLACEMENT,
        "common_flags": frozen.COMMON_FLAGS,
        "logical_roster": frozen.roster(),
        "counts": frozen.expected_counts(),
        "split_proof": frozen.expected_split_proof(),
        "run_result": run_result_ref,
    }


def write_manifest(stage: Path) -> dict[str, Any]:
    paths = sorted(
        path.relative_to(stage).as_posix()
        for path in stage.rglob("*")
        if path.is_file()
    )
    if "MANIFEST.sha256" in paths:
        fail("staging manifest unexpectedly exists before manifest construction")
    raw = "".join(f"{frozen.sha256_file(stage / relative)}  {relative}\n" for relative in paths).encode("ascii")
    write_bytes_new(stage / "MANIFEST.sha256", raw)
    return frozen.portable_ref(stage / "MANIFEST.sha256", "MANIFEST.sha256")


def export(
    workspace: Path,
    parent_run_dir: Path,
    split_run_dir: Path,
    release_root: Path,
) -> dict[str, str]:
    workspace = workspace.resolve(strict=True)
    parent_run_dir = parent_run_dir.resolve(strict=True)
    split_run_dir = split_run_dir.resolve(strict=True)
    release_root = release_root.resolve(strict=False)
    if release_root.exists():
        fail(f"refusing to overwrite existing frozen release: {release_root}")
    evidence_parent = release_root.parent
    evidence_parent.mkdir(parents=True, exist_ok=True)
    stage = evidence_parent / f".{release_root.name}.staging"
    if stage.exists():
        fail(f"staging directory already exists; preserve/audit it manually: {stage}")

    transient = load_transient(workspace, parent_run_dir, split_run_dir)
    stage.mkdir(parents=False, exist_ok=False)
    direct = export_direct(
        stage,
        parent_run_dir,
        transient["partitions"],
        transient["parent_46"],
    )
    census_ref = export_frontier(stage, split_run_dir, transient["frontier"])
    child_entries = export_children(stage, split_run_dir, transient["children"])
    run_result = build_run_result(direct, census_ref, child_entries)
    run_result_ref = write_json_new(stage, "RUN_RESULT.json", run_result)
    release = build_release(workspace, run_result_ref)
    write_json_new(stage, "RELEASE.json", release)
    write_manifest(stage)

    preflight = frozen.verify_release(stage)
    os.replace(stage, release_root)
    final = frozen.verify_release(release_root)
    if final != preflight:
        fail("frozen release digests changed during atomic publication")
    return final


def build_parser() -> argparse.ArgumentParser:
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", default=str(here.parents[1]))
    parser.add_argument("--parent-run-dir", default=str(here / ".run" / "full_preserved_v1"))
    parser.add_argument("--split-run-dir", default=str(here / ".run" / "path8_14_split_v1"))
    parser.add_argument("--release-root", default=str(here / "evidence" / "full_preserved_v1"))
    return parser


def main() -> int:
    args = build_parser().parse_args()
    try:
        result = export(
            Path(args.workspace),
            Path(args.parent_run_dir),
            Path(args.split_run_dir),
            Path(args.release_root),
        )
    except (base.HarnessError, frozen.VerifyError, OSError, ValueError) as exc:
        print(f"CONFIG3_A2_FROZEN_SPLIT_EXPORT_FAIL: {exc}", file=sys.stderr)
        return 2
    print(
        f"{EXPORT_MARKER} schema={frozen.RELEASE_SCHEMA} logical_partitions=47 "
        f"direct=46 children=22 logical_nodes={frozen.LOGICAL_NODE_SUM} "
        f"manifest_sha256={result['manifest_sha256']} "
        f"release_sha256={result['release_sha256']} "
        f"run_result_sha256={result['run_result_sha256']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
