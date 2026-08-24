#!/usr/bin/env python3
"""Replay the two sealed calibration packages and make the exact terminal plan."""

from __future__ import annotations

import argparse
import contextlib
import hashlib
import importlib.util
import io
import json
import os
import shutil
import stat
import sys
import tarfile
import tempfile
from fractions import Fraction
from pathlib import Path, PurePosixPath
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Set, Tuple

# Package replay dynamically imports hash-bound provenance sources.  It must
# never create bytecode caches in either frozen source or sealed packages.
sys.dont_write_bytecode = True
os.environ["PYTHONDONTWRITEBYTECODE"] = "1"

import g001_terminal5_common_v1 as common


COMPAT_NAME = ("c157_resume861_collect_compat_v2r1_20260818T160902Z/"
               "collect_g001_c157_job376839_resume861_prior_provenance_compat_v2.py")
RECOVERY_NAME = "g001_config4_p2_heavy16_job377045_recovery_v1.py"
LEAF_COMMON = "g001_remaining_leaf_common.py"
LEAF_WORKER = "g001_remaining_leaf_worker.py"
LEAF_COLLECTOR = "g001_remaining_leaf_collect.py"


def load_module(path: Path, name: str) -> Any:
    specification = importlib.util.spec_from_file_location(name, str(path))
    if specification is None or specification.loader is None:
        raise common.TerminalError(f"cannot load module {path}")
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


def check_bound_archive(path: Path, binding: Mapping[str, Any], label: str) -> Path:
    path = path.resolve(strict=True)
    if path.name != binding["name"]:
        raise common.TerminalError(f"{label} archive basename mismatch")
    info = path.stat()
    if not stat.S_ISREG(info.st_mode) or path.is_symlink() or info.st_nlink != 1:
        raise common.TerminalError(f"{label} archive is not a single-link regular file")
    if info.st_size != binding["bytes"] or common.sha256_file(path) != binding["sha256"]:
        raise common.TerminalError(f"{label} archive hash/size mismatch")
    return path


def audit_archive_matches_package(archive: Path, package: Path,
                                  expected_root: str, label: str) -> None:
    """Stream-check a safe archive against the already published package tree."""
    package = common.require_directory(package, f"{label} package")
    if package.name != expected_root:
        raise common.TerminalError(f"{label} package basename mismatch")
    observed: Set[str] = set()
    with tarfile.open(archive, "r:gz") as stream:
        for member in stream:
            pure = PurePosixPath(member.name)
            if (pure.is_absolute() or not pure.parts or ".." in pure.parts or
                    pure.parts[0] != expected_root):
                raise common.TerminalError(f"unsafe {label} archive member: {member.name}")
            relative = PurePosixPath(*pure.parts[1:]).as_posix()
            if relative in ("", "."):
                if not member.isdir():
                    raise common.TerminalError(f"{label} archive root is not a directory")
                continue
            if member.isdir():
                continue
            if not member.isfile() or member.issym() or member.islnk():
                raise common.TerminalError(f"{label} archive has a non-regular member")
            if relative in observed:
                raise common.TerminalError(f"{label} archive has duplicate member {relative}")
            observed.add(relative)
            target = package.joinpath(*PurePosixPath(relative).parts)
            raw = common.read_regular(target, f"{label} package member")
            if len(raw) != member.size:
                raise common.TerminalError(f"{label} archive/package size mismatch: {relative}")
            extracted = stream.extractfile(member)
            if extracted is None:
                raise common.TerminalError(f"cannot stream {label} member: {relative}")
            digest = hashlib.sha256()
            for block in iter(lambda: extracted.read(1024 * 1024), b""):
                digest.update(block)
            if digest.hexdigest() != common.sha256_bytes(raw):
                raise common.TerminalError(f"{label} archive/package hash mismatch: {relative}")
    actual: Set[str] = set()
    for path in package.rglob("*"):
        info = path.lstat()
        if stat.S_ISLNK(info.st_mode):
            raise common.TerminalError(f"{label} package contains a symlink")
        if stat.S_ISREG(info.st_mode):
            if info.st_nlink != 1:
                raise common.TerminalError(f"{label} package contains a hard-linked file")
            actual.add(path.relative_to(package).as_posix())
        elif not stat.S_ISDIR(info.st_mode):
            raise common.TerminalError(f"{label} package contains a special file")
    if actual != observed:
        raise common.TerminalError(
            f"{label} archive/package exact-set mismatch: missing={len(actual-observed)} extra={len(observed-actual)}")


def verify_package_anchors(package: Path, binding: Mapping[str, Any], label: str) -> None:
    for name, key in (("aggregate.json", "aggregate_sha256"),
                      ("package_receipt.json", "receipt_sha256"),
                      ("collection_artifacts.sha256", "manifest_sha256")):
        if common.sha256_file(package / name) != binding[key]:
            raise common.TerminalError(f"{label} package anchor mismatch: {name}")


def export_c157(package: Path, source_dir: Path) -> List[Dict[str, Any]]:
    compat = load_module(source_dir / COMPAT_NAME, "_terminal5_c157_compat")
    frozen_source, _ = compat.bootstrap_frozen_source(
        ["--verify-package", str(package)])
    collector = compat.load_frozen_collector(frozen_source)
    compat.install_compatibility(collector)
    post = collector.verify_package(package)
    if (post.get("exit_code") != 0 or not post.get("merged_exact") or
            post.get("terminal_search_result") is not False):
        raise common.TerminalError("C157 packaged replay is not exact calibration evidence")
    merge = collector.merge
    frozen_common = collector.common
    strict = collector.strict
    raw_archive = package / "prior_archives" / merge.PRIOR_RAW_ARCHIVE
    compact_archive = package / "prior_archives" / merge.PRIOR_COMPACT_ARCHIVE
    with tempfile.TemporaryDirectory(prefix=".terminal5-c157-export-") as temporary_name:
        temporary = Path(temporary_name)
        raw_root = temporary / "raw"
        compact_root = temporary / "compact"
        collector.extract_regular_tar(raw_archive, raw_root)
        collector.extract_regular_tar(compact_archive, compact_root)
        prior_matrix = (raw_root / "c157_adaptive_matrix_v1_runs" /
                        frozen_common.plan_verify.MATRIX_BASENAME)
        prior_source = compat.canonical_prior_source(prior_matrix)
        prior = merge.load_pristine_prior_verifier(prior_source)
        prior_leaves: Dict[Tuple[int, Tuple[int, ...]], Mapping[str, Any]] = {}
        original_targets: Set[Tuple[int, Tuple[int, ...]]] = set()
        for index in range(16):
            with contextlib.redirect_stdout(io.StringIO()):
                report = prior.verify_shard(prior_matrix / f"shard_{index:02d}", False)
            for key in prior._target_map(report["plan"], index):
                normalized = (int(key[0]), tuple(key[1]))
                if normalized in original_targets:
                    raise common.TerminalError("C157 original target repeated")
                original_targets.add(normalized)
            for item in report["reconstruction"]["valid_leaves"]:
                key = (int(item["user_configuration"]), tuple(item["path"]))
                if key in prior_leaves:
                    raise common.TerminalError("C157 prior valid leaf repeated")
                prior_leaves[key] = item
        continuation = strict.verify_matrix(package / "matrix", require_complete=True)
        continuation_leaves: Dict[Tuple[int, Tuple[int, ...]], Mapping[str, Any]] = {}
        for item in continuation["valid_leaves"]:
            key = (int(item["user_configuration"]), tuple(item["path"]))
            if key in continuation_leaves or key in prior_leaves:
                raise common.TerminalError("C157 continuation leaf repeated")
            continuation_leaves[key] = item
        base_leaves = prior.common.build_base_partition(
            prior_matrix / "shard_00/prior/v1", prior_matrix / "shard_00/prior/v2")
        untouched = {
            (int(leaf.user_configuration), tuple(leaf.path)): leaf
            for leaf in base_leaves
            if (int(leaf.user_configuration), tuple(leaf.path)) not in original_targets
        }
        if any(leaf.outcome != "VALID" for leaf in untouched.values()):
            raise common.TerminalError("C157 untouched partition contains non-valid leaf")
        final_keys = set(untouched) | set(prior_leaves) | set(continuation_leaves)
        common.assert_prefix_free(final_keys, "C157 exported partition")
        records: List[Dict[str, Any]] = []
        for configuration, path in sorted(final_keys):
            if (configuration, path) in untouched:
                item = untouched[(configuration, path)]
                frontier = int(item.frontier or 0)
                source_id = str(getattr(item, "run_id", f"untouched:{common.path_text(path)}"))
                kind = "c157_untouched_base"
            elif (configuration, path) in prior_leaves:
                item = prior_leaves[(configuration, path)]
                frontier = int(item["frontier"])
                source_id = str(item.get("run_id", f"prior:{common.path_text(path)}"))
                kind = "c157_preserved_adaptive"
            else:
                item = continuation_leaves[(configuration, path)]
                frontier = int(item["frontier"])
                source_id = str(item.get("run_id", f"continuation:{common.path_text(path)}"))
                kind = "c157_continuation_adaptive"
            records.append({
                "configuration": configuration, "path": path,
                "classification": "SEARCH", "weight": frontier,
                "evidence": {"source": "C157", "kind": kind,
                             "calibration_depth": 12,
                             "calibration_frontier": frontier,
                             "source_id": source_id},
            })
    counts = {config: sum(item["configuration"] == config for item in records)
              for config in (1, 5, 6, 7)}
    if counts != {1: 5176, 5: 25254, 6: 3977, 7: 3299} or len(records) != 37706:
        raise common.TerminalError(f"C157 exported count mismatch: {counts}")
    return records


def export_config4(package: Path) -> List[Dict[str, Any]]:
    recovery_source = package / "provenance" / "g001_config4_p2_heavy16_job377045_recovery_v1"
    recovery = load_module(recovery_source / RECOVERY_NAME, "_terminal5_config4_recovery")
    report = recovery.verify_package(package, recovery_source)
    if (not report.get("recovery_complete") or report.get("unresolved") != [] or
            not report.get("matrix_audit", {}).get("exact")):
        raise common.TerminalError("Config4 packaged replay is not exact calibration evidence")
    plan = common.read_json(package / "matrix/shard_00/plan_snapshot.json", "Config4 plan")
    base = {tuple(item["path"]): item for item in plan["p2_partition"]["leaves"]}
    targets = {tuple(item["path"]) for item in plan["heavy16"]["targets"]}
    preserved_zero = {tuple(item) for item in plan["p2_partition"]["preserved_zero_paths"]}
    descendants: Dict[Tuple[int, ...], Mapping[str, Any]] = {}
    discharged: Set[Tuple[int, ...]] = set()
    for index in range(4):
        summary = common.read_json(package / f"matrix/shard_{index:02d}/summary.json",
                                   "Config4 shard summary")
        reconstruction = summary["reconstruction"]
        if not reconstruction["exact"]:
            raise common.TerminalError("Config4 shard reconstruction is not exact")
        for item in reconstruction["descendant_leaves"]:
            path = tuple(item["path"])
            if path in descendants:
                raise common.TerminalError("Config4 descendant repeated")
            descendants[path] = item
        for replacement in reconstruction["replacement_records"]:
            for text in replacement["zero_subtrees"]:
                path = tuple(int(part) for part in text.split(","))
                if path in discharged:
                    raise common.TerminalError("Config4 discharged zero repeated")
                discharged.add(path)
    surviving = (set(base) - targets) | set(descendants)
    partition = surviving | discharged
    common.assert_prefix_free(
        ((4, path) for path in partition),
        "Configuration 4 exported partition",
    )
    if (len(surviving) != 1307 or len(preserved_zero) != 13 or len(discharged) != 17 or
            len(partition) != 1324 or not preserved_zero.issubset(surviving)):
        raise common.TerminalError("Config4 final partition arithmetic mismatch")
    records: List[Dict[str, Any]] = []
    for path in sorted(partition):
        if path in discharged:
            classification = "CERTIFIED_ZERO"
            kind = "config4_discharged_zero"
            frontier = 0
            depth = 15
            source_id = "discharged:" + common.path_text(path)
        elif path in preserved_zero:
            item = base[path]
            classification = "CERTIFIED_ZERO"
            kind = "config4_preserved_zero"
            frontier = int(item.get("frontier", 0))
            depth = int(item.get("calibration_depth", 12))
            source_id = str(item.get("source_run_id", "preserved:" + common.path_text(path)))
        elif path in descendants:
            item = descendants[path]
            classification = "SEARCH"
            kind = "config4_depth15_descendant"
            frontier = int(item["frontier"])
            depth = 15
            source_id = str(item["run_id"])
        else:
            item = base[path]
            classification = "SEARCH"
            kind = "config4_retained_p2"
            frontier = int(item["frontier"])
            depth = int(item["calibration_depth"])
            source_id = str(item["source_run_id"])
        records.append({
            "configuration": 4, "path": path,
            # Config4 mixes calibration depths 12, 13, and 15.  Its raw
            # frontier values are therefore not comparable load measures.
            # Count-balance this small branch; retain the frontier only as
            # descriptive evidence.
            "classification": classification,
            "weight": 1 if classification == "SEARCH" else 0,
            "evidence": {"source": "CONFIG4", "kind": kind,
                         "calibration_depth": depth,
                         "calibration_frontier": frontier,
                         "source_id": source_id},
        })
    if (sum(item["classification"] == "SEARCH" for item in records) != 1294 or
            sum(item["classification"] == "CERTIFIED_ZERO" for item in records) != 30):
        raise common.TerminalError("Config4 search/zero classification mismatch")
    return records


def assign_bundles(records: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    provisional: List[Tuple[int, int, int, Dict[str, Any], List[Dict[str, Any]]]] = []
    for configuration in (1, 4, 5, 6, 7):
        count = common.EXPECTED_BUNDLES[configuration]
        buckets: List[List[Dict[str, Any]]] = [[] for _ in range(count)]
        totals = [0] * count
        search = [item for item in records
                  if item["configuration"] == configuration and
                  item["classification"] == "SEARCH"]
        search.sort(key=lambda item: (-max(1, item["weight"]), tuple(item["path"])))
        for item in search:
            bucket = min(range(count), key=lambda index: (totals[index], len(buckets[index]), index))
            buckets[bucket].append(item)
            totals[bucket] += max(1, item["weight"])
        if any(not bucket for bucket in buckets):
            raise common.TerminalError(f"configuration {configuration} has an empty bundle")
        for local_index, bucket in enumerate(buckets):
            bucket.sort(key=lambda item: tuple(item["path"]))
            bundle_id = f"c{configuration}_b{local_index:03d}"
            descriptor = {
                "schema": common.BUNDLE_SCHEMA,
                "bundle_id": bundle_id,
                "bundle_index": -1,
                "configuration": configuration,
                "record_ids": [item["record_id"] for item in bucket],
                "search_count": len(bucket),
                "weight_sum": totals[local_index],
            }
            provisional.append((local_index, count, configuration, descriptor, bucket))
    # Interleave configurations by normalized local progress.  The first
    # scheduler wave therefore represents all five branches instead of
    # consuming one configuration contiguously.
    provisional.sort(key=lambda item: (Fraction(item[0], item[1]), item[2]))
    bundles: List[Dict[str, Any]] = []
    for next_index, (_local, _count, _configuration, descriptor, bucket) in enumerate(provisional):
        descriptor["bundle_index"] = next_index
        for item in bucket:
            item["bundle_index"] = next_index
        bundles.append(descriptor)
    return bundles


def relative_binding(workspace: Path, path: Path) -> Dict[str, str]:
    path = path.resolve(strict=True)
    try:
        relative = path.relative_to(workspace).as_posix()
    except ValueError as error:
        raise common.TerminalError(f"bound artifact is outside workspace: {path}") from error
    return {"path": relative, "sha256": common.sha256_file(path)}


def make_leaf_plan(plan_id: str, bundle: Mapping[str, Any],
                   records: Mapping[str, Mapping[str, Any]], runtime: Mapping[str, Any]) -> Dict[str, Any]:
    bindings = runtime["bindings"]
    leaves = []
    for record_id in bundle["record_ids"]:
        record = records[record_id]
        path = list(record["path"])
        leaves.append({
            "leaf_id": record_id,
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
        })
    return {
        "schema": "G001_REMAINING_LEAF_PLAN_V1",
        "plan_id": f"{plan_id}.{bundle['bundle_id']}",
        "pipeline_artifacts": runtime["pipeline_artifacts"],
        "leaves": leaves,
    }


def write_new(path: Path, raw: bytes, mode: int = 0o444) -> None:
    descriptor = os.open(str(path), os.O_WRONLY | os.O_CREAT | os.O_EXCL, mode)
    try:
        with os.fdopen(descriptor, "wb", closefd=False) as stream:
            stream.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
    finally:
        os.close(descriptor)


def build_plan(c157_archive: Path, c157_package: Path, config4_archive: Path,
               config4_package: Path, workspace: Path, source_dir: Path,
               runtime_dir: Path, output: Path, plan_id: str,
               audit_archive_identity: bool = True) -> Dict[str, Any]:
    workspace = common.require_directory(workspace, "workspace")
    source_dir = common.require_directory(source_dir, "frozen source")
    runtime_dir = common.require_directory(runtime_dir, "sealed runtime")
    output = Path(os.path.abspath(os.fspath(output)))
    if output.exists() or output.is_symlink():
        raise common.TerminalError("plan output already exists")
    c157_archive = check_bound_archive(c157_archive, common.C157_ARCHIVE, "C157")
    config4_archive = check_bound_archive(config4_archive, common.CONFIG4_ARCHIVE, "Config4")
    c157_package = common.require_directory(c157_package, "C157 package")
    config4_package = common.require_directory(config4_package, "Config4 package")
    verify_package_anchors(c157_package, common.C157_ARCHIVE, "C157")
    verify_package_anchors(config4_package, common.CONFIG4_ARCHIVE, "Config4")
    if audit_archive_identity:
        audit_archive_matches_package(c157_archive, c157_package,
                                      common.C157_ARCHIVE["package"], "C157")
        audit_archive_matches_package(config4_archive, config4_package,
                                      common.CONFIG4_ARCHIVE["package"], "Config4")
    records = export_c157(c157_package, source_dir) + export_config4(config4_package)
    records.sort(key=lambda item: (item["configuration"], tuple(item["path"])))
    for item in records:
        token = f"{item['configuration']}:{common.path_text(item['path'])}:{item['classification']}"
        item["record_id"] = "c{}_{}_{}".format(
            item["configuration"], "s" if item["classification"] == "SEARCH" else "z",
            hashlib.sha256(token.encode("ascii")).hexdigest()[:24])
        item["schema"] = common.RECORD_SCHEMA
        item["mode"] = common.CONFIGURATION_TO_MODE[item["configuration"]]
        item["path_text"] = common.path_text(item["path"])
        item["path"] = list(item["path"])
        item["bundle_index"] = None
    bundles = assign_bundles(records)
    runtime_freeze = common.read_json(runtime_dir / "runtime_freeze.json", "runtime freeze")
    if (runtime_freeze.get("schema") != "G001_TERMINAL5_RUNTIME_FREEZE_V1" or
            runtime_freeze.get("terminal_policy", {}).get("stop_depth", "bad") is not None):
        raise common.TerminalError("sealed runtime policy mismatch")
    runtime = {
        "workers_per_bundle": common.WORKERS_PER_BUNDLE,
        "cpus_per_bundle": common.CPUS_PER_BUNDLE,
        "bundle_count": common.TOTAL_BUNDLES,
        "solver_setting": "exact6",
        "multi_edge_cover_validate": "OFF",
        "bindings": {
            "solver_source": relative_binding(workspace, source_dir / "g001_remaining_witness_solver.cpp"),
            "solver_executable": relative_binding(workspace, runtime_dir / "bin/g001_remaining_witness_solver"),
            "checker_source": relative_binding(workspace, source_dir / "check_g001_leech_witness.cpp"),
            "checker_executable": relative_binding(workspace, runtime_dir / "bin/check_g001_leech_witness"),
            "runtime_freeze": relative_binding(workspace, runtime_dir / "runtime_freeze.json"),
        },
        "pipeline_artifacts": {
            "leaf_worker": relative_binding(workspace, source_dir / LEAF_WORKER),
            "leaf_common": relative_binding(workspace, source_dir / LEAF_COMMON),
            "leaf_collector": relative_binding(workspace, source_dir / LEAF_COLLECTOR),
        },
    }
    invariants = {
        "record_count": common.TOTAL_RECORDS,
        "search_count": common.TOTAL_SEARCH,
        "certified_zero_count": common.TOTAL_ZERO,
        "records_by_configuration": {str(k): v for k, v in common.EXPECTED_RECORDS.items()},
        "search_by_configuration": {str(k): v for k, v in common.EXPECTED_SEARCH.items()},
        "zero_by_configuration": {str(k): v for k, v in common.EXPECTED_ZERO.items()},
        "bundles_by_configuration": {str(k): v for k, v in common.EXPECTED_BUNDLES.items()},
    }
    plan = {
        "schema": common.PLAN_SCHEMA,
        "plan_id": common.require_id(plan_id, "plan_id"),
        "inputs": {
            "c157": dict(common.C157_ARCHIVE),
            "config4": dict(common.CONFIG4_ARCHIVE),
            "selection_sha256": {str(k): v for k, v in common.SELECTION_HASHES.items()},
        },
        "runtime": runtime,
        "invariants": invariants,
        "claim_boundary": {
            "terminal_search": True,
            "found_requires_independent_checker": True,
            "found_report_immediately": True,
            "global_zero_requires_all_receipts": True,
            "timeouts_are_non_evidence": True,
            "calibration_frontier_is_not_certificate": True,
        },
        "records": records,
        "bundles": bundles,
    }
    common.validate_plan(plan, production=True)
    private = Path(tempfile.mkdtemp(prefix=".terminal5-plan-", dir=str(output.parent)))
    try:
        bundle_dir = private / "bundle_plans"
        bundle_dir.mkdir(mode=0o700)
        write_new(private / "terminal_plan_v1.json", common.canonical_json(plan))
        by_id = {item["record_id"]: item for item in records}
        for bundle in bundles:
            leaf_plan = make_leaf_plan(plan_id, bundle, by_id, runtime)
            write_new(bundle_dir / f"bundle_{bundle['bundle_index']:03d}.json",
                      common.canonical_json(leaf_plan))
        manifest_lines = []
        artifact_files = [private / "terminal_plan_v1.json"] + sorted(bundle_dir.glob("*.json"))
        for path in artifact_files:
            manifest_lines.append(f"{common.sha256_file(path)}  {path.relative_to(private).as_posix()}\n")
        manifest_raw = "".join(manifest_lines).encode("ascii")
        write_new(private / "plan_artifacts.sha256", manifest_raw)
        receipt = {
            "schema": common.PLAN_RECEIPT_SCHEMA,
            "plan_id": plan_id,
            "plan_sha256": common.sha256_file(private / "terminal_plan_v1.json"),
            "manifest_sha256": common.sha256_bytes(manifest_raw),
            "record_count": common.TOTAL_RECORDS,
            "search_count": common.TOTAL_SEARCH,
            "certified_zero_count": common.TOTAL_ZERO,
            "bundle_count": common.TOTAL_BUNDLES,
            "archive_package_identity_audited": audit_archive_identity,
            "package_replay_exact": True,
            "terminal_search_performed": False,
        }
        write_new(private / "plan_receipt.json", common.canonical_json(receipt))
        os.rename(private, output)
        private = None
    finally:
        if private is not None and private.exists():
            shutil.rmtree(private, ignore_errors=True)
    return receipt


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--c157-archive", required=True, type=Path)
    parser.add_argument("--c157-package", required=True, type=Path)
    parser.add_argument("--config4-archive", required=True, type=Path)
    parser.add_argument("--config4-package", required=True, type=Path)
    parser.add_argument("--workspace", required=True, type=Path)
    parser.add_argument("--source-dir", required=True, type=Path)
    parser.add_argument("--runtime-dir", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--plan-id", required=True)
    parser.add_argument("--skip-archive-package-identity", action="store_true",
                        help="test-only; production receipt records this as false")
    args = parser.parse_args(argv)
    try:
        receipt = build_plan(
            args.c157_archive, args.c157_package, args.config4_archive,
            args.config4_package, args.workspace, args.source_dir,
            args.runtime_dir, args.output, args.plan_id,
            audit_archive_identity=not args.skip_archive_package_identity)
        if not receipt["archive_package_identity_audited"]:
            raise common.TerminalError("test-only archive identity skip cannot publish a production plan")
        print("G001_TERMINAL5_PLAN_V1_OK records=39030 search=39000 zero=30 bundles=192 sha256={}".format(
            receipt["plan_sha256"]))
        return 0
    except (common.TerminalError, OSError, ValueError, KeyError, tarfile.TarError) as error:
        print(f"G001_TERMINAL5_PLAN_V1_FAILED: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
