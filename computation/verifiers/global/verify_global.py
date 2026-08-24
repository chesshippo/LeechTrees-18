#!/usr/bin/env python3
"""Replay the frozen Terminal5 global collector after a filesystem relocation.

This is a path-virtualization adapter, not an independent search verifier.  It
does not edit the frozen collector, plans, receipts, launches, markers, or
expected global JSON.  It independently pins the exact frozen source tree,
then preserves the collector's content, schema, census, and hash checks while
intentionally replacing literal absolute-path identity with a checked mapping
from the relocated physical tree to the original POSIX workspace spelling.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import stat
import subprocess
import sys
from typing import Any, Mapping, Sequence


sys.dont_write_bytecode = True

LOGICAL_WORKSPACE = PurePosixPath(
    "/home1/aghodsi/leech18_remaining5_pilot_20260817_v1/"
    "g001_terminal5_candidate4_20260818T230000Z_workspace"
)
SOURCE_FREEZE_SHA256 = (
    "537fb0d163cc04e891d544d4e4accefdf5fdbb91cdbb20c54d05e4037abb852c"
)
SOURCE_CHECKSUM_SHA256 = (
    "8d9a3a2fd9fd7efae2d1e819861816f44ea79cf5c03217b7ade9514893b4068f"
)
GLOBAL_JSON_SHA256 = (
    "8c915a2ad6d6957740eb97bafb734603d59b5c0376704fd311ebfa6cb27d0eb5"
)
FREEZE_NAME = "g001_terminal5_source_freeze_v1.json"
CHECKSUM_NAME = "G001_TERMINAL5_PRODUCTION_V1_SHA256SUMS.txt"


class RelocationError(RuntimeError):
    """Raised when the relocation contract is not exact."""


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(4 * 1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def require_regular(path: Path, context: str) -> Path:
    if path.is_symlink() or not path.is_file():
        raise RelocationError(f"{context} is not a real regular file: {path}")
    return path


def require_directory(path: Path, context: str) -> Path:
    resolved = path.resolve(strict=True)
    if path.is_symlink() or not resolved.is_dir():
        raise RelocationError(f"{context} is not a real directory: {path}")
    return resolved


def require_same_path(actual: Path, expected: Path, context: str) -> None:
    if actual.resolve(strict=True) != expected.resolve(strict=True):
        raise RelocationError(
            f"{context} path mismatch: expected {expected}, got {actual}"
        )


def parse_checksum_manifest(raw: bytes) -> dict[str, str]:
    try:
        text = raw.decode("ascii", errors="strict")
    except UnicodeError as error:
        raise RelocationError("source checksum manifest is not ASCII") from error

    result: dict[str, str] = {}
    for line in text.splitlines():
        parts = line.split("  ")
        if len(parts) != 2:
            raise RelocationError("malformed source checksum line")
        digest, name = parts
        relative = PurePosixPath(name)
        if (
            len(digest) != 64
            or any(character not in "0123456789abcdef" for character in digest)
            or not name
            or relative.is_absolute()
            or ".." in relative.parts
            or relative.as_posix() != name
            or name in result
        ):
            raise RelocationError("malformed/duplicate source checksum line")
        result[name] = digest
    return result


def verify_source_freeze(source_dir: Path) -> None:
    freeze = require_regular(
        source_dir / FREEZE_NAME, "source freeze"
    )
    checksums = require_regular(
        source_dir / CHECKSUM_NAME,
        "source checksum manifest",
    )
    freeze_raw = freeze.read_bytes()
    checksum_raw = checksums.read_bytes()
    if hashlib.sha256(freeze_raw).hexdigest() != SOURCE_FREEZE_SHA256:
        raise RelocationError("source-freeze JSON digest mismatch")
    if hashlib.sha256(checksum_raw).hexdigest() != SOURCE_CHECKSUM_SHA256:
        raise RelocationError("source checksum-manifest digest mismatch")

    manifest = parse_checksum_manifest(checksum_raw)
    if set(manifest) == set() or FREEZE_NAME not in manifest:
        raise RelocationError("source checksum manifest has no frozen source set")
    if manifest[FREEZE_NAME] != SOURCE_FREEZE_SHA256:
        raise RelocationError("source checksum manifest does not pin the freeze JSON")

    try:
        freeze_record = json.loads(freeze_raw.decode("utf-8", errors="strict"))
    except (UnicodeError, json.JSONDecodeError) as error:
        raise RelocationError("source-freeze JSON is not canonical JSON data") from error
    if not isinstance(freeze_record, dict):
        raise RelocationError("source-freeze JSON is not an object")
    distribution = freeze_record.get("distribution_files")
    if not isinstance(distribution, dict):
        raise RelocationError("source-freeze distribution map is missing")
    if freeze_record.get("distribution_count") != len(distribution):
        raise RelocationError("source-freeze distribution count mismatch")
    expected_distribution = dict(manifest)
    del expected_distribution[FREEZE_NAME]
    if distribution != expected_distribution:
        raise RelocationError("source-freeze and checksum-manifest maps differ")

    expected_set = set(manifest) | {CHECKSUM_NAME}
    observed_set: set[str] = set()
    for item in source_dir.rglob("*"):
        info = item.lstat()
        if stat.S_ISLNK(info.st_mode):
            raise RelocationError("frozen source contains a symlink")
        if stat.S_ISDIR(info.st_mode):
            continue
        if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1:
            raise RelocationError(
                "frozen source contains a non-regular/single-link entry"
            )
        observed_set.add(item.relative_to(source_dir).as_posix())
    if observed_set != expected_set:
        raise RelocationError(
            "frozen source exact-set mismatch "
            f"missing={sorted(expected_set - observed_set)} "
            f"extra={sorted(observed_set - expected_set)}"
        )
    for name, expected_digest in manifest.items():
        item = require_regular(source_dir.joinpath(*PurePosixPath(name).parts), name)
        if sha256_file(item) != expected_digest:
            raise RelocationError(f"source checksum mismatch: {name}")

    verifier = require_regular(
        source_dir / "verify_g001_terminal5_source_freeze_v1.py",
        "source-freeze verifier",
    )
    environment = dict(os.environ)
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    environment["PYTHONUTF8"] = "1"
    completed = subprocess.run(
        [
            sys.executable,
            "-B",
            str(verifier),
            "--source-dir",
            str(source_dir),
        ],
        cwd=str(source_dir),
        env=environment,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    expected_marker = (
        "G001_TERMINAL5_SOURCE_FREEZE_V1_OK files=28 "
        f"freeze_sha256={SOURCE_FREEZE_SHA256} "
        f"checksum_sha256={SOURCE_CHECKSUM_SHA256}\n"
    ).encode("ascii")
    if completed.returncode != 0:
        raise RelocationError(
            f"source-freeze verifier exited {completed.returncode}"
        )
    accepted_stdout = (
        expected_marker,
        expected_marker.replace(b"\n", b"\r\n"),
    )
    if completed.stderr != b"" or completed.stdout not in accepted_stdout:
        raise RelocationError("source-freeze verifier output was not canonical")


def load_frozen_collector(source_dir: Path) -> Any:
    collector_path = require_regular(
        source_dir / "collect_g001_terminal5_results_v1.py",
        "frozen global collector",
    )
    common_name = "g001_terminal5_common_v1"
    common_path = require_regular(
        source_dir / f"{common_name}.py", "frozen terminal common"
    )
    saved_path = list(sys.path)
    saved_common = sys.modules.pop(common_name, None)
    try:
        sys.path.insert(0, str(source_dir))
        specification = importlib.util.spec_from_file_location(
            "_frozen_terminal5_global_collector", str(collector_path)
        )
        if specification is None or specification.loader is None:
            raise RelocationError("cannot load frozen global collector")
        module = importlib.util.module_from_spec(specification)
        specification.loader.exec_module(module)
        if Path(module.__file__).resolve(strict=True) != collector_path.resolve(
            strict=True
        ):
            raise RelocationError("frozen global collector import-path mismatch")
        imported_common = getattr(module, "common", None)
        imported_common_file = getattr(imported_common, "__file__", None)
        if imported_common_file is None or Path(imported_common_file).resolve(
            strict=True
        ) != common_path.resolve(strict=True):
            raise RelocationError("frozen terminal common import-path mismatch")
        return module
    finally:
        sys.path[:] = saved_path
        sys.modules.pop(common_name, None)
        if saved_common is not None:
            sys.modules[common_name] = saved_common


def logical_path(relative: str) -> str:
    candidate = PurePosixPath(relative)
    if candidate.is_absolute() or ".." in candidate.parts:
        raise RelocationError(f"unsafe frozen relative path: {relative}")
    return str(LOGICAL_WORKSPACE.joinpath(*candidate.parts))


def logicalize_bindings(bindings: Mapping[str, Any]) -> dict[str, Any]:
    result = copy.deepcopy(dict(bindings))
    for role, value in result.items():
        if role == "dependencies":
            for dependency in value:
                dependency["absolute_path"] = logical_path(dependency["path"])
        else:
            value["absolute_path"] = logical_path(value["path"])
    return result


def describe_difference(actual: Any, expected: Any, path: str = "$" ) -> str:
    """Return the first deterministic structural difference for diagnostics."""
    if type(actual) is not type(expected):
        return (
            f"{path}: type {type(actual).__name__} != "
            f"{type(expected).__name__}"
        )
    if isinstance(actual, dict):
        actual_keys = set(actual)
        expected_keys = set(expected)
        if actual_keys != expected_keys:
            return (
                f"{path}: keys missing={sorted(expected_keys - actual_keys)} "
                f"extra={sorted(actual_keys - expected_keys)}"
            )
        for key in sorted(actual_keys):
            difference = describe_difference(
                actual[key], expected[key], f"{path}.{key}"
            )
            if difference:
                return difference
        return ""
    if isinstance(actual, list):
        if len(actual) != len(expected):
            return f"{path}: length {len(actual)} != {len(expected)}"
        for index, (actual_item, expected_item) in enumerate(
            zip(actual, expected)
        ):
            difference = describe_difference(
                actual_item, expected_item, f"{path}[{index}]"
            )
            if difference:
                return difference
        return ""
    if actual != expected:
        return f"{path}: {actual!r} != {expected!r}"
    return ""


def install_relocation_adapter(
    global_collector: Any, physical_workspace: Path
) -> None:
    # Python 3.12 changed built-in sum() for floats from the left-to-right
    # arithmetic used by the frozen production runtime to compensated
    # summation.  The frozen global JSON binds the legacy result exactly.  Give
    # only this loaded collector module the historical operation; integer sums
    # are unchanged, and the final report still has to match byte-for-byte.
    def frozen_left_fold_sum(values: Any, start: Any = 0) -> Any:
        total = start
        for value in values:
            total = total + value
        return total

    global_collector.sum = frozen_left_fold_sum
    original_loader = global_collector.load_leaf_modules

    def patched_loader(source_dir: Path) -> tuple[Any, Any]:
        leaf_common, leaf_collector = original_loader(source_dir)

        original_verify_pipeline = leaf_common.verify_pipeline_artifacts
        original_verify_bound = leaf_common.verify_bound_artifacts
        original_resolved_argv = leaf_common.resolved_solver_argv

        def verify_pipeline(plan: Mapping[str, Any], workspace: Path) -> dict[str, Any]:
            physical = original_verify_pipeline(plan, workspace)
            return logicalize_bindings(physical)

        def verify_bound(leaf: Mapping[str, Any], workspace: Path) -> dict[str, Any]:
            physical = original_verify_bound(leaf, workspace)
            return logicalize_bindings(physical)

        def verify_executing(
            bindings: Mapping[str, Mapping[str, str]],
            expected_paths: Mapping[str, Path],
        ) -> None:
            for role, actual_path in expected_paths.items():
                if role not in bindings:
                    raise RelocationError(f"unknown executing pipeline role: {role}")
                relative = bindings[role]["path"]
                physical_bound = (physical_workspace / relative).resolve(strict=True)
                physical_actual = actual_path.resolve(strict=True)
                if physical_actual != physical_bound:
                    raise RelocationError(
                        f"executing {role} physical path mismatch: "
                        f"expected {physical_bound}, got {physical_actual}"
                    )

        def to_logical_physical_path(path: Path) -> PurePosixPath:
            try:
                relative = path.relative_to(physical_workspace)
            except ValueError as error:
                raise RelocationError(
                    f"runtime path is outside physical workspace: {path}"
                ) from error
            if ".." in relative.parts:
                raise RelocationError(f"unsafe runtime relative path: {relative}")
            return LOGICAL_WORKSPACE.joinpath(*relative.parts)

        def resolved_argv(
            leaf: Mapping[str, Any], bindings: Mapping[str, Any], witness: Path
        ) -> list[str]:
            return original_resolved_argv(
                leaf, bindings, to_logical_physical_path(witness)
            )

        leaf_common.verify_pipeline_artifacts = verify_pipeline
        leaf_common.verify_bound_artifacts = verify_bound
        leaf_common.verify_executing_pipeline = verify_executing
        leaf_common.resolved_solver_argv = resolved_argv

        # The leaf collector imported these names directly, so patch its globals
        # as well as the common module's attributes.
        leaf_collector.verify_pipeline_artifacts = verify_pipeline
        leaf_collector.verify_bound_artifacts = verify_bound
        leaf_collector.verify_executing_pipeline = verify_executing
        leaf_collector.resolved_solver_argv = resolved_argv
        return leaf_common, leaf_collector

    global_collector.load_leaf_modules = patched_loader


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", required=True, type=Path)
    parser.add_argument("--plan-dir", required=True, type=Path)
    parser.add_argument("--source-dir", required=True, type=Path)
    parser.add_argument("--run-root", required=True, type=Path)
    parser.add_argument("--expected-global-json", required=True, type=Path)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        workspace = require_directory(args.workspace, "physical workspace")
        plan_dir = require_directory(args.plan_dir, "physical plan directory")
        source_dir = require_directory(args.source_dir, "physical source directory")
        run_root = require_directory(args.run_root, "physical run root")
        expected_json = require_regular(
            args.expected_global_json, "expected global JSON"
        ).resolve(strict=True)

        require_same_path(
            plan_dir, workspace / "plan" / "terminal5_plan_v1", "plan"
        )
        require_same_path(source_dir, workspace / "source", "source")
        require_same_path(
            run_root, workspace / "production_run" / "production_v1", "run root"
        )
        if sha256_file(expected_json) != GLOBAL_JSON_SHA256:
            raise RelocationError("expected global JSON digest mismatch")

        verify_source_freeze(source_dir)
        collector = load_frozen_collector(source_dir)
        install_relocation_adapter(collector, workspace)
        report = collector.collect(plan_dir, workspace, source_dir, run_root, None)
        raw = collector.common.canonical_json(report)
        expected_raw = expected_json.read_bytes()
        if raw != expected_raw:
            expected_record = json.loads(
                expected_raw.decode("utf-8", errors="strict")
            )
            difference = describe_difference(report, expected_record)
            raise RelocationError(
                "recomputed canonical global report is not byte-identical to "
                "the preserved global JSON; "
                f"actual_sha256={hashlib.sha256(raw).hexdigest()}; "
                f"first_difference={difference or 'byte framing only'}"
            )
        if report.get("status") != "GLOBAL_ZERO_COMPLETE":
            raise RelocationError("recomputed report status is not GLOBAL_ZERO_COMPLETE")

        print(
            "G001_TERMINAL5_GLOBAL_RELOCATED_VERIFIED "
            f"status={report['status']} "
            f"search={report['search_receipts']} "
            f"certified_zero={report['certified_zero_records']} "
            f"bytes={len(raw)} sha256={sha256_file(expected_json)}"
        )
        return 0
    except (OSError, ValueError, KeyError, RelocationError) as error:
        print(
            f"G001_TERMINAL5_GLOBAL_RELOCATED_FAILED: {error}", file=sys.stderr
        )
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
