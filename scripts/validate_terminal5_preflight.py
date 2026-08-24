#!/usr/bin/env python3
"""Fail-closed validation for the frozen Terminal5 plan and ZERO receipts.

This is a release-side guard around the immutable production implementation.
It does not alter, replace, or regenerate the solver, plans, or evidence.

With no ``--run-root``, the command validates the complete 39,030-record plan
and checks that its mathematical roster is byte-for-byte derived from the
hash-pinned frozen plan (runtime/compiler bindings may differ).

With ``--run-root``, it additionally requires the exact 39,000 SEARCH receipt
set and 192 bundle receipts, authenticates every referenced ZERO leaf artifact,
and rejects a branch unless every requested ordinal was actually reached.
"""

from __future__ import annotations

import argparse
import contextlib
import hashlib
import importlib.util
import json
import os
import re
import stat
import subprocess
import sys
from pathlib import Path
from types import ModuleType
from typing import Any, Iterable, Mapping, Sequence


FROZEN_PLAN_SHA256 = (
    "b317a3b7cef71e11fea762ce5e70322f168e06c6e04b97293f066cb2e313bdae"
)
ROSTER_FIELDS = (
    "schema",
    "plan_id",
    "inputs",
    "invariants",
    "claim_boundary",
    "records",
    "bundles",
)
EXPECTED_RECORDS = 39_030
EXPECTED_SEARCH = 39_000
EXPECTED_CERTIFIED_ZERO = 30
EXPECTED_BUNDLES = 192
BASE_BRANCH_DEPTH = 3
RECEIPT_SCHEMA = "LEECH18_TERMINAL5_PREFLIGHT_V1"
UINT = re.compile(r"(?:0|[1-9][0-9]*)\Z")
RESULT_FIELD = re.compile(r"(?:^|\s)([A-Za-z0-9_]+)=([^\s]+)")


class PreflightError(RuntimeError):
    """A fail-closed preflight rejection."""


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while True:
            block = stream.read(1024 * 1024)
            if not block:
                break
            digest.update(block)
    return digest.hexdigest()


def canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
            allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")


def verifier_identity(plan: Mapping[str, Any], source_dir: Path) -> dict[str, Any]:
    """Hash-identify this guard, its authoritative parsers, and bound runtime."""

    bindings = plan["runtime"]["bindings"]
    pipeline = plan["runtime"]["pipeline_artifacts"]
    return {
        "preflight_source_sha256": sha256_file(Path(__file__).resolve()),
        "authoritative_plan_verifier_sha256": sha256_file(
            source_dir / "verify_g001_terminal5_plan_v1.py"
        ),
        "terminal_plan_parser_sha256": sha256_file(
            source_dir / "g001_terminal5_common_v1.py"
        ),
        "leaf_plan_parser_sha256": sha256_file(
            source_dir / "g001_remaining_leaf_common.py"
        ),
        "runtime_binding_sha256": {
            role: bindings[role]["sha256"] for role in sorted(bindings)
        },
        "pipeline_binding_sha256": {
            role: pipeline[role]["sha256"] for role in sorted(pipeline)
        },
    }


def write_new(path: Path, raw: bytes) -> None:
    """Atomically create a new receipt and refuse to replace any file."""

    absolute = Path(os.path.abspath(os.fspath(path)))
    if not absolute.parent.is_dir():
        raise PreflightError(f"output parent directory does not exist: {absolute.parent}")
    try:
        descriptor = os.open(str(absolute), os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o444)
    except OSError as error:
        raise PreflightError(f"refusing/cannot create output receipt {absolute}: {error}") from error
    try:
        with os.fdopen(descriptor, "wb", closefd=False) as stream:
            stream.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
    finally:
        os.close(descriptor)


def strict_json_bytes(raw: bytes, context: str) -> Any:
    try:
        text = raw.decode("utf-8", errors="strict")
    except UnicodeDecodeError as error:
        raise PreflightError(f"{context} is not UTF-8: {error}") from error

    def reject_duplicates(pairs: Sequence[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise PreflightError(f"{context} has duplicate JSON key {key!r}")
            result[key] = value
        return result

    def reject_constant(token: str) -> Any:
        raise PreflightError(f"{context} has nonstandard JSON constant {token}")

    try:
        return json.loads(
            text,
            object_pairs_hook=reject_duplicates,
            parse_constant=reject_constant,
        )
    except json.JSONDecodeError as error:
        raise PreflightError(f"{context} is malformed JSON: {error}") from error


def read_regular(path: Path, context: str) -> bytes:
    try:
        info = path.lstat()
    except OSError as error:
        raise PreflightError(f"missing {context}: {path}") from error
    if not stat.S_ISREG(info.st_mode) or stat.S_ISLNK(info.st_mode):
        raise PreflightError(f"{context} is not a real regular file: {path}")
    return path.read_bytes()


def read_json(path: Path, context: str) -> tuple[dict[str, Any], bytes]:
    raw = read_regular(path, context)
    value = strict_json_bytes(raw, context)
    if not isinstance(value, dict):
        raise PreflightError(f"{context} must be a JSON object")
    return value, raw


def exact_keys(value: Mapping[str, Any], expected: Iterable[str], context: str) -> None:
    actual = set(value)
    wanted = set(expected)
    if actual != wanted:
        raise PreflightError(
            f"{context} keys differ: missing={sorted(wanted - actual)} "
            f"extra={sorted(actual - wanted)}"
        )


def parse_uint(value: Any, context: str) -> int:
    if not isinstance(value, str) or UINT.fullmatch(value) is None:
        raise PreflightError(f"{context} is not a canonical nonnegative integer")
    return int(value)


def parse_child_max(value: Any, context: str) -> dict[int, int]:
    if not isinstance(value, str) or not value or not value.endswith(","):
        raise PreflightError(f"{context} is not a nonempty child_max list")
    result: dict[int, int] = {}
    for item in value[:-1].split(","):
        parts = item.split(":")
        if len(parts) != 2 or UINT.fullmatch(parts[0]) is None or UINT.fullmatch(parts[1]) is None:
            raise PreflightError(f"{context} contains malformed entry {item!r}")
        depth = int(parts[0])
        maximum = int(parts[1])
        if depth in result:
            raise PreflightError(f"{context} contains duplicate depth {depth}")
        if maximum <= 0:
            raise PreflightError(f"{context} has nonpositive fanout at depth {depth}")
        result[depth] = maximum
    return result


def validate_selector_reached(path: Sequence[int], solver_result: Mapping[str, Any], context: str) -> None:
    """Reject the production solver's false-ZERO response to an absent path.

    The frozen source numbers branch-path choices from depth 3.  At each
    selected ancestor it records the number of valid children in ``child_max``.
    ``root_valid`` is updated only when the requested depth-3 ordinal is
    reached.  Hence both values are mandatory evidence that each ordinal was
    present; merely receiving status=ZERO is not sufficient.
    """

    if not path or any(isinstance(item, bool) or not isinstance(item, int) or item < 0 for item in path):
        raise PreflightError(f"{context} has malformed branch path")
    root_valid = parse_uint(solver_result.get("root_valid"), f"{context}.root_valid")
    if root_valid == 0:
        raise PreflightError(f"{context} did not reach the requested root selector")
    if path[0] >= root_valid:
        raise PreflightError(
            f"{context} root selector {path[0]} is outside root_valid={root_valid}"
        )
    child_max = parse_child_max(solver_result.get("child_max"), f"{context}.child_max")
    for offset, ordinal in enumerate(path):
        depth = BASE_BRANCH_DEPTH + offset
        if depth not in child_max:
            raise PreflightError(f"{context} did not record selected depth {depth}")
        if ordinal >= child_max[depth]:
            raise PreflightError(
                f"{context} selector {ordinal} is outside child_max[{depth}]={child_max[depth]}"
            )


@contextlib.contextmanager
def source_modules(source_dir: Path):
    source_dir = source_dir.resolve(strict=True)
    loaded: dict[str, ModuleType] = {}
    saved: dict[str, ModuleType | None] = {}
    names = (
        "g001_terminal5_common_v1",
        "g001_remaining_leaf_common",
    )
    try:
        for name in names:
            path = source_dir / f"{name}.py"
            if not path.is_file():
                raise PreflightError(f"missing authoritative source module: {path}")
            saved[name] = sys.modules.pop(name, None)
            specification = importlib.util.spec_from_file_location(name, str(path))
            if specification is None or specification.loader is None:
                raise PreflightError(f"cannot load authoritative source module: {path}")
            module = importlib.util.module_from_spec(specification)
            sys.modules[name] = module
            specification.loader.exec_module(module)
            if Path(module.__file__).resolve() != path.resolve():
                raise PreflightError(f"authoritative module path mismatch: {name}")
            loaded[name] = module
        yield loaded["g001_terminal5_common_v1"], loaded["g001_remaining_leaf_common"]
    finally:
        for name in names:
            sys.modules.pop(name, None)
            if saved.get(name) is not None:
                sys.modules[name] = saved[name]  # type: ignore[assignment]


def run_authoritative_plan_verifier(
    plan_dir: Path, workspace: Path, source_dir: Path
) -> str:
    command = [
        sys.executable,
        "-B",
        str(source_dir / "verify_g001_terminal5_plan_v1.py"),
        "--plan-dir",
        str(plan_dir),
        "--workspace",
        str(workspace),
        "--source-dir",
        str(source_dir),
    ]
    completed = subprocess.run(
        command,
        cwd=str(source_dir),
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if completed.returncode != 0:
        stderr = completed.stderr.decode("utf-8", errors="replace").strip()
        raise PreflightError(
            f"authoritative plan verifier exited {completed.returncode}: {stderr}"
        )
    if completed.stderr != b"":
        raise PreflightError("authoritative plan verifier wrote to stderr")
    try:
        output = completed.stdout.decode("utf-8", errors="strict")
    except UnicodeDecodeError as error:
        raise PreflightError("authoritative plan verifier stdout is not UTF-8") from error
    if not output.startswith("G001_TERMINAL5_PLAN_V1_VERIFIED "):
        raise PreflightError("authoritative plan verifier success marker is absent")
    return output.rstrip("\n")


def validate_plan(
    plan_dir: Path,
    workspace: Path,
    source_dir: Path,
    frozen_plan_path: Path,
) -> tuple[dict[str, Any], str, Any, str]:
    plan_path = plan_dir / "terminal_plan_v1.json"
    frozen_raw = read_regular(frozen_plan_path, "frozen terminal plan")
    frozen_hash = sha256_bytes(frozen_raw)
    if frozen_hash != FROZEN_PLAN_SHA256:
        raise PreflightError(
            f"frozen terminal plan hash mismatch: expected {FROZEN_PLAN_SHA256}, got {frozen_hash}"
        )
    frozen_value = strict_json_bytes(frozen_raw, "frozen terminal plan")
    if not isinstance(frozen_value, dict):
        raise PreflightError("frozen terminal plan must be an object")

    with source_modules(source_dir) as (terminal_common, leaf_common):
        try:
            plan, plan_hash = terminal_common.load_plan(plan_path, production=True)
        except Exception as error:
            raise PreflightError(f"authoritative terminal-plan parser rejected plan: {error}") from error
        try:
            frozen_parsed = terminal_common.validate_plan(frozen_value, production=True)
        except Exception as error:
            raise PreflightError(f"authoritative parser rejected frozen plan: {error}") from error

        exact_keys(plan, (*ROSTER_FIELDS, "runtime"), "terminal plan")
        for field in ROSTER_FIELDS:
            if plan[field] != frozen_parsed[field]:
                raise PreflightError(f"terminal plan differs from frozen roster in field {field}")

        records = plan["records"]
        search = [record for record in records if record["classification"] == "SEARCH"]
        certified = [
            record for record in records if record["classification"] == "CERTIFIED_ZERO"
        ]
        if (
            len(records) != EXPECTED_RECORDS
            or len(search) != EXPECTED_SEARCH
            or len(certified) != EXPECTED_CERTIFIED_ZERO
            or len(plan["bundles"]) != EXPECTED_BUNDLES
        ):
            raise PreflightError("terminal plan production counts differ from the frozen roster")

        # The authoritative verifier checks the exact plan/bundle directory,
        # hashes all runtime bindings, and confirms every derived leaf plan.
        verifier_output = run_authoritative_plan_verifier(plan_dir, workspace, source_dir)
        return plan, plan_hash, leaf_common, verifier_output


def exact_named_files(directory: Path, expected: set[str], context: str) -> None:
    try:
        entries = list(directory.iterdir())
    except OSError as error:
        raise PreflightError(f"cannot enumerate {context}: {directory}") from error
    actual: set[str] = set()
    for entry in entries:
        info = entry.lstat()
        if not stat.S_ISREG(info.st_mode) or stat.S_ISLNK(info.st_mode):
            raise PreflightError(f"{context} contains non-regular entry: {entry.name}")
        actual.add(entry.name)
    if actual != expected:
        raise PreflightError(
            f"{context} exact set differs: missing={sorted(expected - actual)} "
            f"extra={sorted(actual - expected)}"
        )


def result_fields(stdout: bytes, expected_mode: str, context: str) -> dict[str, str]:
    try:
        text = stdout.decode("utf-8", errors="strict")
    except UnicodeDecodeError as error:
        raise PreflightError(f"{context} stdout is not UTF-8") from error
    lines = [line for line in text.splitlines() if line.startswith("RESULT ")]
    if len(lines) != 1:
        raise PreflightError(f"{context} does not have exactly one RESULT line")
    fields: dict[str, str] = {}
    for match in RESULT_FIELD.finditer(lines[0]):
        name, value = match.groups()
        if name in fields:
            raise PreflightError(f"{context} has duplicate RESULT field {name}")
        fields[name] = value
    if fields.get("mode") != expected_mode:
        raise PreflightError(f"{context} RESULT mode mismatch")
    return fields


def option_value(argv: Sequence[Any], option: str, context: str) -> str:
    positions = [index for index, value in enumerate(argv) if value == option]
    if len(positions) != 1 or positions[0] + 1 >= len(argv):
        raise PreflightError(f"{context} requires exactly one {option}")
    value = argv[positions[0] + 1]
    if not isinstance(value, str):
        raise PreflightError(f"{context} {option} value is not a string")
    return value


def validate_zero_leaf(
    run_root: Path,
    terminal_plan: Mapping[str, Any],
    terminal_plan_hash: str,
    record: Mapping[str, Any],
    bundle: Mapping[str, Any],
    leaf: Mapping[str, Any],
    leaf_plan_hash: str,
    local_index: int,
    receipt: Mapping[str, Any],
    leaf_common: Any,
) -> None:
    record_id = record["record_id"]
    context = f"record {record_id}"
    exact_keys(
        receipt,
        (
            "schema",
            "terminal_plan_id",
            "record_id",
            "configuration",
            "path",
            "bundle_index",
            "leaf_plan",
            "leaf_plan_sha256",
            "outcome",
            "evidence",
        ),
        f"{context} receipt",
    )
    expected_receipt_envelope = {
        "schema": "G001_TERMINAL5_LEAF_RECEIPT_V1",
        "terminal_plan_id": terminal_plan["plan_id"],
        "record_id": record_id,
        "configuration": record["configuration"],
        "path": record["path"],
        "bundle_index": bundle["bundle_index"],
        "leaf_plan": f"bundle_plans/bundle_{bundle['bundle_index']:03d}.json",
        "leaf_plan_sha256": leaf_plan_hash,
        "outcome": "ZERO",
    }
    for key, expected in expected_receipt_envelope.items():
        if receipt.get(key) != expected:
            raise PreflightError(f"{context} receipt {key} mismatch")

    expected_selector = {"kind": "path", "indices": record["path"]}
    if (
        leaf.get("leaf_id") != record_id
        or leaf.get("configuration") != record["configuration"]
        or leaf.get("mode") != record["mode"]
        or leaf.get("selector") != expected_selector
    ):
        raise PreflightError(f"{context} derived leaf identity/configuration/mode/path mismatch")

    evidence = receipt.get("evidence")
    if not isinstance(evidence, dict):
        raise PreflightError(f"{context} receipt evidence is not an object")
    required_evidence = {
        "schema",
        "plan_id",
        "plan_sha256",
        "leaf_index",
        "leaf_id",
        "leaf_sha256",
        "configuration",
        "mode",
        "selector",
        "selector_text",
        "outcome",
        "solver_exit_code",
        "solver_result",
        "solver_wall_seconds",
        "checker_wall_seconds",
        "witness_sha256",
        "argv",
        "argv_sha256",
        "cover_candidate_validation_enabled",
        "bound_hashes",
        "marker_file",
        "marker_sha256",
        "artifact_hashes",
    }
    exact_keys(evidence, required_evidence, f"{context} evidence")
    expected_evidence = {
        "schema": "G001_REMAINING_LEAF_EVIDENCE_V1",
        "plan_id": f"{terminal_plan['plan_id']}.{bundle['bundle_id']}",
        "plan_sha256": leaf_plan_hash,
        "leaf_index": local_index,
        "leaf_id": record_id,
        "leaf_sha256": leaf_common.canonical_sha256(leaf),
        "configuration": record["configuration"],
        "mode": record["mode"],
        "selector": expected_selector,
        "selector_text": "path:" + record["path_text"],
        "outcome": "ZERO",
        "solver_exit_code": 0,
        "checker_wall_seconds": None,
        "witness_sha256": None,
        "marker_file": "ZERO_COMPLETE_V1.json",
    }
    for key, expected in expected_evidence.items():
        if evidence.get(key) != expected:
            raise PreflightError(f"{context} evidence {key} mismatch")

    solver_result = evidence.get("solver_result")
    if not isinstance(solver_result, dict):
        raise PreflightError(f"{context} solver_result is not an object")
    if solver_result.get("status") != "ZERO" or solver_result.get("mode") != record["mode"]:
        raise PreflightError(f"{context} has non-ZERO status or mismatched mode")
    if parse_uint(solver_result.get("frontier"), f"{context}.frontier") != 0:
        raise PreflightError(f"{context} has nonzero frontier")
    if parse_uint(solver_result.get("solution_topologies"), f"{context}.solution_topologies") != 0:
        raise PreflightError(f"{context} ZERO has a solution topology")
    validate_selector_reached(record["path"], solver_result, context)

    leaf_directory = run_root / f"bundle_{bundle['bundle_index']:03d}" / record_id
    expected_leaf_files = {
        "launch.json",
        "solver.exit.json",
        "solver.stderr.txt",
        "solver.stdout.txt",
        "solver.timing.json",
        "ZERO_COMPLETE_V1.json",
    }
    exact_named_files(leaf_directory, expected_leaf_files, f"{context} leaf directory")

    marker, marker_raw = read_json(
        leaf_directory / "ZERO_COMPLETE_V1.json", f"{context} ZERO marker"
    )
    if sha256_bytes(marker_raw) != evidence.get("marker_sha256"):
        raise PreflightError(f"{context} marker hash mismatch")
    for key in (
        "plan_id",
        "plan_sha256",
        "leaf_index",
        "leaf_id",
        "leaf_sha256",
        "configuration",
        "mode",
        "selector",
        "selector_text",
        "outcome",
        "solver_exit_code",
        "solver_result",
        "argv_sha256",
        "bound_hashes",
    ):
        if marker.get(key) != evidence.get(key):
            raise PreflightError(f"{context} marker/evidence {key} mismatch")
    if marker.get("schema") != "G001_REMAINING_ZERO_COMPLETE_V1":
        raise PreflightError(f"{context} marker schema mismatch")

    artifact_hashes = evidence.get("artifact_hashes")
    if not isinstance(artifact_hashes, dict) or marker.get("files") != artifact_hashes:
        raise PreflightError(f"{context} marker/evidence artifact map mismatch")
    expected_artifacts = expected_leaf_files - {"ZERO_COMPLETE_V1.json"}
    if set(artifact_hashes) != expected_artifacts:
        raise PreflightError(f"{context} artifact exact set mismatch")
    for name, expected_hash in artifact_hashes.items():
        if not isinstance(expected_hash, str) or sha256_file(leaf_directory / name) != expected_hash:
            raise PreflightError(f"{context} artifact hash mismatch: {name}")

    exit_data, _ = read_json(leaf_directory / "solver.exit.json", f"{context} exit")
    if (
        exit_data.get("schema") != "G001_REMAINING_PROCESS_EXIT_V1"
        or exit_data.get("process") != "solver"
        or exit_data.get("exit_code") != 0
        or exit_data.get("timed_out") is not False
        or exit_data.get("interrupted_signal") is not None
        or exit_data.get("launch_error") is not None
    ):
        raise PreflightError(f"{context} does not have a clean solver exit 0")
    if read_regular(leaf_directory / "solver.stderr.txt", f"{context} stderr") != b"":
        raise PreflightError(f"{context} solver stderr is nonempty")
    stdout_raw = read_regular(leaf_directory / "solver.stdout.txt", f"{context} stdout")
    parsed_result = result_fields(stdout_raw, record["mode"], context)
    if parsed_result != solver_result:
        raise PreflightError(f"{context} stdout/receipt solver_result mismatch")

    launch, _ = read_json(leaf_directory / "launch.json", f"{context} launch")
    for key, expected in (
        ("schema", "G001_REMAINING_LEAF_LAUNCH_V1"),
        ("plan_id", expected_evidence["plan_id"]),
        ("plan_sha256", leaf_plan_hash),
        ("leaf_index", local_index),
        ("leaf_id", record_id),
        ("configuration", record["configuration"]),
        ("mode", record["mode"]),
        ("selector", expected_selector),
    ):
        if launch.get(key) != expected:
            raise PreflightError(f"{context} launch {key} mismatch")
    argv = launch.get("argv")
    if not isinstance(argv, list) or argv != evidence.get("argv"):
        raise PreflightError(f"{context} launch/evidence argv mismatch")
    if option_value(argv, "--configuration", context) != str(record["configuration"]):
        raise PreflightError(f"{context} argv configuration mismatch")
    if option_value(argv, "--branch-path", context) != record["path_text"]:
        raise PreflightError(f"{context} argv branch path mismatch")
    if "--root-branch" in argv:
        raise PreflightError(f"{context} argv unexpectedly uses root selector")


def validate_bundle_receipt(
    path: Path,
    bundle: Mapping[str, Any],
    plan: Mapping[str, Any],
    plan_hash: str,
    receipt_hashes: Mapping[str, str],
) -> str:
    value, raw = read_json(path, f"bundle receipt {bundle['bundle_index']}")
    exact_keys(
        value,
        (
            "schema",
            "plan_id",
            "plan_sha256",
            "mode",
            "bundle_index",
            "gate_task",
            "workers",
            "expected_records",
            "exact_records",
            "incomplete",
            "verified_found",
            "signal",
            "global_search_complete",
            "results",
        ),
        f"bundle receipt {bundle['bundle_index']}",
    )
    envelope = {
        "schema": "G001_TERMINAL5_BUNDLE_RECEIPT_V1",
        "plan_id": plan["plan_id"],
        "plan_sha256": plan_hash,
        "mode": "production",
        "bundle_index": bundle["bundle_index"],
        "gate_task": None,
        "workers": 15,
        "expected_records": bundle["search_count"],
        "exact_records": bundle["search_count"],
        "incomplete": 0,
        "verified_found": 0,
        "signal": None,
        "global_search_complete": False,
    }
    for key, expected in envelope.items():
        if value.get(key) != expected:
            raise PreflightError(f"bundle {bundle['bundle_index']} receipt {key} mismatch")
    results = value.get("results")
    if not isinstance(results, list) or len(results) != len(bundle["record_ids"]):
        raise PreflightError(f"bundle {bundle['bundle_index']} result count mismatch")
    by_id: dict[str, Mapping[str, Any]] = {}
    for result in results:
        if not isinstance(result, dict):
            raise PreflightError(f"bundle {bundle['bundle_index']} has malformed result")
        exact_keys(
            result,
            ("record_id", "configuration", "bundle_index", "outcome", "receipt_sha256"),
            f"bundle {bundle['bundle_index']} result",
        )
        record_id = result.get("record_id")
        if not isinstance(record_id, str) or record_id in by_id:
            raise PreflightError(f"bundle {bundle['bundle_index']} has duplicate result")
        by_id[record_id] = result
    if set(by_id) != set(bundle["record_ids"]):
        raise PreflightError(f"bundle {bundle['bundle_index']} result union mismatch")
    for record_id in bundle["record_ids"]:
        result = by_id[record_id]
        if (
            result.get("configuration") != bundle["configuration"]
            or result.get("bundle_index") != bundle["bundle_index"]
            or result.get("outcome") != "ZERO"
            or result.get("receipt_sha256") != receipt_hashes[record_id]
        ):
            raise PreflightError(f"bundle {bundle['bundle_index']} result mismatch: {record_id}")
    return sha256_bytes(raw)


def validate_run(
    plan_dir: Path,
    workspace: Path,
    source_dir: Path,
    run_root: Path,
    frozen_plan_path: Path,
) -> tuple[dict[str, Any], str, str, str, str]:
    plan, plan_hash, leaf_common, verifier_output = validate_plan(
        plan_dir, workspace, source_dir, frozen_plan_path
    )
    # Preserve a caller-supplied Windows drive alias.  Path.resolve() expands
    # SUBST paths to the much longer backing path, which can make otherwise
    # valid historical receipt names exceed the Win32 path limit.
    run_root = Path(os.path.abspath(os.fspath(run_root)))
    if not run_root.is_dir() or run_root.is_symlink():
        raise PreflightError(f"run root is not a real directory: {run_root}")
    records = {record["record_id"]: record for record in plan["records"]}
    search_records = {
        record_id: record
        for record_id, record in records.items()
        if record["classification"] == "SEARCH"
    }
    expected_leaf_names = {f"{record_id}.json" for record_id in search_records}
    expected_bundle_names = {
        f"bundle_{index:03d}.json" for index in range(EXPECTED_BUNDLES)
    }
    exact_named_files(run_root / "leaf_receipts", expected_leaf_names, "leaf receipt directory")
    exact_named_files(
        run_root / "bundle_receipts", expected_bundle_names, "bundle receipt directory"
    )

    expected_bundle_directories = {
        f"bundle_{index:03d}" for index in range(EXPECTED_BUNDLES)
    }
    actual_bundle_directories = {
        entry.name
        for entry in run_root.iterdir()
        if re.fullmatch(r"bundle_[0-9]{3}", entry.name)
        and entry.is_dir()
        and not entry.is_symlink()
    }
    if actual_bundle_directories != expected_bundle_directories:
        raise PreflightError(
            "production bundle directory exact set differs: "
            f"missing={sorted(expected_bundle_directories - actual_bundle_directories)} "
            f"extra={sorted(actual_bundle_directories - expected_bundle_directories)}"
        )

    bundle_plans: dict[int, tuple[dict[str, Any], str]] = {}
    for bundle in plan["bundles"]:
        index = bundle["bundle_index"]
        try:
            leaf_plan, leaf_hash = leaf_common.load_plan(
                plan_dir / "bundle_plans" / f"bundle_{index:03d}.json"
            )
        except Exception as error:
            raise PreflightError(f"bundle {index} leaf plan rejected: {error}") from error
        bundle_plans[index] = (leaf_plan, leaf_hash)

    receipt_hashes: dict[str, str] = {}
    for bundle in plan["bundles"]:
        index = bundle["bundle_index"]
        leaf_plan, leaf_plan_hash = bundle_plans[index]
        leaves = leaf_plan["leaves"]
        if len(leaves) != len(bundle["record_ids"]):
            raise PreflightError(f"bundle {index} leaf-plan count mismatch")
        for local_index, record_id in enumerate(bundle["record_ids"]):
            record = search_records.get(record_id)
            if record is None:
                raise PreflightError(f"bundle {index} names missing/non-SEARCH record {record_id}")
            receipt_path = run_root / "leaf_receipts" / f"{record_id}.json"
            receipt, receipt_raw = read_json(receipt_path, f"receipt {record_id}")
            validate_zero_leaf(
                run_root,
                plan,
                plan_hash,
                record,
                bundle,
                leaves[local_index],
                leaf_plan_hash,
                local_index,
                receipt,
                leaf_common,
            )
            receipt_hashes[record_id] = sha256_bytes(receipt_raw)

    if set(receipt_hashes) != set(search_records):
        raise PreflightError("validated receipt set is not exactly the SEARCH record set")
    bundle_receipt_hashes: dict[int, str] = {}
    for bundle in plan["bundles"]:
        bundle_receipt_hashes[bundle["bundle_index"]] = validate_bundle_receipt(
            run_root / "bundle_receipts" / f"bundle_{bundle['bundle_index']:03d}.json",
            bundle,
            plan,
            plan_hash,
            receipt_hashes,
        )
    leaf_set_document = "".join(
        f"{receipt_hashes[record_id]}  {record_id}.json\n"
        for record_id in sorted(receipt_hashes)
    ).encode("ascii")
    bundle_set_document = "".join(
        f"{bundle_receipt_hashes[index]}  bundle_{index:03d}.json\n"
        for index in sorted(bundle_receipt_hashes)
    ).encode("ascii")
    return (
        plan,
        plan_hash,
        verifier_output,
        sha256_bytes(leaf_set_document),
        sha256_bytes(bundle_set_document),
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan-dir", required=True, type=Path)
    parser.add_argument("--workspace", required=True, type=Path)
    parser.add_argument("--source-dir", required=True, type=Path)
    parser.add_argument("--frozen-plan", required=True, type=Path)
    parser.add_argument(
        "--run-root",
        type=Path,
        help="completed production_v1 directory; omit for pre-search plan validation",
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        help="create (never overwrite) a deterministic canonical JSON preflight receipt",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        plan_dir = args.plan_dir.resolve(strict=True)
        workspace = args.workspace.resolve(strict=True)
        source_dir = args.source_dir.resolve(strict=True)
        frozen_plan = args.frozen_plan.resolve(strict=True)
        if args.run_root is None:
            plan, plan_hash, _leaf_common, verifier_output = validate_plan(
                plan_dir, workspace, source_dir, frozen_plan
            )
            success_line = (
                "LEECH18_TERMINAL5_PREFLIGHT_OK "
                f"mode=plan records={len(plan['records'])} search={EXPECTED_SEARCH} "
                f"certified_zero={EXPECTED_CERTIFIED_ZERO} bundles={len(plan['bundles'])} "
                f"plan_sha256={plan_hash}"
            )
            report = {
                "schema": RECEIPT_SCHEMA,
                "status": "PASS",
                "mode": "plan",
                "terminal_plan_sha256": plan_hash,
                "frozen_plan_sha256": FROZEN_PLAN_SHA256,
                "records": EXPECTED_RECORDS,
                "search_records": EXPECTED_SEARCH,
                "certified_zero_records": EXPECTED_CERTIFIED_ZERO,
                "bundles": EXPECTED_BUNDLES,
                "roster_matches_frozen": True,
                "authoritative_plan_verifier_passed": True,
                "completed_run_checked": False,
                "selectors_reached": 0,
                "zero_receipts": 0,
                "zero_artifacts_checked": 0,
                "clean_exit_receipts": 0,
                "leaf_receipt_set_sha256": None,
                "bundle_receipt_set_sha256": None,
                "verifier_identity": verifier_identity(plan, source_dir),
            }
        else:
            (
                plan,
                plan_hash,
                verifier_output,
                leaf_receipt_set_sha256,
                bundle_receipt_set_sha256,
            ) = validate_run(
                plan_dir,
                workspace,
                source_dir,
                args.run_root,
                frozen_plan,
            )
            success_line = (
                "LEECH18_TERMINAL5_PREFLIGHT_OK "
                f"mode=completed-run records={EXPECTED_RECORDS} search={EXPECTED_SEARCH} "
                f"certified_zero={EXPECTED_CERTIFIED_ZERO} bundles={EXPECTED_BUNDLES} "
                f"selectors_reached={EXPECTED_SEARCH} zero_receipts={EXPECTED_SEARCH} "
                f"plan_sha256={plan_hash}"
            )
            report = {
                "schema": RECEIPT_SCHEMA,
                "status": "PASS",
                "mode": "completed-run",
                "terminal_plan_sha256": plan_hash,
                "frozen_plan_sha256": FROZEN_PLAN_SHA256,
                "records": EXPECTED_RECORDS,
                "search_records": EXPECTED_SEARCH,
                "certified_zero_records": EXPECTED_CERTIFIED_ZERO,
                "bundles": EXPECTED_BUNDLES,
                "roster_matches_frozen": True,
                "authoritative_plan_verifier_passed": True,
                "completed_run_checked": True,
                "selectors_reached": EXPECTED_SEARCH,
                "zero_receipts": EXPECTED_SEARCH,
                "zero_artifacts_checked": EXPECTED_SEARCH,
                "clean_exit_receipts": EXPECTED_SEARCH,
                "leaf_receipt_set_sha256": leaf_receipt_set_sha256,
                "bundle_receipt_set_sha256": bundle_receipt_set_sha256,
                "verifier_identity": verifier_identity(plan, source_dir),
            }
        if args.output_json is not None:
            write_new(args.output_json, canonical_json_bytes(report))
        print(verifier_output)
        print(success_line)
        if args.output_json is not None:
            print("LEECH18_TERMINAL5_PREFLIGHT_RECEIPT_WRITTEN " +
                  str(Path(os.path.abspath(os.fspath(args.output_json)))))
        return 0
    except (PreflightError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"LEECH18_TERMINAL5_PREFLIGHT_FAILED: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
