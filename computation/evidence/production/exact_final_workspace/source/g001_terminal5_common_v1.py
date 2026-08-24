#!/usr/bin/env python3
"""Strict shared contract for the five-configuration terminal search."""

from __future__ import annotations

import hashlib
import json
import os
import re
import stat
from pathlib import Path
from typing import Any, Dict, Iterable, List, Mapping, Sequence, Tuple


PLAN_SCHEMA = "G001_TERMINAL5_PLAN_V1"
RECORD_SCHEMA = "G001_TERMINAL5_RECORD_V1"
BUNDLE_SCHEMA = "G001_TERMINAL5_BUNDLE_V1"
PLAN_RECEIPT_SCHEMA = "G001_TERMINAL5_PLAN_RECEIPT_V1"
BUNDLE_RECEIPT_SCHEMA = "G001_TERMINAL5_BUNDLE_RECEIPT_V1"
PARTIAL_RECEIPT_SCHEMA = "G001_TERMINAL5_PARTIAL_RECEIPT_V1"
COLLECTION_SCHEMA = "G001_TERMINAL5_COLLECTION_V1"
PACKAGE_SCHEMA = "G001_TERMINAL5_RESULT_PACKAGE_V1"

CONFIGURATION_TO_MODE = {
    1: "g001_row0",
    4: "g001_row3",
    5: "g001_row4",
    6: "g001_row5",
    7: "g001_row6",
}
EXPECTED_RECORDS = {1: 5176, 4: 1324, 5: 25254, 6: 3977, 7: 3299}
EXPECTED_SEARCH = {1: 5176, 4: 1294, 5: 25254, 6: 3977, 7: 3299}
EXPECTED_ZERO = {1: 0, 4: 30, 5: 0, 6: 0, 7: 0}
EXPECTED_BUNDLES = {1: 26, 4: 6, 5: 124, 6: 20, 7: 16}
TOTAL_RECORDS = 39030
TOTAL_SEARCH = 39000
TOTAL_ZERO = 30
TOTAL_BUNDLES = 192
WORKERS_PER_BUNDLE = 15
CPUS_PER_BUNDLE = 16

C157_ARCHIVE = {
    "name": "AMD_G001_C157_JOB376839_RESUME861_V1_SLURM377219_COLLECTED_20260818T175225Z.tar.gz",
    "sha256": "97f3584ad70917031e3bef44c43d6d8cd4705c51c50869860961fa41ca7726d0",
    "bytes": 94329607,
    "package": "G001_C157_JOB376839_RESUME861_V1_SLURM377219_COLLECTED",
    "aggregate_sha256": "d3461fb7c88477604befb09172e09af83fcda863d6c016e506434f7b5ed43127",
    "receipt_sha256": "39c7d2c01d50bd8aa861302659681880908dc9c773217eaed655a7a887fc7444",
    "manifest_sha256": "4bcc4a5ea774c55700560f3dd0939e28efba14df9ca7ca4b8917ca5bbd36351e",
}
CONFIG4_ARCHIVE = {
    "name": "AMD_G001_CONFIG4_P2_HEAVY16_V1_SLURM377045_RECOVERED_COLLECTED.tar.gz",
    "sha256": "76e793a1911e54de2ebec04cfe22df7115f3cecbfbd0f53df6b187256d0949c2",
    "bytes": 70200766,
    "package": "G001_CONFIG4_P2_HEAVY16_V1_SLURM377045_RECOVERED_COLLECTED",
    "aggregate_sha256": "1a7e626b61267f13b49671d4129e666790fafb009777f1b54ac978e0fb374f41",
    "receipt_sha256": "ab526c6ea7ad255c452ce185709561378123e965bd5427956c7256f44d814f2e",
    "manifest_sha256": "11033f185bcab6021d4b25a6e103c4fc247f87609265e9ca375beededd3bcb01",
}

SELECTION_HASHES = {
    1: "0f3e5944d4786a494533a0519adbc52f995d0f9d56533659f65775a7074f404d",
    4: "10a95422331b3fb90a05848998f47d3952ad28861d2f8d1402fb540f5a88b8bc",
    5: "0f3e5944d4786a494533a0519adbc52f995d0f9d56533659f65775a7074f404d",
    6: "0f3e5944d4786a494533a0519adbc52f995d0f9d56533659f65775a7074f404d",
    7: "0f3e5944d4786a494533a0519adbc52f995d0f9d56533659f65775a7074f404d",
}

EXACT_FLAGS = [
    "--multi-edge-cover",
    "--multi-edge-cover-no-hall",
    "--multi-edge-cover-max-components", "6",
    "--multi-edge-cover-budget", "100",
    "--multi-edge-cover-no-exact-hall",
    "--multi-edge-cover-exact-max-components", "6",
]

SAFE_ID = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_.-]{0,127}$")
HEX64 = re.compile(r"^[0-9a-f]{64}$")


class TerminalError(RuntimeError):
    """A fail-closed terminal plan or result validation error."""


def canonical_json(value: Any) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True, allow_nan=False) + "\n").encode("utf-8")


def strict_json(raw: bytes, label: str) -> Any:
    def pairs(items: Sequence[Tuple[str, Any]]) -> Dict[str, Any]:
        result: Dict[str, Any] = {}
        for key, value in items:
            if key in result:
                raise TerminalError(f"duplicate key {key!r} in {label}")
            result[key] = value
        return result

    try:
        return json.loads(
            raw.decode("utf-8", errors="strict"), object_pairs_hook=pairs,
            parse_constant=lambda token: (_ for _ in ()).throw(
                TerminalError(f"non-finite JSON token in {label}: {token}")))
    except (UnicodeError, json.JSONDecodeError) as error:
        raise TerminalError(f"invalid strict JSON in {label}: {error}") from error


def read_json(path: Path, label: str) -> Any:
    return strict_json(read_regular(path, label), label)


def read_regular(path: Path, label: str) -> bytes:
    try:
        info = path.lstat()
    except OSError as error:
        raise TerminalError(f"{label} is missing: {path}") from error
    if stat.S_ISLNK(info.st_mode) or not stat.S_ISREG(info.st_mode) or info.st_nlink != 1:
        raise TerminalError(f"{label} is not a single-link regular file: {path}")
    return path.read_bytes()


def require_directory(path: Path, label: str) -> Path:
    path = Path(os.path.abspath(os.fspath(path)))
    try:
        info = path.lstat()
    except OSError as error:
        raise TerminalError(f"{label} is missing: {path}") from error
    if stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode):
        raise TerminalError(f"{label} is not a non-symlink directory: {path}")
    return path


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def require_keys(value: Mapping[str, Any], expected: Iterable[str], label: str) -> None:
    actual = set(value)
    wanted = set(expected)
    if actual != wanted:
        raise TerminalError(
            f"{label} keys differ: missing={sorted(wanted-actual)} extra={sorted(actual-wanted)}")


def require_id(value: Any, label: str) -> str:
    if not isinstance(value, str) or not SAFE_ID.fullmatch(value):
        raise TerminalError(f"{label} is not a safe identifier")
    return value


def require_sha(value: Any, label: str) -> str:
    if not isinstance(value, str) or not HEX64.fullmatch(value):
        raise TerminalError(f"{label} is not a lowercase SHA-256")
    return value


def require_path(value: Any, label: str) -> Tuple[int, ...]:
    if (not isinstance(value, list) or not value or len(value) > 14 or
            any(isinstance(item, bool) or not isinstance(item, int) or item < 0
                for item in value)):
        raise TerminalError(f"{label} must be 1..14 nonnegative indices")
    return tuple(value)


def path_text(path: Sequence[int]) -> str:
    return ",".join(str(item) for item in path)


def assert_prefix_free(keys: Iterable[Tuple[int, Tuple[int, ...]]], label: str) -> None:
    roots: Dict[int, Dict[int, Any]] = {}
    terminal = object()
    for configuration, path in sorted(keys):
        node = roots.setdefault(configuration, {})
        for part in path:
            if terminal in node:
                raise TerminalError(f"{label} has prefix overlap at c{configuration}:{path_text(path)}")
            node = node.setdefault(part, {})
        if node:
            raise TerminalError(f"{label} has reverse prefix overlap at c{configuration}:{path_text(path)}")
        if terminal in node:
            raise TerminalError(f"{label} has duplicate c{configuration}:{path_text(path)}")
        node[terminal] = True


def solver_argv(configuration: int, path: Sequence[int]) -> List[str]:
    return (["--configuration", str(configuration), "--branch-path", path_text(path),
             "--witness-file", "{WITNESS_FILE}"] + list(EXACT_FLAGS))


def _binding(value: Any, label: str) -> Dict[str, str]:
    if not isinstance(value, dict):
        raise TerminalError(f"{label} must be an object")
    require_keys(value, ("path", "sha256"), label)
    path = value["path"]
    if (not isinstance(path, str) or not path or Path(path).is_absolute() or
            ".." in Path(path).parts):
        raise TerminalError(f"{label}.path must stay relative to workspace")
    return {"path": Path(path).as_posix(), "sha256": require_sha(value["sha256"], label)}


def validate_record(value: Any) -> Dict[str, Any]:
    if not isinstance(value, dict):
        raise TerminalError("record must be an object")
    require_keys(value, ("schema", "record_id", "configuration", "mode", "path",
                         "path_text", "classification", "bundle_index", "weight",
                         "evidence"), "record")
    if value["schema"] != RECORD_SCHEMA:
        raise TerminalError("record schema mismatch")
    record_id = require_id(value["record_id"], "record_id")
    configuration = value["configuration"]
    if isinstance(configuration, bool) or configuration not in CONFIGURATION_TO_MODE:
        raise TerminalError("unsupported configuration")
    if value["mode"] != CONFIGURATION_TO_MODE[configuration]:
        raise TerminalError("record mode/configuration mismatch")
    path = require_path(value["path"], "record.path")
    if value["path_text"] != path_text(path):
        raise TerminalError("record path_text mismatch")
    classification = value["classification"]
    if classification not in ("SEARCH", "CERTIFIED_ZERO"):
        raise TerminalError("record classification mismatch")
    bundle_index = value["bundle_index"]
    if classification == "SEARCH":
        if isinstance(bundle_index, bool) or not isinstance(bundle_index, int) or not 0 <= bundle_index < TOTAL_BUNDLES:
            raise TerminalError("search record needs a valid bundle_index")
    elif bundle_index is not None:
        raise TerminalError("certified zero must not enter a solver bundle")
    weight = value["weight"]
    if isinstance(weight, bool) or not isinstance(weight, int) or weight < 0:
        raise TerminalError("record weight must be nonnegative")
    evidence = value["evidence"]
    if not isinstance(evidence, dict):
        raise TerminalError("record evidence must be an object")
    require_keys(evidence, ("source", "kind", "calibration_depth",
                            "calibration_frontier", "source_id"), "record.evidence")
    source = evidence["source"]
    kind = evidence["kind"]
    if source not in ("C157", "CONFIG4") or not isinstance(kind, str):
        raise TerminalError("record evidence source/kind mismatch")
    if source == "C157" and configuration == 4:
        raise TerminalError("C157 evidence cannot supply configuration 4")
    if source == "CONFIG4" and configuration != 4:
        raise TerminalError("CONFIG4 evidence can supply only configuration 4")
    depth = evidence["calibration_depth"]
    frontier = evidence["calibration_frontier"]
    if (isinstance(depth, bool) or not isinstance(depth, int) or depth < 0 or
            isinstance(frontier, bool) or not isinstance(frontier, int) or frontier < 0 or
            not isinstance(evidence["source_id"], str) or not evidence["source_id"]):
        raise TerminalError("record evidence scalar mismatch")
    if classification == "CERTIFIED_ZERO" and kind not in (
            "config4_preserved_zero", "config4_discharged_zero"):
        raise TerminalError("only explicit Config4 zero certificates may be excluded")
    if kind == "config4_depth15_descendant" and classification != "SEARCH":
        raise TerminalError("Config4 depth-15 frontier zero is not a terminal certificate")
    return dict(value)


def validate_plan(value: Any, production: bool = True) -> Dict[str, Any]:
    if not isinstance(value, dict):
        raise TerminalError("plan must be an object")
    require_keys(value, ("schema", "plan_id", "inputs", "runtime", "invariants",
                         "claim_boundary", "records", "bundles"), "plan")
    if value["schema"] != PLAN_SCHEMA:
        raise TerminalError("plan schema mismatch")
    require_id(value["plan_id"], "plan_id")
    inputs = value["inputs"]
    runtime = value["runtime"]
    invariants = value["invariants"]
    boundary = value["claim_boundary"]
    if not all(isinstance(item, dict) for item in (inputs, runtime, invariants, boundary)):
        raise TerminalError("plan metadata objects are malformed")
    require_keys(inputs, ("c157", "config4", "selection_sha256"), "inputs")
    for label, expected in (("c157", C157_ARCHIVE), ("config4", CONFIG4_ARCHIVE)):
        observed = inputs[label]
        if not isinstance(observed, dict):
            raise TerminalError(f"inputs.{label} must be an object")
        require_keys(observed, expected.keys(), f"inputs.{label}")
        if observed != expected:
            raise TerminalError(f"inputs.{label} binding mismatch")
    if inputs["selection_sha256"] != {str(k): v for k, v in SELECTION_HASHES.items()}:
        raise TerminalError("validation-selection binding mismatch")
    require_keys(runtime, ("workers_per_bundle", "cpus_per_bundle", "bundle_count",
                           "solver_setting", "multi_edge_cover_validate", "bindings",
                           "pipeline_artifacts"), "runtime")
    if (runtime["workers_per_bundle"] != WORKERS_PER_BUNDLE or
            runtime["cpus_per_bundle"] != CPUS_PER_BUNDLE or
            runtime["bundle_count"] != TOTAL_BUNDLES or
            runtime["solver_setting"] != "exact6" or
            runtime["multi_edge_cover_validate"] != "OFF"):
        raise TerminalError("runtime policy mismatch")
    bindings = runtime["bindings"]
    if not isinstance(bindings, dict):
        raise TerminalError("runtime.bindings must be an object")
    require_keys(bindings, ("solver_source", "solver_executable", "checker_source",
                            "checker_executable", "runtime_freeze"), "runtime.bindings")
    for role in bindings:
        _binding(bindings[role], f"runtime.bindings.{role}")
    pipeline = runtime["pipeline_artifacts"]
    if not isinstance(pipeline, dict):
        raise TerminalError("pipeline_artifacts must be an object")
    require_keys(pipeline, ("leaf_worker", "leaf_common", "leaf_collector"),
                 "pipeline_artifacts")
    for role in pipeline:
        _binding(pipeline[role], f"pipeline_artifacts.{role}")
    require_keys(invariants, ("record_count", "search_count", "certified_zero_count",
                              "records_by_configuration", "search_by_configuration",
                              "zero_by_configuration", "bundles_by_configuration"),
                 "invariants")
    require_keys(boundary, ("terminal_search", "found_requires_independent_checker",
                            "found_report_immediately", "global_zero_requires_all_receipts",
                            "timeouts_are_non_evidence", "calibration_frontier_is_not_certificate"),
                 "claim_boundary")
    if boundary != {
        "terminal_search": True,
        "found_requires_independent_checker": True,
        "found_report_immediately": True,
        "global_zero_requires_all_receipts": True,
        "timeouts_are_non_evidence": True,
        "calibration_frontier_is_not_certificate": True,
    }:
        raise TerminalError("claim boundary mismatch")
    records_raw = value["records"]
    bundles_raw = value["bundles"]
    if not isinstance(records_raw, list) or not isinstance(bundles_raw, list):
        raise TerminalError("records/bundles must be arrays")
    records = [validate_record(item) for item in records_raw]
    ids = [item["record_id"] for item in records]
    keys = [(item["configuration"], tuple(item["path"])) for item in records]
    if len(set(ids)) != len(ids) or len(set(keys)) != len(keys):
        raise TerminalError("duplicate record identity")
    assert_prefix_free(keys, "terminal record partition")

    bundles: List[Dict[str, Any]] = []
    for raw in bundles_raw:
        if not isinstance(raw, dict):
            raise TerminalError("bundle must be an object")
        require_keys(raw, ("schema", "bundle_id", "bundle_index", "configuration",
                           "record_ids", "search_count", "weight_sum"), "bundle")
        if raw["schema"] != BUNDLE_SCHEMA:
            raise TerminalError("bundle schema mismatch")
        require_id(raw["bundle_id"], "bundle_id")
        index = raw["bundle_index"]
        config = raw["configuration"]
        record_ids = raw["record_ids"]
        if (isinstance(index, bool) or not isinstance(index, int) or index < 0 or
                config not in CONFIGURATION_TO_MODE or not isinstance(record_ids, list) or
                not record_ids or any(not isinstance(item, str) for item in record_ids) or
                len(set(record_ids)) != len(record_ids) or
                raw["search_count"] != len(record_ids) or
                isinstance(raw["weight_sum"], bool) or not isinstance(raw["weight_sum"], int) or
                raw["weight_sum"] < 0):
            raise TerminalError("bundle scalar/list mismatch")
        bundles.append(dict(raw))
    if [item["bundle_index"] for item in bundles] != list(range(len(bundles))):
        raise TerminalError("bundle indices must be contiguous and ordered")
    if len({item["bundle_id"] for item in bundles}) != len(bundles):
        raise TerminalError("duplicate bundle_id")
    by_id = {item["record_id"]: item for item in records}
    assigned: List[str] = []
    for bundle in bundles:
        members = [by_id.get(item) for item in bundle["record_ids"]]
        if any(item is None for item in members):
            raise TerminalError("bundle names an unknown record")
        assert all(item is not None for item in members)
        if any(item["classification"] != "SEARCH" or
               item["configuration"] != bundle["configuration"] or
               item["bundle_index"] != bundle["bundle_index"] for item in members):
            raise TerminalError("bundle membership/configuration mismatch")
        if bundle["weight_sum"] != sum(max(1, item["weight"]) for item in members):
            raise TerminalError("bundle weight_sum mismatch")
        assigned.extend(bundle["record_ids"])
    search_ids = [item["record_id"] for item in records if item["classification"] == "SEARCH"]
    if sorted(assigned) != sorted(search_ids):
        raise TerminalError("bundle union is not exactly the search set")

    if production:
        record_counts = {config: 0 for config in CONFIGURATION_TO_MODE}
        search_counts = dict(record_counts)
        zero_counts = dict(record_counts)
        bundle_counts = dict(record_counts)
        for item in records:
            record_counts[item["configuration"]] += 1
            (search_counts if item["classification"] == "SEARCH" else zero_counts)[
                item["configuration"]] += 1
        for item in bundles:
            bundle_counts[item["configuration"]] += 1
        if (len(records) != TOTAL_RECORDS or len(search_ids) != TOTAL_SEARCH or
                len(records) - len(search_ids) != TOTAL_ZERO or len(bundles) != TOTAL_BUNDLES or
                record_counts != EXPECTED_RECORDS or search_counts != EXPECTED_SEARCH or
                zero_counts != EXPECTED_ZERO or bundle_counts != EXPECTED_BUNDLES):
            raise TerminalError("production count invariant mismatch")
        expected_invariants = {
            "record_count": TOTAL_RECORDS,
            "search_count": TOTAL_SEARCH,
            "certified_zero_count": TOTAL_ZERO,
            "records_by_configuration": {str(k): v for k, v in EXPECTED_RECORDS.items()},
            "search_by_configuration": {str(k): v for k, v in EXPECTED_SEARCH.items()},
            "zero_by_configuration": {str(k): v for k, v in EXPECTED_ZERO.items()},
            "bundles_by_configuration": {str(k): v for k, v in EXPECTED_BUNDLES.items()},
        }
        if invariants != expected_invariants:
            raise TerminalError("declared production invariants mismatch")
    return dict(value)


def load_plan(path: Path, production: bool = True) -> Tuple[Dict[str, Any], str]:
    raw = read_regular(path, "terminal plan")
    value = strict_json(raw, "terminal plan")
    return validate_plan(value, production=production), sha256_bytes(raw)


def utc_now() -> str:
    from datetime import datetime, timezone
    return datetime.now(timezone.utc).isoformat(timespec="microseconds").replace("+00:00", "Z")

