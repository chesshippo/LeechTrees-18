#!/usr/bin/env python3
"""Validate a release against its required externally retained manifest hash."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import sys
from pathlib import Path, PurePosixPath
from typing import Any, Sequence


HERE = Path(__file__).absolute().parent
DEFAULT_SOURCE_MANIFEST = HERE / "MANIFEST.sha256"
HEX64 = re.compile(r"[0-9a-f]{64}")
HEX40 = re.compile(r"[0-9a-f]{40}")
SAFE_LOG = re.compile(r"[A-Za-z0-9_.-]+")
FULL_MARKER = (
    "LEECH18_HYBRID_END_TO_END_PASS configurations=8 "
    "reported_node_visits=8565199014 global_status=GLOBAL_ZERO_COMPLETE"
)
PAYLOAD_FILES = {
    "INPUT_MANIFEST.sha256",
    "ORCHESTRATOR_TRANSCRIPT.sanitized.txt",
    "RUN_RESULT.txt",
    "SEMANTIC_BRIDGE_RUN_RESULT.json",
    "SEMANTIC_BRIDGE_RUN_RESULT.sha256",
    "STAGE_LOGS.sha256",
    "STAGE_DIGESTS.json",
}
ALL_FILES = PAYLOAD_FILES | {"RELEASE_MANIFEST.sha256"}
FULL_STAGE_NAMES = {
    "configuration_2",
    "configuration_3",
    "config3_a2_frozen_split_strict",
    "configuration_3_strict_ledger_audit",
    "configuration_8",
    "frozen_runtime_source",
    "global_relocated_collector",
    "hybrid_record",
    "hybrid_record_final",
    "lean_clean_baseline_build",
    "lean_git_archive",
    "lean_git_archive_extract",
    "lean_git_archive_objects",
    "lean_git_tree",
    "lean_hybrid_boundary",
    "lean_version",
    "prior_three_manifest",
    "python_version",
    "semantic_bridge",
    "source_freeze",
    "terminal5_source_tests",
    "terminal_plan",
    "terminal_plan_regeneration_build",
    "terminal_plan_regeneration_compare",
}
SEMANTIC_RESULT_FIELDS = {
    "artifacts",
    "axiom_allowlist",
    "axiom_audit_declarations",
    "baseline_dossier_olean_sha256",
    "baseline_mode",
    "bridge_sources",
    "full_checker_stdout_sha256",
    "lean_emitter_stdout_sha256",
    "lean_elaboration_threads",
    "lean_source_commit",
    "lean_toolchain",
    "logs",
    "pinned_inputs",
    "record_sha256",
    "schema",
    "status",
    "terminal_marker",
}
SEMANTIC_BRIDGE_SOURCES = {
    "LeanRowSemanticBridge.lean",
    "README.md",
    "SEMANTIC_BRIDGE_RECORD.json",
    "verify_semantic_bridge.py",
    "verify_semantic_bridge.ps1",
    "SemanticBridge/A2Split.lean",
    "SemanticBridge/AdjacentRows.lean",
    "SemanticBridge/Aggregate.lean",
    "SemanticBridge/DescriptorData.lean",
    "SemanticBridge/DescriptorWellFormed.lean",
    "SemanticBridge/DisjointRows.lean",
    "SemanticBridge/RowCore.lean",
}
SEMANTIC_ARTIFACTS = {
    "lean_build/LeanRowSemanticBridge.olean",
    "lean_build/SemanticBridge/A2Split.olean",
    "lean_build/SemanticBridge/AdjacentRows.olean",
    "lean_build/SemanticBridge/Aggregate.olean",
    "lean_build/SemanticBridge/DescriptorData.olean",
    "lean_build/SemanticBridge/DescriptorWellFormed.olean",
    "lean_build/SemanticBridge/DisjointRows.olean",
    "lean_build/SemanticBridge/RowCore.olean",
}
SEMANTIC_LOG_STEMS = {
    "full_semantic_bridge",
    "lean_a2_split",
    "lean_adjacent_rows",
    "lean_aggregate",
    "lean_descriptor_data",
    "lean_descriptor_well_formed",
    "lean_disjoint_rows",
    "lean_row_core",
    "lean_semantic_bridge",
    "lean_version",
    "static_source_bridge",
}
SEMANTIC_LOGS = {
    f"logs/{stem}.{stream}.txt"
    for stem in SEMANTIC_LOG_STEMS
    for stream in ("stdout", "stderr")
}
SEMANTIC_AXIOM_DECLARATIONS = [
    "Leech18SemanticBridge.rowDescriptors_all_wellFormed",
    "Leech18SemanticBridge.eightRowDossier_implies_some_realized_core",
    "Leech18SemanticBridge.isLeech_implies_some_realized_seed_descriptor",
    "Leech18SemanticBridge.adjacentMeetsTwoRow_implies_a2_production_split",
]
SEMANTIC_INPUT_ROLES = {
    "a2_production_source",
    "authoritative_dossier_olean",
    "authoritative_lean_dossier",
    "configuration2_certificate",
    "configuration3_certificate",
    "configuration3_partition_ledger",
    "configuration8_certificate",
    "final_five_solver",
    "final_five_source_freeze",
    "lake_manifest",
    "lakefile",
    "lean_toolchain",
    "row1_production_snapshot",
    "row7_production_snapshot",
    "solver_core",
}
SEMANTIC_SPEC_FIELDS = {
    "status",
    "directory",
    "record_path",
    "record_sha256",
    "wrapper_path",
    "wrapper_sha256",
    "source_files",
    "rows",
    "direct_rows",
    "projected_rows",
    "uses_fresh_baseline_lean_lib",
    "expected_marker",
    "run_result_schema",
    "run_result_sha256",
    "run_result_sidecar_sha256",
}
OMITTED_ARTIFACT_BINDINGS = {
    "fresh_dossier_olean": (
        "lean_project/.lake/build_release_clean/lib/lean/LeechTrees/Expanded/"
        "FirstEdge/FirstEdgeDossier.olean",
        "FRESH_DOSSIER_OLEAN_SHA256",
    ),
    "lean_project_archive": (
        "lean_project.tar",
        "LEAN_PROJECT_ARCHIVE_SHA256",
    ),
    "regenerated_plan": (
        "regenerated_terminal_plan/terminal_plan_v1.json",
        "REGENERATED_PLAN_SHA256",
    ),
    "regenerated_plan_manifest": (
        "regenerated_terminal_plan/plan_artifacts.sha256",
        "REGENERATED_PLAN_MANIFEST_SHA256",
    ),
    "regenerated_plan_receipt": (
        "regenerated_terminal_plan/plan_receipt.json",
        "REGENERATED_PLAN_RECEIPT_SHA256",
    ),
    "runtime_source_manifest": (
        "frozen_runtime_source/runtime_source_validation.sha256",
        "RUNTIME_SOURCE_MANIFEST_SHA256",
    ),
    "runtime_source_report": (
        "frozen_runtime_source/runtime_source_validation.json",
        "RUNTIME_SOURCE_REPORT_SHA256",
    ),
}
CONFIG3_RELEASE_BINDINGS = {
    "CONFIG3_RELEASE_RECORD_SHA256": (
        "config3_repair/evidence/full_preserved_v1/RELEASE.json"
    ),
    "CONFIG3_RUN_RESULT_SHA256": (
        "config3_repair/evidence/full_preserved_v1/RUN_RESULT.json"
    ),
    "CONFIG3_RELEASE_MANIFEST_SHA256": (
        "config3_repair/evidence/full_preserved_v1/MANIFEST.sha256"
    ),
}
CONFIG3_SPEC_FIELDS = {
    "status",
    "schema",
    "release_directory",
    "engine",
    "logical_partitions",
    "direct_partitions",
    "split_children",
    "logical_nodes",
    "release_record_path",
    "release_record_sha256",
    "release_sidecar_path",
    "release_sidecar_sha256",
    "run_result_path",
    "run_result_sha256",
    "run_result_sidecar_path",
    "run_result_sidecar_sha256",
    "manifest_path",
    "manifest_sha256",
    "exporter_path",
    "exporter_sha256",
    "verifier_path",
    "verifier_sha256",
    "split_harness_path",
    "split_harness_sha256",
    "expected_marker",
    "normalized_stdout_sha256",
}
RESULT_FIELDS = {
    "MODE",
    "EXIT_CODE",
    "FINAL_MARKER",
    "MANIFEST_SHA256",
    "INITIAL_MANIFEST_SHA256",
    "RUNTIME_SOURCE_REPORT_SHA256",
    "RUNTIME_SOURCE_MANIFEST_SHA256",
    "LEAN_PROJECT_ARCHIVE_SHA256",
    "PYTHON_EXECUTABLE_SHA256",
    "POWERSHELL_EXECUTABLE_SHA256",
    "GIT_EXECUTABLE_SHA256",
    "TAR_EXECUTABLE_SHA256",
    "LEAN_EXECUTABLE_SHA256",
    "LAKE_EXECUTABLE_SHA256",
    "LEAN_ELABORATION_THREADS",
    "LEAN_NUM_THREADS",
    "CONFIG3_RUN_RESULT_SHA256",
    "CONFIG3_RELEASE_RECORD_SHA256",
    "CONFIG3_RELEASE_MANIFEST_SHA256",
    "FRESH_DOSSIER_OLEAN_SHA256",
    "SEMANTIC_BRIDGE_RECORD_SHA256",
    "SEMANTIC_BRIDGE_RUN_RESULT_SHA256",
    "SEMANTIC_BRIDGE_RUN_RESULT_SIDECAR_SHA256",
    "SEMANTIC_BRIDGE_STDOUT_SHA256",
    "REGENERATED_PLAN_SHA256",
    "REGENERATED_PLAN_MANIFEST_SHA256",
    "REGENERATED_PLAN_RECEIPT_SHA256",
    "STAGE_LOG_MANIFEST_SHA256",
    "TRANSCRIPT_SHA256",
    "TRANSCRIPT",
    "STARTED_AT",
    "COMPLETED_AT",
}
RESULT_NONDIGEST_FIELDS = {
    "MODE",
    "EXIT_CODE",
    "FINAL_MARKER",
    "LEAN_ELABORATION_THREADS",
    "LEAN_NUM_THREADS",
    "TRANSCRIPT",
    "STARTED_AT",
    "COMPLETED_AT",
}


class CheckError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CheckError(message)


def is_link_like(path: Path) -> bool:
    junction_test = getattr(path, "is_junction", None)
    if path.is_symlink() or bool(junction_test is not None and junction_test()):
        return True
    try:
        attributes = getattr(path.lstat(), "st_file_attributes", 0)
    except OSError:
        return False
    return bool(attributes & getattr(stat, "FILE_ATTRIBUTE_REPARSE_POINT", 0))


def require_plain_directory(path: Path, label: str) -> Path:
    try:
        info = path.lstat()
    except OSError as exc:
        raise CheckError(f"cannot inspect {label}: {path}: {exc}") from exc
    require(
        stat.S_ISDIR(info.st_mode) and not is_link_like(path),
        f"{label} is not a plain directory: {path}",
    )
    return path


def require_plain_file(path: Path, label: str) -> Path:
    try:
        info = path.lstat()
    except OSError as exc:
        raise CheckError(f"cannot inspect {label}: {path}: {exc}") from exc
    require(
        stat.S_ISREG(info.st_mode) and info.st_nlink == 1 and not is_link_like(path),
        f"{label} is not a regular single-link file: {path}",
    )
    return path


def lexical_absolute(path: Path) -> Path:
    return Path(os.path.abspath(os.fspath(path)))


def require_plain_ancestor_chain(
    path: Path, label: str, anchor: Path | None = None
) -> Path:
    target = lexical_absolute(path)
    base = lexical_absolute(anchor if anchor is not None else Path(target.anchor))
    try:
        relative = target.relative_to(base)
    except ValueError as exc:
        raise CheckError(f"{label} is outside its permitted root: {target}") from exc
    current = require_plain_directory(base, f"{label} root")
    for part in relative.parts[:-1]:
        current = require_plain_directory(current / part, f"{label} ancestor")
    require(not is_link_like(target), f"{label} leaf is a link/reparse point: {target}")
    try:
        target.resolve(strict=True).relative_to(base.resolve(strict=True))
    except (OSError, ValueError) as exc:
        raise CheckError(
            f"{label} is missing or resolves outside its permitted root: {target}"
        ) from exc
    return target


def require_plain_directory_tree(
    path: Path, label: str, anchor: Path | None = None
) -> Path:
    return require_plain_directory(
        require_plain_ancestor_chain(path, label, anchor), label
    )


def require_plain_file_tree(
    path: Path, label: str, anchor: Path | None = None
) -> Path:
    return require_plain_file(require_plain_ancestor_chain(path, label, anchor), label)


def reject_duplicate_json_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON object key: {key!r}")
        result[key] = value
    return result


def reject_json_constant(value: str) -> Any:
    raise CheckError(f"non-finite JSON number is forbidden: {value}")


def parse_strict_json(raw: bytes, label: str) -> Any:
    try:
        return json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=reject_duplicate_json_keys,
            parse_constant=reject_json_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, CheckError) as exc:
        raise CheckError(f"cannot parse strict JSON for {label}: {exc}") from exc


def require_safe_relative(relative: str, label: str) -> PurePosixPath:
    require(isinstance(relative, str), f"non-string {label} path")
    pure = PurePosixPath(relative)
    require(
        bool(relative)
        and "\\" not in relative
        and "\x00" not in relative
        and all(0x20 <= ord(character) < 0x7F for character in relative)
        and ":" not in relative
        and not pure.is_absolute()
        and ".." not in pure.parts
        and "." not in pure.parts
        and all(
            not part.endswith((".", " "))
            and re.fullmatch(
                r"(?i)(?:con|prn|aux|nul|com[1-9]|lpt[1-9])(?:\..*)?",
                part,
            )
            is None
            for part in pure.parts
        )
        and pure.as_posix() == relative,
        f"unsafe {label} path: {relative!r}",
    )
    return pure


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def require_publication_safe(text: str, label: str) -> None:
    private_key_markers = (
        "-" * 5 + "BEGIN " + "PRIVATE KEY" + "-" * 5,
        "-" * 5 + "BEGIN RSA " + "PRIVATE KEY" + "-" * 5,
        "-" * 5 + "BEGIN OPENSSH " + "PRIVATE KEY" + "-" * 5,
        "-" * 5 + "BEGIN EC " + "PRIVATE KEY" + "-" * 5,
    )
    credential_patterns = (
        r"(?im)\b(?:api[_-]?key|access[_-]?token|auth[_-]?token|client[_-]?secret|secret[_-]?key|password)\b\s*[:=]\s*[\"']?[A-Za-z0-9_./+=-]{8,}",
        r"(?i)\bAKIA[0-9A-Z]{16}\b",
        r"(?i)\bgh[pousr]_[A-Za-z0-9]{30,}\b",
        r"(?i)\bsk-[A-Za-z0-9]{20,}\b",
    )
    require("\x00" not in text, f"released {label} contains a NUL byte")
    require(
        all(marker not in text for marker in private_key_markers),
        f"released {label} contains a private-key marker",
    )
    require(
        all(re.search(pattern, text) is None for pattern in credential_patterns),
        f"released {label} contains a credential/token pattern",
    )


def read_utf8(path: Path, label: str) -> str:
    raw = require_plain_file(path, label).read_bytes()
    try:
        return raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise CheckError(f"released {label} is not UTF-8: {path}") from exc


def parse_result(text: str) -> dict[str, str]:
    require("\r" not in text and text.endswith("\n"), "released RUN_RESULT is not canonical LF text")
    result: dict[str, str] = {}
    for line in text[:-1].split("\n"):
        require(bool(line) and " " in line, f"malformed RUN_RESULT line: {line!r}")
        key, value = line.split(" ", 1)
        require(re.fullmatch(r"[A-Z0-9_]+", key) is not None, f"bad RUN_RESULT key: {key}")
        require(key not in result and bool(value), f"bad RUN_RESULT field: {key}")
        result[key] = value
    require(set(result) == RESULT_FIELDS, "released RUN_RESULT field set mismatch")
    require(result.get("MODE") == "full-global-replay", "release is not a full replay")
    require(result.get("EXIT_CODE") == "0", "released run did not exit successfully")
    require(result.get("FINAL_MARKER") == FULL_MARKER, "released final marker mismatch")
    require(
        result.get("LEAN_ELABORATION_THREADS") == "1"
        and result.get("LEAN_NUM_THREADS") == "1",
        "released run did not use the required single-thread Lean runtime policy",
    )
    require("FAILURE" not in result, "released result contains a failure")
    require(
        result.get("TRANSCRIPT") == "ORCHESTRATOR_TRANSCRIPT.txt",
        "released run has the wrong transcript binding",
    )
    timestamp_pattern = re.compile(
        r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d{7}(?:Z|[+-]\d{2}:\d{2})"
    )
    require(
        timestamp_pattern.fullmatch(result["STARTED_AT"]) is not None
        and timestamp_pattern.fullmatch(result["COMPLETED_AT"]) is not None,
        "released RUN_RESULT contains a malformed timestamp",
    )
    require(
        isinstance(result.get("INITIAL_MANIFEST_SHA256"), str)
        and HEX64.fullmatch(result["INITIAL_MANIFEST_SHA256"]) is not None
        and result.get("MANIFEST_SHA256") == result["INITIAL_MANIFEST_SHA256"],
        "released run does not bind one stable source manifest",
    )
    require(
        all(HEX64.fullmatch(result[key]) is not None for key in RESULT_FIELDS - RESULT_NONDIGEST_FIELDS),
        "released RUN_RESULT contains a malformed successful-stage digest",
    )
    return result


def read_release_manifest(path: Path) -> dict[str, str]:
    raw = require_plain_file(path, "release manifest").read_bytes()
    try:
        text = raw.decode("ascii")
    except UnicodeDecodeError as exc:
        raise CheckError("release manifest is not ASCII") from exc
    require(text.endswith("\n") and "\r" not in text, "release manifest is not canonical LF text")
    entries: dict[str, str] = {}
    lines = text[:-1].split("\n")
    order = []
    for line in lines:
        match = re.fullmatch(r"([0-9a-f]{64})  ([A-Za-z0-9_.-]+)", line)
        require(match is not None, f"malformed release-manifest line: {line!r}")
        digest, name = match.groups()
        require(name not in entries, f"duplicate release-manifest entry: {name}")
        entries[name] = digest
        order.append(name)
    require(set(entries) == PAYLOAD_FILES, "release-manifest file set mismatch")
    require(order == sorted(order), "release manifest is not sorted by filename")
    return entries


def read_stage_log_manifest(raw: bytes) -> dict[str, str]:
    try:
        text = raw.decode("ascii")
    except UnicodeDecodeError as exc:
        raise CheckError("released stage-log manifest is not ASCII") from exc
    require(text.endswith("\n") and "\r" not in text, "stage-log manifest is not canonical")
    lines = text[:-1].split("\n")
    require(bool(lines) and lines == sorted(lines), "stage-log manifest is empty or unsorted")
    result: dict[str, str] = {}
    for line in lines:
        match = re.fullmatch(
            r"([0-9a-f]{64})  logs/([A-Za-z0-9_.-]+\.(?:stdout|stderr)\.txt)",
            line,
        )
        require(match is not None, f"malformed stage-log manifest line: {line!r}")
        digest, name = match.groups()
        require(name not in result, f"duplicate stage-log entry: {name}")
        result[name] = digest
    return result


def validate_source_package(manifest_path: Path, raw: bytes) -> None:
    try:
        text = raw.decode("ascii")
    except UnicodeDecodeError as exc:
        raise CheckError("source package manifest is not ASCII") from exc
    require(text.endswith("\n") and "\r" not in text, "source manifest is not canonical")
    expected: dict[str, str] = {}
    normalized_names: set[str] = set()
    order = []
    for line in text[:-1].split("\n"):
        match = re.fullmatch(r"([0-9a-f]{64})  (.+)", line)
        require(match is not None, f"malformed source-manifest line: {line!r}")
        digest, relative = match.groups()
        pure = require_safe_relative(relative, "source-manifest")
        require(
            ".run" not in {part.lower() for part in pure.parts}
            and relative.casefold() != "manifest.sha256",
            f"forbidden source-manifest path: {relative!r}",
        )
        normalized = os.path.normcase(relative)
        require(
            normalized not in normalized_names,
            f"duplicate/aliased source-manifest path: {relative}",
        )
        normalized_names.add(normalized)
        expected[relative] = digest
        order.append(relative)
    require(order == sorted(order), "source package manifest is not sorted by path")

    root = require_plain_directory_tree(
        manifest_path.parent, "source package directory", manifest_path.parent
    )
    observed: dict[str, Path] = {}
    observed_normalized: set[str] = set()
    pending = [root]
    while pending:
        directory = pending.pop()
        for entry in os.scandir(directory):
            path = Path(entry.path)
            if entry.name.lower() == ".run":
                require_plain_directory(path, "excluded source .run directory")
                continue
            try:
                info = path.lstat()
            except OSError as exc:
                raise CheckError(f"cannot inspect source package entry: {path}: {exc}") from exc
            require(not is_link_like(path), f"source package contains a link: {path}")
            if stat.S_ISDIR(info.st_mode):
                pending.append(path)
            elif stat.S_ISREG(info.st_mode):
                require(info.st_nlink == 1, f"source package contains a hard link: {path}")
                if os.path.normcase(str(path)) != os.path.normcase(str(manifest_path)):
                    relative = path.relative_to(root).as_posix()
                    normalized = os.path.normcase(relative)
                    require(
                        normalized not in observed_normalized,
                        f"source package contains aliased paths: {relative}",
                    )
                    observed_normalized.add(normalized)
                    observed[relative] = path
            else:
                raise CheckError(f"source package contains a special file: {path}")
    require(set(observed) == set(expected), "source package and manifest exact sets differ")
    for relative, digest in expected.items():
        actual = sha256_file(observed[relative])
        require(actual == digest, f"source package SHA-256 mismatch: {relative}: {actual}")
    require(
        require_plain_file_tree(
            manifest_path, "final source package manifest", manifest_path.parent
        ).read_bytes()
        == raw,
        "source package manifest changed during package validation",
    )


def canonical_json(value: Any) -> bytes:
    return (
        json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
            allow_nan=False,
        )
        + "\n"
    ).encode("ascii")


def validate_config3_source_bindings(
    source_root: Path, outer_result: dict[str, str]
) -> None:
    root = require_plain_directory_tree(source_root, "Config3 source-package root")
    paths: dict[str, Path] = {}
    for field, relative in CONFIG3_RELEASE_BINDINGS.items():
        pure = require_safe_relative(relative, f"Config3 {field}")
        path = require_plain_file_tree(
            root.joinpath(*pure.parts), f"Config3 source binding {field}", root
        )
        require(
            sha256_file(path) == outer_result[field],
            f"Config3 source binding differs from RUN_RESULT: {field}",
        )
        paths[field] = path

    release_raw = paths["CONFIG3_RELEASE_RECORD_SHA256"].read_bytes()
    run_raw = paths["CONFIG3_RUN_RESULT_SHA256"].read_bytes()
    release = parse_strict_json(release_raw, "Config3 released RELEASE.json")
    run_result = parse_strict_json(run_raw, "Config3 released RUN_RESULT.json")
    require(
        canonical_json(release) == release_raw and canonical_json(run_result) == run_raw,
        "Config3 root records are not canonical JSON",
    )
    require(
        isinstance(release, dict)
        and set(release)
        == {
            "schema",
            "status",
            "scope",
            "evidence_origin",
            "engine",
            "source_inputs",
            "tooling",
            "parent_plan_provenance",
            "split_plan_provenance",
            "transient_replacement_provenance",
            "common_flags",
            "logical_roster",
            "counts",
            "split_proof",
            "run_result",
        }
        and release["schema"] == "config3-a2-frozen-split-release-v1"
        and release["status"] == "PASS"
        and release["counts"]
        == {
            "logical_partitions": 47,
            "direct_partitions": 46,
            "split_children": 22,
            "zero_processes": 68,
            "frontier_censuses": 1,
            "logical_nodes": 167742832,
            "direct_nodes": 124893923,
            "child_reported_nodes": 42848972,
            "normalization_subtraction": 63,
            "normalized_parent_nodes": 42848909,
        }
        and isinstance(release["logical_roster"], list)
        and all(isinstance(item, str) for item in release["logical_roster"])
        and len(release["logical_roster"]) == len(set(release["logical_roster"])) == 47
        and release["run_result"]
        == {
            "bytes": len(run_raw),
            "path": "RUN_RESULT.json",
            "sha256": outer_result["CONFIG3_RUN_RESULT_SHA256"],
        },
        "Config3 RELEASE.json contract mismatch in publication release",
    )
    require(
        isinstance(run_result, dict)
        and set(run_result)
        == {
            "schema",
            "status",
            "release_schema",
            "engine_sha256",
            "logical_partition_count",
            "logical_node_sum",
            "logical_roster",
            "direct_partition_count",
            "direct_node_sum",
            "direct_receipts",
            "split_replacement",
            "physical_zero_process_count",
            "frontier_census_process_count",
        }
        and run_result["schema"] == "config3-a2-frozen-split-run-result-v1"
        and run_result["status"] == "PASS"
        and run_result["release_schema"] == release["schema"]
        and run_result["logical_partition_count"] == 47
        and run_result["logical_node_sum"] == 167742832
        and run_result["logical_roster"] == release["logical_roster"]
        and run_result["direct_partition_count"] == 46
        and run_result["direct_node_sum"] == 124893923
        and isinstance(run_result["direct_receipts"], list)
        and len(run_result["direct_receipts"]) == 46
        and isinstance(run_result["split_replacement"], dict)
        and run_result["split_replacement"].get("child_count") == 22
        and isinstance(run_result["split_replacement"].get("children"), list)
        and len(run_result["split_replacement"]["children"]) == 22
        and run_result["physical_zero_process_count"] == 68
        and run_result["frontier_census_process_count"] == 1,
        "Config3 RUN_RESULT.json contract mismatch in publication release",
    )

    release_root = paths["CONFIG3_RELEASE_RECORD_SHA256"].parent
    release_sidecar = require_plain_file_tree(
        release_root / "RELEASE.json.sha256", "Config3 RELEASE sidecar", release_root
    )
    run_sidecar = require_plain_file_tree(
        release_root / "RUN_RESULT.json.sha256", "Config3 RUN_RESULT sidecar", release_root
    )
    require(
        release_sidecar.read_bytes()
        == (
            f"{outer_result['CONFIG3_RELEASE_RECORD_SHA256']}  RELEASE.json\n"
        ).encode("ascii")
        and run_sidecar.read_bytes()
        == (
            f"{outer_result['CONFIG3_RUN_RESULT_SHA256']}  RUN_RESULT.json\n"
        ).encode("ascii"),
        "Config3 root-record sidecar mismatch in publication release",
    )

    hybrid_record_path = require_plain_file_tree(
        root / "HYBRID_PROOF_RECORD.json", "hybrid proof record", root
    )
    hybrid_record = parse_strict_json(
        hybrid_record_path.read_bytes(), "hybrid proof record"
    )
    try:
        spec = hybrid_record["evidence"]["configuration3_fresh_result"]
    except (KeyError, TypeError) as exc:
        raise CheckError("hybrid proof record has no Config3 release contract") from exc
    expected_root = "proof/config3_repair/evidence/full_preserved_v1"
    expected_marker = (
        "CONFIG3_A2_FROZEN_SPLIT_STRICT_OK "
        "schema=config3-a2-frozen-split-release-v1 "
        "logical_partitions=47 direct=46 children=22 logical_nodes=167742832 "
        f"manifest_sha256={outer_result['CONFIG3_RELEASE_MANIFEST_SHA256']} "
        f"release_sha256={outer_result['CONFIG3_RELEASE_RECORD_SHA256']} "
        f"run_result_sha256={outer_result['CONFIG3_RUN_RESULT_SHA256']}"
    )
    require(
        isinstance(spec, dict)
        and set(spec) == CONFIG3_SPEC_FIELDS
        and spec["status"] == "PASS"
        and spec["schema"] == release["schema"]
        and spec["release_directory"] == expected_root
        and spec["engine"] == "preserved"
        and spec["logical_partitions"] == 47
        and spec["direct_partitions"] == 46
        and spec["split_children"] == 22
        and spec["logical_nodes"] == 167742832
        and spec["release_record_path"] == expected_root + "/RELEASE.json"
        and spec["release_sidecar_path"] == expected_root + "/RELEASE.json.sha256"
        and spec["run_result_path"] == expected_root + "/RUN_RESULT.json"
        and spec["run_result_sidecar_path"] == expected_root + "/RUN_RESULT.json.sha256"
        and spec["manifest_path"] == expected_root + "/MANIFEST.sha256"
        and spec["exporter_path"]
        == "proof/config3_repair/freeze_config3_a2_evidence.py"
        and spec["verifier_path"]
        == "proof/config3_repair/verify_config3_a2_frozen.py"
        and spec["split_harness_path"]
        == "proof/config3_repair/run_config3_a2_path8_14_split.py"
        and spec["release_record_sha256"]
        == outer_result["CONFIG3_RELEASE_RECORD_SHA256"]
        and spec["run_result_sha256"] == outer_result["CONFIG3_RUN_RESULT_SHA256"]
        and spec["manifest_sha256"]
        == outer_result["CONFIG3_RELEASE_MANIFEST_SHA256"]
        and spec["release_sidecar_sha256"] == sha256_file(release_sidecar)
        and spec["run_result_sidecar_sha256"] == sha256_file(run_sidecar)
        and spec["expected_marker"] == expected_marker
        and spec["normalized_stdout_sha256"]
        == sha256_bytes(expected_marker.encode("utf-8")),
        "hybrid proof record and Config3 released evidence are not exactly cross-bound",
    )


def check_summary(
    raw: bytes,
    transcript_raw: bytes,
    result_raw: bytes,
    input_digest: str,
    stage_manifest_digest: str,
    stage_hashes: dict[str, str],
    transcript_source_digest: str,
    semantic_stdout_digest: str,
    outer_result: dict[str, str],
) -> None:
    summary = parse_strict_json(raw, "stage-digest summary")
    require(canonical_json(summary) == raw, "stage-digest summary is not canonical JSON")
    require(
        isinstance(summary, dict)
        and set(summary)
        == {
            "schema",
            "input_manifest_sha256",
            "run_result_source_sha256",
            "run_result_released_sha256",
            "transcript_source_sha256",
            "transcript_released_sha256",
            "stage_log_manifest_sha256",
            "extra_redaction_tokens",
            "omitted_run_artifacts",
            "terminal_marker",
            "stages",
        }
        and summary["schema"] == "LEECH18_VERIFICATION_RELEASE_STAGE_DIGESTS_V2"
        and summary["input_manifest_sha256"] == input_digest
        and summary["run_result_source_sha256"] == sha256_bytes(result_raw)
        and summary["run_result_released_sha256"] == sha256_bytes(result_raw)
        and summary["transcript_released_sha256"] == sha256_bytes(transcript_raw)
        and summary["stage_log_manifest_sha256"] == stage_manifest_digest
        and isinstance(summary["extra_redaction_tokens"], int)
        and summary["extra_redaction_tokens"] >= 0
        and summary["terminal_marker"] == FULL_MARKER
        and isinstance(summary["transcript_source_sha256"], str)
        and summary["transcript_source_sha256"] == transcript_source_digest,
        "stage-digest summary header mismatch",
    )
    omitted = summary["omitted_run_artifacts"]
    require(
        isinstance(omitted, dict)
        and set(omitted)
        == {
            "schema",
            "artifacts",
            "runtime_source_manifest_entries",
            "regenerated_plan_manifest_entries",
        }
        and omitted["schema"]
        == "LEECH18_OMITTED_RUN_ARTIFACT_ASSERTIONS_V1"
        and omitted["runtime_source_manifest_entries"] == 16
        and omitted["regenerated_plan_manifest_entries"] == 193,
        "omitted run-artifact assertion header mismatch",
    )
    artifacts = omitted["artifacts"]
    require(
        isinstance(artifacts, list)
        and len(artifacts) == len(OMITTED_ARTIFACT_BINDINGS),
        "omitted run-artifact assertion list mismatch",
    )
    observed_roles: list[str] = []
    for item in artifacts:
        require(
            isinstance(item, dict)
            and set(item) == {"role", "path", "result_field", "sha256"},
            "malformed omitted run-artifact assertion",
        )
        role = item["role"]
        require(
            isinstance(role, str)
            and role in OMITTED_ARTIFACT_BINDINGS
            and role not in observed_roles,
            f"unexpected or duplicate omitted run-artifact role: {role!r}",
        )
        expected_path, expected_field = OMITTED_ARTIFACT_BINDINGS[role]
        require_safe_relative(item["path"], f"omitted run artifact {role}")
        require(
            item["path"] == expected_path
            and item["result_field"] == expected_field
            and item["sha256"] == outer_result[expected_field],
            f"omitted run-artifact assertion differs from RUN_RESULT: {role}",
        )
        observed_roles.append(role)
    require(
        observed_roles == sorted(OMITTED_ARTIFACT_BINDINGS),
        "omitted run-artifact assertions are not in canonical role order",
    )
    stages = summary["stages"]
    require(isinstance(stages, list) and bool(stages), "stage-digest list is empty")
    names = []
    summarized_logs: dict[str, str] = {}
    normalized_logs: dict[str, str] = {}
    for item in stages:
        require(
            isinstance(item, dict) and set(item) == {"stage", "stdout", "stderr"},
            "malformed stage-digest entry",
        )
        name = item["stage"]
        require(isinstance(name, str) and SAFE_LOG.fullmatch(name), "unsafe stage name")
        names.append(name)
        for stream in ("stdout", "stderr"):
            value = item[stream]
            require(
                isinstance(value, dict)
                and set(value) == {"bytes", "sha256", "normalized_text_sha256"}
                and isinstance(value["bytes"], int)
                and value["bytes"] >= 0
                and isinstance(value["sha256"], str)
                and HEX64.fullmatch(value["sha256"]) is not None
                and isinstance(value["normalized_text_sha256"], str)
                and HEX64.fullmatch(value["normalized_text_sha256"]) is not None,
                f"malformed {name} {stream} digest",
            )
            summarized_logs[f"{name}.{stream}.txt"] = value["sha256"]
            normalized_logs[f"{name}.{stream}.txt"] = value[
                "normalized_text_sha256"
            ]
    require(names == sorted(names) and len(names) == len(set(names)), "stage list is not unique/sorted")
    require(
        set(names) == FULL_STAGE_NAMES,
        "full replay stage set mismatch: "
        f"missing={sorted(FULL_STAGE_NAMES - set(names))} "
        f"extra={sorted(set(names) - FULL_STAGE_NAMES)}",
    )
    require(summarized_logs == stage_hashes, "stage summary and stage-log manifest differ")
    require(
        normalized_logs["semantic_bridge.stdout.txt"] == semantic_stdout_digest,
        "semantic-bridge stdout digest differs from RUN_RESULT",
    )


def validate_released_semantic_result(
    release: Path, source_root: Path, outer_result: dict[str, str]
) -> None:
    report_path = require_plain_file_tree(
        release / "SEMANTIC_BRIDGE_RUN_RESULT.json",
        "released semantic bridge result",
        release,
    )
    sidecar_path = require_plain_file_tree(
        release / "SEMANTIC_BRIDGE_RUN_RESULT.sha256",
        "released semantic bridge sidecar",
        release,
    )
    report_raw = report_path.read_bytes()
    report_sha256 = sha256_bytes(report_raw)
    require(
        report_sha256 == outer_result["SEMANTIC_BRIDGE_RUN_RESULT_SHA256"],
        "released semantic bridge result differs from outer RUN_RESULT",
    )
    require(
        sidecar_path.read_bytes()
        == f"{report_sha256}  SEMANTIC_BRIDGE_RUN_RESULT.json\n".encode("ascii"),
        "released semantic bridge sidecar content mismatch",
    )
    source_sidecar = f"{report_sha256}  RUN_RESULT.json\n".encode("ascii")
    require(
        sha256_bytes(source_sidecar)
        == outer_result["SEMANTIC_BRIDGE_RUN_RESULT_SIDECAR_SHA256"],
        "semantic bridge source-sidecar binding differs from outer RUN_RESULT",
    )
    try:
        report_text = report_raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise CheckError("released semantic bridge result is not UTF-8") from exc
    absolute_path_patterns = (
        r"(?i)(?:\\\\\?\\)?[a-z]:[\\/]",
        r"(?i)(?:^|[\s='\"])/(?:home|users|private|tmp)/",
        r"(?i)\\\\[^\\\s]+\\[^\\\s]+",
    )
    require(
        all(re.search(pattern, report_text) is None for pattern in absolute_path_patterns),
        "released semantic bridge result contains an absolute host path",
    )
    require_publication_safe(report_text, "semantic bridge result")
    semantic = parse_strict_json(report_raw, "released semantic bridge result")
    require(
        isinstance(semantic, dict)
        and set(semantic) == SEMANTIC_RESULT_FIELDS
        and semantic["schema"] == "leech18-semantic-bridge-run-result-v1"
        and semantic["status"] == "PASS"
        and semantic["terminal_marker"]
        == "LEECH18_SEMANTIC_BRIDGE_REPLAY_OK rows=8 direct=7 projected=1"
        and semantic["baseline_mode"] == "explicit_fresh"
        and type(semantic["lean_elaboration_threads"]) is int
        and semantic["lean_elaboration_threads"] == 1
        and semantic["baseline_dossier_olean_sha256"]
        == outer_result["FRESH_DOSSIER_OLEAN_SHA256"]
        and semantic["record_sha256"]
        == outer_result["SEMANTIC_BRIDGE_RECORD_SHA256"]
        and semantic["axiom_allowlist"]
        == ["Classical.choice", "Quot.sound", "propext"]
        and semantic["axiom_audit_declarations"]
        == SEMANTIC_AXIOM_DECLARATIONS,
        "released semantic bridge result header mismatch",
    )

    bridge_root = source_root / "semantic_bridge"
    record_path = require_plain_file_tree(
        bridge_root / "SEMANTIC_BRIDGE_RECORD.json",
        "semantic bridge source record",
        source_root,
    )
    record_raw = record_path.read_bytes()
    require(
        sha256_bytes(record_raw) == semantic["record_sha256"],
        "semantic bridge source-record digest mismatch",
    )
    bridge_record = parse_strict_json(record_raw, "semantic bridge source record")
    require(
        isinstance(bridge_record, dict)
        and set(bridge_record)
        == {"schema", "claim", "non_claims", "lean_environment", "inputs", "rows"}
        and bridge_record.get("schema") == "leech18-semantic-bridge-v1"
        and isinstance(bridge_record.get("lean_environment"), dict)
        and set(bridge_record["lean_environment"])
        == {"toolchain", "repository", "commit"}
        and bridge_record["lean_environment"]["repository"]
        == "lean/LeechTrees"
        and isinstance(bridge_record["lean_environment"]["toolchain"], str)
        and isinstance(bridge_record["lean_environment"]["commit"], str)
        and HEX40.fullmatch(bridge_record["lean_environment"]["commit"])
        is not None
        and semantic["lean_toolchain"]
        == bridge_record.get("lean_environment", {}).get("toolchain")
        and semantic["lean_source_commit"]
        == bridge_record.get("lean_environment", {}).get("commit"),
        "released semantic bridge environment binding mismatch",
    )
    bridge_rows = bridge_record.get("rows")
    require(
        isinstance(bridge_rows, list)
        and len(bridge_rows) == 8
        and all(isinstance(row, dict) for row in bridge_rows)
        and [row.get("paper_configuration") for row in bridge_rows]
        == list(range(1, 9))
        and [row.get("solver_row") for row in bridge_rows] == list(range(8)),
        "semantic bridge source-record row roster mismatch",
    )

    hybrid_record_path = require_plain_file_tree(
        source_root / "HYBRID_PROOF_RECORD.json",
        "hybrid proof record",
        source_root,
    )
    hybrid_record = parse_strict_json(
        hybrid_record_path.read_bytes(), "hybrid proof record"
    )
    try:
        semantic_spec = hybrid_record["evidence"]["semantic_bridge"]
    except (KeyError, TypeError) as exc:
        raise CheckError("hybrid proof record has no semantic-bridge contract") from exc
    require(
        isinstance(semantic_spec, dict)
        and set(semantic_spec) == SEMANTIC_SPEC_FIELDS
        and semantic_spec["status"] == "PASS"
        and semantic_spec["directory"] == "proof/semantic_bridge"
        and semantic_spec["record_path"]
        == "proof/semantic_bridge/SEMANTIC_BRIDGE_RECORD.json"
        and semantic_spec["wrapper_path"]
        == "proof/semantic_bridge/verify_semantic_bridge.ps1"
        and semantic_spec["source_files"] == 12
        and semantic_spec["rows"] == 8
        and semantic_spec["direct_rows"] == 7
        and semantic_spec["projected_rows"] == 1
        and semantic_spec["uses_fresh_baseline_lean_lib"] is True
        and semantic_spec["expected_marker"] == semantic["terminal_marker"]
        and semantic_spec["run_result_schema"] == semantic["schema"]
        and semantic_spec["record_sha256"] == semantic["record_sha256"]
        and semantic_spec["run_result_sha256"] == report_sha256
        and semantic_spec["run_result_sidecar_sha256"]
        == sha256_bytes(source_sidecar),
        "hybrid proof record and semantic run result are not exactly cross-bound",
    )
    semantic_wrapper = require_plain_file_tree(
        bridge_root / "verify_semantic_bridge.ps1",
        "semantic bridge wrapper",
        bridge_root,
    )
    require(
        isinstance(semantic_spec["wrapper_sha256"], str)
        and HEX64.fullmatch(semantic_spec["wrapper_sha256"]) is not None
        and sha256_file(semantic_wrapper) == semantic_spec["wrapper_sha256"],
        "semantic bridge wrapper digest differs from the hybrid proof record",
    )

    def exact_path_hash_inventory(
        records: Any, expected_paths: set[str], label: str, rehash_root: Path | None
    ) -> dict[str, str]:
        require(isinstance(records, list), f"{label} inventory is not a list")
        observed: dict[str, str] = {}
        normalized: set[str] = set()
        for item in records:
            require(
                isinstance(item, dict) and set(item) == {"path", "sha256"},
                f"malformed {label} inventory item",
            )
            relative = item["path"]
            pure = require_safe_relative(relative, label)
            digest = item["sha256"]
            require(
                isinstance(digest, str) and HEX64.fullmatch(digest) is not None,
                f"malformed {label} digest: {relative!r}",
            )
            alias = os.path.normcase(relative)
            require(alias not in normalized, f"duplicate/aliased {label} path: {relative}")
            normalized.add(alias)
            observed[relative] = digest
            if rehash_root is not None:
                path = require_plain_file_tree(
                    rehash_root.joinpath(*pure.parts),
                    f"{label} file {relative}",
                    rehash_root,
                )
                require(
                    sha256_file(path) == digest,
                    f"{label} file digest mismatch: {relative}",
                )
        require(
            set(observed) == expected_paths,
            f"{label} exact-set mismatch: "
            f"missing={sorted(expected_paths - set(observed))} "
            f"extra={sorted(set(observed) - expected_paths)}",
        )
        return observed

    exact_path_hash_inventory(
        semantic["bridge_sources"],
        SEMANTIC_BRIDGE_SOURCES,
        "semantic bridge source",
        bridge_root,
    )
    exact_path_hash_inventory(
        semantic["artifacts"],
        SEMANTIC_ARTIFACTS,
        "semantic bridge artifact",
        None,
    )
    log_hashes = exact_path_hash_inventory(
        semantic["logs"], SEMANTIC_LOGS, "semantic bridge log", None
    )
    require(
        log_hashes["logs/lean_semantic_bridge.stdout.txt"]
        == semantic["lean_emitter_stdout_sha256"]
        and log_hashes["logs/full_semantic_bridge.stdout.txt"]
        == semantic["full_checker_stdout_sha256"],
        "released semantic bridge named stdout bindings mismatch",
    )

    recorded_inputs = bridge_record.get("inputs")
    require(isinstance(recorded_inputs, dict), "semantic bridge source inputs are malformed")
    expected_inputs: dict[str, tuple[str, str]] = {}
    for role, item in recorded_inputs.items():
        require(
            isinstance(role, str)
            and isinstance(item, dict)
            and set(item) == {"path", "sha256"}
            and isinstance(item["sha256"], str)
            and HEX64.fullmatch(item["sha256"].lower()) is not None,
            f"malformed semantic bridge source input: {role!r}",
        )
        require_safe_relative(item["path"], f"semantic bridge input {role}")
        expected_inputs[role] = (item["path"], item["sha256"].lower())
    require(
        set(expected_inputs) == SEMANTIC_INPUT_ROLES,
        "semantic bridge source input-role exact set mismatch",
    )
    observed_inputs: dict[str, tuple[str, str]] = {}
    require(isinstance(semantic["pinned_inputs"], list), "semantic pinned inputs are not a list")
    for item in semantic["pinned_inputs"]:
        require(
            isinstance(item, dict) and set(item) == {"role", "path", "sha256"},
            "malformed semantic pinned-input item",
        )
        role = item["role"]
        require(isinstance(role, str) and role not in observed_inputs, "duplicate semantic input role")
        require_safe_relative(item["path"], f"semantic pinned input {role}")
        require(
            isinstance(item["sha256"], str)
            and HEX64.fullmatch(item["sha256"]) is not None,
            f"malformed semantic pinned-input digest: {role}",
        )
        observed_inputs[role] = (item["path"], item["sha256"])
    require(
        observed_inputs == expected_inputs,
        "released semantic pinned-input inventory differs from its source record",
    )
    repository_root = source_root.parent
    for role, (relative, expected_digest) in expected_inputs.items():
        # Explicit-fresh mode replaces the recorded standalone prebuilt olean;
        # the fresh dossier hash is bound by the outer and semantic results.
        if role == "authoritative_dossier_olean":
            continue
        pure = require_safe_relative(relative, f"semantic bridge input {role}")
        source_input = require_plain_file_tree(
            repository_root.joinpath(*pure.parts),
            f"semantic bridge input {role}",
            repository_root,
        )
        require(
            sha256_file(source_input) == expected_digest,
            f"semantic bridge pinned-input file digest mismatch: {role}",
        )


def verify(
    release: Path,
    source_manifest: Path,
    expected_release_manifest_sha256: str,
) -> tuple[str, str]:
    require_plain_file_tree(Path(__file__).absolute(), "release validator")
    release = require_plain_directory_tree(release, "release directory")
    observed = set()
    for entry in os.scandir(release):
        path = Path(entry.path)
        require_plain_file(path, "released file")
        observed.add(entry.name)
    require(observed == ALL_FILES, "released directory file set mismatch")
    release_manifest_path = release / "RELEASE_MANIFEST.sha256"
    manifest = read_release_manifest(release_manifest_path)
    release_manifest_sha256 = sha256_file(release_manifest_path)
    require(
        isinstance(expected_release_manifest_sha256, str)
        and HEX64.fullmatch(expected_release_manifest_sha256) is not None,
        "expected release-manifest SHA-256 is malformed",
    )
    require(
        release_manifest_sha256 == expected_release_manifest_sha256,
        "release-manifest SHA-256 differs from the external expected value",
    )
    for name, expected in manifest.items():
        actual = sha256_file(release / name)
        require(actual == expected, f"released file SHA-256 mismatch: {name}: {actual}")

    released_input = require_plain_file(
        release / "INPUT_MANIFEST.sha256", "released input manifest"
    ).read_bytes()
    source_manifest = require_plain_file_tree(source_manifest, "source manifest")
    try:
        release.resolve(strict=True).relative_to(
            source_manifest.parent.resolve(strict=True)
        )
    except ValueError:
        pass
    else:
        raise CheckError(
            "release directory resolves inside the source proof package"
        )
    current_input = source_manifest.read_bytes()
    require(released_input == current_input, "released and current source manifests differ byte-for-byte")
    validate_source_package(source_manifest, current_input)
    input_digest = sha256_bytes(released_input)

    result_raw = require_plain_file(release / "RUN_RESULT.txt", "released run result").read_bytes()
    result = parse_result(read_utf8(release / "RUN_RESULT.txt", "run result"))
    require(
        result["INITIAL_MANIFEST_SHA256"] == input_digest,
        "RUN_RESULT input-manifest digest does not match the released source manifest",
    )
    validate_config3_source_bindings(source_manifest.parent, result)
    validate_released_semantic_result(release, source_manifest.parent, result)
    transcript_raw = require_plain_file(
        release / "ORCHESTRATOR_TRANSCRIPT.sanitized.txt", "released transcript"
    ).read_bytes()
    transcript = read_utf8(
        release / "ORCHESTRATOR_TRANSCRIPT.sanitized.txt", "transcript"
    )
    require("\r" not in transcript and transcript.endswith("\n"), "transcript is not canonical LF text")
    require(
        transcript.split("\n").count(FULL_MARKER) == 1,
        "transcript does not contain exactly one standalone final marker",
    )
    require("LEECH18_HYBRID_END_TO_END_FAIL" not in transcript, "transcript contains failure marker")
    forbidden = (
        r"(?i)(?:\\\\\?\\)?[a-z]:[\\/]",
        r"(?i)(?:^|[\s='\"])/(?:home|users|private|tmp)/",
        r"(?i)\\\\[^\\\s]+\\[^\\\s]+",
    )
    require(
        all(re.search(pattern, transcript) is None for pattern in forbidden),
        "released transcript contains an absolute host path",
    )
    require_publication_safe(transcript, "transcript")
    summary_raw = require_plain_file(
        release / "STAGE_DIGESTS.json", "stage-digest summary"
    ).read_bytes()
    stage_manifest_raw = require_plain_file(
        release / "STAGE_LOGS.sha256", "released stage-log manifest"
    ).read_bytes()
    stage_manifest_digest = sha256_bytes(stage_manifest_raw)
    require(
        stage_manifest_digest == result["STAGE_LOG_MANIFEST_SHA256"],
        "released stage-log manifest digest differs from RUN_RESULT",
    )
    stage_hashes = read_stage_log_manifest(stage_manifest_raw)
    check_summary(
        summary_raw,
        transcript_raw,
        result_raw,
        input_digest,
        stage_manifest_digest,
        stage_hashes,
        result["TRANSCRIPT_SHA256"],
        result["SEMANTIC_BRIDGE_STDOUT_SHA256"],
        result,
    )
    final_observed = set()
    for entry in os.scandir(release):
        path = require_plain_file(Path(entry.path), "final released file")
        require(entry.name in ALL_FILES, f"unexpected final released file: {entry.name}")
        final_observed.add(entry.name)
        if entry.name == "RELEASE_MANIFEST.sha256":
            require(
                sha256_file(path) == expected_release_manifest_sha256,
                "release manifest changed during validation",
            )
        else:
            require(
                sha256_file(path) == manifest[entry.name],
                f"released file changed during validation: {entry.name}",
            )
    require(final_observed == ALL_FILES, "released file set changed during validation")
    require(
        source_manifest.read_bytes() == current_input,
        "source manifest changed during release validation",
    )
    validate_source_package(source_manifest, current_input)
    final_release_names = {entry.name for entry in os.scandir(release)}
    require(
        final_release_names == ALL_FILES,
        "released file set changed during final source validation",
    )
    require(
        sha256_file(
            require_plain_file(
                release / "RELEASE_MANIFEST.sha256",
                "final release manifest",
            )
        )
        == expected_release_manifest_sha256,
        "release manifest changed before publication marker",
    )
    for name, expected in manifest.items():
        require(
            sha256_file(
                require_plain_file(release / name, f"final released file {name}")
            )
            == expected,
            f"released file changed before publication marker: {name}",
        )
    return input_digest, release_manifest_sha256


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--release", required=True, type=Path)
    parser.add_argument("--source-manifest", type=Path, default=DEFAULT_SOURCE_MANIFEST)
    parser.add_argument(
        "--expected-release-manifest-sha256",
        required=True,
        help="externally retained SHA-256 identity of RELEASE_MANIFEST.sha256",
    )
    args = parser.parse_args(argv)
    try:
        manifest_sha256, release_manifest_sha256 = verify(
            args.release,
            args.source_manifest,
            args.expected_release_manifest_sha256,
        )
        print(
            "LEECH18_VERIFICATION_RELEASE_OK "
            f"files={len(PAYLOAD_FILES)} input_manifest_sha256={manifest_sha256} "
            f"release_manifest_sha256={release_manifest_sha256}"
        )
        return 0
    except (CheckError, OSError, ValueError) as exc:
        print(f"LEECH18_VERIFICATION_RELEASE_FAIL: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
