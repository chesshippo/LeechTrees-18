#!/usr/bin/env python3
"""Export a successful full replay from .run into a separate release tree."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import sys
import tempfile
from pathlib import Path, PurePosixPath
from typing import Any, Sequence


HERE = Path(__file__).absolute().parent
RUN_BASE = HERE / ".run"
SOURCE_MANIFEST = HERE / "MANIFEST.sha256"
HEX64 = re.compile(r"[0-9a-f]{64}")
HEX40 = re.compile(r"[0-9a-f]{40}")
SAFE_LOG = re.compile(r"[A-Za-z0-9_.-]+")
FULL_MARKER = (
    "LEECH18_HYBRID_END_TO_END_PASS configurations=8 "
    "reported_node_visits=8565199014 global_status=GLOBAL_ZERO_COMPLETE"
)
RELEASE_FILES = {
    "INPUT_MANIFEST.sha256",
    "ORCHESTRATOR_TRANSCRIPT.sanitized.txt",
    "RUN_RESULT.txt",
    "SEMANTIC_BRIDGE_RUN_RESULT.json",
    "SEMANTIC_BRIDGE_RUN_RESULT.sha256",
    "STAGE_LOGS.sha256",
    "STAGE_DIGESTS.json",
}
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
RUNTIME_TARGETS = {
    "g001_remaining_witness_solver.exe",
    "check_g001_leech_witness.exe",
    "test_g001_remaining_witness_solver.exe",
}
RUNTIME_LOGS = {
    "compiler_version.stdout.txt",
    "compiler_version.stderr.txt",
    *(f"compile_{target.removesuffix('.exe')}.{stream}.txt"
      for target in RUNTIME_TARGETS for stream in ("stdout", "stderr")),
    "witness_regression.stdout.txt",
    "witness_regression.stderr.txt",
    "checker_self_test.stdout.txt",
    "checker_self_test.stderr.txt",
}
PLAN_BUNDLES = {
    f"bundle_plans/bundle_{index:03d}.json" for index in range(192)
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


class ExportError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ExportError(message)


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
        raise ExportError(f"cannot inspect {label}: {path}: {exc}") from exc
    require(
        stat.S_ISDIR(info.st_mode) and not is_link_like(path),
        f"{label} is not a plain directory: {path}",
    )
    return path


def require_plain_file(path: Path, label: str) -> Path:
    try:
        info = path.lstat()
    except OSError as exc:
        raise ExportError(f"cannot inspect {label}: {path}: {exc}") from exc
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
        raise ExportError(f"{label} is outside its permitted root: {target}") from exc
    current = require_plain_directory(base, f"{label} root")
    for part in relative.parts[:-1]:
        current = require_plain_directory(current / part, f"{label} ancestor")
    require(not is_link_like(target), f"{label} leaf is a link/reparse point: {target}")
    try:
        target.resolve(strict=True).relative_to(base.resolve(strict=True))
    except (OSError, ValueError) as exc:
        raise ExportError(
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
    raise ExportError(f"non-finite JSON number is forbidden: {value}")


def parse_strict_json(raw: bytes, label: str) -> Any:
    try:
        return json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=reject_duplicate_json_keys,
            parse_constant=reject_json_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, ExportError) as exc:
        raise ExportError(f"cannot parse strict JSON for {label}: {exc}") from exc


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


def parse_exact_relative_manifest(
    raw: bytes, expected_order: Sequence[str], label: str
) -> dict[str, str]:
    try:
        text = raw.decode("ascii")
    except UnicodeDecodeError as exc:
        raise ExportError(f"{label} manifest is not ASCII") from exc
    require(
        text.endswith("\n") and "\r" not in text,
        f"{label} manifest is not canonical LF text",
    )
    lines = text[:-1].split("\n")
    require(len(lines) == len(expected_order), f"{label} manifest length mismatch")
    entries: dict[str, str] = {}
    order: list[str] = []
    normalized: set[str] = set()
    for line in lines:
        match = re.fullmatch(r"([0-9a-f]{64})  (.+)", line)
        require(match is not None, f"malformed {label} manifest line: {line!r}")
        digest, relative = match.groups()
        require_safe_relative(relative, f"{label} manifest")
        alias = os.path.normcase(relative.replace("/", os.sep))
        require(
            relative not in entries and alias not in normalized,
            f"duplicate or aliased {label} manifest path: {relative}",
        )
        entries[relative] = digest
        normalized.add(alias)
        order.append(relative)
    require(order == list(expected_order), f"{label} manifest order/set mismatch")
    return entries


def validate_source_package(manifest_path: Path, raw: bytes) -> None:
    try:
        text = raw.decode("ascii")
    except UnicodeDecodeError as exc:
        raise ExportError("source package manifest is not ASCII") from exc
    require(
        text.endswith("\n") and "\r" not in text,
        "source package manifest is not canonical LF text",
    )
    expected: dict[str, str] = {}
    normalized_names: set[str] = set()
    order: list[str] = []
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
        manifest_path.parent, "source package directory", HERE
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
                raise ExportError(
                    f"cannot inspect source package entry {path}: {exc}"
                ) from exc
            require(not is_link_like(path), f"source package contains a link: {path}")
            if stat.S_ISDIR(info.st_mode):
                pending.append(path)
            elif stat.S_ISREG(info.st_mode):
                require(
                    info.st_nlink == 1,
                    f"source package contains a hard-linked file: {path}",
                )
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
                raise ExportError(f"source package contains a special file: {path}")
    require(
        set(observed) == set(expected),
        "source package and source manifest exact sets differ",
    )
    for relative, digest in expected.items():
        actual = sha256_file(observed[relative])
        require(
            actual == digest,
            f"source package SHA-256 mismatch: {relative}: {actual}",
        )
    require(
        require_plain_file_tree(
            manifest_path, "final source package manifest", root
        ).read_bytes()
        == raw,
        "source package manifest changed during package validation",
    )


def decode_text(raw: bytes, label: str) -> str:
    try:
        if raw.startswith((b"\xff\xfe", b"\xfe\xff")):
            return raw.decode("utf-16")
        return raw.decode("utf-8-sig")
    except UnicodeDecodeError as exc:
        raise ExportError(f"{label} is neither BOM-marked UTF-16 nor UTF-8") from exc


def read_text(path: Path, label: str) -> str:
    raw = require_plain_file(path, label).read_bytes()
    return decode_text(raw, label)


def normalized_text(text: str) -> str:
    return text.replace("\r\n", "\n").replace("\r", "\n").rstrip("\n")


def normalized_text_sha256(text: str) -> str:
    return sha256_bytes(normalized_text(text).encode("utf-8"))


def parse_run_result(text: str) -> dict[str, str]:
    result: dict[str, str] = {}
    for line in normalized_text(text).split("\n"):
        require(bool(line) and " " in line, f"malformed RUN_RESULT line: {line!r}")
        key, value = line.split(" ", 1)
        require(re.fullmatch(r"[A-Z0-9_]+", key) is not None, f"bad RUN_RESULT key: {key}")
        require(key not in result, f"duplicate RUN_RESULT key: {key}")
        require(bool(value), f"empty RUN_RESULT value: {key}")
        result[key] = value
    required = {
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
    require(set(result) == required, "RUN_RESULT field set mismatch")
    require(result["MODE"] == "full-global-replay", "run was not a full global replay")
    require(result["EXIT_CODE"] == "0", "run did not exit successfully")
    require(result["FINAL_MARKER"] == FULL_MARKER, "run has the wrong final marker")
    require(
        result["LEAN_ELABORATION_THREADS"] == "1"
        and result["LEAN_NUM_THREADS"] == "1",
        "run did not use the required single-thread Lean runtime policy",
    )
    require(
        result["TRANSCRIPT"] == "ORCHESTRATOR_TRANSCRIPT.txt",
        "run has the wrong transcript binding",
    )
    timestamp_pattern = re.compile(
        r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d{7}(?:Z|[+-]\d{2}:\d{2})"
    )
    require(
        timestamp_pattern.fullmatch(result["STARTED_AT"]) is not None
        and timestamp_pattern.fullmatch(result["COMPLETED_AT"]) is not None,
        "RUN_RESULT contains a malformed timestamp",
    )
    digest_fields = required - {
        "MODE",
        "EXIT_CODE",
        "FINAL_MARKER",
        "LEAN_ELABORATION_THREADS",
        "LEAN_NUM_THREADS",
        "TRANSCRIPT",
        "STARTED_AT",
        "COMPLETED_AT",
    }
    require(
        all(HEX64.fullmatch(result[key]) is not None for key in digest_fields),
        "RUN_RESULT contains a missing or malformed successful-stage digest",
    )
    require(
        result["MANIFEST_SHA256"] == result["INITIAL_MANIFEST_SHA256"],
        "source package manifest changed during the successful run",
    )
    return result


def replace_root(text: str, root: str, token: str) -> str:
    variants = {
        root.rstrip("\\/"),
        root.rstrip("\\/").replace("\\", "/"),
    }
    if re.match(r"^[A-Za-z]:[\\/]", root):
        variants.add("\\\\?\\" + root.rstrip("\\/"))
    for variant in sorted((item for item in variants if item), key=len, reverse=True):
        text = re.sub(re.escape(variant), token, text, flags=re.IGNORECASE)
    return text


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
    require("\x00" not in text, f"{label} contains a NUL byte")
    require(
        all(marker not in text for marker in private_key_markers),
        f"{label} contains a private-key marker",
    )
    require(
        all(re.search(pattern, text) is None for pattern in credential_patterns),
        f"{label} contains a credential/token pattern",
    )


def sanitize_transcript(
    text: str, run_directory: Path, extra_redaction_roots: Sequence[Path]
) -> str:
    sanitized = normalized_text(text)
    roots: list[tuple[str, str]] = [
        (str(run_directory.resolve()), "<RUN_ROOT>"),
        (str(HERE.parent.resolve()), "<WORKSPACE_ROOT>"),
    ]
    environment_roots = (
        ("USERPROFILE", "<USER_HOME>"),
        ("HOME", "<USER_HOME>"),
        ("LOCALAPPDATA", "<LOCAL_APP_DATA>"),
        ("APPDATA", "<APP_DATA>"),
        ("ProgramFiles", "<PROGRAM_FILES>"),
        ("ProgramFiles(x86)", "<PROGRAM_FILES_X86>"),
        ("ProgramData", "<PROGRAM_DATA>"),
        ("SystemRoot", "<SYSTEM_ROOT>"),
        ("TEMP", "<TEMP_ROOT>"),
        ("TMP", "<TEMP_ROOT>"),
    )
    roots.extend(
        (value, token)
        for name, token in environment_roots
        if (value := os.environ.get(name))
    )
    for index, candidate in enumerate(extra_redaction_roots, start=1):
        plain = require_plain_ancestor_chain(
            candidate, f"extra redaction root {index}"
        )
        info = plain.lstat()
        require(
            not is_link_like(plain)
            and (
                stat.S_ISDIR(info.st_mode)
                or (stat.S_ISREG(info.st_mode) and info.st_nlink == 1)
            ),
            f"extra redaction root {index} is linked or special: {plain}",
        )
        resolved = plain.resolve(strict=True)
        require(
            str(resolved) != resolved.anchor,
            "an extra redaction root may not be a filesystem root",
        )
        roots.append((str(resolved), f"<EXTRA_HOST_PATH_{index}>"))
    for root, token in sorted(roots, key=lambda item: len(item[0]), reverse=True):
        sanitized = replace_root(sanitized, root, token)
    identity_variables = (
        ("USERDOMAIN", "<DOMAIN>"),
        ("USERNAME", "<USER>"),
        ("COMPUTERNAME", "<HOST>"),
    )
    for name, token in identity_variables:
        value = os.environ.get(name)
        if value:
            sanitized = re.sub(
                r"(?<![A-Za-z0-9_.-])" + re.escape(value)
                + r"(?![A-Za-z0-9_.-])",
                token,
                sanitized,
                flags=re.IGNORECASE,
            )
    private_patterns = (
        r"(?i)(?:\\\\\?\\)?[a-z]:[\\/]",
        r"(?i)(?:^|[\s='\"])/(?:home|users|private|tmp)/",
        r"(?i)\\\\[^\\\s]+\\[^\\\s]+",
    )
    for pattern in private_patterns:
        require(
            re.search(pattern, sanitized) is None,
            f"sanitized transcript still contains an absolute host path matching {pattern}",
        )
    require(
        sanitized.split("\n").count(FULL_MARKER) == 1,
        "transcript does not contain exactly one standalone final marker",
    )
    require(
        "LEECH18_HYBRID_END_TO_END_FAIL" not in sanitized,
        "transcript also contains the failure marker",
    )
    require_publication_safe(sanitized, "sanitized transcript")
    return sanitized + "\n"


def read_stage_log_manifest(raw: bytes) -> dict[str, str]:
    try:
        text = raw.decode("ascii")
    except UnicodeDecodeError as exc:
        raise ExportError("stage-log manifest is not ASCII") from exc
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
        require(name not in result, f"duplicate stage-log manifest entry: {name}")
        result[name] = digest
    return result


def inventory_stage_logs(
    log_root: Path, expected_hashes: dict[str, str]
) -> list[dict[str, Any]]:
    require_plain_directory(log_root, "stage-log directory")
    observed: dict[str, dict[str, Path]] = {}
    for entry in os.scandir(log_root):
        path = Path(entry.path)
        require_plain_file(path, "stage log")
        match = re.fullmatch(r"(.+)\.(stdout|stderr)\.txt", entry.name)
        require(match is not None, f"unexpected stage-log filename: {entry.name}")
        stage, stream = match.groups()
        require(SAFE_LOG.fullmatch(stage) is not None, f"unsafe stage name: {stage}")
        require(stream not in observed.setdefault(stage, {}), f"duplicate {stage} {stream} log")
        observed[stage][stream] = path
    require(bool(observed), "stage-log directory is empty")
    require(
        set(observed) == FULL_STAGE_NAMES,
        "full replay stage set mismatch: "
        f"missing={sorted(FULL_STAGE_NAMES - set(observed))} "
        f"extra={sorted(set(observed) - FULL_STAGE_NAMES)}",
    )
    require(
        all(set(streams) == {"stdout", "stderr"} for streams in observed.values()),
        "a stage is missing its stdout/stderr log pair",
    )
    observed_names = {
        path.name for streams in observed.values() for path in streams.values()
    }
    require(observed_names == set(expected_hashes), "stage-log manifest exact-set mismatch")
    stages = []
    for stage in sorted(observed):
        item: dict[str, Any] = {"stage": stage}
        for stream in ("stdout", "stderr"):
            path = observed[stage][stream]
            raw = path.read_bytes()
            require(
                sha256_bytes(raw) == expected_hashes[path.name],
                f"stage log changed after the run: {path.name}",
            )
            text = decode_text(raw, f"stage log {path}")
            item[stream] = {
                "bytes": len(raw),
                "sha256": sha256_bytes(raw),
                "normalized_text_sha256": normalized_text_sha256(text),
            }
        stages.append(item)
    return stages


def validate_semantic_result(
    run_directory: Path, outer_result: dict[str, str]
) -> tuple[bytes, bytes]:
    semantic_root = require_plain_directory_tree(
        run_directory / "semantic_bridge",
        "semantic bridge run directory",
        run_directory,
    )
    result_path = require_plain_file_tree(
        semantic_root / "RUN_RESULT.json",
        "semantic bridge run result",
        semantic_root,
    )
    sidecar_path = require_plain_file_tree(
        semantic_root / "RUN_RESULT.sha256",
        "semantic bridge run-result sidecar",
        semantic_root,
    )
    result_raw = result_path.read_bytes()
    result_sha256 = sha256_bytes(result_raw)
    require(
        result_sha256 == outer_result["SEMANTIC_BRIDGE_RUN_RESULT_SHA256"],
        "semantic bridge run-result digest differs from outer RUN_RESULT",
    )
    source_sidecar = f"{result_sha256}  RUN_RESULT.json\n".encode("ascii")
    sidecar_raw = sidecar_path.read_bytes()
    require(
        sidecar_raw == source_sidecar,
        "semantic bridge source sidecar content mismatch",
    )
    require(
        sha256_bytes(sidecar_raw)
        == outer_result["SEMANTIC_BRIDGE_RUN_RESULT_SIDECAR_SHA256"],
        "semantic bridge source-sidecar digest differs from outer RUN_RESULT",
    )
    try:
        result_text = result_raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ExportError("semantic bridge run result is not UTF-8") from exc
    absolute_path_patterns = (
        r"(?i)(?:\\\\\?\\)?[a-z]:[\\/]",
        r"(?i)(?:^|[\s='\"])/(?:home|users|private|tmp)/",
        r"(?i)\\\\[^\\\s]+\\[^\\\s]+",
    )
    require(
        all(re.search(pattern, result_text) is None for pattern in absolute_path_patterns),
        "semantic bridge run result contains an absolute host path",
    )
    require_publication_safe(result_text, "semantic bridge run result")
    semantic = parse_strict_json(result_raw, "semantic bridge run result")
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
        "semantic bridge run-result header mismatch",
    )

    bridge_root = HERE / "semantic_bridge"
    bridge_record_path = require_plain_file_tree(
        bridge_root / "SEMANTIC_BRIDGE_RECORD.json",
        "semantic bridge source record",
        HERE,
    )
    bridge_record_raw = bridge_record_path.read_bytes()
    require(
        sha256_bytes(bridge_record_raw) == semantic["record_sha256"],
        "semantic bridge source record digest mismatch",
    )
    bridge_record = parse_strict_json(bridge_record_raw, "semantic bridge source record")
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
        "semantic bridge environment binding mismatch",
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
        HERE / "HYBRID_PROOF_RECORD.json",
        "hybrid proof record",
        HERE,
    )
    hybrid_record = parse_strict_json(
        hybrid_record_path.read_bytes(), "hybrid proof record"
    )
    try:
        semantic_spec = hybrid_record["evidence"]["semantic_bridge"]
    except (KeyError, TypeError) as exc:
        raise ExportError("hybrid proof record has no semantic-bridge contract") from exc
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
        and semantic_spec["run_result_sha256"] == result_sha256
        and semantic_spec["run_result_sidecar_sha256"]
        == sha256_bytes(sidecar_raw),
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
        records: Any,
        expected_paths: set[str],
        label: str,
        root: Path,
        rehash: bool,
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
            if rehash:
                path = require_plain_file_tree(
                    root.joinpath(*pure.parts), f"{label} file {relative}", root
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
        True,
    )
    artifact_hashes = exact_path_hash_inventory(
        semantic["artifacts"],
        SEMANTIC_ARTIFACTS,
        "semantic bridge artifact",
        semantic_root,
        True,
    )
    log_hashes = exact_path_hash_inventory(
        semantic["logs"],
        SEMANTIC_LOGS,
        "semantic bridge log",
        semantic_root,
        True,
    )
    require(
        log_hashes["logs/lean_semantic_bridge.stdout.txt"]
        == semantic["lean_emitter_stdout_sha256"]
        and log_hashes["logs/full_semantic_bridge.stdout.txt"]
        == semantic["full_checker_stdout_sha256"],
        "semantic bridge named stdout bindings mismatch",
    )
    require(len(artifact_hashes) == 8, "semantic bridge artifact count mismatch")

    recorded_inputs = bridge_record.get("inputs")
    require(isinstance(recorded_inputs, dict), "semantic bridge input record is malformed")
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
        "semantic bridge pinned-input inventory differs from its source record",
    )
    repository_root = HERE.parent
    for role, (relative, expected_digest) in expected_inputs.items():
        # Explicit-fresh mode intentionally does not consume the recorded
        # standalone prebuilt olean.  Its replacement is the fresh dossier
        # olean already bound above by the outer and semantic results.
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
    released_sidecar = (
        f"{result_sha256}  SEMANTIC_BRIDGE_RUN_RESULT.json\n"
    ).encode("ascii")
    return result_raw, released_sidecar


def validate_omitted_run_artifacts(
    run_directory: Path, result: dict[str, str]
) -> dict[str, Any]:
    runtime_root = require_plain_directory_tree(
        run_directory / "frozen_runtime_source",
        "runtime-source output directory",
        run_directory,
    )
    runtime_bin = require_plain_directory_tree(
        runtime_root / "bin", "runtime-source binary directory", runtime_root
    )
    runtime_logs = require_plain_directory_tree(
        runtime_root / "logs", "runtime-source log directory", runtime_root
    )
    require(
        {entry.name for entry in os.scandir(runtime_root)}
        == {
            "bin",
            "logs",
            "runtime_source_validation.json",
            "runtime_source_validation.sha256",
        },
        "runtime-source output root exact-set mismatch during export",
    )
    require(
        {entry.name for entry in os.scandir(runtime_bin)} == RUNTIME_TARGETS,
        "runtime-source binary exact-set mismatch during export",
    )
    require(
        {entry.name for entry in os.scandir(runtime_logs)} == RUNTIME_LOGS,
        "runtime-source log exact-set mismatch during export",
    )
    runtime_manifest_path = require_plain_file_tree(
        runtime_root / "runtime_source_validation.sha256",
        "runtime-source output manifest",
        runtime_root,
    )
    runtime_manifest_raw = runtime_manifest_path.read_bytes()
    require(
        sha256_bytes(runtime_manifest_raw)
        == result["RUNTIME_SOURCE_MANIFEST_SHA256"],
        "runtime-source manifest differs from RUN_RESULT during export",
    )
    runtime_covered = sorted(
        {"runtime_source_validation.json"}
        | {f"bin/{name}" for name in RUNTIME_TARGETS}
        | {f"logs/{name}" for name in RUNTIME_LOGS}
    )
    runtime_entries = parse_exact_relative_manifest(
        runtime_manifest_raw, runtime_covered, "runtime-source output"
    )
    for relative, expected in runtime_entries.items():
        target = require_plain_file_tree(
            runtime_root.joinpath(*PurePosixPath(relative).parts),
            f"runtime-source output {relative}",
            runtime_root,
        )
        require(
            sha256_file(target) == expected,
            f"runtime-source output changed before export: {relative}",
        )
    require(
        runtime_entries["runtime_source_validation.json"]
        == result["RUNTIME_SOURCE_REPORT_SHA256"],
        "runtime-source report differs from RUN_RESULT during export",
    )

    plan_root = require_plain_directory_tree(
        run_directory / "regenerated_terminal_plan",
        "regenerated plan directory",
        run_directory,
    )
    plan_bundle_root = require_plain_directory_tree(
        plan_root / "bundle_plans", "regenerated plan bundle directory", plan_root
    )
    require(
        {entry.name for entry in os.scandir(plan_root)}
        == {
            "bundle_plans",
            "terminal_plan_v1.json",
            "plan_artifacts.sha256",
            "plan_receipt.json",
        },
        "regenerated plan root exact-set mismatch during export",
    )
    require(
        {entry.name for entry in os.scandir(plan_bundle_root)}
        == {PurePosixPath(relative).name for relative in PLAN_BUNDLES},
        "regenerated plan bundle exact-set mismatch during export",
    )
    plan_manifest_path = require_plain_file_tree(
        plan_root / "plan_artifacts.sha256",
        "regenerated plan artifact manifest",
        plan_root,
    )
    plan_manifest_raw = plan_manifest_path.read_bytes()
    require(
        sha256_bytes(plan_manifest_raw)
        == result["REGENERATED_PLAN_MANIFEST_SHA256"],
        "regenerated plan manifest differs from RUN_RESULT during export",
    )
    plan_order = ["terminal_plan_v1.json", *sorted(PLAN_BUNDLES)]
    plan_entries = parse_exact_relative_manifest(
        plan_manifest_raw, plan_order, "regenerated plan"
    )
    for relative, expected in plan_entries.items():
        target = require_plain_file_tree(
            plan_root.joinpath(*PurePosixPath(relative).parts),
            f"regenerated plan output {relative}",
            plan_root,
        )
        require(
            sha256_file(target) == expected,
            f"regenerated plan output changed before export: {relative}",
        )
    require(
        plan_entries["terminal_plan_v1.json"]
        == result["REGENERATED_PLAN_SHA256"],
        "regenerated plan differs from RUN_RESULT during export",
    )
    plan_receipt = require_plain_file_tree(
        plan_root / "plan_receipt.json", "regenerated plan receipt", plan_root
    )
    require(
        sha256_file(plan_receipt) == result["REGENERATED_PLAN_RECEIPT_SHA256"],
        "regenerated plan receipt differs from RUN_RESULT during export",
    )

    records: list[dict[str, str]] = []
    for role, (relative, field) in sorted(OMITTED_ARTIFACT_BINDINGS.items()):
        require_safe_relative(relative, f"omitted run artifact {role}")
        target = require_plain_file_tree(
            run_directory.joinpath(*PurePosixPath(relative).parts),
            f"omitted run artifact {role}",
            run_directory,
        )
        actual = sha256_file(target)
        require(
            actual == result[field],
            f"omitted run artifact differs from RUN_RESULT: {role}",
        )
        records.append(
            {
                "role": role,
                "path": relative,
                "result_field": field,
                "sha256": actual,
            }
        )

    # Rehash the two omitted trees after all semantic checks so the export
    # summary describes their final observed bytes, not an earlier snapshot.
    for relative, expected in runtime_entries.items():
        target = require_plain_file_tree(
            runtime_root.joinpath(*PurePosixPath(relative).parts),
            f"final runtime-source output {relative}",
            runtime_root,
        )
        require(
            sha256_file(target) == expected,
            f"runtime-source output changed during export: {relative}",
        )
    for relative, expected in plan_entries.items():
        target = require_plain_file_tree(
            plan_root.joinpath(*PurePosixPath(relative).parts),
            f"final regenerated plan output {relative}",
            plan_root,
        )
        require(
            sha256_file(target) == expected,
            f"regenerated plan output changed during export: {relative}",
        )
    require(
        {entry.name for entry in os.scandir(runtime_root)}
        == {
            "bin",
            "logs",
            "runtime_source_validation.json",
            "runtime_source_validation.sha256",
        }
        and {entry.name for entry in os.scandir(runtime_bin)} == RUNTIME_TARGETS
        and {entry.name for entry in os.scandir(runtime_logs)} == RUNTIME_LOGS,
        "runtime-source output tree changed during export",
    )
    require(
        {entry.name for entry in os.scandir(plan_root)}
        == {
            "bundle_plans",
            "terminal_plan_v1.json",
            "plan_artifacts.sha256",
            "plan_receipt.json",
        }
        and {entry.name for entry in os.scandir(plan_bundle_root)}
        == {PurePosixPath(relative).name for relative in PLAN_BUNDLES},
        "regenerated plan tree changed during export",
    )
    for item in records:
        target = require_plain_file_tree(
            run_directory.joinpath(*PurePosixPath(item["path"]).parts),
            f"final omitted run artifact {item['role']}",
            run_directory,
        )
        require(
            sha256_file(target) == item["sha256"],
            f"omitted run artifact changed during export: {item['role']}",
        )
    require(
        runtime_manifest_path.read_bytes() == runtime_manifest_raw
        and plan_manifest_path.read_bytes() == plan_manifest_raw,
        "an omitted run-artifact manifest changed during export",
    )
    return {
        "schema": "LEECH18_OMITTED_RUN_ARTIFACT_ASSERTIONS_V1",
        "artifacts": records,
        "runtime_source_manifest_entries": len(runtime_entries),
        "regenerated_plan_manifest_entries": len(plan_entries),
    }


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
        "Config3 RELEASE.json contract mismatch during publication export",
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
        "Config3 RUN_RESULT.json contract mismatch during publication export",
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
        "Config3 root-record sidecar mismatch during publication export",
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
        raise ExportError("hybrid proof record has no Config3 release contract") from exc
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


def write_new(path: Path, raw: bytes) -> None:
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o444)
    try:
        with os.fdopen(descriptor, "wb", closefd=False) as stream:
            stream.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
    finally:
        os.close(descriptor)


def remove_owned_temporary_release(path: Path, parent: Path) -> None:
    """Remove only the flat, verifier-created temporary tree; never recurse."""
    path = lexical_absolute(path)
    parent = lexical_absolute(parent)
    require(path.parent == parent, "temporary release escaped its output parent")
    require(path.name.startswith(".verification-release-"), "unexpected temporary release name")
    require_plain_directory_tree(path, "temporary release cleanup directory", parent)
    allowed = RELEASE_FILES | {"RELEASE_MANIFEST.sha256"}
    entries = list(os.scandir(path))
    require(
        all(entry.name in allowed for entry in entries),
        "temporary release contains an unexpected cleanup entry",
    )
    for entry in entries:
        candidate = require_plain_file(Path(entry.path), "temporary release cleanup file")
        candidate.unlink()
    path.rmdir()


def export(
    run_directory: Path, output: Path, extra_redaction_roots: Sequence[Path]
) -> tuple[str, str]:
    require_plain_file_tree(Path(__file__).absolute(), "release exporter")
    run_base = require_plain_directory_tree(RUN_BASE, "run base")
    run_directory = require_plain_directory_tree(
        run_directory, "run directory", run_base
    )
    require(run_directory.parent == run_base, "run directory is not a direct child of .run")
    output = lexical_absolute(output)
    require(
        SAFE_LOG.fullmatch(output.name) is not None
        and output.name not in {".", ".."}
        and not output.name.endswith((".", " "))
        and re.fullmatch(
            r"(?i)(?:con|prn|aux|nul|com[1-9]|lpt[1-9])(?:\..*)?",
            output.name,
        )
        is None,
        f"unsafe release-output directory name: {output.name!r}",
    )
    require(
        not os.path.lexists(output),
        "release output already exists, including as a dangling link/reparse point",
    )
    output_parent = require_plain_directory_tree(
        output.parent, "release-output parent"
    )
    output = output_parent / output.name
    try:
        common = os.path.normcase(os.path.commonpath((str(output), str(HERE))))
    except ValueError:
        common = ""
    require(
        common != os.path.normcase(str(HERE)),
        "release output must be outside the source proof package",
    )
    try:
        output_parent.resolve(strict=True).relative_to(HERE.resolve(strict=True))
    except ValueError:
        pass
    else:
        raise ExportError(
            "release output resolves inside the source proof package"
        )

    result_path = require_plain_file(run_directory / "RUN_RESULT.txt", "run result")
    transcript_path = require_plain_file(
        run_directory / "ORCHESTRATOR_TRANSCRIPT.txt", "outer transcript"
    )
    result_source_raw = result_path.read_bytes()
    result_text = read_text(result_path, "run result")
    result = parse_run_result(result_text)
    source_manifest = require_plain_file_tree(
        SOURCE_MANIFEST, "source package manifest"
    )
    source_manifest_raw = source_manifest.read_bytes()
    source_manifest_sha256 = sha256_bytes(source_manifest_raw)
    require(
        source_manifest_sha256 == result["INITIAL_MANIFEST_SHA256"],
        "current source package manifest is not the manifest used by the run",
    )
    validate_source_package(source_manifest, source_manifest_raw)
    validate_config3_source_bindings(HERE, result)
    transcript_raw = transcript_path.read_bytes()
    require(
        sha256_bytes(transcript_raw) == result["TRANSCRIPT_SHA256"],
        "outer transcript changed after RUN_RESULT was written",
    )
    transcript_text = read_text(transcript_path, "outer transcript")
    sanitized_transcript = sanitize_transcript(
        transcript_text, run_directory, extra_redaction_roots
    ).encode("utf-8")
    released_result = (normalized_text(result_text) + "\n").encode("utf-8")
    require(
        result_source_raw == released_result,
        "source RUN_RESULT is not canonical UTF-8 LF text",
    )
    stage_manifest_path = require_plain_file(
        run_directory / "STAGE_LOGS.sha256", "stage-log manifest"
    )
    stage_manifest_raw = stage_manifest_path.read_bytes()
    require(
        sha256_bytes(stage_manifest_raw) == result["STAGE_LOG_MANIFEST_SHA256"],
        "stage-log manifest changed after RUN_RESULT was written",
    )
    stage_hashes = read_stage_log_manifest(stage_manifest_raw)
    stages = inventory_stage_logs(run_directory / "logs", stage_hashes)
    semantic_stage = next(
        item for item in stages if item["stage"] == "semantic_bridge"
    )
    require(
        semantic_stage["stdout"]["normalized_text_sha256"]
        == result["SEMANTIC_BRIDGE_STDOUT_SHA256"],
        "semantic-bridge stdout digest differs from RUN_RESULT",
    )
    semantic_result_raw, semantic_released_sidecar = validate_semantic_result(
        run_directory, result
    )
    omitted_run_artifacts = validate_omitted_run_artifacts(
        run_directory, result
    )
    final_stages = inventory_stage_logs(run_directory / "logs", stage_hashes)
    require(
        final_stages == stages,
        "raw stage logs changed during release export",
    )
    stages = final_stages
    require(
        stage_manifest_path.read_bytes() == stage_manifest_raw,
        "stage-log manifest changed during release export",
    )
    require(
        result_path.read_bytes() == result_source_raw
        and transcript_path.read_bytes() == transcript_raw,
        "RUN_RESULT or raw transcript changed during release export",
    )
    final_semantic_raw, final_semantic_sidecar = validate_semantic_result(
        run_directory, result
    )
    require(
        final_semantic_raw == semantic_result_raw
        and final_semantic_sidecar == semantic_released_sidecar,
        "semantic bridge result changed during release export",
    )
    summary = {
        "schema": "LEECH18_VERIFICATION_RELEASE_STAGE_DIGESTS_V2",
        "input_manifest_sha256": source_manifest_sha256,
        "run_result_source_sha256": sha256_bytes(result_source_raw),
        "run_result_released_sha256": sha256_bytes(released_result),
        "transcript_source_sha256": sha256_bytes(transcript_raw),
        "transcript_released_sha256": sha256_bytes(sanitized_transcript),
        "terminal_marker": FULL_MARKER,
        "stage_log_manifest_sha256": result["STAGE_LOG_MANIFEST_SHA256"],
        "extra_redaction_tokens": len(extra_redaction_roots),
        "omitted_run_artifacts": omitted_run_artifacts,
        "stages": stages,
    }
    payloads = {
        "INPUT_MANIFEST.sha256": source_manifest_raw,
        "ORCHESTRATOR_TRANSCRIPT.sanitized.txt": sanitized_transcript,
        "RUN_RESULT.txt": released_result,
        "SEMANTIC_BRIDGE_RUN_RESULT.json": semantic_result_raw,
        "SEMANTIC_BRIDGE_RUN_RESULT.sha256": semantic_released_sidecar,
        "STAGE_LOGS.sha256": stage_manifest_raw,
        "STAGE_DIGESTS.json": canonical_json(summary),
    }
    require(set(payloads) == RELEASE_FILES, "internal release file-set mismatch")
    temporary = Path(tempfile.mkdtemp(prefix=".verification-release-", dir=output_parent))
    try:
        for name in sorted(payloads):
            write_new(temporary / name, payloads[name])
        manifest = "".join(
            f"{sha256_bytes(payloads[name])}  {name}\n" for name in sorted(payloads)
        ).encode("ascii")
        write_new(temporary / "RELEASE_MANIFEST.sha256", manifest)
        release_manifest_sha256 = sha256_bytes(manifest)
        os.rename(temporary, output)
        temporary = None
        released_root = require_plain_directory_tree(output, "released output directory")
        observed_release_names = {entry.name for entry in os.scandir(released_root)}
        require(
            observed_release_names == RELEASE_FILES | {"RELEASE_MANIFEST.sha256"},
            "released output exact-set mismatch after publication rename",
        )
        for name, expected_raw in payloads.items():
            released_file = require_plain_file_tree(
                released_root / name, f"released output {name}", released_root
            )
            require(
                sha256_file(released_file) == sha256_bytes(expected_raw),
                f"released output changed during publication: {name}",
            )
        released_manifest = require_plain_file_tree(
            released_root / "RELEASE_MANIFEST.sha256",
            "released output manifest",
            released_root,
        )
        require(
            released_manifest.read_bytes() == manifest
            and sha256_file(released_manifest) == release_manifest_sha256,
            "released output manifest changed during publication",
        )
        require(
            require_plain_file_tree(
                SOURCE_MANIFEST, "final source package manifest"
            ).read_bytes()
            == source_manifest_raw,
            "source package manifest changed during release export",
        )
        validate_source_package(source_manifest, source_manifest_raw)
        final_release_names = {entry.name for entry in os.scandir(released_root)}
        require(
            final_release_names == RELEASE_FILES | {"RELEASE_MANIFEST.sha256"},
            "released output tree changed during final source validation",
        )
        for name, expected_raw in payloads.items():
            released_file = require_plain_file_tree(
                released_root / name, f"final released output {name}", released_root
            )
            require(
                sha256_file(released_file) == sha256_bytes(expected_raw),
                f"released output changed before export marker: {name}",
            )
        require(
            require_plain_file_tree(
                released_root / "RELEASE_MANIFEST.sha256",
                "final released output manifest",
                released_root,
            ).read_bytes()
            == manifest,
            "released output manifest changed before export marker",
        )
    finally:
        if temporary is not None and temporary.exists():
            remove_owned_temporary_release(temporary, output_parent)
    return source_manifest_sha256, release_manifest_sha256


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-dir", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument(
        "--redact-root",
        action="append",
        default=[],
        type=Path,
        help="additional host path or directory to replace with a numbered token",
    )
    args = parser.parse_args(argv)
    try:
        manifest_sha256, release_manifest_sha256 = export(
            args.run_dir, args.output, args.redact_root
        )
        print(
            "LEECH18_VERIFICATION_RELEASE_EXPORTED "
            f"files={len(RELEASE_FILES)} input_manifest_sha256={manifest_sha256} "
            f"release_manifest_sha256={release_manifest_sha256}"
        )
        return 0
    except (ExportError, OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"LEECH18_VERIFICATION_RELEASE_EXPORT_FAIL: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
