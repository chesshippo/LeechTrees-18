#!/usr/bin/env python3
"""Shared strict schema and durability helpers for remaining-G001 leaves."""

from __future__ import annotations

import hashlib
import json
import os
import re
import stat
import tempfile
from pathlib import Path
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple


PLAN_SCHEMA = "G001_REMAINING_LEAF_PLAN_V1"
LAUNCH_SCHEMA = "G001_REMAINING_LEAF_LAUNCH_V1"
TIMING_SCHEMA = "G001_REMAINING_PROCESS_TIMING_V1"
EXIT_SCHEMA = "G001_REMAINING_PROCESS_EXIT_V1"
ZERO_MARKER_SCHEMA = "G001_REMAINING_ZERO_COMPLETE_V1"
FOUND_MARKER_SCHEMA = "G001_REMAINING_VERIFIED_FOUND_V1"
NO_EVIDENCE_SCHEMA = "G001_REMAINING_NO_EVIDENCE_V1"
EVIDENCE_SCHEMA = "G001_REMAINING_LEAF_EVIDENCE_V1"
COLLECTION_SCHEMA = "G001_REMAINING_LEAF_COLLECTION_V1"

NO_EVIDENCE_EXIT = 75
USAGE_EXIT = 64
IO_EXIT = 74
WITNESS_PLACEHOLDER = "{WITNESS_FILE}"

CONFIGURATION_TO_MODE = {
    1: "g001_row0",
    4: "g001_row3",
    5: "g001_row4",
    6: "g001_row5",
    7: "g001_row6",
}

ARTIFACT_ROLES = (
    "solver_source",
    "solver_executable",
    "checker_source",
    "checker_executable",
)

PIPELINE_ARTIFACT_ROLES = (
    "leaf_worker",
    "leaf_common",
    "leaf_collector",
)

VALUE_OPTIONS = {
    "--configuration",
    "--witness-file",
    "--root-branch",
    "--branch-path",
    "--multi-edge-cover-local-max-components",
    "--multi-edge-cover-max-components",
    "--multi-edge-cover-exact-max-components",
    "--multi-edge-cover-budget",
    "--multi-edge-cover-candidate-cap",
}

FLAG_OPTIONS = {
    "--multi-edge-cover",
    "--multi-edge-cover-no-hall",
    "--multi-edge-cover-no-exact",
    "--multi-edge-cover-no-exact-hall",
    "--multi-edge-cover-validate",
}

FORBIDDEN_OPTIONS = {
    "--max-nodes",
    "--stop-edges",
    "--multi-edge-cover-shadow",
    "--help",
    "--mode",
}

SAFE_IDENTIFIER = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_.-]{0,127}$")
SHA256_PATTERN = re.compile(r"^[0-9a-f]{64}$")
ASCII_UINT_PATTERN = re.compile(r"^(?:0|[1-9][0-9]*)$")
RESULT_FIELD = re.compile(r"(?:^|\s)([A-Za-z0-9_]+)=([^\s]+)")
INT_MAX = (1 << 31) - 1
UINT64_MAX = (1 << 64) - 1


class ValidationError(RuntimeError):
    """Raised when a plan or evidence artifact violates the strict schema."""


def canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True, allow_nan=False) + "\n").encode(
                           "utf-8")


def strict_json_loads(text: str, context: str) -> Any:
    def object_from_pairs(pairs: Sequence[Tuple[str, Any]]) -> Dict[str, Any]:
        result: Dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise ValidationError(
                    f"{context} contains duplicate JSON key {key!r}")
            result[key] = value
        return result

    def reject_constant(token: str) -> Any:
        raise ValidationError(
            f"{context} contains nonstandard JSON constant {token}")

    try:
        return json.loads(
            text, object_pairs_hook=object_from_pairs,
            parse_constant=reject_constant)
    except (json.JSONDecodeError, ValueError) as exc:
        raise ValidationError(f"{context} is not valid JSON: {exc}") from exc


def canonical_sha256(value: Any) -> str:
    return hashlib.sha256(canonical_json_bytes(value)).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while True:
            block = stream.read(1024 * 1024)
            if not block:
                break
            digest.update(block)
    return digest.hexdigest()


def utc_now() -> str:
    from datetime import datetime, timezone
    return datetime.now(timezone.utc).isoformat(timespec="microseconds").replace(
        "+00:00", "Z")


def require_exact_keys(value: Mapping[str, Any], expected: Iterable[str],
                       context: str) -> None:
    expected_set = set(expected)
    actual_set = set(value.keys())
    if actual_set != expected_set:
        missing = sorted(expected_set - actual_set)
        extra = sorted(actual_set - expected_set)
        raise ValidationError(
            f"{context} keys differ: missing={missing}, extra={extra}")


def require_identifier(value: Any, context: str) -> str:
    if not isinstance(value, str) or not SAFE_IDENTIFIER.fullmatch(value):
        raise ValidationError(f"{context} is not a safe identifier")
    return value


def require_sha256(value: Any, context: str) -> str:
    if not isinstance(value, str):
        raise ValidationError(f"{context} SHA-256 must be a string")
    lowered = value.lower()
    if not SHA256_PATTERN.fullmatch(lowered):
        raise ValidationError(f"{context} SHA-256 is not 64 hexadecimal digits")
    return lowered


def parse_ascii_uint(text: str, context: str, maximum: int) -> int:
    if not ASCII_UINT_PATTERN.fullmatch(text) or len(text) > 20:
        raise ValidationError(f"{context} is not an ASCII nonnegative integer")
    value = int(text)
    if value > maximum:
        raise ValidationError(f"{context} exceeds {maximum}")
    return value


def require_relative_path(value: Any, context: str) -> str:
    if not isinstance(value, str) or not value or "\x00" in value:
        raise ValidationError(f"{context} path must be a nonempty string")
    path = Path(value)
    if path.is_absolute() or any(part == ".." for part in path.parts):
        raise ValidationError(f"{context} path must stay relative to workspace")
    normalized = path.as_posix()
    if normalized in ("", "."):
        raise ValidationError(f"{context} path must name a file")
    return normalized


def resolve_workspace_file(workspace: Path, relative: str,
                           context: str) -> Path:
    workspace = workspace.resolve(strict=True)
    candidate = (workspace / relative).resolve(strict=True)
    try:
        candidate.relative_to(workspace)
    except ValueError as exc:
        raise ValidationError(f"{context} resolves outside workspace") from exc
    if not candidate.is_file():
        raise ValidationError(f"{context} is not a regular file: {relative}")
    return candidate


def validate_binding(value: Any, context: str,
                     dependency: bool = False) -> Dict[str, str]:
    if not isinstance(value, dict):
        raise ValidationError(f"{context} must be an object")
    keys = ("role", "path", "sha256") if dependency else ("path", "sha256")
    require_exact_keys(value, keys, context)
    result = {
        "path": require_relative_path(value["path"], context),
        "sha256": require_sha256(value["sha256"], context),
    }
    if dependency:
        result["role"] = require_identifier(value["role"], f"{context}.role")
    return result


def validate_pipeline_artifacts(value: Any) -> Dict[str, Dict[str, str]]:
    if not isinstance(value, dict):
        raise ValidationError("pipeline_artifacts must be an object")
    require_exact_keys(value, PIPELINE_ARTIFACT_ROLES,
                       "pipeline_artifacts")
    result = {
        role: validate_binding(value[role], f"pipeline_artifacts.{role}")
        for role in PIPELINE_ARTIFACT_ROLES
    }
    paths = [binding["path"] for binding in result.values()]
    if len(set(paths)) != len(paths):
        raise ValidationError("pipeline artifact paths must be unique")
    return result


def validate_selector(value: Any) -> Dict[str, Any]:
    if not isinstance(value, dict) or "kind" not in value:
        raise ValidationError("selector must be an object with kind")
    kind = value["kind"]
    if kind == "all":
        require_exact_keys(value, ("kind",), "selector")
        return {"kind": "all"}
    if kind == "root":
        require_exact_keys(value, ("kind", "index"), "selector")
        index = value["index"]
        if isinstance(index, bool) or not isinstance(index, int) or \
                not 0 <= index <= INT_MAX:
            raise ValidationError("root selector index must be nonnegative integer")
        return {"kind": "root", "index": index}
    if kind == "path":
        require_exact_keys(value, ("kind", "indices"), "selector")
        indices = value["indices"]
        if not isinstance(indices, list) or not indices or len(indices) > 14:
            raise ValidationError("path selector requires 1..14 indices")
        if any(isinstance(item, bool) or not isinstance(item, int) or
               not 0 <= item <= INT_MAX
               for item in indices):
            raise ValidationError("path selector indices must be nonnegative integers")
        return {"kind": "path", "indices": list(indices)}
    raise ValidationError(f"unsupported selector kind: {kind!r}")


def selector_text(selector: Mapping[str, Any]) -> str:
    if selector["kind"] == "all":
        return "all"
    if selector["kind"] == "root":
        return f"root:{selector['index']}"
    return "path:" + ",".join(str(item) for item in selector["indices"])


def selectors_overlap(left: Mapping[str, Any],
                      right: Mapping[str, Any]) -> bool:
    if left["kind"] == "all" or right["kind"] == "all":
        return True
    if left["kind"] == "root" and right["kind"] == "root":
        return left["index"] == right["index"]
    if left["kind"] == "root" and right["kind"] == "path":
        return left["index"] == right["indices"][0]
    if left["kind"] == "path" and right["kind"] == "root":
        return right["index"] == left["indices"][0]
    a = left["indices"]
    b = right["indices"]
    shorter = min(len(a), len(b))
    return a[:shorter] == b[:shorter]


def parse_solver_options(argv: Sequence[str]) -> Dict[str, List[str]]:
    parsed: Dict[str, List[str]] = {}
    index = 0
    while index < len(argv):
        option = argv[index]
        if option in FORBIDDEN_OPTIONS:
            raise ValidationError(f"forbidden terminal-search option: {option}")
        if option in VALUE_OPTIONS:
            if index + 1 >= len(argv):
                raise ValidationError(f"{option} requires a value")
            value = argv[index + 1]
            parsed.setdefault(option, []).append(value)
            index += 2
            continue
        if option in FLAG_OPTIONS:
            parsed.setdefault(option, []).append("")
            index += 1
            continue
        raise ValidationError(f"unsupported solver argument in plan: {option!r}")
    for option, occurrences in parsed.items():
        if len(occurrences) != 1:
            raise ValidationError(f"duplicate solver option: {option}")
    return parsed


def validate_argv_template(value: Any, configuration: int,
                           selector: Mapping[str, Any]) -> List[str]:
    if not isinstance(value, list) or not value:
        raise ValidationError("argv_template must be a nonempty string array")
    if any(not isinstance(item, str) or not item or "\x00" in item
           for item in value):
        raise ValidationError("argv_template contains an invalid token")
    argv = list(value)
    parsed = parse_solver_options(argv)
    if parsed.get("--configuration") != [str(configuration)]:
        raise ValidationError("argv_template configuration does not match leaf")
    if parsed.get("--witness-file") != [WITNESS_PLACEHOLDER]:
        raise ValidationError(
            "argv_template needs exactly '--witness-file {WITNESS_FILE}'")
    if "--multi-edge-cover" not in parsed:
        raise ValidationError("production leaf must enable --multi-edge-cover")

    root = parsed.get("--root-branch")
    path = parsed.get("--branch-path")
    kind = selector["kind"]
    if kind == "all" and (root is not None or path is not None):
        raise ValidationError("all selector cannot carry a branch option")
    if kind == "root":
        if root != [str(selector["index"])] or path is not None:
            raise ValidationError("root selector and argv_template disagree")
    if kind == "path":
        expected = ",".join(str(item) for item in selector["indices"])
        if path != [expected] or root is not None:
            raise ValidationError("path selector and argv_template disagree")

    for option in (
        "--multi-edge-cover-local-max-components",
        "--multi-edge-cover-max-components",
        "--multi-edge-cover-exact-max-components",
    ):
        if option in parsed:
            text = parsed[option][0]
            if parse_ascii_uint(text, option, 18) < 1:
                raise ValidationError(f"invalid component threshold for {option}")
    max_components = int(parsed.get(
        "--multi-edge-cover-max-components", ["7"])[0])
    exact_max_components = int(parsed.get(
        "--multi-edge-cover-exact-max-components", ["6"])[0])
    if exact_max_components > max_components:
        raise ValidationError(
            "cover thresholds require exact-max-components <= max-components")
    for option in (
        "--multi-edge-cover-budget",
        "--multi-edge-cover-candidate-cap",
    ):
        if option in parsed:
            parse_ascii_uint(parsed[option][0], option, UINT64_MAX)
    return argv


def validate_leaf(value: Any) -> Dict[str, Any]:
    if not isinstance(value, dict):
        raise ValidationError("leaf must be an object")
    require_exact_keys(
        value,
        ("leaf_id", "configuration", "mode", "selector", "argv_template",
         "timeout_seconds", "artifacts"),
        "leaf",
    )
    leaf_id = require_identifier(value["leaf_id"], "leaf_id")
    configuration = value["configuration"]
    if isinstance(configuration, bool) or configuration not in CONFIGURATION_TO_MODE:
        raise ValidationError("configuration must be one of 1,4,5,6,7")
    mode = value["mode"]
    if mode != CONFIGURATION_TO_MODE[configuration]:
        raise ValidationError("mode does not match configuration")
    selector = validate_selector(value["selector"])
    argv_template = validate_argv_template(
        value["argv_template"], configuration, selector)
    timeout = value["timeout_seconds"]
    if isinstance(timeout, bool) or not isinstance(timeout, int) or timeout < 0:
        raise ValidationError("timeout_seconds must be a nonnegative integer")

    artifacts_value = value["artifacts"]
    if not isinstance(artifacts_value, dict):
        raise ValidationError("artifacts must be an object")
    require_exact_keys(artifacts_value, ARTIFACT_ROLES + ("dependencies",),
                       "artifacts")
    artifacts: Dict[str, Any] = {}
    for role in ARTIFACT_ROLES:
        artifacts[role] = validate_binding(artifacts_value[role], role)
    dependencies = artifacts_value["dependencies"]
    if not isinstance(dependencies, list):
        raise ValidationError("dependencies must be an array")
    artifacts["dependencies"] = [
        validate_binding(item, f"dependencies[{index}]", dependency=True)
        for index, item in enumerate(dependencies)
    ]
    dependency_roles = [item["role"] for item in artifacts["dependencies"]]
    if len(set(dependency_roles)) != len(dependency_roles):
        raise ValidationError("dependency roles must be unique within a leaf")
    all_paths = [artifacts[role]["path"] for role in ARTIFACT_ROLES]
    all_paths.extend(item["path"] for item in artifacts["dependencies"])
    if len(set(all_paths)) != len(all_paths):
        raise ValidationError("artifact paths must be unique")

    return {
        "leaf_id": leaf_id,
        "configuration": configuration,
        "mode": mode,
        "selector": selector,
        "argv_template": argv_template,
        "timeout_seconds": timeout,
        "artifacts": artifacts,
    }


def load_plan(path: Path) -> Tuple[Dict[str, Any], str]:
    try:
        raw = path.read_bytes()
    except OSError as exc:
        raise ValidationError(f"cannot read plan: {exc}") from exc
    plan_hash = hashlib.sha256(raw).hexdigest()
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ValidationError(f"plan is not valid UTF-8: {exc}") from exc
    value = strict_json_loads(text, "plan")
    if not isinstance(value, dict):
        raise ValidationError("plan root must be an object")
    require_exact_keys(
        value, ("schema", "plan_id", "pipeline_artifacts", "leaves"),
        "plan")
    if value["schema"] != PLAN_SCHEMA:
        raise ValidationError(f"unsupported plan schema: {value['schema']!r}")
    plan_id = require_identifier(value["plan_id"], "plan_id")
    pipeline_artifacts = validate_pipeline_artifacts(
        value["pipeline_artifacts"])
    if not isinstance(value["leaves"], list) or not value["leaves"]:
        raise ValidationError("plan leaves must be a nonempty array")
    leaves = [validate_leaf(item) for item in value["leaves"]]
    ids = [item["leaf_id"] for item in leaves]
    if len(set(ids)) != len(ids):
        raise ValidationError("plan contains duplicate leaf_id values")
    for index, left in enumerate(leaves):
        for right in leaves[index + 1:]:
            if (left["configuration"] == right["configuration"] and
                    selectors_overlap(left["selector"], right["selector"])):
                raise ValidationError(
                    "plan selectors overlap: " + left["leaf_id"] + " and " +
                    right["leaf_id"])
    return {
        "schema": PLAN_SCHEMA,
        "plan_id": plan_id,
        "pipeline_artifacts": pipeline_artifacts,
        "leaves": leaves,
    }, plan_hash


def verify_pipeline_artifacts(plan: Mapping[str, Any],
                              workspace: Path) -> Dict[str, Dict[str, str]]:
    result: Dict[str, Dict[str, str]] = {}
    for role in PIPELINE_ARTIFACT_ROLES:
        binding = plan["pipeline_artifacts"][role]
        path = resolve_workspace_file(workspace, binding["path"], role)
        actual = sha256_file(path)
        if actual != binding["sha256"]:
            raise ValidationError(
                f"{role} hash mismatch: expected {binding['sha256']}, "
                f"got {actual}")
        result[role] = {
            "path": binding["path"],
            "sha256": actual,
            "absolute_path": str(path),
        }
    return result


def verify_executing_pipeline(
        bindings: Mapping[str, Mapping[str, str]],
        expected_paths: Mapping[str, Path]) -> None:
    for role, expected_path in expected_paths.items():
        if role not in PIPELINE_ARTIFACT_ROLES:
            raise ValidationError(f"unknown executing pipeline role: {role}")
        actual = expected_path.resolve(strict=True)
        bound = Path(bindings[role]["absolute_path"]).resolve(strict=True)
        if actual != bound:
            raise ValidationError(
                f"executing {role} path differs from frozen plan: "
                f"expected {bound}, got {actual}")


def bound_hash_document(
        leaf_bindings: Mapping[str, Any],
        pipeline_bindings: Mapping[str, Mapping[str, str]]) -> Dict[str, Any]:
    return {
        "solver": {
            role: leaf_bindings[role]["sha256"]
            for role in ARTIFACT_ROLES
        },
        "pipeline": {
            role: pipeline_bindings[role]["sha256"]
            for role in PIPELINE_ARTIFACT_ROLES
        },
        "dependencies": [
            {"role": item["role"], "sha256": item["sha256"]}
            for item in leaf_bindings["dependencies"]
        ],
    }


def verify_bound_artifacts(leaf: Mapping[str, Any], workspace: Path) -> Dict[str, Any]:
    result: Dict[str, Any] = {}
    for role in ARTIFACT_ROLES:
        binding = leaf["artifacts"][role]
        path = resolve_workspace_file(workspace, binding["path"], role)
        actual = sha256_file(path)
        if actual != binding["sha256"]:
            raise ValidationError(
                f"{role} hash mismatch: expected {binding['sha256']}, got {actual}")
        if role.endswith("executable") and os.name == "posix":
            mode = path.stat().st_mode
            if not stat.S_ISREG(mode) or not os.access(path, os.X_OK):
                raise ValidationError(f"{role} is not executable")
        result[role] = {
            "path": binding["path"],
            "sha256": actual,
            "absolute_path": str(path),
        }
    dependencies = []
    for binding in leaf["artifacts"]["dependencies"]:
        path = resolve_workspace_file(workspace, binding["path"],
                                      f"dependency {binding['role']}")
        actual = sha256_file(path)
        if actual != binding["sha256"]:
            raise ValidationError(
                f"dependency {binding['role']} hash mismatch: "
                f"expected {binding['sha256']}, got {actual}")
        dependencies.append({
            "role": binding["role"],
            "path": binding["path"],
            "sha256": actual,
            "absolute_path": str(path),
        })
    result["dependencies"] = dependencies
    return result


def resolved_solver_argv(leaf: Mapping[str, Any], bindings: Mapping[str, Any],
                         witness_path: Path) -> List[str]:
    argv = [bindings["solver_executable"]["absolute_path"]]
    argv.extend(str(witness_path) if token == WITNESS_PLACEHOLDER else token
                for token in leaf["argv_template"])
    return argv


def fsync_directory(path: Path) -> None:
    descriptor = os.open(str(path), os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def atomic_write_new(path: Path, data: bytes, mode: int = 0o600) -> None:
    if path.exists() or path.is_symlink():
        raise FileExistsError(f"refusing to overwrite {path}")
    path.parent.mkdir(parents=False, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=path.name + ".tmp.", dir=str(path.parent))
    temporary = Path(temporary_name)
    try:
        os.fchmod(descriptor, mode)
        with os.fdopen(descriptor, "wb", closefd=True) as stream:
            descriptor = -1
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        os.link(temporary, path)
        fsync_directory(path.parent)
    finally:
        if descriptor >= 0:
            os.close(descriptor)
        try:
            temporary.unlink()
            fsync_directory(path.parent)
        except FileNotFoundError:
            pass


def atomic_write_json_new(path: Path, value: Any) -> None:
    atomic_write_new(path, canonical_json_bytes(value))


def load_json(path: Path, expected_schema: Optional[str] = None) -> Dict[str, Any]:
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        raise ValidationError(f"cannot read {path.name}: {exc}") from exc
    value = strict_json_loads(text, path.name)
    if not isinstance(value, dict):
        raise ValidationError(f"{path.name} must contain a JSON object")
    if expected_schema is not None and value.get("schema") != expected_schema:
        raise ValidationError(
            f"{path.name} has unexpected schema {value.get('schema')!r}")
    return value


def parse_result(stdout_text: str, expected_mode: str) -> Dict[str, str]:
    lines = [line for line in stdout_text.splitlines()
             if line.startswith("RESULT ")]
    if len(lines) != 1:
        raise ValidationError("solver stdout must contain exactly one RESULT line")
    fields: Dict[str, str] = {}
    for match in RESULT_FIELD.finditer(lines[0]):
        name = match.group(1)
        if name in fields:
            raise ValidationError(f"duplicate RESULT field: {name}")
        fields[name] = match.group(2)
    required = {
        "mode", "status", "nodes", "states", "generated",
        "solution_topologies", "frontier", "multi_cover",
        "cover_validation_fail",
    }
    missing = sorted(required - set(fields))
    if missing:
        raise ValidationError(f"RESULT line lacks fields: {missing}")
    if fields["mode"] != expected_mode:
        raise ValidationError("RESULT mode does not match leaf mode")
    for field in (
        "nodes", "states", "generated", "solution_topologies", "frontier",
        "cover_validation_fail",
    ):
        if not fields[field].isdigit():
            raise ValidationError(f"RESULT field {field} is not nonnegative integer")
    if int(fields["nodes"]) <= 0 or int(fields["states"]) <= 0 or \
            int(fields["generated"]) <= 0:
        raise ValidationError("production RESULT counters must be positive")
    if fields["multi_cover"] != "on":
        raise ValidationError("production RESULT must report multi_cover=on")
    if int(fields["cover_validation_fail"]) != 0:
        raise ValidationError("cover_validation_fail is nonzero")
    return fields


def verify_file_hashes(directory: Path, files: Mapping[str, str]) -> None:
    for name, expected in files.items():
        if Path(name).name != name:
            raise ValidationError(f"unsafe evidence filename: {name!r}")
        require_sha256(expected, f"evidence file {name}")
        path = directory / name
        if not path.is_file() or path.is_symlink():
            raise ValidationError(f"missing evidence file: {name}")
        actual = sha256_file(path)
        if actual != expected:
            raise ValidationError(
                f"evidence file hash mismatch for {name}: {actual}")
