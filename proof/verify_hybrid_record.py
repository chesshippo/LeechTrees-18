#!/usr/bin/env python3
"""Fail-closed, read-only checks for the hybrid proof record."""

from __future__ import annotations

import hashlib
import json
import os
import re
import stat
import subprocess
import sys
from pathlib import Path, PurePosixPath
from typing import Any


HERE = Path(__file__).absolute().parent
ROOT = HERE.parent
RECORD_PATH = HERE / "HYBRID_PROOF_RECORD.json"
HEX64 = re.compile(r"[0-9a-f]{64}")
HEX40 = re.compile(r"[0-9a-f]{40}")
EXPECTED_NONLAKE_DEPENDENCY_CACHE_FILES = {
    "proofwidgets": {
        "widget/package-lock.json.hash":
            "06e7fd2f2e52da3ffe50016df8da50419425f01c2d92438f46209811af760c89",
    },
}
GIT_EXECUTABLE = os.environ.get("LEECH18_GIT_EXECUTABLE", "git")


class CheckError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CheckError(message)


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def require_file(relative: str) -> Path:
    return require_plain_file(
        extended_windows_path(workspace_path(relative, "proof-record file")),
        f"proof-record file {relative}",
    )


def check_hash(relative: str, expected: str) -> None:
    path = require_file(relative)
    actual = sha256_file(path)
    require(actual == expected, f"SHA-256 mismatch for {relative}: {actual}")
    print(f"CHECK SHA256 OK {relative} {actual}")


def require_unique_exact_line(text: str, marker: str, label: str) -> None:
    require(
        isinstance(marker, str)
        and bool(marker)
        and text.splitlines().count(marker) == 1,
        f"{label} does not contain its marker as one unique exact line",
    )


def reject_duplicate_json_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON object key: {key!r}")
        result[key] = value
    return result


def reject_json_constant(value: str) -> Any:
    raise CheckError(f"non-finite JSON number is forbidden: {value}")


def read_json(path: Path) -> Any:
    try:
        return json.loads(
            path.read_text(encoding="utf-8"),
            object_pairs_hook=reject_duplicate_json_keys,
            parse_constant=reject_json_constant,
        )
    except (OSError, UnicodeError, json.JSONDecodeError, CheckError) as exc:
        raise CheckError(f"cannot read strict JSON {path}: {exc}") from exc


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
    ).encode("ascii")


def read_canonical_json(path: Path, label: str) -> Any:
    raw = require_plain_file(path, label).read_bytes()
    try:
        value = json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=reject_duplicate_json_keys,
            parse_constant=reject_json_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, CheckError) as exc:
        raise CheckError(f"cannot read strict JSON for {label}: {exc}") from exc
    require(canonical_json_bytes(value) == raw, f"{label} is not canonical JSON")
    return value


def git_environment() -> dict[str, str]:
    environment = {
        name: value
        for name, value in os.environ.items()
        if not name.upper().startswith("GIT_")
    }
    environment["GIT_CONFIG_GLOBAL"] = os.devnull
    environment["GIT_CONFIG_NOSYSTEM"] = "1"
    environment["GIT_OPTIONAL_LOCKS"] = "0"
    environment["GIT_TERMINAL_PROMPT"] = "0"
    return environment


def git_output(repository: Path, *args: str) -> str:
    proc = subprocess.run(
        [GIT_EXECUTABLE, "-C", str(repository), *args],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
        env=git_environment(),
    )
    require(proc.returncode == 0, f"git {' '.join(args)} failed: {proc.stderr.strip()}")
    require(not proc.stderr, f"git {' '.join(args)} wrote to stderr: {proc.stderr.strip()}")
    return proc.stdout.strip()


def git_status(repository: Path) -> list[str]:
    output = git_output(
        repository, "status", "--porcelain=v1", "--untracked-files=all"
    )
    return output.splitlines() if output else []


def require_no_git_index_hiding(repository: Path, label: str) -> None:
    """Reject assume-unchanged/skip-worktree index flags before clean checks."""
    output = git_output(repository, "ls-files", "-v")
    lines = output.splitlines() if output else []
    require(lines, f"{label} has no tracked files")
    hidden = [line for line in lines if not line.startswith("H ")]
    require(
        not hidden,
        f"{label} has nonordinary index flags that can hide changes: "
        f"{hidden[:8]!r}",
    )


def require_plain_dependency_worktree(checkout: Path, label: str) -> None:
    """Reject links/hardlinks in dependency inputs while excluding cache metadata."""
    pending = [checkout]
    while pending:
        directory = pending.pop()
        for entry in os.scandir(directory):
            path = Path(entry.path)
            if directory == checkout and entry.name in {".git", ".lake"}:
                # .git identity is checked separately.  .lake is the explicit
                # trusted dependency-build-cache boundary documented by the
                # package and is not treated as source input here.
                continue
            try:
                info = path.lstat()
            except OSError as exc:
                raise CheckError(f"cannot inspect {label} entry {path}: {exc}") from exc
            require(not is_link_like(path), f"{label} contains a link: {path}")
            if stat.S_ISDIR(info.st_mode):
                pending.append(path)
            else:
                require(
                    stat.S_ISREG(info.st_mode) and info.st_nlink == 1,
                    f"{label} contains a non-regular/single-link file: {path}",
                )


def require_safe_relative(relative: str, context: str) -> PurePosixPath:
    require(isinstance(relative, str), f"non-string {context} path: {relative!r}")
    candidate = PurePosixPath(relative)
    require(
        bool(relative)
        and "\\" not in relative
        and "\x00" not in relative
        and all(0x20 <= ord(character) < 0x7F for character in relative)
        and ":" not in relative
        and not candidate.is_absolute()
        and ".." not in candidate.parts
        and "." not in candidate.parts
        and all(
            not part.endswith((".", " "))
            and re.fullmatch(
                r"(?i)(?:con|prn|aux|nul|com[1-9]|lpt[1-9])(?:\..*)?",
                part,
            )
            is None
            for part in candidate.parts
        )
        and candidate.as_posix() == relative,
        f"unsafe {context} path: {relative!r}",
    )
    return candidate


def workspace_path(relative: str, context: str) -> Path:
    candidate = require_safe_relative(relative, context)
    root = ROOT.absolute()
    target = root.joinpath(*candidate.parts).absolute()
    try:
        target.relative_to(root)
    except ValueError as exc:
        raise CheckError(f"{context} escapes the workspace root: {relative!r}") from exc

    current = root
    require_plain_directory(current, "workspace root")
    for part in candidate.parts[:-1]:
        current = current / part
        require_plain_directory(
            extended_windows_path(current), f"{context} ancestor"
        )
    require(
        not is_link_like(extended_windows_path(target)),
        f"{context} leaf is a link/reparse point: {relative!r}",
    )
    try:
        resolved_root = extended_windows_path(root).resolve(strict=True)
        resolved_target = extended_windows_path(target).resolve(strict=True)
        resolved_target.relative_to(resolved_root)
    except (OSError, ValueError) as exc:
        raise CheckError(
            f"{context} is missing or resolves outside the workspace: {relative!r}"
        ) from exc
    return target


def is_link_like(path: Path) -> bool:
    junction_test = getattr(path, "is_junction", None)
    if path.is_symlink() or bool(junction_test is not None and junction_test()):
        return True
    try:
        attributes = getattr(path.lstat(), "st_file_attributes", 0)
    except OSError:
        return False
    return bool(attributes & getattr(stat, "FILE_ATTRIBUTE_REPARSE_POINT", 0))


def extended_windows_path(path: Path) -> Path:
    """Use an extended path for the retained extraction's long file names."""
    absolute = path.absolute()
    text = str(absolute)
    if sys.platform == "win32" and not text.startswith("\\\\?\\"):
        return Path("\\\\?\\" + text)
    return absolute


def require_plain_file(path: Path, context: str) -> Path:
    try:
        info = path.lstat()
    except OSError as exc:
        raise CheckError(f"cannot inspect {context}: {path}: {exc}") from exc
    require(
        stat.S_ISREG(info.st_mode) and info.st_nlink == 1 and not is_link_like(path),
        f"{context} is not a regular single-link file: {path}",
    )
    return path


def require_plain_directory(path: Path, context: str) -> Path:
    try:
        info = path.lstat()
    except OSError as exc:
        raise CheckError(f"cannot inspect {context}: {path}: {exc}") from exc
    require(
        stat.S_ISDIR(info.st_mode) and not is_link_like(path),
        f"{context} is not a plain directory: {path}",
    )
    return path


def require_plain_directory_ancestry(path: Path, context: str) -> Path:
    absolute = path.absolute()
    for directory in reversed((absolute, *absolute.parents)):
        require_plain_directory(directory, f"{context} ancestor")
    try:
        absolute.resolve(strict=True)
    except OSError as exc:
        raise CheckError(f"cannot resolve {context}: {absolute}: {exc}") from exc
    return absolute


def check_lean_identity(record: dict[str, Any]) -> None:
    lean = record["lean"]
    require(
        isinstance(lean, dict)
        and set(lean)
        == {
            "repository",
            "commit",
            "toolchain",
            "mathlib_commit",
            "declarations",
            "critical_files",
        },
        "Lean identity field set mismatch",
    )
    require(
        lean["declarations"]
        == {
            "eight_row_exhaustion":
                "LeechTrees.Foundation.FirstEdgeDossier.firstEdge_eightRowDossier",
            "zero_certificate_boundary": "Leech18EndToEnd.no_order18_leech_of_all_rows",
        },
        "Lean declaration map mismatch",
    )
    expected_critical_files = {
        "lean/LeechTrees/lean-toolchain",
        "lean/LeechTrees/lakefile.toml",
        "lean/LeechTrees/lake-manifest.json",
        "lean/LeechTrees/LeechTrees/Expanded/FirstEdge/FirstEdgeDossier.lean",
        "proof/HybridEndToEndBoundary.lean",
    }
    require(
        set(lean["critical_files"]) == expected_critical_files,
        "Lean critical-file set mismatch",
    )
    repository = workspace_path(lean["repository"], "Lean repository")
    require_plain_directory(repository, "Lean repository")
    require_plain_directory(repository / ".git", "Lean repository .git directory")

    actual_commit = git_output(repository, "rev-parse", "HEAD")
    require(actual_commit == lean["commit"], f"Lean commit mismatch: {actual_commit}")
    actual_top = Path(git_output(repository, "rev-parse", "--show-toplevel")).resolve()
    require(
        os.path.normcase(str(actual_top)) == os.path.normcase(str(repository.resolve())),
        f"Lean Git top level is redirected: {actual_top}",
    )
    print(f"CHECK LEAN COMMIT OK {actual_commit}")
    require_no_git_index_hiding(repository, "Lean repository")

    tracked_diff = subprocess.run(
        [GIT_EXECUTABLE, "-C", str(repository), "diff", "--quiet", "HEAD", "--"],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
        env=git_environment(),
    )
    require(
        tracked_diff.returncode in (0, 1),
        f"cannot inspect tracked Lean repository files: {tracked_diff.stderr.strip()}",
    )
    require(
        tracked_diff.returncode == 0,
        "tracked Lean repository files differ from HEAD",
    )
    require(not tracked_diff.stderr, f"Lean git diff wrote to stderr: {tracked_diff.stderr.strip()}")
    untracked_all = git_output(
        repository, "ls-files", "--others", "--exclude-standard"
    )
    untracked_build_inputs = [
        line
        for line in untracked_all.splitlines()
        if line
        in {
            "LeechTrees.lean",
            "lakefile.lean",
            "lakefile.toml",
            "lake-manifest.json",
            "lean-toolchain",
        }
        or line.startswith("LeechTrees/")
    ]
    require(
        not untracked_build_inputs,
        "untracked baseline build inputs: " + ", ".join(untracked_build_inputs),
    )
    print("CHECK LEAN TRACKED TREE OK")

    toolchain_path = require_file("lean/LeechTrees/lean-toolchain")
    actual_toolchain = toolchain_path.read_text(encoding="utf-8").strip()
    require(
        actual_toolchain == lean["toolchain"],
        f"Lean toolchain mismatch: {actual_toolchain}",
    )
    print(f"CHECK LEAN TOOLCHAIN OK {actual_toolchain}")

    for relative, expected in lean["critical_files"].items():
        check_hash(relative, expected)

    lake_manifest = read_json(repository / "lake-manifest.json")
    packages = lake_manifest.get("packages")
    require(isinstance(packages, list) and packages, "Lake package list is missing")
    lake_root = require_plain_directory(
        repository / ".lake", "Lean repository .lake directory"
    )
    packages_root = require_plain_directory(
        lake_root / "packages", "Lake packages directory"
    )
    expected_names: list[str] = []
    expected_revisions: dict[str, str] = {}
    for package in packages:
        require(isinstance(package, dict), "malformed Lake package record")
        name = package.get("name")
        revision = package.get("rev")
        require(
            package.get("type") == "git"
            and isinstance(name, str)
            and isinstance(revision, str)
            and HEX40.fullmatch(revision) is not None,
            f"unsupported or malformed Lake package record: {package!r}",
        )
        safe_name = require_safe_relative(name, "Lake package name")
        require(
            len(safe_name.parts) == 1 and safe_name.name == name,
            f"Lake package name is not one safe path component: {name!r}",
        )
        require(name not in expected_revisions, f"duplicate Lake package: {name}")
        expected_names.append(name)
        expected_revisions[name] = revision

    package_entries = list(packages_root.iterdir())
    malformed_package_entries = [
        item.name for item in package_entries if is_link_like(item) or not item.is_dir()
    ]
    require(
        not malformed_package_entries,
        "non-directory or linked Lake package entries are forbidden: "
        f"{malformed_package_entries}",
    )
    actual_package_dirs = {item.name for item in package_entries}
    require(
        actual_package_dirs == set(expected_names),
        "installed Lake package set mismatch: "
        f"missing={sorted(set(expected_names) - actual_package_dirs)} "
        f"extra={sorted(actual_package_dirs - set(expected_names))}",
    )
    for name in expected_names:
        checkout = packages_root / name
        require_plain_directory(
            checkout / ".git", f"Lake package {name} .git directory"
        )
        require_plain_dependency_worktree(checkout, f"Lake package {name} worktree")
        actual_revision = git_output(checkout, "rev-parse", "HEAD")
        require(
            actual_revision == expected_revisions[name],
            f"Lake package {name} revision mismatch: {actual_revision}",
        )
        status = git_status(checkout)
        require(not status, f"Lake package {name} is dirty: {status!r}")
        require_no_git_index_hiding(checkout, f"Lake package {name}")
        actual_top = Path(git_output(checkout, "rev-parse", "--show-toplevel")).resolve()
        require(
            os.path.normcase(str(actual_top)) == os.path.normcase(str(checkout.resolve())),
            f"Lake package {name} Git top level is redirected: {actual_top}",
        )
        untracked_outside_lake = git_output(
            checkout, "ls-files", "--others", "--", ":!.lake/**"
        )
        observed_cache_files = (
            untracked_outside_lake.splitlines() if untracked_outside_lake else []
        )
        expected_cache_files = EXPECTED_NONLAKE_DEPENDENCY_CACHE_FILES.get(name, {})
        require(
            set(observed_cache_files) == set(expected_cache_files),
            f"Lake package {name} has unexpected non-.lake cache files: "
            f"{observed_cache_files!r}",
        )
        for relative, expected_hash in expected_cache_files.items():
            candidate = require_safe_relative(relative, f"Lake package {name} cache")
            cache_file = require_plain_file(
                checkout.joinpath(*candidate.parts),
                f"Lake package {name} cache file {relative}",
            )
            require(
                sha256_file(cache_file) == expected_hash,
                f"Lake package {name} cache file digest mismatch: {relative}",
            )
        print(f"CHECK LAKE PACKAGE CLEAN {name} {actual_revision}")

    require(
        expected_revisions.get("mathlib") == lean["mathlib_commit"],
        "proof record mathlib revision differs from the pinned Lake manifest",
    )
    print(f"CHECK MATHLIB COMMIT OK {lean['mathlib_commit']}")

    dossier = require_file(
        "lean/LeechTrees/LeechTrees/Expanded/FirstEdge/FirstEdgeDossier.lean"
    ).read_text(encoding="utf-8")
    artifact_boundary = require_file(
        "proof/HybridEndToEndBoundary.lean"
    ).read_text(encoding="utf-8")
    for declaration in (
        "theorem firstEdge_eightRowDossier",
        "def EightRowDossier",
    ):
        require(declaration in dossier, f"declaration text not found: {declaration}")
    for declaration in (
        "structure RowExclusions",
        "theorem no_order18_leech_of_all_rows",
    ):
        require(
            declaration in artifact_boundary,
            f"declaration text not found: {declaration}",
        )
    print("CHECK LEAN DECLARATION SOURCE NAMES OK count=4")


def check_configuration_map(record: dict[str, Any]) -> None:
    expected = [
        (1, "AdjacentNoneRow", 0, 5),
        (2, "AdjacentMeetsOneRow", 1, 6),
        (3, "AdjacentMeetsTwoRow", 2, 5),
        (4, "AdjacentMeetsBothRow", 3, 7),
        (5, "DisjointNoneRow", 4, 4),
        (6, "DisjointMeetsOneRow", 5, 5),
        (7, "DisjointMeetsTwoRow", 6, 4),
        (8, "DisjointMeetsBothRow", 7, 7),
    ]
    correspondence = record["configuration_correspondence"]
    require(
        isinstance(correspondence, list)
        and all(
            isinstance(item, dict)
            and set(item)
            == {
                "paper_configuration",
                "lean_row",
                "solver_row",
                "next_weight",
            }
            for item in correspondence
        ),
        "configuration correspondence field mismatch",
    )
    actual = [
        (
            item["paper_configuration"],
            item["lean_row"],
            item["solver_row"],
            item["next_weight"],
        )
        for item in correspondence
    ]
    require(actual == expected, f"configuration correspondence mismatch: {actual!r}")
    print("CHECK CONFIGURATION CORRESPONDENCE OK paper=1..8 solver=0..7")


def check_semantic_bridge_contract(record: dict[str, Any]) -> None:
    spec = record["evidence"]["semantic_bridge"]
    expected_directory = "proof/semantic_bridge"
    expected_files = {
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
    require(
        isinstance(spec, dict)
        and set(spec)
        == {
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
        and spec["directory"] == expected_directory
        and spec["record_path"]
        == expected_directory + "/SEMANTIC_BRIDGE_RECORD.json"
        and spec["wrapper_path"]
        == expected_directory + "/verify_semantic_bridge.ps1"
        and spec["source_files"] == len(expected_files) == 12
        and spec["rows"] == 8
        and spec["direct_rows"] == 7
        and spec["projected_rows"] == 1
        and spec["uses_fresh_baseline_lean_lib"] is True
        and spec["expected_marker"]
        == "LEECH18_SEMANTIC_BRIDGE_REPLAY_OK rows=8 direct=7 projected=1"
        and spec["run_result_schema"]
        == "leech18-semantic-bridge-run-result-v1",
        "semantic bridge contract is malformed",
    )
    bridge = workspace_path(expected_directory, "semantic bridge directory")
    require_plain_directory(bridge, "semantic bridge directory")
    observed: set[str] = set()
    pending = [bridge]
    while pending:
        directory = pending.pop()
        for entry in os.scandir(directory):
            path = Path(entry.path)
            if entry.name.lower() == ".run":
                require_plain_directory(path, "excluded semantic bridge .run directory")
                continue
            try:
                info = path.lstat()
            except OSError as exc:
                raise CheckError(
                    f"cannot inspect semantic bridge entry {path}: {exc}"
                ) from exc
            require(not is_link_like(path), f"semantic bridge contains a link: {path}")
            if stat.S_ISDIR(info.st_mode):
                pending.append(path)
            elif stat.S_ISREG(info.st_mode):
                require(
                    info.st_nlink == 1,
                    f"semantic bridge contains a hard-linked file: {path}",
                )
                observed.add(path.relative_to(bridge).as_posix())
            else:
                raise CheckError(f"semantic bridge contains a special file: {path}")
    require(
        observed == expected_files,
        "semantic bridge source exact-set mismatch: "
        f"missing={sorted(expected_files - observed)} "
        f"extra={sorted(observed - expected_files)}",
    )
    require(
        spec["status"] == "PASS",
        "semantic bridge has not completed its required fresh-baseline Lean replay",
    )
    require(
        isinstance(spec["record_sha256"], str)
        and HEX64.fullmatch(spec["record_sha256"]) is not None
        and isinstance(spec["wrapper_sha256"], str)
        and HEX64.fullmatch(spec["wrapper_sha256"]) is not None
        and isinstance(spec["run_result_sha256"], str)
        and HEX64.fullmatch(spec["run_result_sha256"]) is not None
        and isinstance(spec["run_result_sidecar_sha256"], str)
        and HEX64.fullmatch(spec["run_result_sidecar_sha256"]) is not None,
        "semantic bridge has an absent or malformed source digest",
    )
    check_hash(spec["record_path"], spec["record_sha256"])
    check_hash(spec["wrapper_path"], spec["wrapper_sha256"])
    bridge_record = read_json(require_file(spec["record_path"]))
    rows = bridge_record.get("rows")
    require(
        bridge_record.get("schema") == "leech18-semantic-bridge-v1"
        and isinstance(rows, list)
        and len(rows) == 8
        and [item.get("paper_configuration") for item in rows] == list(range(1, 9))
        and [item.get("solver_row") for item in rows] == list(range(8)),
        "semantic bridge record row contract mismatch",
    )
    print("CHECK SEMANTIC BRIDGE CONTRACT PINNED rows=8 direct=7 projected=1")


def parse_source_checksums(raw: bytes) -> dict[str, str]:
    try:
        text = raw.decode("ascii", errors="strict")
    except UnicodeError as exc:
        raise CheckError("source checksum manifest is not ASCII") from exc
    result: dict[str, str] = {}
    for line in text.splitlines():
        parts = line.split("  ")
        require(len(parts) == 2, "malformed source checksum line")
        digest, relative = parts
        require(
            HEX64.fullmatch(digest) is not None,
            f"malformed source checksum digest: {digest!r}",
        )
        require_safe_relative(relative, "source checksum")
        require(relative not in result, f"duplicate source checksum path: {relative}")
        result[relative] = digest
    return result


def check_frozen_source_directory(
    source_dir: Path,
    freeze_name: str,
    freeze_sha256: str,
    checksum_name: str,
    checksum_sha256: str,
    expected_distribution: dict[str, str],
    label: str,
) -> None:
    source_dir = extended_windows_path(source_dir)
    require_plain_directory(source_dir, f"{label} source directory")
    freeze_path = require_plain_file(source_dir / freeze_name, f"{label} source freeze")
    checksum_path = require_plain_file(
        source_dir / checksum_name, f"{label} source checksum manifest"
    )
    require(
        sha256_file(freeze_path) == freeze_sha256,
        f"{label} source-freeze digest mismatch",
    )
    require(
        sha256_file(checksum_path) == checksum_sha256,
        f"{label} source-checksum digest mismatch",
    )
    checksum_map = parse_source_checksums(checksum_path.read_bytes())
    require(
        checksum_map.get(freeze_name) == freeze_sha256,
        f"{label} checksum manifest does not pin the source freeze",
    )
    checksum_distribution = dict(checksum_map)
    checksum_distribution.pop(freeze_name, None)
    require(
        checksum_distribution == expected_distribution,
        f"{label} source freeze and checksum maps differ",
    )

    expected_set = set(checksum_map) | {checksum_name}
    observed_set: set[str] = set()
    pending = [source_dir]
    while pending:
        directory = pending.pop()
        for entry in os.scandir(directory):
            item = Path(entry.path)
            try:
                info = item.lstat()
            except OSError as exc:
                raise CheckError(
                    f"cannot inspect {label} source entry {item}: {exc}"
                ) from exc
            require(
                not is_link_like(item), f"{label} source contains a link: {item}"
            )
            if stat.S_ISDIR(info.st_mode):
                pending.append(item)
                continue
            require(
                stat.S_ISREG(info.st_mode) and info.st_nlink == 1,
                f"{label} source contains a non-regular/single-link entry: {item}",
            )
            observed_set.add(item.relative_to(source_dir).as_posix())
    require(
        observed_set == expected_set,
        f"{label} source exact-set mismatch: "
        f"missing={sorted(expected_set - observed_set)} "
        f"extra={sorted(observed_set - expected_set)}",
    )
    for relative, expected in checksum_map.items():
        candidate = require_safe_relative(relative, f"{label} source")
        target = require_plain_file(
            source_dir.joinpath(*candidate.parts), f"{label} source file {relative}"
        )
        require(
            sha256_file(target) == expected,
            f"{label} source SHA-256 mismatch: {relative}",
        )
    print(f"CHECK FROZEN SOURCE EXACT {label} files={len(expected_distribution)}")


def check_prior_three_evidence(record: dict[str, Any]) -> None:
    spec = record["evidence"]["prior_three_evidence"]
    root = workspace_path(spec["root"], "prior-three evidence root")
    require_plain_directory(root, "prior-three evidence root")
    manifest_name = spec["manifest"]
    require_safe_relative(manifest_name, "prior-three manifest")
    manifest_path = require_plain_file(root / manifest_name, "prior-three manifest")
    actual_manifest_hash = sha256_file(manifest_path)
    require(
        actual_manifest_hash == spec["manifest_sha256"],
        f"prior-three manifest digest mismatch: {actual_manifest_hash}",
    )

    expected: dict[str, str] = {}
    try:
        lines = manifest_path.read_text(encoding="utf-8-sig").splitlines()
    except (OSError, UnicodeError) as exc:
        raise CheckError(f"cannot read prior-three manifest: {exc}") from exc
    for line_number, line in enumerate(lines, start=1):
        if not line.strip():
            continue
        match = re.fullmatch(r"([0-9a-f]{64})  (.+)", line)
        require(match is not None, f"malformed prior-three manifest line {line_number}")
        digest, relative = match.groups()
        require_safe_relative(relative, "prior-three manifest")
        require(
            relative != manifest_name and relative not in expected,
            f"duplicate/self-referential prior-three manifest path: {relative}",
        )
        expected[relative] = digest.lower()

    observed: dict[str, Path] = {}
    total_bytes = 0
    pending = [root]
    while pending:
        directory = pending.pop()
        for entry in os.scandir(directory):
            item = Path(entry.path)
            try:
                info = item.lstat()
            except OSError as exc:
                raise CheckError(
                    f"cannot inspect prior-three evidence entry {item}: {exc}"
                ) from exc
            require(
                not is_link_like(item),
                f"prior-three evidence contains a link: {item}",
            )
            if stat.S_ISDIR(info.st_mode):
                pending.append(item)
                continue
            require(
                stat.S_ISREG(info.st_mode) and info.st_nlink == 1,
                f"prior-three evidence contains a non-regular/single-link entry: {item}",
            )
            relative = item.relative_to(root).as_posix()
            if relative == manifest_name:
                continue
            require(
                relative not in observed,
                f"prior-three evidence contains an aliased path: {relative}",
            )
            observed[relative] = item
            total_bytes += info.st_size
    require(
        set(observed) == set(expected),
        "prior-three evidence exact-set mismatch: "
        f"missing={sorted(set(expected) - set(observed))} "
        f"extra={sorted(set(observed) - set(expected))}",
    )
    for relative, expected_digest in expected.items():
        actual = sha256_file(observed[relative])
        require(
            actual == expected_digest,
            f"prior-three SHA-256 mismatch: {relative}",
        )
    require(len(expected) == spec["files"], "prior-three evidence file-count mismatch")
    require(total_bytes == spec["bytes"], "prior-three evidence byte-count mismatch")
    print(
        "CHECK PRIOR-THREE EVIDENCE INDEPENDENT "
        f"files={len(expected)} bytes={total_bytes} sha256={actual_manifest_hash}"
    )


def check_exact_release_manifest(
    root: Path, manifest_path: Path, label: str
) -> dict[str, str]:
    raw = require_plain_file(manifest_path, f"{label} manifest").read_bytes()
    try:
        text = raw.decode("ascii")
    except UnicodeDecodeError as exc:
        raise CheckError(f"{label} manifest is not ASCII") from exc
    require(
        text.endswith("\n") and "\r" not in text,
        f"{label} manifest is not canonical LF text",
    )
    lines = text[:-1].split("\n")
    require(bool(lines) and all(lines), f"{label} manifest is empty or has blank lines")
    expected: dict[str, str] = {}
    normalized_paths: set[str] = set()
    order: list[str] = []
    for line in lines:
        match = re.fullmatch(r"([0-9a-f]{64})  (.+)", line)
        require(match is not None, f"malformed {label} manifest line: {line!r}")
        digest, relative = match.groups()
        candidate = require_safe_relative(relative, f"{label} manifest")
        require(
            ".run" not in {part.lower() for part in candidate.parts}
            and relative.casefold() != manifest_path.name.casefold(),
            f"unsafe/self-referential {label} manifest path: {relative}",
        )
        normalized = os.path.normcase(relative.replace("/", os.sep))
        require(
            relative not in expected and normalized not in normalized_paths,
            f"duplicate {label} manifest path: {relative}",
        )
        expected[relative] = digest
        normalized_paths.add(normalized)
        order.append(relative)
    require(order == sorted(order), f"{label} manifest is not sorted by path")

    observed_files: dict[str, Path] = {}
    observed_directories: set[str] = set()
    pending = [root]
    while pending:
        directory = pending.pop()
        require_plain_directory(directory, f"{label} directory")
        for entry in os.scandir(directory):
            path = Path(entry.path)
            try:
                info = path.lstat()
            except OSError as exc:
                raise CheckError(f"cannot inspect {label} entry {path}: {exc}") from exc
            require(not is_link_like(path), f"{label} contains a link: {path}")
            relative = path.relative_to(root).as_posix()
            if stat.S_ISDIR(info.st_mode):
                observed_directories.add(relative)
                pending.append(path)
            elif stat.S_ISREG(info.st_mode):
                require(info.st_nlink == 1, f"{label} contains a hard link: {path}")
                if os.path.normcase(str(path)) != os.path.normcase(str(manifest_path)):
                    observed_files[relative] = path
            else:
                raise CheckError(f"{label} contains a special file: {path}")
    require(
        set(observed_files) == set(expected),
        f"{label} manifest/file exact-set mismatch: "
        f"missing={sorted(set(expected) - set(observed_files))} "
        f"extra={sorted(set(observed_files) - set(expected))}",
    )
    expected_directories: set[str] = set()
    for relative in expected:
        parts = PurePosixPath(relative).parts[:-1]
        for length in range(1, len(parts) + 1):
            expected_directories.add(PurePosixPath(*parts[:length]).as_posix())
    require(
        observed_directories == expected_directories,
        f"{label} directory exact-set mismatch: "
        f"missing={sorted(expected_directories - observed_directories)} "
        f"extra={sorted(observed_directories - expected_directories)}",
    )
    for relative, expected_digest in expected.items():
        actual = sha256_file(observed_files[relative])
        require(
            actual == expected_digest,
            f"{label} manifest SHA-256 mismatch: {relative}: {actual}",
        )
    final_files: dict[str, Path] = {}
    final_directories: set[str] = set()
    pending = [root]
    while pending:
        directory = pending.pop()
        require_plain_directory(directory, f"final {label} directory")
        for entry in os.scandir(directory):
            path = Path(entry.path)
            try:
                info = path.lstat()
            except OSError as exc:
                raise CheckError(
                    f"cannot finally inspect {label} entry {path}: {exc}"
                ) from exc
            require(not is_link_like(path), f"{label} gained a link: {path}")
            relative = path.relative_to(root).as_posix()
            if stat.S_ISDIR(info.st_mode):
                final_directories.add(relative)
                pending.append(path)
            elif stat.S_ISREG(info.st_mode):
                require(info.st_nlink == 1, f"{label} gained a hard link: {path}")
                if os.path.normcase(str(path)) != os.path.normcase(str(manifest_path)):
                    final_files[relative] = path
            else:
                raise CheckError(f"{label} gained a special file: {path}")
    require(
        set(final_files) == set(expected)
        and final_directories == expected_directories,
        f"{label} tree changed during validation",
    )
    for relative, expected_digest in expected.items():
        actual = sha256_file(final_files[relative])
        require(
            actual == expected_digest,
            f"{label} file changed during validation: {relative}: {actual}",
        )
    require(
        require_plain_file(manifest_path, f"final {label} manifest").read_bytes()
        == raw,
        f"{label} manifest changed during validation",
    )
    return expected


def expected_config3_keys() -> list[str]:
    keys = ["a2_attached|root_0"]
    keys.extend(f"a2_attached|path_1_{index}" for index in range(6))
    keys.extend(f"a2_separate|root_{index}" for index in range(4))
    keys.extend(f"a2_separate|path_4_{index}" for index in range(6))
    keys.extend(f"a2_separate|path_5_{index}" for index in range(5))
    keys.extend(f"a2_separate|path_6_{index}" for index in range(2))
    keys.extend(f"a2_separate|path_7_{index}" for index in range(8))
    keys.extend(f"a2_separate|path_8_{index}" for index in range(15))
    require(len(keys) == len(set(keys)) == 47, "internal Config3 roster is invalid")
    return keys


CONFIG3_SPLIT_CHILD_NODES = [
    613263,
    151044,
    113834,
    208504,
    129957,
    690996,
    327187,
    285624,
    303586,
    93109,
    47875,
    2747480,
    2802625,
    4374904,
    1794084,
    257576,
    351480,
    404615,
    4460848,
    4409631,
    4156885,
    14123865,
]


def require_release_file_reference(
    root: Path,
    reference: Any,
    expected_path: str,
    manifest: dict[str, str],
    label: str,
) -> tuple[int, str]:
    require(
        isinstance(reference, dict)
        and set(reference) == {"bytes", "path", "sha256"}
        and type(reference["bytes"]) is int
        and reference["bytes"] >= 0
        and reference["path"] == expected_path
        and isinstance(reference["sha256"], str)
        and HEX64.fullmatch(reference["sha256"]) is not None,
        f"malformed {label} file reference",
    )
    candidate = require_safe_relative(expected_path, label)
    path = require_plain_file(
        root.joinpath(*candidate.parts), f"{label} file {expected_path}"
    )
    actual_digest = sha256_file(path)
    require(
        path.stat().st_size == reference["bytes"]
        and actual_digest == reference["sha256"]
        and manifest.get(expected_path) == actual_digest,
        f"{label} reference differs from its released byte: {expected_path}",
    )
    return reference["bytes"], actual_digest


def require_receipt_reference(
    root: Path,
    reference: Any,
    expected_path: str,
    manifest: dict[str, str],
    label: str,
) -> None:
    _, digest = require_release_file_reference(
        root, reference, expected_path, manifest, label
    )
    sidecar_relative = expected_path + ".sha256"
    sidecar = require_safe_relative(sidecar_relative, f"{label} sidecar")
    raw = require_plain_file(
        root.joinpath(*sidecar.parts), f"{label} sidecar"
    ).read_bytes()
    require(
        raw == f"{digest}  RECEIPT.json\n".encode("ascii")
        and manifest.get(sidecar_relative) == hashlib.sha256(raw).hexdigest(),
        f"{label} sidecar is not exact",
    )


def require_workspace_binding(binding: Any, label: str) -> tuple[str, str]:
    require(
        isinstance(binding, dict)
        and set(binding) == {"bytes", "relative_path", "sha256"}
        and type(binding["bytes"]) is int
        and binding["bytes"] >= 0
        and isinstance(binding["relative_path"], str)
        and isinstance(binding["sha256"], str)
        and HEX64.fullmatch(binding["sha256"]) is not None,
        f"malformed {label} workspace binding",
    )
    path = require_file(binding["relative_path"])
    require(
        path.stat().st_size == binding["bytes"]
        and sha256_file(path) == binding["sha256"],
        f"{label} workspace binding does not match its current byte",
    )
    return binding["relative_path"], binding["sha256"]


def check_configuration3_fresh_result(record: dict[str, Any]) -> None:
    spec = record["evidence"]["configuration3_fresh_result"]
    require(
        not (
            isinstance(spec, dict)
            and spec.get("schema") == "config3-a2-frozen-release-v1"
        ),
        "obsolete direct-47 Configuration 3 release schema is rejected; "
        "the split-release schema is required",
    )
    expected_release_directory = (
        "proof/config3_repair/evidence/full_preserved_v1"
    )
    expected_release = expected_release_directory + "/RELEASE.json"
    expected_sidecar = expected_release + ".sha256"
    expected_run_result = expected_release_directory + "/RUN_RESULT.json"
    expected_run_sidecar = expected_run_result + ".sha256"
    expected_manifest = expected_release_directory + "/MANIFEST.sha256"
    expected_exporter = (
        "proof/config3_repair/freeze_config3_a2_evidence.py"
    )
    expected_verifier = (
        "proof/config3_repair/verify_config3_a2_frozen.py"
    )
    expected_split_harness = (
        "proof/config3_repair/run_config3_a2_path8_14_split.py"
    )
    require(
        isinstance(spec, dict)
        and set(spec)
        == {
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
        and spec["schema"] == "config3-a2-frozen-split-release-v1"
        and spec["release_directory"] == expected_release_directory
        and spec["engine"] == "preserved"
        and spec["logical_partitions"] == 47
        and spec["direct_partitions"] == 46
        and spec["split_children"] == 22
        and spec["logical_nodes"] == 167742832
        and spec["release_record_path"] == expected_release
        and spec["release_sidecar_path"] == expected_sidecar
        and spec["run_result_path"] == expected_run_result
        and spec["run_result_sidecar_path"] == expected_run_sidecar
        and spec["manifest_path"] == expected_manifest
        and spec["exporter_path"] == expected_exporter
        and spec["verifier_path"] == expected_verifier
        and spec["split_harness_path"] == expected_split_harness,
        "fresh Configuration 3 release contract is malformed",
    )
    require(
        spec["status"] == "PASS",
        "fresh Configuration 3 release is not complete and pinned",
    )
    digest_fields = {
        "release_record_sha256",
        "release_sidecar_sha256",
        "run_result_sha256",
        "run_result_sidecar_sha256",
        "manifest_sha256",
        "exporter_sha256",
        "verifier_sha256",
        "split_harness_sha256",
        "normalized_stdout_sha256",
    }
    require(
        all(
            isinstance(spec[name], str) and HEX64.fullmatch(spec[name]) is not None
            for name in digest_fields
        ),
        "fresh Configuration 3 release has an absent or malformed digest",
    )
    release_directory = workspace_path(
        spec["release_directory"], "fresh Config3 release"
    )
    require(
        release_directory.is_dir() and not is_link_like(release_directory),
        f"fresh Config3 release directory is missing or linked: {release_directory}",
    )
    check_hash(spec["release_record_path"], spec["release_record_sha256"])
    check_hash(spec["release_sidecar_path"], spec["release_sidecar_sha256"])
    check_hash(spec["run_result_path"], spec["run_result_sha256"])
    check_hash(spec["run_result_sidecar_path"], spec["run_result_sidecar_sha256"])
    check_hash(spec["manifest_path"], spec["manifest_sha256"])
    check_hash(spec["exporter_path"], spec["exporter_sha256"])
    check_hash(spec["verifier_path"], spec["verifier_sha256"])
    check_hash(spec["split_harness_path"], spec["split_harness_sha256"])
    manifest = check_exact_release_manifest(
        release_directory,
        workspace_path(spec["manifest_path"], "fresh Config3 release manifest"),
        "fresh Config3 release",
    )
    roster = expected_config3_keys()
    direct_roster = roster[:-1]
    target_key = roster[-1]
    receipt_files = {
        "RECEIPT.json",
        "RECEIPT.json.sha256",
        "stdout.txt",
        "stderr.txt",
    }
    expected_files = {
        "RELEASE.json",
        "RELEASE.json.sha256",
        "RUN_RESULT.json",
        "RUN_RESULT.json.sha256",
    }
    for key in direct_roster:
        directory = "direct/" + key.replace("|", "__")
        expected_files.update(f"{directory}/{name}" for name in receipt_files)
    expected_files.update(f"split/frontier/{name}" for name in receipt_files)
    for index in range(22):
        expected_files.update(
            f"split/children/k_{index:03d}/{name}" for name in receipt_files
        )
    require(
        set(manifest) == expected_files and len(manifest) == 280,
        "fresh Config3 split release manifest does not cover the exact 280-file roster",
    )
    sidecar = require_file(spec["release_sidecar_path"]).read_bytes()
    require(
        sidecar
        == (
            f"{spec['release_record_sha256']}  RELEASE.json\n"
        ).encode("ascii"),
        "fresh Config3 release sidecar content mismatch",
    )
    run_sidecar = require_file(spec["run_result_sidecar_path"]).read_bytes()
    require(
        run_sidecar
        == f"{spec['run_result_sha256']}  RUN_RESULT.json\n".encode("ascii"),
        "fresh Config3 run-result sidecar content mismatch",
    )
    release_path = require_file(spec["release_record_path"])
    run_result_path = require_file(spec["run_result_path"])
    manifest_path = require_file(spec["manifest_path"])
    require(
        release_path.stat().st_size == 5621
        and run_result_path.stat().st_size == 16210
        and manifest_path.stat().st_size == 29567,
        "fresh Config3 root-record byte counts differ from the frozen contract",
    )
    release = read_canonical_json(release_path, "fresh Config3 RELEASE.json")
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
        and release["schema"] == spec["schema"]
        and release["status"] == "PASS"
        and release["scope"]
        == "fresh Config3/A2 evidence: 46 direct logical partitions plus a split "
        "replacement for a2_separate|path_8_14"
        and release["evidence_origin"]
        == "freshly generated for this proof; not the missing original raw archive"
        and release["logical_roster"] == roster
        and release["common_flags"]
        == [
            "--multi-edge-cover",
            "--multi-edge-cover-no-hall",
            "--multi-edge-cover-budget",
            "100",
            "--multi-edge-cover-no-exact-hall",
        ],
        "fresh Configuration 3 RELEASE.json header mismatch",
    )
    expected_counts = {
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
    require(release["counts"] == expected_counts, "fresh Config3 count contract mismatch")

    engine = release["engine"]
    require(
        isinstance(engine, dict)
        and set(engine) == {"executable", "kind", "name", "source_claim"}
        and engine["kind"] == "hash-pinned-historical-production-binary"
        and engine["name"] == "preserved"
        and engine["source_claim"]
        == "historical package binding; not a reproducible-build proof",
        "fresh Config3 engine header mismatch",
    )
    engine_path, engine_digest = require_workspace_binding(
        engine["executable"], "fresh Config3 preserved engine"
    )
    require(
        engine_path
        == "computation/evidence/production/"
        "prior_three_configurations/work/a2_solver/a2_topology_free_search_multicover.exe",
        "fresh Config3 engine path mismatch",
    )

    source_inputs = release["source_inputs"]
    require(
        isinstance(source_inputs, dict)
        and set(source_inputs)
        == {
            "source",
            "exact_cover_header",
            "optimized_header",
            "stronger_header",
            "expected_ledger",
        },
        "fresh Config3 source-input role set mismatch",
    )
    source_bindings = {
        role: require_workspace_binding(value, f"fresh Config3 source input {role}")
        for role, value in source_inputs.items()
    }
    source_base = (
        "computation/evidence/production/"
        "prior_three_configurations/"
    )
    require(
        {role: binding[0] for role, binding in source_bindings.items()}
        == {
            "source": source_base + "work/a2_solver/a2_topology_free_search.cpp",
            "exact_cover_header": source_base
            + "work/a2_solver/a2_multi_edge_exact_cover.hpp",
            "optimized_header": source_base
            + "work/a2_solver/a2_multi_edge_exact_cover_optimized.hpp",
            "stronger_header": source_base
            + "work/a2_solver/a2_multi_edge_stronger_relaxation.hpp",
            "expected_ledger": source_base
            + "outputs/A2_MULTI_EDGE_PARTITION_RESULTS.csv",
        },
        "fresh Config3 source-input path map mismatch",
    )
    tooling = release["tooling"]
    require(
        isinstance(tooling, dict)
        and set(tooling)
        == {
            "base_harness",
            "engine_runner",
            "exporter",
            "independent_verifier",
            "split_harness",
        },
        "fresh Config3 tooling role set mismatch",
    )
    tooling_bindings = {
        role: require_workspace_binding(value, f"fresh Config3 tool {role}")
        for role, value in tooling.items()
    }
    require(
        {role: binding[0] for role, binding in tooling_bindings.items()}
        == {
            "base_harness": "proof/config3_repair/rerun_config3_a2.py",
            "engine_runner": "proof/config3_repair/run_config3_a2_engines.py",
            "exporter": expected_exporter,
            "independent_verifier": expected_verifier,
            "split_harness": expected_split_harness,
        },
        "fresh Config3 tooling path map mismatch",
    )
    require(
        tooling_bindings["exporter"]
        == (spec["exporter_path"], spec["exporter_sha256"])
        and tooling_bindings["independent_verifier"]
        == (spec["verifier_path"], spec["verifier_sha256"])
        and tooling_bindings["split_harness"]
        == (spec["split_harness_path"], spec["split_harness_sha256"]),
        "fresh Config3 record/tooling cross-binding mismatch",
    )
    for label in (
        "parent_plan_provenance",
        "split_plan_provenance",
        "transient_replacement_provenance",
    ):
        provenance = release[label]
        require(
            isinstance(provenance, dict)
            and set(provenance) == {"bytes", "sha256"}
            and type(provenance["bytes"]) is int
            and provenance["bytes"] > 0
            and isinstance(provenance["sha256"], str)
            and HEX64.fullmatch(provenance["sha256"]) is not None,
            f"malformed fresh Config3 {label}",
        )

    split_proof = release["split_proof"]
    require(
        isinstance(split_proof, dict)
        and set(split_proof)
        == {
            "target_key",
            "child_count",
            "child_indices",
            "repeated_prefix_calls_per_child",
            "node_identity",
            "fanout",
            "source_semantics",
        }
        and split_proof["target_key"] == target_key
        and split_proof["child_count"] == 22
        and split_proof["child_indices"] == list(range(22))
        and split_proof["repeated_prefix_calls_per_child"] == 3
        and split_proof["node_identity"]
        == "parent_nodes=sum(child_nodes)-3*(M-1)"
        and split_proof["fanout"]
        == {
            "census_child_max": "4:9,5:15,6:22,",
            "census_depth": "4:1,5:1,6:1,7:22,",
            "census_frontier": 22,
            "census_nodes": 25,
            "exact_child_roster": "0..21",
        }
        and split_proof["source_semantics"]
        == {
            "branch_path_parser_lines": "693-700",
            "candidate_static_upper_bound": "C(18,2)=153",
            "child_max_before_selector_filter_lines": "553-557",
            "contiguous_branch_counter_lines": "540-552",
            "deterministic_candidate_sort_lines": "536-538",
            "nodes_first_in_rec_lines": "411-414",
            "ordinary_separate_branch_path_base_depth_lines": "881-882",
            "recursion_after_selector_filter_lines": "564-566",
            "seed_depth_four_lines": "900-904",
            "source_sha256": source_bindings["source"][1],
        },
        "fresh Config3 split-proof contract mismatch",
    )
    _, referenced_run_digest = require_release_file_reference(
        release_directory,
        release["run_result"],
        "RUN_RESULT.json",
        manifest,
        "fresh Config3 run result",
    )
    require(
        referenced_run_digest == spec["run_result_sha256"],
        "fresh Config3 RELEASE.json run-result binding mismatch",
    )

    run_result = read_canonical_json(run_result_path, "fresh Config3 RUN_RESULT.json")
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
        and run_result["release_schema"] == spec["schema"]
        and run_result["engine_sha256"] == engine_digest
        and run_result["logical_partition_count"] == 47
        and run_result["logical_node_sum"] == 167742832
        and run_result["logical_roster"] == roster
        and run_result["direct_partition_count"] == 46
        and run_result["direct_node_sum"] == 124893923
        and run_result["physical_zero_process_count"] == 68
        and run_result["frontier_census_process_count"] == 1,
        "fresh Config3 RUN_RESULT.json header mismatch",
    )
    direct_receipts = run_result["direct_receipts"]
    require(
        isinstance(direct_receipts, list) and len(direct_receipts) == 46,
        "fresh Config3 direct-receipt roster length mismatch",
    )
    direct_nodes: list[int] = []
    for index, (key, item) in enumerate(zip(direct_roster, direct_receipts)):
        require(
            isinstance(item, dict)
            and set(item) == {"logical_index", "key", "expected_nodes", "receipt"}
            and item["logical_index"] == index
            and item["key"] == key
            and type(item["expected_nodes"]) is int
            and item["expected_nodes"] >= 0,
            f"fresh Config3 direct receipt entry mismatch at logical index {index}",
        )
        direct_nodes.append(item["expected_nodes"])
        directory = "direct/" + key.replace("|", "__")
        require_receipt_reference(
            release_directory,
            item["receipt"],
            f"{directory}/RECEIPT.json",
            manifest,
            f"fresh Config3 direct receipt {index}",
        )
    require(sum(direct_nodes) == 124893923, "fresh Config3 direct node sum mismatch")

    split = run_result["split_replacement"]
    require(
        isinstance(split, dict)
        and set(split)
        == {
            "logical_index",
            "key",
            "expected_nodes",
            "census_receipt",
            "child_count",
            "child_indices",
            "children",
            "child_reported_node_sum",
            "repeated_prefix_calls_per_child",
            "normalization_subtraction",
            "normalized_parent_nodes",
            "node_identity",
        }
        and split["logical_index"] == 46
        and split["key"] == target_key
        and split["expected_nodes"] == 42848909
        and split["child_count"] == 22
        and split["child_indices"] == list(range(22))
        and split["child_reported_node_sum"] == 42848972
        and split["repeated_prefix_calls_per_child"] == 3
        and split["normalization_subtraction"] == 63
        and split["normalized_parent_nodes"] == 42848909
        and split["node_identity"] == split_proof["node_identity"],
        "fresh Config3 split-replacement header mismatch",
    )
    require_receipt_reference(
        release_directory,
        split["census_receipt"],
        "split/frontier/RECEIPT.json",
        manifest,
        "fresh Config3 split frontier receipt",
    )
    children = split["children"]
    require(
        isinstance(children, list) and len(children) == 22,
        "fresh Config3 split-child roster length mismatch",
    )
    for index, (expected_nodes, child) in enumerate(
        zip(CONFIG3_SPLIT_CHILD_NODES, children)
    ):
        require(
            isinstance(child, dict)
            and set(child) == {"index", "nodes", "receipt"}
            and child["index"] == index
            and child["nodes"] == expected_nodes,
            f"fresh Config3 split child mismatch at index {index}",
        )
        require_receipt_reference(
            release_directory,
            child["receipt"],
            f"split/children/k_{index:03d}/RECEIPT.json",
            manifest,
            f"fresh Config3 split child receipt {index}",
        )
    require(
        sum(CONFIG3_SPLIT_CHILD_NODES) == 42848972
        and sum(CONFIG3_SPLIT_CHILD_NODES) - 3 * (22 - 1) == 42848909
        and sum(direct_nodes) + 42848909 == 167742832,
        "fresh Config3 split normalization identity failed",
    )

    expected_marker = (
        "CONFIG3_A2_FROZEN_SPLIT_STRICT_OK "
        "schema=config3-a2-frozen-split-release-v1 "
        "logical_partitions=47 direct=46 children=22 logical_nodes=167742832 "
        f"manifest_sha256={spec['manifest_sha256']} "
        f"release_sha256={spec['release_record_sha256']} "
        f"run_result_sha256={spec['run_result_sha256']}"
    )
    require(
        spec["expected_marker"] == expected_marker
        and spec["normalized_stdout_sha256"]
        == hashlib.sha256(expected_marker.encode("utf-8")).hexdigest(),
        "fresh Config3 exact stdout contract mismatch",
    )
    require(
        sha256_file(release_path) == spec["release_record_sha256"]
        and sha256_file(run_result_path) == spec["run_result_sha256"]
        and sha256_file(manifest_path) == spec["manifest_sha256"],
        "fresh Config3 root evidence changed during validation",
    )
    print(
        "CHECK CONFIGURATION 3 FROZEN SPLIT RELEASE PINNED "
        f"logical_partitions=47 direct=46 children=22 nodes=167742832 "
        f"files={len(manifest) + 1} "
        f"sha256={spec['release_record_sha256']}"
    )


def check_terminal_plan_regeneration_contract(
    plan: dict[str, Any],
    freeze: dict[str, Any],
    distribution: dict[str, str],
) -> None:
    regeneration = plan["regeneration"]
    require(
        isinstance(regeneration, dict)
        and set(regeneration)
        == {
            "builder_source_relative_path",
            "builder_sha256",
            "comparator_path",
            "comparator_sha256",
            "plan_id",
            "runtime_directory",
            "c157_archive_path",
            "c157_archive_sha256",
            "c157_archive_bytes",
            "c157_package_path",
            "config4_archive_path",
            "config4_archive_sha256",
            "config4_archive_bytes",
            "config4_package_path",
            "expected_files",
            "archive_package_identity_audited",
            "package_replay_exact",
        },
        "terminal-plan regeneration contract field mismatch",
    )
    backup_root = "computation/evidence/full"
    full_workspace = (
        f"{backup_root}/g001_terminal5_candidate4_20260818T230000Z_workspace"
    )
    expected_fixed = {
        "builder_source_relative_path": "make_g001_terminal5_plan_v1.py",
        "builder_sha256":
            "3a59bf1fbf79443a06de90ee3b556d5d19b2d0cab3ce12bac3d88ee3b8dc9e79",
        "comparator_path": "proof/verify_terminal_plan_regeneration.py",
        "plan_id": "g001-terminal5-v1-candidate4",
        "runtime_directory": f"{full_workspace}/runtime/terminal5_runtime_v1",
        "c157_archive_path": (
            f"{backup_root}/results/"
            "c157_resume861_collect_compat_v2r1_20260818T160902Z_"
            "publication3_archive_20260818T175225Z/"
            "AMD_G001_C157_JOB376839_RESUME861_V1_SLURM377219_"
            "COLLECTED_20260818T175225Z.tar.gz"
        ),
        "c157_archive_sha256":
            "97f3584ad70917031e3bef44c43d6d8cd4705c51c50869860961fa41ca7726d0",
        "c157_archive_bytes": 94329607,
        "c157_package_path": (
            f"{backup_root}/results/"
            "c157_resume861_collect_compat_v2r1_20260818T160902Z_publication3/"
            "G001_C157_JOB376839_RESUME861_V1_SLURM377219_COLLECTED"
        ),
        "config4_archive_path": (
            f"{backup_root}/results/config4_job377045_recovery_v1_"
            "20260818T131100Z_workspace/"
            "AMD_G001_CONFIG4_P2_HEAVY16_V1_SLURM377045_RECOVERED_"
            "COLLECTED.tar.gz"
        ),
        "config4_archive_sha256":
            "76e793a1911e54de2ebec04cfe22df7115f3cecbfbd0f53df6b187256d0949c2",
        "config4_archive_bytes": 70200766,
        "config4_package_path": (
            f"{backup_root}/results/config4_job377045_recovery_v1_"
            "20260818T131100Z_workspace/"
            "G001_CONFIG4_P2_HEAVY16_V1_SLURM377045_RECOVERED_COLLECTED"
        ),
        "expected_files": 195,
        "archive_package_identity_audited": True,
        "package_replay_exact": True,
    }
    for key, expected in expected_fixed.items():
        require(
            regeneration.get(key) == expected,
            f"terminal-plan regeneration {key} mismatch",
        )
    require(
        isinstance(regeneration["comparator_sha256"], str)
        and HEX64.fullmatch(regeneration["comparator_sha256"]) is not None,
        "terminal-plan comparator SHA-256 is malformed",
    )
    require(
        freeze["full_replay_directory"] == f"{full_workspace}/source",
        "terminal-plan builder is not bound to the full frozen source directory",
    )
    require(
        plan["full_replay_path"]
        == f"{full_workspace}/plan/terminal5_plan_v1/terminal_plan_v1.json",
        "terminal-plan replay path is not the full workspace plan",
    )
    builder_name = regeneration["builder_source_relative_path"]
    require(
        distribution.get(builder_name) == regeneration["builder_sha256"],
        "terminal-plan builder is not bound by the source freeze",
    )
    builder = require_plain_file(
        extended_windows_path(
            workspace_path(
                f"{freeze['full_replay_directory']}/{builder_name}", "plan builder"
            )
        ),
        "terminal-plan builder",
    )
    require(
        sha256_file(builder) == regeneration["builder_sha256"],
        "terminal-plan builder SHA-256 mismatch",
    )
    check_hash(regeneration["comparator_path"], regeneration["comparator_sha256"])
    require_plain_directory(
        extended_windows_path(
            workspace_path(regeneration["runtime_directory"], "plan runtime")
        ),
        "terminal-plan runtime directory",
    )
    for label in ("c157", "config4"):
        archive = require_file(regeneration[f"{label}_archive_path"])
        require(
            archive.stat().st_size == regeneration[f"{label}_archive_bytes"],
            f"terminal-plan {label} archive size mismatch",
        )
        check_hash(
            regeneration[f"{label}_archive_path"],
            regeneration[f"{label}_archive_sha256"],
        )
        package = require_plain_directory(
            extended_windows_path(
                workspace_path(
                    regeneration[f"{label}_package_path"], f"{label} package"
                )
            ),
            f"terminal-plan {label} package",
        )
        require(package.name.startswith("G001_"), f"bad {label} package basename")
    frozen_plan = read_json(
        extended_windows_path(
            workspace_path(plan["full_replay_path"], "full terminal plan")
        )
    )
    require(
        frozen_plan.get("plan_id") == regeneration["plan_id"],
        "terminal-plan identifier mismatch",
    )
    print(
        "CHECK TERMINAL PLAN REGENERATION CONTRACT OK "
        "archives=2 expected_files=195"
    )


def check_final_five(record: dict[str, Any]) -> int:
    evidence = record["evidence"]
    stdout_hashes = evidence["normalized_stdout_sha256"]
    expected_stdout_names = {
        "source_freeze",
        "terminal5_source_tests",
        "terminal_plan_regeneration_build",
        "terminal_plan_regeneration_compare",
        "terminal_plan",
        "prior_three_manifest",
        "configuration_3_strict_ledger_audit",
        "configuration_2",
        "configuration_3",
        "configuration_8",
        "global_relocated_collector",
    }
    require(
        isinstance(stdout_hashes, dict)
        and set(stdout_hashes) == expected_stdout_names
        and all(
            isinstance(value, str) and HEX64.fullmatch(value) is not None
            for value in stdout_hashes.values()
        ),
        "bad normalized verifier-stdout digest map",
    )
    runtime_validation = evidence["runtime_source_validation"]
    require(
        isinstance(runtime_validation, dict)
        and set(runtime_validation)
        == {
            "path",
            "sha256",
            "pinned_source_files",
            "compile_flags",
            "solver_regression_checks",
            "independent_checker_self_test_checks",
            "compiler_include_environment_sanitized",
            "compiler_dynamic_environment_sanitized",
            "compiler_rehashed_after_tests",
            "binaries_rehashed_after_tests",
            "source_rehashed_after_tests",
            "output_tree_exact",
            "production_binary_identity_claimed",
        },
        "bad frozen runtime-source validation field set",
    )
    check_hash(runtime_validation["path"], runtime_validation["sha256"])
    require(
        runtime_validation["pinned_source_files"] == 8
        and runtime_validation["compile_flags"]
        == ["-O2", "-std=c++20", "-Wall", "-Wextra", "-Wpedantic", "-Werror"]
        and runtime_validation["solver_regression_checks"] == 45
        and runtime_validation["independent_checker_self_test_checks"] == 11
        and runtime_validation["compiler_include_environment_sanitized"] is True
        and runtime_validation["compiler_dynamic_environment_sanitized"] is True
        and runtime_validation["compiler_rehashed_after_tests"] is True
        and runtime_validation["binaries_rehashed_after_tests"] is True
        and runtime_validation["source_rehashed_after_tests"] is True
        and runtime_validation["output_tree_exact"] is True
        and runtime_validation["production_binary_identity_claimed"] is False,
        "bad frozen runtime-source validation contract",
    )
    freeze = evidence["source_freeze"]
    check_hash(freeze["path"], freeze["sha256"])
    freeze_path = workspace_path(freeze["path"], "source freeze")
    freeze_json = read_json(freeze_path)
    require(freeze_json["schema"] == "G001_TERMINAL5_SOURCE_FREEZE_V1", "bad freeze schema")
    require(freeze_json["distribution_count"] == freeze["distribution_files"], "bad freeze count")
    require(
        len(freeze_json["distribution_files"]) == freeze["distribution_files"],
        "bad freeze map size",
    )
    distribution = freeze_json["distribution_files"]
    require(
        isinstance(distribution, dict)
        and all(
            isinstance(relative, str)
            and isinstance(digest, str)
            and HEX64.fullmatch(digest) is not None
            for relative, digest in distribution.items()
        ),
        "bad source-freeze distribution map",
    )
    check_hash(freeze["checksum_path"], freeze["checksum_sha256"])
    freeze_name = Path(freeze["path"]).name
    checksum_name = Path(freeze["checksum_path"]).name
    check_frozen_source_directory(
        freeze_path.parent,
        freeze_name,
        freeze["sha256"],
        checksum_name,
        freeze["checksum_sha256"],
        distribution,
        "compact",
    )
    check_frozen_source_directory(
        workspace_path(freeze["full_replay_directory"], "full-replay source"),
        freeze_name,
        freeze["sha256"],
        checksum_name,
        freeze["checksum_sha256"],
        distribution,
        "full-replay",
    )
    print(f"CHECK SOURCE FREEZE RECORD OK files={freeze['distribution_files']}")

    plan = evidence["terminal_plan"]
    require(
        isinstance(plan, dict)
        and set(plan)
        == {
            "path",
            "sha256",
            "full_replay_path",
            "full_manifest_path",
            "full_manifest_sha256",
            "full_receipt_path",
            "full_receipt_sha256",
            "regeneration",
            "exact6_argument_suffix",
            "displayed_records",
            "search_receipts",
            "certified_zero_records",
            "bundles",
        },
        "terminal-plan evidence field mismatch",
    )
    check_hash(plan["path"], plan["sha256"])
    check_hash(plan["full_replay_path"], plan["sha256"])
    check_hash(plan["full_manifest_path"], plan["full_manifest_sha256"])
    check_hash(plan["full_receipt_path"], plan["full_receipt_sha256"])
    check_terminal_plan_regeneration_contract(plan, freeze, distribution)
    require(
        plan["exact6_argument_suffix"]
        == [
            "--multi-edge-cover",
            "--multi-edge-cover-no-hall",
            "--multi-edge-cover-max-components",
            "6",
            "--multi-edge-cover-budget",
            "100",
            "--multi-edge-cover-no-exact-hall",
            "--multi-edge-cover-exact-max-components",
            "6",
        ],
        "terminal-plan exact6 argument suffix mismatch",
    )
    plan_invariants = freeze_json["terminal_plan_invariants"]
    require(
        plan["displayed_records"] == plan_invariants["partition_records"] == 39030
        and plan["search_receipts"] == plan_invariants["search_leaves"] == 39000
        and plan["certified_zero_records"]
        == plan_invariants["certified_zero_records"]
        == 30
        and plan["bundles"] == plan_invariants["bundles"] == 192,
        "terminal-plan counts differ from the pinned source-freeze contract",
    )

    global_spec = evidence["global_record"]
    check_hash(global_spec["path"], global_spec["sha256"])
    data = read_json(workspace_path(global_spec["path"], "global record"))
    require(data["schema"] == "G001_TERMINAL5_COLLECTION_V1", "bad global schema")
    require(data["status"] == global_spec["status"], "bad global terminal status")
    require(data["global_nonexistence"] is True, "global_nonexistence is not true")
    require(data["terminal_search_complete"] is True, "terminal_search_complete is not true")
    require(data["timeouts_are_non_evidence"] is True, "timeouts policy is not fail-closed")
    require(data["search_receipts"] == global_spec["search_receipts"], "bad search receipt count")
    require(
        data["certified_zero_records"] == global_spec["certified_zero_records"],
        "bad certified-zero count",
    )
    require(
        data["displayed_partition_records"] == global_spec["displayed_records"],
        "bad displayed-record count",
    )
    by_configuration = data["by_configuration"]
    configurations = sorted(int(key) for key in by_configuration)
    require(configurations == global_spec["configurations"], "bad final-five configuration set")
    for key, value in by_configuration.items():
        require(value["terminal_zero"] is True, f"configuration {key} is not terminal_zero")
    nodes = sum(item["nodes_sum"] for item in by_configuration.values())
    require(nodes == global_spec["nodes"], f"bad final-five node total: {nodes}")
    print(
        "CHECK GLOBAL RECORD OK "
        f"status={data['status']} search={data['search_receipts']} "
        f"certified_zero={data['certified_zero_records']} nodes={nodes}"
    )

    adapter = evidence["global_relocation_adapter"]
    check_hash(adapter["path"], adapter["sha256"])
    replay = evidence["recorded_global_replay"]
    check_hash(replay["path"], replay["sha256"])
    replay_text = workspace_path(
        replay["path"], "recorded global replay"
    ).read_text(encoding="utf-8")
    require_unique_exact_line(
        replay_text, adapter["expected_marker"], "recorded global replay"
    )
    require(replay["exit_code"] == 0, "recorded global replay did not exit zero")
    require(replay["stderr_bytes"] == 0, "recorded global replay stderr was not empty")
    print("CHECK RECORDED GLOBAL REPLAY OK exit=0 stderr_bytes=0")
    return nodes


def check_earlier_certificates(record: dict[str, Any]) -> tuple[int, int]:
    total_partitions = 0
    total_nodes = 0
    seen: list[int] = []
    expected_totals = {
        2: (79, 193281350),
        3: (47, 167742832),
        8: (52, 239702053),
    }
    for certificate in record["evidence"]["earlier_certificates"]:
        configuration = certificate["configuration"]
        require(
            configuration in expected_totals
            and (certificate["partitions"], certificate["nodes"])
            == expected_totals[configuration],
            f"bad earlier-certificate totals for configuration {configuration}",
        )
        check_hash(certificate["path"], certificate["sha256"])
        text = workspace_path(
            certificate["path"], "earlier certificate"
        ).read_text(encoding="utf-8")
        require_unique_exact_line(
            text,
            certificate["expected_marker"],
            f"configuration {certificate['configuration']} certificate",
        )
        nodes_text = f"{certificate['nodes']:,}"
        require(
            nodes_text in text,
            f"node count {nodes_text} absent from configuration {certificate['configuration']}",
        )
        seen.append(certificate["configuration"])
        total_partitions += certificate["partitions"]
        total_nodes += certificate["nodes"]
        print(
            "CHECK EARLIER CERTIFICATE OK "
            f"configuration={certificate['configuration']} "
            f"partitions={certificate['partitions']} nodes={certificate['nodes']}"
        )
    require(seen == [2, 3, 8], f"bad earlier-configuration order/set: {seen}")
    return total_partitions, total_nodes


def main() -> int:
    try:
        require_plain_directory_ancestry(ROOT, "workspace root")
        require_plain_directory(HERE, "proof package directory")
        require_plain_file(Path(__file__).absolute(), "proof-record verifier")
        record = read_json(require_plain_file(RECORD_PATH, "proof record"))
        require(
            isinstance(record, dict)
            and set(record)
            == {
                "schema",
                "date",
                "claim",
                "proof_kind",
                "pure_lean_end_to_end",
                "search_rerun_by_this_workflow",
                "lean",
                "configuration_correspondence",
                "evidence",
                "known_limits",
            },
            "proof-record top-level field set mismatch",
        )
        require(record["schema"] == "LEECH18_HYBRID_END_TO_END_PROOF_V1", "bad record schema")
        require(record["date"] == "2026-08-21", "bad proof-record date")
        require(
            record["claim"]
            == "There is no positively weighted integral Leech tree on 18 vertices.",
            "bad proof-record claim",
        )
        require(
            record["proof_kind"] == "hybrid computer-assisted proof",
            "bad proof-record kind",
        )
        require(record["pure_lean_end_to_end"] is False, "record misstates pure-Lean status")
        require(record["search_rerun_by_this_workflow"] is False, "record misstates search rerun")
        require(
            record["known_limits"]
            == [
                "The production computation is not checked inside Lean.",
                "The semantic descriptor bridge does not kernel-prove the constructive vertex relabeling, exact-orbit representative preservation, or partition-index transport; the external evidence does not construct a Lean RowExclusions value.",
                "The exact historical global collector shell transcript is absent; the pinned relocation adapter replays the frozen collector.",
                "Configuration 3 has incomplete original raw job evidence and one inferred historical exit code; the current workflow therefore requires a separately released fresh exact 47-logical-partition result, with 46 direct receipts and a complete censused 22-child replacement for the guarded parent.",
                "No independently written verifier checks the complete exhaustive ZERO search.",
                "The production compiler executable, full version output, and exact production Python version were not preserved.",
                "The local frozen-source rebuild and 45+11 tests do not reproduce or identify the historical GCC 12 production binary, and subordinate compiler toolchain components remain trusted.",
                "Terminal-plan regeneration replays sealed calibration outputs but does not rerun the calibration searches or independently verify the frozen package-replay implementation.",
                "The pristine Lean project build reuses pinned dependency build caches; those dependency oleans and the Lean toolchain remain trusted.",
                "The workflow verifies preserved evidence and does not rerun the 8.5-billion-node production search.",
            ],
            "proof-record known-limit list mismatch",
        )
        require(
            set(record["evidence"])
            == {
                "source_freeze",
                "runtime_source_validation",
                "terminal_plan",
                "prior_three_evidence",
                "configuration3_fresh_result",
                "semantic_bridge",
                "global_record",
                "earlier_certificates",
                "global_relocation_adapter",
                "recorded_global_replay",
                "normalized_stdout_sha256",
                "all_eight",
            },
            "proof-record evidence section mismatch",
        )
        print(f"CHECK PROOF RECORD SCHEMA OK {record['schema']}")

        check_lean_identity(record)
        check_configuration_map(record)
        check_semantic_bridge_contract(record)
        final_nodes = check_final_five(record)
        check_prior_three_evidence(record)
        check_configuration3_fresh_result(record)
        earlier_partitions, earlier_nodes = check_earlier_certificates(record)

        combined = record["evidence"]["all_eight"]
        require(
            combined
            == {
                "executed_pieces": 39178,
                "reused_certified_zero_records": 30,
                "covered_pieces": 39208,
                "reported_node_visits": 8565199014,
            },
            "bad all-eight summary record",
        )
        require(earlier_partitions == 178, f"bad earlier partition total: {earlier_partitions}")
        require(
            final_nodes + earlier_nodes == combined["reported_node_visits"],
            "bad all-eight node total",
        )
        require(
            39000 + earlier_partitions == combined["executed_pieces"],
            "bad all-eight executed-piece total",
        )
        require(
            combined["executed_pieces"] + combined["reused_certified_zero_records"]
            == combined["covered_pieces"],
            "bad all-eight covered-piece total",
        )
        print(
            "CHECK ALL EIGHT TOTALS OK "
            f"executed={combined['executed_pieces']} "
            f"reused_zero={combined['reused_certified_zero_records']} "
            f"covered={combined['covered_pieces']} "
            f"nodes={combined['reported_node_visits']}"
        )
        print(
            "LEECH18_HYBRID_RECORD_OK "
            f"configurations=8 reported_node_visits={combined['reported_node_visits']}"
        )
        return 0
    except (CheckError, KeyError, TypeError, ValueError) as exc:
        print(f"LEECH18_HYBRID_RECORD_ERROR {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
