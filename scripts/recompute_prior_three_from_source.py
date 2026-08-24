#!/usr/bin/env python3
"""Build and optionally recompute Configurations 2, 3, and 8 from source.

This is an additive public reproduction driver.  It never overwrites the
preserved production executables.  The default preflight/build paths are
inexpensive; a full search requires both --run-root and
--confirm-expensive-run.
"""

from __future__ import annotations

import argparse
from dataclasses import replace
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
from typing import NoReturn, Sequence

import recompute_prior_three_full as frozen


EXPECTED_COMPILER_VERSION = "14.2.0"
COMPILE_FLAGS = ("-O2", "-std=c++20", "-Wall", "-Wextra", "-Wpedantic")

SOLVERS = (
    (
        "configuration_3",
        "a2_topology_free_search.cpp",
        frozen.CONFIG3_SOURCE_SHA256,
        "a2_topology_free_search_multicover_rebuild.exe",
    ),
    (
        "configuration_8",
        "order18_topology_free_search_production_snapshot.cpp",
        frozen.ROW7_SOURCE_SHA256,
        "order18_topology_free_search_row7_rebuild.exe",
    ),
    (
        "configuration_2",
        "order18_topology_free_search_row1_snapshot.cpp",
        frozen.ROW1_SOURCE_SHA256,
        "order18_topology_free_search_row1_rebuild.exe",
    ),
)

TESTS = (
    ("test_multi_edge_exact_cover.cpp", "MULTI_EDGE_EXACT_COVER_TEST_OK"),
    (
        "test_multi_edge_exact_cover_small_orders.cpp",
        "MULTI_EDGE_EXACT_COVER_SMALL_ORDER_OK",
    ),
    (
        "test_multi_edge_exact_cover_optimized.cpp",
        "MULTI_EDGE_EXACT_COVER_OPTIMIZED_TEST_OK",
    ),
    (
        "test_multi_edge_stronger_relaxation.cpp",
        "MULTI_EDGE_STRONGER_RELAXATION_TEST_OK",
    ),
    (
        "test_multi_edge_stronger_small_orders.cpp",
        "MULTI_EDGE_STRONGER_SMALL_ORDER_OK",
    ),
    (
        "test_multi_edge_parity_coherence.cpp",
        "MULTI_EDGE_PARITY_COHERENCE_OK",
    ),
    ("audit_multi_edge_stronger_oracle.cpp", "MULTI_EDGE_STRONGER_ORACLE_AUDIT_OK"),
)


class SourceRecomputeError(RuntimeError):
    pass


def fail(message: str) -> NoReturn:
    raise SourceRecomputeError(message)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while block := stream.read(1024 * 1024):
            digest.update(block)
    return digest.hexdigest()


def require_new_directory(path: Path, label: str) -> Path:
    path = Path(os.path.abspath(os.fspath(path)))
    if os.path.lexists(path):
        fail(f"{label} already exists: {path}")
    if not path.parent.is_dir():
        fail(f"{label} parent is absent: {path.parent}")
    return path


def compiler_identity(cxx: Path, allow_unpinned: bool) -> tuple[Path, str, str]:
    cxx = cxx.resolve(strict=True)
    if not cxx.is_file():
        fail(f"compiler is not a regular file: {cxx}")
    completed = subprocess.run(
        [str(cxx), "--version"],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
        errors="strict",
    )
    if completed.returncode != 0 or completed.stderr:
        fail(
            "compiler --version failed or wrote stderr: "
            f"exit={completed.returncode} stderr={completed.stderr!r}"
        )
    version = completed.stdout.strip()
    if not version:
        fail("compiler --version returned empty stdout")
    if EXPECTED_COMPILER_VERSION not in version and not allow_unpinned:
        fail(
            f"compiler is not the pinned GNU g++ {EXPECTED_COMPILER_VERSION}; "
            "use --allow-unpinned-compiler only for a clearly labelled portability run"
        )
    return cxx, version, sha256_file(cxx)


def validate_sources() -> list[dict[str, str]]:
    source_dir = frozen.SOLVER_DIR
    records: list[dict[str, str]] = []
    expected = {name: digest for _, name, digest, _ in SOLVERS}
    expected.update(frozen.SOURCE_DEPENDENCY_HASHES)
    for name in sorted(expected):
        path = source_dir / name
        if not path.is_file():
            fail(f"required source is absent: {path}")
        actual = sha256_file(path)
        if actual != expected[name]:
            fail(
                f"source hash mismatch path={path} "
                f"expected={expected[name]} actual={actual}"
            )
        records.append({"path": name, "sha256": actual})
    for name, _ in TESTS:
        path = source_dir / name
        if not path.is_file():
            fail(f"required test source is absent: {path}")
        records.append({"path": name, "sha256": sha256_file(path)})
    return records


def compile_one(cxx: Path, source: Path, output: Path) -> dict[str, object]:
    command = [str(cxx), *COMPILE_FLAGS, source.name, "-o", str(output)]
    completed = subprocess.run(
        command,
        cwd=str(source.parent),
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
        errors="strict",
    )
    if completed.returncode != 0:
        fail(
            f"compile failed source={source.name} exit={completed.returncode} "
            f"stdout={completed.stdout!r} stderr={completed.stderr!r}"
        )
    if completed.stdout or completed.stderr:
        fail(
            f"compile produced unexpected output source={source.name} "
            f"stdout={completed.stdout!r} stderr={completed.stderr!r}"
        )
    if not output.is_file():
        fail(f"compiler returned success without output: {output}")
    return {
        "source": source.name,
        "output": output.name,
        "command": command,
        "sha256": sha256_file(output),
        "size_bytes": output.stat().st_size,
    }


def build_all(
    cxx: Path,
    compiler_version: str,
    compiler_hash: str,
    build_root: Path,
    source_records: list[dict[str, str]],
) -> tuple[dict[str, Path], dict[str, object]]:
    build_root.mkdir(mode=0o700)
    source_dir = frozen.SOLVER_DIR
    executables: dict[str, Path] = {}
    solver_records: list[dict[str, object]] = []
    for role, source_name, _, output_name in SOLVERS:
        output = build_root / output_name
        solver_records.append(compile_one(cxx, source_dir / source_name, output))
        executables[role] = output

    test_records: list[dict[str, object]] = []
    child_environment = os.environ.copy()
    child_environment["PATH"] = str(cxx.parent) + os.pathsep + child_environment.get(
        "PATH", ""
    )
    for source_name, marker in TESTS:
        output = build_root / (Path(source_name).stem + "_rebuild.exe")
        compiled = compile_one(cxx, source_dir / source_name, output)
        completed = subprocess.run(
            [str(output)],
            cwd=str(build_root),
            env=child_environment,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            encoding="utf-8",
            errors="strict",
        )
        if completed.returncode != 0 or completed.stderr:
            fail(
                f"test failed source={source_name} exit={completed.returncode} "
                f"stdout={completed.stdout!r} stderr={completed.stderr!r}"
            )
        lines = completed.stdout.splitlines()
        if marker not in lines:
            fail(f"test marker absent source={source_name} marker={marker!r}")
        compiled.update(
            {
                "exit_code": completed.returncode,
                "expected_marker": marker,
                "stdout": completed.stdout,
            }
        )
        test_records.append(compiled)

    receipt: dict[str, object] = {
        "schema": "LEECH18_PRIOR_THREE_SOURCE_BUILD_V1",
        "compiler": {
            "path": str(cxx),
            "sha256": compiler_hash,
            "version_output": compiler_version,
            "historical_documented_version": EXPECTED_COMPILER_VERSION,
            "matches_historical_documented_version": EXPECTED_COMPILER_VERSION
            in compiler_version,
        },
        "compile_flags": list(COMPILE_FLAGS),
        "sources": source_records,
        "solvers": solver_records,
        "tests": test_records,
    }
    receipt_path = build_root / "BUILD_RECEIPT.json"
    receipt_path.write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    (build_root / "BUILD_RECEIPT.sha256").write_text(
        sha256_file(receipt_path) + "  BUILD_RECEIPT.json\n",
        encoding="ascii",
        newline="\n",
    )
    return executables, receipt


def rebuilt_groups(executables: dict[str, Path]) -> tuple[list[frozen.Job], ...]:
    groups = frozen.assemble_jobs()
    replacements = {
        2: executables["configuration_2"],
        3: executables["configuration_3"],
        8: executables["configuration_8"],
    }
    return tuple(
        [replace(job, solver=replacements[job.configuration]) for job in group]
        for group in groups
    )


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cxx", type=Path, required=True)
    parser.add_argument("--allow-unpinned-compiler", action="store_true")
    selection = parser.add_mutually_exclusive_group(required=True)
    selection.add_argument("--preflight", action="store_true")
    selection.add_argument("--build-only", action="store_true")
    selection.add_argument("--run-root", type=Path)
    parser.add_argument("--build-root", type=Path)
    parser.add_argument("--confirm-expensive-run", action="store_true")
    arguments = parser.parse_args(argv)

    try:
        if os.name != "nt":
            fail("the prior-three source build is documented for Windows/MSYS2 UCRT64")
        cxx, version, compiler_hash = compiler_identity(
            arguments.cxx, arguments.allow_unpinned_compiler
        )
        sources = validate_sources()
        if arguments.preflight:
            if arguments.build_root is not None or arguments.confirm_expensive_run:
                fail("--preflight does not accept build/run options")
            print(
                "LEECH18_PRIOR_THREE_SOURCE_PREFLIGHT_OK "
                f"compiler_sha256={compiler_hash} sources={len(sources)} "
                f"pinned_compiler={int(EXPECTED_COMPILER_VERSION in version)}"
            )
            return 0

        if arguments.build_root is None:
            fail("--build-root is required for build and run modes")
        build_root = require_new_directory(arguments.build_root, "build root")
        executables, receipt = build_all(
            cxx, version, compiler_hash, build_root, sources
        )
        receipt_hash = sha256_file(build_root / "BUILD_RECEIPT.json")
        print(
            "LEECH18_PRIOR_THREE_SOURCE_BUILD_OK "
            f"solvers={len(receipt['solvers'])} tests={len(receipt['tests'])} "
            f"receipt_sha256={receipt_hash}"
        )
        if arguments.build_only:
            if arguments.confirm_expensive_run:
                fail("--confirm-expensive-run is invalid with --build-only")
            return 0

        if not arguments.confirm_expensive_run:
            fail("full search requires the explicit --confirm-expensive-run flag")
        run_root = require_new_directory(arguments.run_root, "run root")
        os.environ["PATH"] = str(cxx.parent) + os.pathsep + os.environ.get("PATH", "")
        frozen.recompute(rebuilt_groups(executables), run_root)
        return 0
    except (SourceRecomputeError, frozen.RecomputeError, OSError, ValueError) as exc:
        print(f"LEECH18_PRIOR_THREE_SOURCE_RECOMPUTATION_FAIL: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
