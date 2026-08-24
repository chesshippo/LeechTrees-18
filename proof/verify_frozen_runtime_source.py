#!/usr/bin/env python3
"""Rebuild and self-test the pinned Terminal5 C++ sources without editing them."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
from typing import Sequence


SOURCE_HASHES = {
    "g001_remaining_witness_solver.cpp": "b741e28729da7c771a2129a9439e0f921730866ddaf2357cf472c876fdbd2b57",
    "check_g001_leech_witness.cpp": "802ed17b7857310fe1d220a6ef500ee7c7d5e18051f5c7b66136731f5acfb4ca",
    "test_g001_remaining_witness_solver.cpp": "ecd8e59aed72ed9ac6b31dc9987a22f5343f8fceccc68c2f3bf4c32bd77b171f",
    "order18_topology_free_search.cpp": "134373d19ad4b1b1dfb30595f73beabcef30fa21c19b74a652669fb7705a72d9",
    "a2_multi_edge_exact_cover.hpp": "c156eae52bceef28db0df1a38d10dea253de09e5f627d0952a6bb1b9356cd813",
    "a2_multi_edge_exact_cover_optimized.hpp": "5320c920e800ce2f9e2348b90d672e26cddd748b43bc02bc24b9146dedb5e48b",
    "a2_multi_edge_stronger_relaxation.hpp": "e58f917a631c48f2419835d41c2b0ee164f0d24f44ba489c152b9c00cddbbd5c",
    "multi_edge_parity_coherence.hpp": "af09e37c9e50fb3891bb11bbfead6d5f8299200c7abf81bc8049fb20a07d30c7",
}

COMPILE_FLAGS = ["-O2", "-std=c++20", "-Wall", "-Wextra", "-Wpedantic", "-Werror"]
TARGETS = {
    "g001_remaining_witness_solver": "g001_remaining_witness_solver.cpp",
    "check_g001_leech_witness": "check_g001_leech_witness.cpp",
    "test_g001_remaining_witness_solver": "test_g001_remaining_witness_solver.cpp",
}
SANITIZED_ENVIRONMENT_VARIABLES = (
    "C_INCLUDE_PATH",
    "COMPILER_PATH",
    "CPATH",
    "CPLUS_INCLUDE_PATH",
    "DEPENDENCIES_OUTPUT",
    "DYLD_FALLBACK_FRAMEWORK_PATH",
    "DYLD_FALLBACK_LIBRARY_PATH",
    "DYLD_FRAMEWORK_PATH",
    "DYLD_INSERT_LIBRARIES",
    "DYLD_LIBRARY_PATH",
    "GCC_EXEC_PREFIX",
    "GCC_COMPARE_DEBUG",
    "GCC_COMPARE_DEBUG_ORIGINAL",
    "GXX_INCLUDE_PATH",
    "INCLUDE",
    "LD_LIBRARY_PATH",
    "LD_PRELOAD",
    "LIB",
    "LIBPATH",
    "LIBRARY_PATH",
    "SUNPRO_DEPENDENCIES",
)


class ValidationError(RuntimeError):
    pass


def is_link_like(path: Path) -> bool:
    junction_test = getattr(path, "is_junction", None)
    if path.is_symlink() or bool(junction_test is not None and junction_test()):
        return True
    try:
        attributes = getattr(path.lstat(), "st_file_attributes", 0)
    except OSError:
        return False
    return bool(attributes & getattr(stat, "FILE_ATTRIBUTE_REPARSE_POINT", 0))


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def require_regular(path: Path, label: str) -> Path:
    try:
        info = path.lstat()
    except OSError as error:
        raise ValidationError(f"cannot inspect {label}: {path}: {error}") from error
    if (
        not stat.S_ISREG(info.st_mode)
        or info.st_nlink != 1
        or is_link_like(path)
    ):
        raise ValidationError(
            f"{label} is not a regular single-link file: {path}"
        )
    return path


def require_directory(path: Path, label: str) -> Path:
    try:
        info = path.lstat()
    except OSError as error:
        raise ValidationError(f"cannot inspect {label}: {path}: {error}") from error
    if not stat.S_ISDIR(info.st_mode) or is_link_like(path):
        raise ValidationError(f"{label} is not a plain directory: {path}")
    return path


def lexical_absolute(path: Path) -> Path:
    return Path(os.path.abspath(os.fspath(path)))


def require_directory_ancestry(path: Path, label: str) -> Path:
    target = lexical_absolute(path)
    for directory in reversed((target, *target.parents)):
        require_directory(directory, f"{label} ancestry")
    try:
        target.resolve(strict=True)
    except OSError as error:
        raise ValidationError(f"cannot resolve {label}: {target}: {error}") from error
    return target


def require_regular_tree(path: Path, label: str) -> Path:
    target = lexical_absolute(path)
    require_directory_ancestry(target.parent, f"{label} parent")
    require_regular(target, label)
    try:
        target.resolve(strict=True).relative_to(target.parent.resolve(strict=True))
    except (OSError, ValueError) as error:
        raise ValidationError(
            f"{label} resolves outside its original parent: {target}"
        ) from error
    return target


def write_bytes_new(path: Path, data: bytes) -> None:
    with path.open("xb") as stream:
        stream.write(data)


def run_logged(
    command: Sequence[str],
    cwd: Path,
    stdout_path: Path,
    stderr_path: Path,
    environment: dict[str, str],
) -> None:
    try:
        completed = subprocess.run(
            list(command),
            cwd=str(cwd),
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=environment,
            check=False,
            timeout=1800,
        )
    except subprocess.TimeoutExpired as error:
        stdout = error.stdout if isinstance(error.stdout, bytes) else b""
        stderr = error.stderr if isinstance(error.stderr, bytes) else b""
        write_bytes_new(stdout_path, stdout)
        write_bytes_new(stderr_path, stderr)
        raise ValidationError(
            f"command timed out after {error.timeout} seconds: "
            f"{' '.join(str(item) for item in command)}"
        ) from error
    write_bytes_new(stdout_path, completed.stdout)
    write_bytes_new(stderr_path, completed.stderr)
    if completed.returncode != 0:
        raise ValidationError(
            f"command exited {completed.returncode}: {' '.join(str(item) for item in command)}"
        )


def validate(source_dir: Path, output_dir: Path, cxx: str) -> dict[str, object]:
    source_dir = require_directory_ancestry(source_dir, "source directory")
    output_dir = lexical_absolute(output_dir)
    require_directory_ancestry(output_dir.parent, "output-directory parent")
    if output_dir.exists() or output_dir.is_symlink():
        raise ValidationError(f"output already exists: {output_dir}")
    try:
        output_dir.relative_to(source_dir)
    except ValueError:
        pass
    else:
        raise ValidationError("output directory may not be inside frozen source")

    observed_sources: dict[str, str] = {}
    for name, expected in sorted(SOURCE_HASHES.items()):
        path = require_regular_tree(source_dir / name, f"source {name}")
        actual = sha256_file(path)
        if actual != expected:
            raise ValidationError(f"source SHA-256 mismatch for {name}: {actual} != {expected}")
        observed_sources[name] = actual

    compiler_text = shutil.which(cxx)
    if compiler_text is None:
        candidate = Path(cxx)
        if not candidate.exists():
            raise ValidationError(f"C++ compiler not found: {cxx}")
        compiler_text = str(candidate)
    compiler = require_regular_tree(Path(compiler_text), "C++ compiler")
    compiler_sha256 = sha256_file(compiler)
    environment = dict(os.environ)
    for name in SANITIZED_ENVIRONMENT_VARIABLES:
        environment.pop(name, None)

    output_dir.mkdir(parents=False)
    bin_dir = output_dir / "bin"
    log_dir = output_dir / "logs"
    bin_dir.mkdir()
    log_dir.mkdir()

    try:
        version = subprocess.run(
            [str(compiler), "--version"],
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=environment,
            check=False,
            timeout=60,
        )
    except subprocess.TimeoutExpired as error:
        stdout = error.stdout if isinstance(error.stdout, bytes) else b""
        stderr = error.stderr if isinstance(error.stderr, bytes) else b""
        write_bytes_new(log_dir / "compiler_version.stdout.txt", stdout)
        write_bytes_new(log_dir / "compiler_version.stderr.txt", stderr)
        raise ValidationError(
            f"compiler version command timed out after {error.timeout} seconds"
        ) from error
    write_bytes_new(log_dir / "compiler_version.stdout.txt", version.stdout)
    write_bytes_new(log_dir / "compiler_version.stderr.txt", version.stderr)
    if version.returncode != 0:
        raise ValidationError(f"compiler version command exited {version.returncode}")
    if not version.stdout:
        raise ValidationError("compiler version command produced empty stdout")
    suffix = ".exe" if os.name == "nt" else ""

    binaries: dict[str, dict[str, str]] = {}
    for target, source in TARGETS.items():
        binary = bin_dir / f"{target}{suffix}"
        run_logged(
            [str(compiler), *COMPILE_FLAGS, str(source_dir / source), "-o", str(binary)],
            source_dir,
            log_dir / f"compile_{target}.stdout.txt",
            log_dir / f"compile_{target}.stderr.txt",
            environment,
        )
        require_regular(binary, f"compiled binary {target}")
        binaries[target] = {
            "path": binary.relative_to(output_dir).as_posix(),
            "sha256": sha256_file(binary),
        }

    regression_stdout = log_dir / "witness_regression.stdout.txt"
    regression_stderr = log_dir / "witness_regression.stderr.txt"
    run_logged(
        [str(bin_dir / f"test_g001_remaining_witness_solver{suffix}")],
        source_dir,
        regression_stdout,
        regression_stderr,
        environment,
    )
    expected_newline = os.linesep.encode("ascii")
    if regression_stdout.read_bytes() != \
            b"PASS test_g001_remaining_witness_solver checks=45" + expected_newline:
        raise ValidationError("45-check solver regression marker mismatch")
    if regression_stderr.read_bytes():
        raise ValidationError("45-check solver regression wrote to stderr")

    checker_stdout = log_dir / "checker_self_test.stdout.txt"
    checker_stderr = log_dir / "checker_self_test.stderr.txt"
    run_logged(
        [str(bin_dir / f"check_g001_leech_witness{suffix}"), "--self-test"],
        source_dir,
        checker_stdout,
        checker_stderr,
        environment,
    )
    if checker_stdout.read_bytes() != b"SELF_TEST PASS checks=11" + expected_newline:
        raise ValidationError("11-check independent-checker marker mismatch")
    if checker_stderr.read_bytes():
        raise ValidationError("11-check independent checker wrote to stderr")

    for name, expected in observed_sources.items():
        actual = sha256_file(
            require_regular_tree(source_dir / name, f"source {name}")
        )
        if actual != expected:
            raise ValidationError(f"source changed during validation: {name}")
    for target, binding in binaries.items():
        binary = require_regular(
            output_dir / binding["path"], f"compiled binary {target}"
        )
        actual = sha256_file(binary)
        if actual != binding["sha256"]:
            raise ValidationError(f"compiled binary changed during validation: {target}")
    final_compiler_sha256 = sha256_file(
        require_regular_tree(compiler, "C++ compiler")
    )
    if final_compiler_sha256 != compiler_sha256:
        raise ValidationError("C++ compiler executable changed during validation")

    report: dict[str, object] = {
        "schema": "LEECH18_FROZEN_RUNTIME_SOURCE_VALIDATION_V1",
        "source_dir": str(source_dir),
        "source_hashes": observed_sources,
        "compiler": {
            "path": str(compiler),
            "sha256": compiler_sha256,
            "version_stdout_sha256": hashlib.sha256(version.stdout).hexdigest(),
            "version_stderr_sha256": hashlib.sha256(version.stderr).hexdigest(),
        },
        "compile_flags": COMPILE_FLAGS,
        "pinned_source_files": len(SOURCE_HASHES),
        "compiler_include_environment_sanitized": True,
        "compiler_dynamic_environment_sanitized": True,
        "compiler_rehashed_after_tests": True,
        "source_rehashed_after_tests": True,
        "binaries_rehashed_after_tests": True,
        "output_tree_exact": True,
        "production_binary_identity_claimed": False,
        "sanitized_environment_variables": SANITIZED_ENVIRONMENT_VARIABLES,
        "binaries": binaries,
        "tests": {
            "solver_regression_checks": 45,
            "independent_checker_self_test_checks": 11,
        },
    }
    report_bytes = (
        json.dumps(
            report,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
            allow_nan=False,
        )
        + "\n"
    ).encode("ascii")
    write_bytes_new(output_dir / "runtime_source_validation.json", report_bytes)

    expected_logs = {
        "compiler_version.stdout.txt",
        "compiler_version.stderr.txt",
        *(f"compile_{target}.{stream}.txt" for target in TARGETS for stream in ("stdout", "stderr")),
        "witness_regression.stdout.txt",
        "witness_regression.stderr.txt",
        "checker_self_test.stdout.txt",
        "checker_self_test.stderr.txt",
    }
    require_directory(output_dir, "validation output directory")
    require_directory(bin_dir, "validation binary directory")
    require_directory(log_dir, "validation log directory")
    root_entries = {item.name for item in output_dir.iterdir()}
    if root_entries != {"bin", "logs", "runtime_source_validation.json"}:
        raise ValidationError(f"validation output root exact-set mismatch: {sorted(root_entries)}")
    expected_binaries = {f"{target}{suffix}" for target in TARGETS}
    binary_entries = {item.name for item in bin_dir.iterdir()}
    if binary_entries != expected_binaries:
        raise ValidationError(f"validation binary exact-set mismatch: {sorted(binary_entries)}")
    log_entries = {item.name for item in log_dir.iterdir()}
    if log_entries != expected_logs:
        raise ValidationError(f"validation log exact-set mismatch: {sorted(log_entries)}")
    expected_files = {
        "runtime_source_validation.json",
        *(f"bin/{name}" for name in expected_binaries),
        *(f"logs/{name}" for name in expected_logs),
    }
    for relative in sorted(expected_files):
        require_regular(output_dir / Path(relative), f"validation output {relative}")
    manifest_lines = [
        f"{sha256_file(output_dir / Path(relative))}  {relative}\n"
        for relative in sorted(expected_files)
    ]
    manifest_bytes = "".join(manifest_lines).encode("ascii")
    write_bytes_new(
        output_dir / "runtime_source_validation.sha256", manifest_bytes
    )
    final_root_entries = {item.name for item in output_dir.iterdir()}
    if final_root_entries != {
        "bin", "logs", "runtime_source_validation.json",
        "runtime_source_validation.sha256",
    }:
        raise ValidationError(
            f"final validation output exact-set mismatch: {sorted(final_root_entries)}"
        )
    output_manifest = require_regular(
        output_dir / "runtime_source_validation.sha256",
        "validation output manifest",
    )
    for relative in sorted(expected_files):
        expected_digest = next(
            line.split("  ", 1)[0]
            for line in manifest_lines
            if line.endswith(f"  {relative}\n")
        )
        actual_digest = sha256_file(
            require_regular(
                output_dir / Path(relative), f"final validation output {relative}"
            )
        )
        if actual_digest != expected_digest:
            raise ValidationError(
                f"validation output changed before completion: {relative}"
            )
    if output_manifest.read_bytes() != manifest_bytes:
        raise ValidationError("validation output manifest changed before completion")
    return report


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-dir", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--cxx", default="g++")
    args = parser.parse_args(argv)
    try:
        require_regular_tree(Path(__file__).absolute(), "runtime-source verifier")
        report = validate(args.source_dir, args.output_dir, args.cxx)
    except (OSError, subprocess.SubprocessError, ValidationError) as error:
        print(f"LEECH18_FROZEN_RUNTIME_SOURCE_FAILED: {error}", file=sys.stderr)
        return 1
    binaries = report["binaries"]
    if not isinstance(binaries, dict):
        print("LEECH18_FROZEN_RUNTIME_SOURCE_FAILED: malformed binary report", file=sys.stderr)
        return 1
    print(
        "LEECH18_FROZEN_RUNTIME_SOURCE_OK "
        "solver_checks=45 checker_checks=11 "
        f"solver_sha256={binaries['g001_remaining_witness_solver']['sha256']} "
        f"checker_sha256={binaries['check_g001_leech_witness']['sha256']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
