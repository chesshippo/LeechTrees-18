#!/usr/bin/env python3
"""Build and seal the terminal witness solver/checker in a fresh runtime dir."""

from __future__ import annotations

import argparse
import json
import os
import shutil
import stat
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Dict, Optional, Sequence

# Frozen source and sealed evidence trees are read-only inputs.  Suppress
# interpreter cache writes before importing any local module.
sys.dont_write_bytecode = True

import g001_terminal5_common_v1 as common


RUNTIME_SCHEMA = "G001_TERMINAL5_RUNTIME_FREEZE_V1"
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


def _write_new(path: Path, raw: bytes, mode: int = 0o444) -> None:
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    descriptor = os.open(str(path), flags, mode)
    try:
        with os.fdopen(descriptor, "wb", closefd=False) as stream:
            stream.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
    finally:
        os.close(descriptor)


def _run(command: Sequence[str], cwd: Path, stdout: Path, stderr: Path) -> None:
    completed = subprocess.run(
        list(command), cwd=str(cwd), stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
    _write_new(stdout, completed.stdout)
    _write_new(stderr, completed.stderr)
    if completed.returncode != 0:
        raise common.TerminalError(
            f"command failed with exit {completed.returncode}: {command[0]}")


def build(source_dir: Path, workspace_root: Path, output: Path, cxx: str) -> Dict[str, object]:
    source_dir = common.require_directory(source_dir, "frozen source")
    workspace_root = common.require_directory(workspace_root, "workspace root")
    output = Path(os.path.abspath(os.fspath(output)))
    if output.exists() or output.is_symlink():
        raise common.TerminalError("runtime output already exists")
    if output.parent.resolve(strict=True) != output.parent:
        raise common.TerminalError("runtime output parent is not canonical")
    try:
        source_relative = source_dir.relative_to(workspace_root).as_posix()
        output.relative_to(workspace_root)
    except ValueError as error:
        raise common.TerminalError("source and runtime must be inside workspace root") from error
    for name, digest in SOURCE_HASHES.items():
        path = source_dir / name
        if common.sha256_file(path) != digest:
            raise common.TerminalError(f"frozen scientific source mismatch: {name}")
    compiler = shutil.which(cxx)
    if not compiler:
        raise common.TerminalError(f"C++ compiler not found: {cxx}")
    compiler = str(Path(compiler).resolve())
    version = subprocess.run(
        [compiler, "--version"], stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
    if version.returncode != 0 or version.stderr:
        raise common.TerminalError("compiler version preflight failed")
    private = Path(tempfile.mkdtemp(prefix=".terminal5-runtime-", dir=str(output.parent)))
    try:
        bin_dir = private / "bin"
        logs = private / "logs"
        bin_dir.mkdir(mode=0o700)
        logs.mkdir(mode=0o700)
        targets = {
            "g001_remaining_witness_solver": "g001_remaining_witness_solver.cpp",
            "check_g001_leech_witness": "check_g001_leech_witness.cpp",
            "test_g001_remaining_witness_solver": "test_g001_remaining_witness_solver.cpp",
        }
        for binary, source in targets.items():
            _run([compiler] + COMPILE_FLAGS + [str(source_dir / source), "-o", str(bin_dir / binary)],
                 source_dir, logs / f"compile_{binary}.stdout.txt",
                 logs / f"compile_{binary}.stderr.txt")
            os.chmod(bin_dir / binary, 0o555)
        _run([str(bin_dir / "test_g001_remaining_witness_solver")], source_dir,
             logs / "witness_regression.stdout.txt", logs / "witness_regression.stderr.txt")
        if common.read_regular(logs / "witness_regression.stdout.txt", "witness test stdout") != \
                b"PASS test_g001_remaining_witness_solver checks=45\n" or \
                common.read_regular(logs / "witness_regression.stderr.txt", "witness test stderr"):
            raise common.TerminalError("terminal solver regression marker mismatch")
        _run([str(bin_dir / "check_g001_leech_witness"), "--self-test"], source_dir,
             logs / "checker_self_test.stdout.txt", logs / "checker_self_test.stderr.txt")
        if common.read_regular(logs / "checker_self_test.stdout.txt", "checker stdout") != \
                b"SELF_TEST PASS checks=11\n" or \
                common.read_regular(logs / "checker_self_test.stderr.txt", "checker stderr"):
            raise common.TerminalError("independent checker self-test marker mismatch")
        binaries = {
            name: {"path": f"bin/{name}", "sha256": common.sha256_file(bin_dir / name)}
            for name in sorted(targets)
        }
        freeze = {
            "schema": RUNTIME_SCHEMA,
            "source_relative_to_workspace": source_relative,
            "runtime_relative_to_workspace": output.relative_to(workspace_root).as_posix(),
            "scientific_core_matches_calibration": True,
            "calibration_solver_sha256": "bce4c2766fb9aedc942aaca7127eafac5c983e552d61266d882b87f2260f1147",
            "sources": {name: {"path": f"{source_relative}/{name}", "sha256": digest}
                        for name, digest in sorted(SOURCE_HASHES.items())},
            "compiler": {"path": compiler, "version_sha256": common.sha256_bytes(version.stdout)},
            "compile_flags": list(COMPILE_FLAGS),
            "binaries": binaries,
            "tests": {"witness_regression_checks": 45, "checker_self_test_checks": 11},
            "terminal_policy": {
                "node_cap": None, "depth_cap": None, "stop_depth": None,
                "witness_required_before_found_exit": True,
                "independent_checker_required": True,
            },
        }
        _write_new(private / "runtime_freeze.json", common.canonical_json(freeze))
        manifest_lines = []
        for path in sorted(item for item in private.rglob("*") if item.is_file()):
            if path.name == "runtime_artifacts.sha256":
                continue
            manifest_lines.append(f"{common.sha256_file(path)}  {path.relative_to(private).as_posix()}\n")
        _write_new(private / "runtime_artifacts.sha256", "".join(manifest_lines).encode("ascii"))
        os.rename(private, output)
        private = None
    finally:
        if private is not None and private.exists():
            shutil.rmtree(private, ignore_errors=True)
    return freeze


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-dir", type=Path, required=True)
    parser.add_argument("--workspace-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--cxx", default="g++")
    args = parser.parse_args(argv)
    try:
        freeze = build(args.source_dir, args.workspace_root, args.output, args.cxx)
        print("G001_TERMINAL5_RUNTIME_V1_OK solver_sha256={} checker_sha256={}".format(
            freeze["binaries"]["g001_remaining_witness_solver"]["sha256"],
            freeze["binaries"]["check_g001_leech_witness"]["sha256"]))
        return 0
    except (common.TerminalError, OSError, subprocess.SubprocessError, ValueError) as error:
        print(f"G001_TERMINAL5_RUNTIME_V1_FAILED: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
