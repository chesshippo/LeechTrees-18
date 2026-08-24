#!/usr/bin/env python3
"""Verify the external freeze, checksum, exact set, and static launch policy."""

from __future__ import annotations

import argparse
import os
import stat
import sys
from pathlib import Path
from typing import Dict, Optional, Sequence

# A clean external verification must not modify the frozen directory merely by
# importing the two local helper modules below.  Pre-existing cache files still
# fail the exact-set gate; this only prevents the verifier from creating them.
sys.dont_write_bytecode = True

import g001_terminal5_common_v1 as common
import make_g001_terminal5_source_freeze_v1 as maker


def parse_checksums(raw: bytes) -> Dict[str, str]:
    try:
        text = raw.decode("ascii", errors="strict")
    except UnicodeError as error:
        raise common.TerminalError("source checksum is not ASCII") from error
    result: Dict[str, str] = {}
    for line in text.splitlines():
        parts = line.split("  ")
        if (len(parts) != 2 or not common.HEX64.fullmatch(parts[0]) or
                Path(parts[1]).is_absolute() or ".." in Path(parts[1]).parts or
                parts[1] in result):
            raise common.TerminalError("malformed/duplicate checksum line")
        result[Path(parts[1]).as_posix()] = parts[0]
    return result


def verify(source_dir: Path) -> dict:
    source_dir = common.require_directory(source_dir, "frozen source directory")
    expected_set = set(maker.DISTRIBUTION_FILES) | {maker.FREEZE_NAME, maker.CHECKSUM_NAME}
    observed = set()
    for item in source_dir.rglob("*"):
        info = item.lstat()
        if stat.S_ISLNK(info.st_mode):
            raise common.TerminalError("frozen source contains a symlink")
        if stat.S_ISDIR(info.st_mode):
            continue
        if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1:
            raise common.TerminalError("frozen source contains a non-regular/single-link entry")
        observed.add(item.relative_to(source_dir).as_posix())
    if observed != expected_set:
        raise common.TerminalError(
            f"frozen source exact-set mismatch missing={sorted(expected_set-observed)} extra={sorted(observed-expected_set)}")
    freeze_raw = common.read_regular(source_dir / maker.FREEZE_NAME, "source freeze")
    freeze = common.strict_json(freeze_raw, "source freeze")
    expected = maker.make(source_dir)
    if freeze != expected:
        raise common.TerminalError("source freeze content/hash map mismatch")
    checksum_raw = common.read_regular(source_dir / maker.CHECKSUM_NAME, "source checksum")
    checksums = parse_checksums(checksum_raw)
    expected_checksums = set(maker.DISTRIBUTION_FILES) | {maker.FREEZE_NAME}
    if set(checksums) != expected_checksums:
        raise common.TerminalError("source checksum exact-set mismatch")
    for name, digest in checksums.items():
        if common.sha256_file(source_dir / name) != digest:
            raise common.TerminalError(f"source checksum mismatch: {name}")
    # Freeze/checksum are generated only after this test file and every launch
    # wrapper are stable, so these static policy checks are externally bound.
    wrapper_expectations = {
        "g001_terminal5_devel_smoke_v1.sbatch": ("--partition=devel", "--array=0-3%4"),
        "g001_terminal5_mi2101x_canary_v1.sbatch": ("--partition=mi2101x", "--array=0-1%2"),
        "g001_terminal5_mi2101x_full_v1.sbatch": ("--partition=mi2101x", "--array=0-191%24"),
    }
    for name, markers in wrapper_expectations.items():
        text = common.read_regular(source_dir / name, name).decode("utf-8", errors="strict")
        if ("--cpus-per-task=16" not in text or "--workers 15" not in text or
                "export PYTHONDONTWRITEBYTECODE=1" not in text or
                text.count("python3 -B ") != 2 or
                any(marker not in text for marker in markers) or
                "--stop-edges" in text or "--max-nodes" in text):
            raise common.TerminalError(f"Slurm wrapper policy mismatch: {name}")
    return {
        "schema": "G001_TERMINAL5_SOURCE_FREEZE_AUDIT_V1",
        "freeze_sha256": common.sha256_bytes(freeze_raw),
        "checksum_sha256": common.sha256_bytes(checksum_raw),
        "distribution_files": len(maker.DISTRIBUTION_FILES),
        "exact_set": True,
        "terminal_search_performed": False,
    }


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-dir", type=Path, default=Path(__file__).parent)
    args = parser.parse_args(argv)
    try:
        report = verify(args.source_dir)
        print("G001_TERMINAL5_SOURCE_FREEZE_V1_OK files={} freeze_sha256={} checksum_sha256={}".format(
            report["distribution_files"], report["freeze_sha256"], report["checksum_sha256"]))
        return 0
    except (common.TerminalError, OSError, ValueError, KeyError) as error:
        print(f"G001_TERMINAL5_SOURCE_FREEZE_V1_VERIFY_FAILED: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
