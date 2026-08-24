#!/usr/bin/env python3
"""Write or verify the SHA-256 manifest for Git-resident repository files."""

from __future__ import annotations

import argparse
import hashlib
import os
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess
import sys


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
MANIFEST_PATH = REPOSITORY_ROOT / "MANIFEST.sha256"
LINE_PATTERN = re.compile(r"([0-9a-f]{64})  ([!-~]+)")


def fail(message: str) -> "NoReturn":
    raise SystemExit(f"LEECH18_REPOSITORY_MANIFEST_ERROR {message}")


def filesystem_path(path: Path) -> Path:
    """Use the extended Windows namespace for preserved long filenames."""
    if os.name != "nt":
        return path
    absolute = os.path.abspath(os.fspath(path))
    if absolute.startswith("\\\\?\\"):
        return Path(absolute)
    if absolute.startswith("\\\\"):
        return Path("\\\\?\\UNC\\" + absolute[2:])
    return Path("\\\\?\\" + absolute)


def git_inventory() -> list[str]:
    completed = subprocess.run(
        [
            "git",
            "-C",
            os.fspath(REPOSITORY_ROOT),
            "ls-files",
            "-z",
            "--cached",
            "--others",
            "--exclude-standard",
        ],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if completed.returncode != 0:
        fail(
            "git inventory failed: "
            + completed.stderr.decode("utf-8", errors="replace").strip()
        )

    try:
        decoded = completed.stdout.decode("utf-8")
    except UnicodeDecodeError as error:
        fail(f"non-UTF-8 Git path: {error}")

    paths: list[str] = []
    seen: set[str] = set()
    for raw in decoded.split("\0"):
        if not raw or raw == MANIFEST_PATH.name:
            continue
        if raw in seen:
            fail(f"duplicate Git path: {raw}")
        if raw != PurePosixPath(raw).as_posix() or PurePosixPath(raw).is_absolute():
            fail(f"unsafe Git path: {raw}")
        if ".." in PurePosixPath(raw).parts or not raw.isascii():
            fail(f"unsafe or non-ASCII Git path: {raw}")

        absolute = filesystem_path(
            REPOSITORY_ROOT.joinpath(*PurePosixPath(raw).parts)
        )
        try:
            metadata = absolute.lstat()
        except FileNotFoundError:
            fail(f"Git-resident file is absent: {raw}")
        if stat.S_ISLNK(metadata.st_mode):
            fail(f"symbolic link is not allowed: {raw}")
        if not stat.S_ISREG(metadata.st_mode):
            fail(f"Git inventory entry is not a regular file: {raw}")
        seen.add(raw)
        paths.append(raw)

    return sorted(paths)


def digest(relative: str) -> str:
    hasher = hashlib.sha256()
    path = filesystem_path(
        REPOSITORY_ROOT.joinpath(*PurePosixPath(relative).parts)
    )
    with path.open("rb") as stream:
        while block := stream.read(1024 * 1024):
            hasher.update(block)
    return hasher.hexdigest()


def write_manifest() -> None:
    paths = git_inventory()
    lines = [f"{digest(relative)}  {relative}" for relative in paths]
    MANIFEST_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
    manifest_hash = hashlib.sha256(MANIFEST_PATH.read_bytes()).hexdigest()
    print(
        "LEECH18_REPOSITORY_MANIFEST_WRITTEN "
        f"files={len(paths)} manifest_sha256={manifest_hash}"
    )


def read_manifest() -> dict[str, str]:
    try:
        text = MANIFEST_PATH.read_text(encoding="utf-8")
    except FileNotFoundError:
        fail("MANIFEST.sha256 is absent")
    if not text.endswith("\n"):
        fail("manifest has no final newline")

    expected: dict[str, str] = {}
    prior = ""
    for number, line in enumerate(text.splitlines(), 1):
        match = LINE_PATTERN.fullmatch(line)
        if match is None:
            fail(f"malformed line {number}")
        expected_hash, relative = match.groups()
        if relative in expected:
            fail(f"duplicate manifest path: {relative}")
        if prior and relative <= prior:
            fail(f"manifest paths are not strictly sorted at line {number}")
        prior = relative
        expected[relative] = expected_hash
    return expected


def verify_manifest() -> None:
    expected = read_manifest()
    actual_paths = git_inventory()
    expected_paths = sorted(expected)
    if expected_paths != actual_paths:
        missing = sorted(set(expected_paths) - set(actual_paths))
        extra = sorted(set(actual_paths) - set(expected_paths))
        fail(f"file-set mismatch missing={missing!r} extra={extra!r}")

    for relative in actual_paths:
        actual_hash = digest(relative)
        if actual_hash != expected[relative]:
            fail(
                f"hash mismatch path={relative} "
                f"expected={expected[relative]} actual={actual_hash}"
            )

    manifest_hash = hashlib.sha256(MANIFEST_PATH.read_bytes()).hexdigest()
    print(
        "LEECH18_REPOSITORY_MANIFEST_OK "
        f"files={len(actual_paths)} manifest_sha256={manifest_hash}"
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--write",
        action="store_true",
        help="replace MANIFEST.sha256 with the current Git-resident inventory",
    )
    arguments = parser.parse_args()
    if arguments.write:
        write_manifest()
    else:
        verify_manifest()
    return 0


if __name__ == "__main__":
    sys.exit(main())
