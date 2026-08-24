#!/usr/bin/env python3
"""Hash-check and safely install the complete evidence release asset."""

from __future__ import annotations

import argparse
import hashlib
import os
import shutil
import sys
import tarfile
import uuid
from pathlib import Path, PurePosixPath


ARCHIVE_NAME = "leech18_full_extracted_tree_repacked_20260820.tar.gz"
ARCHIVE_SIZE = 826_575_460
ARCHIVE_SHA256 = "69bc248cf9688b8d273983068249e7e91c9a5cde5a42488f21f2569cd7904f87"
ARCHIVE_MEMBERS = 991_377
ARCHIVE_REGULAR_FILES = 950_293
ARCHIVE_DIRECTORIES = 41_083
ARCHIVE_HARDLINKS = 1
TOP_LEVEL = "leech18_remaining5_pilot_20260817_v1_FULL_BACKUP_20260819"
PAYLOAD_LEVEL = "leech18_remaining5_pilot_20260817_v1"
HARDLINK_MEMBER = (
    TOP_LEVEL
    + "/leech18_remaining5_pilot_20260817_v1/results/"
    "leaf_pipeline_selftest_20260817_02ba606efe0f48f79e2d1decc0a04611/"
    "hardlink_fsync_probe.partial"
)
HARDLINK_TARGET = (
    TOP_LEVEL
    + "/leech18_remaining5_pilot_20260817_v1/results/"
    "leaf_pipeline_selftest_20260817_02ba606efe0f48f79e2d1decc0a04611/"
    "hardlink_fsync_probe.final"
)


class InstallError(RuntimeError):
    pass


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def is_link_or_junction(path: Path) -> bool:
    return path.is_symlink() or bool(
        getattr(os.path, "isjunction", lambda _path: False)(path)
    )


def safe_archive_name(raw_name: str, label: str) -> PurePosixPath:
    if "\x00" in raw_name or "\\" in raw_name:
        raise InstallError(f"{label} has unsafe spelling: {raw_name!r}")
    name = PurePosixPath(raw_name)
    if name.is_absolute() or not name.parts or name.parts[0] != TOP_LEVEL:
        raise InstallError(f"{label} has unexpected root: {raw_name!r}")
    if any(part in ("", ".", "..") for part in name.parts):
        raise InstallError(f"{label} has unsafe path: {raw_name!r}")
    canonical = name.as_posix()
    if raw_name.rstrip("/") != canonical or "//" in raw_name:
        raise InstallError(f"{label} is not canonical: {raw_name!r}")
    if os.name == "nt" and any(
        ":" in part or part.endswith((".", " ")) for part in name.parts
    ):
        raise InstallError(f"{label} is unsafe on Windows: {raw_name!r}")
    return name


def safe_member(member: tarfile.TarInfo) -> str:
    safe_archive_name(member.name, "archive member")
    if member.isfile():
        return "regular"
    if member.isdir():
        return "directory"
    if member.islnk():
        safe_archive_name(member.linkname, "archive hardlink target")
        if member.name != HARDLINK_MEMBER or member.linkname != HARDLINK_TARGET:
            raise InstallError(
                "archive contains an unexpected hardlink: "
                f"{member.name!r} -> {member.linkname!r}"
            )
        return "hardlink"
    raise InstallError(f"archive member has forbidden type: {member.name!r}")


def require_archive_counts(counts: dict[str, int]) -> None:
    expected = {
        "regular": ARCHIVE_REGULAR_FILES,
        "directory": ARCHIVE_DIRECTORIES,
        "hardlink": ARCHIVE_HARDLINKS,
    }
    if counts != expected or sum(counts.values()) != ARCHIVE_MEMBERS:
        raise InstallError(
            f"archive member-count mismatch: expected {expected!r}, got {counts!r}"
        )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", required=True, type=Path)
    parser.add_argument("--repo-root", type=Path)
    parser.add_argument(
        "--verify-only",
        action="store_true",
        help="scan every archive member without writing the evidence tree",
    )
    args = parser.parse_args(argv)

    if sys.version_info < (3, 12):
        raise InstallError("Python 3.12 or newer is required for filtered extraction")
    root = (args.repo_root or Path(__file__).resolve().parents[1]).resolve(strict=True)
    archive_input = Path(os.path.abspath(os.fspath(args.archive)))
    if not archive_input.is_file() or is_link_or_junction(archive_input):
        raise InstallError(f"archive is not a regular unlinked file: {archive_input}")
    archive = archive_input.resolve(strict=True)
    size = archive.stat().st_size
    if size != ARCHIVE_SIZE:
        raise InstallError(f"archive size mismatch: expected {ARCHIVE_SIZE}, got {size}")
    digest = sha256_file(archive)
    if digest != ARCHIVE_SHA256:
        raise InstallError(
            f"archive SHA-256 mismatch: expected {ARCHIVE_SHA256}, got {digest}"
        )

    if args.verify_only:
        counts = {"regular": 0, "directory": 0, "hardlink": 0}
        with tarfile.open(archive, "r:gz") as package:
            for member in package:
                counts[safe_member(member)] += 1
        require_archive_counts(counts)
        print(
            "LEECH18_EVIDENCE_ARCHIVE_OK "
            f"members={ARCHIVE_MEMBERS} files={ARCHIVE_REGULAR_FILES + ARCHIVE_HARDLINKS} "
            f"directories={ARCHIVE_DIRECTORIES} hardlinks={ARCHIVE_HARDLINKS} "
            f"bytes={ARCHIVE_SIZE} sha256={ARCHIVE_SHA256}"
        )
        return 0

    evidence = root / "computation" / "evidence"
    if not evidence.is_dir() or is_link_or_junction(evidence):
        raise InstallError(f"missing or unsafe evidence directory: {evidence}")
    destination = evidence / "full"
    if os.path.lexists(destination):
        raise InstallError(f"refusing to overwrite existing evidence: {destination}")

    temporary = evidence / f".evidence-install-{os.getpid()}-{uuid.uuid4().hex}"
    temporary.mkdir(mode=0o700)
    counts = {"regular": 0, "directory": 0, "hardlink": 0}
    try:
        with tarfile.open(archive, "r:gz") as package:
            for member in package:
                kind = safe_member(member)
                package.extract(member, path=temporary, filter="data")
                counts[kind] += 1
        require_archive_counts(counts)
        wrapper = temporary / TOP_LEVEL
        if not wrapper.is_dir() or is_link_or_junction(wrapper):
            raise InstallError("archive did not create the expected top-level directory")
        payload = wrapper / PAYLOAD_LEVEL
        if not payload.is_dir() or is_link_or_junction(payload):
            raise InstallError("archive did not create the expected evidence payload")
        if sorted(path.name for path in wrapper.iterdir()) != [PAYLOAD_LEVEL]:
            raise InstallError("archive wrapper contains an unexpected entry")
        os.rename(payload, destination)
        wrapper.rmdir()
        temporary.rmdir()
        temporary = None
    finally:
        if temporary is not None and temporary.exists():
            shutil.rmtree(temporary)

    print(
        "LEECH18_EVIDENCE_INSTALLED "
        f"members={ARCHIVE_MEMBERS} files={ARCHIVE_REGULAR_FILES + ARCHIVE_HARDLINKS} "
        f"directories={ARCHIVE_DIRECTORIES} hardlinks={ARCHIVE_HARDLINKS} "
        f"bytes={ARCHIVE_SIZE} sha256={ARCHIVE_SHA256}"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (InstallError, OSError, tarfile.TarError) as error:
        print(f"LEECH18_EVIDENCE_INSTALL_FAIL: {error}", file=sys.stderr)
        raise SystemExit(1)
