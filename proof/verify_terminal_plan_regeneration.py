#!/usr/bin/env python3
"""Compare a regenerated Terminal5 plan tree with the pinned frozen tree."""

from __future__ import annotations

import argparse
import hashlib
import os
import re
import stat
import sys
from pathlib import Path
from typing import Sequence


HEX64 = re.compile(r"[0-9a-f]{64}")
PLAN_NAME = "terminal_plan_v1.json"
MANIFEST_NAME = "plan_artifacts.sha256"
RECEIPT_NAME = "plan_receipt.json"
BUNDLE_COUNT = 192
EXPECTED_FILES = {
    PLAN_NAME,
    MANIFEST_NAME,
    RECEIPT_NAME,
    *(f"bundle_plans/bundle_{index:03d}.json" for index in range(BUNDLE_COUNT)),
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


def require_plain_directory_ancestry(path: Path, label: str) -> Path:
    target = Path(os.path.abspath(os.fspath(path)))
    for directory in reversed((target, *target.parents)):
        require_plain_directory(directory, f"{label} ancestry")
    try:
        resolved = target.resolve(strict=True)
        resolved.relative_to(Path(target.anchor).resolve(strict=True))
    except (OSError, ValueError) as exc:
        raise CheckError(f"cannot safely resolve {label}: {target}: {exc}") from exc
    return target


def inventory_tree(root: Path, label: str) -> tuple[dict[str, Path], set[str]]:
    """Inventory a tree without following links or accepting special files."""
    pending = [root]
    files: dict[str, Path] = {}
    directories: set[str] = set()
    while pending:
        directory = pending.pop()
        require_plain_directory(directory, label)
        try:
            entries = sorted(os.scandir(directory), key=lambda item: item.name)
        except OSError as exc:
            raise CheckError(f"cannot enumerate {label}: {directory}: {exc}") from exc
        for entry in entries:
            path = Path(entry.path)
            try:
                info = path.lstat()
            except OSError as exc:
                raise CheckError(f"cannot inspect {label} entry: {path}: {exc}") from exc
            require(not is_link_like(path), f"{label} contains a link: {path}")
            if stat.S_ISDIR(info.st_mode):
                relative = path.relative_to(root).as_posix()
                directories.add(relative)
                pending.append(path)
            elif stat.S_ISREG(info.st_mode):
                require(info.st_nlink == 1, f"{label} contains a hard-linked file: {path}")
                relative = path.relative_to(root).as_posix()
                files[relative] = path
            else:
                raise CheckError(f"{label} contains a special file: {path}")
    return files, directories


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def equal_bytes(left: Path, right: Path) -> bool:
    if left.stat().st_size != right.stat().st_size:
        return False
    with left.open("rb") as left_stream, right.open("rb") as right_stream:
        while True:
            left_block = left_stream.read(1024 * 1024)
            right_block = right_stream.read(1024 * 1024)
            if left_block != right_block:
                return False
            if not left_block:
                return True


def checked_digest(value: str, label: str) -> str:
    require(HEX64.fullmatch(value) is not None, f"malformed {label} SHA-256")
    return value


def compare(
    frozen: Path,
    regenerated: Path,
    plan_sha256: str,
    manifest_sha256: str,
    receipt_sha256: str,
) -> None:
    frozen = require_plain_directory_ancestry(frozen, "frozen plan tree")
    regenerated = require_plain_directory_ancestry(
        regenerated, "regenerated plan tree"
    )
    require(
        os.path.normcase(str(frozen)) != os.path.normcase(str(regenerated)),
        "frozen and regenerated plan directories are the same path",
    )
    require(
        not os.path.samefile(frozen, regenerated),
        "frozen and regenerated plan directories identify the same filesystem object",
    )
    expected_anchors = {
        PLAN_NAME: checked_digest(plan_sha256, "plan"),
        MANIFEST_NAME: checked_digest(manifest_sha256, "manifest"),
        RECEIPT_NAME: checked_digest(receipt_sha256, "receipt"),
    }
    frozen_files, frozen_directories = inventory_tree(frozen, "frozen plan tree")
    regenerated_files, regenerated_directories = inventory_tree(
        regenerated, "regenerated plan tree"
    )
    require(
        frozen_directories == {"bundle_plans"},
        "frozen plan tree does not have the exact production directory shape",
    )
    require(
        regenerated_directories == {"bundle_plans"},
        "regenerated plan tree does not have the exact production directory shape",
    )
    require(
        set(frozen_files) == EXPECTED_FILES,
        "frozen plan tree does not have the exact 195-file production shape",
    )
    require(
        set(regenerated_files) == EXPECTED_FILES,
        "regenerated plan tree does not have the exact 195-file production shape",
    )
    for relative, expected_digest in expected_anchors.items():
        actual = sha256_file(frozen_files[relative])
        require(actual == expected_digest, f"frozen {relative} SHA-256 mismatch: {actual}")
    compared_digests: dict[str, str] = {}
    for relative in sorted(EXPECTED_FILES):
        frozen_path = require_plain_file(frozen_files[relative], f"frozen {relative}")
        regenerated_path = require_plain_file(
            regenerated_files[relative], f"regenerated {relative}"
        )
        frozen_digest = sha256_file(frozen_path)
        regenerated_digest = sha256_file(regenerated_path)
        require(
            regenerated_digest == frozen_digest,
            f"regenerated {relative} SHA-256 mismatch: {regenerated_digest}",
        )
        compared_digests[relative] = frozen_digest
        require(
            equal_bytes(frozen_path, regenerated_path),
            f"regenerated {relative} differs byte-for-byte from the frozen plan",
        )
    final_frozen_files, final_frozen_directories = inventory_tree(
        frozen, "final frozen plan tree"
    )
    final_regenerated_files, final_regenerated_directories = inventory_tree(
        regenerated, "final regenerated plan tree"
    )
    require(
        final_frozen_directories == {"bundle_plans"}
        and final_regenerated_directories == {"bundle_plans"}
        and set(final_frozen_files) == EXPECTED_FILES
        and set(final_regenerated_files) == EXPECTED_FILES,
        "plan tree shape changed during comparison",
    )
    for relative in sorted(EXPECTED_FILES):
        expected_digest = compared_digests[relative]
        require(
            sha256_file(final_frozen_files[relative]) == expected_digest
            and sha256_file(final_regenerated_files[relative]) == expected_digest,
            f"plan file changed during comparison: {relative}",
        )


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--frozen", required=True, type=Path)
    parser.add_argument("--regenerated", required=True, type=Path)
    parser.add_argument("--plan-sha256", required=True)
    parser.add_argument("--manifest-sha256", required=True)
    parser.add_argument("--receipt-sha256", required=True)
    args = parser.parse_args(argv)
    try:
        require_plain_directory_ancestry(
            Path(__file__).absolute().parent,
            "terminal-plan comparator parent",
        )
        require_plain_file(
            Path(__file__).absolute(), "terminal-plan comparator"
        )
        compare(
            args.frozen,
            args.regenerated,
            args.plan_sha256,
            args.manifest_sha256,
            args.receipt_sha256,
        )
        print(
            "LEECH18_TERMINAL_PLAN_REGENERATION_OK "
            f"files={len(EXPECTED_FILES)} plan_sha256={args.plan_sha256}"
        )
        return 0
    except (CheckError, OSError, ValueError) as exc:
        print(f"LEECH18_TERMINAL_PLAN_REGENERATION_FAIL: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
