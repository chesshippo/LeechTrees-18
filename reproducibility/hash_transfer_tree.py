#!/usr/bin/env python3
"""Create or verify a relocatable SHA-256 manifest for one transfer tree."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
from pathlib import Path, PurePosixPath
from typing import Any, Iterable


SCHEMA = "LEECH18_TRANSFER_TREE_MANIFEST_V1"


class TransferError(RuntimeError):
    pass


def canonical_json(value: Any) -> bytes:
    return (json.dumps(value, ensure_ascii=True, separators=(",", ":"), sort_keys=True) + "\n").encode("ascii")


def reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise TransferError(f"duplicate JSON key: {key!r}")
        result[key] = value
    return result


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


def safe_relative(path: Path, root: Path) -> str:
    relative = path.relative_to(root)
    value = PurePosixPath(*relative.parts).as_posix()
    if not value or value == "." or any(part in ("", ".", "..") for part in PurePosixPath(value).parts):
        raise TransferError(f"unsafe relative path: {value!r}")
    return value


def inventory(root: Path) -> list[dict[str, Any]]:
    if not root.is_dir() or is_link_or_junction(root):
        raise TransferError(f"root is not a regular directory: {root}")
    records: list[dict[str, Any]] = []
    for current, directories, files in os.walk(root, topdown=True, followlinks=False):
        current_path = Path(current)
        for name in directories:
            path = current_path / name
            if is_link_or_junction(path):
                raise TransferError(f"directory link is forbidden: {safe_relative(path, root)}")
        for name in files:
            path = current_path / name
            relative = safe_relative(path, root)
            if is_link_or_junction(path) or not path.is_file():
                raise TransferError(f"non-regular file is forbidden: {relative}")
            records.append({"path": relative, "bytes": path.stat().st_size, "sha256": sha256_file(path)})
    records.sort(key=lambda item: item["path"].encode("utf-8"))
    if len({item["path"] for item in records}) != len(records):
        raise TransferError("duplicate normalized path")
    return records


def roster_sha256(records: Iterable[dict[str, Any]]) -> str:
    digest = hashlib.sha256()
    for item in records:
        digest.update(f"{item['sha256']}  {item['bytes']}  {item['path']}\n".encode("utf-8"))
    return digest.hexdigest()


def make_manifest(root: Path) -> dict[str, Any]:
    records = inventory(root)
    return {
        "schema": SCHEMA,
        "files": records,
        "file_count": len(records),
        "total_bytes": sum(item["bytes"] for item in records),
        "roster_sha256": roster_sha256(records),
    }


def strict_manifest(path: Path) -> dict[str, Any]:
    if not path.is_file() or is_link_or_junction(path):
        raise TransferError(f"manifest is missing or linked: {path}")
    try:
        value = json.loads(path.read_text(encoding="ascii"), object_pairs_hook=reject_duplicate_keys)
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise TransferError(f"cannot read strict manifest: {error}") from error
    if not isinstance(value, dict) or value.get("schema") != SCHEMA:
        raise TransferError("unexpected manifest schema")
    if set(value) != {"schema", "files", "file_count", "total_bytes", "roster_sha256"}:
        raise TransferError("unexpected manifest field set")
    return value


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--create", metavar="ROOT", type=Path)
    mode.add_argument("--verify", metavar="ROOT", type=Path)
    parser.add_argument("--manifest", required=True, type=Path)
    args = parser.parse_args(argv)
    try:
        root = (args.create or args.verify).resolve(strict=True)
        if args.create is not None:
            manifest = make_manifest(root)
            output = Path(os.path.abspath(os.fspath(args.manifest)))
            if os.path.lexists(output):
                raise TransferError(f"refusing to overwrite manifest: {output}")
            if not output.parent.is_dir():
                raise TransferError(f"manifest parent directory is missing: {output.parent}")
            try:
                output.relative_to(root)
            except ValueError:
                pass
            else:
                raise TransferError("manifest output must be outside the tree it describes")
            with output.open("xb") as stream:
                stream.write(canonical_json(manifest))
            action = "CREATED"
        else:
            expected = strict_manifest(args.manifest)
            actual = make_manifest(root)
            if actual != expected:
                raise TransferError("transfer tree does not match manifest")
            manifest = actual
            action = "VERIFIED"
        print(
            f"LEECH18_TRANSFER_TREE_{action} files={manifest['file_count']} "
            f"bytes={manifest['total_bytes']} roster_sha256={manifest['roster_sha256']}"
        )
        return 0
    except (TransferError, OSError, ValueError) as error:
        print(f"LEECH18_TRANSFER_TREE_FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
