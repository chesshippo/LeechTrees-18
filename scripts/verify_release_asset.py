#!/usr/bin/env python3
"""Fail-closed size and SHA-256 check for the separate evidence release asset."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
ASSET_RECORD = REPOSITORY_ROOT / "release" / "EVIDENCE_ASSET.json"


def fail(message: str) -> "NoReturn":
    raise SystemExit(f"LEECH18_RELEASE_ASSET_ERROR {message}")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while block := stream.read(8 * 1024 * 1024):
            digest.update(block)
    return digest.hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument(
        "--require-published-record",
        action="store_true",
        help="also require a non-null release tag and HTTPS download URL",
    )
    arguments = parser.parse_args()

    try:
        record = json.loads(ASSET_RECORD.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        fail(f"cannot read {ASSET_RECORD}: {error}")

    if record.get("schema") != "LEECH18_PUBLIC_EVIDENCE_ASSET_V1":
        fail("unexpected asset-record schema")
    asset = record.get("asset")
    if not isinstance(asset, dict):
        fail("asset record has no object-valued asset field")

    archive = arguments.archive.resolve()
    if not archive.is_file():
        fail(f"archive is absent or not a regular file: {archive}")
    if archive.name != asset.get("filename"):
        fail(
            f"filename mismatch expected={asset.get('filename')!r} "
            f"actual={archive.name!r}"
        )

    size = archive.stat().st_size
    expected_size = asset.get("size_bytes")
    if size != expected_size:
        fail(f"size mismatch expected={expected_size!r} actual={size}")

    actual_hash = sha256(archive)
    expected_hash = asset.get("sha256")
    if actual_hash != expected_hash:
        fail(f"sha256 mismatch expected={expected_hash!r} actual={actual_hash}")

    tag = record.get("release_tag")
    url = record.get("download_url")
    if arguments.require_published_record:
        if not isinstance(tag, str) or not tag.strip():
            fail("published record has no release tag")
        if not isinstance(url, str) or not url.startswith("https://"):
            fail("published record has no HTTPS download URL")

    print(
        "LEECH18_RELEASE_ASSET_OK "
        f"filename={archive.name} size={size} sha256={actual_hash} "
        f"published_record={int(arguments.require_published_record)}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
