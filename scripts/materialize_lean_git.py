#!/usr/bin/env python3
"""Materialize pinned nested Git metadata without changing Lean source bytes."""

from __future__ import annotations

import hashlib
import os
import shutil
import subprocess
import sys
import uuid
from pathlib import Path


COMMIT = "2747de53478568e580e364ddc685871d55dc6e7e"
BUNDLE_NAME = f"LeechTrees-{COMMIT}.bundle"
BUNDLE_SHA256 = "2959021161bd8d58f79e6468a6841bcfae8081a3b93cb1cc1f883fd8b6dc3e96"


class MaterializeError(RuntimeError):
    pass


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def run(argv: list[str], *, cwd: Path | None = None) -> bytes:
    result = subprocess.run(
        argv,
        cwd=cwd,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if result.returncode != 0:
        raise MaterializeError(
            f"command failed ({result.returncode}): {argv!r}\n"
            + result.stderr.decode("utf-8", errors="replace")
        )
    return result.stdout


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    target = root / "lean" / "LeechTrees"
    bundle = root / "repository_support" / BUNDLE_NAME
    git_dir = target / ".git"

    if not target.is_dir() or target.is_symlink():
        raise MaterializeError(f"missing or unsafe Lean source directory: {target}")
    if not bundle.is_file() or bundle.is_symlink():
        raise MaterializeError(f"missing or unsafe Git bundle: {bundle}")
    actual = sha256_file(bundle)
    if actual != BUNDLE_SHA256:
        raise MaterializeError(
            f"Git bundle SHA-256 mismatch: expected {BUNDLE_SHA256}, got {actual}"
        )

    if git_dir.exists():
        head = run(["git", "rev-parse", "HEAD"], cwd=target).decode("ascii").strip()
        status = run(["git", "status", "--porcelain"], cwd=target)
        if head != COMMIT or status:
            raise MaterializeError(
                f"existing nested Git state is not the clean pinned commit: {head}"
            )
        print(f"LEECH18_LEAN_GIT_ALREADY_OK commit={COMMIT}")
        return 0

    support = root / "repository_support"
    temporary = support / f".materialize-{os.getpid()}-{uuid.uuid4().hex}"
    try:
        run(["git", "init", "--bare", str(temporary)])
        run(["git", "--git-dir", str(temporary), "fetch", "--no-tags", str(bundle), "HEAD"])
        fetched = run(
            ["git", "--git-dir", str(temporary), "rev-parse", "FETCH_HEAD"]
        ).decode("ascii").strip()
        if fetched != COMMIT:
            raise MaterializeError(f"bundle resolved to unexpected commit: {fetched}")
        run(["git", "--git-dir", str(temporary), "update-ref", "refs/heads/main", COMMIT])
        run(["git", "--git-dir", str(temporary), "symbolic-ref", "HEAD", "refs/heads/main"])
        run(["git", "--git-dir", str(temporary), "config", "core.bare", "false"])
        run(["git", "--git-dir", str(temporary), "config", "core.worktree", ".."])
        run(["git", "--git-dir", str(temporary), "read-tree", COMMIT])
        status = run(
            [
                "git",
                "--git-dir",
                str(temporary),
                "--work-tree",
                str(target),
                "status",
                "--porcelain",
            ]
        )
        if status:
            raise MaterializeError(
                "vendored Lean source differs from the pinned Git tree:\n"
                + status.decode("utf-8", errors="replace")
            )
        os.rename(temporary, git_dir)
        temporary = None
    finally:
        if temporary is not None and temporary.exists():
            shutil.rmtree(temporary)

    head = run(["git", "rev-parse", "HEAD"], cwd=target).decode("ascii").strip()
    status = run(["git", "status", "--porcelain"], cwd=target)
    if head != COMMIT or status:
        raise MaterializeError("post-materialization Git check failed")
    print(f"LEECH18_LEAN_GIT_MATERIALIZED commit={COMMIT} bundle_sha256={BUNDLE_SHA256}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (MaterializeError, OSError, subprocess.SubprocessError) as error:
        print(f"LEECH18_LEAN_GIT_MATERIALIZE_FAIL: {error}", file=sys.stderr)
        raise SystemExit(1)
