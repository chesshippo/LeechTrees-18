#!/usr/bin/env python3
"""Read-only consistency checks for the public LeechTrees snapshot."""

from __future__ import annotations

import csv
import hashlib
import json
import re
import sys
from collections import Counter
from pathlib import Path, PurePosixPath


ROOT = Path(__file__).resolve().parents[1]
VALIDATION = ROOT / "evidence" / "validation"
RESULTS = ROOT / "results"


class VerificationError(Exception):
    pass


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def read_tsv(path: Path, expected_header: list[str]) -> list[dict[str, str]]:
    raw = path.read_bytes()
    if raw.startswith(b"\xef\xbb\xbf"):
        raise VerificationError(f"{path.relative_to(ROOT)} has a UTF-8 BOM")
    if b"\r" in raw:
        raise VerificationError(f"{path.relative_to(ROOT)} is not LF-only")
    text = raw.decode("utf-8", errors="strict")
    reader = csv.DictReader(text.splitlines(), delimiter="\t")
    if reader.fieldnames != expected_header:
        raise VerificationError(
            f"{path.relative_to(ROOT)} header {reader.fieldnames!r} "
            f"!= {expected_header!r}"
        )
    return list(reader)


def safe_repo_path(value: str) -> Path:
    posix = PurePosixPath(value)
    if posix.is_absolute() or ".." in posix.parts or not posix.parts:
        raise VerificationError(f"unsafe repository path: {value!r}")
    path = ROOT.joinpath(*posix.parts)
    try:
        path.resolve().relative_to(ROOT.resolve())
    except ValueError as exc:
        raise VerificationError(f"path escapes repository: {value!r}") from exc
    return path


def expect_unique(values: list[str], label: str) -> None:
    duplicates = [value for value, count in Counter(values).items() if count != 1]
    if duplicates:
        raise VerificationError(f"{label} has duplicate values: {duplicates[:5]!r}")


def verify_inputs() -> tuple[list[dict[str, str]], set[str]]:
    rows = read_tsv(
        VALIDATION / "PRE_VALIDATION_INPUTS.tsv", ["path", "bytes", "sha256"]
    )
    if len(rows) != 75:
        raise VerificationError(f"validated input count is {len(rows)}, expected 75")
    paths = [row["path"] for row in rows]
    expect_unique(paths, "validated inputs")
    lean_paths: set[str] = set()
    for row in rows:
        path = safe_repo_path(row["path"])
        if not path.is_file():
            raise VerificationError(f"missing validated input: {row['path']}")
        actual_bytes = path.stat().st_size
        try:
            expected_bytes = int(row["bytes"])
        except ValueError as exc:
            raise VerificationError(f"invalid byte count for {row['path']}") from exc
        if actual_bytes != expected_bytes:
            raise VerificationError(
                f"byte mismatch for {row['path']}: {actual_bytes} != {expected_bytes}"
            )
        actual_hash = sha256(path)
        if actual_hash != row["sha256"].lower():
            raise VerificationError(
                f"SHA-256 mismatch for {row['path']}: {actual_hash}"
            )
        if row["path"].endswith(".lean"):
            lean_paths.add(row["path"])
    if len(lean_paths) != 72:
        raise VerificationError(f"Lean input count is {len(lean_paths)}, expected 72")
    return rows, lean_paths


def verify_module_order(lean_paths: set[str]) -> None:
    rows = read_tsv(
        VALIDATION / "MODULE_ORDER.tsv",
        ["order", "kind", "module", "source", "fresh_output"],
    )
    if len(rows) != 72:
        raise VerificationError(f"module order has {len(rows)} rows, expected 72")
    orders = [int(row["order"]) for row in rows]
    if orders != list(range(1, 73)):
        raise VerificationError("module order is not contiguous 1..72")
    sources = [row["source"] for row in rows]
    expect_unique(sources, "module order sources")
    if set(sources) != lean_paths:
        missing = sorted(lean_paths - set(sources))
        extra = sorted(set(sources) - lean_paths)
        raise VerificationError(
            f"module order/source ledger differs; missing={missing}, extra={extra}"
        )


def verify_axioms() -> set[str]:
    expected = read_tsv(
        VALIDATION / "EXPECTED_AXIOM_QUERIES.tsv", ["order", "declaration"]
    )
    observed = read_tsv(
        VALIDATION / "AXIOM_RESULTS.tsv", ["order", "declaration", "axioms"]
    )
    if len(expected) != 350 or len(observed) != 350:
        raise VerificationError(
            f"axiom row counts are {len(expected)}/{len(observed)}, expected 350/350"
        )
    expected_pairs = [(row["order"], row["declaration"]) for row in expected]
    observed_pairs = [(row["order"], row["declaration"]) for row in observed]
    if expected_pairs != observed_pairs:
        raise VerificationError("expected and observed axiom query orders differ")
    if [int(row["order"]) for row in expected] != list(range(1, 351)):
        raise VerificationError("axiom query order is not contiguous 1..350")
    declarations = [row["declaration"] for row in expected]
    expect_unique(declarations, "axiom declarations")

    allowed = {"propext", "Classical.choice", "Quot.sound"}
    distribution = Counter({"<none>": 0, **{name: 0 for name in allowed}})
    for row in observed:
        names = set(filter(None, row["axioms"].split(",")))
        unexpected = names - allowed
        if unexpected:
            raise VerificationError(
                f"unexpected axiom(s) for {row['declaration']}: {sorted(unexpected)}"
            )
        if not names:
            distribution["<none>"] += 1
        for name in names:
            distribution[name] += 1
    required = {
        "<none>": 6,
        "propext": 344,
        "Classical.choice": 342,
        "Quot.sound": 343,
    }
    if dict(distribution) != required:
        raise VerificationError(
            f"axiom distribution {dict(distribution)!r} != {required!r}"
        )
    return set(declarations)


def verify_claim_ledgers(audited_declarations: set[str]) -> None:
    matrix = read_tsv(
        RESULTS / "VALIDATED_FORMAL_CLAIM_MATRIX.tsv",
        [
            "claim_id",
            "group",
            "exact_claim",
            "validity",
            "novelty",
            "formalization",
            "validation",
            "endpoint_basis",
            "endpoint_count",
            "boundary",
        ],
    )
    if len(matrix) != 92:
        raise VerificationError(f"claim matrix has {len(matrix)} rows, expected 92")
    validity_counts = Counter(row["validity"] for row in matrix)
    if validity_counts != Counter({"V": 66, "U": 25, "OPEN": 1}):
        raise VerificationError(f"unexpected claim validity counts: {validity_counts}")
    open_rows = [row for row in matrix if row["validity"] == "OPEN"]
    required_open = {
        "claim_id": "P0",
        "group": "OPEN",
        "formalization": "OUTSIDE_THEOREM_CREDIT",
        "validation": "NO_KERNEL_CREDIT",
        "endpoint_count": "0",
        "boundary": "No witness and no universal obstruction",
    }
    if len(open_rows) != 1 or any(
        open_rows[0][field] != value for field, value in required_open.items()
    ):
        raise VerificationError(f"unexpected open-problem row: {open_rows!r}")
    verified_endpoint_total = sum(
        int(row["endpoint_count"]) for row in matrix if row["validity"] == "V"
    )
    if verified_endpoint_total != 324:
        raise VerificationError(
            f"verified endpoint total is {verified_endpoint_total}, expected 324"
        )
    if any(
        int(row["endpoint_count"]) != 0
        for row in matrix
        if row["validity"] != "V"
    ):
        raise VerificationError("a non-verified matrix row has theorem endpoints")
    if any(
        row["formalization"] != "FORMALIZED_EXACT"
        or row["validation"] != "VALIDATION_003_KERNEL_PASS"
        for row in matrix
        if row["validity"] == "V"
    ):
        raise VerificationError("a verified family lacks the accepted formal status")

    endpoints = read_tsv(
        RESULTS / "CLAIM_ENDPOINTS.tsv",
        ["claim_id", "scope", "declaration", "kind", "source"],
    )
    if len(endpoints) != 324:
        raise VerificationError(f"endpoint map has {len(endpoints)} rows, expected 324")
    declarations = [row["declaration"] for row in endpoints]
    expect_unique(declarations, "claim endpoint declarations")
    if not set(declarations).issubset(audited_declarations):
        missing = sorted(set(declarations) - audited_declarations)
        raise VerificationError(f"claim endpoints absent from axiom audit: {missing[:5]}")
    verified_ids = {row["claim_id"] for row in matrix if row["validity"] == "V"}
    if {row["claim_id"] for row in endpoints} != verified_ids:
        raise VerificationError("endpoint family IDs do not equal the 66 verified IDs")
    endpoint_counts = Counter(row["claim_id"] for row in endpoints)
    matrix_counts = {
        row["claim_id"]: int(row["endpoint_count"])
        for row in matrix
        if row["validity"] == "V"
    }
    if dict(endpoint_counts) != matrix_counts:
        raise VerificationError("per-family endpoint counts differ from the claim matrix")
    for row in endpoints:
        source = safe_repo_path(row["source"])
        if not source.is_file():
            raise VerificationError(f"missing endpoint source: {row['source']}")

    theorem_index = (RESULTS / "THEOREM_INDEX.md").read_text(encoding="utf-8")
    indexed_ids = re.findall(r"^\| `([^`]+)` \|", theorem_index, flags=re.MULTILINE)
    expect_unique(indexed_ids, "theorem index family IDs")
    if set(indexed_ids) != verified_ids:
        raise VerificationError("theorem index does not cover exactly the 66 verified IDs")


def verify_receipts() -> None:
    path = VALIDATION / "CURRENT_LEAN_SOURCE_INTEGRITY_AUDIT.json"
    data = json.loads(path.read_text(encoding="utf-8"))
    if data.get("result") != "PASS_CURRENT_VALIDATED_SOURCE_INTEGRITY":
        raise VerificationError(f"{path.relative_to(ROOT)} does not record PASS")
    if data.get("errors") != []:
        raise VerificationError(f"{path.relative_to(ROOT)} records errors")
    counts = data.get("counts", {})
    required_counts = {
        "lean_sources": 72,
        "validated_lean_inputs": 72,
        "print_axioms_commands": 350,
        "lexical_errors": 0,
        "executable_forbidden_hits": 0,
        "executable_equivalent_escape_hits": 0,
    }
    for field, expected in required_counts.items():
        if counts.get(field) != expected:
            raise VerificationError(
                f"{path.relative_to(ROOT)} {field}={counts.get(field)!r}, expected {expected}"
            )
    manifest = data.get("source_manifest", {})
    if manifest != {
        "record_bytes": 8383,
        "sha256": "b406623fe167701f4e1e6a9ec4e824cd4e0a72cef59b0211b9237740d2658bb6",
    }:
        raise VerificationError(f"unexpected source-integrity manifest: {manifest!r}")


def main() -> int:
    try:
        _, lean_paths = verify_inputs()
        verify_module_order(lean_paths)
        audited_declarations = verify_axioms()
        verify_claim_ledgers(audited_declarations)
        verify_receipts()
    except (OSError, UnicodeError, csv.Error, json.JSONDecodeError, VerificationError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1
    summary = {
        "result": "PASS_PUBLIC_SNAPSHOT_REPLAY",
        "validated_inputs": 75,
        "lean_sources": 72,
        "module_order_rows": 72,
        "axiom_queries": 350,
        "verified_families": 66,
        "claim_endpoints": 324,
        "original_problem_solved": False,
    }
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
