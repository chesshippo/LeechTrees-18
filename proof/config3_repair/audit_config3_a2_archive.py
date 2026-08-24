#!/usr/bin/env python3
"""Strict, read-only audit of the surviving historical Configuration 3/A2 archive.

This verifier deliberately distinguishes a structurally exact ledger from raw
process evidence.  It exits nonzero in full mode while any of the 47 original
stdout/stderr/done/pid bundles is unavailable; ``--ledger-only`` proves only
the narrower, explicitly labelled ledger claim.
"""

from __future__ import annotations

import argparse
import csv
import decimal
import hashlib
import io
import json
import sys
from pathlib import Path
from typing import Any


PINS = {
    "evidence_manifest": (
        "computation/evidence/production/"
        "prior_three_configurations/MANIFEST.sha256",
        157214,
        "3779ba12c799a328ed1dd751cc79f643b9a636069a628447245f891eae6ac3d6",
    ),
    "a2_manifest": (
        "computation/evidence/production/"
        "prior_three_configurations/outputs/A2_EXHAUSTIVE_ZERO_SHA256SUMS.txt",
        782,
        "18e0e957c30b9ad7cdf421b591be497728c8249041309ed7a1d996c859692817",
    ),
    "ledger": (
        "computation/evidence/production/"
        "prior_three_configurations/outputs/A2_MULTI_EDGE_PARTITION_RESULTS.csv",
        2441,
        "bc6a5909d2de7b0cbc0e1a886a03c675b92419c8c4e553ad944e1a123dbc93ac",
    ),
    "source": (
        "computation/evidence/production/"
        "prior_three_configurations/work/a2_solver/a2_topology_free_search.cpp",
        41199,
        "e8dedc62323152ba586f9c8607d119440c8be9927ec4d38e546ba11de9100e9c",
    ),
    "preserved_binary": (
        "computation/evidence/production/"
        "prior_three_configurations/work/a2_solver/a2_topology_free_search_multicover.exe",
        355685,
        "65bbaa57e5b462663b3656bc77499cc5956053f4137878c21072c99a327483f3",
    ),
    "legacy_verifier": (
        "computation/evidence/production/"
        "prior_three_configurations/work/a2_solver/verify_a2_partition_coverage.ps1",
        2250,
        "daae5dba585cacb4f27fae7199ea446433f6e6c26e997c8e20730f26ae4d91d6",
    ),
}

HEADER = [
    "mode",
    "partition",
    "status",
    "nodes",
    "wall_seconds",
    "exit_code",
    "notes",
]

EXPECTED_TOTALS = {
    "a2_attached": (7, 17_650_190, decimal.Decimal("2269.8161381")),
    "a2_separate": (40, 150_092_642, decimal.Decimal("43265.2712488")),
}

RAW_ROLES = ("stdout", "stderr", "done", "pid")


class AuditFailure(RuntimeError):
    pass


def expected_keys() -> list[str]:
    keys = ["a2_attached|root_0"]
    keys += [f"a2_attached|path_1_{i}" for i in range(6)]
    keys += [f"a2_separate|root_{i}" for i in range(4)]
    keys += [f"a2_separate|path_4_{i}" for i in range(6)]
    keys += [f"a2_separate|path_5_{i}" for i in range(5)]
    keys += [f"a2_separate|path_6_{i}" for i in range(2)]
    keys += [f"a2_separate|path_7_{i}" for i in range(8)]
    keys += [f"a2_separate|path_8_{i}" for i in range(15)]
    assert len(keys) == len(set(keys)) == 47
    return keys


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def verify_pins(workspace: Path) -> dict[str, dict[str, Any]]:
    result: dict[str, dict[str, Any]] = {}
    for name, (relative, expected_bytes, expected_hash) in PINS.items():
        path = workspace / relative
        if not path.is_file():
            raise AuditFailure(f"missing pinned {name}: {path}")
        raw = path.read_bytes()
        actual_hash = sha256(raw)
        if len(raw) != expected_bytes or actual_hash != expected_hash:
            raise AuditFailure(
                f"pin mismatch {name}: expected=({expected_bytes},{expected_hash}) "
                f"actual=({len(raw)},{actual_hash})"
            )
        result[name] = {
            "path": str(path.resolve()),
            "bytes": len(raw),
            "sha256": actual_hash,
        }
    return result


def verify_ledger(path: Path) -> dict[str, Any]:
    raw = path.read_bytes()
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise AuditFailure(f"ledger is not UTF-8: {exc}") from exc
    reader = csv.DictReader(io.StringIO(text, newline=""))
    if reader.fieldnames != HEADER:
        raise AuditFailure(f"wrong ledger header: {reader.fieldnames!r}")
    rows = list(reader)
    keys = [f"{row['mode']}|{row['partition']}" for row in rows]
    expected = expected_keys()
    if keys != expected:
        raise AuditFailure(
            "ledger is not the exact ordered roster: "
            f"missing={sorted(set(expected)-set(keys))} "
            f"extra={sorted(set(keys)-set(expected))}"
        )
    if len(set(keys)) != 47:
        raise AuditFailure("duplicate ledger keys")
    totals: dict[str, list[Any]] = {
        mode: [0, 0, decimal.Decimal(0)] for mode in EXPECTED_TOTALS
    }
    inferred_exit_keys: list[str] = []
    for row in rows:
        key = f"{row['mode']}|{row['partition']}"
        if row["status"] != "ZERO" or row["exit_code"] != "0":
            raise AuditFailure(f"non-ZERO/nonzero ledger field: {key}")
        try:
            nodes = int(row["nodes"])
            wall = decimal.Decimal(row["wall_seconds"])
        except (ValueError, decimal.InvalidOperation) as exc:
            raise AuditFailure(f"bad numeric field {key}: {exc}") from exc
        if nodes <= 0 or wall <= 0:
            raise AuditFailure(f"nonpositive metric: {key}")
        totals[row["mode"]][0] += 1
        totals[row["mode"]][1] += nodes
        totals[row["mode"]][2] += wall
        if "exit inferred" in row["notes"]:
            inferred_exit_keys.append(key)
    normalized = {mode: tuple(values) for mode, values in totals.items()}
    if normalized != EXPECTED_TOTALS:
        raise AuditFailure(f"ledger totals mismatch: {normalized!r}")
    if inferred_exit_keys != ["a2_separate|path_6_1"]:
        raise AuditFailure(f"unexpected inferred-exit annotation: {inferred_exit_keys}")
    return {
        "status": "STRICT_LEDGER_PASS",
        "row_count": len(rows),
        "ordered_exact_set": True,
        "unexpected_rows_rejected": True,
        "totals": {
            mode: {
                "partitions": values[0],
                "nodes": values[1],
                "wall_seconds": str(values[2]),
            }
            for mode, values in normalized.items()
        },
        "inferred_exit_keys": inferred_exit_keys,
    }


def verify_manifests(workspace: Path) -> dict[str, Any]:
    evidence_path = workspace / PINS["evidence_manifest"][0]
    lines = evidence_path.read_text(encoding="utf-8").splitlines()
    partition_lines = [line for line in lines if "partition_runs/" in line]
    row1 = [line for line in partition_lines if "row1_partition_runs/" in line]
    row7 = [line for line in partition_lines if "row7_partition_runs/" in line]
    a2 = [
        line
        for line in partition_lines
        if "work/a2_solver/partition_runs/" in line
        and "row1_partition_runs/" not in line
        and "row7_partition_runs/" not in line
    ]
    if (len(lines), len(partition_lines), len(row1), len(row7), len(a2)) != (
        1078,
        524,
        316,
        208,
        0,
    ):
        raise AuditFailure("evidence manifest inventory counts changed")
    a2_manifest_path = workspace / PINS["a2_manifest"][0]
    a2_lines = a2_manifest_path.read_text(encoding="utf-8").splitlines()
    if len(a2_lines) != 7 or any("partition_runs" in line for line in a2_lines):
        raise AuditFailure("A2 manifest no longer has the expected seven non-raw entries")
    return {
        "evidence_manifest_entries": len(lines),
        "partition_run_entries": len(partition_lines),
        "row1_partition_run_entries": len(row1),
        "row7_partition_run_entries": len(row7),
        "a2_partition_run_entries": len(a2),
        "a2_manifest_entries": len(a2_lines),
        "a2_manifest_raw_entries": 0,
    }


def named_raw_roots(workspace: Path) -> list[dict[str, Any]]:
    relative_roots = [
        "computation/evidence/production/prior_three_configurations/"
        "work/a2_solver/partition_runs",
    ]
    result = []
    for relative in relative_roots:
        path = workspace / relative
        result.append({"path": str(path.resolve()), "exists": path.exists()})
    if any(item["exists"] for item in result):
        raise AuditFailure("an A2 raw root now exists and needs explicit bundle verification")
    return result


def audit(workspace: Path) -> dict[str, Any]:
    pins = verify_pins(workspace)
    ledger = verify_ledger(Path(pins["ledger"]["path"]))
    manifests = verify_manifests(workspace)
    roots = named_raw_roots(workspace)
    missing = [
        {"key": key, "missing_roles": list(RAW_ROLES)} for key in expected_keys()
    ]
    return {
        "schema": "config3-a2-historical-archive-audit-v1",
        "ledger": ledger,
        "manifests": manifests,
        "named_raw_roots": roots,
        "missing_original_bundle_count": 47,
        "missing_original_artifact_role_count": 47 * len(RAW_ROLES),
        "missing_bundles": missing,
        "byte_identical_recovery": {
            "status": "NOT_ESTABLISHABLE_FROM_PROVIDED_ARCHIVE",
            "reason": (
                "no original A2 raw-artifact roster or raw SHA-256 values survive; "
                "the preserved documentation's statement that 18 terminal logs survive has no "
                "identifying list or digests in the supplied trees"
            ),
        },
        "inferred_exit_repair": {
            "historical_a2_separate_path_6_1": "NOT_REPAIRABLE_AS_AN_OBSERVATION",
            "fresh_rerun_can_replace_it": True,
        },
        "legacy_extra_row_repair": {
            "strict_exact_set_verifier": True,
            "unexpected_rows_rejected": True,
        },
        "pins": pins,
        "full_raw_evidence_status": "INCOMPLETE",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace")
    parser.add_argument("--ledger-only", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    workspace = (
        Path(args.workspace).resolve()
        if args.workspace
        else Path(__file__).resolve().parents[2]
    )
    try:
        result = audit(workspace)
    except (AuditFailure, OSError, ValueError) as exc:
        print(f"CONFIG3_A2_ARCHIVE_AUDIT_FAIL: {exc}", file=sys.stderr)
        return 2
    if args.json:
        print(json.dumps(result, sort_keys=True, indent=2))
    else:
        print(
            "CONFIG3_A2_LEDGER_STRICT_OK rows=47 nodes=167742832 "
            "unexpected_rows_rejected=true inferred_exit_rows=1"
        )
        print(
            "CONFIG3_A2_RAW_ARCHIVE_INCOMPLETE missing_bundles=47 "
            "missing_roles=188 a2_manifest_raw_entries=0"
        )
        for item in result["missing_bundles"]:
            print(
                f"MISSING_BUNDLE key={item['key']} "
                f"roles={','.join(item['missing_roles'])}"
            )
    if args.ledger_only:
        print("CONFIG3_A2_LEDGER_ONLY_AUDIT_PASS")
        return 0
    print(
        "CONFIG3_A2_FULL_HISTORICAL_EVIDENCE_FAIL "
        "reason=original_raw_bundles_and_observed_path_6_1_exit_absent",
        file=sys.stderr,
    )
    return 3


if __name__ == "__main__":
    raise SystemExit(main())
