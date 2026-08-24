#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock


SCRIPT = Path(__file__).resolve().parents[1] / "assemble_fresh_all_eight.py"
SPEC = importlib.util.spec_from_file_location("assemble_fresh_all_eight", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


HEX = "1" * 64


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, sort_keys=True) + "\n", encoding="utf-8")


def fixtures(root: Path) -> dict[str, Path]:
    frozen, source_driver = MODULE.prior_modules()
    jobs = [job for group in frozen.assemble_jobs() for job in group]
    build_root = root / "prior-build"
    build_root.mkdir()
    compiler_path = str(root / "fake-g++.exe")
    compile_flags = ["-O2", "-std=c++20", "-Wall", "-Wextra", "-Wpedantic"]
    solver_specs = (
        (3, "a2_topology_free_search.cpp", "a2_topology_free_search_multicover_rebuild.exe"),
        (8, "order18_topology_free_search_production_snapshot.cpp", "order18_topology_free_search_row7_rebuild.exe"),
        (2, "order18_topology_free_search_row1_snapshot.cpp", "order18_topology_free_search_row1_rebuild.exe"),
    )
    solvers = []
    solver_hashes = {}
    for configuration, source, output in solver_specs:
        path = build_root / output
        path.write_bytes(f"solver-{configuration}\n".encode("ascii"))
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        solver_hashes[configuration] = digest
        solvers.append({
            "source": source, "output": output,
            "command": [compiler_path, *compile_flags, source, "-o", str(path)],
            "sha256": digest, "size_bytes": path.stat().st_size,
        })
    tests = []
    for index, (source, marker) in enumerate(source_driver.TESTS):
        output = Path(source).stem + "_rebuild.exe"
        path = build_root / output
        path.write_bytes(f"test-{index}\n".encode("ascii"))
        tests.append({
            "source": source, "output": output,
            "command": [compiler_path, *compile_flags, source, "-o", str(path)],
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "size_bytes": path.stat().st_size, "exit_code": 0,
            "expected_marker": marker, "stdout": marker + "\n",
        })
    build = {
        "schema": "LEECH18_PRIOR_THREE_SOURCE_BUILD_V1",
        "compiler": {
            "path": compiler_path,
            "sha256": HEX,
            "version_output": "g++ 14.2.0",
            "matches_historical_documented_version": True,
        },
        "compile_flags": compile_flags,
        "sources": source_driver.validate_sources(),
        "solvers": solvers,
        "tests": tests,
    }
    build_path = build_root / "BUILD_RECEIPT.json"
    build_path.write_text(
        json.dumps(build, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    build_hash = hashlib.sha256(build_path.read_bytes()).hexdigest()
    (build_root / "BUILD_RECEIPT.sha256").write_bytes(
        f"{build_hash}  BUILD_RECEIPT.json\n".encode("ascii")
    )

    prior_root = root / "prior-run"
    prior_root.mkdir()
    receipts = []
    for job in jobs:
        result = {
            "status": job.expected_status,
            "mode": job.expected_mode,
            "nodes": str(job.expected_nodes),
            "frontier": str(job.expected_frontier),
            "solution_topologies": "0",
            "multi_cover": "on",
        }
        stdout_raw = (
            "RESULT " + " ".join(f"{key}={value}" for key, value in result.items()) + "\n"
        ).encode("ascii")
        stderr_raw = b""
        receipt = {
            "schema": "LEECH18_PRIOR_THREE_FRESH_PROCESS_V1",
            "configuration": job.configuration,
            "logical_key": job.logical_key,
            "process_key": job.process_key,
            "category": job.category,
            "solver_sha256": solver_hashes[job.configuration],
            "argv": list(job.argv),
            "exit_code": 0,
            "elapsed_seconds": 0.0,
            "result": result,
            "stdout": {"bytes": len(stdout_raw), "sha256": hashlib.sha256(stdout_raw).hexdigest()},
            "stderr": {"bytes": 0, "sha256": hashlib.sha256(stderr_raw).hexdigest()},
        }
        directory = prior_root / f"configuration_{job.configuration}" / job.process_key
        directory.mkdir(parents=True)
        (directory / "stdout.txt").write_bytes(stdout_raw)
        (directory / "stderr.txt").write_bytes(stderr_raw)
        (directory / "RECEIPT.json").write_bytes(frozen.canonical_json(receipt))
        receipts.append(receipt)
    configuration3_direct = sum(
        job.expected_nodes for job in jobs
        if job.configuration == 3 and job.category == "direct"
    )
    configuration3_children = sum(
        job.expected_nodes for job in jobs
        if job.configuration == 3 and job.category == "split_child"
    )
    prior = {
        "schema": "LEECH18_PRIOR_THREE_FULL_RECOMPUTATION_V1",
        "status": "ZERO_COMPLETE",
        "logical_partitions": 178,
        "physical_processes": 200,
        "zero_processes": 199,
        "frontier_census_processes": 1,
        "nodes": {
            "configuration_2": 193_281_350,
            "configuration_3_logical": 167_742_832,
            "configuration_3_direct": configuration3_direct,
            "configuration_3_split_children": configuration3_children,
            "configuration_3_normalization_subtraction": 63,
            "configuration_8": 239_702_053,
            "logical_total": 600_726_235,
        },
        "receipts": receipts,
    }
    prior_path = prior_root / "RECOMPUTATION_SUMMARY.json"
    prior_path.write_bytes(frozen.canonical_json(prior))

    c157_root = root / "c157"
    c157_root.mkdir()
    member = c157_root / "member.txt"
    member.write_text("test\n", encoding="ascii")
    member_hash = hashlib.sha256(member.read_bytes()).hexdigest()
    manifest = c157_root / "RESULTS_MANIFEST.sha256"
    manifest.write_text(f"{member_hash}  member.txt\n", encoding="ascii")
    c157 = {
        "schema": "leech18-c157-fresh-recomputation-v1",
        "status": "C157_FRESH_RECOMPUTATION_COMPLETE",
        "plan_sha256": MODULE.FROZEN_PLAN_SHA256,
        "leaf_count": 37_706,
        "internal_prefix_count": 2_135,
        "zero_child_count": 464,
        "solver_invocation_count": 80_142,
        "source_manifest_sha256": MODULE.C157_SOURCE_MANIFEST_SHA256,
        "results_manifest_sha256": hashlib.sha256(manifest.read_bytes()).hexdigest(),
        "solver_sha256": HEX,
        "preflight_sha256": HEX,
        "workload_sha256": HEX,
        "coverage": {
            "prefix_free": True,
            "exhaustive_gate_check": True,
            "leaf_frontiers_match_plan": True,
            "gate_parent_count": 2_135,
            "gate_child_count": 40_301,
            "gate_zero_child_count": 464,
            "omitted_zero_child_count": 464,
            "planned_zero_leaf_count": 813,
        },
        "configurations": {
            "1": {"mode": "g001_row0", "leaf_count": 5_176, "internal_prefix_count": 287, "gate_zero_child_count": 26, "omitted_zero_child_count": 26, "planned_zero_leaf_count": 153, "frontier_sum": 20_045_473},
            "5": {"mode": "g001_row4", "leaf_count": 25_254, "internal_prefix_count": 1_460, "gate_zero_child_count": 430, "omitted_zero_child_count": 430, "planned_zero_leaf_count": 378, "frontier_sum": 74_092_284},
            "6": {"mode": "g001_row5", "leaf_count": 3_977, "internal_prefix_count": 213, "gate_zero_child_count": 6, "omitted_zero_child_count": 6, "planned_zero_leaf_count": 155, "frontier_sum": 18_016_722},
            "7": {"mode": "g001_row6", "leaf_count": 3_299, "internal_prefix_count": 175, "gate_zero_child_count": 2, "omitted_zero_child_count": 2, "planned_zero_leaf_count": 127, "frontier_sum": 15_688_080},
        },
    }

    plan_hash = "9" * 64
    preflight = {
        "schema": "LEECH18_TERMINAL5_PREFLIGHT_V1",
        "status": "PASS",
        "mode": "completed-run",
        "terminal_plan_sha256": plan_hash,
        "frozen_plan_sha256": MODULE.FROZEN_PLAN_SHA256,
        "records": 39_030,
        "search_records": 39_000,
        "certified_zero_records": 30,
        "bundles": 192,
        "roster_matches_frozen": True,
        "authoritative_plan_verifier_passed": True,
        "completed_run_checked": True,
        "selectors_reached": 39_000,
        "zero_receipts": 39_000,
        "zero_artifacts_checked": 39_000,
        "clean_exit_receipts": 39_000,
        "leaf_receipt_set_sha256": HEX,
        "bundle_receipt_set_sha256": HEX,
        "verifier_identity": {
            "preflight_source_sha256": HEX,
            "authoritative_plan_verifier_sha256": HEX,
            "terminal_plan_parser_sha256": HEX,
            "leaf_plan_parser_sha256": HEX,
            "runtime_binding_sha256": {"solver": HEX},
            "pipeline_binding_sha256": {"runner": HEX},
        },
    }
    terminal = {
        "schema": "G001_TERMINAL5_COLLECTION_V1",
        "plan_id": "g001-terminal5-v1-candidate4",
        "scope": "global",
        "status": "GLOBAL_ZERO_COMPLETE",
        "plan_sha256": plan_hash,
        "search_receipts": 39_000,
        "certified_zero_records": 30,
        "displayed_partition_records": 39_030,
        "terminal_search_complete": True,
        "global_nonexistence": True,
        "configuration_nonexistence": False,
        "timeouts_are_non_evidence": True,
        "by_configuration": {
            "1": {"search_receipts": 5_176, "certified_zero_records": 0, "displayed_partition_records": 5_176, "nodes_sum": 1_321_606_123, "terminal_zero": True},
            "4": {"search_receipts": 1_294, "certified_zero_records": 30, "displayed_partition_records": 1_324, "nodes_sum": 225_016_655, "terminal_zero": True},
            "5": {"search_receipts": 25_254, "certified_zero_records": 0, "displayed_partition_records": 25_254, "nodes_sum": 4_242_081_806, "terminal_zero": True},
            "6": {"search_receipts": 3_977, "certified_zero_records": 0, "displayed_partition_records": 3_977, "nodes_sum": 1_165_724_514, "terminal_zero": True},
            "7": {"search_receipts": 3_299, "certified_zero_records": 0, "displayed_partition_records": 3_299, "nodes_sum": 1_010_043_681, "terminal_zero": True},
        },
    }
    supplement_records = [
        {"record_id": f"record-{i}", "nodes": i, "argv_sha256": HEX, "marker_sha256": HEX}
        for i in range(30)
    ]
    config4 = {
        "schema": "LEECH18_CONFIG4_CERTIFIED_ZERO_FRESH_RECOMPUTATION_V1",
        "status": "ZERO_COMPLETE",
        "configuration": 4,
        "mode": "g001_row3",
        "prior_classification": "CERTIFIED_ZERO",
        "fresh_terminal_searches": 30,
        "fresh_zero_results": 30,
        "terminal_plan_id": "g001-terminal5-v1-candidate4",
        "terminal_plan_sha256": plan_hash,
        "frozen_terminal_plan_sha256": MODULE.FROZEN_PLAN_SHA256,
        "non_runtime_plan_fields_match_frozen": True,
        "authoritative_plan_runtime_verified": True,
        "derived_roster_bytes": 12_402,
        "derived_roster_sha256": "ead047bedce8674ce516172919846873531b82932a4533a57ac88f7b3fea5de9",
        "reported_terminal5_nodes_excluding_supplemental": 7_964_472_779,
        "supplemental_nodes": sum(range(30)),
        "records": supplement_records,
    }

    paths = {
        "prior": prior_path,
        "build": build_path,
        "c157": c157_root / "C157_RECOMPUTATION.json",
        "terminal": root / "terminal.json",
        "config4": root / "config4.json",
        "preflight": root / "preflight.json",
        "output": root / "output.json",
    }
    for name, value in (
        ("c157", c157), ("terminal", terminal),
        ("config4", config4), ("preflight", preflight),
    ):
        write_json(paths[name], value)
    return paths


def arguments(paths: dict[str, Path]) -> list[str]:
    return [
        "--prior-three-summary", str(paths["prior"]),
        "--prior-three-build-receipt", str(paths["build"]),
        "--c157-summary", str(paths["c157"]),
        "--terminal-summary", str(paths["terminal"]),
        "--config4-summary", str(paths["config4"]),
        "--terminal-preflight", str(paths["preflight"]),
        "--output", str(paths["output"]),
    ]


class AssemblyTests(unittest.TestCase):
    def test_complete_fixture_is_assembled(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            paths = fixtures(Path(directory))
            with mock.patch.object(MODULE, "verify_c157_complete_run"):
                self.assertEqual(MODULE.main(arguments(paths)), 0)
            value = json.loads(paths["output"].read_text(encoding="utf-8"))
            self.assertEqual(value["status"], MODULE.STATUS)
            self.assertEqual(value["reported_node_visits"], 8_565_199_014)

    def test_tampered_completed_run_count_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            paths = fixtures(Path(directory))
            value = json.loads(paths["preflight"].read_text(encoding="utf-8"))
            value["zero_receipts"] = 38_999
            write_json(paths["preflight"], value)
            with mock.patch.object(MODULE, "verify_c157_complete_run"):
                self.assertEqual(MODULE.main(arguments(paths)), 1)
            self.assertFalse(paths["output"].exists())

    def test_minimal_c157_manifest_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            paths = fixtures(Path(directory))
            self.assertEqual(MODULE.main(arguments(paths)), 1)
            self.assertFalse(paths["output"].exists())

    def test_arbitrary_prior_process_identity_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            paths = fixtures(Path(directory))
            value = json.loads(paths["prior"].read_text(encoding="utf-8"))
            value["receipts"][0]["process_key"] = "invented-process"
            frozen, _source_driver = MODULE.prior_modules()
            paths["prior"].write_bytes(frozen.canonical_json(value))
            with mock.patch.object(MODULE, "verify_c157_complete_run"):
                self.assertEqual(MODULE.main(arguments(paths)), 1)
            self.assertFalse(paths["output"].exists())

    def test_existing_output_is_not_overwritten(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            paths = fixtures(Path(directory))
            paths["output"].write_bytes(b"keep\n")
            with mock.patch.object(MODULE, "verify_c157_complete_run"):
                self.assertEqual(MODULE.main(arguments(paths)), 1)
            self.assertEqual(paths["output"].read_bytes(), b"keep\n")


if __name__ == "__main__":
    unittest.main()
