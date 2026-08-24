#!/usr/bin/env python3
"""Bounded tests for the public C157 reconstruction driver."""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock


SCRIPT = Path(__file__).resolve().parents[1] / "recompute_c157_full.py"
SPEC = importlib.util.spec_from_file_location("recompute_c157_full", SCRIPT)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("cannot import recompute_c157_full.py")
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


class WorkloadTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.workload = MODULE.load_workload(MODULE.DEFAULT_PLAN)

    def test_authoritative_zero_weight_search_leaf_is_retained(self) -> None:
        matches = [
            leaf for leaf in self.workload.leaves
            if leaf.configuration == 1 and leaf.path == (3, 4, 4)
        ]
        self.assertEqual(len(matches), 1)
        self.assertEqual(matches[0].frontier, 0)

    def test_zero_weight_leaf_census(self) -> None:
        zero_leaves = [leaf for leaf in self.workload.leaves if leaf.frontier == 0]
        self.assertEqual(len(zero_leaves), MODULE.EXPECTED_PLANNED_ZERO_LEAVES)
        self.assertEqual(
            {configuration: sum(
                leaf.configuration == configuration and leaf.frontier == 0
                for leaf in self.workload.leaves)
             for configuration in MODULE.CONFIGURATIONS},
            {1: 153, 5: 378, 6: 155, 7: 127},
        )

    def test_trie_and_invocation_census(self) -> None:
        self.assertEqual(len(self.workload.leaves), MODULE.EXPECTED_LEAVES)
        self.assertEqual(
            sum(map(len, self.workload.internal.values())),
            MODULE.EXPECTED_INTERNAL_PREFIXES,
        )
        planned_edges = sum(
            len(children) for children in self.workload.children.values()
        )
        self.assertEqual(planned_edges, MODULE.EXPECTED_PLANNED_CHILDREN)
        self.assertEqual(MODULE.EXPECTED_CHILD_GATES, 40301)
        self.assertEqual(MODULE.EXPECTED_INVOCATIONS, 80142)

    def test_resume_rejects_cached_nonzero_exit(self) -> None:
        task = MODULE.Task(
            "gate_parent", 1, "g001_row0", tuple(), 4
        )
        with tempfile.TemporaryDirectory(prefix="c157-cache-test-") as raw:
            tasks_dir = Path(raw)
            stdout_path, stderr_path, meta_path = MODULE.task_paths(
                tasks_dir, task
            )
            stdout_path.write_bytes(b"")
            stderr_path.write_bytes(b"")
            metadata = {
                "command": ["g001_remaining_shallow_pilot"] + task.arguments(),
                "exit_code": 1,
                "schema": "leech18-c157-task-v1",
                "solver_sha256": "0" * 64,
                "status": "COMPLETE",
                "stderr_sha256": MODULE.sha256(stderr_path),
                "stdout_sha256": MODULE.sha256(stdout_path),
                "task": task.identity(),
                "timed_out": False,
            }
            meta_path.write_text(
                json.dumps(metadata), encoding="utf-8"
            )
            with self.assertRaisesRegex(
                    MODULE.RecomputeError, "cached task binding mismatch"):
                MODULE.load_cached_task(
                    tasks_dir, task, "0" * 64, object(),
                    "g001_remaining_shallow_pilot",
                )

    def test_minimal_self_consistent_manifest_is_rejected_without_execution(
            self) -> None:
        configurations = {}
        for configuration, expected in MODULE.CONFIGURATIONS.items():
            configurations[str(configuration)] = {
                "frontier_sum": expected["frontier_sum"],
                "gate_zero_child_count": expected["gate_zero_child_count"],
                "internal_prefix_count": expected["internal_prefix_count"],
                "leaf_count": expected["leaf_count"],
                "mode": expected["mode"],
                "omitted_zero_child_count":
                    expected["omitted_zero_child_count"],
                "planned_zero_leaf_count": expected["planned_zero_leaf_count"],
            }
        coverage = {
            "exhaustive_gate_check": True,
            "gate_child_count": MODULE.EXPECTED_CHILD_GATES,
            "gate_parent_count": MODULE.EXPECTED_INTERNAL_PREFIXES,
            "gate_zero_child_count": MODULE.EXPECTED_GATE_ZERO_CHILDREN,
            "leaf_frontiers_match_plan": True,
            "omitted_zero_child_count": MODULE.EXPECTED_ZERO_CHILDREN,
            "planned_zero_leaf_count": MODULE.EXPECTED_PLANNED_ZERO_LEAVES,
            "prefix_free": True,
        }
        with tempfile.TemporaryDirectory(prefix="c157-minimal-run-") as raw:
            run_dir = Path(raw)
            manifest = run_dir / "RESULTS_MANIFEST.sha256"
            manifest.write_bytes(b"")
            summary = {
                "build": {},
                "completed_utc": "synthetic",
                "configurations": configurations,
                "coverage": coverage,
                "historical_solver_sha256": MODULE.HISTORICAL_SOLVER_SHA256,
                "internal_prefix_count": MODULE.EXPECTED_INTERNAL_PREFIXES,
                "leaf_count": MODULE.EXPECTED_LEAVES,
                "plan_sha256": MODULE.PLAN_SHA256,
                "preflight_sha256": "0" * 64,
                "production_flags": list(MODULE.PRODUCTION_FLAGS),
                "results_manifest_sha256": MODULE.sha256(manifest),
                "schema": MODULE.SCHEMA,
                "solver_invocation_count": MODULE.EXPECTED_INVOCATIONS,
                "solver_sha256": "0" * 64,
                "source_manifest_sha256": MODULE.sha256(
                    MODULE.SOURCE_MANIFEST
                ),
                "started_utc": "synthetic",
                "status": MODULE.STATUS,
                "workload_sha256": MODULE.EXPECTED_WORKLOAD_SHA256,
                "zero_child_count": MODULE.EXPECTED_ZERO_CHILDREN,
            }
            (run_dir / "C157_RECOMPUTATION.json").write_text(
                json.dumps(summary), encoding="utf-8"
            )
            with mock.patch.object(
                    MODULE.subprocess, "Popen",
                    side_effect=AssertionError("solver execution attempted")):
                with self.assertRaisesRegex(
                        MODULE.RecomputeError, "WORKLOAD.json is missing"):
                    MODULE.verify_run(run_dir)

    def test_workload_byte_tamper_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory(prefix="c157-workload-test-") as raw:
            run_dir = Path(raw)
            data = MODULE.pretty_json_bytes(self.workload.canonical) + b"\n"
            (run_dir / "WORKLOAD.json").write_bytes(data)
            with self.assertRaisesRegex(
                    MODULE.RecomputeError, "exact canonical workload"):
                MODULE.verify_workload_record(run_dir, self.workload)


if __name__ == "__main__":
    unittest.main()
