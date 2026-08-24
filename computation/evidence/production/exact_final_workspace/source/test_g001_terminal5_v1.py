#!/usr/bin/env python3
"""Static, synthetic, mutation-negative, and optional real-anchor tests."""

from __future__ import annotations

import copy
import importlib.util
import os
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List

sys.dont_write_bytecode = True

import g001_terminal5_common_v1 as common
import g001_terminal5_build_runtime_v1 as runtime
import make_g001_terminal5_plan_v1 as maker
import run_g001_terminal5_bundle_v1 as runner


CHECKS = 0


def require(condition: bool, label: str) -> None:
    global CHECKS
    CHECKS += 1
    if not condition:
        raise AssertionError(label)


def rejected(callable_value: Any, label: str) -> None:
    global CHECKS
    CHECKS += 1
    try:
        callable_value()
    except (RuntimeError, ValueError):
        return
    raise AssertionError(label)


def binding(name: str) -> Dict[str, str]:
    return {"path": name, "sha256": "0" * 64}


def synthetic_plan() -> Dict[str, Any]:
    records: List[Dict[str, Any]] = []
    for configuration in (1, 4, 5, 6, 7):
        total = common.EXPECTED_RECORDS[configuration]
        zeros = common.EXPECTED_ZERO[configuration]
        for index in range(total):
            classification = "CERTIFIED_ZERO" if index < zeros else "SEARCH"
            if configuration == 4 and index < 13:
                kind = "config4_preserved_zero"
            elif configuration == 4 and index < 30:
                kind = "config4_discharged_zero"
            elif configuration == 4 and index < 500:
                kind = "config4_depth15_descendant"
            elif configuration == 4:
                kind = "config4_retained_p2"
            else:
                kind = "c157_untouched_base"
            path = [index]
            records.append({
                "schema": common.RECORD_SCHEMA,
                "record_id": f"c{configuration}_{'z' if classification != 'SEARCH' else 's'}_{index:05d}",
                "configuration": configuration,
                "mode": common.CONFIGURATION_TO_MODE[configuration],
                "path": path,
                "path_text": str(index),
                "classification": classification,
                "bundle_index": None,
                "weight": 0 if kind in ("config4_depth15_descendant",
                                         "config4_preserved_zero",
                                         "config4_discharged_zero") else index + 1,
                "evidence": {
                    "source": "CONFIG4" if configuration == 4 else "C157",
                    "kind": kind,
                    "calibration_depth": 15 if kind in (
                        "config4_depth15_descendant", "config4_discharged_zero") else 12,
                    "calibration_frontier": 0 if kind in (
                        "config4_depth15_descendant", "config4_preserved_zero",
                        "config4_discharged_zero") else index + 1,
                    "source_id": f"synthetic:{configuration}:{index}",
                },
            })
    bundles = maker.assign_bundles(records)
    return {
        "schema": common.PLAN_SCHEMA,
        "plan_id": "terminal5_synthetic_v1",
        "inputs": {"c157": dict(common.C157_ARCHIVE),
                   "config4": dict(common.CONFIG4_ARCHIVE),
                   "selection_sha256": {str(k): v for k, v in common.SELECTION_HASHES.items()}},
        "runtime": {
            "workers_per_bundle": 15, "cpus_per_bundle": 16, "bundle_count": 192,
            "solver_setting": "exact6", "multi_edge_cover_validate": "OFF",
            "bindings": {role: binding(role) for role in (
                "solver_source", "solver_executable", "checker_source",
                "checker_executable", "runtime_freeze")},
            "pipeline_artifacts": {role: binding(role) for role in (
                "leaf_worker", "leaf_common", "leaf_collector")},
        },
        "invariants": {
            "record_count": 39030, "search_count": 39000,
            "certified_zero_count": 30,
            "records_by_configuration": {str(k): v for k, v in common.EXPECTED_RECORDS.items()},
            "search_by_configuration": {str(k): v for k, v in common.EXPECTED_SEARCH.items()},
            "zero_by_configuration": {str(k): v for k, v in common.EXPECTED_ZERO.items()},
            "bundles_by_configuration": {str(k): v for k, v in common.EXPECTED_BUNDLES.items()},
        },
        "claim_boundary": {
            "terminal_search": True, "found_requires_independent_checker": True,
            "found_report_immediately": True, "global_zero_requires_all_receipts": True,
            "timeouts_are_non_evidence": True,
            "calibration_frontier_is_not_certificate": True,
        },
        "records": records, "bundles": bundles,
    }


def load_leaf_common(root: Path) -> Any:
    specification = importlib.util.spec_from_file_location(
        "_terminal5_test_leaf_common", str(root / "g001_remaining_leaf_common.py"))
    assert specification is not None and specification.loader is not None
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


def main() -> int:
    root = Path(__file__).resolve().parent
    plan = synthetic_plan()
    common.validate_plan(plan, production=True)
    require(len(plan["records"]) == 39030, "synthetic record count")
    require(sum(item["classification"] == "SEARCH" for item in plan["records"]) == 39000,
            "synthetic search count")
    require(len(plan["bundles"]) == 192, "synthetic bundle count")
    require(all(bundle["search_count"] > 0 for bundle in plan["bundles"]),
            "all bundles nonempty")
    require(len(runner.deterministic_gate_records(plan, "smoke")) == 60,
            "smoke selection count")
    require(len(runner.deterministic_gate_records(plan, "canary")) == 30,
            "canary selection count")
    require({item["configuration"] for item in runner.deterministic_gate_records(plan, "canary")} ==
            {1, 4, 5, 6, 7}, "canary covers all configurations")

    duplicate = copy.deepcopy(plan)
    duplicate["records"][1]["path"] = list(duplicate["records"][0]["path"])
    duplicate["records"][1]["path_text"] = duplicate["records"][0]["path_text"]
    rejected(lambda: common.validate_plan(duplicate, production=True), "duplicate path rejected")
    overlap = copy.deepcopy(plan)
    overlap["records"][1]["path"] = [0, 1]
    overlap["records"][1]["path_text"] = "0,1"
    rejected(lambda: common.validate_plan(overlap, production=True), "prefix overlap rejected")
    missing = copy.deepcopy(plan)
    missing["records"].pop()
    rejected(lambda: common.validate_plan(missing, production=True), "missing record rejected")
    worker_mismatch = copy.deepcopy(plan)
    worker_mismatch["runtime"]["workers_per_bundle"] = 16
    rejected(lambda: common.validate_plan(worker_mismatch, production=True), "16 workers rejected")
    false_zero = copy.deepcopy(plan)
    descendant = next(item for item in false_zero["records"]
                      if item["evidence"]["kind"] == "config4_depth15_descendant")
    descendant["classification"] = "CERTIFIED_ZERO"
    descendant["bundle_index"] = None
    rejected(lambda: common.validate_plan(false_zero, production=True),
             "C4 calibration frontier zero cannot become certificate")
    bad_setting = copy.deepcopy(plan)
    bad_setting["runtime"]["multi_edge_cover_validate"] = "ON"
    rejected(lambda: common.validate_plan(bad_setting, production=True), "selection OFF binding")

    leaf_common = load_leaf_common(root)
    good_argv = common.solver_argv(1, [0])
    leaf_common.validate_argv_template(good_argv, 1, {"kind": "path", "indices": [0]})
    require("--stop-edges" not in good_argv and "--max-nodes" not in good_argv,
            "terminal argv has no cap")
    rejected(lambda: leaf_common.validate_argv_template(
        good_argv + ["--stop-edges", "12"], 1, {"kind": "path", "indices": [0]}),
        "stop-depth option rejected")
    require(good_argv[-len(common.EXACT_FLAGS):] == common.EXACT_FLAGS,
            "exact6/OFF flags exact")

    for name, digest in runtime.SOURCE_HASHES.items():
        require(common.sha256_file(root / name) == digest, f"scientific source hash {name}")
    for name in ("g001_terminal5_devel_smoke_v1.sbatch",
                 "g001_terminal5_mi2101x_canary_v1.sbatch",
                 "g001_terminal5_mi2101x_full_v1.sbatch"):
        text = (root / name).read_text(encoding="utf-8", errors="strict")
        require("--cpus-per-task=16" in text and "--workers 15" in text,
                f"resource split {name}")
        require("export PYTHONDONTWRITEBYTECODE=1" in text and
                text.count("python3 -B ") == 2,
                f"no-bytecode launch policy {name}")
        require("--stop-edges" not in text and "--max-nodes" not in text,
                f"no terminal cap {name}")
    runner_text = (root / "run_g001_terminal5_bundle_v1.py").read_text(
        encoding="utf-8", errors="strict")
    require(runner_text.count('sys.executable, "-B"') == 2,
            "worker and collector child interpreters suppress bytecode")
    require("--array=0-191%24" in (root / "g001_terminal5_mi2101x_full_v1.sbatch").read_text(),
            "full array width")
    require("--array=0-3%4" in (root / "g001_terminal5_devel_smoke_v1.sbatch").read_text(),
            "devel 64-CPU shape")
    require("--array=0-1%2" in (root / "g001_terminal5_mi2101x_canary_v1.sbatch").read_text(),
            "canary two-node shape")

    # Run every control entrypoint with ordinary Python (no -B and no
    # PYTHONDONTWRITEBYTECODE environment override).  Each script must suppress
    # its own local-import cache writes, so a clean frozen tree stays exact.
    child_environment = dict(os.environ)
    child_environment.pop("PYTHONDONTWRITEBYTECODE", None)
    for name in (
            "g001_terminal5_build_runtime_v1.py",
            "make_g001_terminal5_plan_v1.py",
            "verify_g001_terminal5_plan_v1.py",
            "run_g001_terminal5_bundle_v1.py",
            "collect_g001_terminal5_results_v1.py",
            "verify_g001_terminal5_gate_v1.py",
            "make_g001_terminal5_source_freeze_v1.py",
            "verify_g001_terminal5_source_freeze_v1.py"):
        completed = subprocess.run(
            [sys.executable, str(root / name), "--help"], cwd=str(root),
            stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, env=child_environment, check=False)
        require(completed.returncode == 0, f"no-bytecode entrypoint help {name}")
    dynamically_loaded = maker.load_module(
        root / "verify_g001_terminal5_gate_v1.py",
        "_terminal5_no_bytecode_dynamic_import_test")
    require(Path(dynamically_loaded.__file__).resolve() ==
            (root / "verify_g001_terminal5_gate_v1.py").resolve(),
            "dynamic provenance-style import stays bound to requested source")
    require(not any(path.name == "__pycache__" for path in root.rglob("__pycache__")),
            "control entrypoints leave frozen source cache-free")

    outputs = root.parent.parent / "outputs"
    for binding_value in (common.C157_ARCHIVE, common.CONFIG4_ARCHIVE):
        archive = outputs / binding_value["name"]
        if archive.exists():
            require(archive.stat().st_size == binding_value["bytes"],
                    f"real archive size {archive.name}")
            require(common.sha256_file(archive) == binding_value["sha256"],
                    f"real archive hash {archive.name}")
    print(f"PASS test_g001_terminal5_v1 checks={CHECKS}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
