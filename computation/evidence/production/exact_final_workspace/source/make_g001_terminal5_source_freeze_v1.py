#!/usr/bin/env python3
"""Create the external hash freeze for the terminal5 source distribution."""

from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path
from typing import Optional, Sequence

sys.dont_write_bytecode = True

import g001_terminal5_common_v1 as common


SCHEMA = "G001_TERMINAL5_SOURCE_FREEZE_V1"
FREEZE_NAME = "g001_terminal5_source_freeze_v1.json"
CHECKSUM_NAME = "G001_TERMINAL5_PRODUCTION_V1_SHA256SUMS.txt"
DISTRIBUTION_FILES = (
    "G001_REMAINING_LEAF_PIPELINE_V1.md",
    "G001_TERMINAL5_PRODUCTION_V1_README.md",
    "a2_multi_edge_exact_cover.hpp",
    "a2_multi_edge_exact_cover_optimized.hpp",
    "a2_multi_edge_stronger_relaxation.hpp",
    "check_g001_leech_witness.cpp",
    "c157_resume861_collect_compat_v2r1_20260818T160902Z/collect_g001_c157_job376839_resume861_prior_provenance_compat_v2.py",
    "collect_g001_terminal5_results_v1.py",
    "g001_remaining_leaf_collect.py",
    "g001_remaining_leaf_common.py",
    "g001_remaining_leaf_worker.py",
    "g001_remaining_witness_solver.cpp",
    "g001_terminal5_build_runtime_v1.py",
    "g001_terminal5_common_v1.py",
    "g001_terminal5_devel_smoke_v1.sbatch",
    "g001_terminal5_mi2101x_canary_v1.sbatch",
    "g001_terminal5_mi2101x_full_v1.sbatch",
    "make_g001_terminal5_plan_v1.py",
    "make_g001_terminal5_source_freeze_v1.py",
    "multi_edge_parity_coherence.hpp",
    "order18_topology_free_search.cpp",
    "run_g001_terminal5_bundle_v1.py",
    "test_g001_remaining_leaf_pipeline.py",
    "test_g001_remaining_witness_solver.cpp",
    "test_g001_terminal5_v1.py",
    "verify_g001_terminal5_gate_v1.py",
    "verify_g001_terminal5_plan_v1.py",
    "verify_g001_terminal5_source_freeze_v1.py",
)


def make(source_dir: Path) -> dict:
    source_dir = common.require_directory(source_dir, "source directory")
    hashes = {}
    for name in DISTRIBUTION_FILES:
        path = source_dir / name
        common.read_regular(path, f"distribution source {name}")
        hashes[name] = common.sha256_file(path)
    return {
        "schema": SCHEMA,
        "distribution_count": len(DISTRIBUTION_FILES),
        "distribution_files": hashes,
        "inputs": {"c157": dict(common.C157_ARCHIVE),
                   "config4": dict(common.CONFIG4_ARCHIVE),
                   "selection_sha256": {str(k): v for k, v in common.SELECTION_HASHES.items()}},
        "terminal_plan_invariants": {
            "partition_records": common.TOTAL_RECORDS,
            "search_leaves": common.TOTAL_SEARCH,
            "certified_zero_records": common.TOTAL_ZERO,
            "bundles": common.TOTAL_BUNDLES,
            "workers_per_bundle": common.WORKERS_PER_BUNDLE,
            "cpus_per_bundle": common.CPUS_PER_BUNDLE,
            "maximum_concurrent_bundles": 24,
            "maximum_allocated_cpus": 384,
            "maximum_solver_workers": 360,
        },
        "terminal_policy": {
            "solver_setting": "exact6",
            "multi_edge_cover_validate": "OFF",
            "node_cap": None,
            "depth_cap": None,
            "stop_depth": None,
            "found_requires_independent_checker": True,
            "found_report_immediately": True,
            "global_zero_requires_all_exact_receipts": True,
            "timeouts_are_non_evidence": True,
        },
        "claim_boundary": {
            "source_freeze_only": True,
            "terminal_search_performed": False,
            "proves_existence": False,
            "proves_nonexistence": False,
        },
    }


def write_new(path: Path, raw: bytes) -> None:
    descriptor = os.open(str(path), os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o444)
    try:
        with os.fdopen(descriptor, "wb", closefd=False) as stream:
            stream.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
    finally:
        os.close(descriptor)


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-dir", type=Path, default=Path(__file__).parent)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    try:
        freeze = make(args.source_dir)
        raw = common.canonical_json(freeze)
        if args.output is None:
            sys.stdout.buffer.write(raw)
        else:
            write_new(Path(os.path.abspath(os.fspath(args.output))), raw)
            print(f"G001_TERMINAL5_SOURCE_FREEZE_V1_WRITTEN {args.output}")
        return 0
    except (common.TerminalError, OSError, ValueError) as error:
        print(f"G001_TERMINAL5_SOURCE_FREEZE_V1_FAILED: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
