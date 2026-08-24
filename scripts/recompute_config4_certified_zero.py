#!/usr/bin/env python3
"""Freshly search the 30 Config4 records retained as CERTIFIED_ZERO.

The canonical Terminal5 plan deliberately keeps these records outside its
normal solver bundles.  This supplemental driver derives their terminal argv
templates with the same hash-pinned function used for every Terminal5 SEARCH
leaf, runs them through the frozen leaf worker, and replays the resulting
evidence with the frozen leaf collector.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import subprocess
import sys
import time
from pathlib import Path
from types import ModuleType
from typing import Any, Mapping, Sequence


sys.dont_write_bytecode = True
os.environ["PYTHONDONTWRITEBYTECODE"] = "1"

SCRIPT_DIR = Path(__file__).absolute().parent
REPOSITORY = SCRIPT_DIR.parent
TERMINAL5 = (
    REPOSITORY
    / "computation/evidence/production"
    / "exact_final_workspace"
)
DEFAULT_SOURCE = TERMINAL5 / "source"
DEFAULT_PLAN = TERMINAL5 / "plan/terminal5_plan_v1/terminal_plan_v1.json"

EXPECTED_PLAN_ID = "g001-terminal5-v1-candidate4"
EXPECTED_FROZEN_PLAN_SHA256 = (
    "b317a3b7cef71e11fea762ce5e70322f168e06c6e04b97293f066cb2e313bdae"
)
EXPECTED_ROSTER_BYTES = 12_402
EXPECTED_ROSTER_SHA256 = (
    "ead047bedce8674ce516172919846873531b82932a4533a57ac88f7b3fea5de9"
)
EXPECTED_RECORDS = 30
EXPECTED_WORKERS = 15
WITNESS_PLACEHOLDER = "{WITNESS_FILE}"
WITNESS_NAME = "witness.LEECH_WITNESS_V1.txt"
NON_RUNTIME_PLAN_FIELDS = (
    "schema",
    "plan_id",
    "inputs",
    "invariants",
    "claim_boundary",
    "records",
    "bundles",
)

SOURCE_HASHES = {
    "g001_terminal5_source_freeze_v1.json": (
        "537fb0d163cc04e891d544d4e4accefdf5fdbb91cdbb20c54d05e4037abb852c"
    ),
    "g001_terminal5_common_v1.py": (
        "b743c1890e4c410425d21d80a827753afa742e5958cc9588060931d421e9200d"
    ),
    "g001_remaining_leaf_common.py": (
        "d069b33acd9dc3f49fdc6df11d2f83d39b24f336db91b9239bfefb229586db27"
    ),
    "g001_remaining_leaf_worker.py": (
        "3691b562375742e9fd95e56cbb4c0293fcb5630347483dd3d744ab0ce9181a25"
    ),
    "g001_remaining_leaf_collect.py": (
        "6668f57f7b76206e94d074ff9d0d8059c78f03f1cbb23ae82e6fdac52a287262"
    ),
    "g001_remaining_witness_solver.cpp": (
        "b741e28729da7c771a2129a9439e0f921730866ddaf2357cf472c876fdbd2b57"
    ),
    "check_g001_leech_witness.cpp": (
        "802ed17b7857310fe1d220a6ef500ee7c7d5e18051f5c7b66136731f5acfb4ca"
    ),
    "test_g001_remaining_witness_solver.cpp": (
        "ecd8e59aed72ed9ac6b31dc9987a22f5343f8fceccc68c2f3bf4c32bd77b171f"
    ),
    "order18_topology_free_search.cpp": (
        "134373d19ad4b1b1dfb30595f73beabcef30fa21c19b74a652669fb7705a72d9"
    ),
    "a2_multi_edge_exact_cover.hpp": (
        "c156eae52bceef28db0df1a38d10dea253de09e5f627d0952a6bb1b9356cd813"
    ),
    "a2_multi_edge_exact_cover_optimized.hpp": (
        "5320c920e800ce2f9e2348b90d672e26cddd748b43bc02bc24b9146dedb5e48b"
    ),
    "a2_multi_edge_stronger_relaxation.hpp": (
        "e58f917a631c48f2419835d41c2b0ee164f0d24f44ba489c152b9c00cddbbd5c"
    ),
    "multi_edge_parity_coherence.hpp": (
        "af09e37c9e50fb3891bb11bbfead6d5f8299200c7abf81bc8049fb20a07d30c7"
    ),
    "verify_g001_terminal5_plan_v1.py": (
        "f409341c236a68be28b41e5bb5a9e45c3d3c60fac0125dc725baf02bf1660d98"
    ),
}

RUNTIME_SOURCE_NAMES = (
    "a2_multi_edge_exact_cover.hpp",
    "a2_multi_edge_exact_cover_optimized.hpp",
    "a2_multi_edge_stronger_relaxation.hpp",
    "check_g001_leech_witness.cpp",
    "g001_remaining_witness_solver.cpp",
    "multi_edge_parity_coherence.hpp",
    "order18_topology_free_search.cpp",
    "test_g001_remaining_witness_solver.cpp",
)


class RecomputeError(RuntimeError):
    """A fail-closed roster, execution, or evidence error."""


class FoundEvent(RuntimeError):
    """A fresh solver found and independently checked a witness."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RecomputeError(message)


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def require_hash(path: Path, expected: str, label: str) -> None:
    require(path.is_file() and not path.is_symlink(), f"missing/non-regular {label}: {path}")
    actual = sha256_file(path)
    require(actual == expected, f"{label} SHA-256 mismatch: {actual}")


def canonical_json(value: Any) -> bytes:
    return (
        json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
            allow_nan=False,
        )
        + "\n"
    ).encode("ascii")


def reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON key: {key!r}")
        result[key] = value
    return result


def read_json(path: Path) -> Any:
    try:
        return json.loads(
            path.read_text(encoding="utf-8", errors="strict"),
            object_pairs_hook=reject_duplicate_keys,
            parse_constant=lambda value: (_ for _ in ()).throw(
                RecomputeError(f"non-finite JSON number: {value}")
            ),
        )
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise RecomputeError(f"cannot read strict JSON {path}: {exc}") from exc


def write_new(path: Path, raw: bytes) -> None:
    path.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
    with path.open("xb") as stream:
        stream.write(raw)
        stream.flush()
        os.fsync(stream.fileno())


def load_module(path: Path, name: str) -> ModuleType:
    specification = importlib.util.spec_from_file_location(name, path)
    if specification is None or specification.loader is None:
        raise RecomputeError(f"cannot load frozen module: {path}")
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


def validate_source(source_dir: Path) -> tuple[ModuleType, ModuleType]:
    source_dir = source_dir.resolve(strict=True)
    for name, expected in SOURCE_HASHES.items():
        require_hash(source_dir / name, expected, f"Terminal5 source {name}")
    terminal_common = load_module(
        source_dir / "g001_terminal5_common_v1.py",
        "_config4_fresh_terminal_common",
    )
    leaf_common = load_module(
        source_dir / "g001_remaining_leaf_common.py",
        "_config4_fresh_leaf_common",
    )
    return terminal_common, leaf_common


def assemble_roster(
    plan_path: Path, frozen_plan_path: Path, source_dir: Path
) -> tuple[dict[str, Any], list[dict[str, Any]], bytes, ModuleType]:
    terminal_common, leaf_common = validate_source(source_dir)
    require_hash(
        frozen_plan_path,
        EXPECTED_FROZEN_PLAN_SHA256,
        "canonical frozen Terminal5 plan",
    )
    raw_plan = read_json(plan_path)
    frozen_plan = read_json(frozen_plan_path)
    expected_keys = set(NON_RUNTIME_PLAN_FIELDS) | {"runtime"}
    require(
        isinstance(raw_plan, dict)
        and isinstance(frozen_plan, dict)
        and set(raw_plan) == expected_keys
        and set(frozen_plan) == expected_keys,
        "Terminal5 plan top-level field set mismatch",
    )
    for field in NON_RUNTIME_PLAN_FIELDS:
        require(
            raw_plan[field] == frozen_plan[field],
            f"fresh Terminal5 plan differs from frozen field: {field}",
        )
    try:
        plan = terminal_common.validate_plan(raw_plan, production=True)
        terminal_common.validate_plan(frozen_plan, production=True)
    except Exception as exc:
        raise RecomputeError(f"Terminal5 plan validation failed: {exc}") from exc
    require(plan["plan_id"] == EXPECTED_PLAN_ID, "Terminal5 plan_id mismatch")

    records = [
        record
        for record in plan["records"]
        if record["classification"] == "CERTIFIED_ZERO"
    ]
    require(len(records) == EXPECTED_RECORDS, "expected exactly 30 CERTIFIED_ZERO records")
    require(
        all(
            record["configuration"] == 4
            and record["mode"] == "g001_row3"
            and record["bundle_index"] is None
            for record in records
        ),
        "CERTIFIED_ZERO configuration/mode/bundle invariant mismatch",
    )

    rows: list[dict[str, Any]] = []
    for record in records:
        argv_template = terminal_common.solver_argv(
            record["configuration"], record["path"]
        )
        try:
            leaf_common.validate_argv_template(
                argv_template,
                record["configuration"],
                {"kind": "path", "indices": record["path"]},
            )
        except Exception as exc:
            raise RecomputeError(
                f"derived argv rejected for {record['record_id']}: {exc}"
            ) from exc
        rows.append(
            {
                "record_id": record["record_id"],
                "configuration": record["configuration"],
                "mode": record["mode"],
                "path": record["path"],
                "argv_template": argv_template,
            }
        )

    roster_raw = canonical_json(rows)
    require(
        len(roster_raw) == EXPECTED_ROSTER_BYTES,
        f"derived roster byte length mismatch: {len(roster_raw)}",
    )
    roster_hash = sha256_bytes(roster_raw)
    require(
        roster_hash == EXPECTED_ROSTER_SHA256,
        f"derived roster SHA-256 mismatch: {roster_hash}",
    )
    require(
        len({tuple(row["path"]) for row in rows}) == EXPECTED_RECORDS,
        "derived roster contains duplicate paths",
    )
    return plan, rows, roster_raw, leaf_common


def print_roster(
    rows: Sequence[Mapping[str, Any]], plan_path: Path, frozen_plan_path: Path
) -> None:
    for index, row in enumerate(rows):
        argv = json.dumps(
            row["argv_template"],
            separators=(",", ":"),
            ensure_ascii=True,
        )
        print(
            f"index={index:02d} record_id={row['record_id']} "
            f"configuration=4 mode=g001_row3 path={','.join(map(str, row['path']))} "
            f"argv_template={argv}"
        )
    print(
        "LEECH18_CONFIG4_CERTIFIED_ZERO_ROSTER_OK "
        f"records={EXPECTED_RECORDS} configuration=4 mode=g001_row3 "
        f"bytes={EXPECTED_ROSTER_BYTES} roster_sha256={EXPECTED_ROSTER_SHA256} "
        f"plan_sha256={sha256_file(plan_path)} "
        f"frozen_plan_sha256={sha256_file(frozen_plan_path)}"
    )


def make_leaf_plan(
    plan: Mapping[str, Any], rows: Sequence[Mapping[str, Any]]
) -> dict[str, Any]:
    bindings = plan["runtime"]["bindings"]
    leaves = []
    for row in rows:
        leaves.append(
            {
                "leaf_id": row["record_id"],
                "configuration": row["configuration"],
                "mode": row["mode"],
                "selector": {"kind": "path", "indices": row["path"]},
                "argv_template": row["argv_template"],
                "timeout_seconds": 0,
                "artifacts": {
                    "solver_source": bindings["solver_source"],
                    "solver_executable": bindings["solver_executable"],
                    "checker_source": bindings["checker_source"],
                    "checker_executable": bindings["checker_executable"],
                    "dependencies": [
                        {
                            "role": "terminal5_runtime_freeze",
                            "path": bindings["runtime_freeze"]["path"],
                            "sha256": bindings["runtime_freeze"]["sha256"],
                        }
                    ],
                },
            }
        )
    return {
        "schema": "G001_REMAINING_LEAF_PLAN_V1",
        "plan_id": plan["plan_id"] + ".config4-certified-zero-fresh",
        "pipeline_artifacts": plan["runtime"]["pipeline_artifacts"],
        "leaves": leaves,
    }


def resolve_binding(workspace: Path, binding: Mapping[str, Any], label: str) -> Path:
    relative = binding.get("path")
    digest = binding.get("sha256")
    require(isinstance(relative, str) and relative, f"{label} path is invalid")
    require(isinstance(digest, str) and len(digest) == 64, f"{label} hash is invalid")
    candidate = (workspace / relative).resolve(strict=True)
    try:
        candidate.relative_to(workspace)
    except ValueError as exc:
        raise RecomputeError(f"{label} resolves outside workspace") from exc
    require(candidate.is_file() and not candidate.is_symlink(), f"{label} is not a regular file")
    require(sha256_file(candidate) == digest, f"{label} binding hash mismatch")
    return candidate


def validate_execution_boundary(
    plan: Mapping[str, Any],
    plan_path: Path,
    workspace: Path,
    source_dir: Path,
) -> tuple[bytes, bytes]:
    try:
        source_relative = source_dir.relative_to(workspace).as_posix()
    except ValueError as exc:
        raise RecomputeError("--source-dir must be inside --workspace") from exc

    bindings = plan["runtime"]["bindings"]
    pipeline = plan["runtime"]["pipeline_artifacts"]
    expected_source_paths = {
        "solver_source": source_dir / "g001_remaining_witness_solver.cpp",
        "checker_source": source_dir / "check_g001_leech_witness.cpp",
        "leaf_worker": source_dir / "g001_remaining_leaf_worker.py",
        "leaf_common": source_dir / "g001_remaining_leaf_common.py",
        "leaf_collector": source_dir / "g001_remaining_leaf_collect.py",
    }
    for role in ("solver_source", "checker_source"):
        require(
            resolve_binding(workspace, bindings[role], role)
            == expected_source_paths[role].resolve(strict=True),
            f"{role} is not the supplied frozen source file",
        )
    for role in ("leaf_worker", "leaf_common", "leaf_collector"):
        require(
            resolve_binding(workspace, pipeline[role], role)
            == expected_source_paths[role].resolve(strict=True),
            f"{role} is not the supplied frozen pipeline file",
        )

    runtime_freeze_path = resolve_binding(
        workspace, bindings["runtime_freeze"], "runtime_freeze"
    )
    runtime_freeze = read_json(runtime_freeze_path)
    require(isinstance(runtime_freeze, dict), "runtime freeze must be an object")
    require(
        runtime_freeze.get("schema") == "G001_TERMINAL5_RUNTIME_FREEZE_V1",
        "runtime freeze schema mismatch",
    )
    require(
        runtime_freeze.get("source_relative_to_workspace") == source_relative,
        "runtime freeze source directory mismatch",
    )
    try:
        runtime_relative = runtime_freeze_path.parent.relative_to(workspace).as_posix()
    except ValueError as exc:
        raise RecomputeError("runtime freeze directory escapes workspace") from exc
    require(
        runtime_freeze.get("runtime_relative_to_workspace") == runtime_relative,
        "runtime freeze directory identity mismatch",
    )
    require(
        runtime_freeze.get("scientific_core_matches_calibration") is True,
        "runtime scientific core is not calibration-matched",
    )
    require(
        runtime_freeze.get("compile_flags")
        == ["-O2", "-std=c++20", "-Wall", "-Wextra", "-Wpedantic", "-Werror"],
        "runtime compile flags mismatch",
    )
    require(
        runtime_freeze.get("tests")
        == {"checker_self_test_checks": 11, "witness_regression_checks": 45},
        "runtime test-count mismatch",
    )
    require(
        runtime_freeze.get("terminal_policy")
        == {
            "depth_cap": None,
            "independent_checker_required": True,
            "node_cap": None,
            "stop_depth": None,
            "witness_required_before_found_exit": True,
        },
        "runtime terminal policy mismatch",
    )

    expected_sources = {
        name: {
            "path": (source_dir / name).relative_to(workspace).as_posix(),
            "sha256": SOURCE_HASHES[name],
        }
        for name in RUNTIME_SOURCE_NAMES
    }
    require(runtime_freeze.get("sources") == expected_sources, "runtime source roster mismatch")
    binaries = runtime_freeze.get("binaries")
    require(isinstance(binaries, dict), "runtime binaries roster is missing")
    for role, binary_name in (
        ("solver_executable", "g001_remaining_witness_solver"),
        ("checker_executable", "check_g001_leech_witness"),
    ):
        bound = resolve_binding(workspace, bindings[role], role)
        binary = binaries.get(binary_name)
        require(isinstance(binary, dict), f"runtime binary record missing: {binary_name}")
        require(binary.get("sha256") == bindings[role]["sha256"], f"{role} runtime hash mismatch")
        require(
            bound == (runtime_freeze_path.parent / binary.get("path", "")).resolve(strict=True),
            f"{role} runtime path mismatch",
        )

    verifier = source_dir / "verify_g001_terminal5_plan_v1.py"
    completed = subprocess.run(
        [
            sys.executable,
            "-B",
            str(verifier),
            "--plan-dir",
            str(plan_path.parent),
            "--workspace",
            str(workspace),
            "--source-dir",
            str(source_dir),
        ],
        cwd=str(workspace),
        env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    require(completed.returncode == 0, "authoritative Terminal5 plan/runtime verifier failed")
    require(completed.stderr == b"", "authoritative Terminal5 verifier wrote stderr")
    expected_stdout = (
        "G001_TERMINAL5_PLAN_V1_VERIFIED records=39030 search=39000 zero=30 "
        f"bundles=192 sha256={sha256_file(plan_path)}\n"
    ).encode("ascii")
    require(
        completed.stdout == expected_stdout,
        "authoritative Terminal5 verifier stdout is not the exact expected marker",
    )
    return completed.stdout, completed.stderr


def terminate_processes(processes: Mapping[int, subprocess.Popen[bytes]]) -> None:
    for process in processes.values():
        if process.poll() is None:
            process.terminate()
    deadline = time.monotonic() + 35.0
    while any(process.poll() is None for process in processes.values()):
        if time.monotonic() >= deadline:
            for process in processes.values():
                if process.poll() is None:
                    process.kill()
            break
        time.sleep(0.1)
    for process in processes.values():
        try:
            process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            process.kill()
            process.wait()


def run_worker_wave(
    indices: Sequence[int],
    worker: Path,
    leaf_plan_path: Path,
    workspace: Path,
    leaf_run: Path,
    log_dir: Path,
) -> tuple[int, int] | None:
    processes: dict[int, subprocess.Popen[bytes]] = {}
    streams: dict[int, tuple[Any, Any]] = {}
    try:
        for index in indices:
            stdout = (log_dir / f"worker_{index:02d}.stdout.txt").open("xb")
            stderr = (log_dir / f"worker_{index:02d}.stderr.txt").open("xb")
            streams[index] = (stdout, stderr)
            command = [
                sys.executable,
                "-B",
                str(worker),
                "--plan",
                str(leaf_plan_path),
                "--workspace",
                str(workspace),
                "--run-dir",
                str(leaf_run),
                "--index",
                str(index),
                "--kill-grace-seconds",
                "30",
            ]
            processes[index] = subprocess.Popen(
                command,
                cwd=str(workspace),
                env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
                stdin=subprocess.DEVNULL,
                stdout=stdout,
                stderr=stderr,
                start_new_session=True,
            )

        pending = set(indices)
        failure: tuple[int, int] | None = None
        while pending and failure is None:
            progressed = False
            for index in list(pending):
                return_code = processes[index].poll()
                if return_code is None:
                    continue
                progressed = True
                pending.remove(index)
                streams[index][0].close()
                streams[index][1].close()
                if return_code != 0:
                    failure = (index, return_code)
                    break
            if not progressed and failure is None:
                time.sleep(0.1)
        if failure is not None:
            terminate_processes({index: processes[index] for index in pending})
            return failure
        return None
    finally:
        live = {
            index: process
            for index, process in processes.items()
            if process.poll() is None
        }
        if live:
            terminate_processes(live)
        for stdout, stderr in streams.values():
            if not stdout.closed:
                stdout.close()
            if not stderr.closed:
                stderr.close()


def run_collector(
    collector: Path,
    leaf_plan_path: Path,
    workspace: Path,
    leaf_run: Path,
    output: Path,
    log_prefix: Path,
    *,
    index: int | None = None,
) -> int:
    selection = ["--all"] if index is None else ["--index", str(index)]
    completed = subprocess.run(
        [
            sys.executable,
            "-B",
            str(collector),
            "--plan",
            str(leaf_plan_path),
            "--workspace",
            str(workspace),
            "--run-dir",
            str(leaf_run),
            *selection,
            "--output",
            str(output),
        ],
        cwd=str(workspace),
        env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    write_new(log_prefix.with_suffix(".stdout.txt"), completed.stdout)
    write_new(log_prefix.with_suffix(".stderr.txt"), completed.stderr)
    return completed.returncode


def validate_collection(
    collection: Any,
    rows: Sequence[Mapping[str, Any]],
    leaf_plan_hash: str,
) -> tuple[int, list[dict[str, Any]]]:
    require(isinstance(collection, dict), "fresh collection must be an object")
    require(
        collection.get("schema") == "G001_REMAINING_LEAF_COLLECTION_V1",
        "fresh collection schema mismatch",
    )
    require(collection.get("plan_sha256") == leaf_plan_hash, "leaf-plan hash mismatch")
    records = collection.get("records")
    require(
        isinstance(records, list) and len(records) == EXPECTED_RECORDS,
        "collection count mismatch",
    )
    summaries: list[dict[str, Any]] = []
    nodes_sum = 0
    for index, (record, row) in enumerate(zip(records, rows)):
        require(isinstance(record, dict), f"collection record {index} is not an object")
        require(record.get("leaf_index") == index, f"leaf index mismatch at {index}")
        require(record.get("leaf_id") == row["record_id"], f"leaf id mismatch at {index}")
        require(record.get("configuration") == 4, f"configuration mismatch at {index}")
        require(record.get("mode") == "g001_row3", f"mode mismatch at {index}")
        require(
            record.get("selector") == {"kind": "path", "indices": row["path"]},
            f"selector mismatch at {index}",
        )
        require(record.get("outcome") == "ZERO", f"non-ZERO outcome at {index}")
        require(record.get("solver_exit_code") == 0, f"solver exit mismatch at {index}")
        result = record.get("solver_result")
        require(isinstance(result, dict), f"missing solver result at {index}")
        require(result.get("status") == "ZERO", f"status mismatch at {index}")
        require(int(result.get("frontier", "-1")) == 0, f"frontier mismatch at {index}")
        require(
            int(result.get("solution_topologies", "-1")) == 0,
            f"solution count mismatch at {index}",
        )
        nodes = int(result.get("nodes", "-1"))
        require(nodes >= 0, f"invalid node count at {index}")
        nodes_sum += nodes
        summaries.append(
            {
                "record_id": row["record_id"],
                "path": row["path"],
                "nodes": nodes,
                "argv_sha256": record.get("argv_sha256"),
                "marker_sha256": record.get("marker_sha256"),
            }
        )
    return nodes_sum, summaries


def recompute(
    plan_path: Path,
    frozen_plan_path: Path,
    source_dir: Path,
    workspace_path: Path | None,
    run_root_path: Path,
    workers: int,
) -> None:
    require(os.name == "posix" and sys.platform.startswith("linux"), "Linux is required")
    require(workspace_path is not None, "--workspace is required with --run-root")
    require(workers == EXPECTED_WORKERS, "exactly 15 workers are required")

    workspace = workspace_path.resolve(strict=True)
    source_dir = source_dir.resolve(strict=True)
    plan_path = plan_path.resolve(strict=True)
    frozen_plan_path = frozen_plan_path.resolve(strict=True)
    run_root = Path(os.path.abspath(os.fspath(run_root_path)))
    require(not os.path.lexists(run_root), f"run root already exists: {run_root}")
    require(run_root.parent.is_dir(), f"run-root parent is missing: {run_root.parent}")

    plan, rows, roster_raw, leaf_common = assemble_roster(
        plan_path, frozen_plan_path, source_dir
    )
    verifier_stdout, verifier_stderr = validate_execution_boundary(
        plan, plan_path, workspace, source_dir
    )
    run_root.mkdir(mode=0o700)
    leaf_run = run_root / "leaf_runs"
    log_dir = run_root / "logs"
    leaf_run.mkdir(mode=0o700)
    log_dir.mkdir(mode=0o700)
    verifier_stdout_path = log_dir / "authoritative_plan_verifier.stdout.txt"
    verifier_stderr_path = log_dir / "authoritative_plan_verifier.stderr.txt"
    write_new(verifier_stdout_path, verifier_stdout)
    write_new(verifier_stderr_path, verifier_stderr)
    roster_path = run_root / "CONFIG4_CERTIFIED_ZERO_ROSTER.json"
    write_new(roster_path, roster_raw)

    leaf_plan_path = run_root / "CONFIG4_CERTIFIED_ZERO_LEAF_PLAN.json"
    write_new(leaf_plan_path, canonical_json(make_leaf_plan(plan, rows)))
    try:
        loaded_leaf_plan, leaf_plan_hash = leaf_common.load_plan(leaf_plan_path)
    except Exception as exc:
        raise RecomputeError(f"supplemental leaf plan validation failed: {exc}") from exc
    require(len(loaded_leaf_plan["leaves"]) == EXPECTED_RECORDS, "supplemental leaf count mismatch")

    worker = source_dir / "g001_remaining_leaf_worker.py"
    collector = source_dir / "g001_remaining_leaf_collect.py"
    for wave_start in range(0, EXPECTED_RECORDS, workers):
        indices = list(range(wave_start, min(wave_start + workers, EXPECTED_RECORDS)))
        failure = run_worker_wave(
            indices, worker, leaf_plan_path, workspace, leaf_run, log_dir
        )
        if failure is None:
            continue
        index, return_code = failure
        if return_code == 2:
            found_output = run_root / "VERIFIED_FOUND_COLLECTION.json"
            collector_code = run_collector(
                collector,
                leaf_plan_path,
                workspace,
                leaf_run,
                found_output,
                log_dir / "found_collector",
                index=index,
            )
            require(collector_code == 2, "FOUND collector did not return exit 2")
            raise FoundEvent(
                f"record={rows[index]['record_id']} path={','.join(map(str, rows[index]['path']))} "
                f"evidence={found_output}"
            )
        raise RecomputeError(
            f"worker {index} exited {return_code}; see {log_dir / f'worker_{index:02d}.stderr.txt'}"
        )

    collection_path = run_root / "FRESH_COLLECTION.json"
    collector_code = run_collector(
        collector,
        leaf_plan_path,
        workspace,
        leaf_run,
        collection_path,
        log_dir / "collector",
    )
    require(collector_code == 0, f"fresh collector exited {collector_code}")
    nodes_sum, record_summaries = validate_collection(
        read_json(collection_path), rows, leaf_plan_hash
    )

    terminal_plan_hash = sha256_file(plan_path)
    summary = {
        "schema": "LEECH18_CONFIG4_CERTIFIED_ZERO_FRESH_RECOMPUTATION_V1",
        "status": "ZERO_COMPLETE",
        "configuration": 4,
        "mode": "g001_row3",
        "prior_classification": "CERTIFIED_ZERO",
        "fresh_terminal_searches": EXPECTED_RECORDS,
        "fresh_zero_results": EXPECTED_RECORDS,
        "workers": workers,
        "terminal_plan_id": plan["plan_id"],
        "terminal_plan_sha256": terminal_plan_hash,
        "frozen_terminal_plan_sha256": sha256_file(frozen_plan_path),
        "non_runtime_plan_fields_match_frozen": True,
        "authoritative_plan_runtime_verified": True,
        "derived_roster_bytes": EXPECTED_ROSTER_BYTES,
        "derived_roster_sha256": EXPECTED_ROSTER_SHA256,
        "supplemental_nodes": nodes_sum,
        "reported_terminal5_nodes_excluding_supplemental": 7_964_472_779,
        "node_accounting_note": (
            "supplemental nodes are fresh audit work and are not added to the paper's "
            "reported production-node total"
        ),
        "leaf_plan_sha256": leaf_plan_hash,
        "fresh_collection_sha256": sha256_file(collection_path),
        "authoritative_plan_verifier_stdout_sha256": sha256_file(
            verifier_stdout_path
        ),
        "authoritative_plan_verifier_stderr_sha256": sha256_file(
            verifier_stderr_path
        ),
        "records": record_summaries,
    }
    write_new(run_root / "RECOMPUTATION_SUMMARY.json", canonical_json(summary))
    print(
        "LEECH18_CONFIG4_CERTIFIED_ZERO_FULL_RECOMPUTATION_OK "
        f"fresh_search={EXPECTED_RECORDS} configuration=4 zero={EXPECTED_RECORDS} "
        f"nodes={nodes_sum} roster_sha256={EXPECTED_ROSTER_SHA256}"
    )


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    selection = parser.add_mutually_exclusive_group(required=True)
    selection.add_argument("--list-only", action="store_true")
    selection.add_argument("--run-root", type=Path)
    parser.add_argument("--plan", type=Path, default=DEFAULT_PLAN)
    parser.add_argument("--frozen-plan", type=Path, default=DEFAULT_PLAN)
    parser.add_argument("--source-dir", type=Path, default=DEFAULT_SOURCE)
    parser.add_argument("--workspace", type=Path)
    parser.add_argument("--workers", type=int, default=EXPECTED_WORKERS)
    args = parser.parse_args(argv)
    try:
        plan_path = args.plan.resolve(strict=True)
        frozen_plan_path = args.frozen_plan.resolve(strict=True)
        source_dir = args.source_dir.resolve(strict=True)
        if args.list_only:
            _plan, rows, _roster_raw, _leaf_common = assemble_roster(
                plan_path, frozen_plan_path, source_dir
            )
            print_roster(rows, plan_path, frozen_plan_path)
        else:
            recompute(
                plan_path,
                frozen_plan_path,
                source_dir,
                args.workspace,
                args.run_root,
                args.workers,
            )
        return 0
    except FoundEvent as exc:
        print(f"LEECH18_CONFIG4_CERTIFIED_ZERO_FOUND: {exc}", file=sys.stderr)
        return 2
    except (RecomputeError, OSError, ValueError, KeyError, TypeError) as exc:
        print(f"LEECH18_CONFIG4_CERTIFIED_ZERO_RECOMPUTATION_FAIL: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
