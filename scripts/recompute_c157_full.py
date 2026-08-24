#!/usr/bin/env python3
"""Rebuild and recompute the C157 depth-12 calibration partition.

This public driver does not consume a preserved C157 result archive.  It uses
the frozen terminal-plan paths as a deterministic partition specification,
rebuilds the authoritative shallow solver, checks every internal fanout, and
recomputes every depth-12 frontier value.  A timeout, malformed selector,
missing child, nonzero exit, stderr byte, or value mismatch is a failure.
"""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
from typing import Dict, Iterable, List, Mapping, Optional, Sequence, Set, Tuple


SCHEMA = "leech18-c157-fresh-recomputation-v1"
STATUS = "C157_FRESH_RECOMPUTATION_COMPLETE"
PLAN_SHA256 = "b317a3b7cef71e11fea762ce5e70322f168e06c6e04b97293f066cb2e313bdae"
EXPECTED_WORKLOAD_SHA256 = (
    "8f8812263d5ca90903b0b4ed9f52ddc2e8f1d51d635445f0ea2755f6d35179b8"
)
HISTORICAL_SOLVER_SHA256 = (
    "bce4c2766fb9aedc942aaca7127eafac5c983e552d61266d882b87f2260f1147"
)
SOURCE_HASHES = {
    "a2_multi_edge_exact_cover.hpp":
        "c156eae52bceef28db0df1a38d10dea253de09e5f627d0952a6bb1b9356cd813",
    "a2_multi_edge_exact_cover_optimized.hpp":
        "5320c920e800ce2f9e2348b90d672e26cddd748b43bc02bc24b9146dedb5e48b",
    "a2_multi_edge_stronger_relaxation.hpp":
        "e58f917a631c48f2419835d41c2b0ee164f0d24f44ba489c152b9c00cddbbd5c",
    "audit_g001_remaining_seed_orbits.cpp":
        "442d19b5b84057a5d18d3b0395bde006a07b24814d0bf007bce9ccfc5b51f128",
    "g001_remaining_shallow_pilot.cpp":
        "fcaef4a8104204348a920926e65c1f6209ef16af1d723b28c4df5a9a499a1822",
    "multi_edge_parity_coherence.hpp":
        "af09e37c9e50fb3891bb11bbfead6d5f8299200c7abf81bc8049fb20a07d30c7",
    "order18_topology_free_search.cpp":
        "134373d19ad4b1b1dfb30595f73beabcef30fa21c19b74a652669fb7705a72d9",
    "verify_g001_remaining_shallow_pilot.py":
        "1ed169b8409962b9fd641b013daab34c7eb1456ba82b6853e3667542e94eb9fb",
}
PRODUCTION_FLAGS = (
    "--multi-edge-cover",
    "--multi-edge-cover-no-hall",
    "--multi-edge-cover-max-components", "6",
    "--multi-edge-cover-budget", "100",
    "--multi-edge-cover-no-exact-hall",
    "--multi-edge-cover-exact-max-components", "6",
)
CONFIGURATIONS = {
    1: {
        "mode": "g001_row0", "leaf_count": 5176,
        "internal_prefix_count": 287, "omitted_zero_child_count": 26,
        "planned_zero_leaf_count": 153, "gate_zero_child_count": 26,
        "frontier_sum": 20045473,
    },
    5: {
        "mode": "g001_row4", "leaf_count": 25254,
        "internal_prefix_count": 1460, "omitted_zero_child_count": 430,
        "planned_zero_leaf_count": 378, "gate_zero_child_count": 430,
        "frontier_sum": 74092284,
    },
    6: {
        "mode": "g001_row5", "leaf_count": 3977,
        "internal_prefix_count": 213, "omitted_zero_child_count": 6,
        "planned_zero_leaf_count": 155, "gate_zero_child_count": 6,
        "frontier_sum": 18016722,
    },
    7: {
        "mode": "g001_row6", "leaf_count": 3299,
        "internal_prefix_count": 175, "omitted_zero_child_count": 2,
        "planned_zero_leaf_count": 127, "gate_zero_child_count": 2,
        "frontier_sum": 15688080,
    },
}
EXPECTED_LEAVES = 37706
EXPECTED_INTERNAL_PREFIXES = 2135
EXPECTED_ZERO_CHILDREN = 464
EXPECTED_PLANNED_ZERO_LEAVES = 813
EXPECTED_GATE_ZERO_CHILDREN = EXPECTED_ZERO_CHILDREN
EXPECTED_PLANNED_CHILDREN = EXPECTED_LEAVES + EXPECTED_INTERNAL_PREFIXES - 4
EXPECTED_CHILD_GATES = EXPECTED_PLANNED_CHILDREN + EXPECTED_ZERO_CHILDREN
EXPECTED_VIABLE_CHILDREN = EXPECTED_PLANNED_CHILDREN
EXPECTED_INVOCATIONS = (
    EXPECTED_LEAVES + EXPECTED_INTERNAL_PREFIXES + EXPECTED_CHILD_GATES
)

SCRIPT_PATH = Path(__file__).resolve()
SCRIPTS_DIR = SCRIPT_PATH.parent
REPO_ROOT = SCRIPTS_DIR.parent
DEFAULT_SOURCE_DIR = SCRIPTS_DIR / "c157" / "source"
DEFAULT_PLAN = (
    REPO_ROOT / "computation" / "evidence" / "production" /
    "exact_final_workspace" / "plan" /
    "terminal5_plan_v1" / "terminal_plan_v1.json"
)
SOURCE_MANIFEST = SCRIPTS_DIR / "c157" / "SOURCE_MANIFEST.sha256"

ACTIVE_LOCK = threading.Lock()
ACTIVE: Set[subprocess.Popen] = set()
STOP = threading.Event()


class RecomputeError(RuntimeError):
    pass


PathTuple = Tuple[int, ...]


@dataclass(frozen=True)
class Leaf:
    configuration: int
    mode: str
    path: PathTuple
    frontier: int
    record_id: str


@dataclass(frozen=True)
class Task:
    kind: str
    configuration: int
    mode: str
    path: PathTuple
    stop_edges: int

    def arguments(self) -> List[str]:
        result = ["--mode", self.mode]
        if self.path:
            result += ["--branch-path", ",".join(map(str, self.path))]
        result += ["--stop-edges", str(self.stop_edges)]
        result += PRODUCTION_FLAGS
        return list(result)

    def identity(self) -> Mapping[str, object]:
        return {
            "configuration": self.configuration,
            "kind": self.kind,
            "mode": self.mode,
            "path": list(self.path),
            "stop_edges": self.stop_edges,
            "arguments": self.arguments(),
        }

    def task_id(self) -> str:
        return hashlib.sha256(canonical_bytes(self.identity())).hexdigest()[:32]


@dataclass
class Workload:
    leaves: List[Leaf]
    internal: Dict[int, List[PathTuple]]
    children: Dict[Tuple[int, PathTuple], Set[int]]
    internal_sets: Dict[int, Set[PathTuple]]
    leaf_frontiers: Dict[Tuple[int, PathTuple], int]
    canonical: Mapping[str, object]
    sha256: str


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def canonical_bytes(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True) + "\n").encode("utf-8")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def atomic_bytes(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(prefix=path.name + ".",
                                              dir=str(path.parent))
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    except BaseException:
        try:
            os.unlink(temporary)
        except OSError:
            pass
        raise


def atomic_json(path: Path, value: object) -> None:
    atomic_bytes(path, json.dumps(value, indent=2, sort_keys=True,
                                  ensure_ascii=True).encode("utf-8") + b"\n")


def pretty_json_bytes(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True,
                       ensure_ascii=True).encode("utf-8") + b"\n")


def recorded_basename(value: object) -> str:
    if not isinstance(value, str) or not value:
        return ""
    return value.replace("\\", "/").rsplit("/", 1)[-1]


def verify_workload_record(work_dir: Path, workload: Workload) -> str:
    path = work_dir / "WORKLOAD.json"
    if not path.is_file():
        raise RecomputeError("WORKLOAD.json is missing")
    expected = pretty_json_bytes(workload.canonical)
    if path.read_bytes() != expected:
        raise RecomputeError("WORKLOAD.json is not the exact canonical workload")
    return sha256(path)


def verify_sources(source_dir: Path) -> str:
    if not SOURCE_MANIFEST.is_file():
        raise RecomputeError("missing SOURCE_MANIFEST.sha256")
    expected_names = set(SOURCE_HASHES)
    actual_names = {item.name for item in source_dir.iterdir() if item.is_file()}
    if actual_names != expected_names:
        missing = sorted(expected_names - actual_names)
        extra = sorted(actual_names - expected_names)
        raise RecomputeError(
            "source exact-set mismatch missing={} extra={}".format(missing, extra)
        )
    for name, expected in SOURCE_HASHES.items():
        actual = sha256(source_dir / name)
        if actual != expected:
            raise RecomputeError(
                "source hash mismatch for {}: {} != {}".format(
                    name, actual, expected)
            )
    manifest_lines = []
    for name in sorted(SOURCE_HASHES):
        manifest_lines.append("{}  source/{}".format(SOURCE_HASHES[name], name))
    expected_manifest = "\n".join(manifest_lines) + "\n"
    if SOURCE_MANIFEST.read_text(encoding="utf-8") != expected_manifest:
        raise RecomputeError("SOURCE_MANIFEST.sha256 bytes are noncanonical")
    return sha256(SOURCE_MANIFEST)


def check_prefix_free(paths: Sequence[PathTuple], configuration: int) -> None:
    ordered = sorted(paths)
    if len(set(ordered)) != len(ordered):
        raise RecomputeError("duplicate path in Configuration {}".format(configuration))
    for first, second in zip(ordered, ordered[1:]):
        if len(first) <= len(second) and second[:len(first)] == first:
            raise RecomputeError(
                "prefix overlap in Configuration {}: {} / {}".format(
                    configuration, first, second)
            )


def load_workload(plan_path: Path) -> Workload:
    if not plan_path.is_file():
        raise RecomputeError("terminal plan not found: {}".format(plan_path))
    actual_hash = sha256(plan_path)
    if actual_hash != PLAN_SHA256:
        raise RecomputeError(
            "terminal plan hash mismatch: {} != {}".format(actual_hash, PLAN_SHA256)
        )
    try:
        plan = json.loads(plan_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise RecomputeError("cannot read terminal plan: {}".format(error)) from error
    if plan.get("schema") != "G001_TERMINAL5_PLAN_V1":
        raise RecomputeError("unexpected terminal plan schema")
    raw_records = plan.get("records")
    if not isinstance(raw_records, list):
        raise RecomputeError("terminal plan records are missing")

    leaves: List[Leaf] = []
    by_configuration: Dict[int, List[Leaf]] = {key: [] for key in CONFIGURATIONS}
    for record in raw_records:
        if (not isinstance(record, dict) or
                record.get("classification") != "SEARCH" or
                record.get("configuration") not in CONFIGURATIONS):
            continue
        configuration = int(record["configuration"])
        mode = CONFIGURATIONS[configuration]["mode"]
        if record.get("mode") != mode:
            raise RecomputeError("record mode/configuration mismatch")
        raw_path = record.get("path")
        if (not isinstance(raw_path, list) or not 2 <= len(raw_path) <= 7 or
                any(not isinstance(item, int) or item < 0 for item in raw_path)):
            raise RecomputeError("invalid C157 partition path")
        path = tuple(raw_path)
        if record.get("path_text") != ",".join(map(str, path)):
            raise RecomputeError("path/path_text mismatch")
        frontier = record.get("weight")
        if not isinstance(frontier, int) or frontier < 0:
            raise RecomputeError("invalid calibration frontier")
        evidence = record.get("evidence")
        if (not isinstance(evidence, dict) or evidence.get("source") != "C157" or
                evidence.get("calibration_depth") != 12 or
                evidence.get("calibration_frontier") != frontier):
            raise RecomputeError("C157 evidence descriptor mismatch")
        record_id = record.get("record_id")
        if not isinstance(record_id, str) or not record_id:
            raise RecomputeError("missing record_id")
        leaf = Leaf(configuration, mode, path, frontier, record_id)
        leaves.append(leaf)
        by_configuration[configuration].append(leaf)

    if len(leaves) != EXPECTED_LEAVES:
        raise RecomputeError("C157 leaf count mismatch")
    internal: Dict[int, List[PathTuple]] = {}
    internal_sets: Dict[int, Set[PathTuple]] = {}
    children: Dict[Tuple[int, PathTuple], Set[int]] = {}
    leaf_frontiers: Dict[Tuple[int, PathTuple], int] = {}
    canonical_configurations: Dict[str, object] = {}
    for configuration, expected in CONFIGURATIONS.items():
        selected = by_configuration[configuration]
        paths = [leaf.path for leaf in selected]
        check_prefix_free(paths, configuration)
        prefixes: Set[PathTuple] = set()
        for path in paths:
            for length in range(len(path)):
                prefix = path[:length]
                prefixes.add(prefix)
                children.setdefault((configuration, prefix), set()).add(path[length])
        ordered_prefixes = sorted(prefixes, key=lambda item: (len(item), item))
        internal[configuration] = ordered_prefixes
        internal_sets[configuration] = prefixes
        for leaf in selected:
            leaf_frontiers[(configuration, leaf.path)] = leaf.frontier
        actual = {
            "leaf_count": len(selected),
            "internal_prefix_count": len(prefixes),
            "frontier_sum": sum(leaf.frontier for leaf in selected),
            "planned_zero_leaf_count": sum(leaf.frontier == 0 for leaf in selected),
        }
        for key in actual:
            if actual[key] != expected[key]:
                raise RecomputeError(
                    "Configuration {} {} mismatch".format(configuration, key)
                )
        canonical_configurations[str(configuration)] = {
            "mode": expected["mode"],
            "leaves": [
                {"frontier": leaf.frontier, "path": list(leaf.path),
                 "record_id": leaf.record_id}
                for leaf in sorted(selected, key=lambda item: item.path)
            ],
            "internal_prefixes": [list(path) for path in ordered_prefixes],
        }
    if sum(len(value) for value in internal.values()) != EXPECTED_INTERNAL_PREFIXES:
        raise RecomputeError("internal prefix count mismatch")
    canonical = {
        "configurations": canonical_configurations,
        "plan_sha256": PLAN_SHA256,
        "production_flags": list(PRODUCTION_FLAGS),
        "schema": "leech18-c157-fresh-workload-v1",
    }
    workload_hash = hashlib.sha256(canonical_bytes(canonical)).hexdigest()
    if workload_hash != EXPECTED_WORKLOAD_SHA256:
        raise RecomputeError("deterministic C157 workload digest mismatch")
    return Workload(
        leaves, internal, children, internal_sets, leaf_frontiers,
        canonical, workload_hash)


def resolve_compiler(value: str) -> Path:
    candidate = Path(value)
    if candidate.parent != Path(".") or candidate.is_absolute():
        resolved = candidate.expanduser().resolve()
        if not resolved.is_file():
            raise RecomputeError("compiler not found: {}".format(value))
        return resolved
    found = shutil.which(value)
    if found is None:
        raise RecomputeError("compiler not found on PATH: {}".format(value))
    return Path(found).resolve()


def compiler_version(compiler: Path) -> str:
    completed = subprocess.run(
        [str(compiler), "--version"], stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, check=False,
    )
    if completed.returncode != 0:
        raise RecomputeError("compiler --version failed")
    raw = completed.stdout + completed.stderr
    try:
        value = raw.decode("utf-8", errors="strict").strip()
    except UnicodeError as error:
        raise RecomputeError("compiler version is not UTF-8") from error
    if not value:
        raise RecomputeError("compiler version is empty")
    return value


def executable_name(base: str) -> str:
    return base + (".exe" if os.name == "nt" else "")


def build_binaries(source_dir: Path, build_dir: Path,
                   compiler: Path, reuse: bool = False
                   ) -> Tuple[Path, Path, Mapping[str, object]]:
    build_dir.mkdir(parents=True, exist_ok=True)
    solver = build_dir / executable_name("g001_remaining_shallow_pilot")
    oracle = build_dir / executable_name("audit_g001_remaining_seed_orbits")
    flags = ["-O2", "-std=c++20", "-Wall", "-Wextra", "-Wpedantic", "-Werror"]
    build_record = build_dir / "BUILD.json"
    if reuse and build_record.is_file():
        try:
            metadata = json.loads(build_record.read_text(encoding="utf-8"))
        except (OSError, UnicodeError, json.JSONDecodeError) as error:
            raise RecomputeError("cannot read cached BUILD.json") from error
        if (metadata.get("compiler") != str(compiler) or
                metadata.get("compiler_version") != compiler_version(compiler) or
                metadata.get("flags") != flags or
                not solver.is_file() or not oracle.is_file() or
                metadata.get("solver_sha256") != sha256(solver) or
                metadata.get("oracle_sha256") != sha256(oracle) or
                metadata.get("historical_solver_sha256") !=
                HISTORICAL_SOLVER_SHA256):
            raise RecomputeError("cached build binding mismatch")
        return solver, oracle, metadata
    commands = [
        (source_dir / "g001_remaining_shallow_pilot.cpp", solver),
        (source_dir / "audit_g001_remaining_seed_orbits.cpp", oracle),
    ]
    compile_records = []
    for source, output in commands:
        command = [str(compiler)] + flags + [str(source), "-o", str(output)]
        completed = subprocess.run(
            command, cwd=str(source_dir), stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, check=False,
        )
        label = output.stem
        atomic_bytes(build_dir / (label + ".compile.stdout.txt"), completed.stdout)
        atomic_bytes(build_dir / (label + ".compile.stderr.txt"), completed.stderr)
        if completed.returncode != 0:
            raise RecomputeError("compile failed for {}".format(source.name))
        if not output.is_file():
            raise RecomputeError("compiler did not create {}".format(output))
        compile_records.append({
            "command": command,
            "output": output.name,
            "sha256": sha256(output),
            "source": source.name,
        })
    metadata = {
        "commands": compile_records,
        "compiler": str(compiler),
        "compiler_version": compiler_version(compiler),
        "flags": flags,
        "historical_solver_sha256": HISTORICAL_SOLVER_SHA256,
        "oracle_sha256": sha256(oracle),
        "solver_sha256": sha256(solver),
    }
    atomic_json(build_record, metadata)
    return solver, oracle, metadata


def verify_build_evidence(
        work_dir: Path, summary: Mapping[str, object]
        ) -> Tuple[Path, Path, Mapping[str, object], Set[str]]:
    build_dir = work_dir / "build"
    record_path = build_dir / "BUILD.json"
    if not record_path.is_file():
        raise RecomputeError("build/BUILD.json is missing")
    try:
        metadata = json.loads(record_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise RecomputeError("cannot read build/BUILD.json") from error
    if not isinstance(metadata, dict) or summary.get("build") != metadata:
        raise RecomputeError("summary/build record mismatch")
    flags = ["-O2", "-std=c++20", "-Wall", "-Wextra", "-Wpedantic", "-Werror"]
    compiler = metadata.get("compiler")
    version = metadata.get("compiler_version")
    if (not isinstance(compiler, str) or not compiler or
            not isinstance(version, str) or not version or
            metadata.get("flags") != flags or
            metadata.get("historical_solver_sha256") !=
            HISTORICAL_SOLVER_SHA256):
        raise RecomputeError("invalid build provenance binding")
    commands = metadata.get("commands")
    if not isinstance(commands, list) or len(commands) != 2:
        raise RecomputeError("build command set mismatch")
    specifications = (
        ("g001_remaining_shallow_pilot.cpp", "g001_remaining_shallow_pilot"),
        ("audit_g001_remaining_seed_orbits.cpp",
         "audit_g001_remaining_seed_orbits"),
    )
    binaries: List[Path] = []
    inventory = {"build/BUILD.json"}
    for record, (source_name, output_base) in zip(commands, specifications):
        if not isinstance(record, dict) or set(record) != {
                "command", "output", "sha256", "source"}:
            raise RecomputeError("malformed build command record")
        output_name = record.get("output")
        if (record.get("source") != source_name or
                output_name not in (output_base, output_base + ".exe")):
            raise RecomputeError("build source/output mismatch")
        command = record.get("command")
        if (not isinstance(command, list) or
                any(not isinstance(item, str) for item in command) or
                command[:1] != [compiler] or command[1:1 + len(flags)] != flags or
                len(command) != len(flags) + 4 or command[-2] != "-o" or
                recorded_basename(command[-3]) != source_name or
                recorded_basename(command[-1]) != output_name):
            raise RecomputeError("build command binding mismatch")
        binary = build_dir / str(output_name)
        digest = record.get("sha256")
        if (not binary.is_file() or not isinstance(digest, str) or
                sha256(binary) != digest):
            raise RecomputeError("built binary hash mismatch")
        binaries.append(binary)
        inventory.update({
            "build/{}".format(output_name),
            "build/{}.compile.stdout.txt".format(output_base),
            "build/{}.compile.stderr.txt".format(output_base),
        })
    solver, oracle = binaries
    if (metadata.get("solver_sha256") != sha256(solver) or
            summary.get("solver_sha256") != metadata.get("solver_sha256") or
            metadata.get("oracle_sha256") != sha256(oracle)):
        raise RecomputeError("summary/build binary digest mismatch")
    for relative in inventory:
        if not (work_dir / relative).is_file():
            raise RecomputeError("missing build artifact: {}".format(relative))
    return solver, oracle, metadata, inventory


def load_authoritative_parser(source_dir: Path):
    path = source_dir / "verify_g001_remaining_shallow_pilot.py"
    name = "leech18_c157_authoritative_parser"
    specification = importlib.util.spec_from_file_location(name, path)
    if specification is None or specification.loader is None:
        raise RecomputeError("cannot load authoritative result parser")
    module = importlib.util.module_from_spec(specification)
    sys.dont_write_bytecode = True
    specification.loader.exec_module(module)
    return module


def run_preflight(solver: Path, oracle: Path, source_dir: Path,
                  output_dir: Optional[Path]) -> str:
    parser_script = source_dir / "verify_g001_remaining_shallow_pilot.py"
    if output_dir is None:
        temporary_context = tempfile.TemporaryDirectory(prefix="leech18-c157-preflight-")
        destination = Path(temporary_context.name)
    else:
        temporary_context = None
        destination = output_dir
        destination.mkdir(parents=True, exist_ok=True)
    report = destination / "PREFLIGHT.json"
    command = [
        sys.executable, "-B", str(parser_script),
        "--solver", str(solver), "--oracle", str(oracle),
        "--timeout-seconds", "120", "--output-json", str(report),
    ]
    completed = subprocess.run(
        command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
        env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
    )
    if output_dir is not None:
        atomic_bytes(destination / "PREFLIGHT.stdout.txt", completed.stdout)
        atomic_bytes(destination / "PREFLIGHT.stderr.txt", completed.stderr)
    if completed.returncode != 0:
        raise RecomputeError("authoritative shallow preflight failed")
    if completed.stderr:
        raise RecomputeError("authoritative shallow preflight wrote stderr")
    if not report.is_file():
        raise RecomputeError("authoritative shallow preflight omitted report")
    report_hash = sha256(report)
    if temporary_context is not None:
        temporary_context.cleanup()
    return report_hash


def verify_preflight_evidence(
        work_dir: Path, summary: Mapping[str, object], solver: Path,
        oracle: Path, parser_module) -> Set[str]:
    preflight_dir = work_dir / "preflight"
    report_path = preflight_dir / "PREFLIGHT.json"
    stdout_path = preflight_dir / "PREFLIGHT.stdout.txt"
    stderr_path = preflight_dir / "PREFLIGHT.stderr.txt"
    for path in (report_path, stdout_path, stderr_path):
        if not path.is_file():
            raise RecomputeError("missing preflight artifact: {}".format(path.name))
    if stderr_path.read_bytes() != b"":
        raise RecomputeError("preserved preflight stderr is nonempty")
    if summary.get("preflight_sha256") != sha256(report_path):
        raise RecomputeError("preflight report digest mismatch")
    try:
        report = json.loads(report_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise RecomputeError("cannot read preflight report") from error
    if not isinstance(report, dict) or set(report) != {
            "schema", "solver", "solver_sha256", "oracle", "oracle_sha256",
            "production_flags", "modes"}:
        raise RecomputeError("preflight report schema mismatch")
    if (report.get("schema") != "g001-remaining-shallow-preflight-v1" or
            recorded_basename(report.get("solver")) != solver.name or
            recorded_basename(report.get("oracle")) != oracle.name or
            report.get("solver_sha256") != sha256(solver) or
            report.get("oracle_sha256") != sha256(oracle) or
            report.get("production_flags") !=
            list(getattr(parser_module, "PRODUCTION_FLAGS", []))):
        raise RecomputeError("preflight binary/flag binding mismatch")
    expected_modes = getattr(parser_module, "EXPECTED", None)
    modes = report.get("modes")
    if (not isinstance(expected_modes, dict) or not isinstance(modes, dict) or
            set(modes) != set(expected_modes)):
        raise RecomputeError("preflight mode set mismatch")
    expected_stdout: List[str] = []
    for mode, expected in expected_modes.items():
        seed_mex, first_mex = expected
        observed = modes.get(mode)
        if not isinstance(observed, dict) or set(observed) != {
                "seed_mex", "first_children", "first_child_mex",
                "second_child_counts", "second_frontier", "depth8_frontier"}:
            raise RecomputeError("preflight mode record mismatch: {}".format(mode))
        first_children = sum(first_mex.values())
        expected_first_mex = {str(key): value for key, value in first_mex.items()}
        second_counts = observed.get("second_child_counts")
        second_frontier = observed.get("second_frontier")
        depth8_frontier = observed.get("depth8_frontier")
        if (observed.get("seed_mex") != seed_mex or
                observed.get("first_children") != first_children or
                observed.get("first_child_mex") != expected_first_mex or
                not isinstance(second_counts, list) or
                len(second_counts) != first_children or
                any(not isinstance(value, int) or value < 0
                    for value in second_counts) or
                not isinstance(second_frontier, int) or
                second_frontier != sum(second_counts) or
                not isinstance(depth8_frontier, int) or depth8_frontier < 0):
            raise RecomputeError("preflight mode invariant mismatch: {}".format(mode))
        expected_stdout.append(
            "SHALLOW_OK mode={} roots={} second_frontier={} "
            "depth8_frontier={}".format(
                mode, first_children, second_frontier, depth8_frontier)
        )
    expected_stdout.append("G001_REMAINING_SHALLOW_VERIFICATION_OK")
    try:
        stdout_lines = stdout_path.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeError) as error:
        raise RecomputeError("cannot read preflight stdout") from error
    if stdout_lines != expected_stdout:
        raise RecomputeError("preflight stdout/report mismatch")
    return {
        "preflight/PREFLIGHT.json",
        "preflight/PREFLIGHT.stdout.txt",
        "preflight/PREFLIGHT.stderr.txt",
    }


def terminate_process(process: subprocess.Popen) -> None:
    if process.poll() is not None:
        return
    try:
        if os.name == "nt":
            process.terminate()
        else:
            os.killpg(process.pid, signal.SIGTERM)
    except (OSError, ProcessLookupError):
        pass
    try:
        process.wait(timeout=5)
        return
    except subprocess.TimeoutExpired:
        pass
    try:
        if os.name == "nt":
            process.kill()
        else:
            os.killpg(process.pid, signal.SIGKILL)
    except (OSError, ProcessLookupError):
        pass


def request_stop(_signum: int, _frame: object) -> None:
    STOP.set()
    with ACTIVE_LOCK:
        active = list(ACTIVE)
    for process in active:
        terminate_process(process)


def task_paths(tasks_dir: Path, task: Task) -> Tuple[Path, Path, Path]:
    base = tasks_dir / task.task_id()
    return (Path(str(base) + ".stdout.txt"),
            Path(str(base) + ".stderr.txt"),
            Path(str(base) + ".json"))


def parse_task_output(parser_module, task: Task, stdout: bytes,
                      stderr: bytes, returncode: int):
    if returncode != 0:
        raise RecomputeError(
            "task {} exited {}".format(task.task_id(), returncode)
        )
    if stderr:
        raise RecomputeError("task {} wrote stderr".format(task.task_id()))
    try:
        text = stdout.decode("utf-8", errors="strict")
    except UnicodeError as error:
        raise RecomputeError("task stdout is not UTF-8") from error
    try:
        return parser_module.parse_result(text, task.mode, True)
    except Exception as error:
        raise RecomputeError(
            "task {} result rejected: {}".format(task.task_id(), error)
        ) from error


def load_cached_task(tasks_dir: Path, task: Task, solver_hash: str,
                     parser_module, solver_name: Optional[str] = None):
    stdout_path, stderr_path, meta_path = task_paths(tasks_dir, task)
    if not meta_path.is_file():
        return None
    try:
        metadata = json.loads(meta_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise RecomputeError("invalid cached task metadata") from error
    if not isinstance(metadata, dict):
        raise RecomputeError("invalid cached task metadata")
    command = metadata.get("command")
    if (metadata.get("schema") != "leech18-c157-task-v1" or
            metadata.get("status") != "COMPLETE" or
            metadata.get("exit_code") != 0 or
            metadata.get("timed_out") is not False or
            metadata.get("task") != task.identity() or
            metadata.get("solver_sha256") != solver_hash or
            not isinstance(command, list) or len(command) < 2 or
            any(not isinstance(item, str) for item in command) or
            command[1:] != task.arguments() or
            (solver_name is not None and
             recorded_basename(command[0]) != solver_name) or
            not stdout_path.is_file() or not stderr_path.is_file() or
            sha256(stdout_path) != metadata.get("stdout_sha256") or
            sha256(stderr_path) != metadata.get("stderr_sha256")):
        raise RecomputeError("cached task binding mismatch: {}".format(task.task_id()))
    stdout = stdout_path.read_bytes()
    stderr = stderr_path.read_bytes()
    return parse_task_output(parser_module, task, stdout, stderr, 0)


def execute_task(tasks_dir: Path, task: Task, solver: Path, solver_hash: str,
                 parser_module, timeout_seconds: float, resume: bool):
    if STOP.is_set():
        raise RecomputeError("stop requested")
    if resume:
        cached = load_cached_task(
            tasks_dir, task, solver_hash, parser_module, solver.name
        )
        if cached is not None:
            return cached
    stdout_path, stderr_path, meta_path = task_paths(tasks_dir, task)
    if not resume and any(path.exists() for path in (stdout_path, stderr_path, meta_path)):
        raise RecomputeError("task output already exists: {}".format(task.task_id()))
    command = [str(solver)] + task.arguments()
    started = utc_now()
    popen_arguments = {
        "stdout": subprocess.PIPE,
        "stderr": subprocess.PIPE,
        "cwd": str(solver.parent),
    }
    if os.name == "nt":
        popen_arguments["creationflags"] = subprocess.CREATE_NEW_PROCESS_GROUP
    else:
        popen_arguments["start_new_session"] = True
    process = subprocess.Popen(command, **popen_arguments)
    with ACTIVE_LOCK:
        ACTIVE.add(process)
    timed_out = False
    try:
        try:
            stdout, stderr = process.communicate(
                timeout=None if timeout_seconds == 0 else timeout_seconds
            )
        except subprocess.TimeoutExpired:
            timed_out = True
            terminate_process(process)
            stdout, stderr = process.communicate()
    finally:
        with ACTIVE_LOCK:
            ACTIVE.discard(process)
    atomic_bytes(stdout_path, stdout)
    atomic_bytes(stderr_path, stderr)
    metadata = {
        "command": command,
        "end_utc": utc_now(),
        "exit_code": process.returncode,
        "schema": "leech18-c157-task-v1",
        "solver_sha256": solver_hash,
        "start_utc": started,
        "status": ("TIMEOUT" if timed_out else
                   "COMPLETE" if process.returncode == 0 else "FAILED"),
        "stderr_sha256": sha256(stderr_path),
        "stdout_sha256": sha256(stdout_path),
        "task": task.identity(),
        "timed_out": timed_out,
    }
    atomic_json(meta_path, metadata)
    if timed_out:
        raise RecomputeError("task {} timed out (non-evidence)".format(task.task_id()))
    return parse_task_output(
        parser_module, task, stdout, stderr, int(process.returncode)
    )


def add_map(target: Dict[int, int], source: Mapping[int, int]) -> None:
    for key, value in source.items():
        target[key] = target.get(key, 0) + value


def evaluate_gate(configuration: int, prefix: PathTuple, planned: Set[int],
                  load_task) -> Mapping[str, object]:
    mode = str(CONFIGURATIONS[configuration]["mode"])
    stop = len(prefix) + 4
    parent_task = Task("gate_parent", configuration, mode, prefix, stop)
    parent_fields, parent_maps = load_task(parent_task)
    child_key = len(prefix) + 3
    child_count = parent_maps["child_max"].get(child_key, 0)
    parent_frontier = int(parent_fields["frontier"])
    if child_count < parent_frontier or child_count <= 0:
        raise RecomputeError("invalid parent fanout at {}:{}".format(
            configuration, prefix))
    viable: Set[int] = set()
    aggregates: Dict[str, Dict[int, int]] = {
        "frontier_mex": {}, "frontier_odd": {}, "frontier_q3": {},
    }
    for child in range(child_count):
        task = Task("gate_child", configuration, mode,
                    prefix + (child,), stop)
        fields, maps = load_task(task)
        frontier = int(fields["frontier"])
        if frontier not in (0, 1):
            raise RecomputeError("immediate child frontier is not 0/1")
        if frontier == 1:
            viable.add(child)
        for name in aggregates:
            add_map(aggregates[name], maps[name])
    if len(viable) != parent_frontier:
        raise RecomputeError("parent/child frontier sum mismatch")
    for name in aggregates:
        if aggregates[name] != parent_maps[name]:
            raise RecomputeError("parent/child {} mismatch".format(name))
    if viable != planned:
        raise RecomputeError(
            "partition fanout mismatch at {}:{} planned={} viable={}".format(
                configuration, prefix, sorted(planned), sorted(viable)
            )
        )
    omitted_zero = child_count - len(planned)
    if omitted_zero < 0:
        raise RecomputeError("plan names a child outside the parent fanout")
    return {
        "child_count": child_count,
        "configuration": configuration,
        "omitted_zero_child_count": omitted_zero,
        "path": list(prefix),
        "viable_child_count": len(viable),
        "zero_child_count": child_count - len(viable),
    }


def run_gate(configuration: int, prefix: PathTuple, planned: Set[int],
             tasks_dir: Path, solver: Path, solver_hash: str, parser_module,
             timeout_seconds: float, resume: bool) -> Mapping[str, object]:
    def load_task(task: Task):
        return execute_task(
            tasks_dir, task, solver, solver_hash, parser_module,
            timeout_seconds, resume,
        )

    return evaluate_gate(configuration, prefix, planned, load_task)


def run_parallel(items: Sequence[object], worker, workers: int,
                 label: str) -> List[object]:
    results: List[object] = []
    with ThreadPoolExecutor(max_workers=workers) as executor:
        futures = {executor.submit(worker, item): item for item in items}
        completed_count = 0
        try:
            for future in as_completed(futures):
                results.append(future.result())
                completed_count += 1
                if completed_count % 500 == 0 or completed_count == len(items):
                    print("C157_PROGRESS phase={} completed={} total={}".format(
                        label, completed_count, len(items)), flush=True)
        except BaseException:
            STOP.set()
            for future in futures:
                future.cancel()
            request_stop(signal.SIGTERM, None)
            raise
    return results


def expected_task_ids(workload: Workload,
                      gate_results: Sequence[Mapping[str, object]]) -> Set[str]:
    child_counts: Dict[Tuple[int, PathTuple], int] = {}
    for record in gate_results:
        key = (int(record["configuration"]), tuple(record["path"]))
        if key in child_counts:
            raise RecomputeError("duplicate gate result")
        child_counts[key] = int(record["child_count"])
    result: Set[str] = set()

    def add(task: Task) -> None:
        task_id = task.task_id()
        if task_id in result:
            raise RecomputeError("task identity digest collision")
        result.add(task_id)

    for configuration in sorted(workload.internal):
        mode = str(CONFIGURATIONS[configuration]["mode"])
        for prefix in workload.internal[configuration]:
            key = (configuration, prefix)
            if key not in child_counts:
                raise RecomputeError("missing gate result")
            stop = len(prefix) + 4
            add(Task("gate_parent", configuration, mode, prefix, stop))
            for child in range(child_counts[key]):
                add(Task("gate_child", configuration, mode,
                         prefix + (child,), stop))
    if len(child_counts) != EXPECTED_INTERNAL_PREFIXES:
        raise RecomputeError("unexpected gate result")
    for leaf in workload.leaves:
        add(Task("leaf", leaf.configuration, leaf.mode, leaf.path, 12))
    if len(result) != EXPECTED_INVOCATIONS:
        raise RecomputeError("exact task identity count mismatch")
    return result


def verify_exact_task_set(tasks_dir: Path, task_ids: Set[str]) -> Set[str]:
    if not tasks_dir.is_dir():
        raise RecomputeError("tasks directory is missing")
    expected_extensions = {".json", ".stdout.txt", ".stderr.txt"}
    expected_names = {
        task_id + extension
        for task_id in task_ids for extension in expected_extensions
    }
    observed_names: Set[str] = set()
    for path in tasks_dir.iterdir():
        if not path.is_file():
            raise RecomputeError("non-file in tasks directory: {}".format(path))
        observed_names.add(path.name)
    if observed_names != expected_names:
        raise RecomputeError(
            "exact task artifact set mismatch: expected={} observed={}".format(
                len(expected_names), len(observed_names)
            )
        )
    return {"tasks/" + name for name in expected_names}


def write_results_manifest(work_dir: Path) -> str:
    manifest = work_dir / "RESULTS_MANIFEST.sha256"
    excluded = {manifest.resolve(), (work_dir / "C157_RECOMPUTATION.json").resolve()}
    files = sorted(
        (path for path in work_dir.rglob("*")
         if path.is_file() and path.resolve() not in excluded),
        key=lambda path: path.relative_to(work_dir).as_posix(),
    )
    lines = [
        "{}  {}".format(sha256(path), path.relative_to(work_dir).as_posix())
        for path in files
    ]
    atomic_bytes(manifest, ("\n".join(lines) + "\n").encode("utf-8"))
    return sha256(manifest)


def verify_results_manifest(work_dir: Path) -> str:
    manifest = work_dir / "RESULTS_MANIFEST.sha256"
    if not manifest.is_file():
        raise RecomputeError("RESULTS_MANIFEST.sha256 is missing")
    seen: Set[str] = set()
    digests: Dict[str, str] = {}
    for line in manifest.read_text(encoding="utf-8").splitlines():
        if len(line) < 67 or line[64:66] != "  ":
            raise RecomputeError("malformed result manifest line")
        expected, relative = line[:64], line[66:]
        if relative in seen or not relative or Path(relative).is_absolute():
            raise RecomputeError("unsafe/duplicate result manifest path")
        seen.add(relative)
        path = (work_dir / relative).resolve()
        try:
            path.relative_to(work_dir.resolve())
        except ValueError as error:
            raise RecomputeError("result manifest path escapes work directory") from error
        if not path.is_file() or sha256(path) != expected:
            raise RecomputeError("result manifest mismatch: {}".format(relative))
        digests[relative] = expected
    excluded = {
        manifest.resolve(), (work_dir / "C157_RECOMPUTATION.json").resolve()
    }
    actual = {
        path.relative_to(work_dir).as_posix()
        for path in work_dir.rglob("*")
        if path.is_file() and path.resolve() not in excluded
    }
    if seen != actual:
        raise RecomputeError("result manifest exact-set mismatch")
    canonical = ("\n".join(
        "{}  {}".format(digests[relative], relative)
        for relative in sorted(digests)
    ) + "\n").encode("utf-8")
    if manifest.read_bytes() != canonical:
        raise RecomputeError("result manifest is not canonical")
    return sha256(manifest)


def verify_exact_result_inventory(work_dir: Path,
                                  manifested_files: Set[str]) -> None:
    expected_files = set(manifested_files)
    expected_files.update({
        "C157_RECOMPUTATION.json", "RESULTS_MANIFEST.sha256",
    })
    actual_files = {
        path.relative_to(work_dir).as_posix()
        for path in work_dir.rglob("*") if path.is_file()
    }
    if actual_files != expected_files:
        raise RecomputeError(
            "exact result file inventory mismatch: expected={} observed={}".format(
                len(expected_files), len(actual_files)
            )
        )
    actual_directories = {
        path.relative_to(work_dir).as_posix()
        for path in work_dir.rglob("*") if path.is_dir()
    }
    if actual_directories != {"build", "preflight", "tasks"}:
        raise RecomputeError("exact result directory inventory mismatch")


def execute_full(args, workload: Workload, source_manifest_hash: str,
                 compiler: Path) -> None:
    if args.work_dir is None:
        raise RecomputeError("--run requires --work-dir")
    work_dir = args.work_dir.expanduser().resolve()
    if work_dir == REPO_ROOT or REPO_ROOT in work_dir.parents:
        raise RecomputeError("--work-dir must be outside the repository")
    if work_dir.exists():
        if not args.resume:
            raise RecomputeError("work directory exists; use a new path or --resume")
        if not work_dir.is_dir():
            raise RecomputeError("work path is not a directory")
    else:
        work_dir.mkdir(parents=True)
    tasks_dir = work_dir / "tasks"
    tasks_dir.mkdir(exist_ok=True)
    atomic_json(work_dir / "WORKLOAD.json", workload.canonical)
    if sha256(work_dir / "WORKLOAD.json") != hashlib.sha256(
            json.dumps(workload.canonical, indent=2, sort_keys=True,
                       ensure_ascii=True).encode("utf-8") + b"\n").hexdigest():
        raise RecomputeError("WORKLOAD.json write mismatch")

    solver, oracle, build = build_binaries(
        args.source_dir, work_dir / "build", compiler, reuse=args.resume
    )
    preflight_hash = run_preflight(
        solver, oracle, args.source_dir, work_dir / "preflight"
    )
    parser_module = load_authoritative_parser(args.source_dir)
    solver_hash = str(build["solver_sha256"])
    old_handlers = {}
    for signum in (signal.SIGINT, signal.SIGTERM):
        old_handlers[signum] = signal.getsignal(signum)
        signal.signal(signum, request_stop)
    started = utc_now()
    try:
        gate_items = [
            (configuration, prefix)
            for configuration in sorted(workload.internal)
            for prefix in workload.internal[configuration]
        ]

        def gate_worker(item):
            configuration, prefix = item
            planned = workload.children[(configuration, prefix)]
            return run_gate(
                configuration, prefix, planned, tasks_dir,
                solver, solver_hash, parser_module,
                args.task_timeout_seconds, args.resume,
            )

        gate_results = run_parallel(gate_items, gate_worker, args.workers, "gates")

        def leaf_worker(leaf: Leaf):
            task = Task("leaf", leaf.configuration, leaf.mode, leaf.path, 12)
            fields, _maps = execute_task(
                tasks_dir, task, solver, solver_hash, parser_module,
                args.task_timeout_seconds, args.resume,
            )
            actual = int(fields["frontier"])
            if actual != leaf.frontier:
                raise RecomputeError(
                    "leaf frontier mismatch {}:{} {} != {}".format(
                        leaf.configuration, leaf.path, actual, leaf.frontier
                    )
                )
            return leaf.configuration, actual

        leaf_results = run_parallel(
            workload.leaves, leaf_worker, args.workers, "leaves"
        )
    finally:
        for signum, handler in old_handlers.items():
            signal.signal(signum, handler)
    if STOP.is_set():
        raise RecomputeError("run interrupted")

    gate_by_configuration = {key: [] for key in CONFIGURATIONS}
    for record in gate_results:
        gate_by_configuration[int(record["configuration"])].append(record)
    leaf_by_configuration = {key: [] for key in CONFIGURATIONS}
    for configuration, frontier in leaf_results:
        leaf_by_configuration[configuration].append(frontier)

    configuration_summary = {}
    gate_child_count = 0
    gate_zero_child_count = 0
    omitted_zero_child_count = 0
    planned_zero_child_count = 0
    for configuration, expected in CONFIGURATIONS.items():
        gates = gate_by_configuration[configuration]
        leaves = leaf_by_configuration[configuration]
        actual_gate_zero = sum(int(item["zero_child_count"]) for item in gates)
        actual_omitted_zero = sum(
            int(item["omitted_zero_child_count"]) for item in gates)
        actual_planned_zero = sum(value == 0 for value in leaves)
        actual_child = sum(int(item["child_count"]) for item in gates)
        if (len(gates) != expected["internal_prefix_count"] or
                len(leaves) != expected["leaf_count"] or
                sum(leaves) != expected["frontier_sum"] or
                actual_gate_zero != expected["gate_zero_child_count"] or
                actual_omitted_zero != expected["omitted_zero_child_count"] or
                actual_planned_zero != expected["planned_zero_leaf_count"]):
            raise RecomputeError(
                "Configuration {} final invariant mismatch".format(configuration)
            )
        gate_child_count += actual_child
        gate_zero_child_count += actual_gate_zero
        omitted_zero_child_count += actual_omitted_zero
        planned_zero_child_count += actual_planned_zero
        configuration_summary[str(configuration)] = {
            "frontier_sum": sum(leaves),
            "internal_prefix_count": len(gates),
            "leaf_count": len(leaves),
            "mode": expected["mode"],
            "gate_zero_child_count": actual_gate_zero,
            "omitted_zero_child_count": actual_omitted_zero,
            "planned_zero_leaf_count": actual_planned_zero,
        }
    if gate_child_count != EXPECTED_CHILD_GATES:
        raise RecomputeError("gate child count mismatch")
    if (gate_zero_child_count != EXPECTED_GATE_ZERO_CHILDREN or
            omitted_zero_child_count != EXPECTED_ZERO_CHILDREN or
            planned_zero_child_count != EXPECTED_PLANNED_ZERO_LEAVES):
        raise RecomputeError("zero child totals mismatch")
    task_count = EXPECTED_INTERNAL_PREFIXES + gate_child_count + EXPECTED_LEAVES
    if task_count != EXPECTED_INVOCATIONS:
        raise RecomputeError("solver invocation count mismatch")
    task_ids = expected_task_ids(workload, gate_results)
    verify_exact_task_set(tasks_dir, task_ids)
    manifest_hash = write_results_manifest(work_dir)
    summary = {
        "build": build,
        "completed_utc": utc_now(),
        "configurations": configuration_summary,
        "coverage": {
            "exhaustive_gate_check": True,
            "gate_child_count": gate_child_count,
            "gate_parent_count": EXPECTED_INTERNAL_PREFIXES,
            "gate_zero_child_count": gate_zero_child_count,
            "leaf_frontiers_match_plan": True,
            "omitted_zero_child_count": omitted_zero_child_count,
            "planned_zero_leaf_count": planned_zero_child_count,
            "prefix_free": True,
        },
        "historical_solver_sha256": HISTORICAL_SOLVER_SHA256,
        "internal_prefix_count": EXPECTED_INTERNAL_PREFIXES,
        "leaf_count": EXPECTED_LEAVES,
        "plan_sha256": PLAN_SHA256,
        "preflight_sha256": preflight_hash,
        "production_flags": list(PRODUCTION_FLAGS),
        "results_manifest_sha256": manifest_hash,
        "schema": SCHEMA,
        "solver_invocation_count": task_count,
        "solver_sha256": solver_hash,
        "source_manifest_sha256": source_manifest_hash,
        "started_utc": started,
        "status": STATUS,
        "workload_sha256": workload.sha256,
        "zero_child_count": omitted_zero_child_count,
    }
    atomic_json(work_dir / "C157_RECOMPUTATION.json", summary)
    print(
        "G001_C157_FRESH_RECOMPUTATION_OK configurations=4 leaves={} "
        "internal_prefixes={} zero_children={}".format(
            EXPECTED_LEAVES, EXPECTED_INTERNAL_PREFIXES,
            EXPECTED_ZERO_CHILDREN),
        flush=True,
    )


def verify_run(work_dir: Path, source_dir: Path = DEFAULT_SOURCE_DIR,
               plan_path: Path = DEFAULT_PLAN) -> None:
    work_dir = work_dir.expanduser().resolve()
    if not work_dir.is_dir():
        raise RecomputeError("completed run directory is missing")
    summary_path = work_dir / "C157_RECOMPUTATION.json"
    if not summary_path.is_file():
        raise RecomputeError("C157_RECOMPUTATION.json is missing")
    try:
        summary = json.loads(summary_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise RecomputeError("cannot read C157_RECOMPUTATION.json") from error
    if not isinstance(summary, dict) or set(summary) != {
            "build", "completed_utc", "configurations", "coverage",
            "historical_solver_sha256", "internal_prefix_count", "leaf_count",
            "plan_sha256", "preflight_sha256", "production_flags",
            "results_manifest_sha256", "schema", "solver_invocation_count",
            "solver_sha256", "source_manifest_sha256", "started_utc", "status",
            "workload_sha256", "zero_child_count"}:
        raise RecomputeError("C157_RECOMPUTATION.json field set mismatch")
    required = {
        "schema": SCHEMA,
        "status": STATUS,
        "plan_sha256": PLAN_SHA256,
        "leaf_count": EXPECTED_LEAVES,
        "internal_prefix_count": EXPECTED_INTERNAL_PREFIXES,
        "zero_child_count": EXPECTED_ZERO_CHILDREN,
        "solver_invocation_count": EXPECTED_INVOCATIONS,
    }
    for name, expected in required.items():
        if summary.get(name) != expected:
            raise RecomputeError("summary field mismatch: {}".format(name))
    source_manifest_hash = verify_sources(source_dir.expanduser().resolve())
    workload = load_workload(plan_path.expanduser().resolve())
    if (summary.get("workload_sha256") != workload.sha256 or
            summary.get("source_manifest_sha256") != source_manifest_hash or
            summary.get("historical_solver_sha256") !=
            HISTORICAL_SOLVER_SHA256 or
            summary.get("production_flags") != list(PRODUCTION_FLAGS) or
            not isinstance(summary.get("started_utc"), str) or
            not summary.get("started_utc") or
            not isinstance(summary.get("completed_utc"), str) or
            not summary.get("completed_utc")):
        raise RecomputeError("summary provenance binding mismatch")
    expected_configuration_summary = {}
    for configuration, expected in CONFIGURATIONS.items():
        expected_configuration_summary[str(configuration)] = {
            "frontier_sum": expected["frontier_sum"],
            "gate_zero_child_count": expected["gate_zero_child_count"],
            "internal_prefix_count": expected["internal_prefix_count"],
            "leaf_count": expected["leaf_count"],
            "mode": expected["mode"],
            "omitted_zero_child_count": expected["omitted_zero_child_count"],
            "planned_zero_leaf_count": expected["planned_zero_leaf_count"],
        }
    if summary.get("configurations") != expected_configuration_summary:
        raise RecomputeError("configuration summary mismatch")
    expected_coverage = {
        "exhaustive_gate_check": True,
        "gate_child_count": EXPECTED_CHILD_GATES,
        "gate_parent_count": EXPECTED_INTERNAL_PREFIXES,
        "gate_zero_child_count": EXPECTED_GATE_ZERO_CHILDREN,
        "leaf_frontiers_match_plan": True,
        "omitted_zero_child_count": EXPECTED_ZERO_CHILDREN,
        "planned_zero_leaf_count": EXPECTED_PLANNED_ZERO_LEAVES,
        "prefix_free": True,
    }
    if summary.get("coverage") != expected_coverage:
        raise RecomputeError("summary coverage mismatch")

    verify_workload_record(work_dir, workload)
    solver, oracle, _build, build_inventory = verify_build_evidence(
        work_dir, summary
    )
    parser_module = load_authoritative_parser(source_dir.expanduser().resolve())
    preflight_inventory = verify_preflight_evidence(
        work_dir, summary, solver, oracle, parser_module
    )
    tasks_dir = work_dir / "tasks"
    if not tasks_dir.is_dir():
        raise RecomputeError("tasks directory is missing")
    solver_hash = str(summary["solver_sha256"])

    def load_required(task: Task):
        result = load_cached_task(
            tasks_dir, task, solver_hash, parser_module, solver.name
        )
        if result is None:
            raise RecomputeError(
                "required cached task is missing: {}".format(task.task_id())
            )
        return result

    gate_results: List[Mapping[str, object]] = []
    gate_counter = 0
    for configuration in sorted(workload.internal):
        for prefix in workload.internal[configuration]:
            gate_results.append(evaluate_gate(
                configuration, prefix,
                workload.children[(configuration, prefix)], load_required,
            ))
            gate_counter += 1
            if gate_counter % 500 == 0:
                print("C157_VERIFY_PROGRESS phase=gates completed={} total={}".format(
                    gate_counter, EXPECTED_INTERNAL_PREFIXES), flush=True)

    leaf_values: Dict[int, List[int]] = {key: [] for key in CONFIGURATIONS}
    for index, leaf in enumerate(workload.leaves, 1):
        task = Task("leaf", leaf.configuration, leaf.mode, leaf.path, 12)
        fields, _maps = load_required(task)
        actual = int(fields["frontier"])
        if actual != leaf.frontier:
            raise RecomputeError(
                "leaf frontier mismatch {}:{} {} != {}".format(
                    leaf.configuration, leaf.path, actual, leaf.frontier
                )
            )
        leaf_values[leaf.configuration].append(actual)
        if index % 5000 == 0:
            print("C157_VERIFY_PROGRESS phase=leaves completed={} total={}".format(
                index, EXPECTED_LEAVES), flush=True)

    gate_values: Dict[int, List[Mapping[str, object]]] = {
        key: [] for key in CONFIGURATIONS
    }
    for record in gate_results:
        gate_values[int(record["configuration"])].append(record)
    calculated_configuration_summary = {}
    total_children = total_gate_zero = total_omitted = total_planned_zero = 0
    for configuration, expected in CONFIGURATIONS.items():
        gates = gate_values[configuration]
        leaves = leaf_values[configuration]
        child_count = sum(int(record["child_count"]) for record in gates)
        gate_zero = sum(int(record["zero_child_count"]) for record in gates)
        omitted = sum(
            int(record["omitted_zero_child_count"]) for record in gates
        )
        planned_zero = sum(value == 0 for value in leaves)
        calculated_configuration_summary[str(configuration)] = {
            "frontier_sum": sum(leaves),
            "gate_zero_child_count": gate_zero,
            "internal_prefix_count": len(gates),
            "leaf_count": len(leaves),
            "mode": expected["mode"],
            "omitted_zero_child_count": omitted,
            "planned_zero_leaf_count": planned_zero,
        }
        total_children += child_count
        total_gate_zero += gate_zero
        total_omitted += omitted
        total_planned_zero += planned_zero
    if (calculated_configuration_summary != expected_configuration_summary or
            total_children != EXPECTED_CHILD_GATES or
            total_gate_zero != EXPECTED_GATE_ZERO_CHILDREN or
            total_omitted != EXPECTED_ZERO_CHILDREN or
            total_planned_zero != EXPECTED_PLANNED_ZERO_LEAVES):
        raise RecomputeError("replayed C157 invariant mismatch")

    task_ids = expected_task_ids(workload, gate_results)
    task_inventory = verify_exact_task_set(tasks_dir, task_ids)
    manifested_inventory = {"WORKLOAD.json"}
    manifested_inventory.update(build_inventory)
    manifested_inventory.update(preflight_inventory)
    manifested_inventory.update(task_inventory)
    verify_exact_result_inventory(work_dir, manifested_inventory)
    manifest_hash = verify_results_manifest(work_dir)
    if manifest_hash != summary.get("results_manifest_sha256"):
        raise RecomputeError("results manifest digest mismatch")
    print(
        "G001_C157_FRESH_RECOMPUTATION_RECORD_OK configurations=4 leaves={} "
        "internal_prefixes={} zero_children={}".format(
            EXPECTED_LEAVES, EXPECTED_INTERNAL_PREFIXES,
            EXPECTED_ZERO_CHILDREN)
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--preflight", action="store_true",
                        help="validate, build, and run bounded shallow tests")
    action.add_argument("--list-only", action="store_true",
                        help="validate and print the deterministic workload")
    action.add_argument("--run", action="store_true",
                        help="execute all C157 calibration and coverage tasks")
    action.add_argument("--verify-run", action="store_true",
                        help="rehash and validate a completed run record")
    parser.add_argument("--plan", type=Path, default=DEFAULT_PLAN)
    parser.add_argument("--source-dir", type=Path, default=DEFAULT_SOURCE_DIR)
    parser.add_argument("--compiler", default=os.environ.get("CXX", "g++"))
    parser.add_argument("--work-dir", type=Path)
    parser.add_argument("--workers", type=int, default=15)
    parser.add_argument("--task-timeout-seconds", type=float, default=0.0)
    parser.add_argument("--resume", action="store_true")
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    if not 1 <= args.workers <= 256:
        raise RecomputeError("--workers must be in 1..256")
    if args.task_timeout_seconds < 0:
        raise RecomputeError("--task-timeout-seconds cannot be negative")
    args.source_dir = args.source_dir.expanduser().resolve()
    args.plan = args.plan.expanduser().resolve()
    if args.verify_run:
        if args.work_dir is None:
            raise RecomputeError("--verify-run requires --work-dir")
        verify_run(args.work_dir, args.source_dir, args.plan)
        return 0
    source_manifest_hash = verify_sources(args.source_dir)
    workload = load_workload(args.plan)
    if args.list_only:
        print(
            "C157_WORKLOAD_OK configurations=4 leaves={} internal_prefixes={} "
            "expected_zero_children={} expected_solver_invocations={} "
            "workload_sha256={}".format(
                EXPECTED_LEAVES, EXPECTED_INTERNAL_PREFIXES,
                EXPECTED_ZERO_CHILDREN, EXPECTED_INVOCATIONS,
                workload.sha256)
        )
        return 0
    compiler = resolve_compiler(args.compiler)
    if args.preflight:
        with tempfile.TemporaryDirectory(prefix="leech18-c157-build-") as temporary:
            build_dir = Path(temporary)
            solver, oracle, metadata = build_binaries(
                args.source_dir, build_dir, compiler
            )
            report_hash = run_preflight(
                solver, oracle, args.source_dir, None
            )
        print(
            "C157_PREFLIGHT_OK sources=8 plan_sha256={} leaves={} "
            "internal_prefixes={} solver_sha256={} preflight_sha256={}".format(
                PLAN_SHA256, EXPECTED_LEAVES, EXPECTED_INTERNAL_PREFIXES,
                metadata["solver_sha256"], report_hash)
        )
        return 0
    execute_full(args, workload, source_manifest_hash, compiler)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except RecomputeError as error:
        print("C157_RECOMPUTATION_FAILED: {}".format(error), file=sys.stderr)
        raise SystemExit(1)
