#!/usr/bin/env python3
"""Recompute the exact reduced searches for paper Configurations 2, 3, and 8.

The authoritative Windows executables and their command vectors are retained
in the prior-three evidence and in the released Configuration-3 receipts.  This
driver does not generate a new partition plan.  It validates those frozen
rosters, prints them with --list-only, or executes every selected subtree into
a new output directory.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Iterable, Sequence


sys.dont_write_bytecode = True

SCRIPT_DIR = Path(__file__).absolute().parent
REPOSITORY = SCRIPT_DIR.parent
EVIDENCE = REPOSITORY / "computation/evidence/production"
PRIOR = EVIDENCE / "prior_three_configurations"
SOLVER_DIR = PRIOR / "work/a2_solver"
OUTPUTS = PRIOR / "outputs"
CONFIG3_RELEASE = (
    REPOSITORY
    / "proof/config3_repair/evidence/full_preserved_v1"
)
CONFIG3_VERIFIER = (
    REPOSITORY / "proof/config3_repair/verify_config3_a2_frozen.py"
)

ROW1_PLAN_SHA256 = "3cac29583013a86a5951cb85b846f634efa9e5791c55d4a3d59ef9e65a68c316"
ROW1_LEDGER_SHA256 = "0d6b2843c8a17c3c917f5b1766e44dab018d07c88373cbcecd72b19010fc8a15"
ROW1_RUNNER_SHA256 = "c7d3544428ab05053a7806002fd49249db80db488f4e2a90b5e67c520fd2cb15"
ROW1_SOLVER_SHA256 = "5f50bec4d18947680ee170bf22af747d1e74ea203e34e305eae27768439b46ad"
ROW1_SOURCE_SHA256 = "134373d19ad4b1b1dfb30595f73beabcef30fa21c19b74a652669fb7705a72d9"

ROW7_LEDGER_SHA256 = "830da5b5a96522d8f776d4510faef4e04218554e54580df496b6eca105a69cb9"
ROW7_FANOUT_SHA256 = "992674c8169f6533e88891471218864690b399027b9fa3d8d7f94c103fa9dd76"
ROW7_RUNNER_SHA256 = "4f3865ec89dbfa47444813773d3137f59c7f12fb06045159858c3149b43796ea"
ROW7_SOLVER_SHA256 = "9f894f39efb71e9c8506e5c5b312289b1d3befe95c95b911df8613f2e24baffb"
ROW7_SOURCE_SHA256 = "47183d7b30132bb5e6cc5039bc592eb90b900e8124c08df6ed31ea61b689e2cc"

CONFIG3_LEDGER_SHA256 = "bc6a5909d2de7b0cbc0e1a886a03c675b92419c8c4e553ad944e1a123dbc93ac"
CONFIG3_RELEASE_SHA256 = "ef7addf3ba82b933ae780c57cc8fc633073b422075fbd98171ebabf78da57ae5"
CONFIG3_RESULT_SHA256 = "c0b89376528fdc18881bc82ae9df6cf6632c913f8b1981de9014ef71cbb6f128"
CONFIG3_MANIFEST_SHA256 = "1603fe0bd5d6fee4e47d063a7077690ee76525631e31cc9d555aee71e59a53af"
CONFIG3_VERIFIER_SHA256 = "2e739732b35ed7bb6e7dbeb174ee2e713eae4b691a518ee00c5f7644bfd0a38a"
CONFIG3_SOLVER_SHA256 = "65bbaa57e5b462663b3656bc77499cc5956053f4137878c21072c99a327483f3"
CONFIG3_SOURCE_SHA256 = "e8dedc62323152ba586f9c8607d119440c8be9927ec4d38e546ba11de9100e9c"

ROW1_COVERAGE_VERIFIER_SHA256 = "a74272e29b2f1758a78a58ae3184ed4c296646da385f0b7c66b789b26427eebf"
ROW7_COVERAGE_VERIFIER_SHA256 = "095424ecad1ca994b96b4cfd7f0440645d8083b61352d3c51b25d3490448c1a5"
A2_COVERAGE_VERIFIER_SHA256 = "daae5dba585cacb4f27fae7199ea446433f6e6c26e997c8e20730f26ae4d91d6"

WINDOWS_RUNTIME_HASHES = {
    "libgcc_s_seh-1.dll": "6c0a4c1fa1cdb36ba1d7be050a16f50edeaff12294178cdd25590ef3081b0e89",
    "libstdc++-6.dll": "bc95e3e3b3f83f03e9d05f7bb61c2bf42b4b15c2305b1130a0036d36f2148aa2",
    "libwinpthread-1.dll": "0acbbb8652cdfce8cd4e9df34dc4f64539148e0de6ff1a2a6b2626808faddd36",
}
SOURCE_DEPENDENCY_HASHES = {
    "a2_multi_edge_exact_cover.hpp": "c156eae52bceef28db0df1a38d10dea253de09e5f627d0952a6bb1b9356cd813",
    "a2_multi_edge_exact_cover_optimized.hpp": "5320c920e800ce2f9e2348b90d672e26cddd748b43bc02bc24b9146dedb5e48b",
    "a2_multi_edge_stronger_relaxation.hpp": "e58f917a631c48f2419835d41c2b0ee164f0d24f44ba489c152b9c00cddbbd5c",
    "multi_edge_parity_coherence.hpp": "af09e37c9e50fb3891bb11bbfead6d5f8299200c7abf81bc8049fb20a07d30c7",
}

FLAGS_WITH_MAX = (
    "--multi-edge-cover",
    "--multi-edge-cover-no-hall",
    "--multi-edge-cover-max-components",
    "6",
    "--multi-edge-cover-budget",
    "100",
    "--multi-edge-cover-no-exact-hall",
)
FLAGS_CONFIG3 = (
    "--multi-edge-cover",
    "--multi-edge-cover-no-hall",
    "--multi-edge-cover-budget",
    "100",
    "--multi-edge-cover-no-exact-hall",
)


class RecomputeError(RuntimeError):
    pass


class FoundEvent(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RecomputeError(message)


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


def reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON key: {key!r}")
        result[key] = value
    return result


def read_json(path: Path) -> Any:
    try:
        return json.loads(
            path.read_text(encoding="utf-8"),
            object_pairs_hook=reject_duplicate_keys,
            parse_constant=lambda value: (_ for _ in ()).throw(
                RecomputeError(f"non-finite JSON number: {value}")
            ),
        )
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise RecomputeError(f"cannot read strict JSON {path}: {exc}") from exc


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


def read_csv(
    path: Path,
    expected_fields: Sequence[str],
    *,
    join_extra_last: bool = False,
) -> list[dict[str, str]]:
    try:
        with path.open("r", encoding="utf-8-sig", newline="") as stream:
            reader = csv.reader(stream)
            header = next(reader, None)
            require(header == list(expected_fields), f"CSV fields mismatch: {path}")
            rows = []
            for line_number, values in enumerate(reader, 2):
                if join_extra_last and len(values) > len(expected_fields):
                    values = values[: len(expected_fields) - 1] + [
                        ",".join(values[len(expected_fields) - 1 :])
                    ]
                require(
                    len(values) == len(expected_fields),
                    f"malformed CSV row {line_number}: {path}",
                )
                rows.append(dict(zip(expected_fields, values)))
    except (OSError, UnicodeError, csv.Error) as exc:
        raise RecomputeError(f"cannot read CSV {path}: {exc}") from exc
    return rows


def contained(root: Path, relative: str) -> Path:
    pure = PurePosixPath(relative)
    require(
        not pure.is_absolute()
        and bool(pure.parts)
        and all(part not in ("", ".", "..") for part in pure.parts),
        f"unsafe relative path: {relative!r}",
    )
    candidate = root.joinpath(*pure.parts)
    try:
        candidate.resolve(strict=True).relative_to(root.resolve(strict=True))
    except (OSError, ValueError) as exc:
        raise RecomputeError(f"path escapes release: {relative!r}") from exc
    return candidate


@dataclass(frozen=True)
class Job:
    configuration: int
    logical_key: str
    process_key: str
    category: str
    solver: Path
    argv: tuple[str, ...]
    expected_status: str
    expected_nodes: int
    expected_frontier: int
    expected_mode: str


def expected_row1_keys() -> list[str]:
    return (
        ["root_0", "root_1"]
        + [f"path_2_{index}" for index in range(9)]
        + [f"path_2_9_{index}" for index in range(15)]
        + [f"path_2_9_15_{index}" for index in range(22)]
        + [f"path_2_9_15_22_{index}" for index in range(31)]
    )


def expected_row7_keys() -> list[str]:
    return (
        [f"root_{index}" for index in range(3)]
        + [f"path_3_{index}" for index in range(2)]
        + [f"path_4_{index}" for index in range(9)]
        + [f"path_4_9_{index}" for index in range(15)]
        + [f"path_4_9_15_{index}" for index in range(23)]
    )


def expected_config3_keys() -> list[str]:
    return (
        ["a2_attached|root_0"]
        + [f"a2_attached|path_1_{index}" for index in range(6)]
        + [f"a2_separate|root_{index}" for index in range(4)]
        + [f"a2_separate|path_4_{index}" for index in range(6)]
        + [f"a2_separate|path_5_{index}" for index in range(5)]
        + [f"a2_separate|path_6_{index}" for index in range(2)]
        + [f"a2_separate|path_7_{index}" for index in range(8)]
        + [f"a2_separate|path_8_{index}" for index in range(15)]
    )


def unique_map(rows: Iterable[dict[str, str]], field: str, label: str) -> dict[str, dict[str, str]]:
    result: dict[str, dict[str, str]] = {}
    for row in rows:
        key = row[field]
        require(key not in result, f"duplicate {label} key: {key}")
        result[key] = row
    return result


def validate_authoritative_coverage() -> None:
    require(os.name == "nt", "the prior-three coverage verifiers require Windows")
    powershell = shutil.which("powershell.exe")
    require(powershell is not None, "powershell.exe was not found")
    checks = (
        (
            SOLVER_DIR / "verify_g001_row1_partition_coverage_portable.ps1",
            ROW1_COVERAGE_VERIFIER_SHA256,
            "G001_ROW1_COVERAGE_OK",
        ),
        (
            SOLVER_DIR / "verify_g001_row7_partition_coverage.ps1",
            ROW7_COVERAGE_VERIFIER_SHA256,
            "G001_ROW7_COVERAGE_OK",
        ),
        (
            SOLVER_DIR / "verify_a2_partition_coverage.ps1",
            A2_COVERAGE_VERIFIER_SHA256,
            "STATUS=COVERAGE_OK ALL_EXPECTED_PARTITIONS_ZERO",
        ),
    )
    environment = os.environ.copy()
    environment["G001_AUDIT_MODE"] = "READ_ONLY_COVERAGE"
    for script, digest, marker in checks:
        require_hash(script, digest, f"coverage verifier {script.name}")
        completed = subprocess.run(
            [
                powershell,
                "-NoLogo",
                "-NoProfile",
                "-NonInteractive",
                "-ExecutionPolicy",
                "Bypass",
                "-File",
                str(script),
            ],
            cwd=PRIOR,
            env=environment,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        sys.stdout.buffer.write(completed.stdout)
        sys.stdout.buffer.flush()
        sys.stderr.buffer.write(completed.stderr)
        sys.stderr.buffer.flush()
        require(completed.returncode == 0, f"coverage verifier exit {completed.returncode}: {script.name}")
        require(not completed.stderr, f"coverage verifier wrote stderr: {script.name}")
        try:
            normalized = completed.stdout.decode("utf-8").replace("\r\n", "\n").replace("\r", "\n")
        except UnicodeDecodeError as exc:
            raise RecomputeError(f"coverage verifier emitted non-UTF-8: {script.name}") from exc
        require(marker in normalized.splitlines(), f"coverage verifier marker missing: {script.name}")


def validate_bundled_dependencies() -> None:
    for name, digest in WINDOWS_RUNTIME_HASHES.items():
        require_hash(SOLVER_DIR / name, digest, f"Windows runtime dependency {name}")
    for name, digest in SOURCE_DEPENDENCY_HASHES.items():
        require_hash(SOLVER_DIR / name, digest, f"source dependency {name}")


def row1_jobs() -> list[Job]:
    plan_path = OUTPUTS / "G001_ROW1_PARTITION_PLAN_PROVISIONAL.csv"
    ledger_path = OUTPUTS / "G001_ROW1_PARTITION_RESULTS.csv"
    require_hash(plan_path, ROW1_PLAN_SHA256, "Configuration-2 plan")
    require_hash(ledger_path, ROW1_LEDGER_SHA256, "Configuration-2 ledger")
    require_hash(SOLVER_DIR / "run_g001_row1_partition.ps1", ROW1_RUNNER_SHA256, "Configuration-2 runner")
    solver = SOLVER_DIR / "order18_topology_free_search_row1.exe"
    require_hash(solver, ROW1_SOLVER_SHA256, "Configuration-2 solver")
    require_hash(SOLVER_DIR / "order18_topology_free_search_row1_snapshot.cpp", ROW1_SOURCE_SHA256, "Configuration-2 source")

    plan = read_csv(
        plan_path,
        ("plan_version", "plan_status", "key", "selector", "coverage_parent", "child_index", "notes"),
        # The frozen provisional CSV did not quote commas in its trailing
        # free-text notes column.  Its hash is pinned above; only that final
        # column is joined, and no authoritative byte is rewritten.
        join_extra_last=True,
    )
    ledger = read_csv(
        ledger_path,
        (
            "key", "selector", "status", "exit_code", "nodes", "states",
            "generated", "wall_seconds", "stdout_path", "stderr_path",
            "solver_sha256", "arguments", "notes",
        ),
    )
    expected = expected_row1_keys()
    require([row["key"] for row in plan] == expected, "Configuration-2 plan roster/order mismatch")
    by_key = unique_map(ledger, "key", "Configuration-2 ledger")
    require(set(by_key) == set(expected), "Configuration-2 ledger roster mismatch")

    jobs: list[Job] = []
    for item in plan:
        require(
            item["plan_version"] == "G001-ROW1-COVER-v3-PROVISIONAL-20260816"
            and item["plan_status"] == "PROVISIONAL_DEEP_SPLIT_PROFILE_PENDING",
            "Configuration-2 plan identity/status mismatch",
        )
        key = item["key"]
        row = by_key[key]
        selector = item["selector"]
        if selector.startswith("root:"):
            selector_argv = ("--root-branch", selector.removeprefix("root:"))
        elif selector.startswith("path:"):
            selector_argv = ("--branch-path", selector.removeprefix("path:"))
        else:
            raise RecomputeError(f"bad Configuration-2 selector: {selector}")
        argv = ("--mode", "g001_row1", *selector_argv, *FLAGS_WITH_MAX)
        require(row["selector"] == selector, f"Configuration-2 selector mismatch: {key}")
        require(row["arguments"] == " ".join(argv), f"Configuration-2 argv mismatch: {key}")
        require(
            row["status"] == "ZERO"
            and row["exit_code"] == "0"
            and row["solver_sha256"].lower() == ROW1_SOLVER_SHA256,
            f"Configuration-2 frozen result mismatch: {key}",
        )
        jobs.append(Job(2, key, key, "direct", solver, argv, "ZERO", int(row["nodes"]), 0, "g001_row1"))
    require(sum(job.expected_nodes for job in jobs) == 193_281_350, "Configuration-2 node total mismatch")
    return jobs


def row7_jobs() -> list[Job]:
    ledger_path = OUTPUTS / "G001_ROW7_PARTITION_RESULTS.csv"
    fanout_path = OUTPUTS / "G001_ROW7_PARTITION_FANOUT.csv"
    require_hash(ledger_path, ROW7_LEDGER_SHA256, "Configuration-8 ledger")
    require_hash(fanout_path, ROW7_FANOUT_SHA256, "Configuration-8 fanout")
    require_hash(SOLVER_DIR / "run_g001_row7_partition.ps1", ROW7_RUNNER_SHA256, "Configuration-8 runner")
    solver = SOLVER_DIR / "order18_topology_free_search.exe"
    require_hash(solver, ROW7_SOLVER_SHA256, "Configuration-8 solver")
    require_hash(SOLVER_DIR / "order18_topology_free_search_production_snapshot.cpp", ROW7_SOURCE_SHA256, "Configuration-8 source")

    ledger = read_csv(
        ledger_path,
        (
            "key", "selector", "status", "exit_code", "nodes", "states",
            "generated", "wall_seconds", "stdout_path", "stderr_path",
            "solver_sha256", "notes",
        ),
    )
    fanout = read_csv(
        fanout_path,
        ("parent_depth", "parent_key", "expected_valid_children", "verification_status", "notes"),
    )
    expected_fanout = (
        ("3", "root", "5"),
        ("4", "0", "3"),
        ("4", "1", "3"),
        ("4", "2", "2"),
        ("4", "3", "2"),
        ("4", "4", "10"),
        ("5", "4_9", "16"),
        ("6", "4_9_15", "23"),
    )
    require(
        tuple(
            (row["parent_depth"], row["parent_key"], row["expected_valid_children"])
            for row in fanout
        ) == expected_fanout
        and all(row["verification_status"] == "VERIFIED" for row in fanout),
        "Configuration-8 fanout roster mismatch",
    )
    expected = expected_row7_keys()
    by_key = unique_map(ledger, "key", "Configuration-8 ledger")
    require(set(by_key) == set(expected), "Configuration-8 ledger roster mismatch")

    jobs: list[Job] = []
    for key in expected:
        row = by_key[key]
        if key.startswith("root_"):
            selector_argv = ("--root-branch", key.removeprefix("root_"))
        else:
            selector_argv = ("--branch-path", key.removeprefix("path_").replace("_", ","))
        require(row["selector"] == " ".join(selector_argv), f"Configuration-8 selector mismatch: {key}")
        require(
            row["status"] == "ZERO"
            and row["exit_code"] == "0"
            and row["solver_sha256"].lower() == ROW7_SOLVER_SHA256,
            f"Configuration-8 frozen result mismatch: {key}",
        )
        argv = ("--mode", "g001_row7", *selector_argv, *FLAGS_WITH_MAX)
        jobs.append(Job(8, key, key, "direct", solver, argv, "ZERO", int(row["nodes"]), 0, "g001_row7"))
    require(sum(job.expected_nodes for job in jobs) == 239_702_053, "Configuration-8 node total mismatch")
    return jobs


def config3_selector(mode: str, partition: str) -> tuple[str, ...]:
    if partition.startswith("root_"):
        return ("--mode", mode, "--root-branch", partition.removeprefix("root_"))
    require(partition.startswith("path_"), f"bad Configuration-3 partition: {partition}")
    return ("--mode", mode, "--branch-path", partition.removeprefix("path_").replace("_", ","))


def validate_config3_release() -> tuple[dict[str, Any], dict[str, Any]]:
    require_hash(CONFIG3_RELEASE / "RELEASE.json", CONFIG3_RELEASE_SHA256, "Configuration-3 release record")
    require_hash(CONFIG3_RELEASE / "RUN_RESULT.json", CONFIG3_RESULT_SHA256, "Configuration-3 run result")
    require_hash(CONFIG3_RELEASE / "MANIFEST.sha256", CONFIG3_MANIFEST_SHA256, "Configuration-3 release manifest")
    require_hash(CONFIG3_VERIFIER, CONFIG3_VERIFIER_SHA256, "Configuration-3 verifier")
    completed = subprocess.run(
        [
            sys.executable, "-E", "-s", "-S", "-B", str(CONFIG3_VERIFIER),
            "--release-root", str(CONFIG3_RELEASE),
        ],
        cwd=REPOSITORY,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    require(completed.returncode == 0, f"Configuration-3 verifier exit: {completed.returncode}")
    require(not completed.stderr, "Configuration-3 verifier wrote stderr")
    release = read_json(CONFIG3_RELEASE / "RELEASE.json")
    result = read_json(CONFIG3_RELEASE / "RUN_RESULT.json")
    expected_marker = (
        "CONFIG3_A2_FROZEN_SPLIT_STRICT_OK "
        f"schema={release['schema']} logical_partitions=47 direct=46 children=22 "
        "logical_nodes=167742832 "
        f"manifest_sha256={CONFIG3_MANIFEST_SHA256} "
        f"release_sha256={CONFIG3_RELEASE_SHA256} "
        f"run_result_sha256={CONFIG3_RESULT_SHA256}\n"
    ).encode("ascii")
    normalized_stdout = completed.stdout.replace(b"\r\n", b"\n").replace(b"\r", b"\n")
    require(normalized_stdout == expected_marker, "Configuration-3 verifier marker mismatch")
    return release, result


def config3_jobs() -> list[Job]:
    ledger_path = OUTPUTS / "A2_MULTI_EDGE_PARTITION_RESULTS.csv"
    require_hash(ledger_path, CONFIG3_LEDGER_SHA256, "Configuration-3 ledger")
    solver = SOLVER_DIR / "a2_topology_free_search_multicover.exe"
    require_hash(solver, CONFIG3_SOLVER_SHA256, "Configuration-3 solver")
    require_hash(SOLVER_DIR / "a2_topology_free_search.cpp", CONFIG3_SOURCE_SHA256, "Configuration-3 source")
    release, result = validate_config3_release()
    expected = expected_config3_keys()
    require(release["logical_roster"] == expected, "Configuration-3 logical roster/order mismatch")
    require(result["logical_roster"] == expected, "Configuration-3 result roster/order mismatch")
    require(tuple(release["common_flags"]) == FLAGS_CONFIG3, "Configuration-3 common flags mismatch")
    require(
        release["engine"]["executable"]["sha256"] == CONFIG3_SOLVER_SHA256,
        "Configuration-3 released solver binding mismatch",
    )

    ledger = read_csv(
        ledger_path,
        ("mode", "partition", "status", "nodes", "wall_seconds", "exit_code", "notes"),
    )
    ledger_by_key = unique_map(
        ({**row, "key": f"{row['mode']}|{row['partition']}"} for row in ledger),
        "key",
        "Configuration-3 ledger",
    )
    require(set(ledger_by_key) == set(expected), "Configuration-3 ledger roster mismatch")

    direct_by_key = {item["key"]: item for item in result["direct_receipts"]}
    target = "a2_separate|path_8_14"
    require(set(direct_by_key) == set(expected) - {target}, "Configuration-3 direct roster mismatch")
    jobs: list[Job] = []
    for logical_index, key in enumerate(expected[:-1]):
        mode, partition = key.split("|", 1)
        item = direct_by_key[key]
        require(item["logical_index"] == logical_index, f"Configuration-3 logical index mismatch: {key}")
        receipt = read_json(contained(CONFIG3_RELEASE, item["receipt"]["path"]))
        prefix = config3_selector(mode, partition)
        argv = (*prefix, *FLAGS_CONFIG3)
        require(tuple(receipt["argv_tail"]) == argv, f"Configuration-3 direct argv mismatch: {key}")
        expected_nodes = int(ledger_by_key[key]["nodes"])
        require(
            receipt["expected"] == {
                "exit_code": 0,
                "frontier": 0,
                "nodes": expected_nodes,
                "solution_topologies": 0,
                "status": "ZERO",
            },
            f"Configuration-3 direct expectation mismatch: {key}",
        )
        jobs.append(Job(3, key, f"direct__{mode}__{partition}", "direct", solver, argv, "ZERO", expected_nodes, 0, mode))

    split = result["split_replacement"]
    require(split["key"] == target and split["logical_index"] == 46, "Configuration-3 split target mismatch")
    frontier_receipt = read_json(contained(CONFIG3_RELEASE, split["census_receipt"]["path"]))
    frontier_argv = (
        "--mode", "a2_separate", "--branch-path", "8,14", "--stop-edges", "7",
        *FLAGS_CONFIG3,
    )
    require(tuple(frontier_receipt["argv_tail"]) == frontier_argv, "Configuration-3 frontier argv mismatch")
    jobs.append(Job(3, target, "split__frontier", "frontier_census", solver, frontier_argv, "FRONTIER", 25, 22, "a2_separate"))

    children = split["children"]
    require([item["index"] for item in children] == list(range(22)), "Configuration-3 split-child roster mismatch")
    for item in children:
        index = item["index"]
        receipt = read_json(contained(CONFIG3_RELEASE, item["receipt"]["path"]))
        argv = ("--mode", "a2_separate", "--branch-path", f"8,14,{index}", *FLAGS_CONFIG3)
        require(tuple(receipt["argv_tail"]) == argv, f"Configuration-3 child argv mismatch: {index}")
        require(receipt["expected"]["nodes"] == item["nodes"], f"Configuration-3 child node mismatch: {index}")
        jobs.append(Job(3, target, f"split__child_{index:03d}", "split_child", solver, argv, "ZERO", item["nodes"], 0, "a2_separate"))

    direct_nodes = sum(job.expected_nodes for job in jobs if job.category == "direct")
    child_nodes = sum(job.expected_nodes for job in jobs if job.category == "split_child")
    require(direct_nodes == 124_893_923, "Configuration-3 direct-node total mismatch")
    require(child_nodes == 42_848_972, "Configuration-3 child-node total mismatch")
    require(direct_nodes + child_nodes - 63 == 167_742_832, "Configuration-3 logical-node identity mismatch")
    return jobs


def parse_result(raw: bytes, label: str) -> dict[str, str]:
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise RecomputeError(f"non-UTF-8 solver stdout: {label}") from exc
    lines = [line for line in text.replace("\r\n", "\n").replace("\r", "\n").split("\n") if line.startswith("RESULT ")]
    require(len(lines) == 1, f"expected one RESULT line: {label}")
    fields: dict[str, str] = {}
    for token in lines[0].removeprefix("RESULT ").split(" "):
        require("=" in token, f"malformed RESULT token: {label}: {token!r}")
        key, value = token.split("=", 1)
        require(key and key not in fields, f"duplicate/empty RESULT field: {label}: {key!r}")
        fields[key] = value
    return fields


def run_job(job: Job, run_root: Path) -> dict[str, Any]:
    output = run_root / f"configuration_{job.configuration}" / job.process_key
    output.mkdir(mode=0o700, parents=True, exist_ok=False)
    stdout_path = output / "stdout.txt"
    stderr_path = output / "stderr.txt"
    command = [str(job.solver), *job.argv]
    started = time.time()
    with stdout_path.open("xb") as stdout, stderr_path.open("xb") as stderr:
        completed = subprocess.run(
            command,
            cwd=job.solver.parent,
            stdin=subprocess.DEVNULL,
            stdout=stdout,
            stderr=stderr,
            check=False,
        )
    elapsed = time.time() - started
    fields = parse_result(stdout_path.read_bytes(), job.process_key)
    if completed.returncode == 2 or fields.get("status") == "FOUND":
        raise FoundEvent(f"unexpected FOUND in {job.process_key}; output retained at {output}")
    require(completed.returncode == 0, f"solver exit {completed.returncode}: {job.process_key}")
    require(stderr_path.stat().st_size == 0, f"nonempty solver stderr: {job.process_key}")
    require(fields.get("status") == job.expected_status, f"status mismatch: {job.process_key}")
    require(fields.get("mode") == job.expected_mode, f"mode mismatch: {job.process_key}")
    require(int(fields.get("nodes", "-1")) == job.expected_nodes, f"node mismatch: {job.process_key}")
    require(int(fields.get("frontier", "-1")) == job.expected_frontier, f"frontier mismatch: {job.process_key}")
    require(int(fields.get("solution_topologies", "-1")) == 0, f"solution count mismatch: {job.process_key}")
    require(fields.get("multi_cover") == "on", f"multi-cover inactive: {job.process_key}")
    receipt = {
        "schema": "LEECH18_PRIOR_THREE_FRESH_PROCESS_V1",
        "configuration": job.configuration,
        "logical_key": job.logical_key,
        "process_key": job.process_key,
        "category": job.category,
        "solver_sha256": sha256_file(job.solver),
        "argv": list(job.argv),
        "exit_code": completed.returncode,
        "elapsed_seconds": elapsed,
        "result": fields,
        "stdout": {"bytes": stdout_path.stat().st_size, "sha256": sha256_file(stdout_path)},
        "stderr": {"bytes": stderr_path.stat().st_size, "sha256": sha256_file(stderr_path)},
    }
    (output / "RECEIPT.json").write_bytes(canonical_json(receipt))
    print(
        f"PROCESS_OK configuration={job.configuration} process={job.process_key} "
        f"status={job.expected_status} nodes={job.expected_nodes}",
        flush=True,
    )
    return receipt


def assemble_jobs() -> tuple[list[Job], list[Job], list[Job]]:
    validate_bundled_dependencies()
    configuration2 = row1_jobs()
    configuration3 = config3_jobs()
    configuration8 = row7_jobs()
    require(len(configuration2) == 79, "Configuration-2 process count mismatch")
    require(len(configuration3) == 69, "Configuration-3 physical process count mismatch")
    require(len(configuration8) == 52, "Configuration-8 process count mismatch")
    return configuration2, configuration3, configuration8


def print_roster(groups: Sequence[Sequence[Job]]) -> None:
    for group in groups:
        for job in group:
            print(
                f"configuration={job.configuration} logical_key={job.logical_key} "
                f"process_key={job.process_key} command={subprocess.list2cmdline([str(job.solver), *job.argv])}"
            )
    print(
        "LEECH18_PRIOR_THREE_ROSTER_OK configuration2=79 "
        "configuration3_logical=47 configuration3_zero_processes=68 "
        "configuration3_census_processes=1 configuration8=52 "
        "physical_processes=200 logical_partitions=178 logical_nodes=600726235"
    )


def recompute(groups: Sequence[Sequence[Job]], run_root: Path) -> None:
    require(os.name == "nt", "the preserved prior-three executables require Windows")
    run_root = Path(os.path.abspath(os.fspath(run_root)))
    require(not os.path.lexists(run_root), f"run root already exists: {run_root}")
    require(run_root.parent.is_dir(), f"run-root parent is missing: {run_root.parent}")
    validate_authoritative_coverage()
    run_root.mkdir(mode=0o700)
    receipts: list[dict[str, Any]] = []
    for group in groups:
        for job in group:
            receipts.append(run_job(job, run_root))

    configuration2_nodes = sum(
        int(item["result"]["nodes"]) for item in receipts if item["configuration"] == 2
    )
    configuration8_nodes = sum(
        int(item["result"]["nodes"]) for item in receipts if item["configuration"] == 8
    )
    config3_direct = sum(
        int(item["result"]["nodes"])
        for item in receipts
        if item["configuration"] == 3 and item["category"] == "direct"
    )
    config3_children = sum(
        int(item["result"]["nodes"])
        for item in receipts
        if item["configuration"] == 3 and item["category"] == "split_child"
    )
    configuration3_nodes = config3_direct + config3_children - 63
    require(configuration2_nodes == 193_281_350, "fresh Configuration-2 node total mismatch")
    require(configuration3_nodes == 167_742_832, "fresh Configuration-3 logical node total mismatch")
    require(configuration8_nodes == 239_702_053, "fresh Configuration-8 node total mismatch")
    total = configuration2_nodes + configuration3_nodes + configuration8_nodes
    require(total == 600_726_235, "fresh prior-three logical node total mismatch")
    summary = {
        "schema": "LEECH18_PRIOR_THREE_FULL_RECOMPUTATION_V1",
        "status": "ZERO_COMPLETE",
        "logical_partitions": 178,
        "physical_processes": 200,
        "zero_processes": 199,
        "frontier_census_processes": 1,
        "nodes": {
            "configuration_2": configuration2_nodes,
            "configuration_3_logical": configuration3_nodes,
            "configuration_3_direct": config3_direct,
            "configuration_3_split_children": config3_children,
            "configuration_3_normalization_subtraction": 63,
            "configuration_8": configuration8_nodes,
            "logical_total": total,
        },
        "receipts": receipts,
    }
    (run_root / "RECOMPUTATION_SUMMARY.json").write_bytes(canonical_json(summary))
    print(
        "LEECH18_PRIOR_THREE_FULL_RECOMPUTATION_OK logical_partitions=178 "
        "physical_processes=200 zero_processes=199 logical_nodes=600726235"
    )


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    selection = parser.add_mutually_exclusive_group(required=True)
    selection.add_argument("--list-only", action="store_true")
    selection.add_argument("--run-root", type=Path)
    args = parser.parse_args(argv)
    try:
        groups = assemble_jobs()
        if args.list_only:
            print_roster(groups)
        else:
            recompute(groups, args.run_root)
        return 0
    except FoundEvent as exc:
        print(f"LEECH18_PRIOR_THREE_FOUND: {exc}", file=sys.stderr)
        return 2
    except (RecomputeError, OSError, ValueError, KeyError, TypeError) as exc:
        print(f"LEECH18_PRIOR_THREE_RECOMPUTATION_FAIL: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
