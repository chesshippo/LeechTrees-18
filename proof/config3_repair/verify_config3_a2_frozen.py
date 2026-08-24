#!/usr/bin/env python3
"""Independent verifier for the frozen Config3/A2 split release.

Only Python's standard library is used.  The verifier reconstructs the exact
logical roster, argv tails, expected node counts, split-child roster, tree,
and source/binary pins.  It reparses every raw RESULT line and emits the
publication marker only after a final byte-for-byte rehash.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import sys
from pathlib import Path, PurePosixPath
from typing import Any


RELEASE_SCHEMA = "config3-a2-frozen-split-release-v1"
RUN_RESULT_SCHEMA = "config3-a2-frozen-split-run-result-v1"
DIRECT_SCHEMA = "config3-a2-frozen-direct-receipt-v1"
FRONTIER_SCHEMA = "config3-a2-frozen-split-frontier-receipt-v1"
CHILD_SCHEMA = "config3-a2-frozen-split-child-receipt-v1"

ENGINE_RELATIVE = (
    "computation/evidence/production/"
    "prior_three_configurations/work/a2_solver/a2_topology_free_search_multicover.exe"
)
ENGINE_SHA256 = "65bbaa57e5b462663b3656bc77499cc5956053f4137878c21072c99a327483f3"
PARENT_PLAN = {
    "bytes": 22457,
    "sha256": "851e3b2f45923b94a74c87b8142a26eeabde6428a53ea0ed08c11dead3094741",
}
SPLIT_PLAN = {
    "bytes": 4505,
    "sha256": "cb36d3eec541471ec2bbe952113189e476a991a8f2a5187313b3312dbff2abee",
}
TRANSIENT_REPLACEMENT = {
    "bytes": 124420,
    "sha256": "36d3437d3748a5c960882eac12969ec72af655f6b5147f453b960fa35ecdee07",
}

SOURCE_PINS = {
    "source": (
        "computation/evidence/production/"
        "prior_three_configurations/work/a2_solver/a2_topology_free_search.cpp",
        "e8dedc62323152ba586f9c8607d119440c8be9927ec4d38e546ba11de9100e9c",
    ),
    "exact_cover_header": (
        "computation/evidence/production/"
        "prior_three_configurations/work/a2_solver/a2_multi_edge_exact_cover.hpp",
        "c156eae52bceef28db0df1a38d10dea253de09e5f627d0952a6bb1b9356cd813",
    ),
    "optimized_header": (
        "computation/evidence/production/"
        "prior_three_configurations/work/a2_solver/a2_multi_edge_exact_cover_optimized.hpp",
        "5320c920e800ce2f9e2348b90d672e26cddd748b43bc02bc24b9146dedb5e48b",
    ),
    "stronger_header": (
        "computation/evidence/production/"
        "prior_three_configurations/work/a2_solver/a2_multi_edge_stronger_relaxation.hpp",
        "e58f917a631c48f2419835d41c2b0ee164f0d24f44ba489c152b9c00cddbbd5c",
    ),
    "expected_ledger": (
        "computation/evidence/production/"
        "prior_three_configurations/outputs/A2_MULTI_EDGE_PARTITION_RESULTS.csv",
        "bc6a5909d2de7b0cbc0e1a886a03c675b92419c8c4e553ad944e1a123dbc93ac",
    ),
}

TOOL_PATHS = {
    "exporter": "proof/config3_repair/freeze_config3_a2_evidence.py",
    "independent_verifier": "proof/config3_repair/verify_config3_a2_frozen.py",
    "split_harness": "proof/config3_repair/run_config3_a2_path8_14_split.py",
    "base_harness": "proof/config3_repair/rerun_config3_a2.py",
    "engine_runner": "proof/config3_repair/run_config3_a2_engines.py",
}

COMMON_FLAGS = [
    "--multi-edge-cover",
    "--multi-edge-cover-no-hall",
    "--multi-edge-cover-budget",
    "100",
    "--multi-edge-cover-no-exact-hall",
]

EXPECTED_ROWS = [
    ("a2_attached", "root_0", 1_078_930),
    ("a2_attached", "path_1_0", 100_668),
    ("a2_attached", "path_1_1", 32_841),
    ("a2_attached", "path_1_2", 1_955_081),
    ("a2_attached", "path_1_3", 689_834),
    ("a2_attached", "path_1_4", 2_080_662),
    ("a2_attached", "path_1_5", 11_712_174),
    ("a2_separate", "root_0", 925_924),
    ("a2_separate", "root_1", 1_501_520),
    ("a2_separate", "root_2", 614_692),
    ("a2_separate", "root_3", 9_568_357),
    ("a2_separate", "path_4_0", 67_168),
    ("a2_separate", "path_4_1", 1_089_740),
    ("a2_separate", "path_4_2", 384_840),
    ("a2_separate", "path_4_3", 252_847),
    ("a2_separate", "path_4_4", 1_700_119),
    ("a2_separate", "path_4_5", 8_532_970),
    ("a2_separate", "path_5_0", 99_803),
    ("a2_separate", "path_5_1", 807_662),
    ("a2_separate", "path_5_2", 573_306),
    ("a2_separate", "path_5_3", 1_624_074),
    ("a2_separate", "path_5_4", 9_076_460),
    ("a2_separate", "path_6_0", 199_150),
    ("a2_separate", "path_6_1", 5_945_428),
    ("a2_separate", "path_7_0", 92_157),
    ("a2_separate", "path_7_1", 69_307),
    ("a2_separate", "path_7_2", 1_485_015),
    ("a2_separate", "path_7_3", 1_412_415),
    ("a2_separate", "path_7_4", 217),
    ("a2_separate", "path_7_5", 792_173),
    ("a2_separate", "path_7_6", 745_559),
    ("a2_separate", "path_7_7", 10_624_204),
    ("a2_separate", "path_8_0", 706_489),
    ("a2_separate", "path_8_1", 519_584),
    ("a2_separate", "path_8_2", 323_707),
    ("a2_separate", "path_8_3", 1_183_705),
    ("a2_separate", "path_8_4", 528_072),
    ("a2_separate", "path_8_5", 482_285),
    ("a2_separate", "path_8_6", 138_810),
    ("a2_separate", "path_8_7", 5_520_491),
    ("a2_separate", "path_8_8", 7_232_468),
    ("a2_separate", "path_8_9", 9_217_230),
    ("a2_separate", "path_8_10", 3_692_830),
    ("a2_separate", "path_8_11", 550_259),
    ("a2_separate", "path_8_12", 9_442_990),
    ("a2_separate", "path_8_13", 9_519_706),
    ("a2_separate", "path_8_14", 42_848_909),
]

TARGET_KEY = "a2_separate|path_8_14"
CHILD_NODES = [
    613_263,
    151_044,
    113_834,
    208_504,
    129_957,
    690_996,
    327_187,
    285_624,
    303_586,
    93_109,
    47_875,
    2_747_480,
    2_802_625,
    4_374_904,
    1_794_084,
    257_576,
    351_480,
    404_615,
    4_460_848,
    4_409_631,
    4_156_885,
    14_123_865,
]

M = 22
TARGET_NODES = 42_848_909
CHILD_NODE_SUM = 42_848_972
NORMALIZATION_SUBTRACTION = 63
DIRECT_NODE_SUM = 124_893_923
LOGICAL_NODE_SUM = 167_742_832

RELEASE_FIELDS = {
    "schema",
    "status",
    "scope",
    "evidence_origin",
    "engine",
    "source_inputs",
    "tooling",
    "parent_plan_provenance",
    "split_plan_provenance",
    "transient_replacement_provenance",
    "common_flags",
    "logical_roster",
    "counts",
    "split_proof",
    "run_result",
}
RUN_RESULT_FIELDS = {
    "schema",
    "status",
    "release_schema",
    "engine_sha256",
    "logical_partition_count",
    "logical_node_sum",
    "logical_roster",
    "direct_partition_count",
    "direct_node_sum",
    "direct_receipts",
    "split_replacement",
    "physical_zero_process_count",
    "frontier_census_process_count",
}
DIRECT_FIELDS = {
    "schema",
    "status",
    "kind",
    "logical_index",
    "key",
    "mode",
    "partition",
    "argv_tail",
    "expected",
    "observed",
    "bindings",
    "transient_receipt_provenance",
    "stdout",
    "stderr",
}
FRONTIER_FIELDS = {
    "schema",
    "status",
    "kind",
    "logical_key",
    "argv_tail",
    "expected",
    "observed",
    "bindings",
    "transient_receipt_provenance",
    "stdout",
    "stderr",
}
CHILD_FIELDS = FRONTIER_FIELDS | {"child_index"}


class VerifyError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise VerifyError(message)


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while block := stream.read(1024 * 1024):
            digest.update(block)
    return digest.hexdigest()


def canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode("utf-8")


def strict_json(path: Path) -> dict[str, Any]:
    raw = path.read_bytes()

    def no_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        value: dict[str, Any] = {}
        for key, item in pairs:
            require(key not in value, f"duplicate JSON key {key!r} in {path}")
            value[key] = item
        return value

    try:
        value = json.loads(raw.decode("utf-8"), object_pairs_hook=no_duplicates)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise VerifyError(f"invalid strict JSON in {path}: {exc}") from exc
    require(isinstance(value, dict), f"JSON root is not an object: {path}")
    require(canonical_json_bytes(value) == raw, f"noncanonical JSON bytes: {path}")
    reject_private_strings(value, str(path))
    return value


def reject_private_strings(value: Any, label: str) -> None:
    if isinstance(value, dict):
        forbidden_keys = {"workspace", "hostname", "host", "username", "user", "machine_id"}
        require(not (set(value) & forbidden_keys), f"private/host key in {label}")
        for item in value.values():
            reject_private_strings(item, label)
    elif isinstance(value, list):
        for item in value:
            reject_private_strings(item, label)
    elif isinstance(value, str):
        require("\\" not in value and "\x00" not in value, f"unsafe/private string in {label}")
        require(re.search(r"(?:^|[^A-Za-z])[A-Za-z]:/", value) is None, f"absolute drive path in {label}")
        require(not value.startswith(("/", "//", "file://")), f"absolute/URI path in {label}")


def is_reparse(path: Path) -> bool:
    try:
        st = path.lstat()
    except OSError as exc:
        raise VerifyError(f"cannot lstat {path}: {exc}") from exc
    flag = getattr(stat, "FILE_ATTRIBUTE_REPARSE_POINT", 0)
    return bool(getattr(st, "st_file_attributes", 0) & flag)


def ensure_plain(path: Path, want_dir: bool) -> None:
    require(path.exists(), f"missing path: {path}")
    require(not path.is_symlink(), f"symlink rejected: {path}")
    junction = getattr(path, "is_junction", None)
    require(not (junction is not None and junction()), f"junction rejected: {path}")
    require(not is_reparse(path), f"reparse-point path rejected: {path}")
    require(path.is_dir() if want_dir else path.is_file(), f"wrong path type: {path}")
    if not want_dir:
        require(path.stat().st_nlink == 1, f"hardlinked file rejected: {path}")


def safe_relative(text: str) -> str:
    require("\\" not in text and text != "", f"unsafe relative path: {text!r}")
    pure = PurePosixPath(text)
    require(not pure.is_absolute(), f"absolute release path: {text!r}")
    require(all(part not in ("", ".", "..") for part in pure.parts), f"unsafe release path: {text!r}")
    require(pure.as_posix() == text, f"noncanonical release path: {text!r}")
    return text


def portable_ref(path: Path, relative: str) -> dict[str, Any]:
    return {"path": safe_relative(relative), "bytes": path.stat().st_size, "sha256": sha256_file(path)}


def workspace_ref(workspace: Path, relative: str) -> dict[str, Any]:
    path = workspace / safe_relative(relative)
    ensure_plain(path, False)
    return {"relative_path": relative, "bytes": path.stat().st_size, "sha256": sha256_file(path)}


def key(mode: str, partition: str) -> str:
    return f"{mode}|{partition}"


def roster() -> list[str]:
    result = [key(mode, partition) for mode, partition, _ in EXPECTED_ROWS]
    require(len(result) == 47 and len(set(result)) == 47, "internal roster error")
    return result


def selector_tail(mode: str, partition: str) -> list[str]:
    root = re.fullmatch(r"root_([0-9]+)", partition)
    path = re.fullmatch(r"path_([0-9]+)_([0-9]+)", partition)
    require(root is not None or path is not None, f"internal bad partition: {partition}")
    selector = ["--root-branch", root.group(1)] if root else ["--branch-path", f"{path.group(1)},{path.group(2)}"]
    return ["--mode", mode, *selector, *COMMON_FLAGS]


def frontier_tail() -> list[str]:
    return ["--mode", "a2_separate", "--branch-path", "8,14", "--stop-edges", "7", *COMMON_FLAGS]


def child_tail(index: int) -> list[str]:
    return ["--mode", "a2_separate", "--branch-path", f"8,14,{index}", *COMMON_FLAGS]


def parse_result(raw: bytes, label: str) -> dict[str, str]:
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise VerifyError(f"stdout is not UTF-8 ({label}): {exc}") from exc
    lines = [line for line in text.splitlines() if line]
    require(len(lines) == 1 and lines[0].startswith("RESULT "), f"not exactly one RESULT line: {label}")
    fields: dict[str, str] = {}
    for token in lines[0].split()[1:]:
        require("=" in token, f"malformed RESULT token in {label}: {token!r}")
        name, value = token.split("=", 1)
        require(name not in fields, f"duplicate RESULT field in {label}: {name}")
        fields[name] = value
    return fields


def nonnegative(value: str | None, label: str) -> int:
    require(value is not None and re.fullmatch(r"0|[1-9][0-9]*", value) is not None, f"bad integer {label}: {value!r}")
    return int(value)


def count_map(value: str | None, label: str) -> dict[int, int]:
    require(value is not None and value.endswith(","), f"bad count map {label}")
    result: dict[int, int] = {}
    for item in value[:-1].split(",") if value[:-1] else []:
        match = re.fullmatch(r"(0|[1-9][0-9]*):(0|[1-9][0-9]*)", item)
        require(match is not None, f"malformed count map item in {label}: {item!r}")
        index, count = int(match.group(1)), int(match.group(2))
        require(index not in result, f"duplicate count-map key in {label}: {index}")
        result[index] = count
    return result


def validate_zero_result(fields: dict[str, str], mode: str, nodes: int, label: str) -> None:
    expected = {
        "mode": mode,
        "status": "ZERO",
        "nodes": str(nodes),
        "solution_topologies": "0",
        "frontier": "0",
    }
    for name, value in expected.items():
        require(fields.get(name) == value, f"RESULT {name} mismatch in {label}")


def validate_direct_fanout(fields: dict[str, str], mode: str, partition: str, label: str) -> None:
    if partition.startswith("root_"):
        expected = 2 if mode == "a2_attached" else 9
        require(fields.get("root_valid") == str(expected), f"root_valid mismatch in {label}")
        return
    child = count_map(fields.get("child_max"), f"{label} child_max")
    if mode == "a2_attached":
        require(child.get(4) == 2 and child.get(5) == 6, f"attached fan-out mismatch in {label}")
    else:
        split_depth = int(partition.split("_")[1])
        expected_depth5 = {4: 6, 5: 5, 6: 2, 7: 8, 8: 15}[split_depth]
        require(child.get(4) == 9 and child.get(5) == expected_depth5, f"separate fan-out mismatch in {label}")


def check_ref(root: Path, ref: Any, expected_path: str) -> Path:
    require(isinstance(ref, dict) and set(ref) == {"path", "bytes", "sha256"}, f"bad file ref for {expected_path}")
    require(ref["path"] == safe_relative(expected_path), f"file-ref path mismatch: {expected_path}")
    path = root / expected_path
    ensure_plain(path, False)
    require(ref == portable_ref(path, expected_path), f"file-ref bytes/hash mismatch: {expected_path}")
    return path


def verify_sidecar(path: Path) -> None:
    sidecar = path.with_name(path.name + ".sha256")
    expected = f"{sha256_file(path)}  {path.name}\n".encode("ascii")
    require(sidecar.read_bytes() == expected, f"bad SHA-256 sidecar: {sidecar}")


def expected_tree() -> tuple[set[str], set[str]]:
    dirs = {"", "direct", "split", "split/frontier", "split/children"}
    files = {"RELEASE.json", "RELEASE.json.sha256", "RUN_RESULT.json", "RUN_RESULT.json.sha256", "MANIFEST.sha256"}
    for mode, partition, _ in EXPECTED_ROWS:
        if key(mode, partition) == TARGET_KEY:
            continue
        directory = f"direct/{mode}__{partition}"
        dirs.add(directory)
        files.update(f"{directory}/{name}" for name in ("RECEIPT.json", "RECEIPT.json.sha256", "stdout.txt", "stderr.txt"))
    files.update(f"split/frontier/{name}" for name in ("RECEIPT.json", "RECEIPT.json.sha256", "stdout.txt", "stderr.txt"))
    for index in range(M):
        directory = f"split/children/k_{index:03d}"
        dirs.add(directory)
        files.update(f"{directory}/{name}" for name in ("RECEIPT.json", "RECEIPT.json.sha256", "stdout.txt", "stderr.txt"))
    return dirs, files


def inventory_tree(root: Path) -> tuple[set[str], set[str]]:
    actual_dirs: set[str] = set()
    actual_files: set[str] = set()
    for current, dirnames, filenames in os.walk(root, topdown=True, followlinks=False):
        current_path = Path(current)
        ensure_plain(current_path, True)
        relative_dir = current_path.relative_to(root).as_posix()
        actual_dirs.add("" if relative_dir == "." else relative_dir)
        for name in list(dirnames):
            ensure_plain(current_path / name, True)
        for name in filenames:
            path = current_path / name
            ensure_plain(path, False)
            actual_files.add(path.relative_to(root).as_posix())
    return actual_dirs, actual_files


def verify_manifest(root: Path, expected_files: set[str]) -> dict[str, str]:
    path = root / "MANIFEST.sha256"
    raw = path.read_bytes()
    require(raw.endswith(b"\n") and b"\r" not in raw, "manifest is not canonical LF text")
    entries: dict[str, str] = {}
    lines = raw.decode("ascii").splitlines()
    for line in lines:
        match = re.fullmatch(r"([0-9a-f]{64})  (.+)", line)
        require(match is not None, f"malformed manifest line: {line!r}")
        digest, relative = match.group(1), safe_relative(match.group(2))
        require(relative not in entries, f"duplicate manifest path: {relative}")
        entries[relative] = digest
    require(list(entries) == sorted(entries), "manifest paths are not sorted")
    require(set(entries) == expected_files - {"MANIFEST.sha256"}, "manifest exact file set mismatch")
    for relative, digest in entries.items():
        require(sha256_file(root / relative) == digest, f"manifest digest mismatch: {relative}")
    return entries


def expected_sources(workspace: Path) -> dict[str, dict[str, Any]]:
    result: dict[str, dict[str, Any]] = {}
    for name, (relative, digest) in sorted(SOURCE_PINS.items()):
        ref = workspace_ref(workspace, relative)
        require(ref["sha256"] == digest, f"current source pin mismatch: {name}")
        result[name] = ref
    return result


def expected_tooling(workspace: Path) -> dict[str, dict[str, Any]]:
    return {name: workspace_ref(workspace, relative) for name, relative in sorted(TOOL_PATHS.items())}


def expected_counts() -> dict[str, int]:
    return {
        "logical_partitions": 47,
        "direct_partitions": 46,
        "split_children": M,
        "zero_processes": 46 + M,
        "frontier_censuses": 1,
        "logical_nodes": LOGICAL_NODE_SUM,
        "direct_nodes": DIRECT_NODE_SUM,
        "child_reported_nodes": CHILD_NODE_SUM,
        "normalization_subtraction": NORMALIZATION_SUBTRACTION,
        "normalized_parent_nodes": TARGET_NODES,
    }


def expected_split_proof() -> dict[str, Any]:
    return {
        "target_key": TARGET_KEY,
        "child_count": M,
        "child_indices": list(range(M)),
        "repeated_prefix_calls_per_child": 3,
        "node_identity": "parent_nodes=sum(child_nodes)-3*(M-1)",
        "fanout": {
            "census_nodes": 25,
            "census_frontier": 22,
            "census_depth": "4:1,5:1,6:1,7:22,",
            "census_child_max": "4:9,5:15,6:22,",
            "exact_child_roster": "0..21",
        },
        "source_semantics": {
            "source_sha256": SOURCE_PINS["source"][1],
            "branch_path_parser_lines": "693-700",
            "deterministic_candidate_sort_lines": "536-538",
            "contiguous_branch_counter_lines": "540-552",
            "child_max_before_selector_filter_lines": "553-557",
            "recursion_after_selector_filter_lines": "564-566",
            "nodes_first_in_rec_lines": "411-414",
            "ordinary_separate_branch_path_base_depth_lines": "881-882",
            "seed_depth_four_lines": "900-904",
            "candidate_static_upper_bound": "C(18,2)=153",
        },
    }


def bindings(split: bool) -> dict[str, str]:
    result = {
        "engine_sha256": ENGINE_SHA256,
        "parent_plan_sha256": PARENT_PLAN["sha256"],
        "source_sha256": SOURCE_PINS["source"][1],
        "ledger_sha256": SOURCE_PINS["expected_ledger"][1],
    }
    if split:
        result["split_plan_sha256"] = SPLIT_PLAN["sha256"]
    return result


def validate_provenance(value: Any, label: str) -> None:
    require(isinstance(value, dict) and set(value) == {"bytes", "sha256"}, f"bad transient provenance: {label}")
    require(isinstance(value["bytes"], int) and not isinstance(value["bytes"], bool) and value["bytes"] > 0, f"bad provenance bytes: {label}")
    require(isinstance(value["sha256"], str) and re.fullmatch(r"[0-9a-f]{64}", value["sha256"]) is not None, f"bad provenance hash: {label}")


def validate_direct_receipt(
    root: Path,
    relative: str,
    logical_index: int,
    mode: str,
    partition: str,
    nodes: int,
) -> tuple[dict[str, Any], dict[str, Any]]:
    path = root / relative
    value = strict_json(path)
    require(set(value) == DIRECT_FIELDS, f"direct receipt field set mismatch: {relative}")
    expected = {
        "schema": DIRECT_SCHEMA,
        "status": "PASS",
        "kind": "direct",
        "logical_index": logical_index,
        "key": key(mode, partition),
        "mode": mode,
        "partition": partition,
        "argv_tail": selector_tail(mode, partition),
        "expected": {"exit_code": 0, "status": "ZERO", "nodes": nodes, "solution_topologies": 0, "frontier": 0},
        "bindings": bindings(False),
    }
    for name, item in expected.items():
        require(value[name] == item, f"direct receipt {name} mismatch: {relative}")
    validate_provenance(value["transient_receipt_provenance"], relative)
    directory = str(PurePosixPath(relative).parent)
    stdout_path = check_ref(root, value["stdout"], f"{directory}/stdout.txt")
    stderr_path = check_ref(root, value["stderr"], f"{directory}/stderr.txt")
    require(stderr_path.stat().st_size == 0, f"nonempty direct stderr: {relative}")
    fields = parse_result(stdout_path.read_bytes(), relative)
    validate_zero_result(fields, mode, nodes, relative)
    validate_direct_fanout(fields, mode, partition, relative)
    require(value["observed"] == {"exit_code": 0, "result_fields": fields}, f"direct observed mismatch: {relative}")
    verify_sidecar(path)
    return value, portable_ref(path, relative)


def validate_frontier_receipt(root: Path) -> tuple[dict[str, Any], dict[str, Any]]:
    relative = "split/frontier/RECEIPT.json"
    path = root / relative
    value = strict_json(path)
    require(set(value) == FRONTIER_FIELDS, "frontier receipt field set mismatch")
    required = {
        "schema": FRONTIER_SCHEMA,
        "status": "PASS",
        "kind": "frontier_census",
        "logical_key": TARGET_KEY,
        "argv_tail": frontier_tail(),
        "expected": {"exit_code": 0, "status": "FRONTIER", "nodes": 25, "solution_topologies": 0, "child_count": M},
        "bindings": bindings(True),
    }
    for name, item in required.items():
        require(value[name] == item, f"frontier receipt {name} mismatch")
    validate_provenance(value["transient_receipt_provenance"], relative)
    stdout_path = check_ref(root, value["stdout"], "split/frontier/stdout.txt")
    stderr_path = check_ref(root, value["stderr"], "split/frontier/stderr.txt")
    require(stderr_path.stat().st_size == 0, "nonempty frontier stderr")
    fields = parse_result(stdout_path.read_bytes(), relative)
    for name, item in {
        "mode": "a2_separate",
        "status": "FRONTIER",
        "nodes": "25",
        "solution_topologies": "0",
        "root_valid": "9",
        "frontier": "22",
        "depth": "4:1,5:1,6:1,7:22,",
        "child_max": "4:9,5:15,6:22,",
    }.items():
        require(fields.get(name) == item, f"frontier RESULT {name} mismatch")
    require(value["observed"] == {"exit_code": 0, "result_fields": fields}, "frontier observed mismatch")
    verify_sidecar(path)
    return value, portable_ref(path, relative)


def validate_child_receipt(root: Path, index: int, nodes: int) -> tuple[dict[str, Any], dict[str, Any]]:
    directory = f"split/children/k_{index:03d}"
    relative = f"{directory}/RECEIPT.json"
    path = root / relative
    value = strict_json(path)
    require(set(value) == CHILD_FIELDS, f"child receipt field set mismatch: k={index}")
    required = {
        "schema": CHILD_SCHEMA,
        "status": "PASS",
        "kind": "split_child",
        "logical_key": TARGET_KEY,
        "child_index": index,
        "argv_tail": child_tail(index),
        "expected": {"exit_code": 0, "status": "ZERO", "nodes": nodes, "solution_topologies": 0, "frontier": 0},
        "bindings": bindings(True),
    }
    for name, item in required.items():
        require(value[name] == item, f"child receipt {name} mismatch: k={index}")
    validate_provenance(value["transient_receipt_provenance"], relative)
    stdout_path = check_ref(root, value["stdout"], f"{directory}/stdout.txt")
    stderr_path = check_ref(root, value["stderr"], f"{directory}/stderr.txt")
    require(stderr_path.stat().st_size == 0, f"nonempty child stderr: k={index}")
    fields = parse_result(stdout_path.read_bytes(), relative)
    validate_zero_result(fields, "a2_separate", nodes, relative)
    require(fields.get("root_valid") == "9", f"child root_valid mismatch: k={index}")
    child_max = count_map(fields.get("child_max"), f"child {index} child_max")
    require(child_max.get(4) == 9 and child_max.get(5) == 15 and child_max.get(6) == M, f"child fan-out mismatch: k={index}")
    depth = count_map(fields.get("depth"), f"child {index} depth")
    require(all(depth.get(level) == 1 for level in (4, 5, 6, 7)), f"child selected-prefix depth mismatch: k={index}")
    require(value["observed"] == {"exit_code": 0, "result_fields": fields}, f"child observed mismatch: k={index}")
    verify_sidecar(path)
    return value, portable_ref(path, relative)


def verify_release(root: Path) -> dict[str, str]:
    root = root.resolve(strict=True)
    ensure_plain(root, True)
    workspace = Path(__file__).resolve().parents[2]
    for ancestor in [root, *root.parents]:
        ensure_plain(ancestor, True)
        if ancestor == workspace:
            break
    else:
        raise VerifyError("release root is not inside the verifier workspace")

    expected_dirs, expected_files = expected_tree()
    actual_dirs, actual_files = inventory_tree(root)
    require(actual_dirs == expected_dirs, f"release directory set mismatch: missing={sorted(expected_dirs-actual_dirs)} extras={sorted(actual_dirs-expected_dirs)}")
    require(actual_files == expected_files, f"release file set mismatch: missing={sorted(expected_files-actual_files)} extras={sorted(actual_files-expected_files)}")
    initial_manifest = verify_manifest(root, expected_files)

    release_path = root / "RELEASE.json"
    run_result_path = root / "RUN_RESULT.json"
    release = strict_json(release_path)
    run_result = strict_json(run_result_path)
    verify_sidecar(release_path)
    verify_sidecar(run_result_path)
    require(set(release) == RELEASE_FIELDS, "RELEASE.json exact field set mismatch")
    require(set(run_result) == RUN_RESULT_FIELDS, "RUN_RESULT.json exact field set mismatch")

    sources = expected_sources(workspace)
    tooling = expected_tooling(workspace)
    executable_ref = workspace_ref(workspace, ENGINE_RELATIVE)
    require(executable_ref["sha256"] == ENGINE_SHA256, "current preserved executable pin mismatch")
    logical_roster = roster()
    required_release = {
        "schema": RELEASE_SCHEMA,
        "status": "PASS",
        "scope": "fresh Config3/A2 evidence: 46 direct logical partitions plus a split replacement for a2_separate|path_8_14",
        "evidence_origin": "freshly generated for this proof; not the missing original raw archive",
        "engine": {
            "name": "preserved",
            "kind": "hash-pinned-historical-production-binary",
            "executable": executable_ref,
            "source_claim": "historical package binding; not a reproducible-build proof",
        },
        "source_inputs": sources,
        "tooling": tooling,
        "parent_plan_provenance": PARENT_PLAN,
        "split_plan_provenance": SPLIT_PLAN,
        "transient_replacement_provenance": TRANSIENT_REPLACEMENT,
        "common_flags": COMMON_FLAGS,
        "logical_roster": logical_roster,
        "counts": expected_counts(),
        "split_proof": expected_split_proof(),
        "run_result": portable_ref(run_result_path, "RUN_RESULT.json"),
    }
    require(release == required_release, "RELEASE.json content differs from exact reconstructed release")

    required_run_fields = {
        "schema": RUN_RESULT_SCHEMA,
        "status": "PASS",
        "release_schema": RELEASE_SCHEMA,
        "engine_sha256": ENGINE_SHA256,
        "logical_partition_count": 47,
        "logical_node_sum": LOGICAL_NODE_SUM,
        "logical_roster": logical_roster,
        "direct_partition_count": 46,
        "direct_node_sum": DIRECT_NODE_SUM,
        "physical_zero_process_count": 46 + M,
        "frontier_census_process_count": 1,
    }
    for name, item in required_run_fields.items():
        require(run_result[name] == item, f"RUN_RESULT {name} mismatch")

    direct_entries = run_result["direct_receipts"]
    require(isinstance(direct_entries, list) and len(direct_entries) == 46, "RUN_RESULT direct roster is not exactly 46")
    expected_direct_entries: list[dict[str, Any]] = []
    for logical_index, (mode, partition, nodes) in enumerate(EXPECTED_ROWS):
        if key(mode, partition) == TARGET_KEY:
            continue
        relative = f"direct/{mode}__{partition}/RECEIPT.json"
        _, ref = validate_direct_receipt(root, relative, logical_index, mode, partition, nodes)
        expected_direct_entries.append(
            {
                "logical_index": logical_index,
                "key": key(mode, partition),
                "expected_nodes": nodes,
                "receipt": ref,
            }
        )
    require(direct_entries == expected_direct_entries, "RUN_RESULT ordered direct receipt roster mismatch")
    require(sum(entry["expected_nodes"] for entry in direct_entries) == DIRECT_NODE_SUM, "direct node sum mismatch")

    _, census_ref = validate_frontier_receipt(root)
    child_entries: list[dict[str, Any]] = []
    for index, nodes in enumerate(CHILD_NODES):
        _, ref = validate_child_receipt(root, index, nodes)
        child_entries.append({"index": index, "nodes": nodes, "receipt": ref})
    split_expected = {
        "logical_index": 46,
        "key": TARGET_KEY,
        "expected_nodes": TARGET_NODES,
        "census_receipt": census_ref,
        "child_count": M,
        "child_indices": list(range(M)),
        "children": child_entries,
        "child_reported_node_sum": CHILD_NODE_SUM,
        "repeated_prefix_calls_per_child": 3,
        "normalization_subtraction": NORMALIZATION_SUBTRACTION,
        "normalized_parent_nodes": TARGET_NODES,
        "node_identity": "parent_nodes=sum(child_nodes)-3*(M-1)",
    }
    require(run_result["split_replacement"] == split_expected, "RUN_RESULT split replacement mismatch")
    require(sum(CHILD_NODES) == CHILD_NODE_SUM, "internal child-node sum mismatch")
    require(CHILD_NODE_SUM - 3 * (M - 1) == TARGET_NODES, "split node normalization identity failed")
    require(DIRECT_NODE_SUM + TARGET_NODES == LOGICAL_NODE_SUM, "logical full-node identity failed")

    # Final mutation audit: every release byte and every bound external input
    # must still match after all semantic checks.
    require(verify_manifest(root, expected_files) == initial_manifest, "manifest changed during verification")
    require(strict_json(release_path) == release and strict_json(run_result_path) == run_result, "root JSON changed during verification")
    require(expected_sources(workspace) == sources, "source inputs changed during verification")
    require(expected_tooling(workspace) == tooling, "tooling changed during verification")
    require(workspace_ref(workspace, ENGINE_RELATIVE) == executable_ref, "engine changed during verification")
    return {
        "manifest_sha256": sha256_file(root / "MANIFEST.sha256"),
        "release_sha256": sha256_file(release_path),
        "run_result_sha256": sha256_file(run_result_path),
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--release-root",
        default=str(Path(__file__).resolve().parent / "evidence" / "full_preserved_v1"),
    )
    return parser


def main() -> int:
    args = build_parser().parse_args()
    try:
        result = verify_release(Path(args.release_root))
    except (VerifyError, OSError, ValueError) as exc:
        print(f"CONFIG3_A2_FROZEN_SPLIT_FAIL: {exc}", file=sys.stderr)
        return 2
    print(
        "CONFIG3_A2_FROZEN_SPLIT_STRICT_OK "
        f"schema={RELEASE_SCHEMA} logical_partitions=47 direct=46 children=22 "
        f"logical_nodes={LOGICAL_NODE_SUM} manifest_sha256={result['manifest_sha256']} "
        f"release_sha256={result['release_sha256']} "
        f"run_result_sha256={result['run_result_sha256']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
