#!/usr/bin/env python3
"""Deterministically check the Lean-to-production-seed semantic bridge.

This checker intentionally has a narrow claim.  It verifies hashes, extracts
the eight formal row cores from the authoritative Lean source, extracts the
actual seeds from the certificate-era C++ sources, independently recomputes
their forest distance spectra and positive MEX values, and compares both sides
with descriptor lines emitted by a successful Lean elaboration.

It does not check the search recursion, pruning lemmas, partition ledgers, or
the exhaustiveness of the two A2 weight-5 cases.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import stat
import sys
from pathlib import Path, PurePosixPath
from typing import Any, Iterable


HERE = Path(__file__).absolute().parent
REPO_ROOT = HERE.parents[1]
RECORD_PATH = HERE / "SEMANTIC_BRIDGE_RECORD.json"
BRIDGE_LEAN_DIR = HERE / "SemanticBridge"
EXPECTED_INPUT_ROLES = {
    "a2_production_source",
    "authoritative_dossier_olean",
    "authoritative_lean_dossier",
    "configuration2_certificate",
    "configuration3_certificate",
    "configuration3_partition_ledger",
    "configuration8_certificate",
    "final_five_solver",
    "final_five_source_freeze",
    "lake_manifest",
    "lakefile",
    "lean_toolchain",
    "row1_production_snapshot",
    "row7_production_snapshot",
    "solver_core",
}


class BridgeError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise BridgeError(message)


def reject_duplicate_json_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON object key: {key!r}")
        result[key] = value
    return result


def reject_json_constant(value: str) -> Any:
    raise BridgeError(f"non-finite JSON number is forbidden: {value}")


def parse_json(text: str, label: str) -> Any:
    try:
        return json.loads(
            text,
            object_pairs_hook=reject_duplicate_json_keys,
            parse_constant=reject_json_constant,
        )
    except (json.JSONDecodeError, BridgeError) as exc:
        raise BridgeError(f"cannot parse strict JSON for {label}: {exc}") from exc


def is_link_like(path: Path) -> bool:
    junction_test = getattr(path, "is_junction", None)
    if path.is_symlink() or bool(junction_test is not None and junction_test()):
        return True
    try:
        attributes = getattr(path.lstat(), "st_file_attributes", 0)
    except OSError:
        return False
    return bool(attributes & getattr(stat, "FILE_ATTRIBUTE_REPARSE_POINT", 0))


def require_plain_directory(path: Path, label: str) -> Path:
    try:
        info = path.lstat()
    except OSError as exc:
        raise BridgeError(f"cannot inspect {label}: {path}: {exc}") from exc
    require(
        stat.S_ISDIR(info.st_mode) and not is_link_like(path),
        f"{label} is not a plain directory: {path}",
    )
    return path


def require_plain_file(path: Path, label: str) -> Path:
    try:
        info = path.lstat()
    except OSError as exc:
        raise BridgeError(f"cannot inspect {label}: {path}: {exc}") from exc
    require(
        stat.S_ISREG(info.st_mode)
        and info.st_nlink == 1
        and not is_link_like(path),
        f"{label} is not a regular single-link file: {path}",
    )
    return path


def require_plain_directory_ancestry(path: Path, label: str) -> Path:
    absolute = path.absolute()
    for directory in reversed((absolute, *absolute.parents)):
        require_plain_directory(directory, f"{label} ancestor")
    return absolute


def repository_file(relative: str, label: str) -> Path:
    require(isinstance(relative, str), f"non-string {label} path")
    pure = PurePosixPath(relative)
    require(
        bool(relative)
        and "\\" not in relative
        and "\x00" not in relative
        and all(0x20 <= ord(character) < 0x7F for character in relative)
        and ":" not in relative
        and not pure.is_absolute()
        and ".." not in pure.parts
        and "." not in pure.parts
        and all(
            not part.endswith((".", " "))
            and re.fullmatch(
                r"(?i)(?:con|prn|aux|nul|com[1-9]|lpt[1-9])(?:\..*)?",
                part,
            )
            is None
            for part in pure.parts
        )
        and pure.as_posix() == relative,
        f"unsafe {label} path: {relative!r}",
    )
    root = require_plain_directory_ancestry(REPO_ROOT, "repository root")
    target = root.joinpath(*pure.parts).absolute()
    current = require_plain_directory(root, "repository root")
    for part in pure.parts[:-1]:
        current = require_plain_directory(current / part, f"{label} ancestor")
    require(not is_link_like(target), f"{label} leaf is a link/reparse point")
    try:
        target.resolve(strict=True).relative_to(root.resolve(strict=True))
    except (OSError, ValueError) as exc:
        raise BridgeError(
            f"{label} is missing or resolves outside the repository: {relative!r}"
        ) from exc
    return require_plain_file(target, label)


def read_text(path: Path) -> str:
    data = path.read_bytes()
    if data.startswith(b"\xff\xfe") or data.startswith(b"\xfe\xff"):
        return data.decode("utf-16")
    if data.startswith(b"\xef\xbb\xbf"):
        return data.decode("utf-8-sig")
    try:
        return data.decode("utf-8")
    except UnicodeDecodeError:
        return data.decode("utf-16-le")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_record() -> dict[str, Any]:
    record_path = repository_file(
        "proof/semantic_bridge/SEMANTIC_BRIDGE_RECORD.json",
        "semantic bridge record",
    )
    record = parse_json(
        read_text(record_path),
        "semantic bridge record",
    )
    require(
        isinstance(record, dict)
        and set(record)
        == {"schema", "claim", "non_claims", "lean_environment", "inputs", "rows"}
        and record.get("schema") == "leech18-semantic-bridge-v1"
        and isinstance(record.get("claim"), str)
        and isinstance(record.get("non_claims"), list)
        and isinstance(record.get("lean_environment"), dict)
        and set(record["lean_environment"]) == {"toolchain", "repository", "commit"}
        and isinstance(record.get("inputs"), dict)
        and set(record["inputs"]) == EXPECTED_INPUT_ROLES,
        "unexpected semantic bridge schema or exact field set",
    )
    return record


def check_input_hashes(record: dict[str, Any],
                       skip_prebuilt_dossier: bool = False) -> dict[str, Path]:
    paths: dict[str, Path] = {}
    for role, item in record["inputs"].items():
        require(
            isinstance(item, dict)
            and set(item) == {"path", "sha256"}
            and isinstance(item["sha256"], str)
            and re.fullmatch(r"[0-9a-fA-F]{64}", item["sha256"]) is not None,
            f"malformed pinned-input record for {role}",
        )
        if skip_prebuilt_dossier and role == "authoritative_dossier_olean":
            print("HASH_SKIPPED role=authoritative_dossier_olean "
                  "reason=explicit_fresh_baseline")
            continue
        path = repository_file(item["path"], f"pinned input for {role}")
        actual = sha256(path)
        expected = item["sha256"].lower()
        require(actual == expected,
                f"SHA-256 mismatch for {role}: expected {expected}, got {actual}")
        paths[role] = path
        print(f"HASH_OK role={role} sha256={actual}")
    return paths


def check_provenance_bindings(record: dict[str, Any], paths: dict[str, Path]) -> None:
    """Check that the certificate/freeze metadata names the parsed sources."""
    freeze = parse_json(
        read_text(paths["final_five_source_freeze"]), "final-five source freeze"
    )
    require(freeze.get("schema") == "G001_TERMINAL5_SOURCE_FREEZE_V1",
            "unexpected final-five source-freeze schema")
    frozen_solver_hash = freeze.get("distribution_files", {}).get(
        "g001_remaining_witness_solver.cpp")
    expected_solver_hash = record["inputs"]["final_five_solver"]["sha256"]
    require(frozen_solver_hash == expected_solver_hash,
            "final-five source freeze does not bind the parsed solver source")
    frozen_core_hash = freeze.get("distribution_files", {}).get(
        "order18_topology_free_search.cpp")
    expected_core_hash = record["inputs"]["solver_core"]["sha256"]
    require(frozen_core_hash == expected_core_hash,
            "final-five source freeze does not bind the parsed solver core")

    bindings = (
        ("configuration2_certificate", "row1_production_snapshot"),
        ("configuration3_certificate", "a2_production_source"),
        ("configuration3_certificate", "configuration3_partition_ledger"),
        ("configuration8_certificate", "row7_production_snapshot"),
    )
    for certificate_role, source_role in bindings:
        certificate = read_text(paths[certificate_role]).lower()
        source_hash = record["inputs"][source_role]["sha256"].lower()
        require(source_hash in certificate,
                f"{certificate_role} does not contain the pinned {source_role} hash")
    print("PROVENANCE_BINDINGS_OK final5_freeze=1 prior_certificates=4")


def check_a2_active_modes(paths: dict[str, Path]) -> None:
    """Verify which A2 mode flags the preserved 47-run evidence actually used."""
    with paths["configuration3_partition_ledger"].open(
            "r", encoding="utf-8-sig", newline="") as stream:
        rows = list(csv.DictReader(stream))
    require(len(rows) == 47,
            f"A2 partition ledger has {len(rows)} data rows, expected 47")
    modes = {row.get("mode", "") for row in rows}
    require(modes == {"a2_attached", "a2_separate"},
            f"A2 evidence uses unexpected modes: {sorted(modes)}")
    require(all("equality" not in mode for mode in modes),
            "A2 evidence unexpectedly activates an equality mode")
    print("A2_ACTIVE_MODE_AUDIT_OK partitions=47 modes=a2_attached,a2_separate "
          "equality_profiles_active=0")


def check_bridge_lean_sources() -> None:
    """Fail closed if the executable descriptor relation is weakened."""
    module_names = (
        "DescriptorData.lean", "DescriptorWellFormed.lean", "RowCore.lean",
        "AdjacentRows.lean", "DisjointRows.lean", "A2Split.lean",
        "Aggregate.lean",
    )
    modules = {name: read_text(BRIDGE_LEAN_DIR / name)
               for name in module_names}
    combined = "\n".join(modules.values()) + "\n" + read_text(
        HERE / "LeanRowSemanticBridge.lean")
    code_only = re.sub(r"/-.*?-/", "", combined, flags=re.DOTALL)
    code_only = re.sub(r"--.*", "", code_only)
    forbidden = re.findall(r"\b(?:axiom|sorry|admit)\b", code_only)
    require(not forbidden,
            f"bridge Lean source contains placeholder declarations: {forbidden}")

    wf = re.sub(r"\s+", " ", modules["DescriptorWellFormed.lean"])
    required_wf_fragments = (
        "| .adjacent => meets | .disjoint => !meets) = true",
        "| .none => !meetsOne && !meetsTwo",
        "| .meetsWeightOne => meetsOne && !meetsTwo",
        "| .meetsWeightTwo => !meetsOne && meetsTwo",
        "| .meetsBoth => meetsOne && meetsTwo) = true",
        "def descriptorWellFormedCheck (d : RowDescriptor) : Bool :=",
        "match d.seedEdges with | [one, two, witness] =>",
        "seedTripleIsSimpleForest one two witness &&",
        "decide (one.weight = 1)",
        "decide (two.weight = 2)",
        "decide (witness.weight = d.witnessWeight)",
        "decide (firstPairMatches d.firstPair (one.meets two))",
        "decide (witnessContactMatches d.witnessContact",
        "decide (d.currentSupport.Nodup)",
        "decide (d.currentSupport.toFinset = seedSupport3 one two witness)",
        "decide (PositiveMexCondition",
        "| _ => false",
        "def DescriptorWellFormed (d : RowDescriptor) : Prop := descriptorWellFormedCheck d = true",
    )
    missing = [fragment for fragment in required_wf_fragments
               if fragment not in wf]
    require(not missing,
            f"DescriptorWellFormed source contract changed: {missing}")
    for row in range(8):
        proof = (f"theorem row{row}Descriptor_wellFormed : "
                 f"DescriptorWellFormed row{row}Descriptor := by decide")
        require(proof in wf,
                f"row {row} is no longer proved by kernel decision reduction")

    aggregate = re.sub(r"\s+", " ", modules["Aggregate.lean"])
    require("theorem isLeech_implies_some_realized_seed_descriptor" in aggregate,
            "strong aggregate realized-seed theorem is missing")
    require("RealizedRowCore d T e1 e2" in aggregate,
            "aggregate theorem no longer returns RealizedRowCore")
    print("BRIDGE_LEAN_SOURCE_AUDIT_OK descriptor_well_formed=1 "
          "executable_top_level=1 boolean_enum_checks=2 "
          "row_decide_proofs=8 placeholders=0")


def check_representation_contract(paths: dict[str, Path]) -> None:
    """Audit the source facts relevant to endpoint orientation/relabeling.

    This is intentionally not promoted to a proof of the whole search's
    isomorphism invariance.  It checks the concrete undirected insertion and
    canonical forest encodings on which that remaining manual lemma rests.
    """
    core = read_text(paths["solver_core"])
    invariant_fragments = (
        "edges.push_back({u,v,w});",
        "adj[u].push_back({v,id}); adj[v].push_back({u,id});",
        "sort(parts.begin(),parts.end());",
        "for (int r:vs)",
        "string z=rooted_code(r,-1,0,weighted);",
        "sort(components.begin(),components.end());",
    )
    missing = [fragment for fragment in invariant_fragments if fragment not in core]
    require(not missing,
            f"solver undirected/canonical representation contract changed: {missing}")
    label_sensitive_fragments = (
        "return tie(a.score,a.u,a.v)<tie(b.score,b.u,b.v);",
        "int branch=valid_at_node++;",
        "if (root_branch>=0 && branch!=root_branch) continue;",
        "int c0=find(0), c1=find(1), c2=find(2), c3=find(3), c4=find(4);",
        "if (separate_equality_r>=0 && size[find(5)]!=1) return false;",
    )
    missing_sensitive = [fragment for fragment in label_sensitive_fragments
                         if fragment not in core]
    require(not missing_sensitive,
            "solver label-sensitive representation audit changed: "
            f"{missing_sensitive}")
    a2 = read_text(paths["a2_production_source"])
    dormant_equality_fragments = (
        "int attached_equality_r=-1;",
        "int separate_equality_r=-1;",
        'if (mode=="a2_attached_equality") s.attached_equality_r=equality_r;',
        'if (mode=="a2_separate_equality") s.separate_equality_r=equality_r;',
    )
    missing_equality = [fragment for fragment in dormant_equality_fragments
                        if fragment not in a2]
    require(not missing_equality,
            f"A2 equality-mode activation contract changed: {missing_equality}")
    wrapper = read_text(paths["final_five_solver"])
    require('#include "order18_topology_free_search.cpp"' in wrapper,
            "final-five wrapper no longer includes the pinned solver core")
    print("REPRESENTATION_SOURCE_AUDIT_OK undirected_add_edge=1 "
          "canonical_forest_code=1 label_sensitive_partition_order=1 "
          "hardcoded_equality_port_code_present=1 invariance_proof=0")


def record_rows(record: dict[str, Any]) -> list[dict[str, Any]]:
    rows = record["rows"]
    require(len(rows) == 8, f"record has {len(rows)} rows, expected 8")
    require([r["paper_configuration"] for r in rows] == list(range(1, 9)),
            "paper configurations are not exactly 1..8 in order")
    require([r["solver_row"] for r in rows] == list(range(8)),
            "solver rows are not exactly 0..7 in order")
    require(all(r["paper_configuration"] == r["solver_row"] + 1 for r in rows),
            "paper-configuration/zero-based-solver-row convention failed")
    return rows


def structure_block(text: str, name: str) -> str:
    match = re.search(rf"(?m)^structure\s+{re.escape(name)}\b", text)
    require(match is not None, f"Lean structure {name} not found")
    next_match = re.search(r"(?m)^structure\s+\w+\b|^/-- The exact eight-way local partition", text[match.end():])
    require(next_match is not None, f"could not delimit Lean structure {name}")
    return text[match.start():match.end() + next_match.start()]


def lean_row_core(text: str, name: str) -> dict[str, Any]:
    block = structure_block(text, name)
    if "adjacent12 : T.EdgeAdjacent e1 e2" in block:
        first_pair = "adjacent"
    elif "disjoint12 : T.EdgeEndpointDisjoint e1 e2" in block:
        first_pair = "disjoint"
    else:
        raise BridgeError(f"could not extract first-pair relation from {name}")

    witness_match = re.search(r"T\.weight\s+(e[34])\s*=\s*(\d+)", block)
    require(witness_match is not None, f"could not extract witness weight from {name}")
    witness_var = witness_match.group(1)
    witness_weight = int(witness_match.group(2))

    contacts: dict[int, str] = {}
    for relation, side in re.findall(
            rf"T\.(EdgeAdjacent|EdgeEndpointDisjoint)\s+{witness_var}\s+e([12])",
            block):
        contacts[int(side)] = relation
    require(set(contacts) == {1, 2}, f"could not extract both witness contacts from {name}")
    adjacent_sides = {side for side, relation in contacts.items()
                      if relation == "EdgeAdjacent"}
    contact_codes = {
        frozenset(): "none",
        frozenset({1}): "weight_one",
        frozenset({2}): "weight_two",
        frozenset({1, 2}): "both",
    }
    witness_contact = contact_codes[frozenset(adjacent_sides)]

    forced_match = re.search(
        r"forced(\d+)\s*:\s*ForcedPrefixEdge\s+T\s+(\d+)\s+\{([^}]+)\}", block)
    require(forced_match is not None, f"could not extract ForcedPrefixEdge from {name}")
    field_weight = int(forced_match.group(1))
    next_weight = int(forced_match.group(2))
    require(field_weight == next_weight,
            f"forced field suffix and next weight disagree in {name}")
    support = sorted(int(x) for x in re.findall(r"\d+", forced_match.group(3)))

    return {
        "lean_row": name,
        "first_pair": first_pair,
        "witness_weight": witness_weight,
        "witness_contact": witness_contact,
        "current_support": support,
        "next_weight": next_weight,
    }


def extract_dossier_order(text: str) -> list[str]:
    match = re.search(
        r"def\s+EightRowDossier\b.*?:\s*Prop\s*:=\s*(.*?)(?=\n/-! ##)",
        text,
        flags=re.DOTALL,
    )
    require(match is not None, "could not extract EightRowDossier definition")
    names = re.findall(
        r"\b(AdjacentNoneRow|AdjacentMeetsOneRow|AdjacentMeetsTwoRow|"
        r"AdjacentMeetsBothRow|DisjointNoneRow|DisjointMeetsOneRow|"
        r"DisjointMeetsTwoRow|DisjointMeetsBothRow)\s+T\s+e1\s+e2",
        match.group(1),
    )
    require(len(names) == 8 and len(set(names)) == 8,
            f"EightRowDossier did not contain eight distinct rows: {names}")
    return names


def check_lean_source(text: str, rows: list[dict[str, Any]]) -> None:
    order = extract_dossier_order(text)
    expected_order = [row["lean_row"] for row in rows]
    require(order == expected_order,
            f"Lean dossier order mismatch: expected {expected_order}, got {order}")
    semantic_keys = (
        "lean_row", "first_pair", "witness_weight", "witness_contact",
        "current_support", "next_weight",
    )
    for row in rows:
        actual = lean_row_core(text, row["lean_row"])
        expected = {key: row[key] for key in semantic_keys}
        require(actual == expected,
                f"Lean row-core mismatch for {row['lean_row']}: "
                f"expected {expected}, got {actual}")
    print("LEAN_SOURCE_ROWS_OK count=8 dossier_order=authoritative")


ADD_EDGE_RE = re.compile(
    r"(?:search|s)\.add_edge\s*\(\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)\s*\)\s*;")


def balanced_brace_block(text: str, marker: str) -> str:
    starts = [m.start() for m in re.finditer(re.escape(marker), text)]
    require(len(starts) == 1,
            f"expected one C++ marker {marker!r}, found {len(starts)}")
    brace = text.find("{", starts[0])
    require(brace >= 0, f"no opening brace after C++ marker {marker!r}")
    depth = 0
    for index in range(brace, len(text)):
        char = text[index]
        if char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return text[starts[0]:index + 1]
    raise BridgeError(f"unclosed C++ block after marker {marker!r}")


def edges_from_block(block: str) -> list[list[int]]:
    return [[int(u), int(v), int(w)] for u, v, w in ADD_EDGE_RE.findall(block)]


def extract_final_five(text: str) -> tuple[dict[str, list[list[int]]], dict[str, int], dict[int, str]]:
    mapping: dict[int, str] = {}
    for external, stored, mode in re.findall(
            r"case\s+(\d+)\s*:\s*out\s*=\s*\{\s*(\d+)\s*,\s*\"([^\"]+)\"\s*\}",
            text):
        require(external == stored,
                f"final-five external/stored configuration mismatch: {external}/{stored}")
        mapping[int(external)] = mode
    expected_modes = ["g001_row0", "g001_row3", "g001_row4", "g001_row5", "g001_row6"]
    initializer = balanced_brace_block(
        text, "int initialize_seed(Search &search, const std::string &mode) {")
    seeds: dict[str, list[list[int]]] = {}
    declared_next: dict[str, int] = {}
    for mode in expected_modes:
        block = balanced_brace_block(initializer, f'if (mode == "{mode}") {{')
        edges = edges_from_block(block)
        return_match = re.search(r"\breturn\s+(\d+)\s*;", block)
        require(len(edges) == 3 and return_match is not None,
                f"malformed initialize_seed block for {mode}")
        seeds[mode] = edges
        declared_next[mode] = int(return_match.group(1))
    return seeds, declared_next, mapping


def extract_direct_mode(text: str, mode: str) -> list[list[int]]:
    block = balanced_brace_block(text, f'if (mode=="{mode}") {{')
    edges = edges_from_block(block)
    require(len(edges) == 3, f"expected three seed edges in {mode}, got {edges}")
    require("s.rec();" in block, f"{mode} block does not invoke recursion")
    return edges


def seed_after_comment(text: str, marker: str) -> list[list[int]]:
    start = text.find(marker)
    require(start >= 0, f"missing A2 marker {marker!r}")
    end = text.find("s.rec();", start)
    require(end >= 0, f"missing recursion call after A2 marker {marker!r}")
    return edges_from_block(text[start:end])


def extract_a2_projection(text: str) -> tuple[list[list[int]], list[list[list[int]]]]:
    require('string mode="a2"' in text, "A2 production source no longer defaults to mode a2")
    require('else if (mode!="a2_attached")' in text,
            "A2 prefix-I mode guard changed")
    require('mode!="a2_separate"' in text and '!s.limit' in text and
            's.solution_topologies.empty()' in text,
            "A2 prefix-II continuation guard changed")
    first = seed_after_comment(text, "A2 prefix I:")
    second = seed_after_comment(text, "A2 prefix II:")
    require(len(first) == 4 and len(second) == 4,
            f"A2 production prefixes are not both four-edge seeds: {first}, {second}")
    first_set = {tuple(edge) for edge in first}
    second_set = {tuple(edge) for edge in second}
    common = sorted(first_set & second_set, key=lambda edge: edge[2])
    first_extra = first_set - set(common)
    second_extra = second_set - set(common)
    require(len(common) == 3, f"A2 prefixes do not have a three-edge common core: {common}")
    require(len(first_extra) == 1 and len(second_extra) == 1 and
            next(iter(first_extra))[2] == 5 and next(iter(second_extra))[2] == 5,
            f"A2 prefix-specific edges are not exactly one weight-5 edge each: "
            f"{first_extra}, {second_extra}")

    def endpoints(seed: list[list[int]], weight: int) -> set[int]:
        matches = [{u, v} for u, v, edge_weight in seed if edge_weight == weight]
        require(len(matches) == 1,
                f"A2 prefix does not have one edge of weight {weight}: {seed}")
        return matches[0]

    for seed, expected_relation in ((first, "disjoint"), (second, "adjacent")):
        weight_five = endpoints(seed, 5)
        require(not (weight_five & endpoints(seed, 1)) and
                not (weight_five & endpoints(seed, 2)),
                f"A2 weight-5 edge meets weight 1 or 2: {seed}")
        actual_relation = (
            "adjacent" if weight_five & endpoints(seed, 4) else "disjoint")
        require(actual_relation == expected_relation,
                f"A2 weight-5/weight-4 relation mismatch: expected "
                f"{expected_relation}, got {actual_relation}")
    return [list(edge) for edge in common], [first, second]


def canonical_edges(edges: Iterable[Iterable[int]]) -> list[list[int]]:
    normalized = [[min(u, v), max(u, v), w] for u, v, w in edges]
    return sorted(normalized, key=lambda edge: (edge[2], edge[0], edge[1]))


def forest_semantics(edges: list[list[int]], witness_weight: int) -> dict[str, Any]:
    require(len(edges) >= 3, f"seed has fewer than three edges: {edges}")
    require(all(u != v and w > 0 for u, v, w in edges), f"invalid seed edge: {edges}")
    weights = [w for _, _, w in edges]
    require(len(weights) == len(set(weights)), f"seed weights are not unique: {edges}")

    parent: dict[int, int] = {}

    def find(vertex: int) -> int:
        parent.setdefault(vertex, vertex)
        while parent[vertex] != vertex:
            parent[vertex] = parent[parent[vertex]]
            vertex = parent[vertex]
        return vertex

    def union(left: int, right: int) -> None:
        left_root, right_root = find(left), find(right)
        require(left_root != right_root, f"seed is not a forest: {edges}")
        parent[left_root] = right_root

    adjacency: dict[int, list[tuple[int, int]]] = {}
    for u, v, weight in edges:
        union(u, v)
        adjacency.setdefault(u, []).append((v, weight))
        adjacency.setdefault(v, []).append((u, weight))

    def path_distance(start: int, target: int) -> int | None:
        stack = [(start, -1, 0)]
        while stack:
            vertex, previous, distance = stack.pop()
            if vertex == target:
                return distance
            for neighbor, weight in adjacency[vertex]:
                if neighbor != previous:
                    stack.append((neighbor, vertex, distance + weight))
        return None

    vertices = sorted(adjacency)
    support: set[int] = set()
    for left_index, left in enumerate(vertices):
        for right in vertices[left_index + 1:]:
            distance = path_distance(left, right)
            if distance is not None:
                support.add(distance)
    next_weight = 1
    while next_weight in support:
        next_weight += 1

    by_weight = {weight: {u, v} for u, v, weight in edges}
    require(1 in by_weight and 2 in by_weight,
            f"seed lacks physical weights 1 and 2: {edges}")
    first_pair = "adjacent" if by_weight[1] & by_weight[2] else "disjoint"
    require(witness_weight in by_weight,
            f"seed lacks witness weight {witness_weight}: {edges}")
    witness_endpoints = by_weight[witness_weight]
    adjacent_sides = frozenset(
        side for side in (1, 2) if witness_endpoints & by_weight[side])
    contact = {
        frozenset(): "none",
        frozenset({1}): "weight_one",
        frozenset({2}): "weight_two",
        frozenset({1, 2}): "both",
    }[adjacent_sides]
    return {
        "first_pair": first_pair,
        "witness_weight": witness_weight,
        "witness_contact": contact,
        "current_support": sorted(support),
        "next_weight": next_weight,
    }


def check_cpp_sources(paths: dict[str, Path], rows: list[dict[str, Any]]) -> None:
    final_text = read_text(paths["final_five_solver"])
    final_seeds, final_next, final_mapping = extract_final_five(final_text)
    expected_mapping = {
        row["paper_configuration"]: row["solver_mode"]
        for row in rows if row["source_kind"] == "direct_final5"
    }
    require(final_mapping == expected_mapping,
            f"final-five configuration map mismatch: expected {expected_mapping}, got {final_mapping}")

    source_seeds: dict[int, list[list[int]]] = {}
    for row in rows:
        if row["source_kind"] == "direct_final5":
            source_seeds[row["solver_row"]] = final_seeds[row["solver_mode"]]
            require(final_next[row["solver_mode"]] == row["next_weight"],
                    f"declared initialize_seed MEX mismatch for {row['solver_mode']}")

    source_seeds[1] = extract_direct_mode(
        read_text(paths["row1_production_snapshot"]), "g001_row1")
    source_seeds[7] = extract_direct_mode(
        read_text(paths["row7_production_snapshot"]), "g001_row7")
    a2_projection, a2_full_prefixes = extract_a2_projection(
        read_text(paths["a2_production_source"]))
    source_seeds[2] = a2_projection
    require(sorted(source_seeds) == list(range(8)),
            f"production extraction did not produce rows 0..7: {sorted(source_seeds)}")

    semantic_keys = (
        "first_pair", "witness_weight", "witness_contact",
        "current_support", "next_weight",
    )
    for row in rows:
        solver_row = row["solver_row"]
        actual_edges = canonical_edges(source_seeds[solver_row])
        expected_edges = canonical_edges(row["seed_edges"])
        require(actual_edges == expected_edges,
                f"C++ seed-edge mismatch for solver row {solver_row}: "
                f"expected {expected_edges}, got {actual_edges}")
        actual_semantics = forest_semantics(actual_edges, row["witness_weight"])
        expected_semantics = {key: row[key] for key in semantic_keys}
        require(actual_semantics == expected_semantics,
                f"derived C++ seed semantics mismatch for solver row {solver_row}: "
                f"expected {expected_semantics}, got {actual_semantics}")
        print(
            f"CPP_ROW_OK configuration={row['paper_configuration']} "
            f"solver_row={solver_row} mode={row['solver_mode']} "
            f"support={','.join(map(str, actual_semantics['current_support']))} "
            f"mex={actual_semantics['next_weight']}"
        )
    print(
        "A2_PROJECTION_OK branches=2 full_edge_counts="
        f"{len(a2_full_prefixes[0])},{len(a2_full_prefixes[1])} "
        "common_weights=1,2,4 projected_mex=5 split=disjoint,adjacent"
    )


def parse_lean_descriptors(output: str) -> list[dict[str, Any]]:
    parsed: list[dict[str, Any]] = []
    for line in output.splitlines():
        if not line.startswith("SEMANTIC_ROW\t"):
            continue
        fields = line.split("\t")
        require(len(fields) == 12, f"malformed Lean descriptor line: {line!r}")
        edges = [] if not fields[11] else [
            [int(part) for part in encoded.split("-")]
            for encoded in fields[11].split(",")
        ]
        require(all(len(edge) == 3 for edge in edges),
                f"malformed Lean seed edge field: {fields[11]!r}")
        parsed.append({
            "paper_configuration": int(fields[1]),
            "solver_row": int(fields[2]),
            "lean_row": fields[3],
            "solver_mode": fields[4],
            "source_kind": fields[5],
            "first_pair": fields[6],
            "witness_weight": int(fields[7]),
            "witness_contact": fields[8],
            "current_support": [] if not fields[9] else [int(x) for x in fields[9].split(",")],
            "next_weight": int(fields[10]),
            "seed_edges": edges,
        })
    return parsed


def check_lean_output(path: Path, rows: list[dict[str, Any]]) -> None:
    path = path.absolute()
    require_plain_directory_ancestry(path.parent, "Lean output directory")
    require_plain_file(path, "Lean output file")
    output = read_text(path)
    parsed = parse_lean_descriptors(output)
    require(parsed == rows,
            f"compiled Lean descriptors differ from the record: expected {rows}, got {parsed}")
    audited_declarations = (
        "Leech18SemanticBridge.rowDescriptors_all_wellFormed",
        "Leech18SemanticBridge.eightRowDossier_implies_some_realized_core",
        "Leech18SemanticBridge.isLeech_implies_some_realized_seed_descriptor",
        "Leech18SemanticBridge.adjacentMeetsTwoRow_implies_a2_production_split",
    )
    report_pattern = re.compile(
        r"'([^']+)' (?:depends on axioms: \[(.*?)\]|"
        r"(does not depend on any axioms))",
        flags=re.DOTALL,
    )
    reports: list[tuple[str, tuple[str, ...]]] = []
    for match in report_pattern.finditer(output):
        axiom_text = match.group(2)
        axioms = () if axiom_text is None else tuple(
            item.strip() for item in axiom_text.split(",") if item.strip())
        require(len(axioms) == len(set(axioms)),
                f"duplicate axiom in report for {match.group(1)}: {axioms}")
        reports.append((match.group(1), axioms))

    dependent_occurrences = output.count("depends on axioms:")
    independent_occurrences = output.count("does not depend on any axioms")
    require(dependent_occurrences + independent_occurrences == 4,
            "Lean output does not contain exactly four canonical axiom reports: "
            f"dependent={dependent_occurrences}, independent={independent_occurrences}")
    require(len(reports) == 4,
            f"parsed {len(reports)} axiom reports, expected exactly four")
    report_names = [name for name, _ in reports]
    require(len(report_names) == len(set(report_names)),
            f"duplicate axiom report declaration(s): {report_names}")
    require(set(report_names) == set(audited_declarations),
            "axiom report declaration mismatch: expected "
            f"{sorted(audited_declarations)}, got {sorted(report_names)}")

    allowed_axioms = {"propext", "Classical.choice", "Quot.sound"}
    observed_axioms: set[str] = set()
    for declaration, axioms in reports:
        observed_axioms.update(axioms)
        unexpected = set(axioms) - allowed_axioms
        require(not unexpected,
                f"unexpected axiom(s) for {declaration}: {sorted(unexpected)}")
    require(observed_axioms == allowed_axioms,
            "observed axiom union differs from the exact allowlist: "
            f"expected {sorted(allowed_axioms)}, got {sorted(observed_axioms)}")
    forbidden = ("sorryAx", "trustCompiler", "ofReduceBool")
    found = [name for name in forbidden if name in output]
    require(not found, f"forbidden axiom marker(s) in Lean output: {found}")
    report_map = dict(reports)
    for declaration in audited_declarations:
        encoded = ",".join(report_map[declaration]) or "none"
        print(f"LEAN_AXIOM_REPORT declaration={declaration} axioms={encoded}")
    print("LEAN_AXIOM_AUDIT_OK reports=4 allowlist="
          "Classical.choice,Quot.sound,propext forbidden=0")
    print(f"LEAN_ELABORATION_OK descriptors={len(parsed)} output_sha256={sha256(path)}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--lean-output", type=Path,
                       help="stdout captured from elaborating LeanRowSemanticBridge.lean")
    group.add_argument("--static-only", action="store_true",
                       help="check hashes and source extraction without claiming Lean elaboration")
    parser.add_argument(
        "--skip-prebuilt-dossier", action="store_true",
        help="skip only the recorded prebuilt dossier olean when the wrapper binds an explicit fresh baseline")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    require_plain_directory_ancestry(REPO_ROOT, "repository root")
    require_plain_file(Path(__file__).absolute(), "semantic bridge verifier")
    record = load_record()
    rows = record_rows(record)
    paths = check_input_hashes(record, args.skip_prebuilt_dossier)
    check_provenance_bindings(record, paths)
    check_representation_contract(paths)
    check_a2_active_modes(paths)
    check_bridge_lean_sources()
    check_lean_source(read_text(paths["authoritative_lean_dossier"]), rows)
    check_cpp_sources(paths, rows)
    if args.static_only:
        print("LEECH18_SEMANTIC_BRIDGE_STATIC_OK rows=8 lean_elaboration=NOT_CHECKED")
        return 0
    check_lean_output(args.lean_output, rows)
    print("LEECH18_SEMANTIC_BRIDGE_OK rows=8 direct=7 projected=1")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BridgeError, OSError, ValueError, KeyError, json.JSONDecodeError) as error:
        print(f"SEMANTIC_BRIDGE_ERROR: {error}", file=sys.stderr)
        raise SystemExit(1)
