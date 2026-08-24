#!/usr/bin/env python3
"""Validate and bind the outputs of a fresh all-eight computational rerun.

This script does not run a search and does not construct a Lean proof term.
It accepts only the exact completed-stage schemas and counts produced by the
public reproduction drivers, checks their cross-stage bindings, and creates a
new canonical JSON assembly receipt without overwriting an existing file.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import sys
from typing import Any, Mapping, NoReturn, Sequence


SCHEMA = "LEECH18_FRESH_ALL_EIGHT_ASSEMBLY_V1"
STATUS = "COMPUTATIONAL_EXCLUSIONS_COMPLETE"
FROZEN_PLAN_SHA256 = (
    "b317a3b7cef71e11fea762ce5e70322f168e06c6e04b97293f066cb2e313bdae"
)
C157_SOURCE_MANIFEST_SHA256 = (
    "c703d2d1d410415e4382c62fcce49c0ddb4c28cf6cfbad61ee1b406fc40129c4"
)
PRIOR_NODES = {2: 193_281_350, 3: 167_742_832, 8: 239_702_053}
TERMINAL_NODES = {
    1: 1_321_606_123,
    4: 225_016_655,
    5: 4_242_081_806,
    6: 1_165_724_514,
    7: 1_010_043_681,
}
REPORTED_NODES = 8_565_199_014
HEX64 = re.compile(r"^[0-9a-f]{64}$")


class AssemblyError(RuntimeError):
    pass


def fail(message: str) -> NoReturn:
    raise AssemblyError(message)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def canonical_json(value: object) -> bytes:
    return (
        json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
        + "\n"
    ).encode("ascii")


def read_json(path: Path, label: str) -> tuple[Mapping[str, Any], str]:
    absolute = path.expanduser().resolve(strict=True)
    if not absolute.is_file():
        fail(f"{label} is not a regular file: {absolute}")
    try:
        value = json.loads(absolute.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        fail(f"cannot parse {label}: {error}")
    if not isinstance(value, dict):
        fail(f"{label} is not a JSON object")
    return value, sha256_file(absolute)


def require_equal(value: Mapping[str, Any], expected: Mapping[str, Any], label: str) -> None:
    for key, wanted in expected.items():
        if value.get(key) != wanted:
            fail(f"{label} field {key!r} mismatch: {value.get(key)!r} != {wanted!r}")


def require_hex(value: Any, label: str) -> str:
    if not isinstance(value, str) or HEX64.fullmatch(value) is None:
        fail(f"{label} is not a lowercase SHA-256 digest")
    return value


def write_new(path: Path, data: bytes) -> None:
    absolute = Path(os.path.abspath(os.fspath(path.expanduser())))
    if not absolute.parent.is_dir():
        fail(f"output parent does not exist: {absolute.parent}")
    try:
        descriptor = os.open(absolute, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    except OSError as error:
        fail(f"refusing/cannot create output {absolute}: {error}")
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
    except BaseException:
        try:
            absolute.unlink()
        except OSError:
            pass
        raise


def load_local_module(name: str, path: Path):
    existing = sys.modules.get(name)
    if existing is not None and Path(existing.__file__).resolve() == path.resolve():
        return existing
    specification = importlib.util.spec_from_file_location(name, path)
    if specification is None or specification.loader is None:
        fail(f"cannot load authoritative module: {path}")
    module = importlib.util.module_from_spec(specification)
    sys.modules[name] = module
    specification.loader.exec_module(module)
    return module


def prior_modules():
    scripts = Path(__file__).resolve().parent
    frozen = load_local_module(
        "recompute_prior_three_full", scripts / "recompute_prior_three_full.py"
    )
    source = load_local_module(
        "leech18_recompute_prior_three_from_source",
        scripts / "recompute_prior_three_from_source.py",
    )
    return frozen, source


def verify_c157_complete_run(summary_path: Path) -> None:
    scripts = Path(__file__).resolve().parent
    module = load_local_module(
        "leech18_recompute_c157_full", scripts / "recompute_c157_full.py"
    )
    try:
        module.verify_run(summary_path.expanduser().resolve(strict=True).parent)
    except Exception as error:
        fail(f"complete C157 evidence replay failed: {error}")


def validate_compiled_output(
    item: Mapping[str, Any], root: Path, label: str, expected_source: str,
    compiler_path: str, flags: Sequence[str],
) -> None:
    output = item.get("output")
    size = item.get("size_bytes")
    if not isinstance(output, str) or not output or Path(output).name != output:
        fail(f"{label} output name is invalid")
    path = root / output
    expected_command = [
        compiler_path, *flags, expected_source, "-o", str(path)
    ]
    if (
        item.get("source") != expected_source
        or item.get("command") != expected_command
        or not path.is_file()
        or isinstance(size, bool)
        or not isinstance(size, int)
        or size < 0
        or path.stat().st_size != size
        or sha256_file(path) != require_hex(item.get("sha256"), f"{label} digest")
    ):
        fail(f"{label} output file binding mismatch")


def validate_prior(
    summary_path: Path,
    summary: Mapping[str, Any],
    build_path: Path,
    build: Mapping[str, Any],
    build_hash: str,
) -> Mapping[str, Any]:
    require_equal(
        summary,
        {
            "schema": "LEECH18_PRIOR_THREE_FULL_RECOMPUTATION_V1",
            "status": "ZERO_COMPLETE",
            "logical_partitions": 178,
            "physical_processes": 200,
            "zero_processes": 199,
            "frontier_census_processes": 1,
        },
        "prior-three summary",
    )
    nodes = summary.get("nodes")
    if not isinstance(nodes, dict):
        fail("prior-three nodes is not an object")
    require_equal(
        nodes,
        {
            "configuration_2": PRIOR_NODES[2],
            "configuration_3_logical": PRIOR_NODES[3],
            "configuration_3_normalization_subtraction": 63,
            "configuration_8": PRIOR_NODES[8],
            "logical_total": sum(PRIOR_NODES.values()),
        },
        "prior-three nodes",
    )
    direct = nodes.get("configuration_3_direct")
    children = nodes.get("configuration_3_split_children")
    if (
        isinstance(direct, bool)
        or not isinstance(direct, int)
        or isinstance(children, bool)
        or not isinstance(children, int)
        or direct + children - 63 != PRIOR_NODES[3]
    ):
        fail("prior-three Configuration 3 node normalization mismatch")

    require_equal(build, {"schema": "LEECH18_PRIOR_THREE_SOURCE_BUILD_V1"}, "build receipt")
    compiler = build.get("compiler")
    if not isinstance(compiler, dict):
        fail("prior-three build compiler is not an object")
    require_hex(compiler.get("sha256"), "prior-three compiler digest")
    if not isinstance(compiler.get("version_output"), str) or not compiler["version_output"]:
        fail("prior-three compiler version output is absent")
    compiler_path = compiler.get("path")
    if not isinstance(compiler_path, str) or not compiler_path:
        fail("prior-three compiler path is absent")
    compile_flags = [
        "-O2", "-std=c++20", "-Wall", "-Wextra", "-Wpedantic"
    ]
    if build.get("compile_flags") != compile_flags:
        fail("prior-three compile flags mismatch")

    solvers = build.get("solvers")
    tests = build.get("tests")
    sources = build.get("sources")
    if not isinstance(solvers, list) or len(solvers) != 3:
        fail("prior-three source build does not contain exactly three solvers")
    if not isinstance(tests, list) or len(tests) != 7:
        fail("prior-three source build does not contain exactly seven tests")
    if not isinstance(sources, list) or len(sources) != 14:
        fail("prior-three source build does not contain exactly fourteen source bindings")
    try:
        frozen, source_driver = prior_modules()
        authoritative_sources = source_driver.validate_sources()
        groups = frozen.assemble_jobs()
    except Exception as error:
        fail(f"authoritative prior-three roster/source validation failed: {error}")
    if sources != authoritative_sources:
        fail("prior-three build source bindings differ from the authoritative sources")

    build_root = build_path.expanduser().resolve(strict=True).parent
    expected_build_files = {"BUILD_RECEIPT.json", "BUILD_RECEIPT.sha256"}
    expected_outputs = {
        2: ("order18_topology_free_search_row1_rebuild.exe", "order18_topology_free_search_row1_snapshot.cpp"),
        3: ("a2_topology_free_search_multicover_rebuild.exe", "a2_topology_free_search.cpp"),
        8: ("order18_topology_free_search_row7_rebuild.exe", "order18_topology_free_search_production_snapshot.cpp"),
    }
    solver_hashes: dict[int, str] = {}
    for configuration, (output, source_name) in expected_outputs.items():
        matches = [item for item in solvers if isinstance(item, dict) and item.get("output") == output]
        if len(matches) != 1:
            fail(f"prior-three build solver binding missing/duplicate for Configuration {configuration}")
        solver_hashes[configuration] = require_hex(
            matches[0].get("sha256"), f"Configuration {configuration} rebuilt solver digest"
        )
        validate_compiled_output(
            matches[0], build_root, f"Configuration {configuration} solver",
            source_name, compiler_path, compile_flags,
        )
        expected_build_files.add(output)
    for index, (test, test_specification) in enumerate(zip(tests, source_driver.TESTS)):
        source_name, _marker = test_specification
        if (
            not isinstance(test, dict)
            or test.get("exit_code") != 0
            or not isinstance(test.get("expected_marker"), str)
            or test["expected_marker"] not in str(test.get("stdout", "")).splitlines()
        ):
            fail(f"prior-three build test {index} did not record its expected success marker")
        validate_compiled_output(
            test, build_root, f"prior-three build test {index}",
            source_name, compiler_path, compile_flags,
        )
        expected_build_files.add(str(test["output"]))
    actual_build_files = {
        path.relative_to(build_root).as_posix()
        for path in build_root.rglob("*") if path.is_file()
    }
    if actual_build_files != expected_build_files:
        fail("prior-three build output exact file set mismatch")
    build_digest_record = build_root / "BUILD_RECEIPT.sha256"
    if build_digest_record.read_bytes() != (
        f"{build_hash}  BUILD_RECEIPT.json\n".encode("ascii")
    ):
        fail("prior-three BUILD_RECEIPT.sha256 binding mismatch")

    receipts = summary.get("receipts")
    if not isinstance(receipts, list) or len(receipts) != 200:
        fail("prior-three process receipt count mismatch")
    expected_jobs = [job for group in groups for job in group]
    if len(expected_jobs) != 200 or len({
        (job.configuration, job.process_key) for job in expected_jobs
    }) != 200:
        fail("authoritative prior-three roster is not exactly 200 unique processes")
    if [item.get("process_key") for item in receipts if isinstance(item, dict)] != [
        job.process_key for job in expected_jobs
    ]:
        fail("prior-three process order/identity differs from the authoritative roster")

    status_counts = {"ZERO": 0, "FRONTIER": 0}
    configuration_counts = {2: 0, 3: 0, 8: 0}
    process_keys: set[tuple[int, str]] = set()
    run_root = summary_path.expanduser().resolve(strict=True).parent
    expected_run_files = {"RECOMPUTATION_SUMMARY.json"}
    for index, (receipt, job) in enumerate(zip(receipts, expected_jobs)):
        if not isinstance(receipt, dict):
            fail(f"prior-three receipt {index} is malformed")
        configuration = receipt.get("configuration")
        if configuration not in configuration_counts:
            fail(f"prior-three receipt {index} has an unexpected configuration")
        require_equal(
            receipt,
            {
                "schema": "LEECH18_PRIOR_THREE_FRESH_PROCESS_V1",
                "configuration": job.configuration,
                "logical_key": job.logical_key,
                "process_key": job.process_key,
                "category": job.category,
                "argv": list(job.argv),
                "exit_code": 0,
                "solver_sha256": solver_hashes[job.configuration],
            },
            f"prior-three receipt {index}",
        )
        result = receipt.get("result")
        if not isinstance(result, dict):
            fail(f"prior-three receipt {index} has no result object")
        require_equal(
            result,
            {
                "status": job.expected_status,
                "mode": job.expected_mode,
                "nodes": str(job.expected_nodes),
                "frontier": str(job.expected_frontier),
                "solution_topologies": "0",
                "multi_cover": "on",
            },
            f"prior-three receipt {index} result",
        )
        status = job.expected_status
        key = receipt.get("process_key")
        composite_key = (job.configuration, key)
        if not isinstance(key, str) or not key or composite_key in process_keys:
            fail(f"prior-three process key {index} is missing or duplicate")
        process_keys.add(composite_key)
        status_counts[status] += 1
        configuration_counts[configuration] += 1

        relative_root = Path(f"configuration_{job.configuration}") / job.process_key
        directory = run_root / relative_root
        receipt_path = directory / "RECEIPT.json"
        stdout_path = directory / "stdout.txt"
        stderr_path = directory / "stderr.txt"
        for path in (receipt_path, stdout_path, stderr_path):
            expected_run_files.add(path.relative_to(run_root).as_posix())
        if not receipt_path.is_file() or receipt_path.read_bytes() != frozen.canonical_json(receipt):
            fail(f"prior-three receipt file mismatch: {job.process_key}")
        stdout_raw = stdout_path.read_bytes()
        stderr_raw = stderr_path.read_bytes()
        for name, raw, descriptor in (
            ("stdout", stdout_raw, receipt.get("stdout")),
            ("stderr", stderr_raw, receipt.get("stderr")),
        ):
            if not isinstance(descriptor, dict):
                fail(f"prior-three {name} descriptor missing: {job.process_key}")
            if (
                descriptor.get("bytes") != len(raw)
                or descriptor.get("sha256") != hashlib.sha256(raw).hexdigest()
            ):
                fail(f"prior-three {name} artifact mismatch: {job.process_key}")
        if stderr_raw != b"":
            fail(f"prior-three stderr is nonempty: {job.process_key}")
        try:
            parsed = frozen.parse_result(stdout_raw, job.process_key)
        except Exception as error:
            fail(f"prior-three stdout parse failed for {job.process_key}: {error}")
        if parsed != result:
            fail(f"prior-three stdout/result mismatch: {job.process_key}")
    if status_counts != {"ZERO": 199, "FRONTIER": 1}:
        fail("prior-three ZERO/FRONTIER receipt counts mismatch")
    if configuration_counts != {2: 79, 3: 69, 8: 52}:
        fail("prior-three per-configuration physical process counts mismatch")
    actual_run_files = {
        path.relative_to(run_root).as_posix()
        for path in run_root.rglob("*") if path.is_file()
    }
    if actual_run_files != expected_run_files:
        fail("prior-three run exact file set mismatch")
    if summary_path.read_bytes() != frozen.canonical_json(summary):
        fail("prior-three summary bytes are not canonical")
    return {
        "compiler_sha256": compiler["sha256"],
        "compiler_matches_documented_14_2_0": compiler.get(
            "matches_historical_documented_version"
        ) is True,
        "physical_processes": 200,
        "source_built": True,
        "zero_processes": 199,
    }


def validate_c157(summary_path: Path, summary: Mapping[str, Any]) -> Mapping[str, Any]:
    verify_c157_complete_run(summary_path)
    require_equal(
        summary,
        {
            "schema": "leech18-c157-fresh-recomputation-v1",
            "status": "C157_FRESH_RECOMPUTATION_COMPLETE",
            "plan_sha256": FROZEN_PLAN_SHA256,
            "leaf_count": 37_706,
            "internal_prefix_count": 2_135,
            "zero_child_count": 464,
            "solver_invocation_count": 80_142,
            "source_manifest_sha256": C157_SOURCE_MANIFEST_SHA256,
        },
        "C157 summary",
    )
    coverage = summary.get("coverage")
    if not isinstance(coverage, dict):
        fail("C157 coverage is not an object")
    require_equal(
        coverage,
        {
            "prefix_free": True,
            "exhaustive_gate_check": True,
            "leaf_frontiers_match_plan": True,
            "gate_parent_count": 2_135,
            "gate_child_count": 40_301,
            "gate_zero_child_count": 464,
            "omitted_zero_child_count": 464,
            "planned_zero_leaf_count": 813,
        },
        "C157 coverage",
    )
    expected = {
        "1": ("g001_row0", 5_176, 287, 26, 153, 20_045_473),
        "5": ("g001_row4", 25_254, 1_460, 430, 378, 74_092_284),
        "6": ("g001_row5", 3_977, 213, 6, 155, 18_016_722),
        "7": ("g001_row6", 3_299, 175, 2, 127, 15_688_080),
    }
    configurations = summary.get("configurations")
    if not isinstance(configurations, dict) or set(configurations) != set(expected):
        fail("C157 configuration roster mismatch")
    for key, values in expected.items():
        item = configurations[key]
        if not isinstance(item, dict):
            fail(f"C157 Configuration {key} summary is malformed")
        mode, leaves, prefixes, omitted_zeros, planned_zeros, frontier = values
        require_equal(
            item,
            {
                "mode": mode,
                "leaf_count": leaves,
                "internal_prefix_count": prefixes,
                "gate_zero_child_count": omitted_zeros,
                "omitted_zero_child_count": omitted_zeros,
                "planned_zero_leaf_count": planned_zeros,
                "frontier_sum": frontier,
            },
            f"C157 Configuration {key}",
        )
    for key in (
        "results_manifest_sha256", "solver_sha256", "preflight_sha256", "workload_sha256"
    ):
        require_hex(summary.get(key), f"C157 {key}")
    return {
        "solver_invocations": 80_142,
        "surviving_leaves": 37_706,
        "planned_zero_leaves_within_terminal_roster": 813,
        "zero_children": 464,
    }


def validate_terminal_preflight(receipt: Mapping[str, Any]) -> str:
    require_equal(
        receipt,
        {
            "schema": "LEECH18_TERMINAL5_PREFLIGHT_V1",
            "status": "PASS",
            "mode": "completed-run",
            "frozen_plan_sha256": FROZEN_PLAN_SHA256,
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
        },
        "Terminal5 preflight receipt",
    )
    for key in ("terminal_plan_sha256", "leaf_receipt_set_sha256", "bundle_receipt_set_sha256"):
        require_hex(receipt.get(key), f"Terminal5 preflight {key}")
    identity = receipt.get("verifier_identity")
    if not isinstance(identity, dict) or not identity:
        fail("Terminal5 verifier identity is absent")
    for key in (
        "preflight_source_sha256",
        "authoritative_plan_verifier_sha256",
        "terminal_plan_parser_sha256",
        "leaf_plan_parser_sha256",
    ):
        require_hex(identity.get(key), f"Terminal5 verifier identity {key}")
    for group in ("runtime_binding_sha256", "pipeline_binding_sha256"):
        bindings = identity.get(group)
        if not isinstance(bindings, dict) or not bindings:
            fail(f"Terminal5 verifier identity {group} is absent")
        for role, digest in bindings.items():
            if not isinstance(role, str) or not role:
                fail(f"Terminal5 verifier identity {group} contains an invalid role")
            require_hex(digest, f"Terminal5 verifier identity {group}.{role}")
    return str(receipt["terminal_plan_sha256"])


def validate_terminal(
    terminal: Mapping[str, Any], supplement: Mapping[str, Any], plan_hash: str
) -> Mapping[str, Any]:
    require_equal(
        terminal,
        {
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
        },
        "Terminal5 global summary",
    )
    expected_counts = {
        "1": (5_176, 0, 5_176, TERMINAL_NODES[1]),
        "4": (1_294, 30, 1_324, TERMINAL_NODES[4]),
        "5": (25_254, 0, 25_254, TERMINAL_NODES[5]),
        "6": (3_977, 0, 3_977, TERMINAL_NODES[6]),
        "7": (3_299, 0, 3_299, TERMINAL_NODES[7]),
    }
    observed = terminal.get("by_configuration")
    if not isinstance(observed, dict) or set(observed) != set(expected_counts):
        fail("Terminal5 configuration roster mismatch")
    for configuration, expected in expected_counts.items():
        item = observed[configuration]
        if not isinstance(item, dict):
            fail(f"Terminal5 Configuration {configuration} summary is malformed")
        actual = (
            item.get("search_receipts"),
            item.get("certified_zero_records"),
            item.get("displayed_partition_records"),
            item.get("nodes_sum"),
        )
        if actual != expected or item.get("terminal_zero") is not True:
            fail(f"Terminal5 Configuration {configuration} result mismatch")

    require_equal(
        supplement,
        {
            "schema": "LEECH18_CONFIG4_CERTIFIED_ZERO_FRESH_RECOMPUTATION_V1",
            "status": "ZERO_COMPLETE",
            "configuration": 4,
            "mode": "g001_row3",
            "prior_classification": "CERTIFIED_ZERO",
            "fresh_terminal_searches": 30,
            "fresh_zero_results": 30,
            "terminal_plan_id": "g001-terminal5-v1-candidate4",
            "terminal_plan_sha256": plan_hash,
            "frozen_terminal_plan_sha256": FROZEN_PLAN_SHA256,
            "non_runtime_plan_fields_match_frozen": True,
            "authoritative_plan_runtime_verified": True,
            "derived_roster_bytes": 12_402,
            "derived_roster_sha256": (
                "ead047bedce8674ce516172919846873531b82932a4533a57ac88f7b3fea5de9"
            ),
            "reported_terminal5_nodes_excluding_supplemental": sum(
                TERMINAL_NODES.values()
            ),
        },
        "Configuration 4 supplemental summary",
    )
    records = supplement.get("records")
    if not isinstance(records, list) or len(records) != 30:
        fail("Configuration 4 supplemental record count mismatch")
    identifiers: set[str] = set()
    node_sum = 0
    for index, record in enumerate(records):
        if not isinstance(record, dict):
            fail(f"Configuration 4 supplemental record {index} is malformed")
        identifier = record.get("record_id")
        nodes = record.get("nodes")
        if not isinstance(identifier, str) or not identifier or identifier in identifiers:
            fail(f"Configuration 4 supplemental record {index} identity is missing/duplicate")
        if isinstance(nodes, bool) or not isinstance(nodes, int) or nodes < 0:
            fail(f"Configuration 4 supplemental record {index} node count is invalid")
        require_hex(record.get("argv_sha256"), f"Configuration 4 record {index} argv digest")
        require_hex(record.get("marker_sha256"), f"Configuration 4 record {index} marker digest")
        identifiers.add(identifier)
        node_sum += nodes
    if supplement.get("supplemental_nodes") != node_sum:
        fail("Configuration 4 supplemental node total mismatch")
    return {
        "canonical_search_receipts": 39_000,
        "configuration4_supplemental_zero_searches": 30,
        "reported_nodes_excluding_supplemental": sum(TERMINAL_NODES.values()),
        "supplemental_nodes_not_in_paper_total": node_sum,
    }


def parse_arguments(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prior-three-summary", required=True, type=Path)
    parser.add_argument("--prior-three-build-receipt", required=True, type=Path)
    parser.add_argument("--c157-summary", required=True, type=Path)
    parser.add_argument("--terminal-summary", required=True, type=Path)
    parser.add_argument("--config4-summary", required=True, type=Path)
    parser.add_argument("--terminal-preflight", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    arguments = parse_arguments(argv)
    try:
        prior, prior_hash = read_json(arguments.prior_three_summary, "prior-three summary")
        build, build_hash = read_json(
            arguments.prior_three_build_receipt, "prior-three build receipt"
        )
        c157, c157_hash = read_json(arguments.c157_summary, "C157 summary")
        terminal, terminal_hash = read_json(arguments.terminal_summary, "Terminal5 summary")
        config4, config4_hash = read_json(arguments.config4_summary, "Configuration 4 summary")
        preflight, preflight_hash = read_json(
            arguments.terminal_preflight, "Terminal5 preflight receipt"
        )

        prior_record = validate_prior(
            arguments.prior_three_summary,
            prior,
            arguments.prior_three_build_receipt,
            build,
            build_hash,
        )
        c157_record = validate_c157(arguments.c157_summary, c157)
        plan_hash = validate_terminal_preflight(preflight)
        terminal_record = validate_terminal(terminal, config4, plan_hash)
        if sum(PRIOR_NODES.values()) + sum(TERMINAL_NODES.values()) != REPORTED_NODES:
            fail("internal all-eight reported-node total mismatch")

        output = {
            "schema": SCHEMA,
            "status": STATUS,
            "configuration_results": {
                str(key): {"excluded": True, "reported_nodes": value}
                for key, value in sorted({**PRIOR_NODES, **TERMINAL_NODES}.items())
            },
            "configurations_excluded": list(range(1, 9)),
            "frozen_terminal_plan_sha256": FROZEN_PLAN_SHA256,
            "input_sha256": {
                "prior_three_summary": prior_hash,
                "prior_three_build_receipt": build_hash,
                "c157_summary": c157_hash,
                "terminal_summary": terminal_hash,
                "configuration4_summary": config4_hash,
                "terminal_preflight": preflight_hash,
            },
            "prior_three": prior_record,
            "c157_coverage": c157_record,
            "terminal_five": terminal_record,
            "reported_node_visits": REPORTED_NODES,
            "scope": {
                "constructs_lean_proof_term": False,
                "reruns_search": False,
                "uses_frozen_partition_plan": True,
                "validates_completed_stage_records": True,
            },
            "terminal_plan_sha256": plan_hash,
        }
        data = canonical_json(output)
        write_new(arguments.output, data)
        output_path = Path(os.path.abspath(os.fspath(arguments.output.expanduser())))
        print(
            "LEECH18_FRESH_ALL_EIGHT_ASSEMBLED configurations=8 "
            f"reported_nodes={REPORTED_NODES} status={STATUS}"
        )
        print(
            "LEECH18_FRESH_ALL_EIGHT_RECEIPT "
            f"path={output_path} sha256={hashlib.sha256(data).hexdigest()}"
        )
        return 0
    except (AssemblyError, OSError, UnicodeError, ValueError, TypeError) as error:
        print(f"LEECH18_FRESH_ALL_EIGHT_ASSEMBLY_FAILED: {error}", file=os.sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
