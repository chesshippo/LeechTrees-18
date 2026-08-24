#!/usr/bin/env python3
"""Strict, cross-platform checks for the five-row shallow G001 pilot.

The live check executes only fixed-depth diagnostics (through depth eight).
It cannot start a terminal census.  The run-directory check audits the raw
artifacts produced by run_g001_remaining_shallow_benchmark.py; timeouts and
deadline skips remain explicitly inconclusive.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from typing import Dict, Iterable, List, Mapping, Optional, Sequence, Tuple


PRODUCTION_FLAGS = [
    "--multi-edge-cover",
    "--multi-edge-cover-no-hall",
    "--multi-edge-cover-max-components", "6",
    "--multi-edge-cover-budget", "100",
    "--multi-edge-cover-no-exact-hall",
]
PRODUCTION_SWITCHES = {item for item in PRODUCTION_FLAGS if item.startswith("--")}

# mode: (seed MEX, first-child MEX distribution)
EXPECTED = {
    "g001_row0": (5, {6: 4, 7: 2, 8: 2}),
    "g001_row3": (7, {8: 3, 9: 1, 10: 1}),
    "g001_row4": (4, {5: 4, 6: 2, 8: 1}),
    "g001_row5": (5, {6: 4, 7: 2, 10: 1}),
    "g001_row6": (4, {6: 2, 7: 1, 8: 1}),
}

INTEGER_FIELDS = {
    "nodes", "states", "generated", "duplicate", "collision", "range",
    "parity", "diameter", "g002", "cutlower", "cutupper", "late_t9a",
    "solution_topologies", "root_valid", "frontier", "cover_checks",
    "cover_skipped", "cover_skipped_full", "cover_local_slots",
    "cover_local_patterns", "cover_slots", "cover_patterns",
    "cover_candidates", "cover_no_candidate", "cover_hall_fail",
    "cover_exact_calls", "cover_exact_fail", "cover_exact_pass",
    "cover_exact_budget", "cover_exact_cap", "cover_exact_states",
    "cover_exact_hall_fail", "cover_validation_fail", "cover_shadow_reject",
}
MAP_FIELDS = {
    "depth", "frontier_mex", "frontier_odd", "frontier_q3", "child_max"
}
REQUIRED_BASE = {
    "mode", "status", "nodes", "states", "generated", "duplicate",
    "collision", "range", "parity", "diameter", "g002", "cutlower",
    "cutupper", "late_t9a", "solution_topologies", "depth", "root_valid",
    "frontier", "frontier_mex", "frontier_odd", "frontier_q3", "child_max",
}
REQUIRED_COVER = {
    "multi_cover", "cover_checks", "cover_skipped", "cover_skipped_full",
    "cover_local_slots", "cover_local_patterns", "cover_slots",
    "cover_patterns", "cover_candidates", "cover_no_candidate",
    "cover_hall_fail", "cover_exact_calls", "cover_exact_fail",
    "cover_exact_pass", "cover_exact_budget", "cover_exact_cap",
    "cover_exact_states", "cover_exact_hall_fail", "cover_validation_fail",
    "cover_shadow_reject",
}
COMMON_COMPARE = [
    "nodes", "states", "generated", "duplicate", "collision", "range",
    "parity", "diameter", "g002", "cutlower", "cutupper", "late_t9a",
    "solution_topologies", "depth", "root_valid", "frontier",
    "frontier_mex", "frontier_odd", "frontier_q3", "child_max",
]
TOKEN_RE = re.compile(r"([A-Za-z_][A-Za-z0-9_]*)=([^\s]*)")
HEX64_RE = re.compile(r"[0-9a-f]{64}")


class VerificationError(RuntimeError):
    pass


def atomic_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=path.name + ".", dir=str(path.parent))
    try:
        with os.fdopen(fd, "w", encoding="utf-8", newline="\n") as stream:
            json.dump(value, stream, indent=2, sort_keys=True)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    except BaseException:
        try:
            os.unlink(temporary)
        except OSError:
            pass
        raise


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def expected_benchmark_specs() -> Dict[str, Dict[str, object]]:
    specs: Dict[str, Dict[str, object]] = {}
    for mode in EXPECTED:
        for depth in (8, 9, 10, 11):
            for variant in ("baseline", "production"):
                run_id = "{}.d{}.{}".format(mode, depth, variant)
                arguments = ["--mode", mode, "--stop-edges", str(depth)]
                if variant == "production":
                    arguments += PRODUCTION_FLAGS
                specs[run_id] = {
                    "mode": mode, "variant": variant, "depth": str(depth),
                    "selector": "all", "arguments": arguments,
                }
    for mode, (_mex, distribution) in EXPECTED.items():
        for root in range(sum(distribution.values())):
            for variant in ("baseline", "production"):
                run_id = "{}.d12.root{:02d}.{}".format(mode, root, variant)
                arguments = [
                    "--mode", mode, "--root-branch", str(root),
                    "--stop-edges", "12",
                ]
                if variant == "production":
                    arguments += PRODUCTION_FLAGS
                specs[run_id] = {
                    "mode": mode, "variant": variant, "depth": "12",
                    "selector": "root:{}".format(root), "arguments": arguments,
                }
    if len(specs) != 102:
        raise AssertionError("internal benchmark specification is not 102 runs")
    return specs


def verify_artifact_manifest(run_dir: Path) -> Dict[str, str]:
    manifest = run_dir / "artifacts.sha256"
    if not manifest.is_file():
        raise VerificationError("run directory lacks artifacts.sha256")
    listed: Dict[str, str] = {}
    for line in manifest.read_text(encoding="utf-8", errors="strict").splitlines():
        match = re.fullmatch(r"([0-9a-f]{64})  ([^\\]+)", line)
        if not match:
            raise VerificationError("malformed artifacts.sha256 line")
        expected_hash, relative = match.group(1), match.group(2)
        candidate = (run_dir / relative).resolve()
        if relative in listed or run_dir.resolve() not in candidate.parents or not candidate.is_file():
            raise VerificationError("duplicate, escaping, or missing manifest path {!r}".format(relative))
        if sha256(candidate) != expected_hash:
            raise VerificationError("artifact hash mismatch for {}".format(relative))
        listed[relative] = expected_hash
    for required in ("driver_manifest.json", "environment.json", "results.csv", "summary.json"):
        if required not in listed:
            raise VerificationError("artifact manifest does not bind {}".format(required))
    return listed


def parse_nonnegative(text: str, label: str) -> int:
    if not re.fullmatch(r"0|[1-9][0-9]*", text):
        raise VerificationError("{} is not a canonical nonnegative integer: {!r}".format(label, text))
    return int(text)


def parse_map(text: str, label: str) -> Dict[int, int]:
    if text == "":
        return {}
    if not text.endswith(","):
        raise VerificationError("{} lacks the required trailing comma".format(label))
    result: Dict[int, int] = {}
    for item in text[:-1].split(","):
        match = re.fullmatch(r"(-?(?:0|[1-9][0-9]*)):(0|[1-9][0-9]*)", item)
        if not match:
            raise VerificationError("malformed {} item {!r}".format(label, item))
        key, count = int(match.group(1)), int(match.group(2))
        if key in result or count <= 0:
            raise VerificationError("duplicate key or nonpositive count in {}".format(label))
        result[key] = count
    return result


def parse_result(stdout: str, expected_mode: str, cover: bool) -> Tuple[Dict[str, str], Dict[str, Dict[int, int]]]:
    lines = stdout.splitlines()
    result_lines = [line for line in lines if line.startswith("RESULT ")]
    if len(result_lines) != 1 or len(lines) != 1:
        raise VerificationError("expected exactly one stdout RESULT line")
    line = result_lines[0]
    fields: Dict[str, str] = {}
    position = len("RESULT ")
    for match in TOKEN_RE.finditer(line, position):
        if match.start() != position:
            raise VerificationError("unparsed text in RESULT near {!r}".format(line[position:match.start()]))
        key, value = match.group(1), match.group(2)
        if key in fields:
            raise VerificationError("duplicate RESULT field {}".format(key))
        fields[key] = value
        position = match.end()
        if position < len(line) and line[position] == " ":
            position += 1
    if position != len(line):
        raise VerificationError("unparsed RESULT suffix {!r}".format(line[position:]))
    required = REQUIRED_BASE | (REQUIRED_COVER if cover else set())
    missing = sorted(required - set(fields))
    if missing:
        raise VerificationError("missing RESULT fields: {}".format(",".join(missing)))
    if fields["mode"] != expected_mode or fields["status"] != "FRONTIER":
        raise VerificationError("unexpected mode/status: {}/{}".format(fields["mode"], fields["status"]))
    for key in INTEGER_FIELDS & set(fields):
        parse_nonnegative(fields[key], key)
    maps = {key: parse_map(fields[key], key) for key in MAP_FIELDS}
    frontier = parse_nonnegative(fields["frontier"], "frontier")
    for key in ("frontier_mex", "frontier_odd", "frontier_q3"):
        if sum(maps[key].values()) != frontier:
            raise VerificationError("{} does not sum to frontier".format(key))
    if parse_nonnegative(fields["solution_topologies"], "solution_topologies") != 0:
        raise VerificationError("a shallow run unexpectedly reported a solution")
    for key in ("g002", "cutlower", "cutupper", "late_t9a"):
        if fields[key] != "0":
            raise VerificationError("off-by-default counter {} is nonzero".format(key))
    if cover:
        if fields["multi_cover"] != "on" or fields["cover_validation_fail"] != "0":
            raise VerificationError("active cover or validation invariant failed")
        calls = int(fields["cover_exact_calls"])
        terminal = int(fields["cover_exact_fail"]) + int(fields["cover_exact_pass"]) + int(fields["cover_exact_budget"])
        if calls != terminal:
            raise VerificationError("exact-call accounting identity failed")
        if fields["cover_hall_fail"] != "0" or fields["cover_exact_hall_fail"] != "0":
            raise VerificationError("disabled Hall counter is nonzero")
    elif "multi_cover" in fields:
        raise VerificationError("baseline unexpectedly reports multi_cover")
    return fields, maps


def run_checked(executable: Path, arguments: Sequence[str], mode: str, cover: bool,
                timeout: float) -> Tuple[Dict[str, str], Dict[str, Dict[int, int]]]:
    completed = subprocess.run(
        [str(executable)] + list(arguments), stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, text=True, encoding="utf-8", errors="strict",
        timeout=timeout, check=False,
    )
    if completed.returncode != 0:
        raise VerificationError("command exited {}: {}".format(completed.returncode, " ".join(arguments)))
    if completed.stderr != "":
        raise VerificationError("command wrote stderr: {}".format(" ".join(arguments)))
    return parse_result(completed.stdout, mode, cover)


def add_maps(target: Dict[int, int], source: Mapping[int, int]) -> None:
    for key, count in source.items():
        target[key] = target.get(key, 0) + count


def assert_common_equal(first: Mapping[str, str], second: Mapping[str, str], label: str) -> None:
    differences = [key for key in COMMON_COMPARE if first[key] != second[key]]
    if differences:
        raise VerificationError("baseline/production mismatch at {}: {}".format(label, ",".join(differences)))


def verify_oracle(oracle: Path, timeout: float) -> None:
    completed = subprocess.run(
        [str(oracle)], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        encoding="utf-8", errors="strict", timeout=timeout, check=False,
    )
    if completed.returncode != 0 or completed.stderr != "":
        raise VerificationError("seed-orbit oracle failed")
    expected_lines = []
    for mode, (mex, distribution) in EXPECTED.items():
        children = sum(distribution.values())
        child_mex = "".join("{}:{},".format(k, v) for k, v in sorted(distribution.items()))
        # valid_raw_pairs is deliberately not frozen; the independent orbit
        # count and MEX distribution are the mathematical interface.
        expected_lines.append((mode, mex, children, child_mex))
    lines = completed.stdout.splitlines()
    if not lines or lines[-1] != "G001_REMAINING_SEED_ORBIT_ORACLE_OK":
        raise VerificationError("oracle success marker missing")
    oracle_rows: Dict[str, Tuple[int, int, str]] = {}
    pattern = re.compile(r"ORACLE mode=(\S+) seed_mex=(\d+) valid_raw_pairs=(\d+) children=(\d+) child_mex=(\S+)")
    for line in lines[:-1]:
        match = pattern.fullmatch(line)
        if not match or match.group(1) in oracle_rows:
            raise VerificationError("malformed or duplicate oracle line")
        oracle_rows[match.group(1)] = (int(match.group(2)), int(match.group(4)), match.group(5))
    for mode, mex, children, child_mex in expected_lines:
        if oracle_rows.get(mode) != (mex, children, child_mex):
            raise VerificationError("oracle mismatch for {}".format(mode))
    if set(oracle_rows) != set(EXPECTED):
        raise VerificationError("oracle mode set mismatch")


def live_verify(solver: Path, oracle: Path, timeout: float, output_json: Optional[Path]) -> Dict[str, object]:
    if not solver.is_file() or not oracle.is_file():
        raise VerificationError("solver and oracle must be existing files")
    verify_oracle(oracle, timeout)
    report: Dict[str, object] = {
        "schema": "g001-remaining-shallow-preflight-v1",
        "solver": str(solver.resolve()), "solver_sha256": sha256(solver),
        "oracle": str(oracle.resolve()), "oracle_sha256": sha256(oracle),
        "production_flags": PRODUCTION_FLAGS, "modes": {},
    }
    for mode, (seed_mex, first_mex) in EXPECTED.items():
        mode_report: Dict[str, object] = {"seed_mex": seed_mex}
        for depth in (3, 4):
            base, base_maps = run_checked(solver, ["--mode", mode, "--stop-edges", str(depth)], mode, False, timeout)
            prod, _ = run_checked(solver, ["--mode", mode, "--stop-edges", str(depth)] + PRODUCTION_FLAGS, mode, True, timeout)
            assert_common_equal(base, prod, "{} depth {}".format(mode, depth))
            if depth == 3:
                if base["nodes"] != "1" or base["states"] != "1" or base["generated"] != "0" or base["frontier"] != "1" or base_maps["frontier_mex"] != {seed_mex: 1}:
                    raise VerificationError("seed-depth invariant failed for {}".format(mode))
            else:
                if int(base["root_valid"]) != sum(first_mex.values()) or base_maps["frontier_mex"] != first_mex:
                    raise VerificationError("first fan-out mismatch for {}".format(mode))

        root_count = sum(first_mex.values())
        unfiltered, unfiltered_maps = run_checked(
            solver, ["--mode", mode, "--stop-edges", "5"], mode, False, timeout)
        child_counts: List[int] = []
        child_mex_sum: Dict[int, int] = {}
        for root in range(root_count):
            args = ["--mode", mode, "--branch-path", str(root), "--stop-edges", "5"]
            base, maps = run_checked(solver, args, mode, False, timeout)
            prod, _ = run_checked(solver, args + PRODUCTION_FLAGS, mode, True, timeout)
            assert_common_equal(base, prod, "{} root {}".format(mode, root))
            child_counts.append(int(base["frontier"]))
            add_maps(child_mex_sum, maps["frontier_mex"])
        if sum(child_counts) != int(unfiltered["frontier"]) or child_mex_sum != unfiltered_maps["frontier_mex"]:
            raise VerificationError("second-level additive fan-out failed for {}".format(mode))

        base8, _ = run_checked(solver, ["--mode", mode, "--stop-edges", "8"], mode, False, timeout)
        prod8, _ = run_checked(solver, ["--mode", mode, "--stop-edges", "8"] + PRODUCTION_FLAGS, mode, True, timeout)
        assert_common_equal(base8, prod8, "{} dormant depth 8".format(mode))
        mode_report.update({
            "first_children": root_count,
            "first_child_mex": {str(k): v for k, v in first_mex.items()},
            "second_child_counts": child_counts,
            "second_frontier": int(unfiltered["frontier"]),
            "depth8_frontier": int(base8["frontier"]),
        })
        report["modes"][mode] = mode_report
        print("SHALLOW_OK mode={} roots={} second_frontier={} depth8_frontier={}".format(
            mode, root_count, unfiltered["frontier"], base8["frontier"]))
    if output_json is not None:
        atomic_json(output_json, report)
    print("G001_REMAINING_SHALLOW_VERIFICATION_OK")
    return report


def verify_run_directory(run_dir: Path, require_complete: bool) -> None:
    listed_artifacts = verify_artifact_manifest(run_dir)
    specs = expected_benchmark_specs()
    driver_manifest_path = run_dir / "driver_manifest.json"
    driver_manifest = json.loads(driver_manifest_path.read_text(encoding="utf-8", errors="strict"))
    if (driver_manifest.get("schema") != "g001-remaining-shallow-benchmark-v1" or
            driver_manifest.get("task_count") != 102 or
            driver_manifest.get("production_flags") != PRODUCTION_FLAGS):
        raise VerificationError("driver_manifest.json contract mismatch")
    solver_hash = driver_manifest.get("solver_sha256")
    for hash_key in ("solver_sha256", "oracle_sha256", "verifier_sha256", "driver_sha256"):
        if not isinstance(driver_manifest.get(hash_key), str) or not HEX64_RE.fullmatch(driver_manifest[hash_key]):
            raise VerificationError("invalid {} in driver manifest".format(hash_key))
    results_path = run_dir / "results.csv"
    if not results_path.is_file():
        raise VerificationError("run directory lacks results.csv")
    with results_path.open("r", encoding="utf-8", newline="") as stream:
        reader = csv.DictReader(stream)
        rows = list(reader)
    required_columns = {
        "run_id", "mode", "variant", "depth", "selector", "argv_json",
        "outcome", "exit_code", "timed_out", "stdout_path", "stderr_path",
        "time_path", "meta_path", "result_status", "nodes", "states", "frontier",
        "wall_seconds", "solver_sha256",
    }
    if reader.fieldnames is None or not required_columns.issubset(reader.fieldnames):
        raise VerificationError("results.csv schema mismatch")
    by_id: Dict[str, Mapping[str, str]] = {}
    valid = timeouts = skipped = 0
    for row in rows:
        run_id = row["run_id"]
        if not re.fullmatch(r"[A-Za-z0-9_.-]+", run_id) or run_id in by_id:
            raise VerificationError("bad or duplicate run_id {!r}".format(run_id))
        by_id[run_id] = row
        if run_id not in specs:
            raise VerificationError("unexpected benchmark run ID {}".format(run_id))
        spec = specs[run_id]
        mode, variant = row["mode"], row["variant"]
        for key in ("mode", "variant", "depth", "selector"):
            if row[key] != str(spec[key]):
                raise VerificationError("{} mismatch in {}".format(key, run_id))
        argv = json.loads(row["argv_json"])
        if not isinstance(argv, list) or any(not isinstance(x, str) for x in argv):
            raise VerificationError("invalid argv_json in {}".format(run_id))
        if argv != spec["arguments"]:
            raise VerificationError("exact argv mismatch in {}".format(run_id))
        if "--max-nodes" in argv:
            raise VerificationError("forbidden --max-nodes in {}".format(run_id))
        if variant == "production":
            if argv[-len(PRODUCTION_FLAGS):] != PRODUCTION_FLAGS:
                raise VerificationError("production flags differ in {}".format(run_id))
        elif any(flag in argv for flag in PRODUCTION_SWITCHES):
            raise VerificationError("baseline contains a production flag in {}".format(run_id))
        if row["solver_sha256"] != solver_hash:
            raise VerificationError("solver hash mismatch in {}".format(run_id))

        artifact_keys = ("stdout_path", "stderr_path", "time_path", "meta_path")
        artifact_paths: Dict[str, Path] = {}
        for key in artifact_keys:
            relative = row[key]
            path = (run_dir / relative).resolve()
            if (not relative or run_dir.resolve() not in path.parents or
                    not path.is_file() or relative not in listed_artifacts):
                raise VerificationError("unbound, missing, or escaping {} in {}".format(key, run_id))
            artifact_paths[key] = path
        metadata = json.loads(artifact_paths["meta_path"].read_text(
            encoding="utf-8", errors="strict"))
        if metadata.get("schema") != "g001-remaining-shallow-benchmark-v1":
            raise VerificationError("metadata schema mismatch in {}".format(run_id))
        for key, value in row.items():
            if key not in metadata or str(metadata[key]) != value:
                raise VerificationError("CSV/meta mismatch for {} in {}".format(key, run_id))
        command = metadata.get("command")
        if not isinstance(command, list) or command[1:] != argv:
            raise VerificationError("metadata command mismatch in {}".format(run_id))
        for path_key, hash_key in (("stdout_path", "stdout_sha256"),
                                   ("stderr_path", "stderr_sha256"),
                                   ("time_path", "time_sha256")):
            expected_hash = metadata.get(hash_key)
            if not isinstance(expected_hash, str) or not HEX64_RE.fullmatch(expected_hash) or sha256(artifact_paths[path_key]) != expected_hash:
                raise VerificationError("metadata artifact hash mismatch in {}".format(run_id))
        outcome = row["outcome"]
        if outcome == "VALID":
            valid += 1
            if row["exit_code"] != "0" or row["timed_out"] != "0" or row["result_status"] != "FRONTIER":
                raise VerificationError("invalid successful metadata in {}".format(run_id))
            stderr = artifact_paths["stderr_path"].read_text(encoding="utf-8")
            if stderr != "":
                raise VerificationError("VALID run has nonempty stderr: {}".format(run_id))
            stdout = artifact_paths["stdout_path"].read_text(encoding="utf-8")
            fields, _ = parse_result(stdout, mode, variant == "production")
            for key in ("nodes", "states", "frontier"):
                if row[key] != fields[key]:
                    raise VerificationError("CSV/RESULT mismatch for {} in {}".format(key, run_id))
        elif outcome == "TIMEOUT":
            timeouts += 1
            if row["timed_out"] != "1":
                raise VerificationError("TIMEOUT lacks timed_out=1 in {}".format(run_id))
        elif outcome in ("DEADLINE_SKIPPED", "INTERRUPTED"):
            skipped += 1
        else:
            raise VerificationError("non-auditable outcome {} in {}".format(outcome, run_id))

    missing = sorted(set(specs) - set(by_id))
    unexpected = sorted(set(by_id) - set(specs))
    if missing or unexpected or len(rows) != 102:
        raise VerificationError("benchmark ID set mismatch: missing={} unexpected={} rows={}".format(
            ",".join(missing), ",".join(unexpected), len(rows)))

    complete = timeouts == 0 and skipped == 0 and all(row["outcome"] == "VALID" for row in rows)
    print("RUN_AUDIT_OK rows={} valid={} timeouts={} skipped={} complete={}".format(
        len(rows), valid, timeouts, skipped, int(complete)))
    if require_complete and not complete:
        raise VerificationError("run is integral but incomplete")
    print("G001_REMAINING_BENCHMARK_ARTIFACTS_OK")


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solver", type=Path)
    parser.add_argument("--oracle", type=Path)
    parser.add_argument("--timeout-seconds", type=float, default=120.0)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--run-dir", type=Path)
    parser.add_argument("--require-complete", action="store_true")
    args = parser.parse_args(argv)
    try:
        if args.run_dir is not None:
            if args.solver is not None or args.oracle is not None:
                raise VerificationError("choose live verification or --run-dir audit")
            verify_run_directory(args.run_dir.resolve(), args.require_complete)
        else:
            if args.solver is None or args.oracle is None:
                raise VerificationError("live verification requires --solver and --oracle")
            if args.timeout_seconds <= 0:
                raise VerificationError("timeout must be positive")
            live_verify(args.solver.resolve(), args.oracle.resolve(), args.timeout_seconds,
                        args.output_json.resolve() if args.output_json else None)
    except (VerificationError, OSError, subprocess.SubprocessError, UnicodeError, ValueError, json.JSONDecodeError) as error:
        print("VERIFICATION_FAILED: {}".format(error), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
