#!/usr/bin/env python3
"""Strictly collect one leaf, or every recorded leaf, without claiming coverage."""

from __future__ import annotations

import argparse
import json
import math
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple

import g001_remaining_leaf_common as leaf_common_module
from g001_remaining_leaf_common import (
    COLLECTION_SCHEMA,
    EVIDENCE_SCHEMA,
    EXIT_SCHEMA,
    FOUND_MARKER_SCHEMA,
    LAUNCH_SCHEMA,
    NO_EVIDENCE_EXIT,
    NO_EVIDENCE_SCHEMA,
    TIMING_SCHEMA,
    USAGE_EXIT,
    ValidationError,
    ZERO_MARKER_SCHEMA,
    atomic_write_new,
    bound_hash_document,
    canonical_json_bytes,
    canonical_sha256,
    load_json,
    load_plan,
    parse_result,
    resolved_solver_argv,
    selector_text,
    sha256_file,
    verify_bound_artifacts,
    verify_executing_pipeline,
    verify_file_hashes,
    verify_pipeline_artifacts,
)


WITNESS_NAME = "witness.LEECH_WITNESS_V1.txt"
MARKERS = (
    "ZERO_COMPLETE_V1.json",
    "VERIFIED_FOUND_V1.json",
    "NO_EVIDENCE_V1.json",
)


class NoEvidence(RuntimeError):
    pass


def require_equal(actual: Any, expected: Any, context: str) -> None:
    if actual != expected:
        raise ValidationError(
            f"{context} mismatch: expected {expected!r}, got {actual!r}")


def require_positive_number(value: Any, context: str) -> None:
    if isinstance(value, bool) or not isinstance(value, (int, float)) or \
            not math.isfinite(value) or value <= 0:
        raise ValidationError(f"{context} must be positive")


def select_marker(directory: Path) -> Tuple[Path, Dict[str, Any]]:
    candidates = [directory / name for name in MARKERS
                  if (directory / name).exists() or
                  (directory / name).is_symlink()]
    if any(path.is_symlink() for path in candidates):
        raise ValidationError("terminal marker must not be a symbolic link")
    present = [path for path in candidates if path.is_file()]
    if not present:
        raise NoEvidence("leaf has no durable terminal marker")
    if len(present) != 1:
        raise ValidationError("leaf has multiple terminal markers")
    marker_path = present[0]
    marker = load_json(marker_path)
    if marker_path.name == "NO_EVIDENCE_V1.json":
        if marker.get("schema") != NO_EVIDENCE_SCHEMA or \
                marker.get("outcome") != "NO_EVIDENCE":
            raise ValidationError("malformed NO_EVIDENCE marker")
        raise NoEvidence(str(marker.get("reason", "worker recorded no evidence")))
    expected_schema = (ZERO_MARKER_SCHEMA if marker_path.name.startswith("ZERO")
                       else FOUND_MARKER_SCHEMA)
    if marker.get("schema") != expected_schema:
        raise ValidationError("terminal marker schema does not match filename")
    return marker_path, marker


def validate_identity(marker: Mapping[str, Any], plan: Mapping[str, Any],
                      plan_hash: str, leaf: Mapping[str, Any], index: int,
                      argv: Sequence[str], bindings: Mapping[str, Any],
                      pipeline_bindings: Mapping[str, Any]) -> None:
    require_equal(marker.get("plan_id"), plan["plan_id"], "marker plan_id")
    require_equal(marker.get("plan_sha256"), plan_hash, "marker plan hash")
    require_equal(marker.get("leaf_index"), index, "marker leaf index")
    require_equal(marker.get("leaf_id"), leaf["leaf_id"], "marker leaf_id")
    require_equal(marker.get("leaf_sha256"), canonical_sha256(leaf),
                  "marker leaf hash")
    require_equal(marker.get("configuration"), leaf["configuration"],
                  "marker configuration")
    require_equal(marker.get("mode"), leaf["mode"], "marker mode")
    require_equal(marker.get("selector"), leaf["selector"], "marker selector")
    require_equal(marker.get("selector_text"), selector_text(leaf["selector"]),
                  "marker selector text")
    require_equal(marker.get("argv_sha256"), canonical_sha256(list(argv)),
                  "marker argv hash")
    require_equal(
        marker.get("cover_candidate_validation_enabled"),
        "--multi-edge-cover-validate" in leaf["argv_template"],
        "marker cover candidate validation setting",
    )
    expected_hashes = bound_hash_document(bindings, pipeline_bindings)
    require_equal(marker.get("bound_hashes"), expected_hashes,
                  "marker bound hashes")


def validate_launch(directory: Path, plan: Mapping[str, Any], plan_hash: str,
                    leaf: Mapping[str, Any], index: int, argv: Sequence[str],
                    bindings: Mapping[str, Any],
                    pipeline_bindings: Mapping[str, Any]) -> Dict[str, Any]:
    launch = load_json(directory / "launch.json", LAUNCH_SCHEMA)
    require_equal(launch.get("plan_id"), plan["plan_id"], "launch plan_id")
    require_equal(launch.get("plan_sha256"), plan_hash, "launch plan hash")
    require_equal(launch.get("leaf_index"), index, "launch leaf index")
    require_equal(launch.get("leaf_id"), leaf["leaf_id"], "launch leaf_id")
    require_equal(launch.get("leaf_sha256"), canonical_sha256(leaf),
                  "launch leaf hash")
    require_equal(launch.get("configuration"), leaf["configuration"],
                  "launch configuration")
    require_equal(launch.get("mode"), leaf["mode"], "launch mode")
    require_equal(launch.get("selector"), leaf["selector"], "launch selector")
    require_equal(launch.get("argv"), list(argv), "launch exact argv")
    require_equal(launch.get("argv_sha256"), canonical_sha256(list(argv)),
                  "launch argv hash")
    launch_bindings = launch.get("bindings")
    if not isinstance(launch_bindings, dict):
        raise ValidationError("launch bindings are missing")
    for role in (
        "solver_source", "solver_executable",
        "checker_source", "checker_executable",
    ):
        require_equal(launch_bindings.get(role), bindings[role],
                      f"launch binding {role}")
    require_equal(launch_bindings.get("dependencies"), bindings["dependencies"],
                  "launch dependency bindings")
    require_equal(launch.get("pipeline_bindings"), pipeline_bindings,
                  "launch pipeline bindings")
    require_equal(
        launch.get("executing_pipeline"),
        {
            role: pipeline_bindings[role]
            for role in ("leaf_worker", "leaf_common")
        },
        "launch executing pipeline",
    )
    return launch


def validate_process_metadata(directory: Path, stem: str,
                              expected_exit: int) -> Tuple[Dict[str, Any],
                                                           Dict[str, Any]]:
    timing = load_json(directory / (stem + ".timing.json"), TIMING_SCHEMA)
    exit_data = load_json(directory / (stem + ".exit.json"), EXIT_SCHEMA)
    require_equal(timing.get("process"), stem, f"{stem} timing process")
    require_equal(exit_data.get("process"), stem, f"{stem} exit process")
    require_positive_number(timing.get("wall_seconds"),
                            f"{stem} wall_seconds")
    require_equal(exit_data.get("exit_code"), expected_exit,
                  f"{stem} exit code")
    require_equal(exit_data.get("timed_out"), False, f"{stem} timeout")
    require_equal(exit_data.get("interrupted_signal"), None,
                  f"{stem} interrupted signal")
    require_equal(exit_data.get("launch_error"), None,
                  f"{stem} launch error")
    return timing, exit_data


def canonical_checker_output(leaf: Mapping[str, Any]) -> str:
    return (
        "VALID LEECH_WITNESS_V1 configuration=" +
        str(leaf["configuration"]) + " mode=" + leaf["mode"] +
        " vertices=18 edges=17 distances=1..153\n")


def rerun_checker(checker: Path, witness: Path, workspace: Path,
                  expected_stdout: str) -> None:
    try:
        completed = subprocess.run(
            [str(checker), str(witness)],
            cwd=str(workspace),
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=60,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise ValidationError(f"collector checker rerun failed: {exc}") from exc
    if completed.returncode != 0 or completed.stderr != b"":
        raise ValidationError("collector checker rerun was not clean exit 0")
    try:
        text = completed.stdout.decode("utf-8", errors="strict")
    except UnicodeDecodeError as exc:
        raise ValidationError("collector checker output is not UTF-8") from exc
    if text != expected_stdout:
        raise ValidationError("collector checker rerun output is not canonical")


def collect_leaf(plan: Mapping[str, Any], plan_hash: str, workspace: Path,
                 run_directory: Path, index: int,
                 pipeline_bindings: Mapping[str, Any]) -> Dict[str, Any]:
    if index < 0 or index >= len(plan["leaves"]):
        raise ValidationError(f"leaf index {index} is outside the plan")
    leaf = plan["leaves"][index]
    bindings = verify_bound_artifacts(leaf, workspace)
    directory = run_directory / leaf["leaf_id"]
    if not directory.is_dir() or directory.is_symlink():
        raise NoEvidence("leaf directory is missing or is not a real directory")
    partials = list(directory.glob("*.partial"))
    if partials:
        raise ValidationError("accepted leaf directory contains partial files")
    witness = directory / WITNESS_NAME
    argv = resolved_solver_argv(leaf, bindings, witness)
    marker_path, marker = select_marker(directory)
    validate_identity(
        marker, plan, plan_hash, leaf, index, argv, bindings,
        pipeline_bindings)

    files = marker.get("files")
    if not isinstance(files, dict):
        raise ValidationError("marker files map is missing")
    common_files = {
        "launch.json", "solver.stdout.txt", "solver.stderr.txt",
        "solver.timing.json", "solver.exit.json",
    }
    outcome = marker.get("outcome")
    if outcome == "ZERO":
        expected_files = common_files
        expected_exit = 0
        expected_status = "ZERO"
    elif outcome == "VERIFIED_FOUND":
        expected_files = common_files | {
            WITNESS_NAME, "checker.stdout.txt", "checker.stderr.txt",
            "checker.timing.json", "checker.exit.json",
        }
        expected_exit = 2
        expected_status = "FOUND"
    else:
        raise ValidationError(f"unsupported evidence outcome {outcome!r}")
    require_equal(set(files.keys()), expected_files, "marker evidence file set")
    verify_file_hashes(directory, files)
    validate_launch(
        directory, plan, plan_hash, leaf, index, argv, bindings,
        pipeline_bindings)
    solver_timing, _ = validate_process_metadata(
        directory, "solver", expected_exit)

    if (directory / "solver.stderr.txt").stat().st_size != 0:
        raise ValidationError("solver stderr is nonempty")
    try:
        solver_stdout = (directory / "solver.stdout.txt").read_text(
            encoding="utf-8", errors="strict")
    except (OSError, UnicodeDecodeError) as exc:
        raise ValidationError(f"solver stdout is not strict UTF-8: {exc}") from exc
    fields = parse_result(solver_stdout, leaf["mode"])
    require_equal(fields["status"], expected_status, "solver RESULT status")
    require_equal(marker.get("solver_exit_code"), expected_exit,
                  "marker solver exit")
    require_equal(marker.get("solver_result"), fields,
                  "marker solver RESULT")
    if int(fields["frontier"]) != 0:
        raise ValidationError("terminal evidence has nonzero frontier")

    checker_wall: Optional[float] = None
    witness_hash: Optional[str] = None
    if outcome == "ZERO":
        if int(fields["solution_topologies"]) != 0:
            raise ValidationError("ZERO has nonzero solution_topologies")
        if witness.exists() or witness.is_symlink():
            raise ValidationError("ZERO leaf unexpectedly contains a witness")
    else:
        if int(fields["solution_topologies"]) < 1:
            raise ValidationError("FOUND has no solution topology")
        if not witness.is_file() or witness.is_symlink():
            raise ValidationError("FOUND witness is not a regular file")
        checker_timing, _ = validate_process_metadata(directory, "checker", 0)
        checker_wall = float(checker_timing["wall_seconds"])
        if (directory / "checker.stderr.txt").stat().st_size != 0:
            raise ValidationError("worker checker stderr is nonempty")
        expected_checker = canonical_checker_output(leaf)
        checker_stdout = (directory / "checker.stdout.txt").read_text(
            encoding="utf-8", errors="strict")
        require_equal(checker_stdout, expected_checker,
                      "worker checker canonical output")
        checker = Path(bindings["checker_executable"]["absolute_path"])
        rerun_checker(checker, witness, workspace, expected_checker)
        witness_hash = sha256_file(witness)
        require_equal(witness_hash, files[WITNESS_NAME],
                      "witness hash after checker rerun")
        require_equal(sha256_file(checker),
                      bindings["checker_executable"]["sha256"],
                      "checker executable hash after rerun")

    require_equal(verify_bound_artifacts(leaf, workspace), bindings,
                  "bound artifacts after collection")
    require_equal(verify_pipeline_artifacts(plan, workspace),
                  pipeline_bindings,
                  "pipeline artifacts after collection")

    return {
        "schema": EVIDENCE_SCHEMA,
        "plan_id": plan["plan_id"],
        "plan_sha256": plan_hash,
        "leaf_index": index,
        "leaf_id": leaf["leaf_id"],
        "leaf_sha256": canonical_sha256(leaf),
        "configuration": leaf["configuration"],
        "mode": leaf["mode"],
        "selector": leaf["selector"],
        "selector_text": selector_text(leaf["selector"]),
        "outcome": outcome,
        "solver_exit_code": expected_exit,
        "solver_result": fields,
        "solver_wall_seconds": float(solver_timing["wall_seconds"]),
        "checker_wall_seconds": checker_wall,
        "witness_sha256": witness_hash,
        "argv": argv,
        "argv_sha256": canonical_sha256(argv),
        "cover_candidate_validation_enabled":
            "--multi-edge-cover-validate" in leaf["argv_template"],
        "bound_hashes": marker["bound_hashes"],
        "marker_file": marker_path.name,
        "marker_sha256": sha256_file(marker_path),
        "artifact_hashes": files,
    }


class UsageArgumentParser(argparse.ArgumentParser):
    def error(self, message: str) -> None:
        self.print_usage(sys.stderr)
        self.exit(USAGE_EXIT, f"{self.prog}: error: {message}\n")


def build_parser() -> argparse.ArgumentParser:
    parser = UsageArgumentParser(
        description="Strictly collect durable remaining-G001 leaf evidence")
    parser.add_argument("--plan", required=True, type=Path)
    parser.add_argument("--workspace", required=True, type=Path)
    parser.add_argument("--run-dir", required=True, type=Path)
    selection = parser.add_mutually_exclusive_group(required=True)
    selection.add_argument("--index", type=int)
    selection.add_argument("--all", action="store_true")
    parser.add_argument("--output", type=Path,
                        help="atomically create this JSON file; never append")
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        plan, plan_hash = load_plan(args.plan)
        workspace = args.workspace.resolve(strict=True)
        run_directory = args.run_dir.resolve(strict=True)
        pipeline_bindings = verify_pipeline_artifacts(plan, workspace)
        verify_executing_pipeline(
            pipeline_bindings,
            {
                "leaf_collector": Path(__file__),
                "leaf_common": Path(leaf_common_module.__file__),
            },
        )
        indices = range(len(plan["leaves"])) if args.all else [args.index]
        records = [
            collect_leaf(
                plan, plan_hash, workspace, run_directory, int(index),
                pipeline_bindings)
            for index in indices
        ]
        if args.all:
            document: Any = {
                "schema": COLLECTION_SCHEMA,
                "plan_id": plan["plan_id"],
                "plan_sha256": plan_hash,
                "records": records,
            }
        else:
            document = records[0]
        data = canonical_json_bytes(document)
        if args.output is not None:
            atomic_write_new(args.output.resolve(strict=False), data)
            print("G001_REMAINING_COLLECTION_WRITTEN " + str(args.output))
        else:
            sys.stdout.buffer.write(data)
        return 2 if any(record["outcome"] == "VERIFIED_FOUND"
                        for record in records) else 0
    except NoEvidence as exc:
        print("NO_EVIDENCE " + str(exc), file=sys.stderr)
        return NO_EVIDENCE_EXIT
    except ValidationError as exc:
        print("INVALID_EVIDENCE " + str(exc), file=sys.stderr)
        return 1
    except OSError as exc:
        print("IO_ERROR " + str(exc), file=sys.stderr)
        return 74


if __name__ == "__main__":
    sys.exit(main())
