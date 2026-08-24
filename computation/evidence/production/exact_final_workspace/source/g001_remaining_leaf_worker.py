#!/usr/bin/env python3
"""Run one immutable remaining-G001 terminal leaf on Linux/Slurm."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import resource
import signal
import socket
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Dict, List, Mapping, Optional, Sequence

import g001_remaining_leaf_common as leaf_common_module
from g001_remaining_leaf_common import (
    EXIT_SCHEMA,
    FOUND_MARKER_SCHEMA,
    IO_EXIT,
    LAUNCH_SCHEMA,
    NO_EVIDENCE_EXIT,
    NO_EVIDENCE_SCHEMA,
    TIMING_SCHEMA,
    USAGE_EXIT,
    ValidationError,
    ZERO_MARKER_SCHEMA,
    atomic_write_json_new,
    bound_hash_document,
    canonical_sha256,
    fsync_directory,
    load_plan,
    parse_result,
    resolved_solver_argv,
    selector_text,
    sha256_file,
    utc_now,
    verify_bound_artifacts,
    verify_executing_pipeline,
    verify_pipeline_artifacts,
)


CHECKER_TIMEOUT_SECONDS = 60
WITNESS_NAME = "witness.LEECH_WITNESS_V1.txt"


class SignalState:
    def __init__(self) -> None:
        self.process: Optional[subprocess.Popen[bytes]] = None
        self.received: Optional[int] = None

    def handler(self, signum: int, _frame: Any) -> None:
        self.received = signum
        process = self.process
        if process is not None and process.poll() is None:
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass


SIGNALS = SignalState()


def install_signal_handlers() -> None:
    for name in ("SIGTERM", "SIGINT", "SIGHUP"):
        signum = getattr(signal, name, None)
        if signum is not None:
            signal.signal(signum, SIGNALS.handler)


def publish_temporary(temporary: Path, final: Path) -> None:
    if final.exists() or final.is_symlink():
        raise FileExistsError(f"refusing to overwrite {final}")
    os.link(temporary, final)
    fsync_directory(final.parent)
    temporary.unlink()
    fsync_directory(final.parent)


def terminate_process_group(process: subprocess.Popen[bytes],
                            grace_seconds: int) -> None:
    if process.poll() is not None:
        return
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        return
    try:
        process.wait(timeout=grace_seconds)
        return
    except subprocess.TimeoutExpired:
        pass
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        return
    process.wait()


def resource_snapshot() -> resource.struct_rusage:
    return resource.getrusage(resource.RUSAGE_CHILDREN)


def run_process(argv: Sequence[str], workspace: Path, directory: Path,
                stem: str, timeout_seconds: int,
                kill_grace_seconds: int) -> Dict[str, Any]:
    stdout_temporary = directory / (stem + ".stdout.txt.partial")
    stderr_temporary = directory / (stem + ".stderr.txt.partial")
    stdout_final = directory / (stem + ".stdout.txt")
    stderr_final = directory / (stem + ".stderr.txt")
    started_utc = utc_now()
    started = time.monotonic()
    before = resource_snapshot()
    process: Optional[subprocess.Popen[bytes]] = None
    timed_out = False
    launch_error: Optional[str] = None
    exit_code: Optional[int] = None

    try:
        with stdout_temporary.open("xb", buffering=0) as stdout_stream, \
                stderr_temporary.open("xb", buffering=0) as stderr_stream:
            try:
                if SIGNALS.received is not None:
                    raise OSError(
                        "external signal received before process launch")
                environment = os.environ.copy()
                environment["LC_ALL"] = "C"
                environment["TZ"] = "UTC"
                process = subprocess.Popen(
                    list(argv),
                    cwd=str(workspace),
                    env=environment,
                    stdin=subprocess.DEVNULL,
                    stdout=stdout_stream,
                    stderr=stderr_stream,
                    start_new_session=True,
                )
                SIGNALS.process = process
                deadline = (None if timeout_seconds == 0 else
                            started + timeout_seconds)
                while True:
                    if SIGNALS.received is not None:
                        terminate_process_group(process, kill_grace_seconds)
                        exit_code = process.returncode
                        break
                    remaining = (None if deadline is None else
                                 deadline - time.monotonic())
                    if remaining is not None and remaining <= 0:
                        timed_out = True
                        terminate_process_group(process, kill_grace_seconds)
                        exit_code = process.returncode
                        break
                    interval = 1.0 if remaining is None else min(1.0, remaining)
                    try:
                        exit_code = process.wait(timeout=interval)
                        break
                    except subprocess.TimeoutExpired:
                        continue
            except OSError as exc:
                launch_error = f"process launch failed: {exc}"
            finally:
                SIGNALS.process = None
            os.fsync(stdout_stream.fileno())
            os.fsync(stderr_stream.fileno())
        publish_temporary(stdout_temporary, stdout_final)
        publish_temporary(stderr_temporary, stderr_final)
    except Exception:
        for path in (stdout_temporary, stderr_temporary):
            try:
                path.unlink()
            except FileNotFoundError:
                pass
        raise

    after = resource_snapshot()
    ended = time.monotonic()
    return {
        "argv": list(argv),
        "started_utc": started_utc,
        "ended_utc": utc_now(),
        "wall_seconds": ended - started,
        "user_seconds": after.ru_utime - before.ru_utime,
        "system_seconds": after.ru_stime - before.ru_stime,
        "max_rss_kb": after.ru_maxrss,
        "timeout_seconds": timeout_seconds,
        "timed_out": timed_out,
        "interrupted_signal": SIGNALS.received,
        "launch_error": launch_error,
        "exit_code": exit_code,
        "stdout_name": stdout_final.name,
        "stderr_name": stderr_final.name,
    }


def timing_document(process_name: str, run: Mapping[str, Any]) -> Dict[str, Any]:
    return {
        "schema": TIMING_SCHEMA,
        "process": process_name,
        "started_utc": run["started_utc"],
        "ended_utc": run["ended_utc"],
        "wall_seconds": run["wall_seconds"],
        "user_seconds": run["user_seconds"],
        "system_seconds": run["system_seconds"],
        "max_rss_kb": run["max_rss_kb"],
        "timeout_seconds": run["timeout_seconds"],
    }


def exit_document(process_name: str, run: Mapping[str, Any]) -> Dict[str, Any]:
    return {
        "schema": EXIT_SCHEMA,
        "process": process_name,
        "exit_code": run["exit_code"],
        "timed_out": run["timed_out"],
        "interrupted_signal": run["interrupted_signal"],
        "launch_error": run["launch_error"],
    }


def artifact_hashes(directory: Path, names: Sequence[str]) -> Dict[str, str]:
    return {name: sha256_file(directory / name) for name in names}


def marker_base(plan: Mapping[str, Any], plan_hash: str, leaf: Mapping[str, Any],
                index: int, argv: Sequence[str], bindings: Mapping[str, Any],
                pipeline_bindings: Mapping[str, Any],
                files: Mapping[str, str]) -> Dict[str, Any]:
    return {
        "created_utc": utc_now(),
        "plan_id": plan["plan_id"],
        "plan_sha256": plan_hash,
        "leaf_index": index,
        "leaf_id": leaf["leaf_id"],
        "leaf_sha256": canonical_sha256(leaf),
        "configuration": leaf["configuration"],
        "mode": leaf["mode"],
        "selector": leaf["selector"],
        "selector_text": selector_text(leaf["selector"]),
        "argv_sha256": canonical_sha256(list(argv)),
        "cover_candidate_validation_enabled":
            "--multi-edge-cover-validate" in leaf["argv_template"],
        "bound_hashes": bound_hash_document(bindings, pipeline_bindings),
        "files": dict(files),
    }


def clean_solver_result(run: Mapping[str, Any], leaf: Mapping[str, Any],
                        directory: Path, witness_path: Path) -> Dict[str, str]:
    if run["timed_out"]:
        raise ValidationError("solver timed out")
    if run["interrupted_signal"] is not None:
        raise ValidationError("worker received an external signal")
    if run["launch_error"] is not None:
        raise ValidationError(run["launch_error"])
    stderr_path = directory / run["stderr_name"]
    if stderr_path.stat().st_size != 0:
        raise ValidationError("solver stderr is nonempty")
    try:
        stdout_text = (directory / run["stdout_name"]).read_text(
            encoding="utf-8", errors="strict")
    except (OSError, UnicodeDecodeError) as exc:
        raise ValidationError(f"solver stdout is not strict UTF-8: {exc}") from exc
    fields = parse_result(stdout_text, leaf["mode"])
    if run["exit_code"] == 0:
        if fields["status"] != "ZERO" or \
                int(fields["solution_topologies"]) != 0 or \
                int(fields["frontier"]) != 0:
            raise ValidationError("exit 0 is not a clean terminal ZERO")
        if witness_path.exists() or witness_path.is_symlink():
            raise ValidationError("ZERO job unexpectedly created a witness")
        return fields
    if run["exit_code"] == 2:
        if fields["status"] != "FOUND" or \
                int(fields["solution_topologies"]) < 1 or \
                int(fields["frontier"]) != 0:
            raise ValidationError("exit 2 is not a clean terminal FOUND")
        if not witness_path.is_file() or witness_path.is_symlink():
            raise ValidationError("FOUND job lacks a regular witness file")
        witness_lines = [line for line in stdout_text.splitlines()
                         if line.startswith("WITNESS ")]
        expected_prefix = (
            "WITNESS format=LEECH_WITNESS_V1 configuration=" +
            str(leaf["configuration"]) + " ")
        if len(witness_lines) != 1 or not witness_lines[0].startswith(
                expected_prefix):
            raise ValidationError("FOUND stdout lacks the expected WITNESS line")
        return fields
    raise ValidationError(f"solver exit {run['exit_code']} is not evidence")


def run_leaf(plan_path: Path, workspace: Path, run_directory: Path, index: int,
             dry_run: bool, kill_grace_seconds: int) -> int:
    plan, plan_hash = load_plan(plan_path)
    if index < 0 or index >= len(plan["leaves"]):
        raise ValidationError(f"leaf index {index} is outside the plan")
    leaf = plan["leaves"][index]
    workspace = workspace.resolve(strict=True)
    run_directory = run_directory.resolve(strict=True)
    if not run_directory.is_dir():
        raise ValidationError("run directory must already exist")
    bindings = verify_bound_artifacts(leaf, workspace)
    pipeline_bindings = verify_pipeline_artifacts(plan, workspace)
    verify_executing_pipeline(
        pipeline_bindings,
        {
            "leaf_worker": Path(__file__),
            "leaf_common": Path(leaf_common_module.__file__),
        },
    )
    leaf_directory = run_directory / leaf["leaf_id"]
    witness_path = leaf_directory / WITNESS_NAME
    argv = resolved_solver_argv(leaf, bindings, witness_path)
    if leaf_directory.exists() or leaf_directory.is_symlink():
        raise ValidationError(
            "leaf directory already exists; use a fresh run directory")

    preview = {
        "schema": "G001_REMAINING_LEAF_DRY_RUN_V1",
        "plan_id": plan["plan_id"],
        "plan_sha256": plan_hash,
        "leaf_index": index,
        "leaf_id": leaf["leaf_id"],
        "leaf_sha256": canonical_sha256(leaf),
        "configuration": leaf["configuration"],
        "mode": leaf["mode"],
        "selector": leaf["selector"],
        "selector_text": selector_text(leaf["selector"]),
        "leaf_directory": str(leaf_directory),
        "witness_file": str(witness_path),
        "argv": argv,
        "argv_sha256": canonical_sha256(argv),
        "bound_hashes": bound_hash_document(bindings, pipeline_bindings),
    }
    if dry_run:
        print(json.dumps(preview, sort_keys=True, separators=(",", ":")))
        return 0

    if os.name != "posix":
        raise ValidationError("leaf execution is supported only on POSIX/Linux")
    os.mkdir(leaf_directory, 0o700)
    fsync_directory(run_directory)

    launch = dict(preview)
    launch["schema"] = LAUNCH_SCHEMA
    launch["created_utc"] = utc_now()
    launch["hostname"] = socket.gethostname()
    launch["pid"] = os.getpid()
    launch["slurm"] = {
        name: os.environ.get(name)
        for name in (
            "SLURM_JOB_ID", "SLURM_ARRAY_JOB_ID", "SLURM_ARRAY_TASK_ID",
            "SLURM_CPUS_PER_TASK", "SLURM_JOB_NODELIST",
        )
    }
    launch["bindings"] = bindings
    launch["pipeline_bindings"] = pipeline_bindings
    launch["executing_pipeline"] = {
        role: pipeline_bindings[role]
        for role in ("leaf_worker", "leaf_common")
    }
    atomic_write_json_new(leaf_directory / "launch.json", launch)

    solver_run = run_process(
        argv, workspace, leaf_directory, "solver", leaf["timeout_seconds"],
        kill_grace_seconds)
    atomic_write_json_new(leaf_directory / "solver.timing.json",
                          timing_document("solver", solver_run))
    atomic_write_json_new(leaf_directory / "solver.exit.json",
                          exit_document("solver", solver_run))

    evidence_names = [
        "launch.json", "solver.stdout.txt", "solver.stderr.txt",
        "solver.timing.json", "solver.exit.json",
    ]
    outcome = "NO_EVIDENCE"
    reason = "unclassified solver result"
    fields: Optional[Dict[str, str]] = None
    try:
        fields = clean_solver_result(solver_run, leaf, leaf_directory,
                                     witness_path)
        if solver_run["exit_code"] == 0:
            outcome = "ZERO"
            reason = "clean terminal ZERO"
        else:
            checker_argv = [
                bindings["checker_executable"]["absolute_path"],
                str(witness_path),
            ]
            checker_run = run_process(
                checker_argv, workspace, leaf_directory, "checker",
                CHECKER_TIMEOUT_SECONDS, kill_grace_seconds)
            atomic_write_json_new(leaf_directory / "checker.timing.json",
                                  timing_document("checker", checker_run))
            atomic_write_json_new(leaf_directory / "checker.exit.json",
                                  exit_document("checker", checker_run))
            evidence_names.extend([
                WITNESS_NAME, "checker.stdout.txt", "checker.stderr.txt",
                "checker.timing.json", "checker.exit.json",
            ])
            if checker_run["timed_out"] or \
                    checker_run["interrupted_signal"] is not None or \
                    checker_run["launch_error"] is not None or \
                    checker_run["exit_code"] != 0:
                raise ValidationError("independent checker did not exit cleanly")
            if (leaf_directory / "checker.stderr.txt").stat().st_size != 0:
                raise ValidationError("independent checker stderr is nonempty")
            checker_stdout = (leaf_directory / "checker.stdout.txt").read_text(
                encoding="utf-8", errors="strict")
            expected = (
                "VALID LEECH_WITNESS_V1 configuration=" +
                str(leaf["configuration"]) + " mode=" + leaf["mode"] +
                " vertices=18 edges=17 distances=1..153\n")
            if checker_stdout != expected:
                raise ValidationError("independent checker output is not canonical")
            outcome = "VERIFIED_FOUND"
            reason = "FOUND witness passed the independent checker"
        post_run_bindings = verify_bound_artifacts(leaf, workspace)
        if post_run_bindings != bindings:
            raise ValidationError("bound artifacts changed during the leaf run")
        post_run_pipeline = verify_pipeline_artifacts(plan, workspace)
        if post_run_pipeline != pipeline_bindings:
            raise ValidationError(
                "bound pipeline artifacts changed during the leaf run")
    except (ValidationError, OSError, UnicodeDecodeError) as exc:
        outcome = "NO_EVIDENCE"
        reason = str(exc)

    files = artifact_hashes(leaf_directory, evidence_names)
    marker = marker_base(
        plan, plan_hash, leaf, index, argv, bindings, pipeline_bindings, files)
    marker["solver_exit_code"] = solver_run["exit_code"]
    marker["solver_result"] = fields
    marker["reason"] = reason
    if outcome == "ZERO":
        marker["schema"] = ZERO_MARKER_SCHEMA
        marker["outcome"] = "ZERO"
        atomic_write_json_new(leaf_directory / "ZERO_COMPLETE_V1.json", marker)
        print("G001_REMAINING_LEAF_ZERO_COMPLETE " + leaf["leaf_id"])
        return 0
    if outcome == "VERIFIED_FOUND":
        marker["schema"] = FOUND_MARKER_SCHEMA
        marker["outcome"] = "VERIFIED_FOUND"
        atomic_write_json_new(
            leaf_directory / "VERIFIED_FOUND_V1.json", marker)
        print("G001_REMAINING_LEAF_VERIFIED_FOUND " + leaf["leaf_id"])
        return 2

    marker["schema"] = NO_EVIDENCE_SCHEMA
    marker["outcome"] = "NO_EVIDENCE"
    atomic_write_json_new(leaf_directory / "NO_EVIDENCE_V1.json", marker)
    print("G001_REMAINING_LEAF_NO_EVIDENCE " + leaf["leaf_id"] +
          " reason=" + reason, file=sys.stderr)
    return NO_EVIDENCE_EXIT


def parse_index(text: Optional[str]) -> int:
    if text is None:
        text = os.environ.get("SLURM_ARRAY_TASK_ID")
    if text is None or not text.isdigit():
        raise ValidationError(
            "--index or nonnegative SLURM_ARRAY_TASK_ID is required")
    return int(text)


class UsageArgumentParser(argparse.ArgumentParser):
    def error(self, message: str) -> None:
        self.print_usage(sys.stderr)
        self.exit(USAGE_EXIT, f"{self.prog}: error: {message}\n")


def build_parser() -> argparse.ArgumentParser:
    parser = UsageArgumentParser(
        description="Run one full, uncapped remaining-G001 plan leaf")
    parser.add_argument("--plan", required=True, type=Path)
    parser.add_argument("--workspace", required=True, type=Path)
    parser.add_argument("--run-dir", required=True, type=Path)
    parser.add_argument("--index")
    parser.add_argument("--kill-grace-seconds", type=int, default=30)
    parser.add_argument("--dry-run", action="store_true")
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    if args.kill_grace_seconds < 1 or args.kill_grace_seconds > 600:
        print("ERROR kill grace must be in 1..600", file=sys.stderr)
        return USAGE_EXIT
    try:
        index = parse_index(args.index)
        install_signal_handlers()
        return run_leaf(
            args.plan, args.workspace, args.run_dir, index, args.dry_run,
            args.kill_grace_seconds)
    except ValidationError as exc:
        print("VALIDATION_ERROR " + str(exc), file=sys.stderr)
        return USAGE_EXIT
    except (OSError, FileExistsError) as exc:
        print("IO_ERROR " + str(exc), file=sys.stderr)
        return IO_EXIT


if __name__ == "__main__":
    sys.exit(main())
