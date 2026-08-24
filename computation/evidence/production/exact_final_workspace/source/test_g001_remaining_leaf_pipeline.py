#!/usr/bin/env python3
"""Linux end-to-end self-tests for the generic leaf worker and collector."""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence

from g001_remaining_leaf_common import ValidationError, parse_result


SCRIPT_DIRECTORY = Path(__file__).resolve().parent
WORKER = SCRIPT_DIRECTORY / "g001_remaining_leaf_worker.py"
COMMON = SCRIPT_DIRECTORY / "g001_remaining_leaf_common.py"
COLLECTOR = SCRIPT_DIRECTORY / "g001_remaining_leaf_collect.py"
WRAPPER = SCRIPT_DIRECTORY / "g001_remaining_leaf_array.sbatch"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_file(path: Path, text: str, executable: bool = False) -> None:
    with path.open("w", encoding="utf-8", newline="\n") as stream:
        stream.write(text)
    if executable:
        path.chmod(0o755)


def run(command: Sequence[str], expected: int,
        environment: Optional[Dict[str, str]] = None
        ) -> subprocess.CompletedProcess[bytes]:
    completed = subprocess.run(
        list(command), stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
        env=environment)
    if completed.returncode != expected:
        raise RuntimeError(
            f"unexpected exit {completed.returncode}, expected {expected}: "
            f"{command!r}\nstdout={completed.stdout!r}\nstderr={completed.stderr!r}")
    return completed


def install_pipeline(workspace: Path) -> Dict[str, Any]:
    for source in (WORKER, COMMON, COLLECTOR, WRAPPER):
        target = workspace / source.name
        shutil.copy2(str(source), str(target))
        # copy2 preserves a read-only source mode.  These are mutable test
        # fixtures, so make only the temporary copy owner-writable; the
        # authoritative staged source remains immutable.
        target.chmod(target.stat().st_mode | stat.S_IWUSR)
    return {
        "leaf_worker": {
            "path": WORKER.name,
            "sha256": sha256(workspace / WORKER.name),
        },
        "leaf_common": {
            "path": COMMON.name,
            "sha256": sha256(workspace / COMMON.name),
        },
        "leaf_collector": {
            "path": COLLECTOR.name,
            "sha256": sha256(workspace / COLLECTOR.name),
        },
    }


def make_artifacts(workspace: Path, outcome: str) -> Dict[str, Any]:
    source = workspace / f"solver_{outcome}.cpp"
    checker_source = workspace / f"checker_{outcome}.cpp"
    solver = workspace / f"solver_{outcome}.sh"
    checker = workspace / f"checker_{outcome}.sh"
    write_file(source, "// fake solver source for pipeline test\n")
    write_file(checker_source, "// fake checker source for pipeline test\n")

    common_result = (
        "nodes=10 states=9 generated=8 duplicate=0 collision=0 range=0 "
        "parity=0 diameter=0 solution_topologies={solutions} depth= "
        "root_valid=1 frontier=0 frontier_mex= frontier_odd= frontier_q3= "
        "multi_cover=on cover_validation_fail=0 child_max=\n"
    )
    if outcome == "zero":
        body = (
            "echo \"RESULT mode=g001_row0 configuration=1 status=ZERO " +
            common_result.format(solutions=0).rstrip("\n") + "\"\n"
            "exit 0\n"
        )
    elif outcome in ("found", "badchecker"):
        body = (
            "witness=''\n"
            "while [ \"$#\" -gt 0 ]; do\n"
            "  if [ \"$1\" = '--witness-file' ]; then witness=$2; shift 2; else shift; fi\n"
            "done\n"
            "printf '%s\\n' LEECH_WITNESS_V1 configuration 1 > \"${witness}.tmp\"\n"
            "mv -- \"${witness}.tmp\" \"${witness}\"\n"
            "echo \"RESULT mode=g001_row0 configuration=1 status=FOUND " +
            common_result.format(solutions=1).rstrip("\n") + "\"\n"
            "echo \"WITNESS format=LEECH_WITNESS_V1 configuration=1 file=\\\"${witness}\\\"\"\n"
            "exit 2\n"
        )
    elif outcome == "timeout":
        body = "sleep 5\nexit 0\n"
    elif outcome == "ignoreterm":
        body = (
            "trap '' TERM\n"
            "witness=''\n"
            "while [ \"$#\" -gt 0 ]; do\n"
            "  if [ \"$1\" = '--witness-file' ]; then witness=$2; shift 2; else shift; fi\n"
            "done\n"
            ": > \"${witness}.ready\"\n"
            "while :; do sleep 1; done\n"
        )
    else:
        raise ValueError(outcome)
    write_file(solver, "#!/usr/bin/env bash\nset -euo pipefail\n" + body,
               executable=True)
    checker_body = (
        "#!/usr/bin/env bash\n"
        "set -euo pipefail\n"
        "grep -q '^LEECH_WITNESS_V1$' \"$1\"\n"
    )
    if outcome == "badchecker":
        checker_body += "echo 'checker deliberately rejected' >&2\nexit 1\n"
    else:
        checker_body += (
            "echo 'VALID LEECH_WITNESS_V1 configuration=1 mode=g001_row0 "
            "vertices=18 edges=17 distances=1..153'\n")
    write_file(checker, checker_body, executable=True)
    return {
        "solver_source": {"path": source.name, "sha256": sha256(source)},
        "solver_executable": {"path": solver.name, "sha256": sha256(solver)},
        "checker_source": {
            "path": checker_source.name, "sha256": sha256(checker_source)},
        "checker_executable": {
            "path": checker.name, "sha256": sha256(checker)},
        "dependencies": [],
    }


def write_plan(workspace: Path, outcome: str, timeout: int) -> Path:
    pipeline_artifacts = install_pipeline(workspace)
    artifacts = make_artifacts(workspace, outcome)
    plan = {
        "schema": "G001_REMAINING_LEAF_PLAN_V1",
        "plan_id": "pipeline_test_" + outcome,
        "pipeline_artifacts": pipeline_artifacts,
        "leaves": [{
            "leaf_id": "cfg1_root0_" + outcome,
            "configuration": 1,
            "mode": "g001_row0",
            "selector": {"kind": "root", "index": 0},
            "argv_template": [
                "--configuration", "1", "--root-branch", "0",
                "--witness-file", "{WITNESS_FILE}",
                "--multi-edge-cover",
                "--multi-edge-cover-validate",
            ],
            "timeout_seconds": timeout,
            "artifacts": artifacts,
        }],
    }
    path = workspace / ("plan_" + outcome + ".json")
    path.write_text(json.dumps(plan, indent=2) + "\n", encoding="utf-8")
    return path


def worker_command(plan: Path, workspace: Path, run_directory: Path,
                   dry_run: bool = False) -> List[str]:
    command = [
        sys.executable, str(workspace / WORKER.name), "--plan", str(plan),
        "--workspace", str(workspace), "--run-dir", str(run_directory),
        "--index", "0", "--kill-grace-seconds", "1",
    ]
    if dry_run:
        command.append("--dry-run")
    return command


def collector_command(plan: Path, workspace: Path,
                      run_directory: Path) -> List[str]:
    return [
        sys.executable, str(workspace / COLLECTOR.name), "--plan", str(plan),
        "--workspace", str(workspace), "--run-dir", str(run_directory),
        "--index", "0",
    ]


def wrapper_environment(plan: Path, workspace: Path,
                        run_directory: Path) -> Dict[str, str]:
    environment = os.environ.copy()
    environment.update({
        "G001_PLAN": str(plan),
        "G001_WORKSPACE": str(workspace),
        "G001_RUN_DIR": str(run_directory),
        "G001_PYTHON": sys.executable,
        "G001_KILL_GRACE_SECONDS": "1",
        "SLURM_ARRAY_TASK_ID": "0",
    })
    return environment


def main() -> int:
    if os.name != "posix":
        print("SKIP test_g001_remaining_leaf_pipeline: Linux/POSIX required")
        return 0
    checks = 0

    run([sys.executable, str(WORKER), "--definitely-invalid"], 64)
    run([sys.executable, str(COLLECTOR), "--definitely-invalid"], 64)
    checks += 2

    duplicate_result = (
        "RESULT mode=g001_row0 configuration=1 status=ZERO status=ZERO "
        "nodes=1 states=1 generated=1 solution_topologies=0 frontier=0 "
        "multi_cover=on cover_validation_fail=0\n")
    try:
        parse_result(duplicate_result, "g001_row0")
        raise AssertionError("duplicate RESULT field was accepted")
    except ValidationError as exc:
        assert "duplicate RESULT field" in str(exc)
    checks += 1

    with tempfile.TemporaryDirectory(prefix="g001-leaf-pipeline-test.") as name:
        root = Path(name)

        zero_workspace = root / "zero_workspace"
        zero_run = root / "zero_run"
        zero_workspace.mkdir()
        zero_run.mkdir()
        zero_plan = write_plan(zero_workspace, "zero", 10)
        dry = run(worker_command(zero_plan, zero_workspace, zero_run, True), 0)
        preview = json.loads(dry.stdout.decode("utf-8"))
        assert preview["schema"] == "G001_REMAINING_LEAF_DRY_RUN_V1"
        assert not any(zero_run.iterdir())
        checks += 2
        run(worker_command(zero_plan, zero_workspace, zero_run), 0)
        zero_collected = run(
            collector_command(zero_plan, zero_workspace, zero_run), 0)
        zero_record = json.loads(zero_collected.stdout.decode("utf-8"))
        assert zero_record["outcome"] == "ZERO"
        assert (zero_run / "cfg1_root0_zero" /
                "ZERO_COMPLETE_V1.json").is_file()
        checks += 2
        receipt = root / "zero_receipt.json"
        run(collector_command(zero_plan, zero_workspace, zero_run) +
            ["--output", str(receipt)], 0)
        assert receipt.is_file()
        run(collector_command(zero_plan, zero_workspace, zero_run) +
            ["--output", str(receipt)], 74)
        checks += 2
        run(worker_command(zero_plan, zero_workspace, zero_run), 64)
        checks += 1
        with (zero_run / "cfg1_root0_zero" /
              "solver.stdout.txt").open("ab") as stream:
            stream.write(b"tamper\n")
        run(collector_command(zero_plan, zero_workspace, zero_run), 1)
        checks += 1

        found_workspace = root / "found_workspace"
        found_run = root / "found_run"
        found_workspace.mkdir()
        found_run.mkdir()
        found_plan = write_plan(found_workspace, "found", 10)
        run(worker_command(found_plan, found_workspace, found_run), 2)
        found_collected = run(
            collector_command(found_plan, found_workspace, found_run), 2)
        found_record = json.loads(found_collected.stdout.decode("utf-8"))
        assert found_record["outcome"] == "VERIFIED_FOUND"
        assert found_record["witness_sha256"] is not None
        assert (found_run / "cfg1_root0_found" /
                "VERIFIED_FOUND_V1.json").is_file()
        checks += 3
        found_marker = (found_run / "cfg1_root0_found" /
                        "VERIFIED_FOUND_V1.json")
        marker_data = json.loads(found_marker.read_text(encoding="utf-8"))
        marker_data["configuration"] = 4
        found_marker.write_text(
            json.dumps(marker_data, sort_keys=True) + "\n", encoding="utf-8")
        run(collector_command(found_plan, found_workspace, found_run), 1)
        checks += 1

        wrapper_workspace = root / "wrapper_found_workspace"
        wrapper_run = root / "wrapper_found_run"
        wrapper_workspace.mkdir()
        wrapper_run.mkdir()
        wrapper_plan = write_plan(wrapper_workspace, "found", 10)
        wrapped = run(
            ["bash", str(wrapper_workspace / WRAPPER.name)], 0,
            wrapper_environment(wrapper_plan, wrapper_workspace, wrapper_run))
        assert b"G001_SLURM_LEAF_ACCEPTED_VERIFIED_FOUND" in wrapped.stdout
        run(collector_command(
            wrapper_plan, wrapper_workspace, wrapper_run), 2)
        checks += 2

        false_found_workspace = root / "false_found_workspace"
        false_found_run = root / "false_found_run"
        false_found_workspace.mkdir()
        false_found_run.mkdir()
        false_found_plan = write_plan(false_found_workspace, "zero", 10)
        write_file(
            false_found_workspace / WORKER.name,
            "#!/usr/bin/env python3\nimport sys\nsys.exit(2)\n")
        rejected = run(
            ["bash", str(false_found_workspace / WRAPPER.name)], 75,
            wrapper_environment(
                false_found_plan, false_found_workspace, false_found_run))
        assert b"ACCEPTED_VERIFIED_FOUND" not in rejected.stdout
        checks += 2

        timeout_workspace = root / "timeout_workspace"
        timeout_run = root / "timeout_run"
        timeout_workspace.mkdir()
        timeout_run.mkdir()
        timeout_plan = write_plan(timeout_workspace, "timeout", 1)
        run(worker_command(timeout_plan, timeout_workspace, timeout_run), 75)
        assert (timeout_run / "cfg1_root0_timeout" /
                "NO_EVIDENCE_V1.json").is_file()
        run(collector_command(timeout_plan, timeout_workspace, timeout_run), 75)
        checks += 2

        signal_workspace = root / "signal_workspace"
        signal_run = root / "signal_run"
        signal_workspace.mkdir()
        signal_run.mkdir()
        signal_plan = write_plan(signal_workspace, "ignoreterm", 0)
        process = subprocess.Popen(
            worker_command(signal_plan, signal_workspace, signal_run),
            stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE)
        try:
            ready = (signal_run / "cfg1_root0_ignoreterm" /
                     "witness.LEECH_WITNESS_V1.txt.ready")
            deadline = time.monotonic() + 5.0
            while not ready.is_file() and process.poll() is None and \
                    time.monotonic() < deadline:
                time.sleep(0.02)
            assert ready.is_file()
            process.send_signal(signal.SIGTERM)
            stdout, stderr = process.communicate(timeout=10)
            if process.returncode != 75:
                raise RuntimeError(
                    f"signal test exit={process.returncode} "
                    f"stdout={stdout!r} stderr={stderr!r}")
        finally:
            if process.poll() is None:
                process.kill()
                process.communicate()
        assert (signal_run / "cfg1_root0_ignoreterm" /
                "NO_EVIDENCE_V1.json").is_file()
        run(collector_command(
            signal_plan, signal_workspace, signal_run), 75)
        checks += 3

        bad_checker_workspace = root / "bad_checker_workspace"
        bad_checker_run = root / "bad_checker_run"
        bad_checker_workspace.mkdir()
        bad_checker_run.mkdir()
        bad_checker_plan = write_plan(
            bad_checker_workspace, "badchecker", 10)
        run(worker_command(
            bad_checker_plan, bad_checker_workspace, bad_checker_run), 75)
        assert (bad_checker_run / "cfg1_root0_badchecker" /
                "NO_EVIDENCE_V1.json").is_file()
        run(collector_command(
            bad_checker_plan, bad_checker_workspace, bad_checker_run), 75)
        checks += 3

        hash_workspace = root / "hash_workspace"
        hash_run = root / "hash_run"
        hash_workspace.mkdir()
        hash_run.mkdir()
        hash_plan = write_plan(hash_workspace, "zero", 10)
        with (hash_workspace / "solver_zero.cpp").open("a", encoding="utf-8") as stream:
            stream.write("// changed\n")
        run(worker_command(hash_plan, hash_workspace, hash_run, True), 64)
        assert not any(hash_run.iterdir())
        checks += 2

        pipeline_hash_workspace = root / "pipeline_hash_workspace"
        pipeline_hash_run = root / "pipeline_hash_run"
        pipeline_hash_workspace.mkdir()
        pipeline_hash_run.mkdir()
        pipeline_hash_plan = write_plan(
            pipeline_hash_workspace, "zero", 10)
        with (pipeline_hash_workspace / COMMON.name).open(
                "a", encoding="utf-8") as stream:
            stream.write("# changed\n")
        run(worker_command(
            pipeline_hash_plan, pipeline_hash_workspace,
            pipeline_hash_run, True), 64)
        assert not any(pipeline_hash_run.iterdir())
        checks += 2

        threshold_workspace = root / "threshold_workspace"
        threshold_run = root / "threshold_run"
        threshold_workspace.mkdir()
        threshold_run.mkdir()
        threshold_plan = write_plan(threshold_workspace, "zero", 10)
        threshold_data = json.loads(
            threshold_plan.read_text(encoding="utf-8"))
        threshold_data["leaves"][0]["argv_template"].extend([
            "--multi-edge-cover-max-components", "5"])
        threshold_plan.write_text(
            json.dumps(threshold_data, indent=2) + "\n", encoding="utf-8")
        run(worker_command(
            threshold_plan, threshold_workspace, threshold_run, True), 64)
        assert not any(threshold_run.iterdir())
        checks += 2

    print(f"PASS test_g001_remaining_leaf_pipeline checks={checks}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
