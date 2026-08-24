# Fresh C157 calibration reconstruction

`../recompute_c157_full.py` rebuilds the authoritative shallow solver and
regenerates the complete Configurations 1, 5, 6, and 7 depth-12 calibration
partition used by the terminal-five search.  It does not read a preserved
C157 result archive.

From the repository root:

```bash
python3 -B scripts/recompute_c157_full.py --preflight
python3 -B scripts/recompute_c157_full.py --list-only
python3 -B scripts/recompute_c157_full.py --run \
  --work-dir /absolute/path/to/new-c157-run --workers 15
```

The source requires GCC-compatible `bits/stdc++.h`.  If `g++` on `PATH` is
not GNU GCC, pass it explicitly, for example
`--compiler /absolute/path/to/g++`.  The historical compiler was GCC 12.2.0;
the runner records the actual compiler and rebuilt executable hash.

Interrupted runs are resumed explicitly:

```bash
python3 -B scripts/recompute_c157_full.py --run \
  --work-dir /absolute/path/to/c157-run --workers 15 --resume
```

No task timeout is imposed by default.  If `--task-timeout-seconds` is used,
a timeout is an error and cannot become a zero or coverage result.

Successful completion writes:

```text
WORKLOAD.json
RESULTS_MANIFEST.sha256
C157_RECOMPUTATION.json
build/
preflight/
tasks/
```

Audit a completed directory without executing the solver:

```bash
python3 -B scripts/recompute_c157_full.py --verify-run \
  --work-dir /absolute/path/to/c157-run
```

This check requires the exact canonical workload, bound build and preflight
records, and all 80,142 expected task triplets.  It reparses every preserved
stdout file and rechecks the gate fanout and leaf-frontier invariants; missing,
extra, altered, failed, or timed-out task evidence is rejected.

The final status is `C157_FRESH_RECOMPUTATION_COMPLETE`.  This calibration
stage regenerates the partition and its depth-12 frontier weights.  It is not
the subsequent terminal nonexistence search.  Of the 37,706 frozen partition
paths, 813 legitimately have expected depth-12 frontier zero.  They remain
search records: the immediate fanout check establishes that each selector is
reachable, and the depth-12 run freshly confirms that its continuation dies.
The separate 464 omitted children are freshly rerun and must report immediate
frontier zero.

The current terminal-five runner uses the same frozen terminal plan rather
than ingesting `C157_RECOMPUTATION.json`; the top-level fresh-reproduction
assembler must require this completed summary before accepting the terminal
run.
