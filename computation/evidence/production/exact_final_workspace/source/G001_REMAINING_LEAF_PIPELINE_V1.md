# Remaining-G001 durable leaf pipeline, version 1

This pipeline runs and collects one **terminal search leaf** at a time. It does
not define the final leaf set and does not prove that a collection covers a
configuration. A separate fan-out and prefix-coverage verifier is still
required after the leaf plan is chosen.

## Files

- `g001_remaining_leaf_common.py`: strict plan schema and durability helpers.
- `g001_remaining_leaf_worker.py`: one Linux leaf worker.
- `g001_remaining_leaf_collect.py`: read-only strict evidence collector.
- `g001_remaining_leaf_array.sbatch`: generic Slurm-array entry point.
- `test_g001_remaining_leaf_pipeline.py`: isolated Linux end-to-end tests.

Python 3.8 or newer and a POSIX filesystem supporting hard links and directory
`fsync` are required. The solver and independent checker are separate compiled
executables.

## Plan contract

A plan has schema `G001_REMAINING_LEAF_PLAN_V1`, one safe `plan_id`, and a
nonempty `leaves` array. Its top-level `pipeline_artifacts` object binds the
exact relative paths and SHA-256 hashes of `leaf_worker`, `leaf_common`, and
`leaf_collector`. The worker and collector reject a plan unless their actual
source files and imported common module are those frozen files.

Every leaf binds:

- a unique `leaf_id`;
- one of configurations `1,4,5,6,7` and its exact internal mode;
- an `all`, `root`, or `path` selector;
- the exact solver argument template, including exactly one
  `--witness-file {WITNESS_FILE}`;
- a nonnegative process timeout, where zero means no worker timeout;
- SHA-256 bindings for solver source, solver executable, checker source, and
  checker executable; and
- zero or more additional dependency files with roles and SHA-256 hashes.

The validator rejects overlapping selectors within a configuration, duplicate
IDs, unknown arguments, `--max-nodes`, `--stop-edges`, shadow cover, mismatched
configuration/selector arguments, and a missing active
`--multi-edge-cover`.
It also resolves the solver's default cover thresholds and requires
`exact-max-components <= max-components`, so invalid partial overrides fail at
plan validation instead of after a job starts.
Rejecting overlaps does **not** prove exhaustive coverage.

A schematic plan envelope begins:

```json
{
  "schema": "G001_REMAINING_LEAF_PLAN_V1",
  "plan_id": "A_UNIQUE_FROZEN_PLAN_ID",
  "pipeline_artifacts": {
    "leaf_worker": {"path": "RELATIVE_WORKER_PATH", "sha256": "64_HEX_DIGITS"},
    "leaf_common": {"path": "RELATIVE_COMMON_PATH", "sha256": "64_HEX_DIGITS"},
    "leaf_collector": {"path": "RELATIVE_COLLECTOR_PATH", "sha256": "64_HEX_DIGITS"}
  },
  "leaves": ["LEAF_RECORDS_DESCRIBED_BELOW"]
}
```

A schematic leaf record is:

```json
{
  "leaf_id": "A_UNIQUE_CERTIFIED_LEAF_ID",
  "configuration": 1,
  "mode": "g001_row0",
  "selector": {"kind": "path", "indices": [0, 0]},
  "argv_template": [
    "--configuration", "1",
    "--branch-path", "0,0",
    "--witness-file", "{WITNESS_FILE}",
    "--multi-edge-cover",
    "--multi-edge-cover-validate",
    "--multi-edge-cover-no-hall",
    "--multi-edge-cover-max-components", "6",
    "--multi-edge-cover-budget", "100",
    "--multi-edge-cover-no-exact-hall"
  ],
  "timeout_seconds": 0,
  "artifacts": {
    "solver_source": {"path": "RELATIVE_PATH", "sha256": "64_HEX_DIGITS"},
    "solver_executable": {"path": "RELATIVE_PATH", "sha256": "64_HEX_DIGITS"},
    "checker_source": {"path": "RELATIVE_PATH", "sha256": "64_HEX_DIGITS"},
    "checker_executable": {"path": "RELATIVE_PATH", "sha256": "64_HEX_DIGITS"},
    "dependencies": [
      {"role": "frozen_solver", "path": "RELATIVE_PATH", "sha256": "64_HEX_DIGITS"}
    ]
  }
}
```

The indices above illustrate syntax only. They are not a proposed census leaf.

## Dry run

Create a fresh run directory, then validate a plan entry and every bound hash
without creating a leaf directory or starting the solver:

```bash
python3 work/a2_solver/g001_remaining_leaf_worker.py \
  --plan /absolute/path/frozen-plan.json \
  --workspace /absolute/path/workspace \
  --run-dir /absolute/path/fresh-run \
  --index 0 \
  --dry-run
```

The emitted JSON contains the resolved unique witness path and exact argv hash.

## Slurm array

The plan determines the array length; the wrapper deliberately contains no
invented array bounds or resource request. After benchmarking and freezing a
real plan, submit with appropriate site-specific CPU, memory, and wall time:

```bash
sbatch --array=0-LAST_INDEX \
  --export=ALL,G001_PLAN=/absolute/path/frozen-plan.json,G001_WORKSPACE=/absolute/path/workspace,G001_RUN_DIR=/absolute/path/fresh-run \
  work/a2_solver/g001_remaining_leaf_array.sbatch
```

Each array element creates exactly one new leaf directory. Reusing an existing
leaf directory is rejected. The wrapper maps a verified solver `FOUND` exit 2
to Slurm success because `FOUND` is a successful safety event, not a failed
computation. Slurm `TERM`, `INT`, and `HUP` signals are forwarded to the worker;
the worker then terminates the solver process group and records no evidence.

## Durable outcomes

The worker publishes stdout, stderr, timing, and exit metadata atomically after
the child process stops. A terminal marker is written last:

- `ZERO_COMPLETE_V1.json`: clean solver exit 0, one terminal `ZERO` result,
  empty stderr, no witness, zero frontier, active cover, and a zero validation
  failure counter.
- `VERIFIED_FOUND_V1.json`: clean solver exit 2, one terminal `FOUND` result,
  a durable witness, and immediate clean exit 0 from the independently hashed
  checker with canonical validation output.
- `NO_EVIDENCE_V1.json`: timeout, signal, I/O failure, malformed output,
  checker failure, or any other incomplete state.

A hard kill can occur before any marker is written. Absence of an accepted
marker is also no evidence.

The marker and collection record explicitly state whether
`--multi-edge-cover-validate` was enabled. That option cross-checks optimized
candidate materialization where the full cover path exercises it; it is not an
independent validation of every local/full pruning path. With or without the
flag, a ZERO trusts the frozen cover implementation and its separate audits.
Because the completed benchmarks did not enable this extra cross-check, run a
paired validation-on/off benchmark before deciding whether to require it in a
large census plan.

The command-line front ends reserve exit `2` exclusively for an accepted
`FOUND`; malformed invocations exit `64`. The Slurm wrapper does not trust a
bare worker exit code: it runs the strict collector and accepts the leaf only
when the collector independently confirms the matching durable outcome.

## Strict collection

Collect one leaf without changing the run directory:

```bash
python3 work/a2_solver/g001_remaining_leaf_collect.py \
  --plan /absolute/path/frozen-plan.json \
  --workspace /absolute/path/workspace \
  --run-dir /absolute/path/fresh-run \
  --index 0
```

Use `--all` only when every plan entry is expected to be complete. The
collector re-hashes the plan, sources, executables, dependencies, all three
pipeline sources, the launch record, and every evidence file; reconstructs the
exact argv; checks the raw solver result; and reruns the independent checker
for `FOUND`. It emits a canonical JSON evidence record. `--output NEW_FILE`
creates a new file atomically and refuses to append or overwrite.

Collector/worker outcome codes are:

- `0`: accepted `ZERO` evidence;
- `2`: accepted independently verified `FOUND` evidence;
- `75`: no evidence, including timeout or partial state;
- `1`: present but invalid/tampered evidence;
- `64`: invalid plan or invocation; and
- `74`: worker/collector I/O failure.

Even a clean `--all` collection is not a configuration-level ZERO certificate
until an independent verifier proves that the frozen selectors are a complete,
prefix-free expansion of certified parent fan-outs.

## Integrity and trust boundary

The internal hashes, no-overwrite publication, and collector detect accidental
corruption and inconsistent edits under a trusted-worker/trusted-storage model.
They are not a cryptographic signature: an adversary who can rewrite the plan,
all evidence, and its terminal marker can recompute self-contained hashes. For
a durable scientific record, archive the frozen plan hash and final collection
receipt outside the writable run tree (for example in immutable or signed
storage), run the collector from its independently audited hash, and record the
trusted Python version. Deploy without packaged `__pycache__` files; use an
empty private `PYTHONPYCACHEPREFIX` so imported source is freshly compiled.
The supplied Slurm wrapper creates and exports such a unique private cache
directory under `SLURM_TMPDIR` for every array task (falling back to the run
directory) and disables bytecode writes.
