# G001 terminal search for Configurations 1, 4, 5, 6, and 7

This distribution prepares and runs the full terminal search.  It is not a
result certificate by itself.

## Exact search boundary

The plan maker replays two sealed AMD packages and does not trust their summary
counts alone:

- C157 job 377219: 37,706 terminal-search leaves for Configurations 1, 5, 6,
  and 7.
- Config4 job 377045: 1,324 partition records.  Exactly 30 are authenticated
  zero certificates (13 preserved and 17 newly discharged), leaving 1,294
  terminal-search leaves.

Therefore the displayed partition has exactly 39,030 records and the solver
runs exactly 39,000 leaves.  Configuration counts are:

| Configuration | Partition records | Prior zero certificates | Search leaves | Bundles |
|---:|---:|---:|---:|---:|
| 1 | 5,176 | 0 | 5,176 | 26 |
| 4 | 1,324 | 30 | 1,294 | 6 |
| 5 | 25,254 | 0 | 25,254 | 124 |
| 6 | 3,977 | 0 | 3,977 | 20 |
| 7 | 3,299 | 0 | 3,299 | 16 |
| Total | 39,030 | 30 | 39,000 | 192 |

The verifier explicitly keeps all 470 Config4 depth-15 descendants whose
calibration `frontier` field is zero.  That field is a selection measurement,
not a terminal proof.  Config4 mixes calibration depths, so its six bundles
are count-balanced; raw cross-depth frontier values are not compared.

## Terminal executable and outcome rules

`g001_remaining_witness_solver.cpp` wraps the exact scientific core used by
the calibration executable.  It accepts no node or depth cap.  Every command
uses the selected exact6/OFF setting:

```text
--multi-edge-cover
--multi-edge-cover-no-hall
--multi-edge-cover-max-components 6
--multi-edge-cover-budget 100
--multi-edge-cover-no-exact-hall
--multi-edge-cover-exact-max-components 6
```

There is no `--stop-edges`, `--max-nodes`, shadow mode, or validation toggle.

- `ZERO` is accepted only from clean terminal exit 0 and a strict durable leaf
  receipt.
- `FOUND` is accepted only after the solver durably writes a
  `LEECH_WITNESS_V1` certificate and the separately compiled STL-only checker
  validates it.  The runner writes and prints an immediate FOUND alert, marked
  `global_search_complete=false`.
- timeout, signal, malformed output, checker failure, missing receipt, hash
  drift, or an existing incomplete directory is non-evidence.
- a global nonexistence claim is possible only after all 39,000 terminal leaf
  receipts and all 30 prior zero certificates verify exactly.

## Resource shape

Each Slurm task allocates one 16-CPU node and runs exactly 15 solver processes;
one CPU remains for the Python controller and evidence I/O.  The full plan has
192 interleaved bundles so the first scheduler wave contains all five
configurations.

- devel smoke: 4 nodes, 64 allocated CPUs, 60 solver workers, 60 light leaves,
  30-minute limit;
- mi2101x canary: 2 nodes, 32 allocated CPUs, 30 solver workers, 30
  deterministic within-configuration quantile leaves;
- full mi2101x: up to 24 nodes, 384 allocated CPUs, 360 solver workers,
  `0-191%24`, four-day per-bundle limit.

Smoke evidence uses a separate run root.  Canary evidence uses the production
run root and is re-verified/reused by the full run.  A full launch is allowed
only after both gate arrays are terminal and `verify_g001_terminal5_gate_v1.py`
accepts their exact receipts.

## Fresh workspace layout

Use a newly named workspace; do not overwrite any previous evidence:

```text
WORKSPACE/
  source/       # exact frozen distribution
  runtime/      # freshly compiled and sealed binaries
  plan/         # terminal plan plus 192 derived bundle plans
  smoke_run/    # devel-only evidence
  production_run/ # canary then full evidence
  logs/
```

The two sealed calibration archives and their already published package
directories may remain at their existing absolute AMD paths.  The plan maker
rehashes each archive, streams an exact archive/package member comparison,
runs the frozen package verifier, reconstructs every prefix, and then commits a
fresh plan directory without replacement.

All terminal5 Python entrypoints suppress bytecode-cache creation before any
local or packaged provenance import.  The Slurm wrappers also export
`PYTHONDONTWRITEBYTECODE=1`, invoke control scripts with `python3 -B`, and the
runner invokes both legacy worker and collector children with `-B`.  Thus
verification and execution do not write `__pycache__` into frozen source or
sealed evidence trees; any cache already present still fails the exact-set
source gate.

## Required order

1. Verify the uploaded source checksum and external freeze.
2. Build the runtime with `g001_terminal5_build_runtime_v1.py`; it compiles the
   solver, checker, and regression executable with the recorded flags, then
   requires the 45-check solver regression and 11-check checker self-test.
3. Run `make_g001_terminal5_plan_v1.py` against the exact two archives and
   packages.  Do not use its test-only archive-identity skip.
4. Run `verify_g001_terminal5_plan_v1.py` independently.
5. Submit `g001_terminal5_devel_smoke_v1.sbatch`; after terminal Slurm state,
   audit all four tasks with `verify_g001_terminal5_gate_v1.py --mode smoke`.
6. Submit `g001_terminal5_mi2101x_canary_v1.sbatch`; after terminal state,
   audit both tasks with `verify_g001_terminal5_gate_v1.py --mode canary`.
7. Only if both audited gates pass and no FOUND alert exists, submit
   `g001_terminal5_mi2101x_full_v1.sbatch`.
8. Report a configuration as soon as its config-only collection passes.  Use
   `collect_g001_terminal5_results_v1.py --all` only after all 192 bundle
   receipts exist.

All output paths must be fresh.  No wrapper deletes or overwrites an existing
leaf, receipt, alert, plan, runtime, or result file.
