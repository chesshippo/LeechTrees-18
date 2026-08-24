# Reproducing the order-18 result

There are two distinct checks:

1. **Preserved-evidence replay** rebuilds the formal boundary and runtime and
   rereads every preserved receipt. It does not repeat the 8.5-billion-node
   search.
2. **Fresh recomputation** rebuilds the search programs and executes the
   complete released branch roster. Plan for hundreds of CPU-hours.

The supplied verifier and recomputation drivers cover all eight
configurations. Run the checks below in the new checkout to establish results
for that checkout and environment.

## Requirements

For preserved-evidence replay:

- Windows PowerShell 5.1 or PowerShell 7;
- Python 3.12 or newer;
- Git and `tar`;
- Elan, Lake, and the pinned Lean 4.24.0 toolchain;
- a GCC-compatible C++20 compiler.

For fresh recomputation, use both:

- Windows with PowerShell and MSYS2 UCRT64 GNU g++ 14.2.0 for Configurations
  2, 3, and 8;
- Linux with Python 3.12+ and a GCC-compatible C++20 compiler for
  Configurations 1, 4, 5, 6, and 7.

The exact environment identities are recorded in
[`reproducibility/environment.lock.json`](reproducibility/environment.lock.json).
Do not run `lake update`; `lean/LeechTrees/lake-manifest.json` pins the Lean
dependencies. On Windows, use a short checkout path such as `C:\leech18`.

## 1. Preserved-evidence replay

### 1.1 Install the full evidence asset

Obtain the release asset
`leech18_full_extracted_tree_repacked_20260820.tar.gz`. Its required identity
is:

```text
Size:       826575460 bytes
SHA-256:    69bc248cf9688b8d273983068249e7e91c9a5cde5a42488f21f2569cd7904f87
Members:    991377
```

Check the archive and then install it into the repository-defined evidence
location:

```powershell
python.exe -B .\scripts\install_evidence_archive.py `
  --archive C:\path\to\leech18_full_extracted_tree_repacked_20260820.tar.gz `
  --verify-only

python.exe -B .\scripts\install_evidence_archive.py `
  --archive C:\path\to\leech18_full_extracted_tree_repacked_20260820.tar.gz
```

The commands must emit `LEECH18_EVIDENCE_ARCHIVE_OK` and
`LEECH18_EVIDENCE_INSTALLED`, respectively. The installer verifies the archive
size, digest, complete member inventory, path safety, and destination before
writing anything.

### 1.2 Materialize and build the pinned Lean tree

```powershell
python.exe -B .\scripts\materialize_lean_git.py

Push-Location .\lean\LeechTrees
lake build
Pop-Location
```

The first command restores the nested Git metadata from the bundled commit
`2747de53478568e580e364ddc685871d55dc6e7e`. A cold Lake build may use the
network to obtain the dependency revisions already fixed in
`lake-manifest.json`.

### 1.3 Run the full verifier

```powershell
powershell.exe -NoProfile -ExecutionPolicy Bypass `
  -File .\proof\verify_end_to_end.ps1 `
  -Cxx C:\path\to\g++.exe `
  -PythonExecutable C:\path\to\python.exe
```

The selected Python executable must be a real executable rather than a
Windows application alias. The command succeeds only with exit code zero and
this exact final line:

```text
LEECH18_HYBRID_END_TO_END_PASS configurations=8 reported_node_visits=8565199014 global_status=GLOBAL_ZERO_COMPLETE
```

The verifier checks the pinned Lean source and dependency tree, rebuilds the
formal boundary, compiles and tests the frozen C++ runtime, regenerates and
compares the search plan, validates Configurations 2, 3, and 8, and replays
the global collector over the 39,000 terminal receipts for Configurations 1,
4, 5, 6, and 7.

## 2. Fresh recomputation

Fresh recomputation reruns the complete released branch roster. It begins
from the frozen, hash-identified partition plan; it does not derive that plan
again from the eight root configurations.

Use new output directories. The drivers refuse to overwrite an existing run.

### 2.1 Windows: Configurations 2, 3, and 8

From PowerShell at the repository root:

```powershell
$Python = (Get-Command python.exe).Source
$Cxx = 'C:\msys64\ucrt64\bin\g++.exe'
$RunBase = 'C:\leech18-runs'
New-Item -ItemType Directory -Force $RunBase | Out-Null

powershell.exe -NoProfile -ExecutionPolicy Bypass `
  -File .\reproducibility\preflight_windows.ps1 `
  -PythonExecutable $Python `
  -Cxx $Cxx
```

Required preflight marker:

```text
LEECH18_WINDOWS_PREFLIGHT_OK
```

Compile, test, and execute the full source-built roster:

```powershell
& $Python -E -s -S -B .\scripts\recompute_prior_three_from_source.py `
  --cxx $Cxx `
  --build-root "$RunBase\prior-three-build-v1" `
  --run-root "$RunBase\prior-three-v1" `
  --confirm-expensive-run
```

Required final marker:

```text
LEECH18_PRIOR_THREE_FULL_RECOMPUTATION_OK logical_partitions=178 physical_processes=200 zero_processes=199 logical_nodes=600726235
```

Retain both run directories. The assembly step uses
`prior-three-build-v1/BUILD_RECEIPT.json` and
`prior-three-v1/RECOMPUTATION_SUMMARY.json`.

### 2.2 Linux: C157 coverage and Configurations 1, 4, 5, 6, and 7

From a Linux shell at the repository root, after installing the full evidence
asset:

```sh
CXX="$(command -v g++)"
PYTHON="$(command -v python3)"
RUNS=/srv/leech18-runs
mkdir -p "$RUNS"

bash reproducibility/preflight_linux.sh \
  --cxx "$CXX" \
  --python "$PYTHON"
```

Required marker: `LEECH18_LINUX_PREFLIGHT_OK`.

Recompute the C157 coverage stage:

```sh
"$PYTHON" -E -s -S -B scripts/recompute_c157_full.py \
  --preflight \
  --compiler "$CXX"

"$PYTHON" -E -s -S -B scripts/recompute_c157_full.py \
  --run \
  --work-dir "$RUNS/c157-v1" \
  --compiler "$CXX" \
  --workers 15

"$PYTHON" -E -s -S -B scripts/recompute_c157_full.py \
  --verify-run \
  --work-dir "$RUNS/c157-v1"
```

Required markers:

```text
G001_C157_FRESH_RECOMPUTATION_OK configurations=4 leaves=37706 internal_prefixes=2135 zero_children=464
G001_C157_FRESH_RECOMPUTATION_RECORD_OK configurations=4 leaves=37706 internal_prefixes=2135 zero_children=464
```

If the C157 run is interrupted, repeat its production command with `--resume`
instead of `--run` and the same work directory.

Recompute the 39,000 canonical terminal searches and the 30 supplemental
Configuration-4 searches:

```sh
bash scripts/recompute_terminal5_full.sh \
  --run-root "$RUNS/terminal5-v1" \
  --cxx "$CXX" \
  --python "$PYTHON"
```

Required final marker:

```text
LEECH18_TERMINAL5_FULL_RECOMPUTATION_OK fresh_search=39030 canonical_search_receipts=39000 supplemental_reclassified=30 canonical_certified_zero_records=30 displayed_records=39030 reported_nodes=7964472779 supplemental_nodes=INTEGER
```

Retain the complete `c157-v1` and `terminal5-v1` trees.

### 2.3 Assemble all eight fresh results

Place the completed Windows result trees where the Linux coordinator can read
them, preserving every file. Then run:

```sh
"$PYTHON" -E -s -S -B scripts/assemble_fresh_all_eight.py \
  --prior-three-summary "$RUNS/prior-three-v1/RECOMPUTATION_SUMMARY.json" \
  --prior-three-build-receipt "$RUNS/prior-three-build-v1/BUILD_RECEIPT.json" \
  --c157-summary "$RUNS/c157-v1/C157_RECOMPUTATION.json" \
  --terminal-summary "$RUNS/terminal5-v1/GLOBAL_REPRODUCTION.json" \
  --config4-summary "$RUNS/terminal5-v1/config4_certified_zero_run/RECOMPUTATION_SUMMARY.json" \
  --terminal-preflight "$RUNS/terminal5-v1/TERMINAL5_PREFLIGHT.json" \
  --output "$RUNS/LEECH18_FRESH_ALL_EIGHT.json"
```

Required marker:

```text
LEECH18_FRESH_ALL_EIGHT_ASSEMBLED configurations=8 reported_nodes=8565199014 status=COMPUTATIONAL_EXCLUSIONS_COMPLETE
```

The assembler checks the build receipts, complete job rosters, C157 task
records, Terminal5 selectors and receipts, Configuration-4 results, and the
reported node totals. It does not turn the external search into a Lean proof
term; the logical implication from the eight exclusions to nonexistence is
the separately checked Lean boundary.

## Failure semantics and resources

- `FOUND` is retained as a potentially decisive witness and prevents a
  complete-zero result.
- A timeout, killed child, missing or duplicate receipt, `UNKNOWN`, malformed
  selector, unexpected stderr, or nonzero exit never counts as `ZERO`.
- The full evidence archive expands to approximately 950,000 files. Reserve
  substantially more space than its compressed size; 20 GiB free is a
  conservative allowance rather than a measured minimum.
- Runtime depends strongly on processor, storage, memory, and concurrency.
  The fresh search should be treated as a hundreds-of-CPU-hours computation.
- The exact original compiler executable was not retained. The Windows
  source-build route pins the documented compiler family and version; the
  rebuilt executable hash will necessarily depend on the local toolchain.
