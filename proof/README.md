# Order-18 Leech-tree end-to-end computer-assisted proof

This directory binds the formal structural reduction and the preserved
exhaustive-search evidence into one reproducible, fail-closed hybrid proof
workflow.

The mathematical conclusion is:

> There is no positively weighted integral Leech tree on 18 vertices.

The workflow has two proof layers:

1. Lean checks the exact tree model, the exhaustive eight-row first-edge
   reduction, and the theorem saying that exclusion of all eight rows implies
   nonexistence.
2. The preserved C++/Python/PowerShell computation replays the recorded
   coverage and `ZERO` evidence for those eight rows, with the limitations
   stated below.

This is an end-to-end **hybrid computer-assisted proof**, not an end-to-end
Lean proof. The production search, orbit canonicalization, and coverage
collector remain trusted executable code. See `PROOF_LEDGER.md` for the exact
logical chain and trust boundary.

The formal row propositions and the solver configurations are connected by a
documented, manually audited correspondence; the external search does not
construct a Lean `RowExclusions` value. Configuration 3 lacks its original raw
job bundles: its preserved 47-row ledger includes one inferred exit status and
its legacy verifier has a permissive extra-row rule. The current wrapper audits
that archival defect explicitly and refuses its final marker until fresh
evidence covers the exact 47-partition logical roster, including a complete
censused child replacement for any guarded parent, and strict raw receipts are
frozen into a relocatable release.
The released Config3 evidence uses the distinct
`config3-a2-frozen-split-release-v1` schema. The proof record pins its root
record, run result, manifest, verifier, and complete one-line verifier output;
the retired direct-47 schema is rejected unconditionally.

The semantic bridge narrows, but does not erase, that boundary. Its compiled
Lean layer proves the eight literal
executable descriptors well formed,
row-to-descriptor-level `RealizedRowCore`, and the formal A2
adjacency/disjointness split. It does not prove general descriptor formulas or
endpoint isomorphism. The constructive vertex relabeling, exact-orbit
representative preservation, and partition-index transport remain the explicit
conventional argument in Sections 3–4 of `PROOF_LEDGER.md`; the C++ search is
not claimed to be Lean-verified.

## Files

- `PROOF_LEDGER.md`: theorem chain, configuration correspondence,
  completeness argument, evidence inventory, and trust boundary.
- `HYBRID_PROOF_RECORD.json`: machine-readable frozen identities and counts.
- `HybridEndToEndBoundary.lean`: the exact eight-row-to-nonexistence kernel
  boundary, including declaration and axiom-report commands.
- `verify_hybrid_record.py`: independent checks of the record, critical
  hashes, clean pinned Lake dependency checkouts, both frozen source copies,
  the prior-three evidence manifest, global JSON fields, certificate
  identities, and configuration coverage. Its Config3 gate rejects the retired
  direct-47 schema and independently validates the exact 46-direct-plus-22-child
  split release, its root records, source/tool bindings, rosters, sidecars, and
  node identity.
- `verify_end_to_end.ps1`: one-command orchestrator for Lean, the independent
  record checker, all preserved configuration verifiers, and the full
  relocated global collector replay.
- `verify_frozen_runtime_source.py`: pinned-source C++ rebuild, compiler
  provenance capture, and exact 45+11 regression/self-test gate.
- `verify_terminal_plan_regeneration.py`: exact-tree and byte-for-byte
  comparison of a freshly reconstructed Terminal5 plan against the frozen
  195-file production plan.
- `export_verification_release.py` and `verify_verification_release.py`:
  deterministic post-run export of a successful full transcript/result,
  path-free semantic-bridge result, and a validator that requires an
  externally retained separate-release-manifest identity.
- `config3_repair/`: strict historical-ledger auditor plus guarded, resumable
  Config3 direct and split-child runners/verifiers for the exact 47 logical
  partitions. Transient work is kept below `.run/`; the final relocatable
  release is kept below
  `evidence/full_preserved_v1/` and is package-manifested.
- `semantic_bridge/`: source, record, and a separate static/Lean audit of the
  row-to-seed correspondence. The bridge has completed a standalone pinned
  replay, and the proof record pins its `PASS` contract and deterministic
  fresh-baseline result. The main wrapper must still rebuild and check it from
  the clean Lean library created by that same integrated run; a static-only
  marker is never accepted.
- `MANIFEST.sha256`: SHA-256 identities for the files in this directory,
  excluding the manifest itself and generated output below any `.run/`
  directory.

## Prerequisites

- Windows PowerShell 5.1 or PowerShell 7.
- Python 3. The selected interpreter must be a readable regular executable,
  not a Windows Store app-execution alias; pass
  `-PythonExecutable <absolute-python.exe>` when necessary.
- Git.
- A `tar.exe` capable of extracting a Git archive.
- Elan/Lake with Lean 4.24.0.
- A C++20 compiler compatible with the frozen GCC-oriented sources (the
  default command is `g++`; pass `-Cxx <path-or-command>` to select another).
- The compact evidence under `computation/evidence/production/` and, for the
  full replay, the installed archive under `computation/evidence/full/`.
- Enough time for the full global replay, which reads 39,000 search receipts.

The exact historical production compiler executable and Python version were
not preserved. The workflow verifies the preserved evidence; it does not
re-run the 8.5-billion-node search.

The main wrapper does not launch the multi-hour Config3 repair. It requires a
manifest-covered, relocatable released result and invokes only its separate
read-only verifier. The guarded direct run completed 46 of the 47 logical
partitions before its memory guard stopped the final parent partition; that
parent is replaced by a separately censused, complete 22-child fan-out. The
obsolete direct-47 release schema is not accepted as a substitute.

The completed census gives `M = 22`; the release contains exactly
`k = 0,...,21`. The child searches report 42,848,972 node calls and satisfy
`parent_nodes = sum_k child_nodes[k] - 63 = 42,848,909`; the subtraction
removes the three shared calls at edge depths 4, 5, and 6 from each duplicate
child prefix. Together with 124,893,923 direct node calls, this reconstructs
the recorded 167,742,832 logical Config3 calls. The frontier census fixes the
roster but is not itself a zero certificate; all 22 children have independent
`ZERO` receipts.

The release at `config3_repair/evidence/full_preserved_v1/` has schema
`config3-a2-frozen-split-release-v1`: exactly 281 files and 73 directories
including the root. Its 280-line sorted LF manifest covers every byte except
itself. `RELEASE.json` binds the exact ordered logical roster, source/tool/
binary identities, fan-out semantics, and node identity; canonical
`RUN_RESULT.json` binds 46 direct receipts, the census receipt, and all 22 child
receipts. Every receipt has a sidecar plus raw stdout/stderr. The main stage
`config3_a2_frozen_split_strict` invokes
`verify_config3_a2_frozen.py --release-root <fixed-release>` and requires its
complete sole output line, including the manifest, release, and run-result
digests. The verifier rejects duplicate JSON keys, unsafe or aliased paths,
links, junction ancestors, hardlinks, extra/missing files, nonzero exits,
non-`ZERO` results, nonempty stderr, binding or node-accounting disagreement,
and any final rehash change. No final dependency points into the transient
`.run` tree.

## Full verification

From the workspace root:

```powershell
powershell.exe -NoProfile -ExecutionPolicy Bypass -File .\proof\verify_end_to_end.ps1
```

For example, to select an explicit compiler and a real Python executable when
`python.exe` is a Windows Store alias:

```powershell
powershell.exe -NoProfile -ExecutionPolicy Bypass `
  -File .\proof\verify_end_to_end.ps1 `
  -Cxx C:\toolchains\mingw64\bin\g++.exe `
  -PythonExecutable C:\Python313\python.exe
```

Success requires exit code 0 and this final line:

```text
LEECH18_HYBRID_END_TO_END_PASS configurations=8 reported_node_visits=8565199014 global_status=GLOBAL_ZERO_COMPLETE
```

The default command performs the expensive 39,000-receipt global replay. It
builds and self-tests the frozen runtime source but does not launch a
production search.

For a fast integration check that still checks every frozen identity and runs
the three earlier coverage verifiers but relies on the already recorded
global-replay transcript, use:

```powershell
powershell.exe -NoProfile -ExecutionPolicy Bypass -File .\proof\verify_end_to_end.ps1 -UseRecordedGlobalReplay
```

That faster command intentionally ends with
`LEECH18_HYBRID_RECORDED_REPLAY_PASS`, not the full marker above.

## Publishing a successful run

The source-package manifest is an input to the full replay and must not be
changed during that replay. Consequently, publication output is exported
afterward to a sibling tree with its own manifest, rather than copied back
into `proof/` and creating a circular need to rerun everything.
For a successful full run, create an output parent and run:

```powershell
New-Item -ItemType Directory -Force .\evidence\verification_release | Out-Null
python.exe -E -s -S -B .\proof\export_verification_release.py `
  --run-dir .\proof\.run\<successful-run> `
  --output .\evidence\verification_release\leech18_full_v1
$releaseManifestSha256 = '<externally-retained-64-hex-value>'
python.exe -E -s -S -B .\proof\verify_verification_release.py `
  --release .\evidence\verification_release\leech18_full_v1 `
  --source-manifest .\proof\MANIFEST.sha256 `
  --expected-release-manifest-sha256 $releaseManifestSha256
```

Both commands print the SHA-256 of the separate
`RELEASE_MANIFEST.sha256`; the two values must agree. Report and retain that
hash outside both the source package and release directory as the publication
identity. The validator deliberately has no publication-success mode without
`--expected-release-manifest-sha256`: self-consistency of a substituted tree
is not external identity authentication.

If the replay command named a tool outside the workspace, user profile,
Windows system root, or standard program-files roots, add one or more
`--redact-root <tool-or-install-path>` arguments to the export command. Each
must exist and may not be a filesystem root; it is replaced by a numbered
token, and the token count is recorded in the release summary. Export still
fails if any absolute host path remains.

The exporter accepts only `MODE full-global-replay`, exit 0, the exact full
terminal marker, a stable start/end input-manifest hash, and non-placeholder
stage hashes. It also independently rehashes the current exact source-package
file set before exporting. The orchestrator writes `RUN_RESULT.txt` as
canonical UTF-8 LF text, and the exporter requires and copies those bytes
exactly. It emits that result beside a sanitized LF transcript, the exact
input `MANIFEST.sha256`, a package-canonical JSON summary of every
stdout/stderr log's raw and normalized digests, the stage-log manifest already
bound by `RUN_RESULT.txt`, and the path-free semantic-bridge `RUN_RESULT.json`
with a release-name sidecar. Those seven files are bound by
`RELEASE_MANIFEST.sha256`. The validator rehashes the exact
release set, byte-compares its input-manifest copy with the supplied current
source manifest, independently rehashes that manifest's exact non-`.run`
source-package file set, and checks the manifest digest against both fields in
`RUN_RESULT.txt`, checks the transcript and stage-log-manifest hashes recorded
by that result, verifies the released transcript/result digests and sole
terminal marker, requires the exact 24-stage full-replay log roster (including
the frozen Config3 and semantic-bridge gates), strictly parses and checks the
semantic result's exact source/input/artifact/log inventories, independently
cross-binds the included canonical Config3 `RELEASE.json`/`RUN_RESULT.json`/
manifest and sidecars to both the hybrid record and outer result, and rejects
remaining absolute host paths, private-key markers, and common
credential/token patterns. Both export and validation rehash the 12 bridge
sources and the 14 pinned repository inputs actually consumed in
explicit-fresh mode. The fifteenth recorded input is the standalone prebuilt
dossier olean, which explicit-fresh mode deliberately replaces; its fresh
replacement is instead bound by the outer result and semantic result. This
check therefore expects `--source-manifest` to remain in the repository root
that contains the pinned inputs. Thus
the released result attests the unchanged source package used by the run
without changing that source package afterward. Raw stage logs stay
in the excluded local run tree; the release carries their exact manifest and
per-stream byte/hash summary, not a second copy of those logs. Like the source
manifest, this is tamper evidence relative to an externally reported
`RELEASE_MANIFEST.sha256` hash, not a signature, trusted timestamp, or proof
that an untrusted host actually executed the displayed commands.

Because publication sanitizes the outer transcript, the lightweight validator
cannot reconstruct its excluded raw source bytes. The exporter first rehashes
those raw bytes against `RUN_RESULT.txt`; the release summary retains that raw
digest, while the validator checks the result/summary binding and separately
rehashes the sanitized transcript. Correctness of this redaction mapping
therefore remains part of the hash-pinned exporter trust boundary.
For the same reason, the validator cannot rehash the excluded raw stage logs:
their sizes and hashes are assertions made by the exporter after it rehashes
the run tree. The released manifest authenticates those assertions relative to
the externally retained release-manifest hash; it does not turn them into an
independent replay of the omitted streams. The included semantic result is the
exact path-free PowerShell-serialized report produced by the pinned wrapper;
it is deterministic under that pinned serializer, not claimed to implement a
language-independent JSON canonicalization standard. The exporter rehashes
the report's exact eight inner oleans and 22 inner logs before release, but
those inner bytes are also omitted; the validator checks their exact reported
inventories and bindings rather than pretending to rehash absent files.

Before emitting its export marker, the exporter also revalidates the exact
runtime-source binary/log/report tree and its 16-entry manifest, the exact
195-file regenerated-plan tree and its 193-entry artifact manifest, the
clean-project archive, and the fresh dossier olean. Seven path-free
role/path/result-field/digest bindings are stored in the
`LEECH18_VERIFICATION_RELEASE_STAGE_DIGESTS_V2` `STAGE_DIGESTS.json`.
Because those run-local bytes are deliberately omitted from the compact
release, the lightweight validator checks the bindings against
`RUN_RESULT.txt` and the externally anchored release bytes but cannot
independently rehash the omitted artifacts. They have the same explicit
exporter-assertion boundary as the omitted raw stage streams.

## What the command does

1. Independently checks the machine-readable record, the clean legacy Lean
   repository, the exact Lake-manifest dependency set, every dependency
   revision and worktree, and all critical source-file hashes.
2. Independently verifies both copies of the 28-file frozen Terminal5 source
   set and all 1,078 files in the pinned prior-three evidence manifest. This
   pins the verifier scripts before any of them execute.
3. Runs the frozen Terminal5 static, synthetic, and mutation-negative source
   test and requires its exact `PASS test_g001_terminal5_v1 checks=47` output
   with empty stderr.
4. Rebuilds the pinned frozen solver, independent witness checker, and solver
   regression binary with `-O2 -std=c++20 -Wall -Wextra -Wpedantic -Werror`,
   then requires all 45 solver checks and 11 checker self-tests to pass. The
   rebuild wrapper rejects linked/hard-linked sources, compiler, ancestors,
   and outputs, rehashes the source/compiler/binaries after the tests, and
   rehashes every manifested output immediately before success.
5. Replays the two hash-and-size-pinned C157 and Configuration-4 calibration
   archives against their exact extracted package trees, reconstructs the
   prefix-free 39,030-record/192-bundle Terminal5 plan with the frozen plan
   builder, and compares all 195 output files by SHA-256 and by bytes with the
   frozen production plan. This rederives plan selection and bundling from the
   sealed calibration packages; it does not rerun the calibration searches.
6. Reads the complete pinned Git tree first, rejects non-regular modes and
   unsafe or case-aliased paths before extraction, then extracts that exact
   commit with `git archive` into the run directory. It requires the extracted
   regular-file set and every Git blob identity to match the complete pinned
   tree, and builds fresh project oleans there with
   `lake --rehash --offline build`. Pinned Lake 5.0.0 has no build-job-count
   command-line option, so this stage sets Lean's supported runtime control
   `LEAN_NUM_THREADS=1` for Lake's task scheduler and its Lean subprocesses.
   Only the
   already pinned, clean Lake dependency checkouts and their build caches are
   junctioned into the
   temporary project; the fresh `LeechTrees` output is first in the boundary
   compiler's import path. Ambient `LEAN_PATH`, `LEAN_SRC_PATH`,
   `LEAN_SYSROOT`, and Lean-executable overrides are cleared for this stage.
   The fresh `FirstEdgeDossier.olean` is required explicitly and its hash is
   retained; any later semantic-bridge gating must consume this same fresh
   library rather than a pre-existing project cache.
7. Builds the standalone formal boundary in an isolated output directory with
   the direct Lean elaborator pinned to `-j 1`, and requires exactly the two
   declared axiom reports, each with only `propext`,
   `Classical.choice`, and `Quot.sound`.
8. Runs the semantic-bridge PowerShell wrapper with
   `-BaselineLeanLib` pointing at that same fresh clean-project library and a
   new run-local `-RunRoot`. It requires exit 0, empty wrapper stderr, exactly
   one preliminary static-check marker, the exact full-replay marker as the
   unique last stdout line, and a hash-pinned deterministic path-free
   `RUN_RESULT.json`/sidecar. The preliminary marker belongs only to the source
   preflight; the nested full checker separately rejects that marker in its own
   stdout. The result must bind
   the fresh dossier olean, bridge record, exact four-declaration axiom audit
   (each report a subset of, and their union exactly,
   `{Classical.choice, Quot.sound, propext}`),
   the recorded `lean_elaboration_threads = 1` policy, 12 bridge sources,
   15 pinned inputs, eight fresh oleans, and 22 raw inner
   logs. The proof record status is `PASS` and pins the expected deterministic
   fresh-baseline result and sidecar hashes. This stage remains mandatory in
   every integrated replay and fails closed on any disagreement.
9. Runs the frozen Terminal5 plan verifier and requires its complete
   normalized stdout digest.
10. Runs the preserved Configuration 2, 3, and 8 coverage verifiers and
   requires their complete normalized stdout digests, including exact counts.
   For Configuration 3 it additionally runs the strict historical-ledger
   audit and the independent frozen-evidence verifier over the relocatable
   released 47-logical-partition tree (46 direct receipts plus the censused
   22-child replacement), requiring the pinned release, run result, manifest,
   and exact sole output-line hash.
11. Replays the frozen global collector for Configurations 1, 4, 5, 6, and 7,
   requiring byte-for-byte equality with `GLOBAL_JOB377730.json` and the exact
   normalized success output.
12. Repeats the complete read-only record/evidence/dependency audit, verifies
    the package manifest again, and requires its hash to be unchanged from the
    start of the replay before emitting the final marker.

The separate `test_g001_remaining_leaf_pipeline.py` test requires a
Linux/POSIX host. It reports `SKIP` on Windows and is not counted as a passing
stage of this Windows workflow.

The local C++ rebuild removes compiler include/library and dynamic-loader
injection variables, rehashes its pinned source closure, compiler executable,
and generated binaries after the tests, and requires the exact generated
binary/log/report tree before manifesting it. It records the selected compiler
executable hash, raw version output, flags, generated binary hashes, and test
logs. It is a
source-level build-and-test check, not a claim that those local binaries are
identical to the unavailable historical GCC 12 production executable. The
compiler driver's subordinate assembler/linker/runtime components remain part
of the selected host-toolchain trust boundary. The
clean Lean project rebuild still trusts the pinned dependency build caches;
it specifically prevents reuse or shadowing by an old project `LeechTrees`
olean.

Python verifier entrypoints run with environment paths and site-package
loading disabled (`-E -s -S -B`) after Python injection variables are cleared.
The selected interpreter executable hash and version output are retained, but
the host Python standard library/runtime, PowerShell, Git, `tar`, OS, and
filesystem remain trusted tooling.

No preserved receipt, plan, certificate, source file, or global record is
modified. Temporary build and log files are written only below `.run/`
directories; the main orchestrator uses a unique timestamp-and-process
directory under `proof/.run/`. Every
normally terminating invocation writes `RUN_RESULT.txt` with its mode, exit
 code, final marker, package-manifest hash, runtime report/manifest hashes, the
 pristine Lean-project archive hash, selected Python/PowerShell/Git/`tar`/Lean/
 Lake executable hashes, the exact `LEAN_ELABORATION_THREADS 1` and
 `LEAN_NUM_THREADS 1` fields, the fresh dossier olean hash, and
timestamps; caught
failures include the normalized error. It also retains the three anchor hashes
   of the freshly regenerated Terminal5 plan, the completed outer-transcript
   hash, the released Config3 record/run-result/manifest hashes,
the semantic bridge record/result/sidecar and actual normalized-stdout hashes,
and a manifest hash binding every raw per-stage stdout/stderr log. The
outer host stream is retained as `ORCHESTRATOR_TRANSCRIPT.txt`, while each
external subprocess keeps separate stdout and stderr logs.

The source-package manifest walk prunes every directory segment named `.run`
without descending into it. Every included publication file must be regular,
non-linked UTF-8 text and exactly manifest-listed. Before either terminal
marker, the wrapper also rejects absolute personal home paths,
credential-like filenames, private-key headers, and common credential/token
assignment patterns in that manifest-covered text. Host-specific absolute
paths may remain in excluded raw local logs; the publication exporter replaces
them with explicit tokens and fails if any absolute host path remains.

The record, checker, and package manifest provide mutual tamper evidence only
relative to the manifest hash reported outside the package in a run result;
they are not a cryptographic signature or an external timestamp.
