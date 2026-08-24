# Eight-row semantic bridge

This directory checks one descriptor-level part of the hybrid proof boundary:
the authoritative Lean `EightRowDossier` and the hash-pinned production solver
sources have the same eight local weighted-incidence/support/MEX descriptors.

`LeanRowSemanticBridge.lean` proves, in Lean, that every dossier row implies a
deliberately weaker `RowCore`
consisting of:

- the adjacency/disjointness of the physical weight-1 and weight-2 edges;
- the weight and endpoint contact pattern of the row's weight-3 or weight-4
  witness;
- the current prefix-distance support; and
- the forced next physical-edge weight.

The implementation is split into sequential modules under `SemanticBridge/`.
`DescriptorWellFormed` reads the literal numeric `seedEdges`, checks that they
are a simple three-edge forest, computes their edge-incidence pattern, complete
three-edge distance support, and positive MEX, and is required to prove all
eight descriptors satisfy that relation by kernel reduction.  The aggregate
theorem then returns a `RealizedRowCore`, which is the conjunction of this
seed-data theorem and the formal row projection. Thus `seedEdges` is not
unused by the theorem boundary.

Source presence or the static-only marker is not proof evidence. Every bridge
module has elaborated in the standalone pinned replay, and the exact axiom
audit passed there. The parent proof record is `PASS` and pins the expected
deterministic fresh-baseline result and sidecar hashes. The integrated wrapper
must repeat the elaboration using the clean baseline library built in that same
run and fails closed on any disagreement.

Forgetting the other row facts (path witnesses, missing physical weights, cut
bounds, and restrictions on the next edge) enlarges the formal class.  This is
the required set-theoretic direction for reusing a solver that exhausts all
completions of the weaker seed, conditional on the representation/isomorphism
and solver-soundness premises listed below.

`verify_semantic_bridge.py` then independently:

1. checks every Lean/C++ input against `SEMANTIC_BRIDGE_RECORD.json`;
2. parses the exact row order and core fields from the authoritative Lean
   source;
3. parses the actual seeds and mode/configuration map from the certificate-era
   C++ sources;
4. recomputes every forest's complete internal-distance support and positive
   MEX rather than trusting source comments; and
5. compares those results with descriptor lines emitted by the elaborated Lean
   module.

For configuration 3, the full replay also requires Lean to prove that the
forced weight-5 edge is either
endpoint-disjoint from the weight-4 edge or adjacent to it, while remaining
endpoint-disjoint from weights 1 and 2.  These formal incidence alternatives
match the separate and far-end-attached relations parsed from the production
A2 source at descriptor level; the numeric vertex correspondence remains part
of the representation boundary stated below.  This conclusion combines
`A2ProductionSplit` with the original `AdjacentMeetsTwoRow` dossier case; the
weakened aggregate or split theorem alone is not used as a replacement for
the original row facts.

The resulting checked correspondence is:

| Paper configuration | Lean row | Solver mode | Support | Next |
|---:|---|---|---|---:|
| 1 | `AdjacentNoneRow` | `g001_row0` | 1,2,3,4 | 5 |
| 2 | `AdjacentMeetsOneRow` | `g001_row1` | 1,2,3,4,5,7 | 6 |
| 3 | `AdjacentMeetsTwoRow` | `a2` common projection | 1,2,3,4,6,7 | 5 |
| 4 | `AdjacentMeetsBothRow` | `g001_row3` | 1,2,3,4,5,6 | 7 |
| 5 | `DisjointNoneRow` | `g001_row4` | 1,2,3 | 4 |
| 6 | `DisjointMeetsOneRow` | `g001_row5` | 1,2,3,4 | 5 |
| 7 | `DisjointMeetsTwoRow` | `g001_row6` | 1,2,3,5 | 4 |
| 8 | `DisjointMeetsBothRow` | `g001_row7` | 1,2,3,4,5,6 | 7 |

## Replay

From the workspace root on Windows PowerShell:

```powershell
powershell.exe -NoProfile -ExecutionPolicy Bypass `
  -File .\proof\semantic_bridge\verify_semantic_bridge.ps1
```

The standalone default uses the recorded prebuilt baseline library.  A parent
replay that has already built the pinned Lean project from a clean archive must
reuse that build rather than build again or fall back to the standalone
artifact:

```powershell
powershell.exe -NoProfile -ExecutionPolicy Bypass `
  -File .\proof\semantic_bridge\verify_semantic_bridge.ps1 `
  -BaselineLeanLib <clean-project>\.lake\build_release_clean\lib\lean `
  -RunRoot <new-main-run-subdirectory>
```

The explicit library mode discovers its project root, checks the clean
toolchain, Lake files, and authoritative dossier source against the record,
requires the dossier `.olean` beneath the supplied library, and uses that
project's package libraries.  `RunRoot` must not already exist, preventing
reuse of stale bridge `.olean` files.

The replay refuses to launch Lean if another Lean/Lake process exists or if
physical RAM use is at least 90%.  It compiles the bridge modules in separate
Lean processes, each with the explicit `-j 1` elaborator limit, uses Lean
4.24.0 and either the explicitly supplied clean
baseline or the standalone hash-pinned prebuilt dossier, and never rebuilds
the baseline itself. The one-thread setting is a resource-scheduling control,
not a proof-semantic change; the non-compiling `--version` probe does not take
that flag. A complete run ends with:

```text
RUN_DIRECTORY <fresh-run-directory>
RUN_RESULT_JSON <fresh-run-directory>\RUN_RESULT.json sha256=<sha256> sidecar=<fresh-run-directory>\RUN_RESULT.sha256
LEECH18_SEMANTIC_BRIDGE_REPLAY_OK rows=8 direct=7 projected=1
```

`RUN_RESULT.json` and its SHA-256 sidecar are created only after the full
checker succeeds.  The deterministic path-free report omits dynamic run paths
and memory readings.  It is serialized by the pinned PowerShell wrapper and is
not claimed to implement a language-independent canonical JSON standard.  It
records the baseline dossier, source, input, emitter/checker log, axiom-audit,
the integer `lean_elaboration_threads = 1`, and every fresh bridge `.olean`
hash; all generated artifacts and logs remain
beneath the selected run directory.  Before publishing the report the wrapper
requires the exact 8-artifact and 22-log inventories, rejects linked or
hard-linked inventory files, rejects absolute host paths in the report, and
requires both the static and full checker markers to be unique exact final
stdout lines.  Each of the four axiom reports must be a
subset of `{Classical.choice, Quot.sound, propext}` and their union must equal
that allowlist.  Individual per-declaration subsets are not preassigned; the
pinned full-checker stdout hash binds the subsets actually observed.

The source-only half can be run without Lean:

```powershell
python -E -s -S -B .\proof\semantic_bridge\verify_semantic_bridge.py `
  --static-only --skip-prebuilt-dossier
```

That command intentionally ends in `LEAN_ELABORATION=NOT_CHECKED` and is not a
substitute for the full replay.

## Exact remaining boundary

This bridge does **not** turn the external searches into kernel proofs.  The
following premises remain outside Lean:

1. The numeric C++ `add_edge(u,v,w)` representation has the intended ordinary
   weighted-forest semantics implemented by the production solver.
2. The production recursion enumerates every completion of each seed, its
   symmetry reduction is complete, and every active rejection rule is sound.
3. The partition plans and preserved `ZERO` records cover every root branch and
   genuinely came from the pinned executables.
4. For configuration 3, the external runtime and preserved partition evidence
   really execute and cover both formally exhaustive weight-5 placements.
5. The Python parser/runtime, Lean compiler/kernel, and the accepted prebuilt
   dependency artifacts remain in the trusted computing base.
6. A vertex-level theorem that the computed weighted three-edge incidence
   relation induces an explicit weighted-forest isomorphism to the numeric
   vertices, together with a source-level theorem that all solver behavior is
   invariant under endpoint orientation and vertex relabeling.  The production
   source uses undirected `add_edge` adjacency and canonical rooted/forest
   codes, but numeric labels also break candidate-order ties and therefore set
   partition branch indices.  Special A2 equality modes contain additional
   fixed-vertex tests, but the pinned 47-row ledger is checked to use only
   `a2_attached` and `a2_separate`, so those tests are inactive for the evidence
   at issue.  The checker verifies these source/mode facts and the exact numeric
   seeds, but it does not turn them into the required representation/partition-
   invariance proof.

Accordingly, this directory supports the precise statement “the formal row and
the literal searched seed have the same checked weighted incidence,
support, and MEX descriptor.”  It does not yet claim a Lean vertex-isomorphism
to the C++ representation, and it does not support “Lean has verified the
8.565-billion-node external search.”
