# Proof ledger: nonexistence of an order-18 Leech tree

## 1. Claim and proof mode

The claim is:

> There is no finite simple tree on 18 vertices, with strictly positive
> integral edge weights, whose 153 unordered vertex-pair distances are
> exactly `1,2,...,153`.

This ledger records a hybrid computer-assisted proof. Lean checks the tree
model and the complete reduction to eight first-edge rows. Conventional
mathematics proves the recursive search model and the soundness of its
necessary-condition filters. Frozen exhaustive computations eliminate all
eight rows.

It is not asserted that the production C++ search is definitionally equal to
the later Lean executable search kernel, nor that the computation has been
evaluated by Lean's kernel.

## 2. Formal structural reduction

The authoritative baseline project is `lean/LeechTrees` at commit
`2747de53478568e580e364ddc685871d55dc6e7e`, with Lean 4.24.0 and mathlib
commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.

The formal tree model is `LeechTrees.Foundation.PosIntTree`; its exact Leech
spectrum predicate is `LeechTrees.Foundation.IsLeech`.

The declaration

```text
LeechTrees.Foundation.FirstEdgeDossier.firstEdge_eightRowDossier
```

proves, for `n >= 5`, uniqueness of physical edges of weights 1 and 2 and an
exhaustive nested disjunction `EightRowDossier T e1 e2`. Its eight disjuncts,
in source order, are:

1. `AdjacentNoneRow`
2. `AdjacentMeetsOneRow`
3. `AdjacentMeetsTwoRow`
4. `AdjacentMeetsBothRow`
5. `DisjointNoneRow`
6. `DisjointMeetsOneRow`
7. `DisjointMeetsTwoRow`
8. `DisjointMeetsBothRow`

The formal target is exhaustive membership in the nested disjunction. A
separate formal pairwise-exclusivity theorem is not needed for nonexistence
and is not claimed here.

The artifact declaration

```text
Leech18EndToEnd.no_order18_leech_of_all_rows
```

is a kernel proof that functions excluding those eight row propositions imply

```text
not (exists T : PosIntTree 18, IsLeech T).
```

`HybridEndToEndBoundary.lean` prints the types and axiom dependencies of this
chain during its isolated build.
The external search does not construct a Lean value of `RowExclusions`; that
structure marks the exact formal/computational boundary. The reproducible
artifact imports only the authoritative baseline dossier and the small
standalone boundary in this directory.

## 3. Exact row-to-search correspondence

| Paper configuration | Lean row | Solver row | Frozen prefix | Next forced weight |
|---:|---|---:|---|---:|
| 1 | `AdjacentNoneRow` | 0 | path 1-2 plus separate edge 4 | 5 |
| 2 | `AdjacentMeetsOneRow` | 1 | path 4-1-2 | 6 |
| 3 | `AdjacentMeetsTwoRow` | 2 | path 1-2-4 (`A2`) | 5 |
| 4 | `AdjacentMeetsBothRow` | 3 | star with incident weights 1,2,4 | 7 |
| 5 | `DisjointNoneRow` | 4 | separate edges 1,2,3 | 4 |
| 6 | `DisjointMeetsOneRow` | 5 | path 1-3 plus separate edge 2 | 5 |
| 7 | `DisjointMeetsTwoRow` | 6 | separate edge 1 plus path 2-3 | 4 |
| 8 | `DisjointMeetsBothRow` | 7 | path 1-3-2 | 7 |

This table is simultaneously encoded in `HYBRID_PROOF_RECORD.json` and
checked for the exact one-to-one sets `{1,...,8}` and `{0,...,7}`.
This is a manually audited semantic correspondence, not a Lean theorem and
not an independently derived equivalence between the Lean row propositions
and the production solver's state representation.

On a successful mandatory replay, the semantic bridge has a deliberately
smaller formal claim. It proves the eight literal executable descriptors well formed,
row-to-descriptor-level `RealizedRowCore`, and the formal A2
adjacency/disjointness split. It does not prove general descriptor formulas,
endpoint isomorphism, or the correctness of the search implementation. The
normalization below must case-split the original
`firstEdge_eightRowDossier`; its weakened aggregate alone does not retain all
row predicates and physical-weight facts. In the A2 case it uses
`A2ProductionSplit` together with the original `AdjacentMeetsTwoRow`, not the
split theorem in isolation.

The conventional bridge uses the following constructive normalization. Fix
the actual disjunct of `firstEdge_eightRowDossier`, retaining its original row
predicates and physical-weight facts (not merely the weakened `RowCore`). Its
three named seed edges form a three-edge weighted incidence forest. In a tree,
two distinct edges meet in at most one endpoint, and three pairwise-meeting
edges have one common centre because a triangle is impossible. The incidence
bits therefore classify the forest as three disjoint edges, an adjacent pair
plus a disjoint edge, a path, or a star, exactly as listed in the table. Match
the uniquely weighted edges and their incident endpoints to the corresponding
numeric solver seed, then extend that endpoint injection arbitrarily to a
bijection of all 18 vertices. This relabeling preserves edge weights, support
and incidence, weighted paths and distances, and hence the forced positive
MEX. For the A2 continuation, the forced weight-5 edge is either separate or
attached at the recorded far endpoint, giving the two Config3 seed forms
recorded by the repair runner. This is the precise finite isomorphism argument
used here; it is not a kernel-checked theorem connecting Lean structures to
C++ states.

## 4. Search-completeness argument

Fix a hypothetical completion of one row.

At each recursive stage the exposed edges form a weighted forest; unused
vertices are singleton components. The forced-positive-MEX theorem determines
the next physical edge weight. Any next edge of a tree joins two distinct
components, so it is determined by an unordered component pair and one port
in each component. The solver enumerates all such pairs and ports. Exact
weighted-forest canonicalization retains an automorphism representative of
every possible extension. Therefore induction on the number of physical
edges places every genuine completion in a generated recursive subtree unless
a necessary-condition rejection applies.

The pinned solver's numeric labels influence two separate choices. First,
scan/map insertion order selects a concrete representative among extensions
with equal rooted/component codes. The trusted exact-orbit
existence-preservation argument ensures that this representative choice does
not erase a completion. Second, candidate ordering by `(score,u,v)` fixes the
root, path, and child partition indices. Transport through the relabeling above
can change those indices, but it cannot change the union: the preserved
coverage checks require the exact root roster and exact child fan-out rosters
for the same fixed seed/source, and certify their complete union. This
conclusion still assumes the pinned solver's undirected edge insertion and
isomorphism/orbit-reduction soundness; those implementation facts are part of
the conventional trusted-code bridge, not consequences of the Lean theorems.
Equality-profile and fixed-port pruning code is present but inactive in every
proof-producing run (the 47 base-mode Config3 equality fields are `-1`), so no
relabeling-invariance claim for those predicates is used.

The validity checks recompute the new complete cross-distance block. A child
is rejected only for a mathematical obstruction: repeated distance, a value
outside `1,...,153`, incompatible 7/11 parity, excess hop length, or failure of
the whole-block necessary condition. Resource exhaustion in the whole-block
subroutine returns `UNKNOWN/PASS`, never rejection.

For the whole-block condition, delete the selected future physical edges from
a genuine completion and call the resulting components `K_i`. For each pair
`i<j`, the unique route has fixed exit and entry ports and a positive outside
length `L_ij`. Hence all cross distances form

```text
{ d_i(x,p_ij) + L_ij + d_j(p_ji,y) : x in K_i, y in K_j }.
```

Exactness of the Leech spectrum makes each block injective, puts it in the
unused distance set, and makes different component-pair blocks disjoint. The
cardinality identity

```text
sum_{i<j} |K_i||K_j| = choose(18,2) - sum_i choose(|K_i|,2)
```

shows that the blocks fill the unused set. Thus exhaustive failure to find a
required block or compatible exact cover is a sound rejection. The converse
is neither used nor claimed.

At 17 physical edges, a surviving forest is a tree on 18 vertices. If its 153
pair distances are distinct and all lie in `1,...,153`, they equal that whole
set. This establishes terminal completeness.

Formal baseline results support the conventional argument at its mathematical
interfaces: `LeechTrees.Foundation.PosIntTree.t2_forced_mex` supplies the
forced next weight;
`LeechTrees.Foundation.T2_forced_mex_merge_persistence` supplies the full
merge/injectivity/range/avoidance/persistence bundle;
`LeechTrees.QHop.order18_simplePath_length_le_14` supplies the order-18 hop
bound; `LeechTrees.Foundation.T3_taylor_parity_order18` (equivalently the
derived `t3_order18_class_sizes`) supplies the 7/11 parity class sizes;
`LeechTrees.PathMulticut.actual_selectedEdge_gluing_polynomial` formalizes the
selected-component gluing polynomial; and
`LeechTrees.Foundation.FirstEdgeDossier.firstEdge_eightRowDossier` supplies the
eight-row split. These theorems justify the stated mathematics. They do not
prove that the C++ state representation, canonicalizer, or pruning
implementation is extensionally equal to those Lean definitions.

### Exact executed pruning inventory

The production final-five jobs and the fresh Configuration 3 jobs use the
same narrow active-pruner family. The proof credits only these checks:

| Executed check | Final five | Fresh Config3 | Logical role |
|---|---|---|---|
| `analyze.valid` | active | active | rejects a forest only when its currently determined distances already violate uniqueness/range validity |
| `partial_hop_diameter_ok` | active | active | necessary partial hop/diameter bound |
| `parity_profile_possible` | active | active | necessary 7/11 parity-profile feasibility |
| `candidate_cross_ok` | active | active | necessary cross-distance compatibility for a proposed extension |
| `a2_multi_cover` exact6 | active | active | whole-block component-pair cover feasibility, with the fail-open rule below |

The exact final-five argument suffix is

```text
--multi-edge-cover
--multi-edge-cover-no-hall
--multi-edge-cover-max-components 6
--multi-edge-cover-budget 100
--multi-edge-cover-no-exact-hall
--multi-edge-cover-exact-max-components 6
```

The fresh Configuration 3 suffix omits both explicit max-setting pairs,
`--multi-edge-cover-max-components 6` and
`--multi-edge-cover-exact-max-components 6`. In that older A2 solver the
ordinary multi-cover maximum therefore retains its default value 7, whereas
the exact packer retains its separate default `exact_max = 6`. Thus the argv
bytes differ in two pairs, but the sole semantic maximum difference is the
ordinary cap, 7 rather than 6. This distinction is intentional and is recorded
in the fresh run's exact argument vectors; the two runs must not be described
as byte-for-byte identical flag configurations.

The following available code paths are **inactive** in these proof-producing
runs and are not used to justify any rejection: `structural_cut_bounds`,
`late_t9a`, equality-profile pruning, parity-coherence pruning,
stronger-cover pruning, and the optimized exact-pack implementation. Merely
compiling their headers does not put them in the proof path.

The whole-block implementation is deliberately one-sided. A proved
infeasibility may reject a child, but a component cap, operation budget, or
other `UNKNOWN` condition returns `possible=true`. Thus resource exhaustion
weakens pruning and increases search; it cannot manufacture a `ZERO` result by
discarding a branch. This policy is implemented in
`a2_multi_edge_exact_cover.hpp` and selected by the flags above.

Orbit reduction is a separate trusted implementation step, not another
mathematical pruner. `order18_topology_free_search.cpp` forms the exact
weighted rooted/component codes, sorts component codes, and retains a
canonical representative of each generated forest orbit. The final-five
wrapper is `g001_remaining_witness_solver.cpp`; the Configuration 3 engine is
the separately pinned `a2_topology_free_search.cpp`. Correctness of these
canonical encodings and of representative retention remains in the trusted
computational base.

Terminal acceptance is separate again. Only after 17 physical edges does the
solver treat the forest as a complete 18-vertex tree; the terminal validity
test requires all 153 distances to be distinct and in `1,...,153`, hence to be
exactly that spectrum. A reported candidate is not a pruning event and must go
through the independently built witness checker in the final-five workflow.

Relevant compiled source inventory is
`order18_topology_free_search.cpp`, `g001_remaining_witness_solver.cpp`,
`a2_topology_free_search.cpp`, and `a2_multi_edge_exact_cover.hpp`. The
inactive alternatives are housed in
`a2_multi_edge_exact_cover_optimized.hpp`,
`a2_multi_edge_stronger_relaxation.hpp`, and
`multi_edge_parity_coherence.hpp`; their frozen hashes are checked, but their
presence is not evidence that they ran.
In the pinned copies, the final-five recursive gate is at
`g001_remaining_witness_solver.cpp:421` (through the cover gate beginning at
line 448), with `candidate_cross_ok` applied at line 571 and its flag parser
at lines 673-715. The A2 counterparts are
`a2_topology_free_search.cpp:415` (through line 441), line 542, and lines
703-719. The ordinary-cover cap and exact cap/budget fail-open returns are in
`a2_multi_edge_exact_cover.hpp:509-579`. These line references identify the
hash-pinned source snapshots; they are not a claim that those implementations
have been translated into Lean.

This is a conventional proof about the documented algorithm. Correct
implementation of enumeration, canonicalization, pruning, and recursion
remains in the trusted computational base.

## 5. Exhaustive evidence

The frozen final-five plan has SHA-256
`b317a3b7cef71e11fea762ce5e70322f168e06c6e04b97293f066cb2e313bdae`.
It contains 39,000 terminal searches and 30 separately certified-zero records
in 192 bundles. The frozen global JSON has SHA-256
`8c915a2ad6d6957740eb97bafb734603d59b5c0376704fd311ebfa6cb27d0eb5`
and status `GLOBAL_ZERO_COMPLETE`.

| Configuration | Complete pieces | Reported node visits | Evidence |
|---:|---:|---:|---|
| 1 | 5,176 terminal searches | 1,321,606,123 | final global collection |
| 2 | 79 partitions | 193,281,350 | row-1 certificate and strict verifier |
| 3 | 47 partitions | 167,742,832 | strict A2 ledger plus required fresh raw-receipt verification |
| 4 | 1,294 searches plus 30 certified zeros | 225,016,655 | final global collection |
| 5 | 25,254 terminal searches | 4,242,081,806 | final global collection |
| 6 | 3,977 terminal searches | 1,165,724,514 | final global collection |
| 7 | 3,299 terminal searches | 1,010,043,681 | final global collection |
| 8 | 52 partitions | 239,702,053 | row-7 certificate and strict verifier |

Total reported node visits are `8,565,199,014`. They include repeated prefix
work and are not a count of globally unique states.

The exact earlier-certificate SHA-256 identities are recorded in
`HYBRID_PROOF_RECORD.json`. The one-command verifier checks those bytes, runs
all three preserved coverage scripts, verifies the 28-file final source
freeze, requires the frozen Terminal5 source test's exact 47-check result,
reconstructs the Terminal5 plan from the two sealed calibration archives and
compares all 195 generated files byte-for-byte with the frozen plan, then
verifies that plan, strictly audits the incomplete historical A2 archive,
requires the pinned relocatable Config3 release, and replays the final-five
global collector to a byte-identical 1,434-byte JSON record. The guarded fresh
Config3 run completed 46 logical partitions directly; its last parent was
guard-stopped and is represented by a separately censused complete child
fan-out. The obsolete direct-47 release schema is not proof evidence. The
released replacement has the distinct
`config3-a2-frozen-split-release-v1` schema and is accepted only at the fixed
package path `config3_repair/evidence/full_preserved_v1/`.

The completed census has fan-out `M = 22`; the replacement roster is exactly
`k = 0,...,21`. The children report 42,848,972 node calls and satisfy
`parent_nodes = sum_k child_nodes[k] - 63 = 42,848,909`, accounting for the
three shared recursive calls at edge depths 4, 5, and 6. The frontier census
establishes the roster only; each of the 22 children has its own observed
`ZERO` result. The 46 direct searches report 124,893,923 calls, so direct plus
normalized parent calls reproduce the ledger total 167,742,832 exactly.

The Config3 root record carries the exact ordered 47-logical-partition roster,
replacement-child roster, census and normalized node-accounting identity,
source/plan/binary/fan-out bindings, digest-and-byte provenance, and no host
paths. The release contains exactly 281 files in 73 directories including its
root. Its 280-line sorted LF manifest covers `RELEASE.json`, `RUN_RESULT.json`,
their sidecars, and every canonical relative receipt/sidecar/raw stdout/stderr
byte, excluding only the manifest itself. The independent frozen-evidence
verifier strictly parses and reparses every record and stdout, requires
observed exit zero and result `ZERO`, empty stderr, the exact plain single-link
tree, and a final rehash after semantic checks. The end-to-end stage is named
`config3_a2_frozen_split_strict`; it requires the verifier's sole exact line to
bind the schema and the manifest, release, and run-result digests. No final
proof dependency points into the transient `.run` construction tree.

## 6. End-to-end contradiction

Assume an order-18 Leech tree exists.

1. `firstEdge_eightRowDossier` places its first physical edges in at least one
   of the eight rows in Section 3.
2. The search-completeness induction places a completion of that row in a
   certified recursive piece.
3. Sound necessary-condition filters cannot discard the genuine completion.
4. The corresponding preserved coverage verifier reports every required
   piece complete and `ZERO`; the final-five collector additionally requires
   no timeout, missing receipt, malformed result, or unchecked candidate.
5. This contradicts the surviving completion from steps 1-3.

Therefore no order-18 Leech tree exists, subject to the trusted-code boundary
below.

## 7. Reproducibility and trust boundary

Run `verify_end_to_end.ps1` as documented in `README.md`. Its final full marker
is emitted only after all eight configurations, the formal boundary, the
critical hashes, and the byte-identical final global recollection pass.

Before launching Lean or a frozen verifier, the package-local checker requires
the exact Lake-manifest dependency-directory set, the pinned revision and a
clean worktree for every dependency, exact frozen-source maps in both retained
source copies, and all 1,078 files under the independently pinned prior-three
evidence manifest. The orchestrator then requires the complete normalized
stdout digest of each frozen evidence verifier rather than accepting a marker
substring alone. The Lean boundary audit accepts exactly two axiom reports and
the allowlist for each is exactly `propext`, `Classical.choice`, and
`Quot.sound`.

The semantic bridge is a separate mandatory gate. Its proof-record status is
`PASS`, with its source contract and deterministic fresh-baseline result
pinned. It consumes the same fresh clean-project Lean library just built by
the orchestrator, never a second prebuilt project cache. The wrapper must
produce the full replay marker as its
unique last line and a path-free, hash-pinned `RUN_RESULT.json` binding the
fresh dossier olean, the exact four-declaration axiom audit, all bridge sources
and pinned inputs, `lean_elaboration_threads = 1`, eight fresh bridge oleans,
and every inner stdout/stderr
log. Each of those four reports must use only `Classical.choice`, `Quot.sound`,
and `propext`, and their union must equal that exact allowlist. The gate does
not preassign an exact subset to each individual declaration; the pinned full
checker stdout hash binds the four subsets actually reported. A static-only
marker cannot satisfy this gate. This checks the descriptor
bridge; it does not replace the constructive relabeling and trusted
orbit/partition transport argument in Sections 3–4.

The plan-selection completeness check is distinct from the later plan
validator. The frozen `make_g001_terminal5_plan_v1.py` first checks the exact
hash and size of the sealed C157 and Configuration-4 archives, stream-compares
each safe archive member with the exact extracted package tree, checks package
anchors, replays the two calibration packages, reconstructs the prefix-free
record set and deterministic bundle assignment, and binds the sealed runtime.
The package-local comparator then requires the regenerated and frozen plan
trees to have exactly one bundle directory and 195 regular single-link files,
and compares every file both by SHA-256 and by bytes. This rederives the
published plan from the preserved calibration outputs; it does not rerun the
calibration searches or independently verify the calibration-package replay
code.

The frozen Terminal5 source suite is also required to emit exactly
`PASS test_g001_terminal5_v1 checks=47` with empty stderr. The separate
remaining-leaf pipeline test is POSIX-only, reports `SKIP` on Windows, and is
not represented as a passing Windows check.

The orchestrator also rebuilds the eight-hash-pinned frozen C++ source closure
with the selected local C++20 compiler. It requires 45 solver regression checks
and 11 independent-checker self-tests and records the compiler, flags, binary
hashes, and logs, then rehashes the source, driver executable, and binaries.
Compiler include/library and dynamic-loader injection variables are removed,
and the generated binary/log/report tree must have the exact expected shape
before its manifest is written.
This tests the frozen source under a current compiler; it does not reproduce
the unavailable historical production binary, and the driver's subordinate
assembler/linker/runtime components remain trusted host tooling.

For the formal layer, `git archive` extracts the exact pinned commit into the
run directory. Before any cache junction is created, the verifier requires
the complete extracted regular-file set and every raw Git blob hash to equal
the pinned commit. Lake then builds every project `LeechTrees` olean fresh
from that archive with rehashed inputs and offline dependency resolution.
Only the pinned, clean dependency checkouts and their pre-existing build
caches are junctioned into the temporary project. Thus old project oleans
cannot be reused or shadow the fresh library, while dependency oleans and the
Lean toolchain remain an explicit cache/toolchain trust boundary.

Each normally terminating run records a package-manifest hash, result status,
timestamps, and an outer transcript in its unique `.run/` directory. These
controls prevent an unpinned verifier, dirty dependency, unexpected package
module, or misleading extra verifier output from silently producing the final
marker. Before that marker, the complete read-only identity audit and package
manifest verification run a second time, and the ending manifest hash must
equal the starting hash. These controls do not make the trusted production
computation into a Lean proof.

The clean Lake project rebuild runs as `lake --rehash --offline build`. Pinned
Lake 5.0.0 has no build-job-count command-line option, so the wrapper sets the
supported Lean runtime control `LEAN_NUM_THREADS=1` for Lake's task scheduler
and its Lean subprocesses; the outer `RUN_RESULT.txt` records
`LEAN_NUM_THREADS 1`. Every direct Lean elaboration launched by the outer or
semantic wrapper also runs with `-j 1`; the outer result records
`LEAN_ELABORATION_THREADS 1`, and the semantic bridge report separately records
`lean_elaboration_threads = 1`. These are
resource-scheduling controls only and do not alter theorem statements, axioms,
or proof semantics. The `--version` probes do not elaborate source files and
therefore do not take a thread flag.

For publication, `export_verification_release.py` accepts only a successful
full-global replay and deterministically exports its sanitized transcript,
machine-readable result, exact input source manifest, per-stage digest
summary, and the path-free semantic-bridge run result to a sibling release
tree. That tree has a separate
`RELEASE_MANIFEST.sha256`; it is deliberately not inserted into the source
package that the run already attested. `verify_verification_release.py`
rehashes every released byte, byte-compares the released input manifest with
the supplied source-package manifest, requires its digest to equal both the
start and end manifest fields in `RUN_RESULT.txt`, and verifies the released
transcript digest, stage-log-manifest digest, result digests, and exact
terminal marker. It also rehashes and strictly cross-binds the source package's
canonical Config3 release/run result/manifest and sidecars to the hybrid record
and outer run result. This avoids both the
excluded-`.run` publication gap and a circular post-export full rerun.
The release validator also requires the exact 24-stage full-replay roster;
omitting either the frozen Config3 verification or semantic-bridge replay is a
hard failure. Raw stage logs remain in the local run tree, while the released
stage manifest and canonical summary bind every raw stream by byte count,
raw SHA-256, and normalized-text SHA-256.
Because those raw streams and the unsanitized transcript are deliberately not
released, their hashes and the redaction mapping remain assertions made by
the pinned exporter after it rehashes the local run tree. The lightweight
validator cannot independently recompute those two mappings; it authenticates
the released assertions only relative to the required externally retained
release-manifest hash. The included semantic report is deterministic under
the pinned PowerShell serializer and is not described as a
language-independent canonical JSON encoding. Its eight inner oleans and 22
inner logs are rehashed by the exporter but are not copied; their reported
hashes therefore have the same explicit exporter-assertion boundary.
The exporter and release validator do independently rehash the 12 bridge
sources and all 14 repository inputs consumed by explicit-fresh mode. The
recorded standalone prebuilt dossier olean is intentionally unused in that
mode; the fresh dossier olean is bound by the semantic and outer run results,
but its omitted bytes remain part of the same exporter-assertion boundary.
The exporter also revalidates the exact runtime-source tree and 16-entry inner
manifest, the exact regenerated 195-file plan tree and 193-entry inner
manifest, the clean-project archive, and the fresh dossier olean immediately
before publication. Seven path-free role/path/result-field/digest bindings and
both inner-manifest entry counts are retained in the canonical stage summary.
The lightweight validator authenticates those bindings against
`RUN_RESULT.txt`; because the underlying run-local bytes are not copied, this
remains an exporter assertion rather than an independent second rehash.
Python verifier entrypoints ignore environment import paths and site packages,
Git identity checks ignore ambient Git configuration/injection variables, and
the selected host-tool executable hashes are retained. The local record/
checker/manifest pins are tamper evidence relative to the externally reported
manifest hash, not a signature or independent timestamp. Both the exporter
and independent release validator print that separate release-manifest hash;
publication requires retaining it outside the trees it identifies.

Trusted elements beyond the Lean kernel and its standard axioms are:

- the conventional search-completeness and whole-block arguments above;
- the frozen calibration-package replay/export and deterministic plan-builder
  implementations, plus the correctness and preservation of the sealed C157
  and Configuration-4 calibration outputs;
- the frozen C++ solver and its orbit/canonicalization implementation;
- the production compiler/runtime behavior;
- the selected local compiler/runtime used for the source regression rebuild;
- the pinned Lean dependency build caches and Lean toolchain executable;
- the Python and PowerShell coverage/collection code and selected host
  interpreters;
- the selected Git, archive, OS, and filesystem implementations;
- correct preservation of raw evidence and filesystem reads.

Known archival limitations are retained rather than hidden:

- Configuration 3 has no available complete *historical* raw process bundle
  for its 47 partitions; its legacy
  certificate documents one inferred exit code and its old verifier permits
  extra rows. The current wrapper does not accept those facts alone: it
  requires the exact logical roster in a fixed relocatable release, with the
  guard-stopped parent replaced by a complete censused child roster, observed
  zero exits, empty stderr, exact normalized node reconstruction,
  raw-byte-bound canonical receipts, and record-pinned
  release/run-result/manifest hashes. The new evidence is fresh replay
  evidence; it does not retroactively reconstruct the missing historical raw
  archive.
- The exact historical global-collector shell transcript is absent. The
  pinned relocation adapter replays the frozen collector and requires exact
  output bytes, but is not an independent exhaustive-search verifier.
- The original production compiler executable, complete version output, and
  exact Python version were not preserved.
- The local C++ source rebuild and tests do not establish binary identity with
  the historical GCC 12 production executable.
- The workflow verifies preserved evidence. It does not re-run the production
  search and does not turn the computational result into a Lean theorem.
