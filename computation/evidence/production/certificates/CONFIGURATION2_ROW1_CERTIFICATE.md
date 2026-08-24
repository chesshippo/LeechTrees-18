# Order-18 G001 row-1 exhaustive ZERO certificate

Status date: 2026-08-16

> **Final computational status.** All 79 certified partitions terminated
> `ZERO` with solver exit code 0. The strict coverage verifier succeeded, and
> the source, executable, plan, profile evidence, ledger, verifier transcript,
> certificate, and selected raw artifacts are frozen by SHA-256.

## Conclusion and exact scope

The completed computation supports the following statement:

> Conditional on the supplied Lean-verified G001 structural reduction and
> the correctness and completeness of the audited C++ search model, no
> order-18 Leech tree realizes G001 row 1 under the project's current
> zero-based row convention.

This is a **conditional computer-assisted branch exclusion**. It is not a
Lean theorem, the C++ program and its execution have not been formalized in
Lean, and it does not eliminate any other G001 row. In particular, this
certificate does not prove full order-18 nonexistence. Lean verification of
the computational layer is a separate workstream.

## Mathematical object and row-1 seed

Let `T=(V,E,w)` be a finite simple tree with strictly positive integral edge
weights. Put `n=|V|` and `N=binom(n,2)`. A Leech tree is one for which
weighted path distance is a bijection

```text
{unordered pairs of distinct vertices} -> {1,2,...,N}.
```

At order 18, `n=18` and `N=153`, so every distance rank from 1 through 153
must occur exactly once.

The supplied eight-row G001 structural classification is reported
Lean-verified. In zero-based G001 row 1, the physical weight-1 and weight-2
edges meet, while the physical weight-4 edge meets the weight-1 edge but not
the weight-2 edge. Up to weighted-tree isomorphism, its unique three-edge
seed is

```text
v0 --4-- v1 --1-- v2 --2-- v3.
```

Its six internal pair distances are `{1,2,3,4,5,7}`. The forced-MEX theorem
therefore requires physical weight 6 next. Ranks 5 and 7 are already
composite path distances, not physical edges in this seed. The source stores
the three physical edges in increasing weight order:

```cpp
s.add_edge(1,2,1);
s.add_edge(2,3,2);
s.add_edge(0,1,4);
```

There are exactly three canonical possibilities for the weight-6 edge:

1. attach a new endpoint at `v0`, the outer endpoint of weight 4;
2. attach a new endpoint at `v3`, the outer endpoint of weight 2; or
3. create a separate weight-6 two-vertex component.

Attachment at either internal seed vertex repeats the already used distance
7. The three valid roots have next-MEX distribution `8:2,10:1`; in the
solver's deterministic canonical order they are roots 0, 1, and 2, whose
next fan-outs are exactly `2,4,10`. Root and path indices are deterministic
partition labels, not additional mathematical restrictions.

## Exhaustive topology-free search model

The solver exposes physical edges in increasing forced-MEX order. At each
prefix the exposed graph is a weighted forest, with every unused vertex
treated as a singleton component. It performs these operations:

1. recompute every distance internal to each current component;
2. reject a repeated internal distance or a rank outside `1..153`;
3. set the next physical weight to the least positive rank missing from the
   internal-distance set;
4. enumerate every pair of distinct components and all attachment ports,
   modulo exact weighted-tree automorphisms represented by canonical rooted
   and unrooted codes;
5. add the forced-weight edge and compute its complete cross-distance block,
   rejecting a collision or out-of-range rank;
6. apply the necessary order-18 `7|11` parity-profile test and the necessary
   bound that a simple path has at most 14 physical edges;
7. apply the separately toggleable whole-block exact-cover condition below;
   and
8. at 17 physical edges, accept only if the next MEX is 154, which means the
   153 final pair distances are exactly `1..153`.

The forced-MEX step is complete under the positive-integral-weight model. A
future physical edge weight is itself a future pair distance, so it cannot
repeat a smaller rank already present. Conversely, the least missing rank
cannot first be produced by a path of two or more still-larger positive
edges. Therefore every completion has the forced next physical weight.

The conclusion remains conditional on correct implementation of this
argument and the complete enumeration, including distance analysis,
canonical orbit reduction, active necessary conditions, recursion, branch
selection, and result reporting.

No production partition used `--max-nodes` or `--stop-edges`. `ZERO` counts
as branch-closing evidence only when the selected recursive subtree
exhausts, emits one valid terminal `RESULT`, and exits 0. `FOUND`, `LIMIT`, a
nonzero exit, missing terminal metadata, nonempty stderr, or abnormal
termination would not close a branch.

## Sound whole-block exact-cover condition

Let a valid prefix forest have components `K_1,...,K_m`, and let `H` be the
set of ranks in `1..153` not already used by distances internal to those
components. If a completion exists, then for every unordered component pair
`i<j`, its unique final intercomponent path has a first port `u` in `K_i`, a
last port `v` in `K_j`, and a positive integral port-to-port length `L`. The
completion induces the indexed block

```text
B_ij(u,v,L) = {
  d_i(x,u) + L + d_j(v,y) : x in K_i, y in K_j
}.
```

Every genuine completion satisfies:

- `B_ij` has exactly `|K_i|*|K_j|` distinct ranks;
- all its ranks lie in `H`;
- blocks for different component pairs are disjoint; and
- their sizes sum to `|H|`, because

  ```text
  sum(i<j) |K_i|*|K_j|
    = binom(18,2) - sum(i) binom(|K_i|,2).
  ```

The checker enumerates all port pairs and positive translations that make a
complete injective block inside `H`. A component pair with no candidate
proves the prefix impossible. When exact search is attempted, exhaustive
failure to choose one pairwise-disjoint block for every component pair also
proves impossibility. The converse is not claimed: a passing block selection
need not be simultaneously realizable by one tree. This layer is a sound
necessary-condition filter, not a construction theorem.

The exact production flags were

```text
--multi-edge-cover
--multi-edge-cover-no-hall
--multi-edge-cover-max-components 6
--multi-edge-cover-budget 100
--multi-edge-cover-no-exact-hall
```

Their operational meaning is important:

- at 7--9 components, only the inexpensive requirement that every component
  pair has at least one candidate block is used;
- complete candidate construction and exact disjoint-block search occur only
  at six or fewer components;
- initial capacitated Hall and residual exact-search Hall checks are disabled,
  which can only weaken pruning;
- the exact search has a 100-state budget at each checked prefix;
- budget exhaustion returns `UNKNOWN/PASS`, never rejection;
- the default cap is 50,000 complete candidate patterns, and exceeding it
  returns `UNKNOWN/PASS`, never rejection; and
- prefixes outside the configured thresholds are skipped/passed.

The strict verifier hash-pins the exact-cover header and checks that both
resource-exhaustion branches still return `exact_unknown` with
`possible=true`. A resource limit in this layer therefore cannot manufacture
`ZERO`.

No structural-cut, late-T9a, parity-coherence, indexed-Hall or
self-puncturing, optimized-packing, stronger-relaxation, or empirical cutoff
such as "third odd edge by 41" was active in any production leaf.

## Exact 79-partition cover

The frozen version-3 plan contains exactly these inclusive ranges:

```text
root_0, root_1,
path_2_0, ..., path_2_8,
path_2_9_0, ..., path_2_9_14,
path_2_9_15_0, ..., path_2_9_15_21,
path_2_9_15_22_0, ..., path_2_9_15_22_30.
```

This is `2 + 9 + 15 + 22 + 31 = 79` leaves. In selector notation, the same
set is

```text
root:0, root:1,
path:2,k                    for every k in 0..8,
path:2,9,k                  for every k in 0..14,
path:2,9,15,k               for every k in 0..21,
path:2,9,15,22,k            for every k in 0..30.
```

Independent shallow runs with the frozen executable establish these complete
canonical fan-outs:

| Parent prefix | Stop edges | Children | Additional check |
|---|---:|---:|---|
| three-edge seed | 4 | 3 | `child_max=3:3` |
| root 2 | 5 | 10 | `child_max=4:10` |
| path `2,9` | 6 | 16 | `child_max=5:16` |
| path `2,9,15` | 7 | 23 | `child_max=6:23` |
| path `2,9,15,22` | 8 | 31 | `child_max=7:31`; MEX `12:21,13:5,14:5` |

The plan keeps roots 0 and 1 whole. It replaces root 2 with all ten children,
but replaces child 9 with all sixteen of its children. It replaces that
parent's child 15 with all twenty-three children, then replaces child 22 of
that parent with all thirty-one children. Thus the displayed leaf set covers
all three roots. It is strictly prefix-free, so the selected recursive
descendant subtrees are pairwise disjoint.

Each process repeats its selected prefix. Consequently the aggregate node,
state, generated-attachment, and wall-time counters contain repeated prefix
work and are not counts of globally unique states. This does not affect
disjoint coverage of the descendant subtrees.

The plan CSV retains its historical metadata name
`G001-ROW1-COVER-v3-PROVISIONAL-20260816` and status
`PROVISIONAL_DEEP_SPLIT_PROFILE_PENDING`. The two separately frozen profile
confirmations below discharge that profile gate; the strict verifier requires
both before accepting the production ledger.

## Deep-split profile evidence

Both oversized-parent replacements were profiled in baseline and production
cover configurations to the same depth-12 frontier. The selected children
reproduce their parent frontiers exactly:

| Profile set | Parent selector | Children | Baseline parent / child sum | Cover parent / child sum |
|---|---|---:|---:|---:|
| `row1_split49_v1` | `path:2,9,15` | 23 | 1,552,327 / 1,552,327 | 689,509 / 689,509 |
| `row1_split79_v1` | `path:2,9,15,22` | 31 | 489,707 / 489,707 | 277,927 / 277,927 |

Node sums are deliberately not compared: separate child jobs revisit their
common parent prefix. Frontier counts at one fixed depth are the additive
partition metric.

For each child, its manifest binds nine files: baseline
stdout/stderr/done, cover stdout/stderr/done, profile CSV, append-only profile
log, and lock. The 23-child layer therefore binds 207 raw artifacts and the
31-child layer binds 279. The evidence verifier checks the complete child
sets, baseline/cover pairing, exact argv and hashes, `FRONTIER`, exit 0,
empty stderr, raw `RESULT` data, done metadata, completed locks, manifests,
and exact frontier sums.

The 23-child profile predates the final additional split. Its raw rows bind
the preceding plan hash
`7603A7D44363A8F4D299D0742AC09C44BF01CB2F63940508EE9C1402B8147750`
and fan-out hash
`D1B3B8EDCEDD8ABB248E3C34F5FF979BE1183FCE502B4B3C7CB937DA08C1D78B`.
Its confirmation preserves those raw bindings and connects them to the
current version-3 plan and verifier. The subsequent 31-child profile binds
the current version-3 plan and certifies the additional replacement of child
`2,9,15,22`. Together they establish the 79-leaf cover.

## Validation before the uncapped cover

The following implementation checks were completed:

- the seed produced one depth-3 state with MEX 6;
- its first fan-out was exactly three, with MEX distribution `8:2,10:1`;
- next fan-outs of roots 0, 1, and 2 were exactly `2,4,10`;
- known topology counts at orders 2 through 6 remained `1,1,2,0,1` with the
  exact-cover layer both off and on;
- exact cover was dormant through depth 8, where baseline and active counts
  were identical;
- depth-9 shadow mode retained every baseline state while recording 2,917
  states that active exact cover would reject;
- scalar candidate validation on row-1 path `0,0` through depth 12 reported
  `cover_validation_fail=0`;
- exact-cover unit and exhaustive small-order tests passed;
- established A2 depth-10 regressions remained 90,904 nodes for the separate
  case and 12,296 for the attached case;
- A2 attached selector `path:1,1` remained exhaustive `ZERO` with 32,841
  nodes; and
- the row-7 seed retained exactly five first-level children.

These are consistency checks, not a formal verification of the C++ program.

## Fixed-depth pruning benchmark

Before the uncapped cover, the same baseline and production-cover searches
were compared at fixed depth.

| Depth | Baseline nodes | Cover nodes | Node reduction | Baseline frontier | Cover frontier | Frontier reduction |
|---:|---:|---:|---:|---:|---:|---:|
| 9 | 19,270 | 19,270 | 0.00% | 16,310 | 13,393 | 17.88% |
| 10 | 139,520 | 123,262 | 11.65% | 120,250 | 88,255 | 26.61% |
| 11 | 1,111,290 | 901,710 | 18.86% | 971,477 | 612,732 | 36.93% |

At depth 12, roots 0 and 1 were measured whole and root 2 as its exact
ten-child partition, so both configurations used the same twelve subtrees:

```text
baseline: nodes=9,526,390 frontier=8,370,258 wall_sum=97.752631 s
cover:    nodes=7,021,940 frontier=2,402,179 wall_sum=3,100.288725 s
```

This reduced node visits by 26.289602% and the surviving frontier by
71.301016%. Summed process wall time was about 31.72 times baseline because
the exact condition is expensive; some jobs overlapped. The predefined gate
required at least 20% node reduction, at least 70% frontier reduction, and a
credible exact partition. It passed before the uncapped cover began. The
benchmark itself was not branch-closing evidence.

## Strict production verification

For every expected leaf, the final verifier checks the exact key/selector,
argv, executable/source hashes, `ZERO`, exit 0, positive search counters,
zero frontier, zero solutions, active exact cover, inactive experimental
layers, and `cover_validation_fail=0`. It requires one complete terminal
`RESULT` line and empty stderr.

It also reconstructs and cross-checks the selected stdout, stderr, PID,
atomic done, and worker files. PID metadata binds the worker PID, timestamp,
executable, source, and argv. Done metadata binds exit 0, positive wall time,
and an ordered end timestamp. The worker must exactly match the frozen
launcher template that writes `.done.tmp` and atomically moves it to
`.done.txt`; no residual temporary file may remain. Ledger counters must
match stdout, and ledger exit/wall values must match done metadata.

Before reading production rows, the verifier rechecks the exact 79-key
prefix-free plan, recomputes all five fan-outs with the frozen executable,
and invokes the separately hash-pinned profile-evidence verifier. Missing,
duplicate, unexpected, stale, malformed, or mismatched evidence causes a
failure; there is no partial-success state.

The final strict verifier emitted:

```text
FANOUT_OK label=seed frontier=3
FANOUT_OK label=root_2 frontier=10
FANOUT_OK label=path_2_9 frontier=16
FANOUT_OK label=path_2_9_15 frontier=23
FANOUT_OK label=path_2_9_15_22 frontier=31
PLAN_SHA256=3CAC29583013A86A5951CB85B846F634EFA9E5791C55D4A3D59EF9E65A68C316
FANOUT_SHA256=BCFA8A6AE25CEB7CCEC9597C7ABBEE9FF924060F8400DD09E47EAB2A33D4D58E
PLAN_ROWS=79 PREFIX_FREE=YES
PROFILE_EVIDENCE_OK label=layer23 children=23 baseline_frontier=1552327 cover_frontier=689509 artifacts=207
PROFILE_EVIDENCE_OK label=layer31 children=31 baseline_frontier=489707 cover_frontier=277927 artifacts=279
G001_ROW1_PROFILE_EVIDENCE_OK
EXPECTED=79 RECORDED=79
NODE_SUM=193281350 STATE_SUM=18371773 GENERATED_SUM=1919285935
WALL_SUM_SECONDS=38225.1631218
COVER_CHECKS_SUM=176180613 COVER_CANDIDATES_SUM=129637560780
COVER_REJECT_SUM=157808840
FAIL_OPEN_UNKNOWN_SUM=17654130
FAIL_OPEN_POLICY=budget_or_candidate_cap_means_UNKNOWN_AND_PASS
G001_ROW1_COVERAGE_OK
```

Final aggregate from `outputs/G001_ROW1_PARTITION_RESULTS.csv`:

| Partitions | Status | Node visits | Accepted states | Generated attachments | Summed process wall time (s) |
|---:|---|---:|---:|---:|---:|
| 79 | `ZERO` | 193,281,350 | 18,371,773 | 1,919,285,935 | 38,225.1631218 |

Additional aggregate exact-cover diagnostics:

| Cover checks | Candidate blocks | Proved cover rejections | Fail-open UNKNOWN returns |
|---:|---:|---:|---:|
| 176,180,613 | 129,637,560,780 | 157,808,840 | 17,654,130 |

`Proved cover rejections` is the sum of no-candidate and exact-cover-failure
returns. `Fail-open UNKNOWN returns` is the sum of exact-search budget and
candidate-cap exhaustion; each such event passed the prefix rather than
rejecting it. Aggregate visits, states, attachments, and wall time include
repeated prefix work. Summed process wall time is not elapsed batch time and
may count overlapping jobs.

Final integrity checks:

- [x] the expected key set equals the 79 recorded keys exactly;
- [x] all 79 leaves are `ZERO`, exit 0, with no solution topology or frontier;
- [x] each leaf has one exact `RESULT`, positive core counters, and empty
      stderr;
- [x] each PID/done/worker bundle binds the frozen source, executable, exact
      argv, times, exit, and raw result;
- [x] no production leaf activates an excluded layer or reports a candidate
      validation failure;
- [x] both profile-evidence layers reverify from 486 raw SHA-bound artifacts;
- [x] all five shallow fan-outs recompute and the 79 selectors are prefix-free;
- [x] the strict verifier exits 0 and prints `G001_ROW1_COVERAGE_OK`; and
- [x] the final SHA-256 manifest contains the exact selected 905-file evidence
      set and excludes smoke, stale, failed, active, and superseded files.

## Frozen provenance and integrity manifest

Core frozen hashes:

```text
5F50BEC4D18947680EE170BF22AF747D1E74EA203E34E305EAE27768439B46AD  work/a2_solver/order18_topology_free_search_row1.exe
134373D19AD4B1B1DFB30595F73BEABCEF30FA21C19B74A652669FB7705A72D9  work/a2_solver/order18_topology_free_search_row1_snapshot.cpp
C156EAE52BCEEF28DB0DF1A38D10DEA253DE09E5F627D0952A6BB1B9356CD813  work/a2_solver/a2_multi_edge_exact_cover.hpp
5320C920E800CE2F9E2348B90D672E26CDDD748B43BC02BC24B9146DEDB5E48B  work/a2_solver/a2_multi_edge_exact_cover_optimized.hpp
E58F917A631C48F2419835D41C2B0EE164F0D24F44BA489C152B9C00CDDBBD5C  work/a2_solver/a2_multi_edge_stronger_relaxation.hpp
AF09E37C9E50FB3891BB11BBFEAD6D5F8299200C7ABF81BC8049FB20A07D30C7  work/a2_solver/multi_edge_parity_coherence.hpp
3CAC29583013A86A5951CB85B846F634EFA9E5791C55D4A3D59EF9E65A68C316  outputs/G001_ROW1_PARTITION_PLAN_PROVISIONAL.csv
BCFA8A6AE25CEB7CCEC9597C7ABBEE9FF924060F8400DD09E47EAB2A33D4D58E  outputs/G001_ROW1_PARTITION_FANOUT_PROVISIONAL.csv
210BBF33D4E49B14365DFDE91E4DF23B31A1AE4F7BF093C292D4E2BED8AF1AC6  work/a2_solver/verify_g001_row1_partition_coverage.ps1
91296DDB7635C8D1683BE4F48B7976638FDDCC0D3BBD1E580040F2EF3969963F  work/a2_solver/verify_g001_row1_profile_evidence.ps1
F1A8F213BFA2C801271A2335087CA270BF6C4D3320810B67CC06CE0D77A0E171  outputs/G001_ROW1_PATH_2_9_15_PROFILE_CONFIRMATION.txt
3CA609DC570692F6B6FDF1E7AA825C6556396CF4206B480C5779F2B4FEB6C3A6  outputs/G001_ROW1_PATH_2_9_15_PROFILE_EVIDENCE_SHA256.txt
7D36C3CB6C4AEB71A7AFC1E87220D84C96AB5629B6794B38B4B11E0087154237  outputs/G001_ROW1_PATH_2_9_15_22_PROFILE_CONFIRMATION.txt
E2B4368E772EE31895DFCAB4E6DC41178155B02AAC4BAA2A3CBCF6122E0211CB  outputs/G001_ROW1_PATH_2_9_15_22_PROFILE_EVIDENCE_SHA256.txt
0D6B2843C8A17C3C917F5B1766E44DAB018D07C88373CBCECD72B19010FC8A15  outputs/G001_ROW1_PARTITION_RESULTS.csv
71C9D8B3E10C97B1F5D0D7AEEEF80A60D87CACDC46AA65EF5EBDD067862B5FF2  outputs/G001_ROW1_FINAL_COVERAGE_VERIFIER.txt
```

The final primary manifest is
`outputs/G001_ROW1_EXHAUSTIVE_ZERO_SHA256SUMS.txt`. It contains exactly 905
entries:

- 24 static/final files: executable, source, four headers, plan, fan-out,
  runner, collector, two verifiers, confirmation generator, two profile
  helpers, benchmark gate and CSV, two confirmations, two nested evidence
  manifests, final ledger, verifier transcript, and this certificate;
- 486 raw profile artifacts (`23*9 + 31*9`), taken exactly from the two nested
  profile manifests; and
- 395 production artifacts (`79*5`): the stdout, stderr, PID, done, and worker
  files selected by each exact ledger row.

The file set was derived from explicit frozen paths, the two nested evidence
manifests, and the 79 ledger rows. It contains no wildcard-selected smoke,
failed, stale, incomplete, aggregate-parent, or superseded run. The primary
manifest does not list itself. Because it includes this certificate, its own
SHA-256 is necessarily external release metadata rather than text embedded
inside the certificate.

## Reproduction and interpretation

From the workspace root, run:

```powershell
powershell.exe -NoProfile -ExecutionPolicy Bypass `
  -File .\work\a2_solver\verify_g001_row1_partition_coverage.ps1
```

The frozen record exits 0 and emits the literal success marker
`G001_ROW1_COVERAGE_OK`. The correct interpretation remains exactly the
conditional row-1-only exclusion stated at the beginning: G001 row 1 is
computationally exhausted under the audited model, while other G001 rows and
formal verification remain separate tasks.
