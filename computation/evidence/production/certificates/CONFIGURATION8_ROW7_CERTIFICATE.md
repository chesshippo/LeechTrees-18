# Order-18 G001 row-7 exhaustive ZERO certificate

Status date: 2026-08-16

> **Final computational status.** All 52 certified partitions terminated
> `ZERO` with solver exit code 0, the strict coverage verifier succeeded, and
> the source, executable, ledger, verifier, and selected raw artifacts have
> been frozen by SHA-256.

## Conclusion and exact scope

The completed computation supports the following statement:

> Conditional on the supplied Lean-verified G001 structural reduction and
> the correctness and completeness of the audited C++ search model, no
> order-18 Leech tree realizes G001 row 7 (using the project's current
> zero-based row convention).

This is a **conditional computer-assisted branch result**.  It is not itself
a Lean theorem, it does not formalize the C++ execution in Lean, and it does
not eliminate any of the other G001 rows.  Lean verification is a separate
workstream.  In particular, even a completed row-7 certificate must not be
reported as a full order-18 nonexistence theorem.

## Mathematical object and row-7 seed

Let `T=(V,E,w)` be a finite simple tree whose physical edges have strictly
positive integral weights.  Put `n=|V|` and `N=binom(n,2)`.  A **Leech tree**
is one for which weighted path distance gives a bijection

```text
{unordered pairs of distinct vertices}  ->  {1,2,...,N}.
```

At order 18, `n=18` and `N=153`; consequently every distance rank from 1
through 153 occurs exactly once.

The supplied G001 eight-row classification is reported Lean-verified.  G001
row 7 is its final displayed configuration under the current zero-based
naming convention.  The physical weight-1 and weight-2 edges are disjoint,
while the physical weight-3 edge meets both.  Up to weighted-tree
isomorphism, the unique three-edge seed is

```text
v0 --1-- v1 --3-- v2 --2-- v3.
```

Its six internal pair distances are exactly `1,2,3,4,5,6`.  The forced-MEX
theorem therefore makes 7 the next physical edge weight.  The weights 4, 5,
and 6 are already realized distances; they are not physical edges in this
seed.

The five canonical possibilities for the weight-7 edge are obtained by
attaching a new endpoint at one of the four seed vertices or by making the
weight-7 edge a separate two-vertex component.  The solver's independent
shallow enumeration gives exactly five orbit children, with next-MEX
distribution

```text
8: 3 children
9: 2 children.
```

The branch identifiers used below are deterministic indices in the solver's
canonical candidate order.  They are partition labels, not additional
mathematical restrictions.

## Exhaustive topology-free search model

The solver exposes physical edges in increasing weight order.  At every
prefix the exposed edges form a weighted forest, with unused vertices treated
as singleton components.  It then performs the following operations.

1. Recompute every distance internal to each current component.
2. Reject a prefix if an internal distance is repeated or lies outside
   `1..153`.
3. Set the next physical edge weight to the least positive rank absent from
   the internal-distance set.
4. Enumerate two distinct components and one attachment port in each, modulo
   exact weighted-tree automorphisms represented by canonical rooted and
   unrooted codes.
5. Add the forced-weight edge and compute its complete new cross-distance
   block exactly; reject any collision or out-of-range distance.
6. Apply the order-18 necessary `7|11` parity-profile test and the theorem
   that a simple path has at most 14 physical edges.
7. Apply the separately toggleable whole-block exact-cover restriction
   described below.
8. Accept a 17-edge tree only if its next MEX is 154, which means that its 153
   pair distances are exactly `1..153`.

The conclusion is conditional on the correctness of this enumeration,
canonical orbit reduction, active necessary conditions, and implementation.
No maximum node limit was used in a production partition.  Thus `ZERO` means
that the selected recursive subtree ended with no accepted topology;
`FOUND`, `LIMIT`, or an abnormal/nonzero process exit is not branch-closing
evidence.

## Sound whole-block exact-cover restriction

Let a valid prefix forest have components `K_1,...,K_m`, and let `H` be the
subset of `1..153` not yet used by distances internal to those components.
Suppose a Leech completion exists.  For each unordered component pair
`i<j`, the unique final path from `K_i` to `K_j` has a first port `u` in
`K_i`, a last port `v` in `K_j`, and positive weighted port-to-port length
`L`.  Its indexed distance block is

```text
B_ij(u,v,L) = {
  d_i(x,u) + L + d_j(v,y) : x in K_i, y in K_j
}.
```

Every genuine completion has all of the following properties:

- `B_ij` has exactly `|K_i|*|K_j|` distinct ranks;
- every member of `B_ij` lies in `H`;
- blocks belonging to different component pairs are disjoint; and
- the block cardinalities sum to `|H|`, since

  ```text
  sum(i<j) |K_i|*|K_j|
    = binom(18,2) - sum(i) binom(|K_i|,2).
  ```

Therefore a completion induces one candidate additive block for every
component pair, and those blocks exactly cover `H`.  The checker enumerates
all port pairs and all possible positive translations `L` whose complete
block is injective and lies in `H`.  If a component pair has no candidate, or
if an exhaustive selection proves that no pairwise-disjoint choice of one
block per component pair exists, then the prefix cannot be completed.

The converse is not claimed: a passing block selection may use ports and
route lengths that cannot coexist in one final tree.  The layer is a sound
necessary-condition filter, not a construction theorem by itself.

The exact production flags were

```text
--multi-edge-cover
--multi-edge-cover-no-hall
--multi-edge-cover-max-components 6
--multi-edge-cover-budget 100
--multi-edge-cover-no-exact-hall
```

Their operational meaning is important:

- at 7--9 components, only the inexpensive check that every component pair
  has at least one candidate block is used;
- full candidate construction starts at six components, and exact
  disjoint-block search is attempted when there are at most six components;
- both the initial capacitated Hall test and residual Hall calls inside the
  exact search are disabled; disabling them can only weaken pruning;
- the exact search receives a 100-state budget at each checked prefix;
- budget exhaustion returns `UNKNOWN/PASS`, never rejection;
- the default candidate cap is 50,000 complete block patterns, and exceeding
  it returns `UNKNOWN/PASS`; and
- prefixes outside the configured component thresholds are skipped/passed.

Consequently, every pruning return used by this layer is a proved
necessary-condition failure; resource limits cannot manufacture `ZERO`.

No parity-coherence experiment, structural-cut experiment, late-T9a
experiment, indexed-Hall/self-puncturing experiment, optimized-packing
experiment, or empirical cutoff such as "third odd edge by 41" was active in
the production partitions.

## Exact 52-partition cover

Independent shallow fan-out enumeration, performed before selecting the
production partitions, records the following complete canonical fan-outs in
`outputs/G001_ROW7_PARTITION_FANOUT.csv`:

```text
three-edge seed:        5 weight-7 root children
root children 0..4:     3, 3, 2, 2, 10 next-level children
path 4,9:               16 next-level children
path 4,9,15:            23 next-level children
```

The uncapped cover deliberately keeps roots 0--2 whole, splits root 3 into
its two children, splits root 4 into children 0--9, and splits the largest
child `4,9` once more into its sixteen children.  The aggregate job for the
largest of those, `4,9,15`, was terminated externally with no result, so it
is excluded and replaced by its 23 verified children.  The exact expected
key set is

```text
root_0, root_1, root_2,
path_3_0, path_3_1,
path_4_0, path_4_1, path_4_2, path_4_3, path_4_4,
path_4_5, path_4_6, path_4_7, path_4_8,
path_4_9_0, path_4_9_1, path_4_9_2, path_4_9_3,
path_4_9_4, path_4_9_5, path_4_9_6, path_4_9_7,
path_4_9_8, path_4_9_9, path_4_9_10, path_4_9_11,
path_4_9_12, path_4_9_13, path_4_9_14,
path_4_9_15_0, path_4_9_15_1, ..., path_4_9_15_22.
```

This is `3 + 2 + 9 + 15 + 23 = 52` disjoint recursive subtrees.  It covers
all five roots: root 3 is replaced by exactly its two children; root 4 is
replaced by children 0--8 and the sixteen children that exactly replace child
9; and child `4,9,15` is in turn replaced by exactly its 23 children.  Parent
prefixes are repeated across processes, so summed node visits are not a count
of globally unique states; the partitioned descendant subtrees are
nevertheless disjoint.

The strict verifier `work/a2_solver/verify_g001_row7_partition_coverage.ps1`
recomputes the shallow fan-outs with the frozen production executable, checks
the certified fan-out CSV, and rejects duplicate, missing, or unexpected
ledger keys.  For every expected row it verifies the exact selector and
production arguments, the hard-coded executable SHA-256, status `ZERO`, exit
code 0, zero solution topologies, empty stderr, and positive node count.  It
also binds ledger nodes/states/generated counters to the raw `RESULT` line and
ledger exit/time values to the raw `.done.txt` artifact.  Artifact paths are
workspace-relative so the package remains portable after extraction.

## Validation before the uncapped cover

The following implementation checks were completed before the production
partition runs:

- the three-edge row-7 seed produced one state with MEX 7;
- its first fan-out produced exactly five canonical children and the
  `8:3,9:2` MEX distribution above;
- the next-level child counts were exactly `[3,3,2,2,10]`, path `4,9` had
  exactly 16 children, and path `4,9,15` had exactly 23 children;
- exhaustive topology counts at orders 2 through 6 remained
  `1,1,2,0,1` with the exact-cover layer both off and on;
- the established A2 attached partition `branch-path 1,1` was reproduced as
  `ZERO` with exactly 32,841 nodes; and
- previously recorded A2 depth-10 regressions also matched.

These are strong consistency checks, but they do not replace formal proof of
the implementation or verification of the compiled binary.

## Fixed-depth pruning benchmark

The full data are in `outputs/G001_ROW7_BENCHMARK.csv`.  Before any uncapped
cover was attempted, the same baseline search and the production exact-cover
configuration were compared at fixed depths.

| Scope | Metric | Baseline | Exact cover | Reduction |
|---|---|---:|---:|---:|
| depth 9, all roots | nodes | 24,120 | 24,120 | 0.00% |
| depth 9, all roots | frontier | 20,396 | 16,376 | 19.71% |
| depth 10, all roots | nodes | 174,419 | 151,125 | 13.36% |
| depth 10, all roots | frontier | 150,299 | 107,982 | 28.16% |
| depth 11, all roots | nodes | 1,371,847 | 1,096,149 | 20.10% |
| depth 11, all roots | frontier | 1,196,935 | 746,417 | 37.64% |
| depth 12, roots 0--3 | nodes | 3,873,238 | 2,919,641 | 24.62% |
| depth 12, roots 0--3 | frontier | 3,390,564 | 754,892 | 77.74% |

At depth 11, observed wall time was about 10.7 seconds for baseline and 18.7
seconds with exact cover.  For the four depth-12 roots, summed observed
process wall times were 37.85 and 919.14 seconds respectively, about 24.28
times slower with the layer.  Some runs overlapped, so these sums are not
batch elapsed time.  The benchmark justified the pruning gate but also
motivated splitting the expensive fifth root.

The aggregate root-4 cover benchmark was manually interrupted and supplies
no `ZERO`, `LIMIT`, or other branch evidence.  Its baseline depth-12 frontier
was 6,826,517.  Independent child profiling showed that child `4,9` accounted
for 3,695,647 states, or 54.14% of that frontier, leading to the certified
two-level split above.

## Excluded root-3 aggregate run

An earlier uncapped aggregate root-3 run printed

```text
status=ZERO  nodes=13375507  wall_seconds=2853.690544
```

and its solver stderr was empty.  After the solver returned, however, its
custom wrapper failed while appending terminal metadata and preserved wrapper
exit 125 instead of a captured solver exit code.  That run is deliberately
excluded from the authoritative ledger and from every aggregate.  The exact
fan-out for root 3 is two, so clean durable runs `path_3_0` and `path_3_1`
replace it completely.  No conclusion depends on the defective wrapper run.

## Excluded path-4,9,15 aggregate run

The first aggregate `path_4_9_15` process accumulated substantial CPU time
but then both solver and wrapper terminated without a `.done.txt` file or a
terminal `RESULT`; stdout and stderr were empty.  It is abnormal, supplies no
evidence, and is excluded from the ledger and every aggregate.  A fresh
shallow production-binary run proved that this prefix has exactly 23
canonical children (`child_max=6:23`).  Clean durable jobs
`path_4_9_15_0` through `path_4_9_15_22` replace it completely.

An initial batch-launch timeout also invalidated the first attempts for split
children 0, 1, 3, 4, 5, and 6.  Those incomplete launch artifacts are
excluded.  Each affected child was rerun individually and only its clean
retryâ€”with a terminal `ZERO`, captured solver exit 0, and empty stderrâ€”is
selected by the final ledger and manifest.  Child 2 had already completed
cleanly and required no retry.

## Final verified computation

The strict verifier emitted:

```text
EXPECTED=52 RECORDED=52
NODE_SUM=239702053 STATE_SUM=22164366 GENERATED_SUM=2313945375
WALL_SUM_SECONDS=50825.498268
G001_ROW7_COVERAGE_OK
```

Final aggregate from `outputs/G001_ROW7_PARTITION_RESULTS.csv`:

| Partitions | Status | Node visits | Accepted states | Generated attachments | Summed process wall time (s) |
|---:|---|---:|---:|---:|---:|
| 52 | `ZERO` | 239,702,053 | 22,164,366 | 2,313,945,375 | 50,825.498268 |

`Node visits`, `accepted states`, and `generated attachments` are sums of
per-process counters and include repeated selected-prefix work.  Summed wall
time also counts overlapping processes and is not elapsed batch time.

Final integrity checks:

- [x] expected key set equals the 52 recorded keys exactly;
- [x] every partition is `ZERO`, exit 0, with zero solution topologies;
- [x] every partition has a positive node count and exactly one terminal
      row-7 `RESULT` line;
- [x] every production stderr file is empty;
- [x] every ledger row has one identical solver SHA-256;
- [x] the strict verifier exits 0 and prints `G001_ROW7_COVERAGE_OK`;
- [x] a frozen SHA-256 manifest covers the solver, source/header snapshot,
      ledger, fan-out certificate, scripts, and raw job artifacts.

## Provenance and frozen hashes

The production jobs are expected to use this frozen executable:

```text
9F894F39EFB71E9C8506E5C5B312289B1D3BEFE95C95B911DF8613F2E24BAFFB
work/a2_solver/order18_topology_free_search.exe
```

The exact production source has been recovered and frozen as

```text
47183D7B30132BB5E6CC5039BC592EB90B900E8124C08DF6ED31EA61B689E2CC
work/a2_solver/order18_topology_free_search_production_snapshot.cpp
```

A fresh `g++ 14.2.0 -O2 -std=c++20 -Wall -Wextra -Wpedantic` rebuild had the
same 360,779-byte size and differed from the production executable only at
six PE timestamp/checksum bytes; the other 360,773 bytes were identical.  It
also reproduced every shallow row-7 check, the small-order counts, and the A2
32,841-node regression.  Full details are in
`outputs/G001_ROW7_PRODUCTION_SOURCE_PROVENANCE.md`.

The final manifest is
`outputs/G001_ROW7_EXHAUSTIVE_ZERO_SHA256SUMS.txt`.  It contains 281 entries:
260 raw files selected from the 52 ledger rows and 21 frozen static
artifacts.  Failed, experimental, smoke-test, and superseded runs are not in
the manifest.

```text
production executable:  9F894F39EFB71E9C8506E5C5B312289B1D3BEFE95C95B911DF8613F2E24BAFFB
production source:      47183D7B30132BB5E6CC5039BC592EB90B900E8124C08DF6ED31EA61B689E2CC
exact-cover header:     C156EAE52BCEEF28DB0DF1A38D10DEA253DE09E5F627D0952A6BB1B9356CD813
optimized header:       5320C920E800CE2F9E2348B90D672E26CDDD748B43BC02BC24B9146DEDB5E48B
stronger header:        E58F917A631C48F2419835D41C2B0EE164F0D24F44BA489C152B9C00CDDBBD5C
partition ledger:       830DA5B5A96522D8F776D4510FAEF4E04218554E54580DF496B6ECA105A69CB9
fan-out certificate:    992674C8169F6533E88891471218864690B399027B9FA3D8D7F94C103FA9DD76
coverage verifier:      095424ECAD1CA994B96B4CFD7F0440645D8083B61352D3C51B25D3490448C1A5
manifest SHA-256:       CF9F98E489A41A3608628C77BDBCE2B72CCCFC0FA1B714C5FC8165A9CF6888F4
```

## Reproduction command and interpretation

Run the final coverage check from the workspace root:

```powershell
powershell.exe -NoProfile -ExecutionPolicy Bypass `
  -File .\work\a2_solver\verify_g001_row7_partition_coverage.ps1
```

The archived run exits 0 and emits the literal success marker shown above.
The correct interpretation remains: this is a conditional computer-assisted
exclusion of G001 row 7, pending separate Lean formalization and not covering
the remaining G001 branches.
