# Order-18 A2 exhaustive ZERO certificate

## Conclusion

The topology-free order-18 solver exhaustively closes both A2 configurations:

- attached weight-5 configuration: `ZERO`;
- separate weight-5 configuration: `ZERO`.

Thus there is no order-18 Leech tree in branch A2, conditional on the
Lean-verified A2 structural reductions supplied to the project and the exact
solver model audited here.  This is a computer-assisted A2 impossibility
result.  It is not a result for order-18 branches outside A2, and the new
multi-edge theorem has not yet been formalized in Lean.

## Sound pruning layer

For every pair of current connected components `K_i,K_j`, any completion
induces a translated rooted-distance block

```text
{ d_i(x,u) + L + d_j(v,y) : x in K_i, y in K_j }.
```

The block must be injective, lie in the currently missing ranks, and be
disjoint from every other current-component-pair block.  The block sizes sum
to the number of missing ranks, so the blocks form an exact cover.  Failure
of whole-block packing is therefore a necessary-condition failure and a
sound prune.  Every search-budget exhaustion is fail-open (`UNKNOWN/PASS`).

The branch-closing runs used only this separately toggleable configuration:

```text
--multi-edge-cover
--multi-edge-cover-no-hall
--multi-edge-cover-budget 100
--multi-edge-cover-no-exact-hall
```

Disabling the Hall calls weakens pruning only.  No experimental or
unverified rule such as "third odd edge by 41" was used.

## Exact partition coverage

An independent unfiltered fan-out audit established:

- attached: 2 roots; root 1 has exactly 6 valid children;
- separate: 9 roots with depth-5 child counts
  `[1,2,1,4,6,5,2,8,15]` for roots 0 through 8.

The exhaustive cover is therefore:

- attached: `root_0`, plus `path_1_0` through `path_1_5`;
- separate: `root_0` through `root_3`, then
  `path_4_0..5`, `path_5_0..4`, `path_6_0..1`,
  `path_7_0..7`, and `path_8_0..14`.

Every one of these 47 partitions returned `ZERO`, with exit code 0.
The coverage checker reports:

```text
EXPECTED_PARTITIONS=47
RECORDED_PARTITIONS=47
ATTACHED_NODES=17650190
SEPARATE_NODES=150092642
STATUS=COVERAGE_OK ALL_EXPECTED_PARTITIONS_ZERO
```

The total reported work is `167,742,832` solver node visits.  This is a sum
over independently launched partitions and therefore includes repeated
prefix work; it is not a count of globally unique states.

## Result totals

| Case | Partitions | Status | Node visits | Summed recorded wall time (s) |
|---|---:|---|---:|---:|
| Attached | 7 | ZERO | 17,650,190 | 2,269.8161381 |
| Separate | 40 | ZERO | 150,092,642 | 43,265.2712488 |
| Combined | 47 | ZERO | 167,742,832 | 45,535.0873869 |

The wall-time column sums per-process measurements.  Runs overlapped, so it
is not elapsed batch time.  It also includes `23,032.6878609` seconds for
`path_5_4` while the desktop was largely inactive/asleep; node counts and
terminal status are unaffected.  Exact per-partition nodes and runtimes are
in `A2_MULTI_EDGE_PARTITION_RESULTS.csv`.

## Benchmark effect before the census

On strict topology-free A2 prefixes, the fast local block layer reduced the
combined frontier:

- depth 10: `103,200 -> 71,602` (`30.62%`);
- depth 11: `840,815 -> 510,182` (`39.32%`).

On the pure attached root, whole-block exact packing reduced the depth-13
local frontier from `129,408` to `33,032` (`74.47%` additional reduction),
then the uncapped search closed the branch.

## Independent validation

- Off-by-default behavior exactly reproduced the prior strict depth-10 A2
  frontier and known small-order topology counts.
- Exhaustive topology counts for orders 2 through 6 remained
  `1,1,2,0,1` with the layer active.
- Candidate masks matched scalar enumeration.
- Randomized exact/Hall checks matched brute-force oracles.
- The stronger matching audit passed 64,000 oracle cases and all 70
  exact-cover-feasible states among 1,233 forced-MEX states through order 8.
- An independent C++20 `-O2 -Wall -Wextra -Wpedantic` build produced no
  warnings and reproduced attached `path_1_1` exactly as `ZERO` with
  `32,841` nodes.
- A final coverage script rejects duplicate, missing, non-ZERO, nonzero-exit,
  or nonpositive-node partition rows; it exits 0 on the final ledger.

## Reproduction and hashes

Coverage check:

```powershell
powershell.exe -NoProfile -ExecutionPolicy Bypass `
  -File .\work\a2_solver\verify_a2_partition_coverage.ps1
```

Production executable SHA-256:

```text
65BBAA57E5B462663B3656BC77499CC5956053F4137878C21072C99A327483F3
```

Main source SHA-256:

```text
E8DEDC62323152BA586F9C8607D119440C8BE9927EC4D38E546BA11DE9100E9C
```

Legacy exact-cover header SHA-256:

```text
C156EAE52BCEEF28DB0DF1A38D10DEA253DE09E5F627D0952A6BB1B9356CD813
```

Final partition ledger SHA-256:

```text
BC6A5909D2DE7B0CBC0E1A886A03C675B92419C8C4E553AD944E1A123DBC93AC
```

## Scope and next step

There is no reason to search A2 further.  The next rigorous step is to
formalize the multi-edge component-pair exact-cover lemma and its connection
to the solver invariants in Lean, then apply analogous certified searches to
the remaining non-A2 order-18 branches if the goal is a full order-18
nonexistence theorem.
