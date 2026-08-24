# Faster whole-block exact packing: isolated prototype

Status: implemented and tested in isolation.  The audited baseline header
`work/a2_solver/a2_multi_edge_exact_cover.hpp` was not edited by this work.

## Algorithm

The prototype enforces exactly the existing whole-block condition: choose one
candidate additive block for every non-generic component-pair family, with all
chosen blocks pairwise disjoint.  It introduces no new mathematical
restriction.

Three exact CSP optimizations replace the expensive residual rank matcher.

1. **Permutation quotient.**  Families with identical sorted candidate-block
   sets are grouped with a multiplicity.  Their selected candidate indices
   are required to be increasing.  Every unordered selection has exactly one
   such ordering, so this removes only duplicate search branches.
2. **Root arc consistency.**  A candidate block in class `i` is deleted if
   some class `j` does not contain enough candidates individually disjoint
   from it to supply all remaining copies of `j` (or the other copies of `i`).
   Any packing containing the deleted block would require those partners, so
   each deletion is sound.  Propagation iterates to a fixed point.  Hitting
   its comparison budget stops propagation and passes; it never rejects.
3. **Mask Hall propagation.**  At a search state, let `D_i` be the union of
   ranks in candidates still compatible with the used ranks.  Every subset
   `S` of live symmetry classes must satisfy

   ```text
   | union(i in S) D_i | >= sum(i in S) demand_i * remaining_i.
   ```

   This is the same arbitrary-domain Hall relaxation used by the old residual
   matcher.  Because all clones within one class have the same domain, taking
   every remaining clone is the strongest condition for a selected set of
   classes.  Three-word rank masks make the subset test much cheaper than a
   rank-by-rank augmenting matcher.

The DFS uses exact dead-state keys containing the used-rank mask, every class
multiplicity, and every increasing-index lower bound.  State-budget exhaustion
returns `UNKNOWN`, never `NO`.

## Validation

`test_multi_edge_exact_cover_optimized.cpp` compares the prototype with the
original exhaustive solver on hand-built coherence gaps, satisfiable cases,
identical-family multiplicities, and 500 deterministic random small CSPs.
Every definite result agreed:

```text
MULTI_EDGE_EXACT_COVER_OPTIMIZED_TEST_OK
```

## Named strict A2 survivors

At a 100,000-state budget, all five exact strict-case prefixes remained
`UNKNOWN`; this optimization does not itself give an early-prefix
contradiction.  It did remove the residual-Hall bottleneck:

| strict prefix | components | old residual-Hall time | optimized time |
|---|---:|---:|---:|
| attached `q3=15` | 10 | 5.86 s | 0.46 s |
| separate `q3=9` | 11 | 5.16 s | 0.25 s |
| separate `q3=11` | 11 | 1.71 s | 0.22 s |
| separate `q3=13` | 9 | 6.24 s | 0.49 s |
| adjacent separate `q3=17` | 10 | 3.18 s | 0.36 s |

Root arc consistency removed no candidates in these early prefixes, which
explains why they remain difficult.

## Later strict A2-prefix sample

The benchmark generated deterministic valid forced-mex A2 prefixes using the
existing validity, hop-diameter, and 7/11 parity checks.  These samples are a
performance probe, not an exhaustive proof.

At the same 10,000-state budget and 100 samples per row, after no-candidate and
root-Hall failures were removed:

| branch/depth | old exact `NO/UNKNOWN` | optimized `NO/UNKNOWN` | old time | optimized time | speedup |
|---|---:|---:|---:|---:|---:|
| separate, 12 edges | 29 / 24 | 43 / 10 | 27.42 s | 1.06 s | 25.8x |
| attached, 12 edges | 38 / 20 | 49 / 9 | 22.77 s | 1.01 s | 22.6x |
| separate, 13 edges | 29 / 2 | 30 / 1 | 7.37 s | 0.38 s | 19.5x |
| attached, 13 edges | 18 / 2 | 20 / 0 | 1.38 s | 0.0048 s | 288x |

There were zero definite-result disagreements.  Including the earlier
no-candidate/root-Hall stages, the optimized layer rejected 90/100 separate
and 91/100 attached samples at 12 edges, 99/100 separate and 100/100 attached
samples at 13 edges, and all sampled prefixes at 14 edges.

A 30-sample arc-consistency ablation showed its separate contribution:

| branch/depth | no-arc `NO` | arc `NO` | no-arc states | arc states |
|---|---:|---:|---:|---:|
| separate, 12 edges | 12 | 14 | 63,059 | 42,655 |
| attached, 12 edges | 12 | 15 | 75,341 | 49,748 |
| separate, 13 edges | 7 | 7 | 4,030 | 37 |
| attached, 13 edges | 5 | 5 | 2,237 | 21 |

Thus root propagation matters mainly after the prefix has coalesced to five
or six components; at ten or eleven components it is too weak.

## Files

- `work/a2_solver/a2_multi_edge_exact_cover_optimized.hpp`: isolated engine
- `work/a2_solver/test_multi_edge_exact_cover_optimized.cpp`: differential test
- `work/a2_solver/benchmark_multi_edge_exact_cover_optimized.cpp`: named strict cases
- `work/a2_solver/benchmark_multi_edge_exact_cover_optimized_samples.cpp`: sampled late prefixes

Recommended integration: retain the existing cheap no-candidate and root Hall
gates, then use this engine for the exact stage at six or fewer components.
The benchmark supports raising the exact stage's useful state budget by about
one to two orders of magnitude at comparable runtime.  It does not support
starting a full A2 census before the integrated frontier benchmark is run.
