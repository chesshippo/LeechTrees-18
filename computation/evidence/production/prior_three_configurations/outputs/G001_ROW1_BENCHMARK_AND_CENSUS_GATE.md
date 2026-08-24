# Order-18 G001 row-1 benchmark and census gate

Status date: 2026-08-16

## Scope

This report concerns zero-based G001 row 1, whose canonical exposed prefix is

```text
v0 --4-- v1 --1-- v2 --2-- v3.
```

Its internal distances are `{1,2,3,4,5,7}`, so forced-MEX search requires
physical weight 6 next.  The seed was stored in increasing physical-weight
order `1,2,4`; optional rank-indexed checks therefore retain their intended
meaning.

## Frozen implementation

```text
source snapshot SHA-256:
134373D19AD4B1B1DFB30595F73BEABCEF30FA21C19B74A652669FB7705A72D9

row-1 executable SHA-256:
5F50BEC4D18947680EE170BF22AF747D1E74EA203E34E305EAE27768439B46AD
```

The frozen A2 and row-7 source/executable artifacts were not overwritten.

## Validation

- seed: one depth-3 state with MEX 6;
- first fan-out: exactly three weight-6 children, MEX distribution `8:2,10:1`;
- next fan-outs for roots 0, 1, 2: exactly `2,4,10`;
- known topology counts at orders 2 through 6: `1,1,2,0,1`, both baseline
  and exact-cover configurations;
- the exact-cover layer is dormant through depth 8 and produced identical
  baseline/active counts there;
- depth-9 shadow mode retained every baseline state while recording exactly
  the states that active mode rejects;
- A2 depth-10 regressions remained 90,904 separate and 12,296 attached;
- A2 attached path `1,1` remained exhaustive `ZERO` with 32,841 nodes;
- the row-7 first fan-out remained exactly five;
- scalar candidate validation on row-1 path `0,0` through depth 12 reported
  `cover_validation_fail=0`; and
- the exact-cover unit and exhaustive small-order test executables passed.

## Compared configurations

Baseline is the audited topology-free forced-MEX search with exact collision,
range, order-18 parity-profile, and hop-diameter checks.  The only additional
active layer in the comparison was

```text
--multi-edge-cover
--multi-edge-cover-no-hall
--multi-edge-cover-max-components 6
--multi-edge-cover-budget 100
--multi-edge-cover-no-exact-hall
```

All budget/candidate-cap exhaustion is fail-open `UNKNOWN/PASS`.  No
structural-cut, late-T9a, parity-coherence, indexed-Hall, optimized-packing,
or empirical cutoff was active.

## Fixed-depth results

| Depth | Baseline nodes | Cover nodes | Node reduction | Baseline frontier | Cover frontier | Frontier reduction |
|---:|---:|---:|---:|---:|---:|---:|
| 9 | 19,270 | 19,270 | 0.00% | 16,310 | 13,393 | 17.88% |
| 10 | 139,520 | 123,262 | 11.65% | 120,250 | 88,255 | 26.61% |
| 11 | 1,111,290 | 901,710 | 18.86% | 971,477 | 612,732 | 36.93% |

At depth 12, roots 0 and 1 were compared whole, while root 2 was compared as
its exact ten-child partition.  Thus both columns use the same 12 selected
subtrees.

```text
baseline: nodes=9,526,390 frontier=8,370,258 wall_sum=97.752631 s
cover:    nodes=7,021,940 frontier=2,402,179 wall_sum=3,100.288725 s
```

The exact-cover layer therefore reduced node visits by **26.29%** and the
surviving depth-12 frontier by **71.30%**.  Summed observed process wall time
was about 31.72 times baseline, driven by the oversized path `2,9`.  Node and
wall sums contain repeated selected-prefix work; frontier sums are the exact
additive partition metric.  Complete per-run data are in
`outputs/G001_ROW1_BENCHMARK.csv`.

## Decision

The predefined mathematical gate was at least 70% frontier reduction and at
least 20% node reduction, with a credible partitioned completion plan.  Row 1
passes: 71.30% and 26.29%, respectively.  The aggregate path `2,9` is too
slow to retain as one production job, but it has a separately certified
16-child fan-out and will be replaced by those disjoint children.

The provisional prefix-free census cover is

```text
root_0, root_1,
path_2_0, ..., path_2_8,
path_2_9_0, ..., path_2_9_15.
```

Before launching the uncapped cover, all sixteen `2,9,k` children are being
profiled at depth 12.  Their frontier sums must reproduce the parent in both
configurations; any unusually large child will be replaced by its complete
certified next fan-out.

This benchmark is not an exclusion of row 1.  Only a complete prefix-cover
ledger of uncapped terminal `ZERO` results can support that conclusion.
