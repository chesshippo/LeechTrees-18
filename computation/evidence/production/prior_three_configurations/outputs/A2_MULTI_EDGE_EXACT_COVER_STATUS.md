# A2 multi-edge block-cover status

## Restriction implemented

For every pair of connected components `K_i,K_j` in a valid forced-MEX
prefix, any completion supplies ports `u in K_i`, `v in K_j` and a route
length `L` whose entire cross-distance block is

```text
{ d_i(x,u) + L + d_j(v,y) : x in K_i, y in K_j }.
```

The block must be internally injective, use only currently missing ranks, and
be disjoint from the corresponding blocks of every other current component
pair.  Since the total block cardinality is exactly the number of missing
ranks, these blocks form an exact cover.  Failure of the whole-block packing
problem is therefore a sound pruning certificate.  Budget exhaustion is
always `UNKNOWN/PASS`, never rejection.

Separately toggleable implementations now include:

- cheap component-pair block existence;
- capacitated Hall and whole-block exact packing;
- indexed vertex-pair and translation Hall;
- one-current-MEX conditioned self-puncturing;
- an optimized exact-packing engine (experimental alternative).

The production branch-closing configuration used in the exhaustive results
below is the audited legacy whole-block solver with residual Hall disabled:

```text
--multi-edge-cover --multi-edge-cover-no-hall
--multi-edge-cover-budget 100 --multi-edge-cover-no-exact-hall
```

Disabling either Hall call weakens pruning only.  The 100-state exact-search
budget is conservative: a budget hit passes the prefix.

## Validation

- Off-by-default behavior matches the prior topology-free executable on the
  known orders and the strict depth-10 A2 frontier.
- Exhaustive known topology counts for orders 2--6 remain `1,1,2,0,1` in
  active and shadow modes.
- Candidate bit masks match independent scalar enumeration.
- Randomized Hall/exact CSP checks agree with brute-force oracles.
- The stronger indexed/self-puncturing layer passed 64,000 matcher-oracle
  cases and all 70 exact-cover-feasible states among 1,233 forced-MEX states
  through order 8.
- Both known A2 equality seeds pass the relaxations, preventing a false claim
  that the restriction alone encodes the earlier equality contradictions.
- An independent C++20 `-O2 -Wall -Wextra -Wpedantic` rebuild produced no
  warnings, passed all bundled tests, and exactly reproduced the attached
  `1,1` certificate (`ZERO`, `32,841` nodes).
- An independent unfiltered fan-out audit proved that attached has 2 root
  branches (root 1 has 6 children), while separate has 9 roots with child
  counts `[1,2,1,4,6,5,2,8,15]`.  These counts, rather than a path run's
  truncated `root_valid` field, certify that the listed partitions cover the
  intended search tree.

## Strict A2 benchmark effect

At depth 10, the fast local block test reduced the combined strict frontier
from `103,200` to `71,602` (`30.62%`).  At depth 11 it reduced the frontier
from `840,815` to `510,182` (`39.32%`).

On the pure attached strict root, exact packing reduced the depth-13 local
frontier from `129,408` to `33,032` and then left no accepted state at depth
15.  The uncapped run returned `ZERO`.

## Exhaustive partition status

The attached A2 case is completely eliminated:

- root 0: `ZERO`;
- root 1 has exactly six valid next children, paths `1,0` through `1,5`;
  every child is `ZERO`.

The separate A2 case is completely eliminated:

- complete `ZERO` roots: 0, 1, 2, 3, and 4;
- root 5: all paths `5,0` through `5,4` are `ZERO`;
- root 6: both paths `6,0` and `6,1` are `ZERO`;
- root 7: all paths `7,0` through `7,7` are `ZERO`;
- root 8: all fifteen paths `8,0` through `8,14` are `ZERO`.

Exact node counts and measured runtimes are recorded in
`A2_MULTI_EDGE_PARTITION_RESULTS.csv`.  An abnormal process termination with
no solver `RESULT` is not counted as evidence.

The final coverage checker reports all `47/47` expected partitions `ZERO`:
`17,650,190` attached node visits and `150,092,642` separate node visits,
for `167,742,832` reported node visits in total.  See
`A2_EXHAUSTIVE_ZERO_CERTIFICATE.md` for the consolidated certificate,
validation record, hashes, and runtime caveats.

## Current conclusion

The exhaustive, independently audited partition composition is complete:
all 47 required partitions return `ZERO`.  Therefore no order-18 Leech tree
exists in branch A2 under the verified structural reductions encoded by this
solver.  This is an A2 impossibility result, not yet a proof for order-18
branches outside A2.
