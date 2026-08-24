# Off-by-default multi-edge exact-cover layer

Status: isolated implementation complete in `a2_multi_edge_exact_cover.hpp`.
The shared `a2_topology_free_search.cpp` has deliberately not been edited.

## Sound necessary condition

Let the current valid prefix forest have components `K[0],...,K[c-1]` and
missing rank set `M`.  In any final completion, fix a component pair `i<j`.
The unique final path has a first port `u` in `K[i]`, a last port `v` in
`K[j]`, and a positive port-to-port distance `L`.  Its complete indexed block
is

```
B(i,j;u,v,L) = {
    dist_i(x,u) + L + dist_j(v,y) : x in K[i], y in K[j]
}.
```

The actual block has all of the following properties.

1. It has exactly `|K[i]|*|K[j]|` distinct members.
2. Every member, including `L`, belongs to `M`.
3. Actual blocks for different component pairs are pairwise disjoint.
4. Their total cardinality is
   `sum(i<j)|K[i]|*|K[j]| = |M|`, so they exactly cover `M`.

The implementation enumerates every block satisfying (1)-(2), without making
any topology or port-compatibility assumption.  It first applies exact
capacitated Hall matching to the union of allowed ranks for every block slot.
Late in the search it runs memoized Algorithm X: choose one whole candidate
block per component pair, requiring pairwise disjoint masks.  A completed
choice automatically covers `M`.  Therefore `no candidate`, Hall failure, and
an exhaustively proved exact-cover failure are all sound pruning outcomes.

Passing is not sufficient for a tree: choices for different component pairs
may use mutually incompatible ports, path lengths, or quotient routes.

## Fast candidate construction

For fixed ports, precompute the offset mask

```
O = {dist_i(x,u) + dist_j(v,y)}.
```

Duplicate offsets kill that port pair for every `L`.  Otherwise the allowed
length mask is calculated in three 64-bit words:

```
AllowedL = M intersect (M >> o_1) intersect ... intersect (M >> o_k).
```

For each set bit `L`, the candidate block is simply `O << L`.  Equal offset
patterns and equal final blocks are deduplicated.  Across an order-18 prefix
there are at most 153 raw port pairs and 153 possible translations per pair.

Singleton-singleton slots are eliminated exactly.  Each can take any one
missing rank; after the nontrivial blocks are disjointly selected, these slots
fill precisely the leftover ranks.

## Performance policy

Recommended initial defaults (all inactive unless the main flag is supplied):

```
--multi-edge-cover
--multi-edge-cover-max-components 7
--multi-edge-cover-exact-max-components 6
--multi-edge-cover-budget 100000
```

Candidate generation and Hall run only with at most seven forest components
(at least eleven exposed edges at order 18).  Exact block DP runs only with at
most six.  The DP chooses the remaining slot with the fewest compatible whole
blocks, performs residual arbitrary-domain Hall at every state, memoizes exact
dead states, and uses a tri-state result.  Hitting the candidate cap or state
budget returns `unknown/pass`; it can never cause pruning.

## Proposed integration hook

Add the include:

```cpp
#include "a2_multi_edge_exact_cover.hpp"
```

Add off-by-default members to `Search`:

```cpp
bool use_multi_edge_cover = false;
bool shadow_multi_edge_cover = false;
a2_multi_cover::Config multi_cover_config;
a2_multi_cover::Counters multi_cover_counters;
a2_multi_cover::Checker multi_cover_checker;
long long multi_cover_shadow_reject = 0;
```

Convert an already computed valid `Analysis z` without recomputation:

```cpp
a2_multi_cover::Input multi_cover_input(const Analysis& z) const {
    a2_multi_cover::Input in;
    in.n = n;
    in.target = target;
    in.mex = z.mex;
    in.components = z.vertices;
    for (int i=0;i<n;i++) for (int j=0;j<n;j++)
        in.distance[i][j] = z.dist[i][j];
    for (int d=1;d<=target;d++) if (!z.used.get(d)) in.missing.set(d);
    return in;
}
```

Place the check in `rec()` after the existing cheap validity, parity,
diameter, and equality-quota checks, but before `accepted++` and candidate
orbit construction:

```cpp
if (use_multi_edge_cover || shadow_multi_edge_cover) {
    auto out = multi_cover_checker.check(
        multi_cover_input(z), multi_cover_config, multi_cover_counters);
    if (!out.possible) {
        if (shadow_multi_edge_cover) multi_cover_shadow_reject++;
        else return false;
    }
}
```

Suggested parser flags:

```text
--multi-edge-cover
--multi-edge-cover-shadow
--multi-edge-cover-max-components K
--multi-edge-cover-exact-max-components K
--multi-edge-cover-budget N
--multi-edge-cover-no-exact
--multi-edge-cover-validate
```

The shadow flag computes and counts would-be rejections but never prunes.
The normal flag and shadow flag should be mutually exclusive.  Defaults leave
the baseline instruction stream unchanged apart from the dormant members.

Append these result counters:

```text
mec_checks, mec_skip, mec_slots, mec_patterns, mec_candidates,
mec_nocandidate, mec_hall, mec_exact_calls, mec_exact_fail,
mec_exact_pass, mec_exact_budget, mec_exact_states,
mec_exact_hall, mec_validate_fail, mec_shadow_reject
```

## Validation gates before benchmarking

1. Compile and run `test_multi_edge_exact_cover.cpp`.  It currently prints
   `MULTI_EDGE_EXACT_COVER_TEST_OK` under `g++ -std=c++17 -O2 -Wall -Wextra`.
2. Run the layer with candidate validation enabled.  Every fast mask-generated
   candidate set is compared with an independent scalar enumeration.
3. Run all known small orders with the layer enabled and verify exactly the
   existing topology counts.
4. Run A2 in shadow mode and verify status, node count, and solution set are
   byte-for-byte identical to baseline; inspect only the would-reject count.
5. Run pruning mode and compare its result with shadow mode.  Any `ZERO` claim
   must be repeated uncapped and split by the existing root branches.
6. Benchmark Hall-only and Hall+exact separately so the incremental benefit
   and overhead of whole-block coherence are visible.

Current isolated validation results:

```text
MULTI_EDGE_EXACT_COVER_TEST_OK
COVER_SMALL order=2 topologies=1
COVER_SMALL order=3 topologies=1
COVER_SMALL order=4 topologies=2
COVER_SMALL order=5 topologies=0
COVER_SMALL order=6 topologies=1
MULTI_EDGE_EXACT_COVER_SMALL_ORDER_OK
```

Scalar-oracle validation also passed on the real separate- and
attached-equality seeds.  They generated 15,913 and 14,559 deduplicated
candidate blocks respectively; root Hall passed in both cases, as expected.

The layer uses only exact current distances and the verified cross-block
decomposition.  It does not add an exploratory restriction such as a bound on
the third odd edge.
