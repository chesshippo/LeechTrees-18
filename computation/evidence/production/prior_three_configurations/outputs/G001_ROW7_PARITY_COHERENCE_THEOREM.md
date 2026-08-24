# Parity-coherent current-component block restriction

Status: proved at paper level and implemented as an off-by-default necessary precheck.  Not Lean formalized.

## Setting

Let `F` be a valid forced-MEX prefix forest on `n` vertices.  Its current connected components are `K_1,...,K_m`.  For each component choose a root `rho_i` and define

```text
c_i(x) = d_Ki(rho_i,x) mod 2.
```

Suppose `F` extends to a weighted tree whose unordered-pair distances are exactly `1,...,N`, where `N=n(n-1)/2`.

The parity of weighted distance defines two global vertex classes: two vertices lie in different classes exactly when their distance is odd.  If the class sizes are `p` and `n-p`, the number of odd-distance pairs is `p(n-p)`.  The prescribed rank interval contains `ceil(N/2)` odd ranks, so necessarily

```text
p(n-p) = ceil(N/2).
```

For `n=18`, `N=153`, this gives `p=7` or `11`.  Designate the smaller global class, of size 7.

For each component let `s_i` be the intrinsic color, 0 or 1, whose vertices belong to that designated global class.  Thus

```text
sum_i |{x in K_i : c_i(x)=s_i}| = 7.                 (1)
```

## Component-pair XOR theorem

For a pair `K_i,K_j`, the current-component whole-block theorem says that any completion supplies a first port `u` in `K_i`, a last port `v` in `K_j`, and a positive port-to-port route length `L`.  Its complete cross-distance block is

```text
B_ij(u,v,L) = {
  d_Ki(x,u) + L + d_Kj(v,y) : x in K_i, y in K_j
}.
```

Every rank in this block is currently missing, and the block is internally injective.

The generating data necessarily satisfy

```text
c_i(u) XOR c_j(v) XOR (L mod 2) = s_i XOR s_j.        (2)
```

Proof: reduce the additive distance formula modulo 2.  Since

```text
d_Ki(x,u) mod 2 = c_i(x) XOR c_i(u)
d_Kj(v,y) mod 2 = c_j(v) XOR c_j(y),
```

the parity of the block rank for `(x,y)` is

```text
c_i(x) XOR c_i(u) XOR (L mod 2)
  XOR c_j(v) XOR c_j(y).
```

The same distance is odd exactly when `x,y` belong to opposite global classes, whose indicator differs by

```text
c_i(x) XOR s_i XOR c_j(y) XOR s_j.
```

Canceling the `x` and `y` terms gives (2).

## Sound precheck

For every component pair, enumerate every port pair and every positive `L` whose translated block is internally injective and contained in the current missing ranks.  Record which values `0,1` occur on the left side of (2).  Then enumerate all component choices `s_i` satisfying (1).

Reject the prefix only if:

- some component pair supports neither relation; or
- no mass-7 profile has `s_i XOR s_j` supported for every pair.

This rejection is sound.  A genuine completion provides its actual global parity class, hence one profile satisfying (1), and its actual route data satisfy (2) for every pair.

Passing is only a relaxation.  It does not require the independently selected blocks to be disjoint or to arise from one common future tree.

## Implementation guardrails

- Use weighted-distance parity, not hop parity.
- Do not fix one component orientation while requiring only mass 7.  Either enumerate all profiles as the implementation does, or fix one orientation and permit selected mass 7 or 11.
- Equal rank-block masks can arise with both parity relations.  An odd-weight dimer rooted at its two endpoints gives the same offset set but opposite labels.  The cheap precheck avoids deduplication; any future profile-aware exact packer must OR both supported relation bits for a duplicate mask.
- If a profile-aware exact solver is budgeted, any unknown profile must make the entire check `UNKNOWN/PASS`.  Reject only when every feasible profile is proved impossible.
- Singleton-singleton families also have a parity relation: their chosen rank `L` must have parity `s_i XOR s_j`.

## Current implementation and measurement

Files:

- `work/a2_solver/multi_edge_parity_coherence.hpp`
- `work/a2_solver/test_multi_edge_parity_coherence.cpp`
- integration in `work/a2_solver/order18_topology_free_search.cpp`

Flags:

```text
--multi-edge-parity-coherence
--multi-edge-parity-coherence-shadow
--multi-edge-parity-max-components K
```

The layer is off by default.

Validation completed:

- dedicated unit tests, including the odd-dimer two-label case;
- known small-order counts `1,1,2,0,1` for orders 2 through 6;
- canonical G001 row-7 seed and five-child fan-out;
- unchanged A2 result when the new flag is absent.

On the row-7 depth-11 benchmark, legacy whole-block pruning left 746,417 frontier states.  Adding parity coherence left 745,849, an additional rejection of 568 states (0.0761%), while observed wall time rose from about 18.7 seconds to 40.30 seconds.  It is mathematically valid but not cost-effective in its current standalone implementation, so it is not enabled in the production uncapped run.
