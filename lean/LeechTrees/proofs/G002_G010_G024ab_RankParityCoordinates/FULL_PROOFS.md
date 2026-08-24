# Rank, parity, allocation, and coordinate lemmas

These are exact necessary conditions for a classical Leech tree. They are not
sufficient and do not resolve existence.

Let `T` have order `n`, `N=binomial(n,2)`, and sorted physical edge weights

```text
w_1 < w_2 < ... < w_m,  m=n-1.
```

For edge `e_i`, let `C_i` be the set of distances of pairs separated by deleting `e_i`, and let `c_i=|C_i|=s_i(n-s_i)`.

## 1. Physical-rank-punctured cut cap

**Theorem.** For every `i=1,...,m`,

```text
C_i intersect {w_1,...,w_m} = {w_i}
```

and therefore

```text
w_i + c_i + (m-i) <= N+1.                 (1)
```

Equality in (1) holds exactly when

```text
C_i = [w_i,N] minus {w_{i+1},...,w_m}.
```

**Proof.** Every crossing path contains `e_i`, so its positive length is at least `w_i`; the endpoints of `e_i` give equality. For `j != i`, both endpoints of `e_j` lie in the same component of `T-e_i`, so the pair uniquely realizing distance `w_j` is noncrossing. Because a Leech tree realizes each numerical distance only once, no crossing pair can also have value `w_j`. Hence `C_i` is a `c_i`-subset of

```text
[w_i,N] minus {w_{i+1},...,w_m},
```

whose cardinality is `N-w_i+1-(m-i)`. This proves (1) and the equality characterization. ∎

At order 18, (1) is

```text
w_i <= 137+i-c_i.
```

It can be intersected with the independently certified inherited cap for the same cut coefficient. It is often sharper for early physical ranks. For example, for coefficient 81 it gives rank-dependent maxima `57,58,...,67` through rank 11, after which the inherited cap 67 dominates.

This strengthens the inherited cardinality bound `w_i+c_i<=N+1` by deleting the `m-i` larger physical ranks which the cut block cannot use.

## 2. Parity-channel puncturing

Let `r` be the number of odd physical weights, let

```text
O=ceil(N/2),  E=floor(N/2),
```

and let `o_i` be the number of odd distances in `C_i`. Then

```text
o_i <= O-r + 1_{w_i odd},
c_i-o_i <= E-(m-r) + 1_{w_i even}.        (2)
```

This is immediate from `C_i intersect W={w_i}` after separating odd and even ranks. The complementary lower bounds follow by subtracting either upper bound from `c_i`.

A sharper rank-aware form uses only the interval `[w_i,N]`. Let `r_i` be the number of odd physical weights among `w_1,...,w_i`. Then

```text
o_i <= #{odd d in [w_i,N]} - (r-r_i),
c_i-o_i <= #{even d in [w_i,N]} - ((m-r)-(i-r_i)).       (3)
```

The subtracted terms are precisely the later physical ranks of the indicated parity. Equality in the exact punctured channel means that channel is exhausted. Equality in the coarser bound (2) additionally requires that no unused rank of that parity lie below `w_i`; omitting this condition is false.

For a parity character `chi(v)=(-1)^{d(root,v)}`, choose one side `A_i` of the cut and put

```text
delta=sum_V chi,  x_i=sum_{A_i} chi.
```

Then

```text
o_i = (c_i-x_i(delta-x_i))/2,              (4)
```

so (2) or (3) couples cut size, edge rank, edge parity, total odd-edge count, and the signed cut imbalance.

## 3. Signed first moment in centered form

**Theorem.** Every Leech tree satisfies

```text
sum_i w_i x_i(delta-x_i) = R_N,
R_N = sum_{d=1}^N (-1)^d d.                (5)
```

**Proof.** For every pair, `chi(u)chi(v)=(-1)^{d(u,v)}`. Expand `d(u,v)` as the sum of weights of the edges on its path, multiply by the character product, sum over pairs, and interchange the pair and edge sums. Across edge `e_i`, the character-product sum factors as `x_i(delta-x_i)`. The target spectrum turns the left side into `R_N`. ∎

Equation (5) is inherited mathematics. The following centered consequence is a useful reformulation. At order 18 choose the global sign with `delta=4`. Since `N=153` and `R_N=-77`,

```text
sum_i w_i x_i(4-x_i) = -77,
sum_i w_i (x_i-2)^2 = 4 sum_i w_i + 77,
sum_i w_i x_i(x_i-4) = 77.                 (6)
```

Because every weight is positive, (6) forces at least one edge with

```text
x_i < 0  or  x_i > 4.                      (7)
```

Side complementation sends `x_i` to `4-x_i`, so (7) is orientation-independent. This is a cheap necessary completion test and a diagnostic for any proposed parity decoration.

## 4. Punctured path-segment order statistics

Let `P` be a contiguous segment of `h` physical edges with total weight `L`. Delete the segment edges and take the two extreme components. From their boundary vertices let the sorted depth sets be

```text
X={x_0<...<x_{a-1}},  Y={y_0<...<y_{b-1}}.
```

The `ab` pairs whose paths contain all of `P` have the distinct distance block

```text
L + (X+Y).
```

If `h=1`, this block meets the physical weight set exactly in `{L}`. If `h>=2`, it is disjoint from every physical weight and `L` is not physical. The proof is the same uniqueness argument as in Section 1: a pair spanning all of `P` cannot be the endpoint pair of any other physical edge, and for `h>=2` cannot be any physical-edge endpoint pair at all.

Let `r_0<...<r_{M-1}` be the allowed offset values after subtracting `L` from the eligible ranks in `[L,N]` and deleting the forbidden physical ranks. Then for every `i,j`,

```text
r_{(i+1)(j+1)-1} <= x_i+y_j
                   <= r_{M-(a-i)(b-j)}.    (8)
```

Indeed, the southwest rectangle through `(i,j)` supplies `(i+1)(j+1)` distinct sums no larger than `x_i+y_j`, while the northeast rectangle supplies `(a-i)(b-j)` distinct sums no smaller. Formula (8) refines the ordinary interval boxes whenever physical ranks puncture the domain.

### Direct-sum variance consequence

For a finite set `S`, put

```text
Delta(S)=|S| sum_{s in S} s^2 - (sum_{s in S} s)^2.
```

If all `ab` sums in `X+Y` are distinct, direct expansion gives

```text
Delta(X+Y)=b^2 Delta(X)+a^2 Delta(Y).
```

Any `ab` distinct integers have at least the centered second moment of `ab`
consecutive integers. Consequently every path-segment block also satisfies

```text
b^2 Delta(X)+a^2 Delta(Y)
    >= (ab)^2 ((ab)^2-1)/12.
```

Equality requires the sumset itself to be a consecutive interval. This is a
necessary variance filter, not a direct-sum sufficiency test.

### Selected-edge quotient gluing

Choose any set of physical edges and let `K_i` be the actual named components
left after deleting them. Let `P_i(z)` be the internal unordered-pair distance
polynomial of `K_i`. For a named exit port `p` in `K_i`, let

```text
R_{i,p}(z)=sum_{v in K_i} z^{d(v,p)}.
```

For each pair `i<j`, the quotient route fixes an exit port `p_ij` in `K_i`, an
exit port `p_ji` in `K_j`, and a length `L_ij` between those ports after the two
extreme rooted contributions are removed. Partitioning vertex pairs by their
two components gives the exact identity

```text
P_T(z) = sum_i P_i(z)
       + sum_{i<j} z^{L_ij} R_{i,p_ij}(z) R_{j,p_ji}(z).
```

Thus a Leech completion is equivalent to coefficientwise equality with
`z+z^2+...+z^N`. In particular, all displayed cross products must be internally
0/1 and globally disjoint from one another and from every `P_i`. This statement
uses the actual jointly indexed component and port rows; replacing them by
independently selected marginal profiles is invalid.

### Coupled allocation for two cuts

Let two edges occur in the order `A--M--B` after deletion, with component sizes
`a,m,b`. Their two crossing-rank sets have four membership categories of sizes

```text
11: ab,   10: am,   01: bm,
00: N-ab-am-bm.
```

For `p>=1`, write `R_e^(p)` and `R_f^(p)` for the sums of the `p`th powers in
the two cut blocks. Let `L_p(k)` and `U_p(k)` be respectively the sums of the
`k` smallest and `k` largest `p`th powers among `1,...,N`. Since the difference
of the cut moments is the `10` bin minus the `01` bin, while their sum is the
`11` bin plus the whole union, every completion obeys

```text
L_p(am)-U_p(bm) <= R_e^(p)-R_f^(p) <= U_p(am)-L_p(bm),

L_p(ab)+L_p(ab+am+bm)
    <= R_e^(p)+R_f^(p)
    <= U_p(ab)+U_p(ab+am+bm).
```

An exact disjoint four-bin subset DP is a safe strengthening. These bounds
couple two cuts but remain only an outer relaxation of pair-level distances.

## 5. Further structural consequences

### Hop-rank allocation for a fixed weighted topology

Let `h_uv` be the unweighted hop count and define

```text
H_e = sum_{u<v: e lies on P_uv} h_uv.
```

Then the exact double count

```text
sum_{u<v} h_uv d(u,v) = sum_e w_e H_e              (9)
```

holds. The hop-one pairs are exactly the physical-edge endpoint pairs, so their ranks are exactly the physical weight set `W` and contribute `sum W`. If the remaining ranks are `r_1<=...<=r_M` and the nonedge hop counts are `eta_1<=...<=eta_M`, rearrangement gives

```text
sum W + sum_k r_k eta_{M+1-k}
    <= sum_e w_e H_e
    <= sum W + sum_k r_k eta_k.                    (10)
```

For edge `e=alpha beta` with sides `A,B`, the coefficient is computable as

```text
H_e = |A||B| + |B| sum_{u in A} h_A(u,alpha)
                + |A| sum_{v in B} h_B(beta,v).    (11)
```

A stronger exact necessary relaxation bins by parity `p` and hop count `h`. Let `n_{p,h}` be the number of such pairs and `k_{e,p,h}` the number whose path contains edge `e`. Put

```text
S_{p,h}=sum_e k_{e,p,h} w_e.
```

The target ranks of parity `p` must admit a disjoint partition into bins `R_{p,h}` satisfying

```text
|R_{p,h}|=n_{p,h},  sum R_{p,h}=S_{p,h},  R_{p,1}=W_p.   (12)
```

Per-bin smallest/largest-sum bounds are cheap; an exact disjoint subset DP is stronger. Equations (9)–(12) require the full edge-to-weight assignment. The unweighted topology and `W` merely as a set do not determine `sum_e w_eH_e`; parity-channel data additionally require the induced edge-parity placement. If only `W` is fixed, the assignment must also be existentially optimized rather than silently chosen.

The order-6 star counterexample below satisfies even the exact parity/hop bin counts and sums, so (9)–(12) remain necessary only.

### Odd-edge quotient distance capacity at order 18

Delete all odd physical edges and contract each remaining even component to a quotient vertex. If quotient components `i,j`, of orders `m_i,m_j`, are separated by `ell` odd quotient edges, those `ell` physical weights are distinct positive odd integers and have sum at least

```text
1+3+...+(2ell-1)=ell^2.
```

Every one of the `m_i m_j` cross-component distances has parity `ell`, is at least `ell^2`, and is distinct. Counting target ranks of that parity gives

```text
m_i m_j <= 77-floor(ell^2/2).              (13)
```

Thus the odd-edge quotient diameter is at most 12. If a quotient path omits the unique weight-1 edge, its `ell` distinct odd weights sum at least `3+5+...+(2ell+1)=ell(ell+2)`. In particular every quotient path of length 12 must contain weight 1, since `12*14=168>153`.

### Exact rooted signed-moment merge

For a rooted weighted tree `(H,r)` define

```text
R_j(H,r)=sum_v (-1)^{d(r,v)} d(r,v)^j
```

and let `A_j(H)` be the analogous signed sum over unordered vertex pairs. Join the roots of rooted trees `A,B` by weight `w`, retaining the root of `A`. Direct binomial expansion gives

```text
R_j(T)=R_j(A)+(-1)^w sum_q binom(j,q) w^(j-q) R_q(B),

A_j(T)=A_j(A)+A_j(B)
       +(-1)^w sum_{p+q+r=j} multinomial(j;p,q,r)
                   w^p R_q(A) R_r(B).       (14)
```

This propagates exact signed moments through forced-mex merges without any collinearity bookkeeping. It is an invariant/filter, not a replacement for the full distance mask.

### Joint signed-cut flow on a fixed topology

Root a candidate topology at `r` and orient every edge from a parent toward its
descendant subtree. Choose the global parity sign so that

```text
delta = sum_z sigma_z = 4,
```

as required by the order-18 parity split `11|7`. For every nonroot vertex `v`,
let

```text
x_v = sum_{z in T_v} sigma_z
```

be the signed imbalance of the descendant side of its parent edge. Define

```text
b_v = x_v - sum_{u child of v} x_u                    (v != r),
b_r = 4   - sum_{u child of r} x_u.
```

Then the entire family of oriented cut imbalances `{x_v}` is jointly realizable
by one weighted-depth parity character if and only if

```text
b_v in {-1,+1}                                      for every vertex v,
b_u b_v = (-1)^(w_uv)                               for every edge uv.   (15)
```

Necessity follows from the disjoint decomposition
`T_v={v} union (union over child subtrees T_u)`, which gives `b_v=sigma_v`,
and from the parity change across an edge. Conversely, set `sigma_v=b_v`.
Bottom-up induction recovers `x_v=sum_{T_v} sigma`, the root equation gives
`sum sigma=4`, and the edge equations propagate exactly the weighted-depth
parity character. Thus (15) is an iff characterization, not merely another
marginal bound. With the opposite global sign, replace `4` by `-4`.

This condition is redundant when a fixed-topology model already assigns a
single parity sign to every vertex, but it is essential before combining
independently chosen per-edge `x` values in a cut-profile relaxation. It uses
edge incidence and a coherent root orientation, so it cannot be imposed on a
histogram that has forgotten which coefficient belongs to which edge.

A concrete marginal false positive is the rooted 18-star with spoke weights
`1,...,17`. Set `x=-1` on weights `{5,14,15,16,17}` and `x=+1` on the other
12 spokes. Each leaf-cut imbalance has the allowed parity and magnitude, and
the exact signed first moment holds:

```text
sum_w w x_w(x_w-4)
  = 5(5+14+15+16+17) - 3(153-(5+14+15+16+17))
  = 77.
```

But the leaf imbalances sum to `7`, hence `b_r=4-7=-3`; no common vertex
parity assignment realizes them. This is a counterexample only to the
marginal algebraic relaxation, not a candidate Leech tree.

### Three-port named-median guard

If three named ports have a genuine named tripod median with positive arm lengths `A_0,A_1,A_2`, then the six named-pair distances

```text
A_0,A_1,A_2,A_0+A_1,A_0+A_2,A_1+A_2
```

must be pairwise distinct. Equivalently the arms are pairwise distinct and no arm equals the sum of the other two. When one arm is zero and the median is a port on a path, only the two positive arms must differ; imposing six-value distinctness in that boundary case would be invalid.

### Logical limits

If the final odd-edge total is not fixed, equations (2)--(4) must be read
existentially over every possible `r`. On a fixed rooted topology, simultaneous
signed cut imbalances must satisfy the joint flow condition (15), or an
equivalent common vertex-parity assignment. Marginal per-edge admissibility
and the signed first moment do not suffice. Equations (1)--(15) are necessary
conditions only; satisfying them does not produce a lift, tree, or spectrum.

A concrete sufficiency counterexample is the order-6 weighted star with odd spoke weights `{1,7}` and even spoke weights `{2,6,8}`. It has distinct positive physical weights including 1 and 2, parity classes `4|2`, all distances at most 15, cut checksum `5(1+2+6+7+8)=120`, and signed checksum `-3(1+7)+(2+6+8)=-8`, exactly the order-6 targets. Nevertheless its distance multiset has only 11 distinct values. Thus even the ordinary and signed first moments, parity, edge distinctness, and range together are far from sufficient.
