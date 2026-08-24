# Multicut, Hall, and shared-tail structure

## Scope

This note proves necessary structural statements for a classical Leech tree.
They do not prove existence or nonexistence at order 18. In particular,
neither the three-odd nor the four-odd layer is closed here. The arguments retain
edge incidence, component identity, and (where needed) the common vertex-parity
character. They are not valid as conditions on a cut-coefficient histogram
that has forgotten those data.

Let `T=(V,E,w)` be a classical Leech tree of order `n`, let
`N=binomial(n,2)`, and let `m=n-1`. For an unordered vertex pair `p={u,v}`,
write `z_p in {0,1}^E` for the incidence vector of its unique path. Thus

```text
d_p = w^T z_p.
```

The physical-weight set is `W={w_e:e in E}`. Its values are distinct, and the
endpoint pair of edge `e` is the unique pair at rank `w_e`.

## 1. Parity-resolved, physical-rank-punctured multicut rearrangement

Choose a root and put `sigma_v=(-1)^{d(root,v)}`. For `tau in {+1,-1}`, let

```text
P_tau = { {u,v}: sigma_u sigma_v=tau },
M^tau = sum_{p in P_tau} z_p z_p^T.
```

Thus `tau=+1` is the even-distance channel and `tau=-1` is the odd-distance
channel. Fix an arbitrary real edge vector `a`, and define the path score

```text
q_p = a^T z_p.
```

Delete from `P_tau` the endpoint pairs of the physical edges whose weights
have parity `tau`. Sort the scores of the remaining nonedge pairs as

```text
eta_1 <= ... <= eta_L.
```

Sort the target ranks of that parity after deleting the physical ranks as

```text
r_1 < ... < r_L,

{r_1,...,r_L}
 = {d in [1,N] : (-1)^d=tau} minus {w_e : (-1)^(w_e)=tau}.
```

Then every Leech tree satisfies the sharp necessary inequalities

```text
sum_{e: (-1)^(w_e)=tau} a_e w_e
  + sum_{k=1}^L eta_k r_{L+1-k}
    <= a^T M^tau w
    <=
sum_{e: (-1)^(w_e)=tau} a_e w_e
  + sum_{k=1}^L eta_k r_k.                         (16)
```

The scores may be negative and may have ties. Equality on the right occurs
exactly when the actual nonedge rank assignment is nondecreasing in score,
up to arbitrary permutations inside score ties; equality on the left has the
analogous nonincreasing condition.

### Proof

Expanding and interchanging finite sums gives

```text
sum_{p in P_tau} q_p d_p
 = sum_p (a^T z_p)(w^T z_p)
 = a^T (sum_p z_p z_p^T) w
 = a^T M^tau w.                                    (17)
```

For the endpoint pair of edge `e`, the path vector is the unit vector at `e`,
so its contribution is `a_e w_e`. The Leech property says that deleting all
such endpoint pairs in this parity channel deletes exactly the corresponding
physical ranks and leaves a bijection between the remaining pairs and the
displayed `r_k`. Therefore the unremoved part of (17) is
`sum_k eta_k r_{pi(k)}` for some permutation `pi`. The ordinary rearrangement
inequality, valid for arbitrary real `eta_k`, gives (16) and its equality
conditions. QED.

### Exact topology entries

The matrices in (16) are computable from a fixed topology and one coherent
parity character. For an edge `e`, choose one deletion side of order `s_e`
and signed imbalance `x_e`; put `delta=sum_v sigma_v`. Then

```text
M^+_{ee} = (s_e(n-s_e)+x_e(delta-x_e))/2,
M^-_{ee} = (s_e(n-s_e)-x_e(delta-x_e))/2.           (18)
```

For distinct edges `e,f`, delete both. Let `A_{e|f}` and `A_{f|e}` be the two
outer components, namely the component beyond `e` away from `f` and the
component beyond `f` away from `e`. If their orders are `alpha,beta` and their
signed imbalances are `y,z`, then

```text
M^+_{ef} = (alpha beta + yz)/2,
M^-_{ef} = (alpha beta - yz)/2.                     (19)
```

Indeed, a path contains both edges exactly when its endpoints lie one in each
outer component. Among those `alpha beta` pairs, the signed sum
`(# even)-(# odd)` factors as `yz`. Formulas (18)--(19) follow. They are
unchanged by complementing a cut side or globally reversing all vertex signs.

Summing the two channels gives the unsigned path-incidence Gram matrix

```text
M = M^+ + M^- = sum_p z_p z_p^T.
```

Its diagonal is the cut coefficient, while for `e != f` its entry is
`alpha beta`. Taking `a` to be the all-ones vector recovers the inherited
hop-rank allocation. Taking `a` on two edges recovers first-moment support
inequalities for the four membership bins of two cuts. General support of
`a` couples arbitrarily many cuts in one inequality.

This remains only a necessary rank-allocation relaxation. It does not assert
that a passing rank matching comes from additive tree distances.

### Signed second-moment corollary at order 18

Take `a=w` in (17) and subtract the odd channel from the even channel. For
`n=18`, choose the global sign with `delta=4`. Equations (18)--(19) give

```text
sum_e w_e^2 x_e(4-x_e)
 + 2 sum_{e<f} w_e w_f y_{e|f} y_{f|e}
 = sum_{d=1}^{153} (-1)^d d^2
 = -11781.                                         (20)
```

Here each `y` is the signed imbalance of the corresponding outer component.
The target arithmetic is

```text
sum_{even d<=153} d^2 = 596904,
sum_{odd  d<=153} d^2 = 608685,
596904-608685 = -11781.
```

The unsigned companion is

```text
w^T M w = sum_{d=1}^{153} d^2 = 1205589.
```

Equation (20) is topology-aware. Independent marginal choices of the `x_e`
do not determine its off-diagonal outer-component products.

## 2. Selected-edge block Hall theorem and odd-quotient tail packing

Delete any selected set of physical edges and call the resulting actual named
components `K_i`. For a component pair `i,j`, the quotient route determines
two exit ports. Let `lambda_ij` be the distance between those ports, let
`h_ij` be the number of physical edges on that port-to-port path, and let

```text
B_ij = {d(u,v): u in K_i, v in K_j}.
```

Then

```text
|B_ij| = |K_i||K_j|,
B_ij subset [lambda_ij,N],
B_ij intersect W = {lambda_ij} if h_ij=1,
B_ij intersect W = emptyset      if h_ij>=2.       (21)
```

The singleton in (21) is the selected edge joining adjacent quotient
components. To prove (21), write every cross distance as the nonnegative depth
from `u` to its exit port, plus `lambda_ij`, plus the nonnegative depth from
the other exit port to `v`. A cross pair cannot be the endpoint pair of an
edge internal to either component. If `h_ij=1`, exactly the selected edge's
endpoint pair occurs. If `h_ij>=2`, no cross pair is a physical-edge endpoint
pair. Uniqueness of every distance rank then gives the claimed intersections.

For each component pair define its allowed rank set by the right side of
(21), also imposing any known parity. The actual `B_ij` for distinct component
pairs are mutually disjoint. Consequently, for every family `F` of component
pairs,

```text
sum_{ij in F} |K_i||K_j|
    <= | union_{ij in F} Allowed_ij |.              (22)
```

These are the capacitated Hall inequalities for the abstract rank-allocation
relaxation. Conversely, all inequalities (22) are sufficient for an injection
of the requested number of abstract rank slots into the allowed sets (clone
each component-pair demand and apply Hall). That converse is only about rank
slots: it supplies no rooted depth sets, additive block, ports, or tree lift.

### Odd-edge quotient specialization

Now delete all `r` odd physical edges. Every resulting even component is
monochromatic for `sigma`, and the quotient `H` is a tree whose edges are the
odd physical edges. Put `m_i=|K_i|` and let `ell_ij` be quotient distance.
Every distance in `B_ij` has parity `ell_ij`. Moreover, the `ell_ij` odd
bridge weights are distinct positive odd integers, so

```text
lambda_ij >= 1+3+...+(2 ell_ij-1) = ell_ij^2.       (23)
```

For any integer `ell>=2`, set `p=ell mod 2`. Applying (22) simultaneously to
all component pairs with `ell_ij>=ell` and `ell_ij=p (mod 2)` yields the
shared-tail inequality

```text
sum_{i<j: ell_ij>=ell, ell_ij congruent ell (mod 2)} m_i m_j
 <= #{d in [ell^2,N]: d congruent p (mod 2), d notin W}.   (24)
```

This is stronger than checking the inherited pairwise capacity separately:
all the displayed component-pair blocks compete for one common rank pool.
An even stronger port-aware suffix family follows directly from (22): for
every threshold `t` and parity `p`, sum the demands of any chosen nonadjacent
component pairs of parity `p` with `lambda_ij>=t`; their total is at most the
number of parity-`p` nonphysical ranks in `[t,N]`.

The strengthening over separate pairwise caps is strict as an abstract
necessary relaxation. Let the odd quotient contain a path
`v_0--...--v_10`, attach three leaf components at `v_0`, and attach two leaf
components at `v_10`. Initially all 16 quotient components are singletons;
enlarge one nonleaf component in each quotient color from order 1 to order 2.
The total order is then 18 and the weighted quotient-color totals are `7|11`.
Each of the six left-leaf/right-leaf component pairs has product 1 and quotient
distance 12. Separately, every pair passes the inherited coarse capacity
`1<=5`. Jointly, all six blocks require distinct even ranks at least
`12^2=144`, but only

```text
{144,146,148,150,152}
```

are available even before physical-rank puncturing. Inequality (24) rejects
`6<=5`. This is a strictness witness for the relaxation, not a Leech candidate.

At order 18, (24) is explicitly

```text
left side <= 77-floor(ell^2/2)
             - #{w in W: w>=ell^2 and w congruent ell (mod 2)}.   (25)
```

For `ell=2`, weight 2 is the unique even physical rank below 4, so (25) gives

```text
sum_{i<j: ell_ij even and ell_ij>=2} m_i m_j <= 59+r.     (26)
```

For `ell=3`, it gives

```text
sum_{i<j: ell_ij odd and ell_ij>=3} m_i m_j
 <= 73 - #{odd physical weights at least 9}.             (27)
```

Equations (24)--(27) use quotient incidence and, in their sharper forms,
port-to-port lengths and the actual physical-weight set. They cannot be
imposed on a histogram of component sizes or cut coefficients alone.

### Scope for `r=3,4`

The bare size versions do not close either low-odd layer. For example, at
`r=3`, (26) has right side 62; on a `P4` quotient its left side is
`m_1 m_3+m_2 m_4`, and on a `K1,3` quotient it is the sum of the three leaf
products. Splitting totals 11 and 7 between two positive parts gives maxima
30 and 12, so the `P4` left side is at most 42. Splitting one total among the
three positive leaves of the star gives maximum 40 (for total 11). At `r=4`,
the analogous right side is 63. The `P5` and fork bipartitions have three
component parts on one color and two on the other, whose combined maximum is
`40+12=52`; four positive star leaves of total 11 have pair-product sum at
most 45. Thus the bare size tests are automatic in all three quotient shapes.
The port-aware inequalities can still prune a specified bridge/port
assignment, but no universal `r=3` or `r=4` obstruction is claimed.

## 3. Hostile histogram counterexample

Even the multiset of `(cut coefficient, physical weight)` pairs does not
determine the multicut matrices. Take the six-vertex broom with edges

```text
c--x--y,  c--a,  c--b,  c--d.
```

The central edge `cx` has cut coefficient `2*4=8`; the other four edges all
have coefficient 5. Yet

```text
M_{cx,xy}=4,
M_{cx,ca}=M_{cx,cb}=M_{cx,cd}=2.
```

Indeed, paths containing `cx,xy` pair `y` with one of `c,a,b,d`, whereas
paths containing `cx,ca` pair `a` with one of `x,y`. Swapping two distinct
weights between `xy` and `ca` preserves the complete multiset
`{(c_e,w_e)}` but changes `(Mw)_{cx}` by twice their weight difference.
The loss is operationally visible. Give `cx` weight 5 and the four leaf edges
the weight set `{1,2,3,4}`. With weight 1 on distal edge `xy`, the central-cut
rank sum is

```text
8*5 + 4*1 + 2*(2+3+4) = 62.
```

For the unit probe on `cx`, (16) requires at least

```text
5 + (6+7+8+9+10+11+12) = 68,
```

because the seven nonedge pairs crossing that cut must receive seven distinct
remaining ranks. Move weight 4 to `xy` and weight 1 to a center leaf; the same
histogram now gives central-cut sum

```text
8*5 + 4*4 + 2*(1+2+3) = 68.
```

Thus the first placement fails this sound multicut inequality while the
second meets its lower equality, despite identical `(coefficient,weight)`
histograms. Neither placement is asserted to be a Leech tree; this is a
data-loss counterexample, not a candidate or a sufficiency example.

## 4. Non-sufficiency warning

- Parity-resolved use requires one coherent vertex character, not independently
  selected cut imbalances.
- Equations (22)--(27) are shared rank-capacity relaxations. Passing them does
  not establish direct-sum injectivity, compatible ports, or a positive lift.
- A cut-coefficient histogram lacks the intersection matrix, outer-component
  signed products, quotient incidence, and port lengths needed here.
