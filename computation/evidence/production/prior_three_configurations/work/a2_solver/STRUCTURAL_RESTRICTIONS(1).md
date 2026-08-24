# Sixty-six verified structural restrictions

## Standing setting and notation

Throughout, $T=(V,E,w)$ is a finite simple tree with $n=|V|$, strictly
positive integral edge weights, and

\[
N=\binom n2.
\]

The tree is assumed to be a **Leech tree**: the map sending an unordered pair
of distinct vertices to its weighted distance is a bijection onto
$\{1,2,\ldots,N\}$. An edge of $T$ is called a *physical edge* when it
must be distinguished from an edge of a quotient tree. For a physical edge
$e$, deleting $e$ gives sides of orders $s_e$ and $n-s_e$, and
$c_e=s_e(n-s_e)$ is its cut coefficient.

The numbered statements below are the 66 verified structural theorem
families in the accepted snapshot. They group 324 claim-bearing Lean
declarations and should not be read as 66 logically independent atomic
theorems. The word *restriction* is used broadly:
some entries are obstructions, while others are necessary identities,
conditional implications, exact forward decompositions, scoped converses, or
counterexamples that delimit an invalid inference. Each scope sentence is
part of the statement.

## Spectrum, parity, and cuts

1. **T1 — The first two physical weights.** If $n\ge 3$, all physical edge
   weights are distinct elements of $\{1,\ldots,N\}$, and there is exactly
   one physical edge of weight $1$ and exactly one of weight $2$. **Scope:**
   This is a structural consequence of the exact distance spectrum, not a
   finite-search conclusion.

2. **T2a — Forced least missing positive distance.** Fix a physical edge
   $e$, expose precisely the physical edges of weight less than $w(e)$,
   and let $D_e$ be the set of distances internal to the components of the
   resulting prefix forest. Then
   \[
   \operatorname{mex}_{+}(D_e)=w(e),
   \]
   so $e$ has minimum weight among the unexposed physical edges. **Scope:**
   The statement concerns the actual smaller-weight prefix of a fixed tree.

3. **T2b — Persistence of the actual-port merge block.** Let $a,b$ be the
   actual endpoints of $e$ in its two incident prefix components $A,B$.
   The indexed values
   \[
   d_A(u,a)+w(e)+d_B(b,v),\qquad (u,v)\in A\times B,
   \]
   are the corresponding distances in $T$; they are injective, lie in
   $\{1,\ldots,N\}$, avoid $D_e$, and remain present in every later prefix
   spectrum. The internal prefix spectra grow monotonically. **Scope:** This
   gives no completeness theorem for a construction or search procedure.

4. **T3a — Root-parity equation.** For any root $o$, let $a$ be the
   number of vertices at even weighted distance from $o$. Then
   \[
   a(n-a)=\left\lceil\frac N2\right\rceil.
   \]
   **Scope:** This is a necessary equation, not a sufficient existence
   criterion.

5. **T3b — Taylor order restriction.** The root-parity equation forces
   \[
   n=t^2\quad\text{or}\quad n=t^2+2
   \]
   for some $t\in\mathbb N$. At order $18$, the two parity classes have
   orders $7$ and $11$. **Scope:** These are necessary conditions only.

6. **T4 — Cut checksum.** Every Leech tree satisfies
   \[
   \sum_{e\in E}s_e(n-s_e)w(e)=\frac{N(N+1)}2.
   \]
   At order $18$, the sum is $11781$. **Scope:** The summands refer to
   actual deletion cuts and indexed vertex-pair paths.

7. **T5 — Indexed direct-sum condition at every edge.** If $e=ab$ has
   weight $w$, root the two sides of $T-e$ at $a,b$, and put
   $α(u)=d_T(a,u)$, $β(v)=d_T(b,v)$. Every cross distance is
   $w+α(u)+β(v)$; both depth maps and the indexed cross-sum map are
   injective. Equivalently, after regarding all depths as integers,
   \[
   α(u)-α(u')=β(v')-β(v)
   \quad\Longrightarrow\quad u=u',\ v=v'.
   \]
   If $c=s(n-s)$, then $w\le N-c+1$. **Scope:** Indices and
   multiplicities are essential; this is not a statement about two
   unindexed marginal value sets.

## Order 18 and parity-tail structure

8. **T6 — Lower bound on the largest physical weight.** In an order-$18$
   Leech tree,
   \[
   \max_{e\in E}w(e)\ge 19.
   \]
   **Scope:** No further finite-band exclusion for the maximum weight is
   asserted beyond this lower bound.

9. **T7 — Hop-diameter bound.** Every simple path in an order-$18$ Leech
   tree contains at most $14$ physical edges. **Scope:** This is a
   graph-level path restriction.

For Restrictions 10–19, choose a sign function
$σ:V\to\{-1,1\}$. For a
nonempty set $F\subseteq E$, let $C_F$ be the number of indexed unordered
vertex pairs whose path contains every edge of $F$, and let

\[
K_F=\sum_{\{u,v\}:\,F\subseteq P_{uv}}σ(u)σ(v).
\]

When $σ(v)=(-1)^{d_T(o,v)}$, write $C_F^+$ and $C_F^-$ for the
even- and odd-distance support counts.

10. **T8a0 — Collinear outer factorization.** If the nonempty set $F$ lies
    on a common canonical vertex-pair path, its two extreme selected edges
    determine outer vertex sets $L_F,R_F$ for which
    \[
    C_F=|L_F||R_F|,
    \qquad
    K_F=\Bigl(\sum_{u\in L_F}σ(u)\Bigr)
          \Bigl(\sum_{v\in R_F}σ(v)\Bigr).
    \]
    **Scope:** Nonempty selection and common-path support are required.

11. **T8a1 — Noncollinear vanishing.** If no canonical vertex-pair path
    contains every edge of $F$, then $C_F=K_F=0$. **Scope:** The exact
    no-common-path premise cannot be weakened.

12. **T8a — Extreme-component form from the actual tree.** In the collinear
    case, one can orient the supporting path and choose its two extreme
    selected edges. The resulting nested cuts and outer components admit an
    indexed equivalence between supported endpoint pairs and
    $L_F\times R_F$, yielding the factorizations in Restriction 10.
    **Scope:** The assertion is the existence of this construction; it does
    not assert a unique orientation or replace indexed support by value sets.

13. **T8b — Parity-resolved support counts.** With the distance-parity sign,
    \[
    C_F^++C_F^-=C_F,
    \qquad
    2C_F^+=C_F+K_F,
    \qquad
    2C_F^-=C_F-K_F.
    \]
    **Scope:** These are identities for actual indexed pairs, not a
    substitution of value images for indexed supports.

14. **T8c — Exact low-degree path coefficients.** In the first three power
    expansions of the distance spectrum, every singleton, pair, or triple
    coefficient is exactly the corresponding indexed parity support count.
    In particular, a three-edge coefficient vanishes if no vertex-pair path
    contains all three distinct selected edges. **Scope:** Repeated entries
    collapse to a finite set before the coefficient is interpreted.

15. **T8d — Parity-resolved moment expansion.** For
    $p\in\{+,-\}$, let
    $P_k^p$ be the $k$-th power sum of target distances of parity $p$.
    For $k=1,2,3$, $P_k^p$ is exactly the expansion obtained by summing
    the one-, two-, and three-edge monomials weighted by their indexed
    parity support counts. For example,
    \[
    \begin{aligned}
    P_1^p&=\sum_e C_e^p w_e,\\
    P_2^p&=\sum_e C_e^p w_e^2
       +2\sum_{e<f}C_{\{e,f\}}^p w_ew_f,
    \end{aligned}
    \]
    with the analogous multinomial formula in degree $3$. **Scope:** Only
    degrees $1,2,3$ are asserted.

16. **T8e — Exact order-$18$ parity moments.** The even and odd target
    classes have sizes $76$ and $77$. Their power sums in degrees
    $1,2,3$, respectively, are
    \[
    (5852,5929),\qquad
    (596904,608685),\qquad
    (68491808,70300153).
    \]
    **Scope:** The ordered pairs in each display are
    $(\text{even},\text{odd})$.

17. **T8f — Order-$18$ cut feasibility equations.** Normalize the parity
    sign so that $Σ_{v\in V}σ(v)=4$. For one side $S$ of a cut, put
    $s=|S|$, $x=Σ_{v\in S}σ(v)$, $c=s(18-s)$, and
    $κ=x(4-x)$. If $h^+$ and $h^-$ are the even and odd cross-pair
    counts, then
    \[
    2h^+=c+κ,
    \qquad
    2h^-=c-κ,
    \]
    subject to $x\equiv s\pmod 2$, $|x|\le s$, and
    $|4-x|\le18-s$. **Scope:** These joined-count conditions do not prove
    that a tree realizing them exists.

18. **T9a — Parity-tail moment bounds.** Across an edge of weight $w$, fix
    a residue $p\in\{0,1\}$, and suppose the cross-distance block of that
    parity has $h>0$ values. Let $L_p(w)$ be the least integer at least
    $w$ congruent to $p\pmod2$. Write $P_k^0=P_k^+$ for the even target
    moment and $P_k^1=P_k^-$ for the odd target moment. For $k=1,2,3$,
    \[
    \sum_{j=0}^{h-1}(L_p(w)+2j)^k
    \le \sum_{d\text{ in the cross block}}d^k
    \le \sum_{\substack{w\le d\le N\\d\equiv p\ (2)}}d^k
    \le P_k^p.
    \]
    In particular, $L_p(w)+2(h-1)\le N$. **Scope:** The parity residue and
    nonempty-block hypotheses are required.

19. **T9b — Saturation of a parity tail.** If the cross block in Restriction
    18 has the same cardinality as the entire eligible parity tail, then its
    value set equals that tail. **Scope:** This is equality of value sets; it
    does not identify indexed ownership or construct a rooted realization.

20. **T10 — Conditional weight-$67$ side mass.** If an order-$18$ Leech
    tree has a physical edge of weight $67$ whose deletion has side orders
    $9|9$, then its normalized signed mass on either oriented side belongs
    to
    \[
    \{-1,1,3,5\}.
    \]
    **Scope:** The theorem assumes such an edge; it neither produces nor
    excludes one and does not assert that it is the largest edge.

21. **T10b — Conditional weight-$68$ odd residual.** If an order-$18$
    physical edge has weight $68$, a $9|9$ cut, and normalized side mass
    $-1$ or $5$, then its odd cross-distance block is
    $\{69,71,\ldots,153\}$. After subtracting $68$, the residual set is
    $\{1,3,\ldots,85\}$, with residual moments
    \[
    1849,\quad105995,\quad6835753
    \]
    and cross-block moments
    \[
    4773,\quad556291,\quad67628637
    \]
    in degrees $1,2,3$. **Scope:** Every conclusion is conditional on the
    displayed edge, cut, and side-mass hypotheses.

22. **T11 — Exclusion of one odd physical edge.** For every $n\ge18$, a
    Leech tree cannot have exactly one odd physical edge. **Scope:** The
    required decomposition is derived from the tree; it is not an additional
    certificate hypothesis.

23. **T12a — Parity consequence of exactly two odd edges.** If $n\ge5$ and
    a Leech tree has exactly two odd physical edges, then the number of odd
    integers in $\{1,\ldots,N\}$ is even. **Scope:** This is only a parity
    conclusion within the exactly-two-odd architecture.

24. **T12b — Order $18$ excludes exactly two odd edges.** An order-$18$
    Leech tree cannot have exactly two odd physical edges, because its target
    interval contains $77$ odd values. **Scope:** This does not exclude
    odd-edge counts $3,4,\ldots,15$.

25. **C17 — Order $18$ excludes seventeen odd edges.** An order-$18$
    Leech tree cannot have all $17$ of its physical edges odd, since the
    forced physical edge of weight $2$ is even. **Scope:** This verified
    family is `C17`, distinct from the uncredited computational family
    `C017`.

## Edges, quotients, and extension operations

26. **F1 — Safe first-edge dichotomy.** Assume $n\ge4$, and let $e_1,e_2$
    be the weight-$1$ and weight-$2$ physical edges. If they are adjacent,
    no weight-$3$ physical edge exists and a unique weight-$4$ physical
    edge exists. If they are disjoint, a unique weight-$3$ physical edge
    exists. **Scope:** This is the two-branch conclusion, not the refined
    eight-row classification in Restriction 43.

27. **F4 — Exact hole hierarchy at every edge.** For an edge $e=ab$ of
    weight $w$, let $L,R$ be the two rooted sides and put
    \[
    S_e=\{d_T(a,u)+d_T(b,v):(u,v)\in L\times R\},
    \qquad
    H_e=\{0,\ldots,N-w\}\setminus S_e.
    \]
    Then
    \[
    |H_e|=N-w+1-|L||R|,
    \]
    and $w+H_e$ is the disjoint union of the two internal spectra at least
    $w$. For degrees $0,1,2,3$, both ordinary and alternating power sums
    of $H_e$ complement the corresponding indexed rooted-product moments
    to the full interval moments. **Scope:** These are necessary identities,
    not a realization converse.

For Restrictions 28–32, delete all odd physical edges. The remaining
even-edge components become vertices of the *odd-edge quotient* $Q_T$, and
within one component define $ρ_C(u,v)=d_T(u,v)/2$. A *port* is the actual
vertex at which a deleted odd bridge meets a component.

28. **F9a — Actual odd-edge quotient tree.** Halving the internal metrics of
    the even components and retaining every indexed odd bridge produces a
    connected acyclic quotient. The indexed odd physical edges are in
    bijection with the quotient edges. **Scope:** This is a forward
    construction from an actual Leech tree, not a lifting theorem.

29. **F9b — Canonical quotient-route formula.** Suppose the canonical simple
    quotient path from the component of $x$ to the component of $y$ crosses
    $k$ actual odd bridges of weights $2λ_i+1$, with every entry and exit
    port retained. Let $R(x,y)$ be the sum of the $λ_i$ and every halved
    internal segment along this lifted route, including the segment from
    $x$ to the first port and that from the last port to $y$. Then
    \[
    d_T(x,y)=2R(x,y)+k
            =2\left(R(x,y)+\left\lfloor\frac k2\right\rfloor\right)
             +(k\bmod2).
    \]
    **Scope:** The actual sequence of ports cannot be replaced by unrelated
    marginal depth profiles.

30. **F9c — Indexed pair partition and rank polynomials.** Unordered vertex
    pairs partition, with multiplicity, into pairs internal to one even
    component and Cartesian products over every pair of distinct components.
    The corresponding rank-generating polynomials decompose coefficientwise,
    and each coefficient is the exact cardinality of its indexed fibre.
    **Scope:** The fibre indices and multiplicities are part of the result.

31. **F9d — Coefficientwise odd/even quotient identities.** Let
    $O=\lceil N/2\rceil$ and $E=\lfloor N/2\rfloor$. The aggregate sum of
    the half-rank polynomials of all indexed cross blocks whose quotient
    routes have odd length has coefficient $1$ at every $0\le h<O$ and
    coefficient $0$ otherwise. The aggregate sum of all internal blocks and
    all positive even-route cross blocks has coefficient $1$ at every
    $1\le h\le E$ and coefficient $0$ otherwise. **Scope:** These are
    identities for the indicated sums over all qualifying indexed blocks,
    not coefficient-one assertions for each block and not a realization
    criterion.

32. **F9e — Forward two-port coordinates.** For named vertices $p,q,u$ in
    one even component, set
    $a=ρ(p,u)$, $b=ρ(q,u)$, and $δ=ρ(p,q)$. There exist
    $c,h\in\mathbb N$, with $0\le c\leδ$, such that
    \[
    a=h+c,
    \qquad b=h+(δ-c),
    \qquad b+2c=a+δ,
    \qquad δ+2h=a+b.
    \]
    **Scope:** The ports may coincide, and no converse is asserted.

33. **D3a — No normalized weighted-path presentation.** If $n\ge5$, the
    vertices of a Leech tree cannot be ordered
    $v_0,v_1,\ldots,v_{n-1}$ so that its physical edges are precisely the
    consecutive pairs $v_{i-1}v_i$ and every distance is the corresponding
    interval sum of the consecutive edge weights. **Scope:** This is the
    graph-level obstruction to a weighted-path topology.

34. **D3b — The physical spectrum is not the full initial interval.** If
    $n\ge5$, then
    \[
    \{w(e):e\in E\}\ne\{1,2,\ldots,n-1\}.
    \]
    **Scope:** The theorem includes the adapter showing that the contrary
    hypothesis would force the prohibited spanning-path presentation.

35. **D4a0 — Exact one-leaf tail criterion.** Let a base tree have order
    $m\ge1$, and attach a new leaf of weight $q$ at an old vertex $v$.
    The new leaf supplies exactly the new target interval
    $\{\binom m2+1,\ldots,\binom m2+m\}$ if and only if
    \[
    q=\binom m2+1
    \quad\text{and}\quad
    \{d_T(v,u):u\in V\}=\{0,1,\ldots,m-1\}.
    \]
    **Scope:** This characterizes the literal operation with the old tree and
    its weights unchanged.

36. **D4a — No unchanged one-leaf extension after order $3$.** If a Leech
    tree has order $m\ge4$, attaching one new leaf while preserving the old
    induced tree and all old physical weights cannot produce another Leech
    tree. **Scope:** Only this exact literal edge-set operation is excluded.

37. **D4a2 — Exact small-order one-leaf boundary.** For $m\ge2$, an
    unchanged literal one-leaf step between Leech trees exists if and only if
    $m\in\{2,3\}$. Under the separate convention that admits the vacuous
    order-$1$ spectrum, the $1\to2$ step also exists. **Scope:** These are
    the complete positive small-order cases for this operation only.

38. **D4b — No literal weight-preserving subdivision.** Replacing one
    physical edge by two positive physical edges through a new vertex, while
    preserving every other edge and weight and preserving the original total
    weight of the subdivided edge, cannot take one Leech tree to another.
    **Scope:** Reweightings outside this literal operation are not addressed.

39. **D4c — No literal unscaled bridge.** Let two Leech trees have orders
    $a,b\ge2$. Preserving both internal weighted trees and joining named
    ports by exactly one new bridge cannot yield a Leech tree, because the
    two unchanged internal distance intervals overlap. **Scope:** The
    order-$1$ component case belongs to the one-leaf problem, and scaled or
    reweighted bridges are not covered.

40. **D5a — Range obstruction for an unchanged subtree.** Suppose $m\ge1$
    and an order-$m$ Leech tree embeds as an induced connected subtree of an
    order-$m+k$ Leech tree, all old indexed distances remain unchanged, and
    $k\ge2$. Necessarily
    \[
    \binom m2+3\le mk+\binom k2.
    \]
    **Scope:** The embedding and preservation of the indexed old metric are
    essential hypotheses.

41. **D5c — No unchanged extension by two vertices.** If $m\ge5$, an
    order-$m$ Leech tree has no unchanged-subtree extension by exactly two
    new vertices. **Scope:** This is the $k=2$ corollary of Restriction 40.

42. **D5b — Order-$18$ unchanged-extension gap.** An order-$18$ Leech
    tree has no unchanged-subtree extension by
    $k\in\{2,3,4,5,6,7\}$ new vertices. **Scope:** No value of $k$
    outside this exact interval is excluded here.

## Refined rank, path, multicut, and quotient restrictions

43. **G001 — Eight local first-edge configurations.** For $n\ge5$, write
    $e_j$ for the physical edge of weight $j$ when it exists, and let
    $A(f)$ be the set of already exposed physical edges adjacent to $f$.
    If $e_1,e_2$ are adjacent, then $e_3$ is absent and $e_4$ exists; the
    four possible positions of $e_4$ give the first four rows below. If
    $e_1,e_2$ are disjoint, then $e_3$ exists, and its four possible
    positions give the last four rows.

    | Branch | Adjacency set | Forced further physical-edge status | Exposed distance set / next positive missing value | Order-$18$ cut consequence |
    |---|---|---|---|---|
    | adjacent | $A(e_4)=\varnothing$ | $e_5$ exists | $\{1,2,3,4\}$ / $5$ | — |
    | adjacent | $A(e_4)=\{e_1\}$ | $e_5,e_7$ absent; $e_6$ exists | $\{1,2,3,4,5,7\}$ / $6$ | $c_{e_1}\ge32$ |
    | adjacent | $A(e_4)=\{e_2\}$ | $e_5$ exists; $e_6,e_7$ absent | $\{1,2,3,4,6,7\}$ / $5$ | $c_{e_2}\ge32$ |
    | adjacent | $A(e_4)=\{e_1,e_2\}$ | $e_5,e_6$ absent; $e_7$ exists | $\{1,2,3,4,5,6\}$ / $7$ | — |
    | disjoint | $A(e_3)=\varnothing$ | $e_4$ exists | $\{1,2,3\}$ / $4$ | — |
    | disjoint | $A(e_3)=\{e_1\}$ | $e_4$ absent; $e_5$ exists | $\{1,2,3,4\}$ / $5$ | — |
    | disjoint | $A(e_3)=\{e_2\}$ | $e_4$ exists; $e_5$ absent | $\{1,2,3,5\}$ / $4$ | — |
    | disjoint | $A(e_3)=\{e_1,e_2\}$ | $e_4,e_5,e_6$ absent; $e_7$ exists | $\{1,2,3,4,5,6\}$ / $7$ | $c_{e_3}\ge32$ |

    **Scope:** This is an exhaustive local prefix classification, not a
    global exclusion; the uniform eight-row formulation does not apply at
    order $4$.

44. **G002 — Physical-rank puncturing.** Write the physical weights in
    increasing order as $w_1<\cdots<w_{n-1}$, and let $C_i$ be the
    crossing-distance block of $e_i$, of size $c_i$. Then
    \[
    C_i\cap\{w_1,\ldots,w_{n-1}\}=\{w_i\}
    \]
    and
    \[
    w_i+c_i+(n-1-i)\le N+1.
    \]
    Equality holds exactly when
    $C_i=[w_i,N]\setminus\{w_{i+1},\ldots,w_{n-1}\}$. Separating odd
    and even ranks gives the corresponding coarse and rank-aware punctured
    channel bounds. Equality in a rank-aware channel holds exactly when its
    permitted parity tail is exhausted. Equality in the corresponding coarse
    channel additionally requires that no unused rank of that parity lies
    below $w_i$. **Scope:** These are necessary structural restrictions.

45. **G003 — Signed cut moment and imbalance.** For a root-parity character
    $χ$, let $δ=\sum_{v\in V}χ(v)$, and let $x_i$ be the signed mass of one
    side of $e_i$. Then
    \[
    \sum_i w_i x_i(δ-x_i)=\sum_{d=1}^N(-1)^d d.
    \]
    At order $18$, choose the global sign with $δ=4$. Then
    \[
    \sum_i w_i(x_i-2)^2=4\sum_iw_i+77,
    \]
    so some oriented side mass satisfies $x_i<0$ or $x_i>4$. **Scope:**
    This is a necessary, orientation-invariant obstruction after allowing
    side complementation.

46. **G004 — Punctured path-segment statistics.** Let an actual contiguous
    segment of $h$ physical edges have total weight $L$, and let the two
    extreme rooted depth sets be
    $X=\{x_0<\cdots<x_{a-1}\}$ and
    $Y=\{y_0<\cdots<y_{b-1}\}$. The $ab$ cross distances form the
    distinct block $L+(X+Y)$, punctured by all forbidden physical ranks.
    If $r_0<\cdots<r_{M-1}$ are the allowed offsets, then
    \[
    r_{(i+1)(j+1)-1}\le x_i+y_j
    \le r_{M-(a-i)(b-j)}.
    \]
    With $Δ(S)=|S|\sum_{s\in S}s^2-(\sum_{s\in S}s)^2$,
    \[
    Δ(X+Y)=b^2Δ(X)+a^2Δ(Y)
      \ge\frac{(ab)^2((ab)^2-1)}{12}.
    \]
    **Scope:** The segment and rooted components are actual contiguous data
    from the tree.

47. **G005 — Selected-edge gluing polynomial.** Delete any selected physical
    edges, obtaining actual components $K_i$. Let $P_i(z)$ be the internal
    pair-distance polynomial, $R_{i,p}(z)$ the depth polynomial at an
    actual port $p$, and $L_{ij}$ the route contribution between the two
    extreme ports. Then
    \[
    P_T(z)=\sum_iP_i(z)+
      \sum_{i<j}z^{L_{ij}}R_{i,p_{ij}}(z)R_{j,p_{ji}}(z).
    \]
    For a Leech tree this equals $z+\cdots+z^N$ coefficientwise, forcing
    every displayed cross product to be internally $0/1$ and all blocks to
    be mutually disjoint. **Scope:** The theorem uses actual ports and jointly
    indexed ranks, not independently chosen marginal profiles.

48. **G006 — Coupled two-cut four-bin allocation.** For two distinct edges,
    orient their deletion components as $A-M-B$, of orders $a,m,b$. The
    four path-membership bins $11,10,01,00$ have sizes
    \[
    ab,\quad am,\quad bm,\quad N-ab-am-bm.
    \]
    For $p\ge1$, let $R_e^{(p)},R_f^{(p)}$ be the two cut-block
    $p$-th moments, and let $\mathcal L_p(k),\mathcal U_p(k)$ be the sums
    of the $k$ smallest and $k$ largest $p$-th powers in the target
    interval. Then
    \[
    \mathcal L_p(am)-\mathcal U_p(bm)
      \le R_e^{(p)}-R_f^{(p)}
      \le \mathcal U_p(am)-\mathcal L_p(bm),
    \]
    and
    \[
    \mathcal L_p(ab)+\mathcal L_p(ab+am+bm)
      \le R_e^{(p)}+R_f^{(p)}
      \le \mathcal U_p(ab)+\mathcal U_p(ab+am+bm).
    \]
    A gap-free, disjoint four-bin subset allocation exists if and only if a
    total four-labeling of the target ranks realizes all prescribed
    cardinalities, moments, parities, and physical-rank intersections.
    **Scope:** The finite equivalence concerns this exact allocation model;
    passing it is not a tree realization.

49. **G007 — Hop-rank allocation.** Let $h_{uv}$ be unweighted path length
    and
    $H_e=\sum_{\{u,v\}:e\in P_{uv}}h_{uv}$. Then
    \[
    \sum_{u<v}h_{uv}d_T(u,v)=\sum_e w(e)H_e,
    \]
    where, for $e=ab$, the cut sides $A,B$ are rooted at $a,b$,
    \[
    H_e=|A||B|+|B|\sum_{u\in A}h_A(u,a)
               +|A|\sum_{v\in B}h_B(b,v).
    \]
    The nonedge ranks obey the corresponding sharp rearrangement bounds.
    More strongly, ranks partition into parity/hop bins $R_{p,h}$ with
    prescribed cardinalities, sums, and $R_{p,1}$ equal to the physical
    weights of parity $p$. **Scope:** These are necessary conditions and
    require the actual edge-to-weight and parity placement.

50. **G008 — Odd-quotient capacity.** In an order-$18$ Leech tree, if two
    even components of orders $m_i,m_j$ are at quotient distance $ℓ$, then
    \[
    m_im_j\le77-\left\lfloor\frac{ℓ^2}{2}\right\rfloor.
    \]
    Hence the odd-edge quotient has diameter at most $12$, and every
    quotient path of length $12$ contains the physical edge of weight $1$.
    For rooted signed moments
    $R_j(H)=\sum_v(-1)^{d_H(o,v)}d_H(o,v)^j$, joining rooted components
    $A,B$ by an edge of weight $w$ gives
    \[
    R_j(T)=R_j(A)+(-1)^w
      \sum_{q=0}^j\binom jq w^{j-q}R_q(B),
    \]
    together with the corresponding trinomial convolution for signed
    unordered-pair moments. **Scope:** These statements concern actual
    quotient routes and actual rooted merges extracted from a Leech tree.

51. **G009 — Joint signed-cut-flow criterion.** Root a fixed order-$18$
    topology and orient each edge toward a descendant subtree. Let $x_v$ be
    that subtree's proposed signed mass and define
    \[
    b_v=x_v-\sum_{u\text{ child of }v}x_u
    \]
    for nonroot $v$, with $b_o=\pm4-\sum_{u\text{ child of }o}x_u$ at
    the root. These cut masses arise jointly from one weighted-depth parity
    character if and only if
    \[
    b_v\in\{-1,1\}\quad\text{for every }v,
    \qquad
    b_ub_v=(-1)^{w(uv)}\quad\text{for every edge }uv.
    \]
    **Scope:** Incidence, root orientation, and one coherent vertex character
    are essential; marginally admissible cuts do not suffice.

52. **G010 — Named three-port median restriction.** If three named ports
    have a genuine named tripod median with positive arm lengths
    $A_0,A_1,A_2$, then the six values
    \[
    A_0,A_1,A_2,A_0+A_1,A_0+A_2,A_1+A_2
    \]
    are pairwise distinct. Equivalently, the arms are pairwise distinct and
    no arm is the sum of the other two. If one arm is $0$, only the two
    positive arms must differ. **Scope:** The median and arms are the named
    tree data; the six-value condition must not be imposed at the zero-arm
    boundary.

53. **G011 — Parity multicut rearrangement.** Choose one coherent
    root-parity character $σ(v)=(-1)^{d_T(o,v)}$; at order $18$, normalize
    its global sign by $\sum_vσ(v)=4$. In either parity channel, remove the
    endpoint pairs of physical edges of that parity. For any real edge-score
    vector, pairing the remaining path scores with the remaining target ranks
    lies between the oppositely sorted and similarly sorted dot products,
    with the standard sharp equality conditions. The parity path-incidence
    matrices have exact diagonal cut and off-diagonal outer-component
    formulas. Let $x_e$ be the signed mass of one deletion side of $e$, and,
    for distinct $e,f$, let $y_{e\mid f}$ be the signed mass of the outer
    component beyond $e$ away from $f$. Then, at order $18$,
    \[
    \sum_e w_e^2x_e(4-x_e)
      +2\sum_{e<f}w_ew_fy_{e|f}y_{f|e}=-11781.
    \]
    **Scope:** This is a topology-aware necessary condition; independent
    marginal side masses do not determine the off-diagonal terms.

54. **G012 — Capacitated Hall and shared tails.** After deleting selected
    physical edges, each actual component-pair block $B_{ij}$ has demand
    $|K_i||K_j|$, an actual route lower bound, and exact physical-rank
    exclusions; a parity constraint may also be imposed when the actual
    route data supply one. Every family $ℱ$ of blocks satisfies
    \[
    \sum_{ij\inℱ}|K_i||K_j|
      \le\left|\bigcup_{ij\inℱ}\operatorname{Allowed}_{ij}\right|.
    \]
    Conversely, all such inequalities are equivalent to an injection of
    cloned abstract demand slots into the allowed ranks. For the odd-edge
    quotient of an order-$18$ Leech tree, write $W=\{w(e):e\in E\}$ for
    the physical-weight set, let $m_i=|K_i|$, and let $ℓ_{ij}$ denote the
    quotient distance between $K_i$ and $K_j$. Every integer $ℓ\ge2$ gives
    the shared parity-tail inequality
    \[
    \sum_{\substack{i<j:\,ℓ_{ij}\geℓ\\ℓ_{ij}\equivℓ\ (2)}}m_im_j
      \le
      \#\{d\in[ℓ^2,N]:d\equivℓ\pmod2,\ d\notin W\}.
    \]
    **Scope:** The converse is only an abstract-slot Hall theorem; it supplies
    no compatible ports, rooted depths, additive blocks, or tree lift.

55. **G013 — Second-odd-weight tail bound.** Suppose the odd physical weights
    are $1=q_1<q_2<\cdots<q_r$, and the two vertex-parity classes have
    orders $a,b$. Let $S$ count original vertex pairs in distinct quotient
    components of the same quotient color. If those colors contain $k,l$
    components, then
    \[
    S\ge F(a,k)+F(b,l)\ge G_{a,b}(r),
    \quad
    F(M,k)=\frac{(k-1)(2M-k)}2.
    \]
    Here
    \[
    G_{a,b}(r)=
    \min_{\substack{k+l=r+1\\1\le k\le a,\ 1\le l\le b}}
      \bigl(F(a,k)+F(b,l)\bigr).
    \]
    These $S$ pairs inject into distinct even nonphysical ranks at least
    $q_2+1$, so, with $E=\lfloor N/2\rfloor$,
    \[
    q_2\le2(E-G_{a,b}(r))+1,
    \]
    with sharper fixed-profile physical-rank punctures. **Scope:** This is a
    necessary quotient-profile bound. Equivalently it gives an upper, not a
    lower, bound on unused even ranks below $q_2$.

56. **G014 — Companion low-rank and truncation bounds.** Write $q_2=2t+1$.
    If $I$ is the number of internal same-component pairs and $x,y$ are
    the orders of the two components incident with the weight-$1$ bridge,
    then
    \[
    t\le I,
    \qquad t\le xy,
    \qquad q_2\le2\min(I,xy)+1.
    \]
    After component profiles are forgotten, put
    \[
    H_{a,b}(r)=
    \max_{\substack{k+l=r+1\\1\le k\le a,\ 1\le l\le b}}
    \min\left\{
      \binom{a-k+1}{2}+\binom{b-l+1}{2},
      (a-k+1)(b-l+1)
    \right\}.
    \]
    The safe topology-free consequence is
    $q_2\le2H_{a,b}(r)+1$; the maximum is essential. At the order-$18$,
    $r=15$, $q_2=7$ equality boundary, the forced local prefix is the
    three-edge star of weights $1,2,4$. At the weight-$1$ port, the
    rooted half-depth polynomials satisfy
    \[
    A(z)B(z)\equiv1+z+\cdots+z^{t-1}\pmod{z^t}.
    \]
    **Scope:** Only the stated capacity, equality, port, and modulo-$z^t$
    conclusions follow; the congruence is not a full factorization unless
    additional equality hypotheses hold.

## Few-odd and block architectures

57. **G015 — Sharp exactly-two-odd bounds.** If a Leech tree has exactly two
    odd physical edges, their weights may be written $1$ and $2q+1$, and
    necessarily
    \[
    q\le10,
    \qquad q\ne7.
    \]
    If the two ports in the middle even component are distinct and the odd
    half-rank target contains ranks through $14$—in particular, if
    $n\ge9$—then $q\le6$. **Scope:** These conclusions apply only in the
    exactly-two-odd architecture and retain the stated port/rank guard.

58. **G016 — Parity-order exclusions and the common-middle-port
    obstruction.** An exactly-two-odd Leech tree does not exist at any order
    in either family
    \[
    n=(4k+2)^2\quad(k\ge1),
    \qquad
    n=(4k)^2+2\quad(k\ge1).
    \]
    In particular, this gives arbitrary-port exclusions at orders $36$ and
    $18$, respectively. Independently, for every $n\ge36$, an
    exactly-two-odd Leech tree cannot have its two odd bridges meet the same
    port in the middle even component. Hence any such tree at another
    admissible order $n\ge36$ would have distinct middle ports, and
    Restriction 57 would force $1\le q\le6$. **Scope:** The arbitrary-port
    exclusion is confined to the two displayed order families; the
    common-port theorem does not exclude all exactly-two-odd trees at every
    order $n\ge36$.

59. **G017 — Restrictions on the order-$6$-block lift.** At order $18$,
    two disjoint uniformly scaled copies of the known order-$6$ Leech tree
    already share an internal least-common-multiple distance; three scaled
    copies also violate the exact parity-profile condition. Thus any
    $6+6+6$ construction based on that fixture must change at least two
    blocks internally. The absolute block-imbalance profile must be one of
    \[
    (0,0,4),\ (0,2,2),\ (0,2,6),\ (2,2,4),\
    (2,4,6),\ (4,4,4),\ (4,6,6);
    \]
    the construction must also satisfy the exact $153$-form all-distinct
    system and the actual rooted difference-set filters. **Scope:** These
    restrictions apply to the named block architectures, not to arbitrary
    order-$18$ trees or arbitrary lifts; the $153$-form system is a
    construction template, not a candidate or completeness theorem.

60. **G018 — Odd complete-rooted-star-block obstruction.** Let $q>1$ be
    odd. Form $q$ rooted stars $K_{1,q-1}$, prescribe in each block one
    pendant weight from every nonzero even residue modulo $2q$, and join
    the roots by an arbitrary tree with positive integral weights. The
    resulting order-$q^2$ weighted tree cannot have distance spectrum
    $\{1,\ldots,\binom{q^2}{2}\}$. **Scope:** This excludes exactly the
    complete-rooted-star-block architecture, not other quotient or block
    topologies.

61. **G019 — Scalar Gaussian flexibility boundary.** For every component
    count $c\in\{4,5,\ldots,18\}$, there are explicit depth-two quotient
    data
    with positive component orders $m_v$, integer imbalances $x_v$, color
    budgets $7$ and $11$,
    \[
    |x_v|\le m_v,
    \qquad x_v\equiv m_v\pmod2,
    \qquad x^{\mathsf T}K_Qx=18+2\mathrm i,
    \quad (K_Q)_{uv}=\mathrm i^{d_Q(u,v)},
    \quad \mathrm i^2=-1.
    \]
    Hence this scalar layer alone cannot exclude any odd-edge count from
    $3$ through $17$. **Scope:** These are arithmetic certificates, not
    component spectra or Leech-tree realizations.

62. **G020 — Three-anchor coordinates and scoped reconstruction.** In an
    actual even component, three distinct named anchors and any named vertex
    admit a named tree median, a nearest projection to the three-arm
    skeleton, and nonnegative integral arm/fibre coordinates. The anchor-
    distance triple uniquely recovers the coordinate values through the usual
    signed half-sum formulas. Conversely, if a finite coordinate table also
    satisfies the formal closed-row hypotheses and is supplied with a
    compatible strictly descending parent choice, that choice decodes a
    positive-integral tree with exactly the prescribed named anchor
    distances. **Scope:** The converse ranges only over the compatible parent
    choices in this explicit closed model; it does not assert uniqueness of
    the parent structure, and raw coordinate equations or marginal anchor
    supports alone do not reconstruct a tree.

63. **G021 — Exact representation of the open three-odd branch.** In the
    formal order-$18$ `OpenMultiport` branch with exactly three odd physical
    edges, every actual quotient normalizes to one of the specified path or
    star port patterns and determines one of $720$ concrete indexed
    assignments. Actual low-distance geometry assigns each such realization
    to exactly one of ten parent-pattern classes, so the semantic assignment
    set is exactly their union. **Scope:** This is an exact representation and
    partition of the `OpenMultiport` branch; it does not say that all $720$
    indices are feasible, excluded, or an exhaustive classification of every
    three-odd tree.

64. **G022 — Four-odd quotient and Gaussian target.** If an order-$18$
    Leech tree has exactly four odd physical edges, deleting them produces
    five nonempty even components. Their quotient is isomorphic to $P_5$,
    the five-vertex fork, or $K_{1,4}$. The component orders are positive,
    sum to $18$, and have quotient-color sums $7$ and $11$. Gauged
    imbalances satisfy
    \[
    |x_v|\le m_v,
    \qquad x_v\equiv m_v\pmod2,
    \qquad x^{\mathsf T}K_Qx=18+2\mathrm i,
    \quad (K_Q)_{uv}=\mathrm i^{d_Q(u,v)},
    \quad \mathrm i^2=-1.
    \]
    In the star case the leaf-coordinate multiset is
    $\{2,-2,1,0\}$, up to the global sign convention. **Scope:** These are
    necessary quotient and scalar conditions, not a census, feasibility
    theorem, or lift.

65. **G023 — Conditional $9|9$ coefficient systems at weights $67$ and
    $66$.** Suppose an order-$18$ Leech tree has a physical edge of weight
    $w\in\{66,67\}$ whose deletion gives two rooted sides of order $9$.
    With the four parity-resolved half-depth polynomials $P,Q,R,S$, let
    $E,O$ denote the even and odd cross-distance half-rank enumerators. The
    coefficientwise decompositions are
    \[
    E=PQ+zRS,
    \qquad O=PS+RQ,
    \]
    with $0/1$ coefficients. If the rooted side imbalances are
    $\delta_A,\delta_B$, the two block sizes are
    $(81\pm\delta_A\delta_B)/2$; for odd $w$,
    $\delta_A-\delta_B=\pm4$, whereas for even $w$,
    $\delta_A+\delta_B=\pm4$. Write
    $U_m(z)=1+z+\cdots+z^m$.

    For $w=67$, write the dimensions in the order
    $(|P|,|R|;|Q|,|S|)$. Up to interchanging the sides, the permitted
    branches are:

    - imbalances $(-1,-5)$, dimensions $(4,5;2,7)$, and
      $PQ+zRS=U_{43}-z^j$ with $1\le j\le43$;
    - imbalances $(1,5)$, the mirror dimensions $(5,4;7,2)$, and
      $PQ+zRS=U_{43}-z^j$ with $1\le j\le43$; or
    - imbalance product $-3$, represented by $(1,-3)$, dimensions
      $(5,4;3,6)$, and $PS+RQ=U_{42}-z^j$ with
      $0\le j\le42$.

    For $w=66$, if the imbalance product is $-5$, then
    \[
    PS+RQ=U_{43}-z^j,\qquad 0\le j\le43,
    \]
    with product dimensions $4\times2$ and $5\times7$. If the product is
    $3$, then
    \[
    PQ+zRS=U_{43}-z^{j_1}-z^{j_2},
    \qquad
    j_1\ne j_2,\quad j_1,j_2\in\{1,\ldots,43\},
    \]
    and the shifted product has dimensions $4\times3$ or $5\times6$.
    The two raw depth rows $D_A,D_B$ also satisfy
    \[
    D_A(z)D_B(z)=U_{87}(z)-H(z),
    \]
    where $H\subseteq\{1,\ldots,87\}$, $|H|=7$, and
    $H(z)=\sum_{h\in H}z^h$. Identifying each depth row with its exponent
    support, and writing $X-X=\{x-x':x,x'\in X\}$,
    \[
    (D_A-D_A)\cap(D_B-D_B)=\{0\},\qquad
    D_A\cap D_B=\{0\},\qquad
    \sum_{h\in H}h\equiv3\pmod9.
    \]
    For sorted raw rows $a_0<\cdots<a_8$ and
    $b_0<\cdots<b_8$,
    \[
    a_7+a_8\ge36,\quad b_7+b_8\ge36,\quad
    a_8,b_8\ge19,\quad a_8+b_8\le87.
    \]
    The formal family further imposes its residue convolutions modulo
    $4,8,11$ and its mod-$4$ Gaussian norm filter. **Scope:** This entire
    family is conditional. It neither enumerates the coefficient systems nor
    proves a rooted-tree lift, feasibility, exclusion of weight $66$ or
    $67$, exclusion of order $18$, or universal nonexistence.

66. **G024 — Three correction witnesses.** Explicit formal counterexamples
    establish that: (i) the same-color tail bound above the second odd weight
    cannot be reversed into a positive lower bound on nonphysical even ranks
    below it; (ii) individually admissible signed cut masses and the signed
    first moment do not imply a jointly realizable vertex-parity flow; and
    (iii) the multiset of pairs $(c_e,w_e)$ does not determine the multicut
    intersection matrix or even the outcome of a particular sound multicut
    lower-bound test: two placements with the same histogram have different
    matrices, one violating and the other attaining that test. **Scope:**
    These witnesses refute only the named invalid inference patterns; they do
    not establish or refute overall rank-allocation feasibility and do not
    refute the correct forward theorems.

## Global boundary

These 66 restrictions do not construct a Leech tree of order at least $18$,
do not exclude order $18$, and do not prove universal nonexistence for all
larger orders. The original existence-or-nonexistence problem remains open in
this development. Historical computational families `C001`–`C022`, held
families `H1`–`H3`, and the open target `P0` are not included in the list and
receive no theorem credit here. No claim of worldwide novelty, priority, or
current literature status is made.

The authoritative family and scope ledger is
[`VALIDATED_FORMAL_CLAIM_MATRIX.tsv`](VALIDATED_FORMAL_CLAIM_MATRIX.tsv); the
reader-facing source catalogue is [`THEOREM_INDEX.md`](THEOREM_INDEX.md), and
the exact nonclaims are recorded in [`SCOPE.md`](SCOPE.md). If this exposition
and a Lean declaration differ, the declaration and all of its hypotheses
control.
