# Baseline spectrum, parity, cut, and order-18 proofs

This note collects the mathematical derivations behind the baseline T1-T12
and C17 theorem families. The [validated claim matrix](../results/VALIDATED_FORMAL_CLAIM_MATRIX.tsv)
and current Lean declarations control the exact published scope.
## 2. Forced physical edges and forced-MEX exposure

### Proposition 2.1 [T1] (physical weights 1 and 2)

**Lean:** LEAN-CHECKED-EXACT as
`LeechTrees.Foundation.T1_physical_weights_one_two`.

For $n\ge3$, all physical edge weights are distinct and lie in
$[1,N]$. Exactly one physical edge has weight 1, and exactly one has weight
2.

**Proof.** Every physical edge is itself the path between its endpoints, so
its weight is a pair distance. Global distance injectivity makes physical
edge weights distinct. A positive integral path of total 1 has one edge. A
multi-edge path of total 2 would contain two weight-1 edges, contradicting
distinctness. The exact spectrum supplies existence and uniqueness. $\square$

### Theorem 2.2 [T2] (forced-MEX and persistent merge block)

**Lean:** LEAN-CHECKED-EXACT as
`LeechTrees.Foundation.PosIntTree.T2_forced_mex_initial_segment` and
`LeechTrees.Foundation.T2_forced_mex_merge_persistence`.

Fix a physical edge $e$. Expose precisely the physical edges whose weights
are smaller than $w_e$. They form an acyclic prefix forest. Let $D_e$ be the
set of pair distances internal to its components and let
$\operatorname{mex}_+(D_e)$ be its least missing positive integer. Then

\[
 \operatorname{mex}_+(D_e)=w_e,
\]

and $e$ has least weight among the unexposed physical edges.

If the two prefix components incident to the endpoints of $e$ are joined at
those actual ports, the indexed merge block is

\[
 d_A(u,a)+w_e+d_B(b,v).
\]

It equals the corresponding actual tree distance, is injective, lies in
$[1,N]$, is disjoint from $D_e$, persists in every later internal-distance
set, and the prefix internal-distance sets grow monotonically.

**Proof.** Let $q$ be the least unexposed physical weight. If $q$ were below
the positive mex, its endpoint distance would already lie in $D_e$, causing
a duplicate. If the mex were below $q$, every edge on the final path
realizing that target would already be exposed, placing the mex in $D_e$.
Thus $q$ is the mex. Unique paths give the displayed actual-port formula;
global distance injectivity and the exact target interval give injectivity,
range, disjointness, and persistence. $\square$

This is an exact semantics for prefixes of a fixed hypothetical tree, not a
classification of all possible trees.

## 3. Parity, cuts, and direct sums

### Theorem 3.1 [T3] (Taylor parity condition)

**Lean:** LEAN-CHECKED-EXACT as
`LeechTrees.Foundation.t3_taylor_order_condition` and
`LeechTrees.Foundation.T3_taylor_parity_order18`.

Color a vertex by the parity of its distance from a fixed root. A path has
odd weight exactly when its endpoints have different colors. If the two
classes have sizes $a$ and $n-a$, then

\[
 a(n-a)=\left\lceil\frac{N}{2}\right\rceil.
\]

The discriminant gives the necessary order form

\[
 n=t^2\quad\text{or}\quad n=t^2+2
\]

for some $t\in\mathbb N$. At order 18 the two class sizes are 7 and 11.

### Theorem 3.2 [T4] (cut checksum)

**Lean:** LEAN-CHECKED-EXACT as
`LeechTrees.Foundation.T4_cut_checksum`; the order-18 specialization is
`LeechTrees.Foundation.T4_order18_checksum`.

If deleting physical edge $e$ gives component orders $s_e$ and $n-s_e$,
then

\[
 \sum_{e\in E}s_e(n-s_e)w_e
 =\sum_{j=1}^{N}j
 =\frac{N(N+1)}2.
\]

At order 18 the sum is 11,781.

**Proof.** Exactly $s_e(n-s_e)$ unordered vertex-pair paths cross $e$.
Exchange the finite sum over pairs with the sum over physical edges on each
canonical path, then use the exact Leech spectrum. $\square$

### Theorem 3.3 [T5] (indexed every-edge direct sum)

**Lean:** LEAN-CHECKED-EXACT as
`LeechTrees.Foundation.T5_every_edge_direct_sum`.

Delete an edge $ab$ of weight $w$. Root its two sides at $a,b$, with depth
functions $\alpha,\beta$. Every cross distance is

\[
 w+\alpha(u)+\beta(v).
\]

Both depth functions and the indexed cross-sum map are injective. Moreover,

\[
 \alpha(u)-\alpha(u')=\beta(v')-\beta(v)
 \quad\Longrightarrow\quad u=u',\ v=v',
\]

and this ordered-difference condition is equivalent to cross-sum
injectivity. If the cut has $c=s(n-s)$ cross pairs, then

\[
 w\le N-c+1.
\]

The criterion is indexed: it cannot be replaced by an unindexed comparison
of marginal depth sets or full internal spectra.

## 4. Two analytic order-18 restrictions

Here $n=18$ and $N=153$.

### Theorem 4.1 [T6] (largest physical edge at least 19)

**Lean:** LEAN-CHECKED-EXACT as
`LeechTrees.QHop.order18_largestPhysicalEdge_ge_19`.

Let $Q=\max_e w_e$. Then $Q\ge19$.

**Proof.** For $1\le k\le9$, at most $18-2k+1$ edges have both deletion
sides of order at least $k$. The resulting decreasing cut-coefficient vector
is componentwise bounded by the path vector

\[
81,80,80,77,77,72,72,65,65,56,56,45,45,32,32,17,17.
\]

If $Q\le18$, the 17 distinct positive edge weights contain 1 and 2. Their
componentwise-largest decreasing vector is obtained by omitting 3:

\[
18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,2,1.
\]

Rearrangement and the cut majorization give
$\sum_e s_e(18-s_e)w_e\le11372$, contradicting the checksum 11,781.
$\square$

### Theorem 4.2 [T7] (hop diameter at most 14)

**Lean:** LEAN-CHECKED-EXACT as
`LeechTrees.QHop.order18_simplePath_length_le_14`.

Every simple path has at most 14 physical edges.

**Proof.** Suppose a 15-edge path has positive consecutive weights
$g_1,\ldots,g_{15}$ and total $L\le153$. Its 42 interval sums spanning one,
two, or three consecutive gaps are distances of distinct endpoint pairs, so
they are 42 distinct positive integers. Their sum $S$ therefore satisfies
$S\ge1+\cdots+42=903$. Their exact gap multiplicities are

\[
(3,5,6,6,6,6,6,6,6,6,6,6,6,5,3),
\]

so $S=6L-B$, where
$B=3g_1+g_2+g_{14}+3g_{15}$. The four boundary weights are distinct and
positive; assigning the two smallest possible values to the coefficient-3
positions gives $B\ge16$. Hence $S\le6\cdot153-16=902$, a contradiction.
Every longer path contains a 15-edge subpath. $\square$

## 5. Parity-resolved cuts, moments, and tails

Fix a root and put

\[
 \sigma(v)=(-1)^{d(r,v)},\qquad x(S)=\sum_{v\in S}\sigma(v).
\]

For a nonempty physical-edge set $F$, let $C_F$ count indexed unordered
pair paths containing every edge of $F$, and let $K_F$ be the sum of
$\sigma(u)\sigma(v)$ over those pairs.

### Theorem 5.1 [T8a] (path support and outer-component factorization)

**Lean:** LEAN-CHECKED-EXACT as
`LeechTrees.ParityTail.GraphAdapterV1.T8_actual_noncollinear_zero` and
`LeechTrees.ParityTail.T8ExactBundle.T8_actual_collinear_extreme_outer_components`;
the actual parity-count identities are bundled in
`LeechTrees.ParityTail.T8ExactBundle.T8_actual_parity_counts_CF_KF`.

If no canonical pair path contains $F$, then $C_F=K_F=0$. Otherwise the
tree supplies a witness path, selected near and far edges of $F$, their
nested-away-cut characterization, and an explicit sign-preserving
equivalence between the indexed support and the product of the resulting
outer vertex sets $L_F,R_F$. In particular,

\[
 C_F=|L_F||R_F|,\qquad K_F=x(L_F)x(R_F).
\]

Consequently the even- and odd-distance support counts are

\[
 C_F^+=\frac{C_F+K_F}{2},\qquad
 C_F^-=\frac{C_F-K_F}{2}.
\]

The parity-count theorem proves the equivalent integral identities
$C_F^++C_F^-=C_F$, $2C_F^+=C_F+K_F$, and
$2C_F^-=C_F-K_F$. The final collinear theorem constructs the extreme
components and support equivalence from the actual tree; no certificate is
an unproved public premise.

### Theorem 5.2 [T8b] (parity-resolved moments)

**Lean:** LEAN-CHECKED-EXACT as
`LeechTrees.ParityTail.GraphAdapterV1.T8_actual_parity_resolved_path_moments`
and
`LeechTrees.ParityTail.GraphAdapterV1.T8_actual_order18_parity_moment_system`,
with the coefficient bridge and noncollinear triple-zero statement in
`LeechTrees.ParityTail.T8ExactBundle.T8_actual_moment_coefficients_are_parity_counts`
and
`LeechTrees.ParityTail.T8ExactBundle.T8_actual_noncollinear_tripleCoefficient_zero`.

Let $P_k^\pm$ be the $k$-th power sums of the even and odd targets. For
$k=1,2,3$, expanding actual path sums gives

\[
P_1^p=\sum_e C_e^p w_e,
\]

\[
P_2^p=\sum_e C_e^p w_e^2
 +2\sum_{e<f}C_{\{e,f\}}^p w_ew_f,
\]

and

\[
\begin{aligned}
P_3^p={}&\sum_e C_e^p w_e^3\\
&+3\sum_{e<f}C_{\{e,f\}}^p(w_e^2w_f+w_ew_f^2)\\
&+6\sum_{e<f<g}C_{\{e,f,g\}}^pw_ew_fw_g.
\end{aligned}
\]

Here each raw singleton, pair, or triple coefficient is exactly the indexed
parity support count for the corresponding one-, two-, or three-edge
Finset. In particular, the triple coefficient is zero whenever no canonical
pair path contains the three displayed edges.

At order 18 the exact target moments are:

| degree | even targets | odd targets |
|---:|---:|---:|
| 0 | 76 | 77 |
| 1 | 5,852 | 5,929 |
| 2 | 596,904 | 608,685 |
| 3 | 68,491,808 | 70,300,153 |

For an edge side of order $s$ and signed mass $x$, with total signed mass
normalized to 4, put $c=s(18-s)$ and $\kappa=x(4-x)$. Then

\[
 2h^+=c+\kappa,\qquad 2h^-=c-\kappa,
\]

with $x\equiv s\pmod2$, $|x|\le s$, and $|4-x|\le18-s$. The exact side
count and feasibility conjunction is compiled as
`LeechTrees.ParityTail.T8ExactBundle.T8_actual_order18_edge_counts_and_feasibility`;
its joined-count component is also named
`T8_actual_order18_edge_joined_counts`.

### Theorem 5.3 [T9] (parity-tail spacing and saturation)

**Lean:** LEAN-CHECKED-EXACT as
`LeechTrees.ParityTail.GraphAdapterV1.T9_actual_edge_parity_tail` and
`LeechTrees.ParityTail.GraphAdapterV1.T9_actual_edge_saturation`.

Across an edge of weight $w$, fix parity $p$, and suppose its cross block has
$h>0$ values of that parity. Let $L_p(w)$ be the least integer at least $w$
of parity $p$. For $k=1,2,3$,

\[
 \sum_{j=0}^{h-1}(L_p(w)+2j)^k
 \le \sum_{\text{cross pairs of parity }p}d(u,v)^k
 \le P_k^p.
\]

In particular, $L_p(w)+2(h-1)\le N$. If $h$ equals the cardinality of the
entire target parity tail at least $w$, containment plus equal cardinality
forces equality of value sets with that tail. This fixes values, not indexed
ownership or a rooted-tree realization.

### Corollary 5.4 [T10] (conditional weight-67 side mass)

**Lean:** LEAN-CHECKED-EXACT as
`LeechTrees.ParityTail.GraphAdapterV1.T10_actual_weight67_nine_nine`.

For an actual order-18 physical edge of weight 67 with a $9|9$ deletion cut,
the root-normalized left signed mass satisfies

\[
x\in\{-1,1,3,5\}.
\]

The theorem assumes that such an edge exists; it neither supplies nor
excludes one and does not say the edge is largest.

### Corollary 5.5 [T10b] (conditional weight-68 residual)

**Lean:** LEAN-CHECKED-EXACT as
`LeechTrees.ParityTail.GraphAdapterV1.T10b_actual_weight68_nine_nine`.

For an actual order-18 physical edge of weight 68 with a $9|9$ cut and left
signed mass $-1$ or 5, its odd cross-distance value block is the complete odd
tail $69,71,\ldots,153$. Subtracting 68 gives the residual value set

\[
\{1,3,\ldots,85\},
\]

with residual moments 1,849; 105,995; and 6,835,753 in degrees 1, 2, and 3,
and cross-block moments 4,773; 556,291; and 67,628,637. This is again only
an implication under the displayed edge and side-mass hypotheses.

## 6. Odd physical-edge restrictions

Let $r$ be the number of physical edges with odd weight.

### Theorem 6.1 [T11] (one odd physical edge is impossible)

**Lean:** LEAN-CHECKED-EXACT as
`LeechTrees.OddEdges.T11Adapter.T11_no_exactly_one_odd`.

For every $n\ge18$, a classical Leech tree cannot have exactly one odd
physical edge.

**Proof route.** Assuming exactly one odd edge, its actual deletion cut and
the two rooted depth systems produce an indexed one-odd decomposition. The
construction proves, rather than assumes, the same-side even-depth
realizations, cross-rank equivalence, collision exclusions, target
cardinalities, parity transport, and signed-imbalance identities. The
one-odd decomposition obstruction then contradicts $n\ge18$. The public
theorem takes only the actual tree, exact spectrum, and order bound; no
decomposition or negative conclusion is passed in as a premise. $\square$

### Theorem 6.2 [T12] (two odd physical edges force even odd-target count)

**Lean:** LEAN-CHECKED-EXACT as
`LeechTrees.OddEdges.T12Adapter.t12_two_odd_physical_edges`.

For $n\ge5$, if a classical Leech tree has exactly two odd physical edges,
then the number of odd targets in $1,\ldots,\binom n2$ is even.

**Proof route.** Fix the two actual odd edges and replace each physical
weight $w$ by $\lceil w/2\rceil$. For every actual pair path,

\[
2d_{\lceil/2\rceil}(u,v)
=d_T(u,v)+I_e(u,v)+I_f(u,v).
\]

The two deletion cuts are laminar, so one of the three non-root four-cell
regions is empty. Ordered-pair character sums, exact transport through the
Leech spectrum, Taylor's coupled order alternatives, and the available
empty-cell coordinates construct the required Gaussian data. The
number-theoretic obstruction then forces the odd-target count to be even.
Every character, laminar, order, and coordinate field is derived from the
actual graph hypotheses. $\square$

At order 18 there are 77 odd targets, so T12 excludes $r=2$.

### Auxiliary corollary [C17] (not all 17 physical edges are odd)

**Lean:** LEAN-CHECKED-EXACT as
`LeechTrees.OddEdges.GraphAdapter.order18_oddPhysicalEdgeCount_ne_seventeen`.

An order-18 tree has 17 physical edges, while T1 supplies an even edge of
weight 2. Hence $r\ne17$. C17 is recorded separately because it is a human
input to VC2 but is not one of the 13 legacy `V` rows.
