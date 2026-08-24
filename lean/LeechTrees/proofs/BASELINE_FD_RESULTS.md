# Baseline edge, quotient, path, and extension proofs

This note collects the human-readable derivations behind F1, F4,
F9a-F9e, and D3a-D5b. The [validated claim matrix](../results/VALIDATED_FORMAL_CLAIM_MATRIX.tsv)
and current Lean declarations control the exact published scope.
## 2. The first two physical edges

### Theorem F1 (safe first-edge split)

Assume (T) is a Leech tree and (n\ge4).  Let (e_1,e_2) be the unique
physical edges of weights 1 and 2 supplied by T1.  Then precisely the
following safe dichotomy is proved:

1. If (e_1) and (e_2) share an endpoint, no physical edge has weight 3,
   and exactly one physical edge has weight 4.
2. If the endpoint sets of (e_1) and (e_2) are disjoint, exactly one
   physical edge has weight 3.

Lean declaration:

```text
LeechTrees.Foundation.firstEdge_physical_split
```

The proof classifies the positive, pairwise-distinct physical weights on the
unique paths realizing target distances 3 and 4.  In the adjacent case, a
weight-3 physical edge would duplicate the path (e_1e_2), so the target-4
path must be one edge.  In the disjoint case, the target-3 path cannot be the
two-edge path (e_1e_2), so it must be a physical edge.  The hypothesis
(n\ge4) is sharp for this combined statement; no stronger eight-row first-
edge dossier is claimed.

## 3. The exact hole hierarchy at every edge

Fix a physical edge (e=ab) of weight (w).  Deleting (e) gives actual
left and right vertex sets (L_e,R_e), rooted at (a,b).  Put

\[
 \alpha(u)=d_T(a,u),\qquad \beta(v)=d_T(b,v).
\]

Every cross distance is (w+\alpha(u)+\beta(v)).  Define the offset interval

\[
 I_e=\{0,1,\ldots,N-w\},
\]

the indexed cross-offset value set

\[
 S_e=\{\alpha(u)+\beta(v):(u,v)\in L_e\times R_e\},
\]

and the exact hole set (H_e=I_e\setminus S_e).  The formal development first
proves that the indexed map ((u,v)\mapsto\alpha(u)+\beta(v)) is injective;
thus later cardinalities do not silently discard pair multiplicity.

### Theorem F4 (every-edge hole identity)

For every physical edge of a Leech tree:

\[
 H_e\subseteq\{1,\ldots,N-w\},
 \qquad
 |H_e|=(N-w+1)-|L_e||R_e|.
\]

After translation by (w), the holes are exactly the disjoint union of the
two internal spectra at least (w):

\[
 w+H_e=\mathcal I^{\ge w}_{L_e}\;\dot\cup\;
          \mathcal I^{\ge w}_{R_e}.
\]

For each (k=0,1,2,3), the ordinary moment identity is

\[
 \sum_{h\in H_e}h^k+
 \sum_{(u,v)\in L_e\times R_e}
      (\alpha(u)+\beta(v))^k
 =\sum_{t=0}^{N-w}t^k,
\]

with the Cartesian term expanded in the formal theorem into the appropriate
binomial products of the indexed rooted moments.  The alternating hierarchy
is proved simultaneously:

\[
 \sum_{h\in H_e}(-1)^h h^k+
 \sum_{(u,v)\in L_e\times R_e}
      (-1)^{\alpha(u)+\beta(v)}
      (\alpha(u)+\beta(v))^k
 =\sum_{t=0}^{N-w}(-1)^t t^k
\]

for the same four degrees, again with the exact binomial factorization into
left and right signed moments.

Lean declaration:

```text
LeechTrees.Foundation.everyEdge_hole_identity
```

This is a necessary identity for each actual edge.  It is not a converse
asserting that compatible Finsets or moments can be realized by rooted tree
components.

## 4. Odd-edge contraction and exact half-rank polynomials

Delete every physical edge whose weight is odd.  The remaining even-edge
forest has connected components (C).  For vertices (x,y) in one such
component, define

\[
 \rho_C(x,y)=\frac{d_T(x,y)}2.
\]

The formal development proves that the division is exact and that $\rho$
has the required path-additivity properties.

Each deleted odd physical edge joins two different even components.  Map the
physical odd edge, with its original index retained, to the corresponding
unordered component pair.  The map is injective: two different physical odd
edges cannot collapse to one simple quotient edge.  Its image defines a
quotient graph (Q_T).

### Theorem F9.1 (the quotient is an actual tree)

The graph (Q_T) is connected and acyclic, hence a tree.  Moreover, the
indexed odd physical edges are in bijection with its edge set.

Lean declarations include:

```text
LeechTrees.OddQuotient.quotientEdgePair_injective
LeechTrees.OddQuotient.oddBridgeQuotientEdgeEquiv
LeechTrees.OddQuotient.quotientGraph_isTree
```

The acyclicity proof shows that every quotient edge is a bridge by lifting a
hypothetical avoiding quotient walk into the deletion cut of its actual
physical edge.  No component contraction theorem that could hide parallel
physical bridges is assumed.

### Theorem F9.2 (canonical route formula with all actual ports)

Let a quotient path from component (C_0) to (C_k) cross actual odd
bridges (b_1,\ldots,b_k).  Write

\[
 w(b_i)=2\lambda_i+1.
\]

Orient each bridge along the quotient path and retain its actual exit and
entry vertices.  For endpoints (x\in C_0), (y\in C_k), the recursively
defined route cost is

\[
 R(x,y)=
 \rho(x,\operatorname{exit}b_1)+\lambda_1+
 \sum_{i=1}^{k-1}
 \bigl(\rho(\operatorname{entry}b_i,
              \operatorname{exit}b_{i+1})+\lambda_{i+1}\bigr)
 +\rho(\operatorname{entry}b_k,y).
\]

Then

\[
 d_T(x,y)=2R(x,y)+k.
\]

Equivalently, with

\[
 H(x,y)=R(x,y)+\left\lfloor\frac{k}{2}\right\rfloor,
\]

one has the half-rank/parity formula

\[
 d_T(x,y)=2H(x,y)+(k\bmod2).
\]

Lean declaration:

```text
LeechTrees.OddQuotient.dist_eq_two_mul_canonicalRouteHalfRank_add_mod
```

The recursive lemmas `routeCost_cons_cons` and `routeShift_cons` expose the
separation between each preceding bridge's actual entry port and the next
bridge's actual exit port.  Thus the formula does not replace a multi-port
component by one marginal depth distribution.

### Theorem F9.3 (indexed pair partition)

There is an actual equivalence

\[
 \binom{V}{2}
 \simeq
 \left(\coprod_C\binom{C}{2}\right)
 \;\sqcup\;
 \left(\coprod_{\{C,D\},\,C\ne D} C\times D\right).
\]

Lean declaration:

```text
LeechTrees.OddQuotient.vertexPairIndexEquiv
```

The second coproduct ranges over every distinct component pair, not merely
adjacent quotient components.  The equivalence is indexed and therefore
preserves multiplicity.

For a finite indexed rank function (r:A\to\mathbb N), define

\[
 \mathcal R_r(X)=\sum_{a\in A}X^{r(a)}.
\]

Lean proves

\[
 [X^h]\mathcal R_r=|\{a\in A:r(a)=h\}|,
\]

as well as exact reindexing, disjoint-sum, shift, and Cartesian-product
identities.  For each distinct component pair, its cross polynomial is a
monomial route shift times the two rooted endpoint polynomials.  Its
coefficient is the exact cardinality of the corresponding indexed Cartesian
fibre.

### Theorem F9.4 (coefficientwise odd/even quotient identities)

Let $O=\lfloor (N+1)/2\rfloor=\lceil N/2\rceil$ and
$E=\lfloor N/2\rfloor$.  Summing cross blocks whose
quotient paths have odd length gives

\[
 [X^h]\,\mathcal Q_{\rm odd}(X)=
 \begin{cases}1,&0\le h<O,\\0,&\text{otherwise}.
 \end{cases}
\]

Internal component pairs together with cross blocks of positive even
quotient length give

\[
 [X^h]\,\mathcal Q_{\rm even}(X)=
 \begin{cases}1,&1\le h\le E,\\0,&\text{otherwise}.
 \end{cases}
\]

Lean declaration:

```text
LeechTrees.OddQuotient.F9_coefficientwise_odd_quotient
```

These equations are proved first as unconditional decompositions of actual
indexed pairs and only then reindexed using `IsLeech`.  They are not support
equalities and contain no construction or realization converse.

### Theorem F9.5 (forward two-port coordinates)

Let (p,q,u) be three named vertices in the same even component and put

\[
 a=\rho(p,u),\qquad b=\rho(q,u),\qquad \delta=\rho(p,q).
\]

There are natural numbers (c,h), with (0\le c\le\delta), such that

\[
 a=h+c,\qquad b=h+(\delta-c).
\]

Consequently,

\[
 b+2c=a+\delta,\qquad \delta+2h=a+b,
\]

and, over the integers,

\[
 2c=a-b+\delta,\qquad 2h=a+b-\delta.
\]

Lean declaration:

```text
LeechTrees.OddQuotient.exists_twoPortCoord
```

The stronger witness `exists_twoPortGate` retains the actual median vertex.
The ports may coincide.  No reverse implication, port injectivity, or raw-
coordinate realization theorem is claimed.

## 5. Path and extension obstructions

### Theorem D3 (the physical spectrum is not the full initial interval)

If (T) is a Leech tree and (n\ge5), then

\[
 \{w(e):e\in E\}\ne\{1,2,\ldots,n-1\}.
\]

Lean declaration:

```text
LeechTrees.Extension.physicalWeightSet_ne_initial_of_five_le
```

Under the contrary hypothesis, the maximum-distance path must contain every
physical edge and hence gives a spanning weighted path with distinct positive
edge weights (1,\ldots,n-1).  Its adjacent one-edge and two-edge subpaths
produce too many distinct positive target values for the sharp sum bound.
The contradiction is first formalized for a normalized weighted-path
presentation and then connected to the actual tree by a spanning-path
adapter.

### Theorem D4a.0 (exact one-leaf tail characterization)

For a positive base order $m\ge1$, a new leaf of weight $q$ attached at a
named old vertex $v$ supplies exactly the new target interval

\[
 \left\{\binom m2+1,\ldots,\binom m2+m\right\}
\]

if and only if

\[
 q=\binom m2+1
 \quad\text{and}\quad
 \{d_T(v,u):u\in V(T)\}=\{0,1,\ldots,m-1\}.
\]

Lean declaration:

```text
LeechTrees.Extension.completesOneLeafTail_iff
```

For an exact literal one-leaf graph operation between two Leech trees,
`LiteralOneLeafAttachment.completesOneLeafTail` derives this certificate from
the operation and the two indexed spectra; it is not an assumed premise.
The standalone obstruction
`LeechTrees.LeafRange.rootedDepthSet_ne_range_of_four_le` proves that the
displayed rooted-depth interval cannot occur in a Leech tree of order at
least four.

### Theorem D4a.1 (literal one-leaf obstruction)

An exact unchanged attachment of one new leaf to a Leech tree of order
(m\ge4) cannot produce another Leech tree.  The operation record specifies
the old induced tree, the unique new vertex, the unique new incident edge,
and preservation of every old physical weight.  The proof derives—not
assumes—the old metric, the exact complement of the old indexed pair image,
and the new-leaf distance tail.  That tail would force the rooted depths in
the old tree to be (0,1,\ldots,m-1), contradicting the weight-1/weight-2
collision.

Lean declaration:

```text
LeechTrees.OperationAdapters.LiteralOneLeafAttachment.no_literalOneLeafAttachment_of_four_le
```

### Theorem D4a.2 (exact formalized small-order boundary)

For base order $m\ge2$, an actual unchanged literal one-leaf step between
Leech trees exists if and only if $m=2$ or $m=3$.  The source constructs the
weighted trees with edge weights $[1]$, $[1,2]$, and $[1,2,4]$, proves their
indexed spectra, and constructs the literal 2-to-3 and 3-to-4 operation
records.  Under the convention admitting the vacuous order-one spectrum, a
separate theorem includes the 1-to-2 step:

```text
LeechTrees.SmallLeafBoundary.hasSuccessfulLiteralOneLeafStep_iff_of_two_le
LeechTrees.SmallLeafBoundary.hasSuccessfulLiteralOneLeafStep_iff_of_one_le
```

These statements have corresponding exact Lean declarations and were included
in the strict release build and axiom audit.  The small witnesses do not answer
the existence question in the open range.

### Theorem D4b (literal weight-preserving subdivision)

Replace one physical edge by two positive physical edges through one new
vertex, preserving every other edge and weight.  If both the old and new
trees satisfied `IsLeech`, the operation would preserve all old indexed
distances while creating a fresh pair whose distance is a proper positive
part of the split weight.  That value already occurs in the old exact target
interval, a contradiction.

Lean declaration:

```text
LeechTrees.OperationAdapters.LiteralWeightPreservingSubdivision.no_literalWeightPreservingSubdivision
```

The formal adapter explicitly lifts every old canonical path through the two
new segments and proves its support, path property, and weight equality.

### Theorem D4c (literal unscaled bridge)

Take two Leech trees of orders (a,b\ge2), preserve both internal graphs and
all internal physical weights, and join named ports by exactly one new bridge.
The result cannot be a Leech tree.  Both component metrics embed unchanged,
so their positive target intervals overlap and give duplicate distances.

Lean declaration:

```text
LeechTrees.OperationAdapters.LiteralUnscaledBridge.no_literalUnscaledBridge_of_nontrivial
```

The order-one component case is the one-leaf operation of D4a, not an omitted
case of this nontrivial bridge statement.

### Theorem D5 (unchanged-subtree range obstruction)

Suppose a Leech tree of order $m\ge1$ embeds as an induced connected subtree
of a Leech tree of order $m+k$, with all old indexed distances unchanged and
$k\ge2$.  Then necessarily

\[
 \binom m2+3\le mk+\binom k2.
\]

Lean declaration:

```text
LeechTrees.LeafRange.UnchangedSubtreeData.unchangedSubtree_range_necessary
```

The larger tree has exactly (k) new physical edges.  Each new edge has
weight exceeding the old target (\binom m2); two distinct new edges lie on
one actual pair path, so the larger target must accommodate their sum.  This
gives the displayed inequality.  Its contrapositive is exposed as
`no_unchangedSubtreeExtension_of_range`.  In particular, every base order
$m\ge5$ rules out an unchanged extension by exactly two new vertices:

```text
LeechTrees.LeafRange.UnchangedSubtreeData.no_unchangedSubtreeExtension_two_new_of_five_le
```

For an order-18 base, unchanged-subtree extensions by
$(k=2,3,\ldots,7)$ are impossible:

```text
LeechTrees.LeafRange.UnchangedSubtreeData.no_order18_unchangedSubtreeExtension_two_to_seven
```

## 6. T8 branches, normalized sign, and parity-tail wording

For every nonempty selected edge Finset $F$ and every sign function
$\sigma:V\to\mathbb Z$, T8 has two exhaustive structural branches.  If some
indexed vertex-pair path contains all of $F$, then
`T8_actual_collinear_outer_factorization_closed` constructs outer vertex sets
$L,R$ with

\[
 \operatorname{actualPathCoefficient}(T,F)=|L|\,|R|,
 \qquad
 \operatorname{actualSignedPathCoefficient}(T,\sigma,F)
   =\operatorname{mass}_{\sigma}(L)\operatorname{mass}_{\sigma}(R).
\]

The stronger `T8_actual_collinear_extreme_outer_components` retains the
witness path, extreme selected edges, nested-cut characterization, indexed
endpoint-pair equivalence, and both factorizations.  In the complementary
case—no indexed vertex-pair path contains every edge of $F$—
`T8_actual_noncollinear_zero` proves that both displayed coefficients are
zero.  This general noncollinear result is stronger than the separate
singleton-pair triple-coefficient zero corollary.

The order-18 cut identities use a globally normalized parity character.  For
an actual root $r$, first define

\[
 \sigma_r(v)=(-1)^{d_T(r,v)}.
\]

The two parity classes have sizes 7 and 11.  Choose
$\varepsilon_r\in\{+1,-1\}$ so that

\[
 \widetilde\sigma_r(v)=\varepsilon_r\sigma_r(v)
\]

has eleven positive and seven negative values.  Hence

\[
 \sum_{v\in V}\widetilde\sigma_r(v)=4.
\]

For a vertex set $S$, the normalized side mass used in the order-18 T8
equations and in T10/T10b is

\[
 x_r(S)=\sum_{v\in S}\widetilde\sigma_r(v).
\]

The common multiplier cancels in pair products, so
$\widetilde\sigma_r(u)\widetilde\sigma_r(v)=(-1)^{d_T(u,v)}$.
These are the exact conventions implemented by
`normalizationMultiplier18`, `normalizedParitySign18`, and
`leftImbalance18`; the raw and normalized side masses must not be conflated.

The specialization `T8_actual_order18_parity_moment_system` then identifies
the actual physical-edge expansions in degrees one, two, and three with the
six integer values

\[
 5852,\ 5929;\qquad
 596904,\ 608685;\qquad
 68491808,\ 70300153,
\]

listed by even and odd target parity, respectively.  This is the direct
graph-level moment system; `T8_order18_target_counts_and_moments` separately
packages the degree-zero counts and the same target moment table for paper
use.

For the literal T9 inequality, let $T$ be a Leech tree, fix an actual
physical edge $e$ of $T$ and $p\in\{0,1\}$, and let

\[
 \operatorname{Tail}_p(w)=
 \{t\in\{1,\ldots,N\}:t\ge w,\ t\equiv p\pmod2\},
\]

and let $L_p(w)$ be the least integer at least $w$ with parity $p$.  If the
actual cross-parity value block $B_{e,p}$ has cardinality $h>0$, then for
$k=1,2,3$,

\[
 \sum_{j=0}^{h-1}(L_p(w_e)+2j)^k
 \;\le\;
 \sum_{t\in B_{e,p}}t^k
 \;\le\;
 \sum_{t\in\operatorname{Tail}_p(w_e)}t^k
 \;\le\;P_k^p,
\]

where $P_k^p$ is the full degree-$k$ moment of target ranks of parity $p$.
The first two inequalities, including the stronger middle upper bound by the
parity tail, are the literal content of `T9_actual_edge_parity_tail`; the
final inequality is its immediate full-target corollary.  If
$|B_{e,p}|=|\operatorname{Tail}_p(w_e)|$, then
`T9_actual_edge_saturation` proves equality of these two value Finsets.  It
does not identify indexed ownership or construct a tree.

## 7. Alignment corollaries for the main paper

Three paper-facing wrappers prevent omissions or weaker prose substitutions.

1. `T3_actual_root_parity_equation` states the literal natural-number equation
   \[
   a(n-a)=\left\lfloor\frac{N+1}{2}\right\rfloor
          =\left\lceil\frac N2\right\rceil,
   \]
   where $a$ is the parity class size determined by an actual root.  The
   floor is Lean's `Nat.div`, not rational division.
2. `T8_order18_target_counts_and_moments` records the degree-zero counts
   (76,77) and the degree-1/2/3 even/odd target moments
   
   \[
   5852,\ 5929;\qquad
   596904,\ 608685;\qquad
   68491808,\ 70300153.
   \]
3. `T12_order18_no_exactly_two_odd_physical_edges` derives the explicit
   order-18 corollary that the number of odd physical edges is not 2, because
   the odd target count is 77 whereas T12 makes it even under exactly two odd
   physical edges.

The last corollary says nothing about odd physical-edge counts 3 through 15.
