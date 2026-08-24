# Sharp exactly-two-odd support-factor bounds

## Theorem and scope

There are three conclusions.

1. The `q<=10` proof does not use order 38, distinct middle ports, component
   orders, the imbalance alternatives, or the even cross term.  It applies to
   every Leech tree of any order having exactly two odd physical edges,
   including the common-port case.
2. Under the same any-order hypotheses, `q=7` is impossible.
3. If the two ports in the quotient-middle component are distinct and the odd
   half-rank target contains ranks through 14, then `q<=6`.  This applies in
   particular to every such tree of order at least 9, and therefore to orders
   25 and 38.  The cases `q=8,9,10` each have a unique low rooted skeleton up
   to swapping the two factors of the unit-bridge product, and each skeleton
   is killed by the linked second product.

This is a scoped structural theorem, not an order-38 witness or a
nonexistence theorem.

## Broad algebraic setup

Let a Leech tree have exactly two odd physical edges.  Deleting those edges
leaves three positive even-edge components whose quotient is a path.  The
unique distance 1 is a physical edge: a positive path of total weight 1 can
only be one edge.  Orient the quotient so this edge is the first bridge.  The
other odd edge has weight `2q+1`.  It cannot also have weight 1, because edge
weights themselves are pair distances and Leech distances are injective;
hence `q>=1`.

Divide internal even weights by two.  Let `A,B` be the rooted depth
polynomials of the two components incident with the unit bridge.  Let `D,C`
be the rooted depth polynomials at the two ends of the other bridge.  The
middle component occurs once as `B` and once, possibly at a different root,
as `D`.  If `O` is the number of odd integers in the full distance target,
partitioning pairs that cross exactly one odd bridge gives

```text
A(t)B(t) + t^q D(t)C(t) = 1+t+...+t^(O-1).                 (A)
```

This derivation permits common ports.  For order 38, `O=352`.

Every polynomial has nonnegative integral coefficients and constant
coefficient exactly one.  Strict positivity of the halved internal edges
means that the root is the unique vertex at depth zero.  Consequently the
second product in (A) has genuine minimum exponent `q`, with coefficient one:
the root-root term is its only term there.  Thus `q` is not merely a lower
bound or a guessed “second minimum.”  There can be no shifted-product support
below it.

Because the right side of (A) has coefficient one and there is no
cancellation:

- each summand has only coefficients zero or one;
- their supports are disjoint;
- `AB` has coefficient one at every rank below `q` and coefficient zero at
  `q`;
- the coefficient of `t^k` in `AB` counts representations `k=a+b`, so every
  represented sum is unique; and
- each factor itself has coefficient at most one, because the other factor's
  root contributes a copy of every factor coefficient.

This answers the coefficient-multiplicity and extra-low-support objections.
Every support element below `q` is explicitly part of the direct-sum case
split; a support element cannot be hidden by a multiplicity or cancellation.

The Leech property also makes all internal halved distances in the first two
components mutually distinct, both within one component and across the two.
This follows directly because equality of two halved internal distances is
equality of the corresponding raw even distances.  It is also the
coefficient-one consequence of the direct-sum equation.  Every positive
rooted depth is one of these internal distances (the root-to-vertex pair).

## LCA and factor-swap argument

Rank 1 has exactly one representation, and both factors contain zero.  Hence
exactly one of `A,B` contains 1.  Swapping the factor names preserves the
direct sum and all within/across-component internal-injectivity hypotheses.
We call the factor containing 1 `P` and the other `Q`.  This is a naming swap,
not a swap of the two odd bridges or their ports.

After a factor swap, the component represented by `P` can be the middle
component. The argument therefore refers to that component by its factor role,
not by a fixed positional name.

There are no hidden LCA or Steiner vertices.  In the actual combinatorial
component, the LCA of two vertices is an actual vertex.  Its halved depth is
an integer in the rooted support.  If its descendants have depths at most 10,
the LCA has smaller depth and therefore is among the already classified low
support elements.  A vertex of depth above 10 cannot be their ancestor.
Because the factor coefficients are at most one, there is at most one actual
vertex at each such depth.  Finally, an attachment at the interior of a
physical edge is not a graph vertex; any genuine branching or subdivision
point is already an actual support vertex.

## Complete proof of `q<=10`

Assume `q>=11`, so ranks 0 through 10 must all occur uniquely in `P+Q`.
Normalize `1 in P`, `1 notin Q`.

1. **Rank 2.**  Suppose `2 in P`.  The depth-1/depth-2 LCA has depth 0 or 1,
   so their distance is 3 or 1.  Distance 1 would repeat the rooted depth 1,
   hence their distance is 3.  The other factor cannot contain 2, since that
   would duplicate rank 2.  Rank 3 therefore has to be a factor depth, which
   repeats the just-forced internal distance 3.  Thus `2 in Q`.  Rank 3 is
   `1+2`, so neither factor contains 3.
2. **Rank 4.**  It must be a factor depth.  If `4 in Q`, the LCA of Q's
   depth-2 and depth-4 vertices has depth 0 or 2; depth 1 is absent.  LCA depth
   2 gives repeated internal distance 2, so LCA depth 0 is forced and their
   distance is 6.  Current sums are exactly 0 through 5.  Rank 6 must then be
   a factor depth and repeats internal distance 6.  Therefore `4 in P`.
3. **Rank 5.**  Current sums are `0,1,2,3,4,6`.  Rank 5 must be a factor
   depth.  Putting it in Q duplicates rank 6 as `4+2=1+5`; hence `5 in P`.
4. **Forced P topology.**  Let `u,v,w` have P-depths 1,4,5.  The `u,v`
   distance is 5 or 3; 5 repeats the rooted depth 5, so `u` is the ancestor of
   `v` and the distance is 3.  The `u,w` distance is 6 or 4; 4 repeats rooted
   depth 4, so their LCA is the root and the distance is 6.  Since `v` lies
   below `u`, the `v,w` LCA is also the root and their distance is 9.  Thus

   ```text
   P contains {0,1,4,5}, Q contains {0,2},
   P+Q contains exactly ranks 0,...,7 below 8.              (B)
   ```

5. **Rank 8.**  It must enter exactly one factor.  If `8 in P`, rank 10 is
   already `8+2`.  Rank 9 is missing.  Putting 9 in Q gives a second rank 10,
   `1+9`; putting 9 in P repeats the forced internal distance 9.  If instead
   `8 in Q`, ranks 8 and 9 occur and rank 10 is missing.  Putting 10 in P
   duplicates rank 12 as `10+2=4+8`.  Putting 10 in Q also fails: the
   depth-2/depth-8 LCA has depth 0 or 2.  The latter gives internal distance 6,
   already used in P; the former gives internal distance 10, which the new
   rooted depth 10 repeats.

Both cases contradict `q>=11`; hence `q<=10`.  Notice that duplicate sums 12
are legitimately used even though only ranks through 10 are forced to be
present: every coefficient of the entire product must be at most one.

## Sharp low cases and physical skeletons

For `q=7`, steps 1--4 still apply because ranks through 6 are present.  But
(B) already contains rank 7 as `5+2`, contradicting the required omission of
`q`.  Thus `q!=7`, even with common ports.

For `q=8,9,10`, the omission of rank `q` fixes the following low supports and
parent maps, up to swapping the first-product factors.  Depths and parent
differences in this table are halved; the listed physical edge weights are
twice those differences.

For q=9, rank 8 must enter a factor.  Putting it in Q would represent the
omitted rank 9 as `1+8`, so it enters P.  Its LCA with `u` cannot be the root,
which would repeat the already-forced internal distance 9; hence it is below
`u`.  It cannot be below the depth-4 vertex, which would repeat distance 4,
and no omitted intermediate depth is available.  Its parent is therefore
`u`.  For q=10, putting depth 8 in P would represent the omitted rank 10 as
`8+2`, so depth 8 enters Q.  Its LCA with Q-depth 2 cannot be that vertex,
which would repeat internal distance 6; it is the root.  These arguments give
the parent maps in the table, not just the support sets.

| q | P low support and forced physical edges | Q low support and forced physical edges | odd bridges |
|---|---|---|---|
| 8 | `{0,1,4,5}`: `0->1` weight 2, `1->4` weight 6, `0->5` weight 10 | `{0,2}`: `0->2` weight 4 | 1 and 17 |
| 9 | `{0,1,4,5,8}`: the q=8 P skeleton plus `1->8` weight 14 | `{0,2}`: `0->2` weight 4 | 1 and 19 |
| 10 | `{0,1,4,5}`: the q=8 P skeleton | `{0,2,8}`: root branches of weights 4 and 16 | 1 and 21 |

These are actual physical edges, not compressed paths.  Any intermediate
vertex would have an omitted integral depth below `q`.  The table does not
say which factor is the quotient-middle component, nor does it locate the
other bridge port.

### Distinct-port elimination of `q=10`

For q=10, `P+Q` occupies `0,...,9,12,13` and omits 11.  Rank 11 could enter
the first product only as a factor depth 11.  Adding it to P duplicates rank
13 (`11+2=5+8`); adding it to Q duplicates rank 12
(`1+11=4+8`).  Therefore the shifted product must supply unshifted sum 1.

If P is outer, its internal distance 1 forbids depth 1 in either component of
the shifted product.  If P is middle, a depth 1 in the third component is
again forbidden, while depth 1 after rerooting P must reuse P's unique
distance-1 pair.  Distinct ports therefore force the other port to be `u`,
the depth-1 neighbor of the first port.  Rerooting at `u` puts the forced
depth-4 vertex at depth 3.  The shifted product then occupies rank `10+3=13`,
already occupied by `5+8`.  Thus q=10 is impossible with distinct ports.

### Distinct-port elimination of `q=8`

The initial internal ranks across P and Q are `1,2,3,4,5,6,9`, and the first
product occupies 0 through 7.  It cannot occupy rank 9: a factor depth 9
repeats internal distance 9.  If P is outer, shifted unrank 1 is also
impossible because outer P already owns internal distance 1.

Hence P must be middle.  Shifted unrank 1 forces the other port to be `u`.
Rerooted P has depths `0,1,3,6`.  Shifted unrank 2 is impossible, since every
new rooted distance 2 repeats Q's internal distance 2.  Rank 10 must therefore
be in the first product.  A Q-depth 10 would also occupy rank 11, colliding
with shifted depth 3, so P-depth 10 is forced.  Internal injectivity forces
that vertex to be a new root branch; the alternatives below `u,v,w` give the
already-used distances 9,6,5.  Its new internal distances are
`10,11,14,15`, and the first product also occupies rank 12.

Shifted unrank 5 is impossible.  The only already-existing rerooted P depths
at most 5 are 0,1,3; every missing part 2,4,5 is an internal distance already
owned by a different pair, and every positive depth in the third component
would also repeat one.  Rank 13 must be first-product.  A Q-depth 13 has
distance 11 or 15 from Q's depth-2 vertex, both already used.  A P-depth 13
cannot attach below any existing low vertex: parents `p,u,v,w,y_10` force,
respectively, a repeated distance `14,15,9,14,3`.  There is no omitted-depth
intermediate vertex.  Thus q=8 is impossible with distinct ports.

### Distinct-port elimination of `q=9`

Here the initial internal ranks are `1,...,10,13` and the first product
occupies `0,...,8,10`.

First suppose P is outer and Q is middle.  At rank 11 there are exactly two
possibilities.

- If rank 11 is first-product, Q-depth 11 is impossible because its distance
  from Q-depth 2 is 9 or 13, both used in P.  P-depth 11 is forced as a root
  branch and creates internal ranks `11,12,15,16,19`.  Rank 12 can then be
  neither P-depth 12 (it repeats internal 12), Q-depth 12 (it duplicates first
  rank 13), nor shifted unrank 3 (outer P owns internal 3).
- The branch omitted in an initial proposed proof is real: rerooting middle Q
  at its depth-2 vertex supplies shifted unrank 2 and hence rank 11.  Rank 12
  must then be first-product.  If it is P-depth 12, the parent is forced to be
  P-depth 1; rank 13 has no source because shifted unrank 4 is forbidden and
  either factor depth 13 repeats internal 13.  If it is Q-depth 12, it is a
  root branch, Q gains internal distance 14, and first ranks 12 and 13 occur.
  Shifted unrank 5 is forbidden, while either factor depth 14 repeats Q's
  internal 14.  Thus rank 14 has no source.

Now suppose P is middle and Q is outer.  Shifted unrank 2 is impossible, so
rank 11 forces P-depth 11, again as a root branch.  Rank 12 cannot be first-
product and therefore forces shifted unrank 3.  The unique middle distance-3
pair is the edge between old depths 1 and 4.  The second port cannot be the
depth-1 vertex because that would also supply forbidden shifted unrank 1; it
is therefore the depth-4 vertex.  Rerooting there gives the original root
depth 4, so the shifted product occupies rank `9+4=13`.  The first product
already occupies rank 13 as `11+2`, a contradiction.

The q=8 proof uses target ranks only through 13, q=9 only through 14, and
q=10 only through 13.  Hence an odd half-rank target through 14 is a uniform
sufficient hypothesis.  Order 25 has odd half-ranks `0,...,149`; order 38 has
`0,...,351`.  No order-38-specific step is hidden in these closures.

## Domain and limitation

The `q<=10` proof applies more broadly than order 38. The distinct-port
order-38 family has the sharper domain

```text
q in {1,2,3,4,5,6}.
```

For order 38, the raw odd edge range gives q=1,...,351.  Equation (A) plus the
fact that the middle component has more than one vertex already excludes
q=351, because a positive `D` depth would shift beyond rank 351.  Thus the
pre-theorem mathematically viable crude domain is at most 350 values.  The
new six-value domain is a factor `350/6 > 58` reduction (or `351/6=58.5`
relative to the raw edge range), stronger than the advertised 35-fold cut.

The theorem does not justify crediting any `q` value as an order-38 exclusion
beyond the exactly-two-odd, distinct-port family.
