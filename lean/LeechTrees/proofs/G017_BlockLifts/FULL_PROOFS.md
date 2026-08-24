# Block-lift identities and obstructions at order 18

## Scope

This note begins with the order-six fixture

```text
12:1, 13:2, 16:5, 46:4, 56:8.
```

It does not claim an order-18 candidate or an exclusion of arbitrary order-18
trees.

## 1. Two preserved scaled order-six blocks already collide

Let a connected six-vertex block be a uniform positive-integral scale `s` of
the fixture.  Its internal distance set is

```text
s*{1,2,...,15}.
```

Inside an order-18 Leech tree all these distances are at most 153, hence
`s<=floor(153/15)=10`.  If two vertex-disjoint blocks have scales `s,t` and
`g=gcd(s,t)`, then

```text
lcm(s,t)=(t/g)s=(s/g)t.
```

Both multipliers are in `1,...,10`, hence in `1,...,15`.  The least common
multiple is therefore an internal distance of both blocks, realized by two
different vertex pairs.  This contradicts distance uniqueness.

Consequently an order-18 construction cannot contain even two preserved
uniformly scaled order-six witnesses, independently of quotient topology,
ports, bridge weights, or the rest of the tree.  Any `6+6+6` route derived
from the fixture must nonuniformly reweight at least two of the three blocks.

The same argument gives a reusable sufficient collision criterion.  For a
target of order `n`, put `N=C(n,2)`, and for a scaled Leech block of order `m`
put `M=C(m,2)`.  Two such disjoint blocks certainly collide whenever

```text
floor(N/M) <= M.
```

Indeed both scales are at most `floor(N/M)`, so their least-common-multiple
multipliers are at most `M`.

## 2. Exact parity constraint for three six-vertex blocks

Partition a weighted tree into three connected blocks of order six whose
quotient is a path.  In block `i`, choose a reference vertex and color by
parity of internal weighted distance.  Let

```text
delta_i = (# local color 0) - (# local color 1),
d_i = |delta_i| in {0,2,4,6}.
```

Each bridge either preserves or reverses the local coloring at its two ports.
Because the quotient is a tree, the resulting relative block signs have no
cycle constraint.  If bridge parities are free, every sign triple is
attainable.  Thus parity feasibility is exactly

```text
there exist tau_i in {+1,-1} with
|tau_1*d_1 + tau_2*d_2 + tau_3*d_3| = 4.                 (P)
```

The right side is forced by the order-18 parity split `7|11`.  Exhausting the
twenty nondecreasing triples from `{0,2,4,6}` gives exactly seven feasible
magnitude profiles:

```text
(0,0,4), (0,2,2), (0,2,6), (2,2,4),
(2,4,6), (4,4,4), (4,6,6).                              (T)
```

Equivalently, in terms of the two local color-class sizes, magnitude
`0,2,4,6` means respectively `3|3`, `2|4`, `1|5`, `0|6`.

For a uniformly scaled order-six fixture, `d_i=2` when the scale is odd and
`d_i=6` when the scale is even.  No triple drawn only from `{2,6}` occurs in
`(T)`.  This independently rules out gluing three scaled copies, even before
using the internal-spectrum collision above.

For fixed ports and bridge parities, `(P)` cannot be replaced by the
existential sign test. If `epsilon_i(p)` is the local parity sign at port `p`
and a bridge `ij` has weight `q_ij`, propagate the actual signs by

```text
tau_j = tau_i * epsilon_i(p_ij) * epsilon_j(p_ji)
              * (-1)^q_ij,
```

then require `|sum_i tau_i delta_i|=4`.  The table `(T)` is the exact
topology-free prefilter when bridge parities remain free.

## 3. Nonuniform deformation equations

The literal scaled-block route is closed, but a nonuniform deformation is not.
For outer/middle/outer six-vertex blocks with internal distance matrices
`D_1,D_2,D_3`, ports `alpha`; `beta,gamma`; `eta`, and bridge weights `q_1,q_2`,
the complete 153 distances are the following exact classes:

```text
D_i[x,y]                                                     (within i),
D_1[x,alpha] + q_1 + D_2[beta,y]                            (1--2),
D_2[x,gamma] + q_2 + D_3[eta,y]                             (2--3),
D_1[x,alpha] + q_1 + D_2[beta,gamma] + q_2 + D_3[eta,y]     (1--3).
```

For fixed unweighted block topologies and ports, give every internal edge and
both bridges a positive integer variable, constrain all 153 forms to
`[1,153]`, and impose one `AllDifferent`.  Since the number of forms equals
the interval size, this is necessary and sufficient for the spectrum.  Before
solving, apply `(T)` to the three induced internal parity splits.  Also reject
any model retaining two uniform fixture blocks by Section 1.

For a bridge incident with a surviving scaled fixture block at port `p`, its
root-depth set is `s A_p`.  If `B` is the actual jointly indexed root-depth set
on the other side, cross-distance injectivity requires

```text
s(A_p-A_p) intersect (B-B) = {0}.
```

Every fixture port has the positive depth differences

```text
{1,2,3,4,5,7,8}
```

in common.  Hence the safe port-independent prefilter is

```text
(B-B)^+ intersect s*{1,2,3,4,5,7,8} = empty.
```

This difference test must use one actual rooted component row.  Independently
selected marginal depth sets are not a sound replacement.

## 4. Constructive conclusion

Changing only quotient shape, ports, bridge weights, or uniform scale cannot
turn copies of the known order-six witness into an order-18 witness.  A viable
order-six-inspired route must change at least two blocks internally and must
land in one of the seven parity profiles `(T)`.  The exact 153-form model above
is a construction template, not a candidate or a completeness claim.
