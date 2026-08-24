# Large-order common-port obstruction for exactly two odd edges

## Theorem and scope

No Leech tree of any parity-admissible order `n>=38` has exactly two odd
physical edges whose endpoints in the middle even-edge component coincide.
Together with the arbitrary-port odd-`O` theorem at order 36 and parity
inadmissibility between the admissible orders, no common-port example exists
at any order `n>=36`.

This theorem covers every positive integral weighting, every component order
split, every internal topology, every bridge shift, and arbitrary interleaving
of the two odd cross classes.  It is an infinite-order extension of the prior
order-36/order-38 factor calculations and uses no enumeration.

## 1. Exact factor and Gaussian constraints

Delete the two odd edges and call the quotient components `X--Y--Z`.  Orient
the weight-1 bridge first and write the other bridge as `2q+1`.  Divide all
internal even weights by two.  Because the two middle ports coincide, the
rooted middle half-depth polynomial `B` is the same for both bridges.  If
`A,C` are the outer rooted half-depth polynomials, the odd half-ranks give

```text
B(t)D(t)=1+t+...+t^(O-1),
D(t)=A(t)+t^q C(t),                                         (1)
```

where `O=ceil(n(n-1)/4)`.  All coefficients are nonnegative and the right
side has coefficient one.  Thus both factors are zero-one polynomials and
their supports form a unique direct sum of `[0,O-1]`.

Parity admissibility gives an integer `s` with `n=s^2` or `n=s^2+2`, and
the two raw parity-class orders are `(n-s)/2,(n+s)/2`.  At orders with even
`O`, evaluating the full odd/even half-rank identities at `-1` gives, with
`m=|Y|` and middle rooted imbalance `eta=B(-1)`,

```text
eta(xi+chi)=0,
(xi-chi)^2+eta^2=s^2.                                       (2)
```

Here `xi=A(-1)` and `chi=(-1)^q C(-1)`.  At orders with odd `O`, the
arbitrary-port theorem already gives impossibility for `n>=5`.  Therefore
only (2) need be considered below.

## 2. Initial-block lemma

Let finite nonnegative integer sets `P,Q`, both containing zero, satisfy
`P+Q=[0,L-1]` uniquely.  If `1 in P` and `r` is the least positive member
of `Q`, then coefficient comparison in

```text
P(t)Q(t)=1+t+...+t^(L-1)
```

gives

```text
P={0,1,...,r-1}+rP',
Q=rQ',
P'+Q'=[0,L/r-1] uniquely.                                  (3)
```

Indeed, below degree `r` only the constant term of `Q` contributes, so the
entire initial block lies in `P`.  The term of `Q` at degree `r` excludes the
corresponding term of `P` and forces the rest of that block empty.  Repeating
coefficient comparison block by block says that every later contribution of
`P` is a whole length-`r` block and every contribution of `Q` begins at a
multiple of `r`, yielding (3) by induction.

Apply this lemma to the support sets `mathcal B=supp(B)` and
`mathcal D=supp(D)` from (1).

## 3. Rank 1 in the middle factor is impossible when `m>4`

Suppose `1 in mathcal B`, and let `r` be the least positive member of
`mathcal D`.  Formula (3) makes `mathcal B` a union of full length-`r`
blocks starting at multiples of `r`.

If `r>=4`, `Y` has vertices at rooted depths 1,2,3.  The LCA of the depth-1
and depth-2 vertices is the root or the depth-1 vertex, making their distance
3 or 1.  Both values are already root distances, a collision.

If `r=3` and `m>3`, a later block `H,H+1,H+2` occurs.  The vertices at
depths 1 and `H+1` have distance `H+2` or `H`, both existing root distances.

If `r=2`, write

```text
mathcal B={2b,2b+1 : b in mathcal B'}.                       (4)
```

Let `o,u` be the depth-0 and depth-1 vertices.  For positive `b`, let
`e_b,f_b` have depths `2b,2b+1`.  Avoiding the root distance `2b+1` forces
`e_b` below `u`; avoiding the root distance `2b` forces `f_b` outside the
subtree of `u`.  For two distinct positive `b,c`, the distinct pairs
`{e_b,f_c}` and `{e_c,f_b}` then both have LCA `o` and distance
`2b+2c+1`.  Hence `mathcal B'` has at most one positive member and `m<=4`.

Thus `1 in mathcal B` is impossible whenever `m>4`.

## 4. Rank 1 in the other factor is impossible for `n>=38`

Suppose `1 in mathcal D`, and let `r` be the least positive member of
`mathcal B`.  Formula (3), with the roles interchanged, says that every
middle rooted depth is divisible by `r`.  Rooting the middle tree shows every
middle edge weight, and hence every internal middle half-distance, is also
divisible by `r`.

If `r` is even, every middle depth is even, so `eta=m`.  Equation (2) gives
`m<=s`.  But for every admissible `n>=38`,

```text
m >= (n-s)/2 > s,                                           (5)
```

a contradiction.

If `r` is odd, then `r>=3`.  The `C(m,2)` distinct internal middle
half-distances must all be multiples of `r` in `[1,E]`, where
`E=floor(n(n-1)/4)`.  Therefore

```text
C(m,2)<=floor(E/r)<=E/3.                                    (6)
```

The reverse strict inequality holds at every admissible `n>=38`.  Put
`m_0=(n-s)/2`.  Since `m>=m_0` and `E<=n(n-1)/4`, it suffices to prove

```text
6m_0(m_0-1)>n(n-1).                                         (7)
```

For `n=s^2` the difference between the two sides is

```text
s(s^2-1)(s-6)/2>0                                           (8)
```

for the relevant `s>=7`.  For `n=s^2+2`, twice that difference is

```text
s^4-6s^3+3s^2-6s-4
 =s^3(s-6)+3s^2-6s-4>0                                     (9)
```

for `s>=6`.  Thus (7) contradicts (6).

Since exactly one of the two direct-sum factors in (1) contains rank 1,
Sections 3--4 prove the theorem.

## 5. Sharp small example and remaining branch

The verified order-six witness

```text
[1,2,1], [1,3,2], [1,5,5], [4,5,4], [5,6,8]
```

has exactly two odd edges and a common middle port.  Its half-depth data are

```text
A={0}, B={0,1}, C={0,2,4}, q=2,
B + (A disjoint-union (q+C))={0,1}+{0,2,4,6}=[0,7].
```

The even half-ranks are respectively

```text
internal B: {1},  internal C: {2,4,6},  outer cross: {3,5,7}.
```

Thus the small alternating-radix pattern is real and explains why a theorem
must use the large middle-class size.

For an exactly-two-odd tree at any order `n>=36`, the middle ports are forced
to be distinct. The low-support theorem further forces `1<=q<=6`. The exact
remaining obstacle is that with
distinct ports the odd identity is a sum of two products

```text
A B_p + t^q B_r C=1+t+...+t^(O-1),
```

not the single interval factor (1); the initial-block recursion does not
survive without a new two-root decomposition theorem.
