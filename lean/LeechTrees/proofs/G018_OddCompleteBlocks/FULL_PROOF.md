# Odd-square complete-block obstruction

## Status and scope

This note proves a global impossibility theorem for the complete-block
architecture at every odd parameter `q>1`.  In particular it covers every
`q>=5`, every quotient-tree topology, every balanced root-sign assignment,
every quotient-edge residue and every choice of positive integer lifts.

It is an exclusion of this architecture, not a Leech-tree witness and not an
exclusion of other tree topologies.

## 1. Architecture and exact pair polynomial

Let `q>1` be odd.  Take `q` rooted stars `B_i`, each of order `q`, and join
their roots by an arbitrary tree `Q` on the `q` roots.  Write the pendant
weights in block `i` as

```
p_(i,a) = 2a (mod 2q),       1 <= a <= q-1.             (1)
```

Thus each block uses each nonzero even residue modulo `2q` exactly once.
The quotient weights are unrestricted in this proof.  Put

```
A_i(X) = 1 + sum_(a=1)^(q-1) X^p_(i,a),
delta_ij = weighted distance in Q between roots i and j.
```

If `F(X)` is the enumerator of all unordered pair distances in the resulting
tree, then the following identity holds in `Z[X]`:

```
F(X)
 = sum_i (A_i(X)^2 - A_i(X^2))/2
   + sum_(i<j) X^delta_ij A_i(X) A_j(X).                (2)
```

Indeed, the first term enumerates the unordered pairs of distinct vertices
inside one rooted star.  A vertex in block `i` has root offset either zero or
one of the `p_(i,a)`, so a pair in two different blocks has distance equal to
the two offsets plus `delta_ij`, giving the second term.  Thus (2) accounts
for every unordered pair exactly once.  This also proves that no assumption
about the shape of `Q` is hidden in the formula.

Let

```
D = X d/dX
```

be the Euler derivative.  If the tree were Leech, with

```
n=q^2,       N=binom(q^2,2)=q^2(q^2-1)/2,
```

then

```
F(X)=X+X^2+...+X^N.                                    (3)
```

## 2. The first Fourier moment

Fix a primitive `q`-th root of unity `omega` and put `z=omega^t`, where
`1<=t<=q-1`.  Reduction of (1) modulo `q` gives every nonzero residue once,
so

```
A_i(z) = 1+z+...+z^(q-1) = 0.                          (4)
```

Apply `D` to (2) and evaluate at `z`.  Every derivative of a cross-block
term still contains `A_i(z)` or `A_j(z)`, so all cross-block terms vanish.
For an internal term,

```
D[(A_i(X)^2-A_i(X^2))/2] at X=z
  = -sum_a p_(i,a) z^(2p_(i,a)).                       (5)
```

Consequently (3) would imply

```
sum_(i,a) p_(i,a) z^(2p_(i,a)) = -N z/(z-1).           (6)
```

For completeness, `q` divides `N`; grouping `1,...,N` into `N/q` blocks of
length `q` gives

```
sum_(d=1)^N d z^d
 = (N/q) sum_(r=1)^q r z^r
 = N z/(z-1),                                          (7)
```

where the final identity is the derivative of
`1+z+...+z^(q-1)=0`.  Equations (5)--(7) prove (6) without an approximation
or a numerical root-of-unity calculation.

For `r in {0,...,q-1}`, define the integer

```
C_r = sum { p_(i,a) : 2p_(i,a) = r (mod q) }.
```

Multiplication by four permutes the residues modulo odd `q`.  Hence `C_0=0`
and every `C_r` with `r!=0` is a sum of exactly `q` pendant weights.  Equation
(6), for all `t=1,...,q-1`, is the nontrivial discrete Fourier transform of
the vector `(C_0,...,C_(q-1))`.

Put `H=N/q`.  The integer vector

```
B_0=0,              B_r=H(q-r),  1<=r<=q-1            (8)
```

has exactly the same nontrivial Fourier transform, because for every
nontrivial `q`-th root `z`,

```
sum_(r=1)^(q-1) (q-r)z^r = -qz/(z-1).                 (9)
```

The difference `C-B` has all its nontrivial Fourier coefficients zero, so it
is a constant vector.  Its zeroth entry is zero, and therefore the constant
is zero.  We have proved the exact, topology-independent identities

```
C_r = (N/q)(q-r),        1<=r<=q-1.                   (10)
```

This is a lifted first-moment condition.  The usual uniform-residue identity
is only the zeroth-order evaluation of (2); differentiating before evaluating
retains the integer magnitudes and produces the much stronger (10).

## 3. Universal contradiction

Because `q` is odd, there is a unique `a in {1,...,q-1}` satisfying

```
4a = -1 (mod q).                                       (11)
```

For the `q` pendant edges of type `a`, (1) and (11) give
`2p_(i,a)=q-1 (mod q)`.  Equation (10) therefore forces

```
sum_i p_(i,a) = C_(q-1) = N/q = q(q^2-1)/2.           (12)
```

Every edge weight is the distance between its endpoints.  In a Leech tree
all pair distances are distinct, so these `q` pendant weights are distinct.
They are positive integers all congruent to `2a` modulo `2q`.  After sorting,
their least possible values are

```
2a, 2a+2q, ..., 2a+2q(q-1).
```

Their sum is therefore at least

```
2aq + q^2(q-1).                                        (13)
```

But (13) exceeds the forced value in (12) by

```
2aq + q^2(q-1) - q(q^2-1)/2
  = q((q-1)^2+4a)/2
  > 0.                                                  (14)
```

This contradiction proves:

> **Theorem.** For every odd integer `q>1`, no weighted tree obtained from
> `q` rooted `K_(1,q-1)` blocks with the nonzero even pendant residues modulo
> `2q`, joined by any tree on their roots, can have pair-distance multiset
> `1,...,binom(q^2,2)`.

Balanced root signs and quotient-edge parity/residue restrictions only make
the family smaller, so the theorem also excludes the complete-block modular
family in its full intended form.

## 4. Checksum and forced-mex consequences (not used in the contradiction)

These record the other uniform layers requested for this architecture.

Let `P` be the sum of all pendant weights.  If a quotient edge separates `s`
whole blocks from `q-s` blocks, its cut coefficient is `q^2 s(q-s)`, while a
pendant edge has cut coefficient `q^2-1`.  The Wiener checksum is therefore

```
(q^2-1)P + q^2 sum_(e in Q) s_e(q-s_e)w_e
  = N(N+1)/2.                                           (15)
```

In particular `P=0 (mod q^2)`.  If the Leech assumption is retained long
enough to use (10), it gives the sharper, exact value

```
P = sum_(r=1)^(q-1) C_r = N(q-1)/2.                   (16)
```

For the smallest distances, weight `1` must be a quotient edge because all
pendants are even.  Distance `2` is an edge: a positive path of at least two
edges cannot sum to `2` without using weight `1` twice, and edge weights are
distinct.  If the weight-`1` and weight-`2` edges are adjacent, their path is
the unique distance `3`; otherwise weight `3` must itself be a quotient
edge.  These are exact forced-mex facts, but (14) makes further prefix
branching unnecessary.

## 5. Proof dependencies

* The proof uses exact polynomial identities and integer inequalities only.
* It uses actual edge weights, not hop counts or arbitrary complete-graph
  labels.
* Distinctness is invoked only where justified: two distinct tree edges are
  two distinct endpoint pairs, hence their weights must differ in a Leech
  tree.
* No primality of `q` is assumed; oddness is used precisely to make four
  invertible modulo `q` and to ensure the prescribed residues cover all
  nonzero classes modulo `q`.
* No conclusion about another quotient topology or architecture follows.
