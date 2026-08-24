# Two-odd-edge common-port factor obstruction at orders 36 and 38

## Strategic scope

- **Potential result.** Either expose an interleaved mixed-radix construction
  generalizing the order-six Leech tree, or eliminate that construction at
  orders 36 and 38.
- **Scope and coverage.** The result below covers every positive integral
  weighting, every component order split, and every internal topology when
  there are exactly two odd physical edges and their endpoints in the middle
  even-edge component coincide.  It does not assume that the two odd pair
  classes are consecutive; arbitrary interleaving is included.
- **Why this task.** It is a topology-free construction theorem at two larger
  admissible orders, rather than another fixed-topology or fixed-weight
  exclusion.  Its factor equation is reusable at other admissible orders.
- **Stop condition.** A rooted-realizable interval factor would have become a
  concrete completion target.  Since all factors are obstructed, this route
  should stop; any successor must use distinct middle ports or at least three
  odd edges.

## 1. General factor lemma

Let a positive weighted tree have exactly two odd physical edges.  Deleting
them leaves three even-edge components in a path, denoted `X-Y-Z`.  Suppose
the two odd edges meet the middle component `Y` at the same vertex `r`.  Put

```text
x=|X|,  m=|Y|,  z=|Z|.
```

The parity classes have orders `m` and `x+z`.  Root `X` and `Z` at their odd
edge endpoints and root `Y` at `r`.  Since all internal edges are even, divide
their rooted depths by two and call the resulting distinct nonnegative integer
sets `D_X,D_Y,D_Z`.  Write the two odd edge weights as

```text
2h_X-1 and 2h_Z-1,     h_X,h_Z >= 1.
```

For an odd distance `d`, call `(d+1)/2` its odd rank.  The odd ranks of the
`X-Y` and `Y-Z` pairs are respectively

```text
h_X + D_X + D_Y,       h_Z + D_Y + D_Z.                 (1)
```

If the full tree is Leech, these two multisets are disjoint and together are
all ranks `1,...,O`, where `O` is the number of odd integers in the target
interval.  For `P_D(t)=sum_{d in D}t^d`, (1) is therefore the coefficient
identity

```text
P_Y(t) [ t^(h_X-1) P_X(t) + t^(h_Z-1) P_Z(t) ]
       = 1+t+...+t^(O-1).                               (2)
```

All coefficients are nonnegative, while the right side has coefficient one.
Consequently the bracket in (2) is itself a zero-one polynomial with exactly
`x+z` terms, and (2) is a unique interval direct-sum factorization of
cardinalities `m` and `x+z`.  Notice that no consecutive-block assumption was
made: (2) includes every possible interleaving of the two odd pair classes.

This proves the following reusable lemma.

> **Common-port factor lemma.** In an exactly-two-odd-edge Leech tree whose
> odd edges share their endpoint in the middle even-edge component, that
> component's half-depth set is the factor of its parity-class cardinality in
> a unique direct-sum factorization of the full odd-rank interval.

## 2. Rooted-LCA obstruction

For a sorted rooted depth set `D`, define

```text
L(D)={a+b-2c : a,b in D, a<b, c in D, c<=a}.            (3)
```

In any positive rooted tree with depth set `D`, the LCA of vertices at depths
`a<=b` is an actual vertex of depth `c in D` with `c<=a`.  Thus every internal
distance belongs to `L(D)`.  If the component has `m` vertices inside a Leech
tree, its `C(m,2)` internal distances are distinct, so necessarily

```text
|L(D)| >= C(m,2).                                       (4)
```

This is a necessary condition only, which is exactly how it is used below.

## 3. Order 36

Here `N=630`, there are `O=315` odd ranks, and the parity classes have orders
15 and 21.  The forced-least-uncovered recursion in
`two_odd_common_port_factor_obstruction.py` enumerates every factorization

```text
A+B=[0,314],   |A|=15, |B|=21.                          (5)
```

At the least uncovered value `k`, a representation by two positive terms
would use membership decisions below `k` that are already fixed.  Hence `k`
itself must next be inserted in one factor, paired with zero in the other.
Trying both legal insertions proves completeness by induction.  The recursion
visits 15,875 nodes and returns exactly 14 tilings; an independent mixed-radix
generation gives the identical list.

Across all 14 tilings, the largest value of `|L(A)|` is 70, below
`C(15,2)=105`, and the largest value of `|L(B)|` is 106, below
`C(21,2)=210`.  Thus neither parity class can be the common-port middle
component.  By the factor lemma, every scoped order-36 tree is impossible.

## 4. Order 38

Here `N=703`, there are `O=352` odd ranks, and the parity classes have orders
16 and 22.  The same complete recursion visits 20,639 nodes and returns
exactly 25 tilings

```text
A+B=[0,351],   |A|=16, |B|=22,                          (6)
```

again identical to the independent mixed-radix list.  Every 22-term factor
has `|L(B)|<=96<C(22,2)=231`, so a 22-vertex middle component is impossible.

For the 16-term factors, 23 of the 25 tilings have
`|L(A)|<C(16,2)=120`.  The two remaining literal sets are also impossible.

First let

```text
D_1={0,1,2,3,44,45,46,47,176,177,178,179,220,221,222,223}.
```

For the vertices at depths 1 and 2, their LCA has depth 0 or 1.  Their
distance is consequently 3 or 1, respectively.  Both values already occur as
root distances, so either choice creates a collision.

Second let

```text
D_2={0,1,4,5,88,89,92,93,176,177,180,181,264,265,268,269}.
```

Call the unique depth-one vertex `u`.  For a vertex of depth `d`, its LCA with
`u` is the root or `u`, giving distance `d+1` or `d-1`.  Avoiding an existing
root distance forces the vertices of depths

```text
4,88,92,176,180,264,268
```

inside the subtree of `u`, and forces those of depths

```text
5,89,93,177,181,265,269
```

outside it.  The depth-4 and depth-89 vertices therefore have the root as
their LCA, so their distance is `4+89=93`, already the root distance of the
depth-93 vertex.  This is a collision.

Thus neither parity class can be the middle component at order 38 either.

## 5. Conclusion and limitation

> **Theorem.** No order-36 or order-38 Leech tree has exactly two odd physical
> edges whose endpoints in the middle even-edge component are the same
> vertex.

The result allows arbitrary positive weights, arbitrary component orders and
topologies, and arbitrary interleaving of the two odd-distance classes.  It
does not cover distinct attachment ports in the middle component, three or
more odd physical edges, or other orders.  Those are the correct construction
directions to retain.
