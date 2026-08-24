# Four-odd quotient shapes and the Gaussian identity

This note gives the mathematical derivation behind the formal `G022`
endpoints. It proves a necessary quotient-shape and scalar identity for an
actual order-18 Leech tree with exactly four odd physical edges. It does not
classify all compatible component metrics or ports, prove feasibility, or
construct a Leech tree.

## 1. Five even components

Assume an order-18 Leech tree has exactly four odd physical edges. Delete
those four edges. A tree loses one connected component per deleted edge, so
the result has five nonempty connected components. Contracting each component
to one vertex gives a five-vertex quotient tree `Q`.

Up to isomorphism, a five-vertex tree is exactly one of:

```text
P5,  the fork with degree sequence (3,2,1,1,1),  or K1,4.
```

Every edge retained inside a component has even weight. Hence all vertices in
one component have the same distance parity from a fixed root, while crossing
an odd deleted edge changes parity. The quotient bipartition therefore lifts
to the two vertex-parity classes of the original tree.

If their orders are `a` and `18-a`, then the number of odd pair distances is
`a(18-a)`. Exactly 77 integers in `1,...,153` are odd, so

```text
a(18-a) = 77.
```

Thus the unordered parity-class orders are `{7,11}`. If `m_v` is the order of
component `v`, then every `m_v` is positive, their total is 18, and their sums
over the two quotient colors are 7 and 11.

## 2. Gauged component imbalances

Choose a reference vertex in component `v` and halve all internal even
lengths. Define the component imbalance

```text
delta_v = sum_{x in C_v} (-1)^(halved distance from the reference to x).
```

Then

```text
|delta_v| <= m_v,          delta_v = m_v (mod 2).
```

Each odd quotient edge carries a sign determined by its odd bridge residue
and the two reference-to-port parities. Because `Q` is a tree, those edge
signs can be written as products `sigma_u sigma_v`, uniquely up to changing
every `sigma` simultaneously. Put

```text
x_v = sigma_v delta_v.
```

Changing component references changes `delta`, the incident edge signs, and
`sigma` together; the gauged vector `x` changes at most by the one global sign.
Consequently `x` records the scalar parity data without a reference-choice
ambiguity.

## 3. The Gaussian form

For quotient vertices `u,v`, let

```text
K_Q(u,v) = i^(graph distance in Q from u to v).
```

Expand `x^T K_Q x` over ordered pairs of quotient components, then expand
each `x_u x_v` over ordered pairs of original vertices in those components.
The gauge signs convert the quotient phase into the phase of the original
weighted path. Diagonal terms contribute one per original vertex. The real
and imaginary parts are therefore

```text
18 + 2 * sum_{even unordered pairs} (-1)^(distance/2),
 2 * sum_{odd unordered pairs}  (-1)^((distance-1)/2).
```

The even target distances are `2,4,...,152`. Their alternating sum is zero.
The odd target distances are `1,3,...,153`. Their alternating sum is one.
It follows that

```text
x^T K_Q x = 18 + 2i.                                  (1)
```

Together with the order constraints, every component coordinate satisfies

```text
m_v > 0,      |x_v| <= m_v,      x_v = m_v (mod 2),
sum_v m_v = 18,
color sums of m = {7,11}.
```

These are necessary scalar conditions extracted from the actual tree. They
are not sufficient conditions for component spectra or a lift.

## 4. Explicit equations for the three shapes

For `P5`, number the path vertices `0,1,2,3,4`. Equation (1) is equivalent to

```text
sum_j x_j^2 - 2(x0*x2 + x1*x3 + x2*x4) + 2*x0*x4 = 18,
x0*x1 + x1*x2 + x2*x3 + x3*x4 - x0*x3 - x1*x4 = 1.
```

For the fork with edges `01,02,03,34`, it is equivalent to

```text
sum_j x_j^2 - 2(x1*x2 + x1*x3 + x2*x3 + x0*x4) = 18,
x0*(x1+x2+x3) + x3*x4 - x4*(x1+x2) = 1.
```

For `K1,4`, let the center coordinate be `a`, the leaf coordinates be
`y_1,...,y_4`, and `Y = sum_j y_j`. Then

```text
a*Y = 1,
a^2 + 2*sum_j y_j^2 - Y^2 = 18.
```

After the global sign choice, the first equation gives `a=Y=1`; the second
gives `sum_j y_j^2=9`. If `k` leaf coordinates have absolute value 2 and `l`
have absolute value 1, then `4k+l=9` with `k+l<=4`, so `(k,l)=(2,1)`. The
two magnitude-two values have opposite signs and the unit value is positive.
Thus the leaf-coordinate multiset is

```text
{2, -2, 1, 0}.
```

This is a consequence at the Gaussian scalar layer. It still leaves the
internal component trees, actual bridge ports, and the full 153-distance
spectrum to be realized.

## 5. Formal boundary

The Lean adapter applies the preceding construction to the actual odd-edge
quotient, supplies a relabelling to one of the three five-vertex shapes, and
records the order, parity, and Gaussian domain conditions. No endpoint in
`G022` asserts a finite census, a feasibility decision, or an order-18
existence/nonexistence result.
