# G023 formal scope

`G023` consists of conditional row-level implications. The common setting is a
positive-integral weighted tree on 18 vertices with indexed pair-distance
spectrum `{1,...,153}` and a physical weight-`q` edge whose deletion gives two
rooted sides of order 9. Rooted depths determine half-depth sets `P,R,Q,S` and
side imbalances `delta_A,delta_B`.

## A. Coefficientwise parity decomposition

Coefficientwise,

```text
E = P Q + z R S,
O = P S + R Q,
```

all coefficients are in `{0,1}`, and the block sizes are
`(81 +/- delta_A delta_B)/2`. For odd `q`,
`delta_A-delta_B = +/-4`; for even `q`,
`delta_A+delta_B = +/-4`.

## B. Weight 67: three intrinsic shapes

Up to swapping sides, exactly these imbalance/dimension patterns occur:

1. `(-1,-5)`: dimensions `(4,5;2,7)` and
   `P Q + z R S = U_43 - z^j`, with `1 <= j <= 43`;
2. `(1,5)`: dimensions `(5,4;7,2)`, the mirror placement
   `5x7 + z(4x2)`, again with `1 <= j <= 43`;
3. product `-3`, for example `(1,-3)`: dimensions `(5,4;3,6)` and
   `P S + R Q = U_42 - z^j`, with `0 <= j <= 42`.

The complementary block has five holes using the same four sets.

## C. Weight-67 boundary consequences

In the product-5 branches, `j != 1` is equivalent to the weight-2 edge being
incident to a bridge endpoint, and `j != 43` is equivalent to the bridge lying
on the distance-153 path. In the product-`-3` branch, `j != 0` is equivalent
to the weight-1 edge being incident to an endpoint. The derivative and
`z=-1` identities in the formal declarations are part of the same conditional
bundle.

## D. Finite coefficient formulation

The coupled polynomial systems are necessary and sufficient for the stated
cross-row directness and hole pattern when

```text
P,Q subset [0,43],       R,S subset [0,42].
```

This is a statement about the coefficient system. It does not control the two
internal spectra or prove a rooted-tree lift.

## E. Weight 66: branch equations

If `delta_A delta_B = -5`, then

```text
P S + R Q = U_43 - z^j,       0 <= j <= 43,
```

with unshifted dimensions `4x2` and `5x7`; the even complement has six holes.

If `delta_A delta_B = 3`, then

```text
P Q + z R S = U_43 - z^j1 - z^j2,
```

where `j1,j2` are distinct members of `{1,...,43}`. Depending on endpoint
color, the shifted product has dimensions `4x3` or `5x6`; the odd complement
has five holes.

## F. Seven-hole system and congruences

For raw depth rows `D_A,D_B`,

```text
D_A(z) D_B(z) = U_87(z) - H(z),
```

where `H` is a seven-element subset of `{1,...,87}`. Moreover,

```text
(D_A-D_A) intersect (D_B-D_B) = {0},
D_A intersect D_B = {0},
sum H = 3 (mod 9).
```

The specialized congruences in the formal source follow from these identities.

## G. Span and residue filters

For sorted rows,

```text
a7+a8 >= 36,     b7+b8 >= 36,
a8 >= 19,        b8 >= 19,
a8+b8 <= 87.
```

For `m` in `{4,8,11}`, every residue coordinate obeys

```text
sum_i a_i b_(r-i) + h_r = 88/m.
```

## H. Mod-4 Gaussian prefilter

Each row norm is positive and congruent to 1 modulo 4. In the `-5` branch at
least one row has norm 1. In the `3` branch, the only exception is hole norm
25 with row norms `(5,5)` and the stated hole-residue profile.

## Nonclaims

The formal bundle does not enumerate all coefficient systems, reconstruct a
rooted tree, prove a lift, establish feasibility or infeasibility, exclude
weight 67, exclude order 18, or prove universal nonexistence. Those are not
endpoints of `G023`.
