# Conditional `9|9` parity-tail identities at `q=67` and `q=66`

## Statement and scope

This note proves conditional coefficient identities for a physical `9|9` edge.
It does not construct a tree, prove that the coefficient systems lift to one,
or establish infeasibility at either weight.

The central conclusion is:

1. At `q=67`, the one-hole parity block has exactly one of two intrinsic
   forms:
   - an even-residual block with products `4*2` and `5*7`, with a carry on the
     odd-odd product; there are **two** endpoint-color placements,
     `4*2 + z(5*7)` and `5*7 + z(4*2)`;
   - an odd-residual block with two unshifted products of sizes `5*6` and
     `4*3`.
2. At `q=66`, the `kappa=-5` one-hole block consists of the two unshifted
   opposite-parity products `4*2` and `5*7`.  The `kappa=3` block has two
   holes and consists of an even-even product plus a shifted odd-odd product;
   which of `5*6` and `4*3` is shifted depends on the endpoint color.

The first `q=67` placement is exactly the requested
`4x2 + shifted 5x7` convention.  The second placement cannot be quotiented
away by swapping the two sides: a side swap preserves which rooted-depth
product incurs the odd-odd carry.

## 1. Hypotheses and intrinsic half-depth polynomials

Assume conditionally that an order-18 positive-integral weighted tree has
unordered pair-distance multiset exactly

```text
{1,2,...,153},
```

and that a physical edge `ab` of weight `q` separates two sides `A,B`, each
of order 9.  Root the sides at `a,b` and write

```text
alpha_u = d_A(a,u),       beta_v = d_B(b,v).
```

All 153 vertex pairs have distinct distances.  Consequently:

- each depth row consists of nine distinct nonnegative integers and contains
  zero exactly once;
- the indexed map `(u,v) -> alpha_u+beta_v` is injective;
- every residual sum lies in `[0,153-q]`.

Put

```text
delta_A = # {alpha even} - # {alpha odd},
delta_B = # {beta  even} - # {beta  odd}.
```

Define four sets of half-depths:

```text
A0 = {alpha/2       : alpha even},
A1 = {(alpha-1)/2   : alpha odd},
B0 = {beta/2        : beta  even},
B1 = {(beta-1)/2    : beta  odd}.
```

For a finite set `C`, use the same letter for its set polynomial
`C(z)=sum_{c in C} z^c`, and put `U_m(z)=1+z+...+z^m`.  The roots give

```text
0 in A0,       0 in B0.                                      (1)
```

The polynomial encoding the even residuals, compressed by a factor of two,
is

```text
E(z) = A0(z)B0(z) + z A1(z)B1(z),                            (2)
```

because `(2r+1)+(2s+1)=2(r+s+1)`.  The polynomial encoding the odd
residuals, after subtracting one and halving, is

```text
O(z) = A0(z)B1(z) + A1(z)B0(z).                              (3)
```

There is no carry in (3).  Equations (2)--(3) are identities with indexed
multiplicity: a coefficient is the number of indexed cross pairs giving that
compressed residual.  The Leech hypothesis makes every coefficient zero or
one, including across the two summands in each equation.  This is stronger
than equality of collapsed supports.

If `p=delta_A delta_B`, then

```text
# even residuals = (81+p)/2,
# odd  residuals = (81-p)/2.                                 (4)
```

Finally, the 77 odd target distances imply that the two vertex parity classes
have sizes 7 and 11: if their sizes are `r,18-r`, then
`r(18-r)=77`.  Thus a coloring rooted at any vertex has total signed
imbalance `+4` or `-4`.

## 2. Complete `q=67` arithmetic

Here the residual range is `[0,86]`.  It contains 44 even values, compressed
to `[0,43]`, and 43 odd values, compressed to `[0,42]`.

Because `q` is odd, a coloring rooted at `a` has total imbalance

```text
delta_A - delta_B = +/-4.                                    (5)
```

Actual distance parity is the opposite of residual parity.  There are 44 odd
targets and 43 even targets at least 67, so (4) gives

```text
(81+p)/2 <= 44,       (81-p)/2 <= 43,
-5 <= p <= 7.                                                (6)
```

Both deltas are odd integers between `-9` and `9`.  Solving (5)--(6) gives
exactly

```text
(-1,-5), (-5,-1), (1,5), (5,1),
(1,-3), (-3,1), (3,-1), (-1,3).                              (7)
```

The first four pairs have `p=5`; the last four have `p=-3`.
Thus there are exactly two one-hole parity mechanisms.

### 2.1 Even residuals: requested `4x2 + shifted 5x7`, and its mirror

When `p=5`, equation (4) gives 43 even residuals and 38 odd residuals.  Hence
the even-residual block misses exactly one of its 44 possible exponents:

```text
E(z) = U_43(z) - z^j.                                        (8)
```

There are two side-swap orbits.

For the negative-delta orbit, orient the sides as

```text
(delta_A,delta_B)=(-1,-5),
(|A0|,|A1|; |B0|,|B1|)=(4,5; 2,7).                          (9)
```

Then (8) is exactly

```text
A0(z)B0(z) + z A1(z)B1(z) = U_43(z)-z^j,                    (10)
```

with term sizes

```text
4*2 + shifted (5*7) = 8+35=43.                              (11)
```

This is the requested case.  By (1), the coefficient of `z^0` in (10) is
one, so

```text
j in {1,2,...,43}.                                           (12)
```

The missing cross distance is the odd target `67+2j`; it is an internal
distance on one of the two sides.

For the positive-delta orbit, orient as

```text
(delta_A,delta_B)=(1,5),
(|A0|,|A1|; |B0|,|B1|)=(5,4; 7,2).                          (13)
```

The same intrinsic formula (8) now has term sizes

```text
unshifted (5*7) + shifted (4*2) = 35+8.                      (14)
```

It also has `j in {1,...,43}`.  Swapping `A` and `B` commutes the factors in
each product but does not move the factor `z`; therefore (14) is not (11).
Any exhaustive classification must retain both placements unless an
additional theorem fixes the endpoint's global parity class.

The complementary odd-residual block has five holes.  In both placements,

```text
O(z) = U_42(z) - H_5(z),                                     (15)
```

where `H_5` is a sum of five distinct monomials.  Equations (8) and (15)
together, not (8) alone, encode all 81 indexed cross sums.

### 2.2 Odd residuals: requested unshifted `5x6 + 4x3`

When `p=-3`, there are 39 even residuals and 42 odd residuals.  Therefore

```text
O(z) = U_42(z)-z^j,       j in {0,1,...,42}.                  (16)
```

There are again two side-swap orbits, but both give the same two product
sizes.  Representatives are

```text
(delta_A,delta_B)=(1,-3):
(|A0|,|A1|; |B0|,|B1|)=(5,4; 3,6),                          (17)
```

and

```text
(delta_A,delta_B)=(3,-1):
(|A0|,|A1|; |B0|,|B1|)=(6,3; 4,5).                          (18)
```

In (17), equation (16) reads

```text
A0(z)B1(z) + A1(z)B0(z) = U_42(z)-z^j                       (19)
```

with sizes

```text
5*6 + 4*3 = 30+12=42.                                       (20)
```

In (18) the sizes are `6*5 + 3*4`, the same two unordered products.  Neither
term in (19) has a carry: it encodes `(even+odd-1)/2` or
`(odd+even-1)/2`.

The constant coefficient gives an exact root/depth-one convention.  Since
`0 in A0 cap B0`,

```text
[z^0]O = 1_{0 in A1} + 1_{0 in B1}.                          (21)
```

Thus indexed directness forbids depth 1 on both sides, and

```text
j=0  iff neither side has rooted depth 1;
j>0  iff exactly one side has rooted depth 1.                 (22)
```

The missing cross distance is the even target `68+2j`.  The complementary
even block has five holes:

```text
E(z)=U_43(z)-K_5(z),       [z^0]K_5=0.                       (23)
```

### 2.3 Endpoint signs in the `X=4, x` convention

Fix the global coloring sign so its total imbalance is `X=4`.  Let `x` be
the signed mass of side `A`, and put `epsilon=sigma(a)`.  For odd `q`,

```text
delta_A = epsilon*x,
delta_B = -epsilon*(4-x).                                    (24)
```

The promoted tail bound leaves `x in {-1,1,3,5}`.  For `kappa=x(4-x)=-5`,
the complete endpoint table is

| `(x,epsilon)` | `(delta_A,delta_B)` | placement |
|---|---|---|
| `(-1,+1)` | `(-1,-5)` | `4*2 + z(5*7)` |
| `(5,-1)` | `(-5,-1)` | side swap of the preceding row |
| `(-1,-1)` | `(1,5)` | `5*7 + z(4*2)` |
| `(5,+1)` | `(5,1)` | side swap of the preceding row |

Therefore the simultaneous normalization `X=4`, `x=-1`, and
`sigma(a)=+1` selects the requested placement but is not available for every
abstract surviving edge.  The endpoint sign is extra data.  For
`kappa=3`, formula (24) gives the four `p=-3` pairs in (7); all retain the
unshifted aggregate sizes `5*6` and `4*3`.

## 3. Coefficient conditions

Let `s(C)=sum_{c in C} c`.  Differentiating the two exact identities at
`z=1` provides useful independent checks.

For the requested orientation (9)--(10),

```text
2s(A0)+4s(B0)+7s(A1)+5s(B1)+35 = 946-j.                     (25)
```

For (17)--(19),

```text
6s(A0)+5s(B1)+3s(A1)+4s(B0) = 903-j.                        (26)
```

Evaluating at `z=-1` checks the carry sign:

```text
A0(-1)B0(-1)-A1(-1)B1(-1) = (-1)^(j+1)                    (27)
```

in (10), whereas

```text
A0(-1)B1(-1)+A1(-1)B0(-1) = 1-(-1)^j                     (28)
```

in (19).  In particular, deleting the factor `z` in (10) changes (27) and is
not a harmless notation change.

An exact finite additive classification requires no unbounded variables.  At
`q=67`, take

```text
A0,B0 subset [0,43],       A1,B1 subset [0,42],              (29)
```

post the cardinalities from one row of (9), (13), (17), or (18), post (1),
and impose the relevant pair of polynomial identities:

```text
p=5:    E=U_43-z^j,       O=U_42-H_5;
p=-3:   E=U_43-K_5,       O=U_42-z^j.                        (30)
```

Here `H_5,K_5` have five distinct exponents in the displayed universe, and
`0` is not an exponent of `K_5`.  Equality is in `Z[z]`, so it also asserts
that every coefficient outside the displayed interval is zero.  Equivalently,
for every exponent, expand the two convolutions in (2)--(3) as sums of binary
products and set the coefficient to zero or one according to (30).  This
explicitly preserves indexed multiplicity and the disjointness of the two
parity sub-blocks.

This finite system is an exact classification specification for the rooted
depth **rows**.  A surviving row pair is not yet a pair of rooted trees.  The
second, still finite, stage must reconstruct a positive-integral rooted tree
on each row and verify

```text
S_A disjoint-union S_B disjoint-union
{67+alpha+beta : alpha in D_A, beta in D_B}
= {1,...,153},                                                (31)
```

with indexed multiplicity, distinct physical edge weights, and every
largest-edge restriction.  The polynomial conditions do not imply (31).
Conditions (30) and (31) do not by themselves prove reconstruction; that is
the precise remaining gap.

## 4. The `q=66` identities

Now let the `9|9` edge have even weight 66.  The residual interval is
`[0,87]`; both compressed parity universes are `[0,43]`.  Because `q` is
even, a coloring rooted at `a` gives

```text
delta_A+delta_B=+/-4,                                        (32)
```

and actual parity equals residual parity.  Both tails have 44 values, so
`-7<=p<=7`.  The surviving delta pairs have either

```text
p=-5:  opposite signs of magnitudes 1 and 5;
p= 3:  equal signs of magnitudes 1 and 3.                    (33)
```

For `p=-5`, the odd block has 43 terms and hence

```text
O(z)=A0(z)B1(z)+A1(z)B0(z)=U_43(z)-z^j,                     (34)
```

where the two unshifted product sizes are `4*2` and `5*7`.
There is no carry because every represented residual is odd.  Here
`j in [0,43]`, and the depth-one rule (22) holds verbatim.  The missing
actual distance is `67+2j`.  The complementary even block has six holes:

```text
E(z)=U_43(z)-K_6(z),       [z^0]K_6=0.                       (35)
```

For `p=3`, the even block has 42 terms and misses two exponents:

```text
E(z)=A0(z)B0(z)+zA1(z)B1(z)
    =U_43(z)-z^j1-z^j2,                                     (36)
```

where `j1,j2` are distinct members of `{1,...,43}`.  The exclusion of zero
follows from the root-root pair.  If the rooted deltas are positive, a
representative is

```text
(delta_A,delta_B)=(1,3):
unshifted 5*6 + shifted 4*3.                                 (37)
```

If they are negative, a representative is

```text
(delta_A,delta_B)=(-1,-3):
unshifted 4*3 + shifted 5*6.                                 (38)
```

Thus the endpoint-color mirror must again be retained.  The complementary
odd block has five holes.  For a global `X=4` coloring and
`epsilon=sigma(a)`, the even-edge relation is

```text
delta_A=epsilon*x,       delta_B=epsilon*(4-x),               (39)
```

which makes (37) the majority-endpoint placement and (38) the
minority-endpoint placement.

For a finite `q=66` coefficient classification, use
`A0,A1,B0,B1 subset [0,43]`, the cardinalities in (33), roots (1), and the
coupled identities (34)--(36) with their complementary hole polynomials.
As at `q=67`, rooted-tree reconstruction and the full internal spectrum remain
separate proof obligations.

### 4.1 The raw seven-hole factorization and its exact characters

Let the two uncompressed rooted depth rows be

```text
D_A={alpha_u:u in A},       D_B={beta_v:v in B}.
```

The indexed directness and range already proved give the ordinary polynomial
identity

```text
D_A(z)D_B(z)=U_87(z)-H(z),                                 (40)
```

where `|D_A|=|D_B|=9`, both rows contain zero exactly once, and `H` is a
seven-element subset of `{1,...,87}`.  Thus (40) is the exact direct sum

```text
D_A direct-sum D_B = [0,87] \ H.                            (41)
```

In particular, `(D_A-D_A) cap (D_B-D_B)={0}` when the difference sets use
all ordered pairs, and `D_A cap D_B={0}`.

The hole parity counts are not free.  From (33)--(36),

| `p=delta_A delta_B` | even holes | odd holes |
|---:|---:|---:|
| `-5` | 6 | 1 |
| `3` | 2 | 5 |

This also follows by evaluating (40) at `z=-1`.  Since `U_87(-1)=0`,

```text
H(-1) = -D_A(-1)D_B(-1) = -p.                              (42)
```

The first derivative at 1 gives a separate exact checksum.  If
`s(D)=sum_{d in D}d`, then

```text
sum H = sum_{t=0}^{87}t - 9s(D_A)-9s(D_B)
      = 3828-9(s(D_A)+s(D_B)),                              (43)
```

and hence

```text
sum H = 3 (mod 9).                                          (44)
```

In the `p=-5` notation (34)--(35), the raw holes are six even values
`2k`, with `k` an exponent of `K_6`, and the one odd value `2j+1`.
Equation (44) becomes

```text
sum_{k in supp(K_6)} k + j = 1 (mod 9).                     (45)
```

For `p=3`, let the five odd-hole half-ranks be the exponents of the
complementary polynomial `H_5`.  Equations (36), (44) give

```text
j1+j2+sum_{h in supp(H_5)}h = 8 (mod 9).                    (46)
```

These are necessary coefficient checks, not replacements for (40).

There is also a topology-independent depth-span condition.  Sort the depth
rows as

```text
0=a0<a1<...<a8,       0=b0<b1<...<b8.
```

Each 9-vertex side has 36 internal vertex pairs, and their 36 distances are
distinct positive integers.  Its diameter is therefore at least 36.  Every
internal distance on side `A` is at most the sum of the two largest distinct
root depths, and similarly on `B`.  Consequently

```text
a7+a8 >= 36,       b7+b8 >= 36,                             (47)
a8 >= 19,          b8 >= 19,       a8+b8 <= 87.             (48)
```

The strict ordering gives the sharpened lower bounds in (48): if, for
example, `a8<=18`, then `a7+a8<=17+18=35`.  The last inequality is the
cross-residual range applied to the two maximal depths.  These bounds remain
necessary before choosing either rooted topology.

Finally, (40) has exact cyclic convolution consequences.  For
`m in {4,8,11}`, define residue counts

```text
a_r^(m)=#{a in D_A:a=r (mod m)},
b_r^(m)=#{b in D_B:b=r (mod m)},
h_r^(m)=#{h in H:h=r (mod m)}.
```

Because 88 is divisible by each named modulus, reduction of (40) in
`Z[z]/(z^m-1)` gives, for every `r in Z/mZ`,

```text
sum_{i in Z/mZ} a_i^(m)b_{r-i}^(m) + h_r^(m) = 88/m.        (49)
```

Explicitly, every cyclic-convolution coordinate plus its hole count is

```text
22  modulo 4,
11  modulo 8,
 8  modulo 11.                                               (50)
```

The count vectors are nonnegative integers with totals `9,9,7`, and
`a_0^(m),b_0^(m)>=1` because both depth rows contain zero.  In particular,
each cyclic convolution coordinate is at most the corresponding number in
(50), and the deficit is exactly the hole count in that residue.  Equivalently,
for every nontrivial `m`-th root of unity `omega`,

```text
D_A(omega)D_B(omega)=-H(omega).                              (51)
```

Equations (49)--(51) are exact consequences of (40); they introduce no
collapsed-support or marginal-sufficiency claim.

## 5. Hypothesis dependencies and boundary

The derivation used every required hypothesis explicitly:

1. **Positive integral weights:** depths are nonnegative integers, path parity
   gives a two-coloring, and the half-depth sets are integral.
2. **Exact Leech spectrum:** all pair distances are distinct and lie in
   `[1,153]`; this proves rooted-depth injectivity, indexed cross-sum
   injectivity, and the residual range.
3. **A physical `9|9` edge:** there are exactly 81 indexed cross pairs, and
   both rooted rows have nine entries.
4. **Parity-class sizes `7|11`:** derived from the 77 odd target distances;
   this gives total imbalance magnitude 4 and equations (5), (32).
5. **Parity of `q`:** odd `q=67` reverses actual/residual parity and endpoint
   signs; even `q=66` preserves both.  This is why (10) has a carry, (19) and
   (34) do not, and (36) does.
6. **Indexed, not collapsed, directness:** every polynomial coefficient counts
   representations.  A coefficient greater than one is immediate noncredit.

The assumption that the named edge is the largest physical edge is not needed
for the parity-tail identities themselves.  It matters only when interpreting
the conditional case as `q=Q` and during rooted-tree reconstruction.

No statement here promotes existence, sufficiency of the polynomial systems,
a finite `q=67` exclusion, an order-18 exclusion, or universal nonexistence.
