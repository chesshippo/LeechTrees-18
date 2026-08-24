# Odd-edge quotient second-weight bound

## Scope

This note proves topology-free necessary conditions for a classical
positive-integral Leech tree. It does not prove existence or nonexistence at
order 18, and it does not assert that any equality pattern below lifts to a
Leech tree. The proof is finite counting.

Let `T` be a Leech tree of order `n`, put

```text
N = binomial(n,2),       E = floor(N/2),
```

and let its two vertex-parity classes have orders `a,b`. Thus

```text
binomial(a,2)+binomial(b,2)=E.
```

Let `r` be the number of odd physical edge weights. Distance 1 is physical,
so `r>=1`; when `r>=2`, list the odd physical weights as

```text
1=q_1<q_2<...<q_r.
```

Deleting all odd physical edges leaves exactly `r+1` connected even-edge
components. Contracting them gives a tree `H` with `r` edges. Each component
is monochromatic, and the bipartition of `H` is exactly the two vertex-parity
colors.

For positive integers `1<=k<=M`, define

```text
F(M,k) = (k-1)(2M-k)/2.
```

For `r>=1`, define the topology-free quantity

```text
G_{a,b}(r)
 = min { F(a,k)+F(b,l) :
         k+l=r+1, 1<=k<=a, 1<=l<=b }.              (1)
```

The feasible range can equivalently be written

```text
max(1,r+1-b) <= k <= min(a,r),   l=r+1-k.           (2)
```

## Theorem

Let `S` be the number of unordered original-vertex pairs whose endpoints lie
in distinct even-edge components of the same parity color. Then:

1. If the two quotient color classes contain `k,l` components, respectively,
   then

   ```text
   S >= F(a,k)+F(b,l) >= G_{a,b}(r).                (3)
   ```

2. Every one of these `S` pairs has a distinct, even, nonphysical distance.
   If `r>=2`, every such distance is at least `q_2+1`.

3. If `h` is the number of even physical weights in `[q_2+1,N]`, then

   ```text
   S <= E-(q_2-1)/2-h.                              (4)
   ```

   Since there are exactly `n-1-r` even physical edges, the two
   placement-free consequences are

   ```text
   S <= E-(n-1-r),
   S <= E-(q_2-1)/2,

   S <= E-max(n-1-r,(q_2-1)/2).                    (5)
   ```

4. In particular, for `r>=2`, every Leech tree satisfies the topology-free
   cap

   ```text
   q_2 <= 2(E-G_{a,b}(r))+1.                        (6)
   ```

The fixed quotient-color count in (3), the exact component sizes used in the
definition of `S`, and the physical puncture `h` in (4) can all strengthen
(6). Formula (6) is the result after deliberately forgetting those data.

## Proof

Write the orders of the `k` components of the first color as
`x_1,...,x_k`, and those of the `l` components of the second color as
`y_1,...,y_l`. They are positive integers with sums `a` and `b`. Hence

```text
S = sum_{i<i'} x_i x_i' + sum_{j<j'} y_j y_j'.     (7)
```

For any positive `z_1+...+z_k=M`,

```text
sum_{i<j} z_i z_j = (M^2-sum_i z_i^2)/2.
```

The sum of squares is maximized, subject only to positivity and the fixed
sum, at `(M-k+1,1,...,1)`: whenever two entries are at least 2, transferring
one unit from the smaller to the larger weakly increases the sum of squares,
and iterating reaches that vector. Therefore

```text
sum_{i<j} z_i z_j
 >= [M^2-(M-k+1)^2-(k-1)]/2
  = F(M,k).                                         (8)
```

Applying (8) to both colors proves the first inequality in (3), and minimizing
over every feasible quotient bipartition count proves the second. This is
topology-free: no quotient shape or port placement has been assumed.

Now take a pair counted by `S`. Its quotient path has positive even length,
so it traverses at least two distinct odd physical edges. Its distance is
therefore even. When `r>=2`, the sum of the odd weights on that path is at
least the sum of the two globally smallest distinct odd physical weights,
namely `1+q_2`; all even-edge contributions are nonnegative. Thus its distance
is at least `q_2+1`.

The endpoints cannot be the endpoints of a physical edge: an even edge would
have kept them in one component, and an odd edge would put them in opposite
colors. In a Leech tree a numerical physical weight is already realized by
the endpoint pair of its physical edge, so uniqueness also prevents any pair
counted by `S` from taking the value of some other physical edge. Thus all
`S` values are nonphysical. The Leech property makes them mutually distinct.

There are exactly

```text
E-(q_2-1)/2
```

even integers in `[q_2+1,N]`. Deleting the `h` even physical ranks in that
interval proves (4). Independently, there are `n-1-r` even physical ranks in
all, so only `E-(n-1-r)` nonphysical even ranks in all. This proves both upper
bounds in (5), and their conjunction is the last line of (5). Finally,
combine `G_{a,b}(r)<=S` with the second upper bound in (5) and rearrange to
obtain (6). QED.

### Direction of the below-`q_2` statement

The same-color distinct-component pairs do **not** give a positive lower
bound on the number of nonphysical even ranks below `q_2`. They occupy the
tail at or above `q_2+1`. Put

```text
I = sum_i binomial(m_i,2),
e = n-1-r,
F_even = E-e.
```

Partitioning all same-color pairs according to whether their even component
is the same gives the exact identity

```text
E = I+S.                                             (7a)
```

If `B_<` is the number of nonphysical even ranks below `q_2`, then (4) is
equivalently

```text
B_< <= F_even-S.                                    (7b)
```

Thus the proposed `S>=G` theorem gives an upper bound below `q_2`, or a lower
bound on the high nonphysical tail. Any wording that reverses this direction
is false. The order-6 control below exhibits `B_< = 0` despite a positive
same-color cross count.

## Order 18 evaluation

At order 18,

```text
N=153, E=76, {a,b}={7,11}.
```

The values needed in (1) are

```text
F(7,k):   0,6,11,15,18,20,21
F(11,k):  0,10,19,27,34,40,45,49,52,54,55.
```

The following table includes every formal `r` boundary. The order-18 interval
highlighted in the theorem family is `3<=r<=15`.

| `r` | one minimizing `(k,l)` | `G_{7,11}(r)` | cap on `q_2` |
|---:|---:|---:|---:|
| 1 | `(1,1)` | 0 | not defined |
| 2 | `(2,1)` | 6 | 141 |
| 3 | `(3,1)` | 11 | 131 |
| 4 | `(4,1)` | 15 | 123 |
| 5 | `(5,1)` | 18 | 117 |
| 6 | `(6,1)` | 20 | 113 |
| 7 | `(7,1)` | 21 | 111 |
| 8 | `(7,2)` | 31 | 91 |
| 9 | `(7,3)` | 40 | 73 |
| 10 | `(7,4)` | 48 | 57 |
| 11 | `(1,11)` | 55 | 43 |
| 12 | `(2,11)` | 61 | 31 |
| 13 | `(3,11)` | 66 | 21 |
| 14 | `(4,11)` | 70 | 13 |
| 15 | `(5,11)` | 73 | 7 |
| 16 | `(6,11)` | 75 | 3 |
| 17 | `(7,11)` | 76 | 1 |

Some rows have a second minimizing endpoint choice. Algebraically,
`F(a,k)+F(b,r+1-k)` is concave in `k`, so it is enough to inspect the two
endpoints of the feasible interval (2). The displayed table was also obtained
by direct substitution of every feasible `k`.

The `r=1` row is a count boundary only: there is no `q_2`. The `r=2` formula
is valid, although an independent inherited theorem already excludes the
two-odd branch at order 18. The `r=16` row is also valid as a necessary
condition, although that layer has a separate exact finite exclusion. The
`r=17` row is physically impossible already because weight 2 is an even
physical edge; its cap `q_2<=1` is consistent with impossibility.

## Stronger companion from both low-rank parities

Write `q_2=2t+1`, and let the unique weight-1 quotient edge join even
components of orders `x,y`. Every odd target rank below `q_2`, namely
`1,3,...,2t-1`, must cross that edge and no other odd edge. Hence `t<=xy`.
Every even target rank below `q_2`, namely `2,4,...,2t`, must lie inside one
even component, because a same-color route crossing two odd edges has weight
at least `1+q_2`. Hence `t<=I`, and the fixed-profile inequality is

```text
q_2 <= 2 min(I,xy)+1.                               (7c)
```

The `t<=I` half is exactly (7a) combined with the unpunctured same-color tail
bound; it is not an independent gain. The new ingredient is `t<=xy`.

For fixed quotient color component counts `k,l`, put

```text
X=a-k+1,       Y=b-l+1.
```

Then `I<=binomial(X,2)+binomial(Y,2)` and `xy<=XY`. Both upper capacities are
attained simultaneously at the abstract component-decomposition level by
placing all excess mass in the two weight-1-incident components. After
forgetting the actual `k`, the quantifier is therefore a **maximum**:

```text
H_{a,b}(r)
 = max { min(binomial(a-k+1,2)+binomial(b-l+1,2),
             (a-k+1)(b-l+1)) :
         k+l=r+1, 1<=k<=a, 1<=l<=b },

q_2 <= 2 H_{a,b}(r)+1.                              (7d)
```

Using a minimum in (7d) would be an unsafe quantifier reversal.

At order 18 the companion and effective tables are:

| `r` | `H_{7,11}(r)` | companion cap | odd packing from `Q<=68` | effective cap |
|---:|---:|---:|---:|---:|
| 3 | 60 | 121 | 65 | 65 |
| 4 | 51 | 103 | 63 | 63 |
| 5 | 45 | 91 | 61 | 61 |
| 6 | 38 | 77 | 59 | 59 |
| 7 | 32 | 65 | 57 | 57 |
| 8 | 27 | 55 | 55 | 55 |
| 9 | 21 | 43 | 53 | 43 |
| 10 | 18 | 37 | 51 | 37 |
| 11 | 13 | 27 | 49 | 27 |
| 12 | 10 | 21 | 47 | 21 |
| 13 | 7 | 15 | 45 | 15 |
| 14 | 4 | 9 | 43 | 9 |
| 15 | 3 | 7 | 41 | 7 |

The packing column uses the separately scoped, computationally certified
order-18 input `Q<=68`. The largest odd weight is then at most 67, and the
`r-2` distinct larger odd weights after `q_2` give

```text
q_2 <= 67-2(r-2)=71-2r.
```

The effective cap is the minimum of this and (7d). The companion first
improves the inherited packing cap at `r=9`, ties it at `r=8`, and is
operationally redundant to it for `r<=7`.

### Fixed-profile form

For a fixed order-18 odd quotient with component orders `m_v`, weight-1 edge
`alpha beta`, and known even physical weights, the necessary fixed-profile
conditions are

```text
t=(q_2-1)/2,
I=sum_v binomial(m_v,2),
S=76-I,
h=#{even physical w : w>=q_2+1},

t <= I,
t <= m_alpha*m_beta,
S+h <= 76-t.                                        (7e)
```

The first and third inequalities are algebraically redundant when `S=76-I`
and `h=0`, but retaining `h` gives the physical-rank-punctured strengthening.
These are necessary constraints only; they do not encode compatible rooted
depths, ports, or a Leech lift.

## Equality and endpoint cases

- Adjacent quotient components have opposite colors and are never counted in
  `S`. Distinct same-color components are at quotient distance at least 2.
- Singleton components are allowed. Formula `F(M,M)=binomial(M,2)` correctly
  counts the case in which every component of that color is a singleton.
- Equality in (8) requires component orders `(M-k+1,1,...,1)`, up to order.
  Equality in the topology-free `G` bound additionally requires a minimizing
  feasible `(k,l)`.
- Equality in (6) would also require `S=G`, no even physical rank at least
  `q_2+1`, and the `S` cross-component distances to fill the entire even tail.
  These are necessary equality conditions, not a lift or existence claim.
- If a same-color quotient path omits the weight-1 edge, its odd-edge sum is
  larger than `1+q_2`; using `1+q_2` remains a valid uniform lower bound.
- The argument counts original vertex pairs, not quotient-vertex pairs. The
  factors `x_i x_j` and `y_i y_j` are essential.

### Exact `r=15`, `q_2=7` boundary

At order 18 the final `r=15` cap can be attained only at a rigid local
capacity boundary. Here `t=3`. Up to swapping parity colors, the weight-1 edge
joins a component of order 3 to a singleton and the other 14 components are
singletons. The three internal pairs of the order-3 component must realize
`2,4,6`, forcing its two even edge weights to be 2 and 4. Its three pairs
across the weight-1 bridge must realize `1,3,5`, forcing that bridge to attach
at the middle vertex of the order-3 path. Thus the forced four-vertex prefix
is the weighted three-edge star with incident weights

```text
1,2,4,
```

whose six distances are exactly `1,...,6`. This is a necessary local prefix
at equality, not an order-18 completion or a layer exclusion.

## Strict improvement over the old `ell=2` aggregate tail

The prior square-threshold inequality at `ell=2` uses only the universal
minimum `1+3=4`. At order 18 its aggregate same-color condition is

```text
S <= 59+r.                                          (9)
```

Indeed, there are 75 even ranks in `[4,153]`; of the `17-r` even physical
weights, weight 2 is the unique one below 4, so exactly `16-r` are punctured
from that tail, giving `75-(16-r)=59+r`.

For an abstract `r=15` quotient-size datum, take five components on the
7-vertex color side with orders

```text
(3,1,1,1,1)
```

and eleven singleton components on the 11-vertex side. A bipartite tree with
color-class counts `(5,11)` exists (for example, a double star), so this is a
legitimate quotient/component-size datum. Its same-color cross count is

```text
S = [3*4+binomial(4,2)] + binomial(11,2)
  = 18+55
  = 73.
```

It passes (9), since `73<=74`. If the second odd physical weight is formally
set to `q_2=9`, however, every one of those 73 distances would have to occupy
an even rank in

```text
{10,12,...,152},
```

which has only 72 elements even before physical-rank puncturing. The new bound
rejects it (`q_2<=7`). This proves strictness relative to the old `ell=2`
numeric relaxation.

This datum is not asserted to be a Leech tree, a candidate, a positive lift,
or a point passing the other inherited inequalities. It is only an abstract
strictness witness between two necessary rank-capacity tests.

## Small-order direction counterexample

The archived order-6 Leech regression fixture has edges

```text
12(1), 13(2), 16(5), 46(4), 56(8)
```

and spectrum exactly `1,...,15`. Its odd physical weights are `1,5`, so
`q_2=5`. Deleting them leaves a quotient path with component orders `1,2,3`.
The two same-color leaf components contribute cross distances `6,10,14`, all
above `q_2`. Both even ranks below `q_2`, namely 2 and 4, are physical, so
there are zero nonphysical even ranks below `q_2`. This is an actual Leech
counterexample to the direction-reversed claim, while fully agreeing with the
high-tail theorem. It has order 6 and is not a target witness.

## Truncated direct sum at the weight-1 port

Let `A,B` be the rooted even-depth sets in the two weight-1-incident
components, divided by 2. Global distance uniqueness makes every indexed sum
in `A+B` distinct. The low odd ranks force

```text
A(z)B(z) = 1+z+...+z^(t-1)             (mod z^t).   (10)
```

This is a sound fixed-rooted-profile filter, but it gives no topology-free
cardinality consequence beyond `|A||B|>=t`. For every positive `x,y` with
`xy>=t`, the direct sets

```text
A={0,1,...,x-1},
B={0,x,2x,...,(y-1)x}
```

tile `0,...,xy-1` and satisfy (10). A ragged control is

```text
t=5, A={0,1,4}, B={0,2}, A+B={0,1,2,3,4,6},
```

which covers the forced prefix but does not continue to an interval. Only at
the equality `xy=t` does (10) become the full interval factorization used by
the archived one-odd argument. With `xy>t`, its exhaustiveness and subsequent
alternating-sum conclusions cannot be imported.
