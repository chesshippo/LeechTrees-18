# Order-18 Gaussian component-count flexibility

This is an arithmetic counterexample theorem for the `t=-1` Gaussian quotient
filter. It is **not** a Leech-tree construction and does not assert that the
listed component data have compatible distance spectra.

## 1. Gaussian quotient conditions

For an order-18 Leech tree, delete all odd-weight physical edges.  The
nonempty even components form a quotient tree `Q`.  If component `v` has
order `m_v` and gauged parity imbalance `x_v`, the promoted necessary layer is

\[
 \sum_{v\in A}m_v=7,\qquad \sum_{v\in B}m_v=11,             \tag{1}
\]

for the two quotient colors (up to swapping),

\[
 m_v>0,\quad |x_v|\le m_v,\quad x_v\equiv m_v\pmod2,       \tag{2}
\]

and

\[
 x^{\mathsf T}K_Qx=18+2\mathrm i,
 \qquad (K_Q)_{uv}=\mathrm i^{d_Q(u,v)}.                   \tag{3}
\]

Condition (2) is exact at the arithmetic parity-class level: the least
possible component order is `|x|` for nonzero `x` and 2 for `x=0`, and any
remaining order is an even slack.  It is not a component-spectrum condition.

## 2. The theorem

**Theorem (complete surviving-range flexibility).** For every
`c in {4,5,...,18}`, there is a depth-two quotient tree `Q` on `c`
vertices and integer data `(m_v,x_v)` satisfying (1)--(3).  Consequently the
number of odd physical edges `r=c-1` can be every value from 3 through 17 at
this necessary-condition layer.

In particular, no argument that uses only the quotient-tree property, the
7/11 color budgets, the component magnitude/parity bounds, and the Gaussian
identity can exclude any `c >= 4`. Any stronger conclusion must retain
information discarded by this layer, such as component spectra, ports,
odd-edge magnitudes, or a stronger residue evaluation.

### Proof

Root a depth-two tree at a vertex with imbalance `a`.  Let its children have
imbalances `y_j`, and let the grandchildren attached to child `j` have
imbalances `z_{jt}`.  Put

\[
 S_j=\sum_tz_{jt},\quad S=\sum_jS_j,\quad Y=\sum_jy_j,
 \quad V=\sum_jy_j^2,\quad U=\sum_{j,t}z_{jt}^2.           \tag{4}
\]

The rooted Gaussian recurrence gives

\[
 Z_{jt}=z_{jt},\quad Z_j=y_j+\mathrm iS_j,
 \quad Z_0=(a-S)+\mathrm iY.
\]

Therefore, expanding
`F=Z_0^2+2 sum_{v != 0} Z_v^2` exactly,

\[
\begin{aligned}
 \Re F&=(a-S)^2-Y^2+2\left(V-\sum_jS_j^2\right)+2U,\\
 \Im F&=2\left((a-S)Y+2\sum_jy_jS_j\right).              \tag{5}
\end{aligned}
\]

The following table gives one set of aggregates entering (5) for every `c`:

| `c` | children | grandchildren | `a` | `Y` | `V` | `S` | `U` | `sum S_j^2` | `sum y_j S_j` |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 4 | 3 | 0 | 1 | 1 | 9 | 0 | 0 | 0 | 0 |
| 5 | 4 | 0 | 1 | 1 | 9 | 0 | 0 | 0 | 0 |
| 6 | 5 | 0 | 1 | 1 | 9 | 0 | 0 | 0 | 0 |
| 7 | 6 | 0 | 1 | 1 | 9 | 0 | 0 | 0 | 0 |
| 8 | 7 | 0 | 1 | 1 | 9 | 0 | 0 | 0 | 0 |
| 9 | 8 | 0 | 1 | 1 | 9 | 0 | 0 | 0 | 0 |
| 10 | 9 | 0 | 1 | 1 | 9 | 0 | 0 | 0 | 0 |
| 11 | 10 | 0 | 1 | 1 | 9 | 0 | 0 | 0 | 0 |
| 12 | 10 | 1 | 0 | -1 | 9 | 1 | 1 | 1 | 0 |
| 13 | 10 | 2 | 0 | -1 | 9 | 1 | 1 | 1 | 0 |
| 14 | 10 | 3 | 0 | -1 | 9 | 1 | 1 | 1 | 0 |
| 15 | 11 | 3 | 0 | -3 | 11 | 1 | 3 | 1 | -1 |
| 16 | 11 | 4 | 0 | -3 | 11 | 1 | 3 | 1 | -1 |
| 17 | 11 | 5 | -2 | -3 | 11 | -5 | 5 | 7 | 5 |
| 18 | 11 | 6 | 1 | 3 | 11 | 2 | 6 | 4 | 2 |

Substitution into (5) gives `(Re F, Im F)=(18,2)` in every row.  For example,
the two least broom-like endpoint rows are

\[
\begin{array}{c|c|c}
c&\Re F&\Im F\\ \hline
17&3^2-(-3)^2+2(11-7)+2(5)&2(3(-3)+2(5))\\
18&(-1)^2-3^2+2(11-4)+2(6)&2((-1)3+2(2)),
\end{array}
\]

which are respectively `(18,2)` and `(18,2)`.

The certificate also assigns positive component orders.  In every row the
root plus all grandchildren have total order 7, the children have total
order 11, and every `(x,m)` satisfies (2).  Thus (1)--(3) hold for every
listed `c`, proving the theorem. The fifteen rows are explicit counterexamples
to every proposed exclusion of a surviving `c` based solely on (1)--(3).
