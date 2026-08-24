# Topology-free multi-edge exact cover

## Definitions

Let `F` be a positive-integral weighted forest on `n` fixed vertices and put
`N = binom(n,2)`.  Its components are actual weighted trees.  Define the
internal pair-distance polynomial

\[
P_F(z)=\sum_{K\in\pi(F)}\ \sum_{\{x,y\}\subset K}z^{d_K(x,y)}.
\]

Assume that `F` is a valid increasing-physical-weight prefix: its displayed
distances are distinct elements of `[1,N]`, and its edges are precisely the
physical edges exposed so far.

A **port-labelled merge certificate** has the components of `F` as leaves.
At each internal node `v`, two already constructed child trees `A_v,B_v`
are joined at actual vertices `a_v in A_v`, `b_v in B_v` by an edge of
positive weight `lambda_v`.  The future labels are distinct, exceed all
prefix edge weights, and increase from descendants to ancestors.  Put

\[
R_{A_v,a_v}(z)=\sum_{x\in A_v}z^{d_{A_v}(x,a_v)},\qquad
C_v(z)=z^{\lambda_v}R_{A_v,a_v}(z)R_{B_v,b_v}(z).
\]

Coefficients retain multiplicity; replacing these polynomials by supports
would lose collision information.

## Theorem (merge-cover and self-puncturing)

If `F` has a Leech-tree completion, then it has a port-labelled merge
certificate satisfying the coefficientwise identity

\[
\boxed{P_F(z)+\sum_v C_v(z)=z+z^2+\cdots+z^N.}\tag{EC}
\]

Conversely, if the children in the certificate are the actual recursively
constructed weighted trees and (EC) holds, their root is a Leech-tree
completion of `F`.  Thus, with actual ports and recursive metrics retained,
(EC) is an exact finite characterization, not only a scalar necessary
condition.

Order the internal nodes so that
`lambda_1 < ... < lambda_{m-1}`, where `m` is the number of components of
`F`.  Then (EC) implies all of the following without adding them as separate
assumptions:

1. every `C_t` is internally `0/1`, and all `C_t` are mutually disjoint and
   disjoint from `P_F`;
2. writing `Lambda={lambda_1,...,lambda_{m-1}}`,
   \[
   \operatorname{supp}(C_t)\cap\Lambda=\{\lambda_t\};\tag{SP}
   \]
3. with
   \[
   D_{t-1}=\operatorname{supp}(P_F)\cup
       \bigcup_{s<t}\operatorname{supp}(C_s),
   \]
   one has
   \[
   \lambda_t=\operatorname{mex}_{+}(D_{t-1}).\tag{MEX}
   \]

Thus one shared exact cover simultaneously creates and punctures all future
physical ranks.  A later physical rank cannot be spent inside an earlier
cross block.

### Proof

Process the future physical edges of a completion in increasing weight.
Because every subset of the edges of a tree is a forest, each new edge joins
two current components.  Recording these successive unions gives the binary
merge certificate.  At a merge, the new vertex-pair distances are exactly

\[
d_{A_v}(x,a_v)+\lambda_v+d_{B_v}(b_v,y),
\qquad (x,y)\in A_v\times B_v,
\]

whose multiplicity enumerator is `C_v`.  Every unordered vertex pair is
internal initially or becomes connected at one unique merge, proving the
polynomial decomposition.  A Leech spectrum makes it (EC).

Every rooted depth polynomial has constant coefficient one and all other
exponents positive, so `min supp(C_t)=lambda_t`, with `lambda_t` occurring
once from the two ports.  In (EC) all summands have nonnegative coefficients
and the right side has coefficient one.  Hence the blocks are disjoint.
In particular `lambda_t` belongs to its own block and no other block, proving
(SP).  If `r<lambda_t`, (EC) assigns `r` either to `P_F` or to some block
`C_s`; in the latter case `lambda_s <= r < lambda_t`, hence `s<t`.
Meanwhile `lambda_t` is absent from all earlier terms.  This proves (MEX).
The converse follows because the constructed root is a tree with all `N`
pair distances distinct in `[1,N]`, hence its spectrum is exactly `[1,N]`.

## Sound exact-cover relaxation

For a proposed merge hierarchy, make one slot for each pair
`(x,y) in A_v x B_v`.  The port-pair slot is forced to `lambda_v`.  Give
every other slot any domain that is a **superset** of its possible additive
distance, intersected with the unused ranks; at minimum its values are
strictly larger than `lambda_v`.  Demand one global injective matching of all
slots into the remaining ranks.  The forced singleton owner slots make the
same `Lambda` unavailable to every non-owner slot, so self-puncturing is
enforced without guessing separate holes block by block.

Any completion induces such a matching.  Therefore a Hall violation after
exhausting all possible merge hierarchies, ports, and labels is a sound
nonexistence certificate.  Enlarging domains by forgetting additive
correlations, replacing exact sums by interval/parity supersets, or allowing
extra port choices remains safe for `UNSAT => no completion`; `SAT` then
does not imply a tree lift.

## Unsound shortcuts to avoid

- `C_v` is the block of pairs **first connected** at that merge, equivalently
  pairs whose largest not-yet-exposed edge is `lambda_v`.  It is generally
  smaller than the final deletion-cut block of that edge.  Equating the two
  gives wrong counts.
- The future physical ranks and their holes are one shared set.  Independently
  choosing a convenient puncture set for each block is not an exact model.
- Rooted profiles used at different merges must come from actual ports in the
  same recursively constructed child metric.  Independently feasible
  marginals need not be jointly realizable.
- Set support is insufficient: a coefficient greater than one is already a
  repeated-distance contradiction.
- The forced value is the least missing **pair distance**, not the least
  unused edge label.
- A truncated lookahead must impose MEX after every explicitly constructed
  merge.  Later MEX identities follow automatically only from a full exact
  cover.
- Passing the relaxed Hall model proves only allocation feasibility.  Only
  the actual additive identity (EC), with coherent ports and metrics, gives a
  completion.
