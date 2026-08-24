# Indexed Hall and mex-conditioned self-puncturing

Let the current valid forest have components `K_1,...,K_m`, and let `H` be
the set of currently missing ranks.  For every unordered component pair
`i<j` and every indexed vertex pair `(x,y) in K_i x K_j`, define

\[
D_{ijxy}=\{d_i(x,u)+L+d_j(v,y)\},
\]

where the union is over all `u in K_i`, `v in K_j`, and `L>=1` for which the
entire block

\[
B(i,j,u,v,L)=
\{d_i(a,u)+L+d_j(v,b):(a,b)\in K_i\times K_j\}
\]

is injective and contained in `H`.

## Theorem 1: indexed Hall

If the prefix has a Leech-tree completion, the bipartite graph with left side
all indexed cross-component vertex pairs, right side `H`, and domains
`D_{ijxy}` has a perfect matching.

Indeed, in a completion the final path from `K_i` to `K_j` has actual first
and last ports `u,v` and a port-to-port length `L`.  Its whole cross block is
injective and contained in `H`, so each actual distance belongs to the
corresponding indexed domain.  All pair distances are distinct.  Finally,

\[
|H|=\sum_{i<j}|K_i||K_j|,
\]

so the induced injection is a perfect matching.  Therefore failure of this
matching is a sound pruning certificate.

This strictly refines the original capacitated Hall relaxation: the original
checker replaces every `D_{ijxy}` in one component-pair family by their
common union.  Every indexed matching induces a matching in that enlarged
model, while the converse need not hold.

There is a second cheap matching that is logically independent of indexed
Hall.  Give each component-pair family the domain of translations `L` of its
valid whole-block patterns.  A completion selects one translation per family,
and these translations are pair distances belonging to mutually disjoint
blocks, hence are globally distinct.  The translation domains must therefore
have a system of distinct representatives.  Conditioning on `B_1` deletes
translations coming from any pattern that intersects `B_1` and gives the
same necessary matching on the remaining families.

## Theorem 2: mex-conditioned indexed Hall

Let `mu=min(H)` be the forced next physical edge weight.  In every completion
there is a component pair `(i,j)` and ports `u,v` such that

\[
B_1=B(i,j,u,v,\mu)
\]

is the first chronological merge block.  After fixing this block:

1. its entire component-pair family is assigned by `B_1`;
2. every other chosen component-pair block is disjoint from `B_1`;
3. all remaining indexed pairs match bijectively to `H\setminus B_1`.

Consequently, enumerate every valid `mu`-translated block `B_1`.  For each
one, remove its family and ranks, delete all remaining candidate patterns
that meet `B_1`, rebuild the indexed domains, and run Hall.  If every branch
fails, the prefix has no completion.  This is precisely a one-block
self-puncturing disjunction; it is stronger than unconditional indexed Hall
but remains a relaxation because each surviving domain can mix values from
different port/length patterns.

## Cost and safe limits

At order 18 there are at most 153 indexed slots.  Unconditional indexed Hall
is one ordinary bipartite matching and is cheap enough to try at 7--8 current
components.  Conditioned Hall performs one matching per distinct block with
translation `mu`; there are at most the number of current cross-component
port pairs before block deduplication (153).  A production implementation
must treat a branch cap or work-budget exhaustion as `UNKNOWN/PASS`, never as
a rejection.

The isolated implementation is
`work/a2_solver/a2_multi_edge_stronger_relaxation.hpp`.  It does not modify
the production solver or the existing exact-cover header.

## Optional exact two-merge conditioning

The first conditioning step can be extended one chronological edge without
guessing a final topology.  Fix a full first pattern
`B_1=B(i,j,u,v,mu)` (including its ports), and put

\[
\mu_2=\min(H\setminus B_1).
\]

T2a forces the second physical edge to have weight `mu_2`.  There are only
two cases.

1. It joins two untouched components `K_k,K_l`; then its complete new block
   is one valid pattern `B(k,l,p,q,mu_2)`.
2. It joins `K_i union K_j` to an untouched `K_k`; choosing its endpoint in
   the already constructed weighted tree `K_i--K_j` and its endpoint in
   `K_k` computes the whole new block exactly.  This coherently fixes the two
   original families `(i,k)` and `(j,k)` at once.

In either case remove all newly fixed families and ranks, discard every
remaining pattern meeting either chronological block, and apply indexed and
translation Hall.  Every completion supplies one enumerated pair of merges,
so rejection after exhaustive failure is sound.  A branch cap or matching
budget must again return `UNKNOWN/PASS`.

This two-merge check is optional and off by default.  On the sampled A2 late
prefixes it was slightly stronger than one-block conditioning but generally
weaker than the full exact block-cover DP.  Its intended role is a cheap
prefilter before that much more expensive DP, not a replacement for it.
