# LeechTrees

Lean-formalized structural results for classical positive-integral Leech
trees.

> **Status: validated formal partial progress; the target problem is not
> solved here.** This repository contains formal structural consequences,
> scoped obstructions, reductions, conditional implications, and explicit
> counterexamples. It contains no qualifying Leech-tree construction for
> `n >= 18`, no proof that order 18 is impossible, and no universal
> nonexistence theorem.

## The problem

Let `T = (V, E, w)` be a finite tree with a strictly positive integer weight
on every edge. For distinct vertices `u` and `v`, let `d_T(u,v)` be the sum
of the weights on their unique path. If `n = |V|` and
`N = binomial(n,2)`, then `T` is a classical positive-integral Leech tree
when the indexed unordered-pair distance map is a bijection onto

```text
1, 2, ..., N.
```

Equivalently, every target distance occurs exactly once. The formal model is
[`PosIntTree`](LeechTrees/Foundations.lean#L123), and the exact spectrum
condition is [`IsLeech`](LeechTrees/Foundations.lean#L275).

The motivating target is to construct such a tree for some `n >= 18`, or to
prove that none exists for every `n >= 18`. The results here narrow and
organize that problem without resolving it.

## What is proved

The accepted theorem ledger contains **66 mathematical families**:

- 42 baseline spectrum, parity, quotient, and extension families;
- 24 expanded families `G001`-`G024`;
- 324 claim-bearing Lean endpoints in total;
- 350 queried declarations after adding 26 model/support declarations.

The 66-family count is a grouping of related declarations, not a count of
independent discoveries. The complete family-level scope is in the
[`theorem index`](results/THEOREM_INDEX.md), and all 324 declarations are in
the machine-readable [`endpoint map`](results/CLAIM_ENDPOINTS.tsv).

Some representative results are:

- every Leech tree of order at least 3 has physical edge weights 1 and 2,
  followed by an exact forced-MEX description;
- the cut checksum
  `sum_e cutSize(e) * (n-cutSize(e)) * weight(e) = N*(N+1)/2`, with value
  `11781` at order 18;
- at order 18, the largest physical edge has weight at least 19 and every
  simple path has at most 14 edges;
- order 18 has neither exactly one nor exactly two odd physical edges, and
  its odd-edge count is not 17;
- deletion of the odd edges produces an actual quotient tree with indexed,
  multiplicity-preserving rank-polynomial decompositions;
- with exactly two odd physical edges of weights `1` and `2*q+1`, one has
  `q <= 10` and `q != 7`; disjoint physical ports strengthen this to
  `q <= 6` under the stated rank guard;
- no common-middle-port exactly-two-odd example exists for `n >= 36`;
- every selected edge has exact gluing-polynomial, multicut, allocation,
  capacitated Hall, and shared-tail formulas in their stated scopes;
- literal unchanged leaf attachment, literal weight-preserving subdivision,
  literal unscaled bridging, and several unchanged-subtree extensions are
  ruled out;
- the named odd complete-rooted-star-block architecture has no
  positive-integral lift for odd block size greater than 1;
- the three-odd and four-odd cases have exact scoped quotient reductions;
  the four-odd case yields the explicit Gaussian `K`-form target `18 + 2i`;
- scalar Gaussian constraints alone cannot exclude any component count from
  4 through 18; and
- three tempting converse/gluing/histogram inference patterns are refuted by
  explicit formal counterexamples.

For a mathematical tour with exact qualifications, see
[`results/README.md`](results/README.md). Human-readable derivations are
routed from [`proofs/README.md`](proofs/README.md). The Lean source and the
validated claim matrix control whenever informal prose is broader.

## Repository layout

```text
LeechTrees/                     Lean library (70 modules)
LeechTrees.lean                aggregate library root
FullClaimAxiomAudit.lean       350 ordered #print axioms queries
results/
  README.md                    mathematical overview
  THEOREM_INDEX.md             all 66 accepted theorem families
  CLAIM_ENDPOINTS.tsv          all 324 claim-bearing declarations
  SCOPE.md                     exact nonclaims and conditional boundaries
proofs/                        human-readable mathematical derivations
evidence/
  validation/                  compact build, source, and axiom records
scripts/verify_snapshot.py     portable hash/ledger consistency check
```

The Lean source tree and its three configuration files are byte-for-byte
copies of the accepted snapshot. Generated `.olean` files, dependency caches,
process logs, research transcripts, solver campaigns, and superseded candidate
sources are intentionally absent.

## Build

The project pins Lean `v4.24.0` and Mathlib `v4.24.0` (resolved Mathlib commit
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`). From the repository root:

```sh
lake build
lake env lean FullClaimAxiomAudit.lean
```

The second command is separate because the axiom driver is not a Lake target.
A cold clone may need network access to fetch the pinned dependencies under
`.lake/`. Do not run `lake update` when reproducing this snapshot: it may
change the frozen dependency resolution.

The archived release validation used a stricter dependency-ordered direct
Lean build from a zero-output tree. Its authoritative order is
[`evidence/validation/MODULE_ORDER.tsv`](evidence/validation/MODULE_ORDER.tsv),
not the textual import order of `LeechTrees.lean`.

To recheck the copied source hashes and the publication ledgers without
building Lean:

```sh
python scripts/verify_snapshot.py
```

## Validation and trust boundary

Lean 4.24.0 accepted all 72 local sources from a fresh local output tree over
the pinned existing dependency `.olean` files:

- 70 library modules, the aggregate root, and the audit driver;
- 72/72 native compiler exits equal to zero;
- 72 final local `.olean` files;
- empty stdout/stderr for all 71 ordinary compilation children;
- 350/350 ordered axiom reports parsed successfully;
- no reported axiom outside `propext`, `Classical.choice`, and `Quot.sound`.

Six queried declarations were axiom-free; 344 reported `propext`, 342
reported `Classical.choice`, and 343 reported `Quot.sound`. These counts
overlap. This is not an axiom-free or constructive development.

A comment-aware source scan found no executable `sorry`, `sorryAx`, `admit`,
custom `axiom`, `unsafe`, `native_decide`, `opaque`, `extern`,
`implemented_by`, `partial def`, or enumerated proof escape. Ordinary kernel
`decide` and `noncomputable` declarations occur and are not proof holes.

The retained records bind the accepted source bytes, module order, generated
object inventory, and axiom results. The repository-local verifier replays
those publication ledgers, while a fresh `lake build` and axiom-driver run
reconstruct the kernel check. See [`evidence/README.md`](evidence/README.md)
for the exact records and the limits of what they establish.

## Scope and nonclaims

The exact boundaries are part of the results. In particular:

- excluding exactly two odd edges at order 18 does not exclude order 18;
- quotient, port, and polynomial results are forward representations unless
  an explicit scoped converse is stated;
- Hall/shared-tail conclusions use the specified abstract-slot model;
- the scalar Gaussian certificates do not construct a tree;
- the `OpenMultiport` and four-odd results do not certify a finite
  classification or feasibility result;
- the conditional `q66/q67` atoms do not establish a tree lift, exhaustive
  exclusion, or nonexistence theorem.

Twenty-two historical computational families remain unverified and receive
no theorem or kernel credit here. Timeouts, capped searches, solver `UNKNOWN`,
partial unions, and census counts are not promoted as mathematical results.
Read [`results/SCOPE.md`](results/SCOPE.md) before quoting a theorem.

No claim of current worldwide open status, novelty, or priority is made: a
current literature review was outside the validated snapshot.

## Citation and licensing

[`CITATION.cff`](CITATION.cff) supplies repository-level citation metadata
using the public collective author label “LeechTrees formalization
contributors.” The frozen Lake package is named `LeechTreesPartial` and has
package version `0.1.0`; repository publication versions are tracked
separately.

No project-wide reuse license is provided for this repository. Except for
rights supplied by applicable law, applicable third-party terms, or GitHub's
Terms of Service, publication here does not grant permission to use, copy,
modify, or redistribute the repository contents. Rights remain with their
respective holders.

Pull requests are not currently accepted. [`CONTRIBUTING.md`](CONTRIBUTING.md)
records the technical requirements for any future contribution process.
