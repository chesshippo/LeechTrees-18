# Mathematical results

This directory is the reader-facing guide to the formal theorem surface. The
development studies finite trees whose edges have strictly positive integral
weights and whose unordered vertex-pair distances are exactly

```text
{1, 2, ..., binomial(n, 2)}.
```

The model is [`PosIntTree`](../LeechTrees/Foundations.lean), and the spectrum
condition is [`IsLeech`](../LeechTrees/Foundations.lean). The Lean sources are
authoritative. The prose below groups related declarations into 66 theorem
families; it does not turn a conditional or architecture-specific theorem
into a global result.

## Formal surface

| Item | Count | Authoritative index |
|---|---:|---|
| Accepted mathematical families | 66 | [`VALIDATED_FORMAL_CLAIM_MATRIX.tsv`](VALIDATED_FORMAL_CLAIM_MATRIX.tsv) |
| Claim-bearing Lean declarations | 324 | [`CLAIM_ENDPOINTS.tsv`](CLAIM_ENDPOINTS.tsv) |
| Axiom-audited declarations | 350 | [`FullClaimAxiomAudit.lean`](../FullClaimAxiomAudit.lean) |
| Local Lean sources | 72 | [`PRE_VALIDATION_INPUTS.tsv`](../evidence/validation/PRE_VALIDATION_INPUTS.tsv) |

The complete linkable catalogue is [`THEOREM_INDEX.md`](THEOREM_INDEX.md).
The extra 26 axiom queries are definitions and support declarations needed to
audit the formal interface around the 324 claim endpoints.

## 1. Spectrum, parity, and cuts

The foundational layer turns the permutation-of-distances hypothesis into
identities on the actual weighted tree.

- For order at least three, physical edge weights 1 and 2 occur. More
  generally, the forced-MEX theorem describes the initial segment of physical
  weights and the persistent merge block at its first gap (`T1`, `T2a`,
  `T2b`).
- Root parity satisfies an exact equation. At order 18 this determines the
  two parity-class sizes (`T3a`, `T3b`).
- Deleting an edge with component size `s` shows that exactly `s(n-s)`
  unordered paths cross it. Summing path lengths first over pairs and then
  over edges gives

  ```text
  sum_e s_e (n - s_e) w_e = N(N+1)/2,
  N = binomial(n,2).
  ```

  At order 18, the right-hand side is `11781` (`T4`).
- Each edge also has an indexed direct-sum description for the distances of
  paths crossing its cut (`T5`). The indexing and multiplicities are part of
  the theorem; it is not merely an equality of marginal value sets.

The baseline derivations are collected in
[`BASELINE_T_RESULTS.md`](../proofs/BASELINE_T_RESULTS.md).

## 2. Order-18 and parity-tail constraints

At order 18, the largest physical edge weight is at least 19 and every simple
path contains at most 14 edges (`T6`, `T7`). The parity-tail modules then give
signed path factorizations, noncollinear vanishing, moment identities through
degree three, and exact feasibility equations for the two parity classes
(`T8a0` through `T10b`).

The odd-edge consequences currently established are deliberately narrower
than a full exclusion:

- exactly one odd physical edge is impossible for every order at least 18
  (`T11`);
- for order at least five, exactly two odd physical edges force an even
  odd-target count (`T12a`);
- order 18 cannot have exactly two odd physical edges (`T12b`); and
- order 18 cannot have 17 odd physical edges (`C17`).

Thus the formalization does **not** exclude all remaining odd-edge counts at
order 18. The expanded rank-parity layer adds physical-rank puncturing, signed
cut moments, and a 52-endpoint conditional `q66/q67` bundle (`G002`, `G003`,
`G023`). The hypotheses of that conditional bundle are part of every use.

## 3. Paths, multicuts, allocation, and Hall conditions

The path/multicut layer keeps actual vertices, ports, ranks, and
multiplicities visible.

- `F1`, `F4`, and `G001` give first-edge splits and exact hole statistics,
  including the eight-row first-edge dossier.
- `G004` and `G005` give path-segment rank statistics and actual selected-edge
  quotient gluing identities.
- `G006`, `G007`, and `G011` give two-cut four-bin moments, subset-DP
  equivalence, hop-allocation rearrangements, and the signed second moment
  `-11781`.
- `G009` and `G010` record joint signed-flow and named three-port median
  identities.
- `G012` gives capacitated Hall equivalences and shared-tail consequences for
  the stated abstract-slot model.

These results are necessary structural descriptions. Unless the indexed
theorem explicitly states a converse, they are not realization criteria for
weighted trees.

## 4. Odd quotients and few-odd architectures

Deleting odd physical edges separates the original tree into even
components. Halving their internal weights and retaining the odd bridges
produces an actual quotient tree. The formalization preserves the pair index,
the route through quotient components, and distance multiplicity (`F9a`
through `F9e`). It also proves coefficientwise odd/even rank-polynomial and
two-port coordinate identities.

The expanded consequences include:

- capacity and diameter boundaries for actual quotient routes (`G008`);
- same-colour injections, companion caps, and equality/truncation statements
  (`G013`, `G014`);
- in the exactly-two-odd case with weights `1` and `2q+1`, the bounds
  `q <= 10` and `q != 7`; under the stated distinct-port rank guard,
  `q <= 6` (`G015`);
- no common-middle-port exactly-two-odd example for `n >= 36`, together with
  its stated parity-order families (`G016`);
- exact three-anchor coordinates and a scoped named-median reconstruction
  (`G020`);
- an `OpenMultiport` three-odd component/parent model (`G021`); and
- for an actual four-odd quotient, relabelling to the `P5`, fork, or star
  shapes and reduction of the scalar constraints to the explicit Gaussian
  target `18 + 2i` (`G022`).

The quotient formulas run forward from an actual Leech tree. They do not, by
themselves, show that abstract quotient data can be lifted back to one.

## 5. Extension and block-lift obstructions

The extension results rule out several literal operations while keeping the
old subtree and its weights fixed:

- normalized weighted paths and a full initial interval of physical weights
  at the stated orders (`D3a`, `D3b`);
- unchanged one-leaf attachment beyond the exact small-order boundary
  (`D4a0`, `D4a`, `D4a2`);
- literal weight-preserving subdivision and literal unscaled bridging of two
  nontrivial examples (`D4b`, `D4c`); and
- unchanged-subtree extensions in the specified size ranges (`D5a`, `D5b`,
  `D5c`).

`G017` supplies a block-lift gadget and a family of named obstruction and
reduction theorems. `G018` rules out the precise positive-integral odd
complete-rooted-star-block architecture for odd block size greater than one.
Neither result excludes every conceivable lift or extension architecture.

## 6. Barrier and correction results

Not every strong-looking necessary condition can close the problem.

- `G019` constructs scalar Gaussian certificates for every component count
  from 4 through 18. This proves that the scalar certificate alone cannot
  exclude those component counts; it does not realize a tree.
- `G024` formalizes counterexamples to three invalid inference patterns:
  reversing a below-`q2` implication, reconstructing gluing from marginal
  flow data, and determining a multicut from a histogram alone.

These correction witnesses are included because they mark exact logical
boundaries of the positive results.

## Reading order

1. Read [`SCOPE.md`](SCOPE.md) for nonclaims and conditional boundaries.
2. Use [`THEOREM_INDEX.md`](THEOREM_INDEX.md) to select a theorem family.
3. Follow its links to the exact Lean module and, where available, a
   human-readable derivation in [`proofs/`](../proofs/README.md).
4. Use [`CLAIM_ENDPOINTS.tsv`](CLAIM_ENDPOINTS.tsv) for the exact declaration
   name and source path.
5. Consult [`evidence/README.md`](../evidence/README.md) for the frozen build,
   source-integrity, and axiom records.

## Unresolved target

No theorem in this repository constructs a qualifying tree of order at least
18, excludes order 18, or proves universal nonexistence for all larger orders.
That original existence-or-nonexistence question remains the sole `OPEN` row
`P0` in the claim matrix.
