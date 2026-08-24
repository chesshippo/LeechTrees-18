# Scope and nonclaims

This file is part of the mathematical statement of the repository. It records
what the formal results do **not** imply. When prose and Lean differ, the Lean
declaration and its hypotheses control.

## Central nonclaim

The original target remains open in this development. There is:

- no `n >= 18` Leech-tree witness;
- no proof that order 18 is impossible; and
- no proof of universal nonexistence for every `n >= 18`.

The claim matrix records this as `P0`, with status `OPEN` and zero theorem
endpoints.

## Status vocabulary

- `V / FORMALIZED_EXACT / VALIDATION_003_KERNEL_PASS` means the scoped family
  has named Lean endpoints in the accepted snapshot.
- `U / NOT_FORMALIZED / NO_KERNEL_CREDIT` means no mathematical credit is
  assigned here, even if historical calculations or prose exist.
- `OPEN / OUTSIDE_THEOREM_CREDIT` identifies the unresolved original target.

The matrix has 92 rows: 66 verified families, 25 unresolved or held families,
and the one open target. Only the 66 verified rows contribute to the 324
claim-bearing endpoints.

## Logical boundaries

### Parity and order 18

`T12b` excludes exactly two odd physical edges at order 18. It does not
exclude odd-edge counts 3 through 15. `C17` separately excludes 17. These
facts do not combine into an order-18 nonexistence theorem.

`G023` is a conditional implication bundle. Its `q66/q67` atoms require the
explicit hypotheses in the declarations. They do not establish an exhaustive
classification, a tree lift, a weight-67 exclusion, or a feasibility theorem.

### Quotient and gluing statements

`F9a`-`F9e`, `G005`, `G008`, and the few-odd reductions are forward statements
about data extracted from an actual Leech tree. Abstract data satisfying some
displayed equations need not arise from a tree. A converse is available only
where a declaration explicitly states one, and only in its stated model.

The formulas retain indexed fibres, actual ports, and multiplicities. They
must not be weakened to unindexed support or marginal-set equalities.

### Hall and shared-tail statements

`G012` uses the stated allowed-rank/abstract-slot model. Its Hall equivalence
and shared-tail conclusions do not by themselves construct compatible tree
paths, ports, or a global weighted-tree realization.

### Exactly-two-odd results

`G015` assumes the exactly-two-odd architecture and its stated rank/port
hypotheses. Its `q <= 10`, `q != 7`, and guarded `q <= 6` conclusions are not
global bounds for arbitrary odd-edge configurations.

`G016` rules out a common-middle-port family for `n >= 36`. It is not a
no-two-odd theorem for arbitrary ports or all orders.

### Three-odd and four-odd models

`G021` is scoped to the formal `OpenMultiport` model and the named optional
parent master. It does not certify a finite classification of all three-odd
trees.

`G022` proves the stated quotient relabelling and Gaussian scalar identity for
the actual four-odd setting. It does not prove that the scalar system is
feasible, exhaustive as a tree classification, or sufficient for a lift.

### Extension and lift obstructions

`D3a`-`D5c`, `G017`, and `G018` concern literal operations or named
architectures with their old weights, embeddings, ports, or block structure
preserved. They do not prohibit every possible reweighting, extension, or
block-lift construction.

### Barrier and counterexample families

`G019` proves scalar-certificate flexibility, not tree existence. `G024`
refutes particular converses and inference patterns; it does not refute the
correct forward theorems.

## Computational boundary

The 22 rows `C001`-`C022` are historical computational families with status
`U`, no Lean endpoints, and no kernel credit. Likewise, held rows `H1`-`H3`
are not promoted. A timeout, cap, partial enumeration, solver `UNKNOWN`, or
missing completeness proof is not a negative mathematical result.

No search transcript, solver campaign, or census is needed to use the 66
formal theorem families in this repository.

## External claims

This snapshot makes no claim of worldwide novelty, priority, or current open
status. Those are literature questions, not conclusions of the Lean kernel
or the included validation records.
