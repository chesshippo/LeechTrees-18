# Formal validation status

## Verdict

**PASS — recorded kernel, source-integrity, and axiom validation for the
frozen snapshot.**

The archived validation covered 75 inputs: 70 library modules,
`LeechTrees.lean`, `FullClaimAxiomAudit.lean`, and three pinned project
configuration files. All 72 Lean sources compiled successfully into a fresh
local output tree, and all 350 expected axiom queries were recorded.

## Recorded results

- 72/72 Lean compiler exits were zero;
- 72 local `.olean` outputs were present in the final inventory;
- 350/350 ordered axiom rows matched the expected declaration order;
- 6 declarations reported no axioms;
- 344 rows reported `propext`, 342 reported `Classical.choice`, and 343
  reported `Quot.sound`, with overlapping counts; and
- no other axiom name appeared in the recorded results.

The source-integrity record covers all 72 Lean sources and reports zero
executable forbidden forms, equivalent proof escapes, or lexical errors under
its stated policy. This development is not advertised as constructive or
axiom-free.

## Public records

The exact publication inputs, compilation order, axiom contract and results,
generated-object inventory, and source-integrity receipt are linked from
[`../README.md`](../README.md). The complete formal result surface is 66
verified theorem families with 324 claim-bearing endpoints, indexed in
[`../../results/VALIDATED_FORMAL_CLAIM_MATRIX.tsv`](../../results/VALIDATED_FORMAL_CLAIM_MATRIX.tsv)
and [`../../results/CLAIM_ENDPOINTS.tsv`](../../results/CLAIM_ENDPOINTS.tsv).

## Reproduction and boundary

Run `python scripts/verify_snapshot.py` for a read-only replay of the public
hash and ledger contracts. Run `lake build` followed by
`lake env lean FullClaimAxiomAudit.lean` to reconstruct the kernel build and
axiom audit with the pinned toolchain.

These records validate the stated Lean snapshot. They do not prove novelty,
priority, search completeness, or the still-open original problem: no
qualifying construction for `n >= 18` and no universal obstruction is proved.
