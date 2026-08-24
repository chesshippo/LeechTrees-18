# Validation evidence

This directory contains a compact publication subset of the validation
records for the exact Lean snapshot in this repository. It is evidence about
the formal source and recorded kernel results, not a substitute for reading
the theorem hypotheses and not an external mathematical peer review.

## Retained records

- [`PRE_VALIDATION_INPUTS.tsv`](validation/PRE_VALIDATION_INPUTS.tsv) binds
  all 75 source and configuration inputs to byte counts and SHA-256 hashes.
- [`MODULE_ORDER.tsv`](validation/MODULE_ORDER.tsv) records the validated
  72-source dependency order.
- [`EXPECTED_AXIOM_QUERIES.tsv`](validation/EXPECTED_AXIOM_QUERIES.tsv) is
  the ordered 350-declaration axiom-audit contract.
- [`AXIOM_RESULTS.tsv`](validation/AXIOM_RESULTS.tsv) records the corresponding
  axiom sets.
- [`FINAL_OLEAN_INVENTORY.tsv`](validation/FINAL_OLEAN_INVENTORY.tsv) records
  the generated local object inventory from the archived validation.
- [`CURRENT_LEAN_SOURCE_INTEGRITY_AUDIT.json`](validation/CURRENT_LEAN_SOURCE_INTEGRITY_AUDIT.json)
  records the source-integrity scan.
- [`FINAL_VALIDATION_STATUS.md`](validation/FINAL_VALIDATION_STATUS.md)
  summarizes the public validation status and trust boundary.

Generated `.olean` files, dependency caches, compiler logs, process records,
research transcripts, and internal review workflow are intentionally absent.

## Reproduction

The repository-local verifier rehashes the 75 inputs, checks the module and
axiom ledgers, verifies the allowed axiom distribution, and reconciles the
66-family and 324-endpoint result indices:

```sh
python scripts/verify_snapshot.py
```

It is read-only and does not invoke Lean. To reconstruct the kernel build and
axiom queries with the pinned Lean and Mathlib versions, run:

```sh
lake build
lake env lean FullClaimAxiomAudit.lean
```

## Trust boundary

The records establish that the listed source compiled in the recorded
environment and that the queried declarations reported only `propext`,
`Classical.choice`, and `Quot.sound`. They do not establish novelty,
literature priority, computational-search completeness, or a solution to the
original existence-or-nonexistence problem.
