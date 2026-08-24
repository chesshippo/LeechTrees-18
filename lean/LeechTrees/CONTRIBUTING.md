# Contributing

> **Contribution status:** Pull requests are not currently accepted. No
> project-wide reuse license or contribution terms have been published. This
> file records technical requirements for a future contribution process.

If contribution intake opens, submissions must preserve the distinction
between formal partial results and the unresolved target problem.

## Development environment

Use the pinned files already in the repository:

- Lean `v4.24.0` from `lean-toolchain`;
- Mathlib `v4.24.0`, resolved by `lake-manifest.json`;
- the existing `lakefile.toml` without dependency updates.

Run:

```sh
lake build
lake env lean FullClaimAxiomAudit.lean
python scripts/verify_snapshot.py
```

Do not run `lake update` as part of a reproduction or unrelated pull request.

## Proof requirements

A result-facing change should:

1. state every mathematical hypothesis explicitly;
2. distinguish actual weighted-tree data from abstract or scalar models;
3. avoid promoting a timeout, partial search, `UNKNOWN`, or census count;
4. contain no `sorry`, `admit`, custom axiom, `native_decide`, or proof escape;
5. add the final declaration to the aggregate root and axiom audit;
6. update the family matrix, endpoint map, theorem index, and scope text; and
7. receive a fresh clean validation before any old validation badge or receipt
   is attached to the changed source bytes.

Ordinary kernel `decide` may be appropriate for finite propositions, but its
use should remain small, transparent, and accepted by the pinned kernel.

## Documentation requirements

Use the exact scope of the Lean declaration. Avoid language suggesting that a
necessary condition is sufficient, a scoped architecture is general, or the
original existence problem has been settled. Human proof notes are secondary
to the current Lean statement and `results/VALIDATED_FORMAL_CLAIM_MATRIX.tsv`.

## Requirements for future pull requests

Please include:

- a short mathematical statement of the change;
- the relevant declaration names and source files;
- successful output from the three commands above;
- any new reported axioms; and
- an explanation of whether the change modifies a validated source byte.

Changing validated source bytes invalidates byte-specific historical receipts
for the new revision, even when the mathematical change appears cosmetic.
