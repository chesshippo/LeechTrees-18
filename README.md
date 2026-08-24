# Nonexistence of an order-18 Leech tree

**Author: Maseeh Ghodsi**

The order-18 nonexistence result and computer-assisted proof presented in this
repository were obtained by Maseeh Ghodsi.

This repository contains a computer-assisted proof of the following result:

> There is no finite simple tree on 18 vertices, with a strictly positive
> integer weight on every edge, whose 153 unordered vertex-pair distances are
> exactly `1, 2, ..., 153`.

Such a weighted tree is called a positive-integral Leech tree of order 18.

## Proof structure

The proof is hybrid: part is checked by Lean and part is an exhaustive finite
search.

1. The Lean development defines positive-integral Leech trees and proves that
   every hypothetical order-18 example belongs to one of eight first-edge
   configurations.
2. The C++ search enumerates the possible extensions of each configuration,
   using necessary distance, parity, path-length, and exact-cover conditions.
3. The preserved certificates and their verifiers establish exhaustive
   `ZERO` results for all eight configurations.
4. The Lean theorem
   `Leech18EndToEnd.no_order18_leech_of_all_rows` proves that exclusion of the
   eight configurations implies nonexistence.

The decisive formal reduction is
`LeechTrees.Foundation.FirstEdgeDossier.firstEdge_eightRowDossier`. The exact
formal/computational boundary is in
[`proof/HybridEndToEndBoundary.lean`](proof/HybridEndToEndBoundary.lean), and
the complete mathematical and computational argument is in
[`proof/PROOF_LEDGER.md`](proof/PROOF_LEDGER.md).

This is not a proof in which Lean evaluates the entire search. The search
implementation, canonicalization, pruning logic, row-to-search correspondence,
compiler, and host runtime remain in the trusted computational base. The
verifiers fail on missing branches, malformed results, unexpected hashes,
timeouts, nonzero exits, and any result other than the required complete
coverage.

## Result summary

| Configuration | Reported search-node visits |
|---:|---:|
| 1 | 1,321,606,123 |
| 2 | 193,281,350 |
| 3 | 167,742,832 |
| 4 | 225,016,655 |
| 5 | 4,242,081,806 |
| 6 | 1,165,724,514 |
| 7 | 1,010,043,681 |
| 8 | 239,702,053 |
| **Total** | **8,565,199,014** |

These are recursive search-node visits, not distinct trees.

## Verify the preserved evidence

The complete preserved-evidence replay rebuilds the Lean boundary and search
runtime, checks all source and certificate identities, and rereads all 39,000
terminal-search receipts. After installing the full evidence asset as
described in [`REPRODUCE.md`](REPRODUCE.md), run:

```powershell
python.exe -B .\scripts\materialize_lean_git.py

Push-Location .\lean\LeechTrees
lake build
Pop-Location

powershell.exe -NoProfile -ExecutionPolicy Bypass `
  -File .\proof\verify_end_to_end.ps1 `
  -Cxx C:\path\to\g++.exe `
  -PythonExecutable C:\path\to\python.exe
```

Success requires exit code zero and the exact final marker:

```text
LEECH18_HYBRID_END_TO_END_PASS configurations=8 reported_node_visits=8565199014 global_status=GLOBAL_ZERO_COMPLETE
```

That command verifies the preserved computation. A fresh execution of the
complete search is much more expensive and is documented separately in
[`REPRODUCE.md`](REPRODUCE.md).

## Repository contents

- `proof/`: proof ledger, Lean boundary, machine-readable proof record, and
  the end-to-end verifier.
- `lean/LeechTrees/`: the pinned Lean 4.24.0 development.
- `computation/evidence/production/`: compact plans, sources, certificates,
  and configuration results.
- `computation/verifiers/global/`: the relocated global evidence verifier.
- `scripts/`: source-build, recomputation, assembly, and integrity tools.
- `reproducibility/`: pinned environment information and platform preflights.

## Licensing

Project-authored Lean, C++, Python, scripts, and verification software are
licensed under Apache License 2.0. Project-authored computational evidence,
data, certificates, documentation, and figures are licensed under Creative
Commons Attribution 4.0. See [`LICENSE`](LICENSE), [`LICENSES/`](LICENSES/),
and [`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md).
