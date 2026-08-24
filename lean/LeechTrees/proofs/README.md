# Proof guide

The primary proofs are the Lean declarations indexed in
[`results/THEOREM_INDEX.md`](../results/THEOREM_INDEX.md). This directory adds
human-readable mathematical derivations for readers who want the algebra and
combinatorics outside tactic syntax.

The notes are supplementary: theorem names, hypotheses, and exact scope are
controlled by the Lean source and the
[`validated claim matrix`](../results/VALIDATED_FORMAL_CLAIM_MATRIX.tsv).
The public notes retain mathematical derivations and scope boundaries.

## Baseline derivations

- [`BASELINE_T_RESULTS.md`](BASELINE_T_RESULTS.md): foundational spectrum,
  parity, cut, order-18, and parity-tail results `T1`-`T12b`.
- [`BASELINE_FD_RESULTS.md`](BASELINE_FD_RESULTS.md): first-edge, hole,
  odd-quotient, and extension results `F1`, `F4`, `F9a`-`F9e`, and
  `D3a`-`D5c`.

## Expanded derivations

| Families | Subject | Notes |
|---|---|---|
| `G001` | Eight-row first-edge dossier | [`FULL_PROOF.md`](G001_FirstEdgeDossier/FULL_PROOF.md) |
| `G002`-`G010`, `G024a-b` | Rank puncturing, cut flow, quotient capacity, allocation, and median coordinates | [`FULL_PROOFS.md`](G002_G010_G024ab_RankParityCoordinates/FULL_PROOFS.md) |
| `G011`, `G012`, `G024c` | Parity multicuts, Hall conditions, shared tails, and histogram counterexample | [`FULL_PROOFS.md`](G011_G012_G024c_Multicut/FULL_PROOFS.md) |
| `G013`, `G014` | Same-colour injection, companion caps, and truncation | [`FULL_PROOF.md`](G013_G014_Q2Bounds/FULL_PROOF.md) |
| `G015` | Sharp exactly-two-odd support-factor bounds | [`FULL_PROOF.md`](G015_TwoOddSharpBounds/FULL_PROOF.md) |
| `G016` | Common-port global obstruction and factor argument | [`FULL_PROOF.md`](G016_TwoOddGlobal/FULL_PROOF.md), [`FACTOR_OBSTRUCTION_PROOF.md`](G016_TwoOddGlobal/FACTOR_OBSTRUCTION_PROOF.md) |
| `G017` | Block-lift identities and obstructions | [`FULL_PROOFS.md`](G017_BlockLifts/FULL_PROOFS.md) |
| `G018` | Odd complete-rooted-star-block obstruction | [`FULL_PROOF.md`](G018_OddCompleteBlocks/FULL_PROOF.md) |
| `G019` | Gaussian scalar flexibility | [`FULL_PROOF.md`](G019_GaussianFlexibility/FULL_PROOF.md) |
| `G020` | Three-port coordinates | [formal proof](../LeechTrees/Expanded/MultiportTail/ThreePortCoordinates.lean) |
| `G021` | Three-odd component and parent models | [formal component model](../LeechTrees/Expanded/MultiportTail/ThreeOddMasterCover.lean), [formal actual-tree adapter](../LeechTrees/Expanded/MultiportTail/ActualThreeOddCover.lean) |
| `G022` | Four-odd Gaussian identity and domain | [`FULL_IDENTITY_AND_DOMAIN_PROOF.md`](G022_FourOddGaussian/FULL_IDENTITY_AND_DOMAIN_PROOF.md) |
| `G023` | Conditional parity-tail atoms | [`FULL_CONDITIONAL_DERIVATION.md`](G023_ParityTailConditional/FULL_CONDITIONAL_DERIVATION.md), [`SCOPE.md`](G023_ParityTailConditional/SCOPE.md) |

## How to cite a proof

For a precise citation, give all three of:

1. the family identifier from the theorem index;
2. the fully qualified Lean declaration from
   [`CLAIM_ENDPOINTS.tsv`](../results/CLAIM_ENDPOINTS.tsv); and
3. the repository release or commit.

For conditional or model-specific results, include the boundary column from
the claim matrix. The human note alone is not a substitute for the formal
hypotheses.
