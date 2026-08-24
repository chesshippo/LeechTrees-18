# Theorem index

This is the reader-facing index for the 66 accepted theorem families. The
[claim matrix](VALIDATED_FORMAL_CLAIM_MATRIX.tsv) is the authoritative status
and scope ledger; [CLAIM_ENDPOINTS.tsv](CLAIM_ENDPOINTS.tsv) lists all 324
claim-bearing Lean declarations. Counts in the endpoint column are interface
endpoints, not separate mathematical discoveries.

Every row below has validity V, formalization status FORMALIZED_EXACT, and
validation status VALIDATION_003_KERNEL_PASS in the authoritative matrix.

## Core spectrum, parity, and cut identities

| Family | Result | Endpoints | Lean source | Human proof | Exact boundary |
|---|---|---:|---|---|---|
| `T1` | Physical weights 1 and 2 for n at least 3 | 1 | [`LeechTrees/Foundations.lean`](../LeechTrees/Foundations.lean) | [baseline T proofs](../proofs/BASELINE_T_RESULTS.md) | No finite-search conclusion |
| `T2a` | Forced-MEX initial segment | 1 | [`LeechTrees/Foundations.lean`](../LeechTrees/Foundations.lean) | [baseline T proofs](../proofs/BASELINE_T_RESULTS.md) | Actual smaller-weight prefix |
| `T2b` | Persistent actual-port merge block | 1 | [`LeechTrees/Foundations.lean`](../LeechTrees/Foundations.lean) | [baseline T proofs](../proofs/BASELINE_T_RESULTS.md) | No search-completeness claim |
| `T3a` | General root-parity equation | 1 | [`LeechTrees/PaperAlignment.lean`](../LeechTrees/PaperAlignment.lean) | [baseline T proofs](../proofs/BASELINE_T_RESULTS.md) | Necessary equation only |
| `T3b` | Taylor order condition and order-18 parity-class sizes | 2 | [`LeechTrees/Foundations.lean`](../LeechTrees/Foundations.lean) | [baseline T proofs](../proofs/BASELINE_T_RESULTS.md) | Necessary condition only |
| `T4` | Cut checksum and order-18 value 11781 | 2 | [`LeechTrees/Foundations.lean`](../LeechTrees/Foundations.lean) | [baseline T proofs](../proofs/BASELINE_T_RESULTS.md) | Actual deletion cuts and indexed paths |
| `T5` | Every-edge indexed direct-sum criterion | 1 | [`LeechTrees/Foundations.lean`](../LeechTrees/Foundations.lean) | [baseline T proofs](../proofs/BASELINE_T_RESULTS.md) | Not an unindexed marginal-set claim |

## Order-18 and parity-tail constraints

| Family | Result | Endpoints | Lean source | Human proof | Exact boundary |
|---|---|---:|---|---|---|
| `T6` | Order-18 largest physical edge at least 19 | 1 | [`LeechTrees/QHop/Claims.lean`](../LeechTrees/QHop/Claims.lean) | [baseline T proofs](../proofs/BASELINE_T_RESULTS.md) | No finite Q-band exclusion |
| `T7` | Order-18 simple paths have at most 14 edges | 1 | [`LeechTrees/QHop/Adapter.lean`](../LeechTrees/QHop/Adapter.lean) | [baseline T proofs](../proofs/BASELINE_T_RESULTS.md) | Graph-level path bound |
| `T8a0` | General collinear signed-path outer factorization | 1 | [`LeechTrees/ParityTailCollinear.lean`](../LeechTrees/ParityTailCollinear.lean) | [baseline T proofs](../proofs/BASELINE_T_RESULTS.md) | Nonempty selected edges and path support |
| `T8a1` | General noncollinear path coefficients vanish | 1 | [`LeechTrees/ParityTailGraphAdapter.lean`](../LeechTrees/ParityTailGraphAdapter.lean) | [baseline T proofs](../proofs/BASELINE_T_RESULTS.md) | Exact no-common-path premise |
| `T8a` | Collinear extreme-component factorization | 1 | [`LeechTrees/ParityTailExactBundle.lean`](../LeechTrees/ParityTailExactBundle.lean) | [baseline T proofs](../proofs/BASELINE_T_RESULTS.md) | Indexed support retained |
| `T8b` | Actual parity counts and C_F K_F identities | 1 | [`LeechTrees/ParityTailExactBundle.lean`](../LeechTrees/ParityTailExactBundle.lean) | [baseline T proofs](../proofs/BASELINE_T_RESULTS.md) | No value-image substitution |
| `T8c` | Raw singleton-pair triple coefficients and noncollinear zero | 2 | [`LeechTrees/ParityTailExactBundle.lean`](../LeechTrees/ParityTailExactBundle.lean) | [baseline T proofs](../proofs/BASELINE_T_RESULTS.md) | Finset duplicate collapse explicit |
| `T8d` | Parity-resolved path moments for residue p | 1 | [`LeechTrees/ParityTailGraphAdapter.lean`](../LeechTrees/ParityTailGraphAdapter.lean) | [baseline T proofs](../proofs/BASELINE_T_RESULTS.md) | Degrees 1 through 3 |
| `T8e` | Order-18 counts and degree-1 through degree-3 moment table | 2 | [`LeechTrees/PaperAlignment.lean`](../LeechTrees/PaperAlignment.lean)<br>[`LeechTrees/ParityTailGraphAdapter.lean`](../LeechTrees/ParityTailGraphAdapter.lean) | [baseline T proofs](../proofs/BASELINE_T_RESULTS.md) | Counts 76 and 77 |
| `T8f` | Order-18 joined counts and side feasibility | 1 | [`LeechTrees/ParityTailExactBundle.lean`](../LeechTrees/ParityTailExactBundle.lean) | [baseline T proofs](../proofs/BASELINE_T_RESULTS.md) | No existence conclusion |
| `T9a` | Literal parity-tail spacing and upper-tail inequalities | 1 | [`LeechTrees/ParityTailGraphAdapter.lean`](../LeechTrees/ParityTailGraphAdapter.lean) | [baseline T proofs](../proofs/BASELINE_T_RESULTS.md) | Requires p less than 2 and nonempty block |
| `T9b` | Equal-cardinality saturation of value Finsets | 1 | [`LeechTrees/ParityTailGraphAdapter.lean`](../LeechTrees/ParityTailGraphAdapter.lean) | [baseline T proofs](../proofs/BASELINE_T_RESULTS.md) | Value equality only |
| `T10` | Conditional order-18 weight-67 cut implication | 1 | [`LeechTrees/ParityTailGraphAdapter.lean`](../LeechTrees/ParityTailGraphAdapter.lean) | [baseline T proofs](../proofs/BASELINE_T_RESULTS.md) | Actual weight 67 and cut size 9 |
| `T10b` | Conditional order-18 weight-68 residual implication | 1 | [`LeechTrees/ParityTailGraphAdapter.lean`](../LeechTrees/ParityTailGraphAdapter.lean) | [baseline T proofs](../proofs/BASELINE_T_RESULTS.md) | Cut size 9 and normalized mass -1 or 5 |
| `T11` | No exactly one odd physical edge for n at least 18 | 1 | [`LeechTrees/OddEdgesT11Adapter.lean`](../LeechTrees/OddEdgesT11Adapter.lean) | [baseline T proofs](../proofs/BASELINE_T_RESULTS.md) | No assumed decomposition certificate |
| `T12a` | For n at least 5 two odd physical edges force even odd-target count | 1 | [`LeechTrees/OddEdgesT12Adapter.lean`](../LeechTrees/OddEdgesT12Adapter.lean) | [baseline T proofs](../proofs/BASELINE_T_RESULTS.md) | Parity conclusion only |
| `T12b` | Order 18 excludes exactly two odd physical edges | 1 | [`LeechTrees/PaperAlignment.lean`](../LeechTrees/PaperAlignment.lean) | [baseline T proofs](../proofs/BASELINE_T_RESULTS.md) | Does not exclude counts 3 through 15 |
| `C17` | Order-18 odd physical-edge count is not 17 | 1 | [`LeechTrees/OddEdgesGraphAdapter.lean`](../LeechTrees/OddEdgesGraphAdapter.lean) | [baseline T proofs](../proofs/BASELINE_T_RESULTS.md) | Auxiliary finite-band input |
| `G002` | Sorted physical-rank puncturing and equality/parity refinements | 7 | [`LeechTrees/Expanded/RankParity/PhysicalRankPuncturing.lean`](../LeechTrees/Expanded/RankParity/PhysicalRankPuncturing.lean) | [proofs](../proofs/G002_G010_G024ab_RankParityCoordinates/FULL_PROOFS.md) | Necessary structure |
| `G003` | Signed cut moments and order-18 imbalance consequence | 5 | [`LeechTrees/Expanded/RankParity/PhysicalRankPuncturing.lean`](../LeechTrees/Expanded/RankParity/PhysicalRankPuncturing.lean) | [proofs](../proofs/G002_G010_G024ab_RankParityCoordinates/FULL_PROOFS.md) | Necessary structure |
| `G023` | Conditional q67/q66 atoms A through H with corrected ranges | 52 | [`LeechTrees/Expanded/MultiportTail/ParityTailConditionalAtoms.lean`](../LeechTrees/Expanded/MultiportTail/ParityTailConditionalAtoms.lean)<br>[`LeechTrees/Expanded/MultiportTail/ParityTailPhysicalAdapters.lean`](../LeechTrees/Expanded/MultiportTail/ParityTailPhysicalAdapters.lean) | [scope](../proofs/G023_ParityTailConditional/SCOPE.md)<br>[derivation](../proofs/G023_ParityTailConditional/FULL_CONDITIONAL_DERIVATION.md) | Conditional atoms only |

## Edge, path, multicut, allocation, and Hall structure

| Family | Result | Endpoints | Lean source | Human proof | Exact boundary |
|---|---|---:|---|---|---|
| `F1` | Safe adjacent/disjoint first-edge split | 1 | [`LeechTrees/FirstEdge.lean`](../LeechTrees/FirstEdge.lean) | [baseline F/D proofs](../proofs/BASELINE_FD_RESULTS.md) | Not the full eight-row dossier |
| `F4` | Every-edge hole cardinality spectra and moments through degree 3 | 1 | [`LeechTrees/EdgeHole.lean`](../LeechTrees/EdgeHole.lean) | [baseline F/D proofs](../proofs/BASELINE_FD_RESULTS.md) | No realization converse |
| `G001` | Full eight-row first-edge dossier and order-18 cut corollaries | 10 | [`LeechTrees/Expanded/FirstEdge/FirstEdgeDossier.lean`](../LeechTrees/Expanded/FirstEdge/FirstEdgeDossier.lean) | [proof](../proofs/G001_FirstEdgeDossier/FULL_PROOF.md) | Local prefix theorem; not global exclusion |
| `G004` | Actual path-segment rank statistics and variance equality | 8 | [`LeechTrees/Expanded/PathMulticut/ActualPathSegmentStatistics.lean`](../LeechTrees/Expanded/PathMulticut/ActualPathSegmentStatistics.lean) | [proofs](../proofs/G002_G010_G024ab_RankParityCoordinates/FULL_PROOFS.md) | Actual contiguous paths |
| `G005` | Actual selected-edge quotient gluing decomposition | 6 | [`LeechTrees/Expanded/PathMulticut/ActualSelectedEdgeDecomposition.lean`](../LeechTrees/Expanded/PathMulticut/ActualSelectedEdgeDecomposition.lean) | [proofs](../proofs/G002_G010_G024ab_RankParityCoordinates/FULL_PROOFS.md) | Actual ports and indexed ranks |
| `G006` | Exact two-cut four-bin moments and subset-DP equivalence | 15 | [`LeechTrees/Expanded/PathMulticut/MulticutHall.lean`](../LeechTrees/Expanded/PathMulticut/MulticutHall.lean) | [proofs](../proofs/G002_G010_G024ab_RankParityCoordinates/FULL_PROOFS.md) | Finite equivalence internal to theorem |
| `G007` | Hop allocation double count rearrangement and parity partition | 13 | [`LeechTrees/Expanded/PathMulticut/RankAllocation.lean`](../LeechTrees/Expanded/PathMulticut/RankAllocation.lean)<br>[`LeechTrees/Expanded/PathMulticut/GraphHopAllocation.lean`](../LeechTrees/Expanded/PathMulticut/GraphHopAllocation.lean) | [proofs](../proofs/G002_G010_G024ab_RankParityCoordinates/FULL_PROOFS.md) | Necessary structure |
| `G009` | Joint signed-cut-flow iff and total -4 specialization | 2 | [`LeechTrees/Expanded/RankParity/SignedCutFlow.lean`](../LeechTrees/Expanded/RankParity/SignedCutFlow.lean) | [proofs](../proofs/G002_G010_G024ab_RankParityCoordinates/FULL_PROOFS.md) | Actual rooted data |
| `G010` | Exact named three-port median guard | 5 | [`LeechTrees/Expanded/RankParity/ThreePortMedian.lean`](../LeechTrees/Expanded/RankParity/ThreePortMedian.lean) | [proofs](../proofs/G002_G010_G024ab_RankParityCoordinates/FULL_PROOFS.md) | Named median only |
| `G011` | Parity multicut rearrangement and signed second moment -11781 | 9 | [`LeechTrees/Expanded/PathMulticut/ParityMulticut.lean`](../LeechTrees/Expanded/PathMulticut/ParityMulticut.lean) | [proofs](../proofs/G011_G012_G024c_Multicut/FULL_PROOFS.md) | Necessary structure |
| `G012` | Allowed-rank sets capacitated Hall iff and shared tails | 32 | [`LeechTrees/Expanded/PathMulticut/SelectedBlockHall.lean`](../LeechTrees/Expanded/PathMulticut/SelectedBlockHall.lean)<br>[`LeechTrees/Expanded/PathMulticut/OddSharedTailHall.lean`](../LeechTrees/Expanded/PathMulticut/OddSharedTailHall.lean) | [proofs](../proofs/G011_G012_G024c_Multicut/FULL_PROOFS.md) | Abstract-slot Hall scope |

## Odd quotient and few-odd architecture

| Family | Result | Endpoints | Lean source | Human proof | Exact boundary |
|---|---|---:|---|---|---|
| `F9a` | Even-component halving indexed odd bridges and quotient tree | 4 | [`LeechTrees/OddQuotient/Components.lean`](../LeechTrees/OddQuotient/Components.lean)<br>[`LeechTrees/OddQuotient/QuotientRoutes.lean`](../LeechTrees/OddQuotient/QuotientRoutes.lean) | [baseline F/D proofs](../proofs/BASELINE_FD_RESULTS.md) | Forward construction only |
| `F9b` | Canonical quotient route with actual ports and half-rank formulas | 3 | [`LeechTrees/OddQuotient/QuotientRoutes.lean`](../LeechTrees/OddQuotient/QuotientRoutes.lean) | [baseline F/D proofs](../proofs/BASELINE_FD_RESULTS.md) | No marginal-support replacement |
| `F9c` | Indexed pair partition and polynomial decomposition | 6 | [`LeechTrees/OddQuotient/PairPartition.lean`](../LeechTrees/OddQuotient/PairPartition.lean)<br>[`LeechTrees/OddQuotient/RankPolynomial.lean`](../LeechTrees/OddQuotient/RankPolynomial.lean)<br>[`LeechTrees/OddQuotient/QuotientPolynomials.lean`](../LeechTrees/OddQuotient/QuotientPolynomials.lean)<br>[`LeechTrees/OddQuotient/F9Endpoints.lean`](../LeechTrees/OddQuotient/F9Endpoints.lean) | [baseline F/D proofs](../proofs/BASELINE_FD_RESULTS.md) | Exact indexed fibres |
| `F9d` | Coefficientwise odd/even quotient identities | 1 | [`LeechTrees/OddQuotient/F9Endpoints.lean`](../LeechTrees/OddQuotient/F9Endpoints.lean) | [baseline F/D proofs](../proofs/BASELINE_FD_RESULTS.md) | No realization criterion |
| `F9e` | Forward two-port coordinate identities | 2 | [`LeechTrees/OddQuotient/TwoPortCoordinates.lean`](../LeechTrees/OddQuotient/TwoPortCoordinates.lean) | [baseline F/D proofs](../proofs/BASELINE_FD_RESULTS.md) | Repeated ports allowed; no converse |
| `G008` | Odd-quotient capacity diameter-12 boundary and signed merges | 8 | [`LeechTrees/Expanded/RankParity/OddQuotientCapacityConsequences.lean`](../LeechTrees/Expanded/RankParity/OddQuotientCapacityConsequences.lean) | [proofs](../proofs/G002_G010_G024ab_RankParityCoordinates/FULL_PROOFS.md) | Actual quotient routes |
| `G013` | Same-color injection above q2 and sharp G cap | 5 | [`LeechTrees/Expanded/Q2Bounds/Q2Bounds.lean`](../LeechTrees/Expanded/Q2Bounds/Q2Bounds.lean)<br>[`LeechTrees/Expanded/Q2Bounds/Q2GraphProfiles.lean`](../LeechTrees/Expanded/Q2Bounds/Q2GraphProfiles.lean) | [proof](../proofs/G013_G014_Q2Bounds/FULL_PROOF.md) | Necessary quotient profile |
| `G014` | H companion caps equality path/port and modulo truncation | 3 | [`LeechTrees/Expanded/Q2Bounds/Q2GraphProfiles.lean`](../LeechTrees/Expanded/Q2Bounds/Q2GraphProfiles.lean)<br>[`LeechTrees/Expanded/Q2Bounds/Q2EqualityTruncation.lean`](../LeechTrees/Expanded/Q2Bounds/Q2EqualityTruncation.lean) | [proof](../proofs/G013_G014_Q2Bounds/FULL_PROOF.md) | Only modulo-X^t truncation |
| `G015` | Exactly-two-odd q at most 10 q not 7 and distinct-port q at most 6 | 10 | [`LeechTrees/Expanded/Q2Bounds/G015SupportFactor.lean`](../LeechTrees/Expanded/Q2Bounds/G015SupportFactor.lean) | [proof](../proofs/G015_TwoOddSharpBounds/FULL_PROOF.md) | Exactly-two-odd scope |
| `G016` | Common-middle-port obstruction for n at least 36 and parity-order families | 10 | [`LeechTrees/Expanded/Q2Bounds/G016GlobalTwoOdd.lean`](../LeechTrees/Expanded/Q2Bounds/G016GlobalTwoOdd.lean)<br>[`LeechTrees/Expanded/Q2Bounds/G016CommonPortAdapter.lean`](../LeechTrees/Expanded/Q2Bounds/G016CommonPortAdapter.lean)<br>[`LeechTrees/Expanded/Q2Bounds/G016CommonPortRankOne.lean`](../LeechTrees/Expanded/Q2Bounds/G016CommonPortRankOne.lean) | [proof](../proofs/G016_TwoOddGlobal/FULL_PROOF.md) | No arbitrary-port global exclusion |
| `G020` | Three-anchor coordinates and named-median parent reconstruction | 4 | [`LeechTrees/Expanded/MultiportTail/ThreePortCoordinates.lean`](../LeechTrees/Expanded/MultiportTail/ThreePortCoordinates.lean) | formal proof in source | Scoped converse only |
| `G021` | OpenMultiport three-odd actual realization and unique optional-parent master | 7 | [`LeechTrees/Expanded/MultiportTail/ThreeOddMasterCover.lean`](../LeechTrees/Expanded/MultiportTail/ThreeOddMasterCover.lean)<br>[`LeechTrees/Expanded/MultiportTail/ActualThreeOddCover.lean`](../LeechTrees/Expanded/MultiportTail/ActualThreeOddCover.lean) | formal proofs in source | OpenMultiport branch only |
| `G022` | Actual four-odd quotient relabeling to P5 fork or star and explicit K-form target | 9 | [`LeechTrees/Expanded/BlockLifts/GaussianScalarCertificates.lean`](../LeechTrees/Expanded/BlockLifts/GaussianScalarCertificates.lean)<br>[`LeechTrees/Expanded/BlockLifts/FourOddGaussianAdapter.lean`](../LeechTrees/Expanded/BlockLifts/FourOddGaussianAdapter.lean) | [proof](../proofs/G022_FourOddGaussian/FULL_IDENTITY_AND_DOMAIN_PROOF.md) | No census or feasibility conclusion |

## Extension and lift obstructions

| Family | Result | Endpoints | Lean source | Human proof | Exact boundary |
|---|---|---:|---|---|---|
| `D3a` | No normalized weighted-path presentation for order at least 5 | 1 | [`LeechTrees/Extensions.lean`](../LeechTrees/Extensions.lean) | [baseline F/D proofs](../proofs/BASELINE_FD_RESULTS.md) | Graph-level obstruction |
| `D3b` | Physical weights not the full initial interval for order at least 5 | 1 | [`LeechTrees/Extensions.lean`](../LeechTrees/Extensions.lean) | [baseline F/D proofs](../proofs/BASELINE_FD_RESULTS.md) | Spanning-path adapter included |
| `D4a0` | Exact one-leaf tail characterization | 3 | [`LeechTrees/Extensions.lean`](../LeechTrees/Extensions.lean)<br>[`LeechTrees/LeafAttachmentAdapter.lean`](../LeechTrees/LeafAttachmentAdapter.lean)<br>[`LeechTrees/LeafRange.lean`](../LeechTrees/LeafRange.lean) | [baseline F/D proofs](../proofs/BASELINE_FD_RESULTS.md) | Actual literal operation |
| `D4a` | No unchanged literal one-leaf attachment for base order at least 4 | 1 | [`LeechTrees/LeafAttachmentAdapter.lean`](../LeechTrees/LeafAttachmentAdapter.lean) | [baseline F/D proofs](../proofs/BASELINE_FD_RESULTS.md) | Exact edge-set operation |
| `D4a2` | Exact positive small-order literal-leaf boundary | 6 | [`LeechTrees/SmallLeafBoundary.lean`](../LeechTrees/SmallLeafBoundary.lean) | [baseline F/D proofs](../proofs/BASELINE_FD_RESULTS.md) | Only base orders 2 and 3 beyond separate order-1 convention |
| `D4b` | No literal weight-preserving subdivision | 1 | [`LeechTrees/OperationAdapters.lean`](../LeechTrees/OperationAdapters.lean) | [baseline F/D proofs](../proofs/BASELINE_FD_RESULTS.md) | Retains old weights |
| `D4c` | No literal unscaled bridge of two nontrivial Leech trees | 1 | [`LeechTrees/OperationAdapters.lean`](../LeechTrees/OperationAdapters.lean) | [baseline F/D proofs](../proofs/BASELINE_FD_RESULTS.md) | Both orders at least 2 |
| `D5a` | Range obstruction for unchanged-subtree extensions | 2 | [`LeechTrees/LeafRange.lean`](../LeechTrees/LeafRange.lean) | [baseline F/D proofs](../proofs/BASELINE_FD_RESULTS.md) | Explicit embedding and indexed metric |
| `D5c` | No two-new-vertex unchanged-subtree extension for base order at least 5 | 1 | [`LeechTrees/LeafRange.lean`](../LeechTrees/LeafRange.lean) | [baseline F/D proofs](../proofs/BASELINE_FD_RESULTS.md) | Generic k equals 2 corollary |
| `D5b` | No order-18 unchanged-subtree extension by 2 through 7 vertices | 1 | [`LeechTrees/LeafRange.lean`](../LeechTrees/LeafRange.lean) | [baseline F/D proofs](../proofs/BASELINE_FD_RESULTS.md) | Exact k interval |
| `G017` | Block-lift gadget and 153-form obstruction/reduction package | 11 | [`LeechTrees/Expanded/BlockLifts/BlockLiftObstructions.lean`](../LeechTrees/Expanded/BlockLifts/BlockLiftObstructions.lean)<br>[`LeechTrees/Expanded/BlockLifts/BlockLiftGraphAdapters.lean`](../LeechTrees/Expanded/BlockLifts/BlockLiftGraphAdapters.lean) | [proofs](../proofs/G017_BlockLifts/FULL_PROOFS.md) | Named architectures |
| `G018` | No positive-integral odd complete-rooted-star-block lift for odd q greater than 1 | 4 | [`LeechTrees/Expanded/BlockLifts/OddCompleteBlock.lean`](../LeechTrees/Expanded/BlockLifts/OddCompleteBlock.lean)<br>[`LeechTrees/Expanded/BlockLifts/OddCompleteBlockArchitecture.lean`](../LeechTrees/Expanded/BlockLifts/OddCompleteBlockArchitecture.lean) | [proof](../proofs/G018_OddCompleteBlocks/FULL_PROOF.md) | Exact architecture only |

## Barrier results and correction witnesses

| Family | Result | Endpoints | Lean source | Human proof | Exact boundary |
|---|---|---:|---|---|---|
| `G019` | Scalar Gaussian certificates for component counts 4 through 18 | 4 | [`LeechTrees/Expanded/BlockLifts/GaussianScalarCertificates.lean`](../LeechTrees/Expanded/BlockLifts/GaussianScalarCertificates.lean) | [proof](../proofs/G019_GaussianFlexibility/FULL_PROOF.md) | Scalar-only; no tree realization |
| `G024` | Counterexamples to reversed below-q2 marginal-flow gluing and histogram determination | 20 | [`LeechTrees/Expanded/PathMulticut/BroomWitness.lean`](../LeechTrees/Expanded/PathMulticut/BroomWitness.lean)<br>[`LeechTrees/Expanded/RankParity/OddQuotientCapacityConsequences.lean`](../LeechTrees/Expanded/RankParity/OddQuotientCapacityConsequences.lean)<br>[`LeechTrees/Expanded/RankParity/SignedCutFlow.lean`](../LeechTrees/Expanded/RankParity/SignedCutFlow.lean) | [q2/flow witnesses](../proofs/G002_G010_G024ab_RankParityCoordinates/FULL_PROOFS.md)<br>[multicut witness](../proofs/G011_G012_G024c_Multicut/FULL_PROOFS.md) | Counterexample scope only |

## Machine-readable declaration map

CLAIM_ENDPOINTS.tsv contains one row for each of the 324 claim-bearing
declarations, with fields claim_id, scope, declaration, kind, and
repository-relative source. The separate 350-query audit includes these 324
declarations plus 26 model/support declarations.
