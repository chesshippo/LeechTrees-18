import LeechTrees.Expanded.PathMulticut.ActualSelectedEdgeDecomposition
import LeechTrees.Expanded.PathMulticut.MulticutHall

/-!
# Actual selected-edge blocks and capacitated Hall

This file supplies the graph/model endpoint for G012.  A block is not an
arbitrary finite set: it is the image of the actual Cartesian product of two
named components of `T \ F`, under the original tree distance.  Its demand,
lower endpoint, physical intersection, mutual disjointness, Hall inequality,
and shared-tail consequences are therefore derived from `PosIntTree` and
`IsLeech`.
-/

open scoped BigOperators

namespace LeechTrees.PathMulticut

open LeechTrees.Foundation
open LeechTrees.OddQuotient

noncomputable section

abbrev SelectedBlockIndex {n : ℕ} (T : PosIntTree n) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) :=
  SelectedComponentVertex T F q.left ×
    SelectedComponentVertex T F q.right

/-- The actual unordered named-vertex pair represented by one component-pair
slot. -/
noncomputable def selectedBlockPair {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) (z : SelectedBlockIndex T F q) :
    VertexPair n :=
  indexToPair (selectedMarker T F) (.inr ⟨q, z⟩)

@[simp] theorem selectedBlockPair_dist {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) (z : SelectedBlockIndex T F q) :
    T.pairDist (selectedBlockPair T F q z) = selectedCrossRank T F q z := by
  exact selected_pair_partition_rank T F (.inr ⟨q, z⟩)

/-- `B_ij`: the actual set of original distances between two selected-deletion
components. -/
def selectedBlock {n : ℕ} (T : PosIntTree n) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) : Finset ℕ :=
  Finset.univ.image (selectedCrossRank T F q)

/-- The exact component-product demand of one block. -/
def selectedBlockDemand {n : ℕ} (T : PosIntTree n) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) : ℕ :=
  Fintype.card (SelectedComponentVertex T F q.left) *
    Fintype.card (SelectedComponentVertex T F q.right)

/-- Number of selected quotient edges on the actual canonical route. -/
def selectedRouteHops {n : ℕ} (T : PosIntTree n) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) : ℕ :=
  (canonicalRouteWalk (selectedMarker T F) q).length

/-- A route joining two distinct quotient components contains at least one
selected bridge.  This fact is used below to make the retained physical
allowance depend only on the route, rather than circularly on the block that
it is meant to contain. -/
theorem selectedRouteHops_pos {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) :
    0 < selectedRouteHops T F q := by
  change 0 < (canonicalRouteData (selectedMarker T F) q).tail.length + 1
  omega

/-- The graph-derived block map is injective in a Leech tree. -/
theorem selectedCrossRank_injective {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) :
    Function.Injective (selectedCrossRank T F q) := by
  intro x y hxy
  have hall := actual_selectedEdge_splitRank_injective hL F
  have hs :
      (Sum.inr ⟨q, x⟩ : SelectedWithinIndex T F ⊕ SelectedCrossIndex T F) =
        Sum.inr ⟨q, y⟩ := hall hxy
  have hsig : (⟨q, x⟩ : SelectedCrossIndex T F) = ⟨q, y⟩ :=
    Sum.inr.inj hs
  cases hsig
  rfl

/-- First equality in (21), with multiplicity justified before taking the
image: `|B_ij| = |K_i||K_j|`. -/
theorem selectedBlock_card {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) :
    (selectedBlock T F q).card = selectedBlockDemand T F q := by
  rw [selectedBlock, Finset.card_image_of_injective _
    (selectedCrossRank_injective hL F q)]
  simp [selectedBlockDemand]

/-- Second assertion in (21): the route shift is a genuine lower endpoint,
and every actual block rank is at most the Leech target. -/
theorem selectedBlock_subset_interval {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) :
    selectedBlock T F q ⊆
      Finset.Icc (selectedRouteLength T F q) (targetN n) := by
  intro d hd
  obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hd
  apply Finset.mem_Icc.mpr
  constructor
  · simp only [selectedCrossRank, selectedLeftDepth, selectedRightDepth]
    omega
  · rw [← selectedBlockPair_dist T F q z]
    exact hL.pairDist_le_target _

/-- Actual selected bridges joining the two fixed quotient components.  The
filter is over indexed bridges, so parallel collapse cannot be hidden. -/
def selectedConnectingBridges {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) :
    Finset (OddBridge (selectedMarker T F)) :=
  Finset.univ.filter fun e =>
    quotientEdgePair (selectedMarker T F) e = s(q.left, q.right)

def selectedConnectingWeights {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) : Finset ℕ :=
  (selectedConnectingBridges T F q).image fun e => T.weight e.1

theorem selectedConnectingBridges_card_le_one {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) :
    (selectedConnectingBridges T F q).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  apply quotientEdgePair_injective (selectedMarker T F)
  exact (Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm

private theorem selectedBlock_of_connectingBridge {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    (q : SelectedComponentPair T F)
    (e : OddBridge (selectedMarker T F))
    (he : quotientEdgePair (selectedMarker T F) e = s(q.left, q.right)) :
    T.weight e.1 ∈ selectedBlock T F q := by
  rw [quotientEdgePair_eq] at he
  rcases Sym2.eq_iff.mp he with h | h
  · let z : SelectedBlockIndex T F q :=
      (⟨T.edgeLeft e.1, h.1⟩, ⟨T.edgeRight e.1, h.2⟩)
    apply Finset.mem_image.mpr
    refine ⟨z, Finset.mem_univ _, ?_⟩
    change selectedRouteLength T F q +
      T.dist z.1.1 (selectedSourcePort T F q).1 +
      T.dist z.2.1 (selectedTargetPort T F q).1 = T.weight e.1
    rw [← selected_cross_distance_decomposition T F q z.1 z.2]
    simpa [z, PosIntTree.pairDist] using T.edgePair_dist e.1
  · let z : SelectedBlockIndex T F q :=
      (⟨T.edgeRight e.1, h.2⟩, ⟨T.edgeLeft e.1, h.1⟩)
    apply Finset.mem_image.mpr
    refine ⟨z, Finset.mem_univ _, ?_⟩
    change selectedRouteLength T F q +
      T.dist z.1.1 (selectedSourcePort T F q).1 +
      T.dist z.2.1 (selectedTargetPort T F q).1 = T.weight e.1
    rw [← selected_cross_distance_decomposition T F q z.1 z.2]
    rw [T.dist_comm]
    simpa [z, PosIntTree.pairDist] using T.edgePair_dist e.1

private theorem connectingBridge_of_block_physical {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) {d : ℕ}
    (hdB : d ∈ selectedBlock T F q)
    (hdW : d ∈ physicalWeightSet T) :
    ∃ e : OddBridge (selectedMarker T F),
      quotientEdgePair (selectedMarker T F) e = s(q.left, q.right) ∧
        T.weight e.1 = d := by
  obtain ⟨z, -, hz⟩ := Finset.mem_image.mp hdB
  obtain ⟨e, -, he⟩ := Finset.mem_image.mp hdW
  have hp : selectedBlockPair T F q z = T.edgePair e := by
    apply hL.pairDist_injective
    calc
      T.pairDist (selectedBlockPair T F q z) =
          selectedCrossRank T F q z := selectedBlockPair_dist T F q z
      _ = d := hz
      _ = T.weight e := he.symm
      _ = T.pairDist (T.edgePair e) := (T.edgePair_dist e).symm
  let M := selectedMarker T F
  have hs := indexToPair_cross_sym2 M
    (⟨q, z⟩ : SelectedCrossIndex T F)
  have hc :
      s(componentOf M (T.edgeLeft e), componentOf M (T.edgeRight e)) =
        s(q.left, q.right) := by
    change s((selectedBlockPair T F q z).left,
      (selectedBlockPair T F q z).right) = s(z.1.1, z.2.1) at hs
    rw [hp] at hs
    simp only [T.edgePair_left, T.edgePair_right] at hs
    rcases Sym2.eq_iff.mp hs with h | h
    · rw [h.1, h.2, z.1.2, z.2.2]
    · rw [h.1, h.2, z.2.2, z.1.2]
      exact Sym2.eq_swap
  have hne : componentOf M (T.edgeLeft e) ≠
      componentOf M (T.edgeRight e) := by
    intro heq
    have hdiag : (s(q.left, q.right) : Sym2 (SelectedComponent T F)).IsDiag := by
      rw [← hc, heq]
      exact Sym2.mk_isDiag_iff.mpr rfl
    exact q.ne (Sym2.mk_isDiag_iff.mp hdiag)
  have hodd : Odd (M.weight e) :=
    (odd_weight_iff_components_ne M e).2 hne
  let b : OddBridge M := ⟨e, hodd⟩
  refine ⟨b, ?_, ?_⟩
  · simpa [b, M, quotientEdgePair_eq] using hc
  · exact he

/-- Exact physical part of (21), before splitting adjacent/nonadjacent cases.
It is the image of the unique possible actual selected bridge between the two
components. -/
theorem selectedBlock_inter_physical {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) :
    selectedBlock T F q ∩ physicalWeightSet T =
      selectedConnectingWeights T F q := by
  apply Finset.ext
  intro d
  constructor
  · intro hd
    obtain ⟨b, hbq, hbd⟩ := connectingBridge_of_block_physical hL F q
      (Finset.mem_inter.mp hd).1 (Finset.mem_inter.mp hd).2
    apply Finset.mem_image.mpr
    refine ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbq⟩, hbd⟩
  · intro hd
    obtain ⟨b, hb, hbd⟩ := Finset.mem_image.mp hd
    have hbq := (Finset.mem_filter.mp hb).2
    apply Finset.mem_inter.mpr
    constructor
    · simpa [hbd] using selectedBlock_of_connectingBridge T F q b hbq
    · rw [← hbd]
      exact weight_mem_physicalWeightSet T b.1

/-- The route has one hop exactly for adjacent quotient components. -/
theorem selectedRouteHops_eq_one_iff_adj {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) :
    selectedRouteHops T F q = 1 ↔
      (quotientGraph (selectedMarker T F)).Adj q.left q.right := by
  let M := selectedMarker T F
  constructor
  · intro hlen
    exact (canonicalRouteWalk M q).adj_of_length_eq_one hlen
  · intro hadj
    have hp : SimpleGraph.Path.singleton hadj =
        quotientPath M q.left q.right := quotientPath_unique M _
    rw [selectedRouteHops, canonicalRouteWalk_eq_quotientPath, ← hp]
    simp [SimpleGraph.Path.singleton]

private theorem selectedRouteInterior_eq_zero_of_length_zero {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    {C D : SelectedComponent T F}
    (p : (quotientGraph (selectedMarker T F)).Walk C D)
    (hp : p.length = 0) (x : SelectedComponentVertex T F C) :
    selectedRouteInterior T F p x = 0 := by
  cases p with
  | nil => rfl
  | cons h p => simp at hp

/-- Adjacent case of (21): the retained physical value is exactly the route
length, not an independently named bridge weight. -/
theorem selectedBlock_inter_physical_eq_singleton_of_one_hop {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) (hh : selectedRouteHops T F q = 1) :
    selectedBlock T F q ∩ physicalWeightSet T =
      {selectedRouteLength T F q} := by
  have hadj := (selectedRouteHops_eq_one_iff_adj T F q).1 hh
  let M := selectedMarker T F
  let R := canonicalRouteData M q
  let ob := orientedBridgeOfAdj M R.head
  let b := ob.bridge
  have htail : R.tail.length = 0 := by
    simpa [selectedRouteHops, canonicalRouteWalk, M, R] using hh
  have hnext : R.next = q.right := R.tail.eq_of_length_eq_zero htail
  have hbq : quotientEdgePair M b = s(q.left, q.right) := by
    simpa [b, ob, hnext] using ob.component_pair
  have hconn : selectedConnectingBridges T F q = {b} := by
    apply Finset.ext
    intro e
    constructor
    · intro he
      have heq : e = b := quotientEdgePair_injective M <|
        (Finset.mem_filter.mp he).2.trans hbq.symm
      simp [heq]
    · intro he
      have heq : e = b := Finset.mem_singleton.mp he
      subst e
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbq⟩
  rw [selectedBlock_inter_physical hL F q, selectedConnectingWeights, hconn]
  simp only [Finset.image_singleton]
  congr 1
  change T.weight b.1 =
    T.weight b.1 + selectedRouteInterior T F R.tail ob.targetPort
  rw [selectedRouteInterior_eq_zero_of_length_zero T F R.tail htail]
  simp

/-- Nonadjacent case of (21). -/
theorem selectedBlock_inter_physical_eq_empty_of_two_le {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) (hh : 2 ≤ selectedRouteHops T F q) :
    selectedBlock T F q ∩ physicalWeightSet T = ∅ := by
  rw [selectedBlock_inter_physical hL F q]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro d hd
  obtain ⟨b, hb, -⟩ := Finset.mem_image.mp hd
  have hadj : (quotientGraph (selectedMarker T F)).Adj q.left q.right :=
    (quotientGraph_adj_iff _ _ _).2 ⟨b, (Finset.mem_filter.mp hb).2⟩
  have hone := (selectedRouteHops_eq_one_iff_adj T F q).2 hadj
  omega

/-- The physical value which the route geometry permits this block to retain.
It is a singleton on a one-hop route and empty on every longer route.  Unlike
the old definition, this set does not mention `selectedBlock`. -/
def selectedPhysicalAllowance {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) : Finset ℕ :=
  if selectedRouteHops T F q = 1 then
    {selectedRouteLength T F q}
  else
    ∅

/-- Exact graph-level identification of the physical part of an actual block
with its independently defined route allowance. -/
theorem selectedBlock_inter_physical_eq_allowance {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) :
    selectedBlock T F q ∩ physicalWeightSet T =
      selectedPhysicalAllowance T F q := by
  by_cases hh : selectedRouteHops T F q = 1
  · simp only [selectedPhysicalAllowance, if_pos hh]
    exact selectedBlock_inter_physical_eq_singleton_of_one_hop hL F q hh
  · have htwo : 2 ≤ selectedRouteHops T F q := by
      have hpos := selectedRouteHops_pos T F q
      omega
    simp only [selectedPhysicalAllowance, if_neg hh]
    exact selectedBlock_inter_physical_eq_empty_of_two_le hL F q htwo

/-- The exact allowed set in (21): all ranks in the route suffix, punctured
by physical weights except for the route-determined one-hop allowance. -/
def selectedAllowedSet {n : ℕ} (T : PosIntTree n) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) : Finset ℕ :=
  (Finset.Icc (selectedRouteLength T F q) (targetN n)).filter fun d =>
    d ∉ physicalWeightSet T ∨ d ∈ selectedPhysicalAllowance T F q

theorem selectedBlock_subset_allowed {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) :
    selectedBlock T F q ⊆ selectedAllowedSet T F q := by
  intro d hd
  apply Finset.mem_filter.mpr
  refine ⟨selectedBlock_subset_interval hL F q hd, ?_⟩
  by_cases hdW : d ∈ physicalWeightSet T
  · right
    have hdI : d ∈ selectedBlock T F q ∩ physicalWeightSet T :=
      Finset.mem_inter.mpr ⟨hd, hdW⟩
    rw [selectedBlock_inter_physical_eq_allowance hL F q] at hdI
    exact hdI
  · exact Or.inl hdW

/-- The allowed set has exactly the independently computed physical part. -/
theorem selectedAllowedSet_inter_physical_eq_allowance {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) :
    selectedAllowedSet T F q ∩ physicalWeightSet T =
      selectedPhysicalAllowance T F q := by
  apply Finset.ext
  intro d
  constructor
  · intro hd
    have hdA := (Finset.mem_filter.mp (Finset.mem_inter.mp hd).1).2
    have hdW := (Finset.mem_inter.mp hd).2
    exact hdA.resolve_left (fun hdNot => hdNot hdW)
  · intro hd
    have hdI : d ∈ selectedBlock T F q ∩ physicalWeightSet T := by
      rw [selectedBlock_inter_physical_eq_allowance hL F q]
      exact hd
    have hdB : d ∈ selectedBlock T F q := (Finset.mem_inter.mp hdI).1
    exact Finset.mem_inter.mpr
      ⟨selectedBlock_subset_allowed hL F q hdB,
        (Finset.mem_inter.mp hdI).2⟩

theorem selectedAllowedSet_inter_physical_eq_singleton_of_one_hop {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) (F : Finset T.Edge)
    (q : SelectedComponentPair T F)
    (hh : selectedRouteHops T F q = 1) :
    selectedAllowedSet T F q ∩ physicalWeightSet T =
      {selectedRouteLength T F q} := by
  rw [selectedAllowedSet_inter_physical_eq_allowance hL F q]
  simp [selectedPhysicalAllowance, hh]

theorem selectedAllowedSet_inter_physical_eq_empty_of_two_le {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) (F : Finset T.Edge)
    (q : SelectedComponentPair T F)
    (hh : 2 ≤ selectedRouteHops T F q) :
    selectedAllowedSet T F q ∩ physicalWeightSet T = ∅ := by
  rw [selectedAllowedSet_inter_physical_eq_allowance hL F q]
  have hne : selectedRouteHops T F q ≠ 1 := by omega
  simp [selectedPhysicalAllowance, hne]

/-- The genuinely punctured suffix used by every route of length at least two. -/
def selectedPuncturedTail {n : ℕ} (T : PosIntTree n) (lower : ℕ) :
    Finset ℕ :=
  (Finset.Icc lower (targetN n)).filter fun d => d ∉ physicalWeightSet T

theorem selectedAllowedSet_subset_puncturedTail_of_two_le {n : ℕ}
    {T : PosIntTree n} (F : Finset T.Edge)
    (q : SelectedComponentPair T F)
    (hh : 2 ≤ selectedRouteHops T F q)
    {lower : ℕ} (hlower : lower ≤ selectedRouteLength T F q) :
    selectedAllowedSet T F q ⊆ selectedPuncturedTail T lower := by
  intro d hd
  have hd' := Finset.mem_filter.mp hd
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr
    ⟨hlower.trans (Finset.mem_Icc.mp hd'.1).1,
      (Finset.mem_Icc.mp hd'.1).2⟩, ?_⟩
  exact hd'.2.resolve_right <| by
    simp [selectedPhysicalAllowance, show selectedRouteHops T F q ≠ 1 by omega]

/-- Distinct actual component-pair blocks are disjoint. -/
theorem selectedBlocks_disjoint {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) (F : Finset T.Edge)
    {q r : SelectedComponentPair T F} (hqr : q ≠ r) :
    Disjoint (selectedBlock T F q) (selectedBlock T F r) := by
  rw [Finset.disjoint_left]
  intro d hdq hdr
  obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hdq
  obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hdr
  have hall := actual_selectedEdge_splitRank_injective hL F
  have hs :
      (Sum.inr ⟨q, x⟩ : SelectedWithinIndex T F ⊕ SelectedCrossIndex T F) =
        Sum.inr ⟨r, y⟩ := hall (hx.trans hy.symm)
  have hsig : (⟨q, x⟩ : SelectedCrossIndex T F) = ⟨r, y⟩ :=
    Sum.inr.inj hs
  exact hqr (congrArg Sigma.fst hsig)

/-- Actual graph-level capacitated Hall inequality (22). -/
theorem actual_selectedBlock_Hall {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) (F : Finset T.Edge)
    (S : Finset (SelectedComponentPair T F)) :
    (∑ q ∈ S, selectedBlockDemand T F q) ≤
      (S.biUnion (selectedAllowedSet T F)).card := by
  have hdisj : S.toSet.PairwiseDisjoint (selectedBlock T F) := by
    intro q hq r hr hqr
    exact selectedBlocks_disjoint hL F hqr
  calc
    (∑ q ∈ S, selectedBlockDemand T F q) =
        (S.biUnion (selectedBlock T F)).card := by
      rw [Finset.card_biUnion hdisj]
      apply Finset.sum_congr rfl
      intro q hq
      exact (selectedBlock_card hL F q).symm
    _ ≤ (S.biUnion (selectedAllowedSet T F)).card :=
      Finset.card_le_card <| by
        intro d hd
        obtain ⟨q, hq, hdq⟩ := Finset.mem_biUnion.mp hd
        exact Finset.mem_biUnion.mpr
          ⟨q, hq, selectedBlock_subset_allowed hL F q hdq⟩

/-- The Hall iff for the actual selected-component demands/allowed sets.  The
reverse direction remains correctly scoped to abstract rank slots. -/
theorem actual_selectedBlock_Hall_iff_injective {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) (F : Finset T.Edge) :
    (∀ S : Finset (SelectedComponentPair T F),
      (∑ q ∈ S, selectedBlockDemand T F q) ≤
        (S.biUnion (selectedAllowedSet T F)).card) ∧
    (
      (∀ S : Finset (SelectedComponentPair T F),
        (∑ q ∈ S, selectedBlockDemand T F q) ≤
          (S.biUnion (selectedAllowedSet T F)).card) ↔
      ∃ assign : DemandSlot (selectedBlockDemand T F) → ℕ,
        Function.Injective assign ∧
          ∀ s, assign s ∈ selectedAllowedSet T F s.1) := by
  exact ⟨actual_selectedBlock_Hall hL F,
    capacitatedHall_iff_injective
      (selectedBlockDemand T F) (selectedAllowedSet T F)⟩

/-- Port-aware shared suffix, derived from the actual Hall inequality rather
than assumed as a set-system premise. -/
theorem actual_selectedBlock_shared_tail {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) (F : Finset T.Edge)
    (S : Finset (SelectedComponentPair T F))
    (tail : Finset ℕ)
    (htail : ∀ q ∈ S, selectedAllowedSet T F q ⊆ tail) :
    (∑ q ∈ S, selectedBlockDemand T F q) ≤ tail.card := by
  exact shared_tail_capacity
    (selectedBlockDemand T F) (selectedAllowedSet T F)
    (actual_selectedBlock_Hall hL F) S tail htail

/-- Direct graph-level form of (24)--(27): every selected component pair in
`S` has a multi-hop route, every route starts no earlier than `lower`, and all
their demands therefore compete for the same physically punctured suffix. -/
theorem actual_selectedBlock_shared_punctured_tail {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) (F : Finset T.Edge)
    (S : Finset (SelectedComponentPair T F)) (lower : ℕ)
    (hhops : ∀ q ∈ S, 2 ≤ selectedRouteHops T F q)
    (hlower : ∀ q ∈ S, lower ≤ selectedRouteLength T F q) :
    (∑ q ∈ S, selectedBlockDemand T F q) ≤
      (selectedPuncturedTail T lower).card := by
  apply actual_selectedBlock_shared_tail hL F S
    (selectedPuncturedTail T lower)
  intro q hq
  exact selectedAllowedSet_subset_puncturedTail_of_two_le F q
    (hhops q hq) (hlower q hq)

/-! ## Exact order-18 tail arithmetic -/

private theorem order18_parity_interval_card
    (ell : ℕ) (hell : 2 ≤ ell) (hellN : ell ^ 2 ≤ 153) :
    ((Finset.Icc (ell ^ 2) 153).filter
      (fun d => d % 2 = ell % 2)).card = 77 - ell ^ 2 / 2 := by
  have hell12 : ell ≤ 12 := by nlinarith
  interval_cases ell <;> decide

/-- Formula (25): cardinality of the parity-punctured order-18 tail. -/
theorem order18_punctured_parity_tail_card
    (W : Finset ℕ) (ell : ℕ)
    (hW : W ⊆ Finset.Icc 1 153)
    (hell : 2 ≤ ell) (hellN : ell ^ 2 ≤ 153) :
    ((Finset.Icc (ell ^ 2) 153).filter
      (fun d => d % 2 = ell % 2 ∧ d ∉ W)).card =
      77 - ell ^ 2 / 2 -
        ((W.filter fun w => ell ^ 2 ≤ w ∧ w % 2 = ell % 2).card) := by
  have hparityCard :
      ((Finset.Icc (ell ^ 2) 153).filter
        (fun d => d % 2 = ell % 2)).card = 77 - ell ^ 2 / 2 := by
    exact order18_parity_interval_card ell hell hellN
  let A := (Finset.Icc (ell ^ 2) 153).filter fun d => d % 2 = ell % 2
  have hsplit := Finset.card_sdiff_add_card_inter A W
  have hinter :
      (A ∩ W).card =
        (W.filter fun w => ell ^ 2 ≤ w ∧ w % 2 = ell % 2).card := by
    apply congrArg Finset.card
    ext d
    have hdUpper : d ∈ W → d ≤ 153 := fun hd =>
      (Finset.mem_Icc.mp (hW hd)).2
    simp only [A, Finset.mem_inter, Finset.mem_filter, Finset.mem_Icc]
    aesop
  have hleft :
      ((Finset.Icc (ell ^ 2) 153).filter
        (fun d => d % 2 = ell % 2 ∧ d ∉ W)) = A \ W := by
    ext d
    simp only [A, Finset.mem_filter, Finset.mem_Icc, Finset.mem_sdiff]
    tauto
  change A.card = 77 - ell ^ 2 / 2 at hparityCard
  rw [hparityCard, hinter] at hsplit
  rw [hleft]
  omega

/-- Formula (26), isolated with its exact physical-rank counting premise. -/
theorem order18_even_tail_at_two
    (W : Finset ℕ) (r : ℕ)
    (hW : W ⊆ Finset.Icc 1 153)
    (hWcard : W.card = 17)
    (hodd : (W.filter Odd).card = r)
    (htwo : 2 ∈ W)
    (hevenBelow : ∀ w ∈ W, Even w → w < 4 → w = 2) :
    ((Finset.Icc 4 153).filter
      (fun d => d % 2 = 0 ∧ d ∉ W)).card = 59 + r := by
  have hevenCard : (W.filter Even).card = 17 - r := by
    have hpartition : (W.filter Even).card + (W.filter Odd).card = W.card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1
        ext w
        simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨hw, -⟩ | ⟨hw, -⟩) <;> exact hw
        · intro hw
          rcases Nat.even_or_odd w with he | ho
          · exact Or.inl ⟨hw, he⟩
          · exact Or.inr ⟨hw, ho⟩
      · rw [Finset.disjoint_left]
        intro w hwE hwO
        exact Nat.not_even_iff_odd.mpr (Finset.mem_filter.mp hwO).2
          (Finset.mem_filter.mp hwE).2
    omega
  have hremoved :
      (W.filter fun w => 4 ≤ w ∧ w % 2 = 0).card = 16 - r := by
    have hdecomp :
        W.filter Even = insert 2 (W.filter fun w => 4 ≤ w ∧ Even w) := by
      ext w
      constructor
      · intro hw
        have hWE := Finset.mem_filter.mp hw
        by_cases hw2 : w = 2
        · simp [hw2]
        · have : 4 ≤ w := by
            by_contra h
            exact hw2 (hevenBelow w hWE.1 hWE.2 (by omega))
          simp [hWE.1, hWE.2, this]
      · intro hw
        simp only [Finset.mem_insert, Finset.mem_filter] at hw ⊢
        rcases hw with rfl | hw
        · exact ⟨htwo, by decide⟩
        · exact ⟨hw.1, hw.2.2⟩
    have hnot : 2 ∉ W.filter (fun w => 4 ≤ w ∧ Even w) := by simp
    rw [hdecomp, Finset.card_insert_of_notMem hnot] at hevenCard
    have hfilter :
        W.filter (fun w => 4 ≤ w ∧ Even w) =
          W.filter (fun w => 4 ≤ w ∧ w % 2 = 0) := by
      ext w
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hw, h4, he⟩
        exact ⟨hw, h4, Nat.even_iff.mp he⟩
      · rintro ⟨hw, h4, hm⟩
        exact ⟨hw, h4, Nat.even_iff.mpr hm⟩
    rw [hfilter] at hevenCard
    omega
  have hevenPos : 0 < (W.filter Even).card := by
    exact Finset.card_pos.mpr
      ⟨2, Finset.mem_filter.mpr ⟨htwo, by decide⟩⟩
  have hr : r ≤ 16 := by omega
  have h25 := order18_punctured_parity_tail_card W 2 hW
    (by omega) (by norm_num)
  norm_num at h25
  rw [hremoved] at h25
  omega

/-- Formula (27). -/
theorem order18_odd_tail_at_three (W : Finset ℕ)
    (hW : W ⊆ Finset.Icc 1 153) :
    ((Finset.Icc 9 153).filter
      (fun d => d % 2 = 1 ∧ d ∉ W)).card =
      73 - (W.filter fun w => 9 ≤ w ∧ Odd w).card := by
  have h25 := order18_punctured_parity_tail_card W 3 hW
    (by omega) (by norm_num)
  norm_num at h25
  simpa [Nat.odd_iff] using h25

end

end LeechTrees.PathMulticut
