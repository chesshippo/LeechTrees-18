import LeechTrees.Expanded.PathMulticut.SelectedBlockHall
import LeechTrees.Expanded.RankParity.OddQuotientCapacityConsequences
import LeechTrees.OddEdgesGraphAdapter

/-!
# Actual odd-quotient shared-tail Hall inequalities

This module reuses the actual route machinery of
`OddCapacity.ActualComponentPair` and adds precisely the G012 family layer:
physical-rank puncturing for nonadjacent component pairs, mutual disjointness,
the simultaneous Hall bound (24), and its order-18 evaluations (25)--(27).
-/

open scoped BigOperators

namespace LeechTrees.PathMulticut

open LeechTrees.Foundation
open LeechTrees.OddQuotient
open LeechTrees.OddCapacity
open LeechTrees.OddCapacity.ActualComponentPair
open LeechTrees.OddEdges.GraphAdapter

noncomputable section

abbrev OddComponentPair (T : PosIntTree 18) := QuotientComponentPair T

def oddBlockDemand (T : PosIntTree 18) (q : OddComponentPair T) : ℕ :=
  Fintype.card (ComponentVertex T q.left) *
    Fintype.card (ComponentVertex T q.right)

def order18OddSharedTail (T : PosIntTree 18) (ell : ℕ) : Finset ℕ :=
  (Finset.Icc (ell ^ 2) 153).filter fun d =>
    d % 2 = ell % 2 ∧ d ∉ physicalWeightSet T

private theorem oddCross_component_pair {T : PosIntTree 18}
    (q : OddComponentPair T)
    (x : ComponentVertex T q.left × ComponentVertex T q.right) :
    s(componentOf T (pairIndex q x).left,
        componentOf T (pairIndex q x).right) = s(q.left, q.right) := by
  have hs := indexToPair_cross_sym2 T (⟨q, x⟩ : CrossIndex T)
  have hmap := congrArg (Sym2.map (componentOf T)) hs
  simp only [Sym2.map_pair_eq] at hmap
  rw [x.1.2, x.2.2] at hmap
  simpa [pairIndex] using hmap

/-- Physical part of (21) for the actual odd quotient: every block at
quotient distance at least two is disjoint from all physical ranks. -/
theorem oddCrossDistances_inter_physical_eq_empty
    {T : PosIntTree 18} (hL : IsLeech T) (q : OddComponentPair T)
    (hell : 2 ≤ ell q) :
    crossDistances q ∩ physicalWeightSet T = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro d hd
  obtain ⟨hdq, hdW⟩ := Finset.mem_inter.mp hd
  obtain ⟨x, -, hxd⟩ := Finset.mem_image.mp hdq
  obtain ⟨e, -, hed⟩ := Finset.mem_image.mp hdW
  have hp : pairIndex q x = T.edgePair e := by
    apply hL.pairDist_injective
    calc
      T.pairDist (pairIndex q x) = d := hxd
      _ = T.weight e := hed.symm
      _ = T.pairDist (T.edgePair e) := (T.edgePair_dist e).symm
  have hc := oddCross_component_pair q x
  rw [hp] at hc
  simp only [T.edgePair_left, T.edgePair_right] at hc
  have hne : componentOf T (T.edgeLeft e) ≠
      componentOf T (T.edgeRight e) := by
    intro heq
    have hdiag : (s(q.left, q.right) : Sym2 (EvenComponent T)).IsDiag := by
      rw [← hc, heq]
      exact Sym2.mk_isDiag_iff.mpr rfl
    exact q.ne (Sym2.mk_isDiag_iff.mp hdiag)
  have hodd : Odd (T.weight e) := (odd_weight_iff_components_ne T e).2 hne
  let b : OddBridge T := ⟨e, hodd⟩
  have hbq : quotientEdgePair T b = s(q.left, q.right) := by
    simpa [b, quotientEdgePair_eq] using hc
  have hadj : (quotientGraph T).Adj q.left q.right :=
    (quotientGraph_adj_iff T q.left q.right).2 ⟨b, hbq⟩
  have hpPath : SimpleGraph.Path.singleton hadj =
      quotientPath T q.left q.right := quotientPath_unique T _
  have hone : ell q = 1 := by
    rw [OddCapacity.ActualComponentPair.ell, ← hpPath]
    simp [SimpleGraph.Path.singleton]
  omega

/-- Actual odd block contained in its square/parity/physical-punctured suffix.
-/
theorem oddCrossDistances_subset_punctured_tail
    {T : PosIntTree 18} (hL : IsLeech T) (q : OddComponentPair T)
    (hell : 2 ≤ ell q) :
    crossDistances q ⊆ order18OddSharedTail T (ell q) := by
  intro d hd
  have htail := crossDistances_subset_square_parity_tail q hL hd
  have hnonphysical : d ∉ physicalWeightSet T := by
    intro hdW
    have : d ∈ crossDistances q ∩ physicalWeightSet T :=
      Finset.mem_inter.mpr ⟨hd, hdW⟩
    rw [oddCrossDistances_inter_physical_eq_empty hL q hell] at this
    exact Finset.notMem_empty d this
  exact Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp htail).1,
      ⟨(Finset.mem_filter.mp htail).2, hnonphysical⟩⟩

/-- Distinct actual odd-quotient component-pair blocks are disjoint. -/
theorem oddCrossDistances_disjoint {T : PosIntTree 18}
    (hL : IsLeech T) {q r : OddComponentPair T} (hqr : q ≠ r) :
    Disjoint (crossDistances q) (crossDistances r) := by
  rw [Finset.disjoint_left]
  intro d hdq hdr
  obtain ⟨x, -, hxd⟩ := Finset.mem_image.mp hdq
  obtain ⟨y, -, hyd⟩ := Finset.mem_image.mp hdr
  have hp : pairIndex q x = pairIndex r y :=
    hL.pairDist_injective (hxd.trans hyd.symm)
  have hs :
      (Sum.inr ⟨q, x⟩ : WithinIndex T ⊕ CrossIndex T) =
        Sum.inr ⟨r, y⟩ := (vertexPairIndexEquiv T).symm.injective hp
  have hsig : (⟨q, x⟩ : CrossIndex T) = ⟨r, y⟩ := Sum.inr.inj hs
  exact hqr (congrArg Sigma.fst hsig)

def oddSharedFamily (T : PosIntTree 18) (ell : ℕ) :
    Finset (OddComponentPair T) :=
  Finset.univ.filter fun q => ell ≤ ActualComponentPair.ell q ∧
    ActualComponentPair.ell q % 2 = ell % 2

private theorem odd_tail_mono {T : PosIntTree 18} {ell : ℕ}
    {q : OddComponentPair T}
    (hq : q ∈ oddSharedFamily T ell) :
    order18OddSharedTail T (ActualComponentPair.ell q) ⊆
      order18OddSharedTail T ell := by
  intro d hd
  rw [oddSharedFamily] at hq
  obtain ⟨hqLower, hqParity⟩ := (Finset.mem_filter.mp hq).2
  rw [order18OddSharedTail] at hd ⊢
  obtain ⟨hdIcc, hdParity, hdPhysical⟩ := Finset.mem_filter.mp hd
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨?_, (Finset.mem_Icc.mp hdIcc).2⟩, ?_, hdPhysical⟩
  · have := (Finset.mem_Icc.mp hdIcc).1
    nlinarith
  · exact hdParity.trans hqParity

/-- Formula (24), derived simultaneously from the actual mutually disjoint
component blocks. -/
theorem actual_odd_shared_tail_inequality
    {T : PosIntTree 18} (hL : IsLeech T) (ell : ℕ) (hell : 2 ≤ ell) :
    (∑ q ∈ oddSharedFamily T ell, oddBlockDemand T q) ≤
      (order18OddSharedTail T ell).card := by
  let S := oddSharedFamily T ell
  have hdisj : S.toSet.PairwiseDisjoint
      (fun q : OddComponentPair T => crossDistances q) := by
    intro q hq r hr hqr
    exact oddCrossDistances_disjoint hL hqr
  calc
    (∑ q ∈ S, oddBlockDemand T q) =
        (S.biUnion fun q => crossDistances q).card := by
      rw [Finset.card_biUnion hdisj]
      apply Finset.sum_congr rfl
      intro q hq
      exact (crossDistances_card q hL).symm
    _ ≤ (order18OddSharedTail T ell).card :=
      Finset.card_le_card <| by
        intro d hd
        obtain ⟨q, hq, hdq⟩ := Finset.mem_biUnion.mp hd
        have hqell : 2 ≤ ActualComponentPair.ell q := by
          have := (Finset.mem_filter.mp hq).2.1
          omega
        exact odd_tail_mono hq
          (oddCrossDistances_subset_punctured_tail hL q hqell hdq)

private theorem physicalWeightSet_order18_subset_target
    {T : PosIntTree 18} (hL : IsLeech T) :
    physicalWeightSet T ⊆ Finset.Icc 1 153 := by
  intro w hw
  obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hw
  simpa [targetN] using t1_edge_weight_mem_target hL e

/-- Actual order-18 formula (25). -/
theorem actual_odd_shared_tail_formula25
    {T : PosIntTree 18} (hL : IsLeech T) (ell : ℕ)
    (hell : 2 ≤ ell) (hell12 : ell ≤ 12) :
    (∑ q ∈ oddSharedFamily T ell, oddBlockDemand T q) ≤
      77 - ell ^ 2 / 2 -
        ((physicalWeightSet T).filter fun w =>
          ell ^ 2 ≤ w ∧ w % 2 = ell % 2).card := by
  have hshared := actual_odd_shared_tail_inequality hL ell hell
  have hcard := order18_punctured_parity_tail_card
    (physicalWeightSet T) ell (physicalWeightSet_order18_subset_target hL)
      hell (by nlinarith)
  simpa [order18OddSharedTail, hcard] using hshared

/-- At order 18 the physical weight set has exactly 17 values. -/
theorem physicalWeightSet_order18_card {T : PosIntTree 18} (hL : IsLeech T) :
    (physicalWeightSet T).card = 17 := by
  rw [physicalWeightSet, Finset.card_image_of_injective _
    (t1_edge_weight_injective hL)]
  have h : Fintype.card T.Edge + 1 = 18 := physicalEdge_card_add_one T
  rw [Finset.card_univ]
  calc
    Fintype.card T.Edge = (Fintype.card T.Edge + 1) - 1 :=
      (Nat.add_sub_cancel (Fintype.card T.Edge) 1).symm
    _ = 18 - 1 := by rw [h]
    _ = 17 := by decide

/-- Formula (26) with `r` defined as the actual number of odd physical
weights. -/
theorem actual_odd_shared_tail_ell_two
    {T : PosIntTree 18} (hL : IsLeech T) :
    (∑ q ∈ oddSharedFamily T 2, oddBlockDemand T q) ≤
      59 + ((physicalWeightSet T).filter Odd).card := by
  have hshared := actual_odd_shared_tail_inequality hL 2 (by omega)
  have htwo : 2 ∈ physicalWeightSet T := by
    obtain ⟨e, he, -⟩ := t1_existsUnique_weight_two hL (by omega)
    exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, he⟩
  have hevenBelow : ∀ w ∈ physicalWeightSet T,
      Even w → w < 4 → w = 2 := by
    intro w hw heven hw4
    have hwpos := (Finset.mem_Icc.mp
      (physicalWeightSet_order18_subset_target hL hw)).1
    have hwmod := Nat.even_iff.mp heven
    omega
  have hcard := order18_even_tail_at_two
    (physicalWeightSet T) ((physicalWeightSet T).filter Odd |>.card)
    (physicalWeightSet_order18_subset_target hL)
    (physicalWeightSet_order18_card hL) rfl htwo hevenBelow
  simpa [order18OddSharedTail, hcard] using hshared

/-- Formula (27) for the actual physical set. -/
theorem actual_odd_shared_tail_ell_three
    {T : PosIntTree 18} (hL : IsLeech T) :
    (∑ q ∈ oddSharedFamily T 3, oddBlockDemand T q) ≤
      73 - ((physicalWeightSet T).filter fun w => 9 ≤ w ∧ Odd w).card := by
  have hshared := actual_odd_shared_tail_inequality hL 3 (by omega)
  have hcard := order18_odd_tail_at_three
    (physicalWeightSet T) (physicalWeightSet_order18_subset_target hL)
  simpa [order18OddSharedTail, hcard] using hshared

/-! ## Strictness witness for the shared relaxation -/

def strictnessTail : Finset ℕ := {144, 146, 148, 150, 152}

namespace SharedTailStrictness

open SimpleGraph

/-- The report's actual sixteen-component quotient topology: a path
`0--...--10`, three leaves at `0`, and two leaves at `10`. -/
def edgeSet : Set (Sym2 (Fin 16)) :=
  {s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 5),
   s(5, 6), s(6, 7), s(7, 8), s(8, 9), s(9, 10),
   s(0, 11), s(0, 12), s(0, 13), s(10, 14), s(10, 15)}

def graph : SimpleGraph (Fin 16) := SimpleGraph.fromEdgeSet edgeSet

private theorem edgeSet_not_isDiag {e : Sym2 (Fin 16)}
    (he : e ∈ edgeSet) : ¬ e.IsDiag := by
  simp only [edgeSet, Set.mem_insert_iff, Set.mem_singleton_iff] at he
  rcases he with
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl) <;> decide

private theorem graph_edgeSet : graph.edgeSet = edgeSet := by
  rw [graph, SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  constructor
  · exact fun he => he.1
  · intro he
    exact ⟨he, edgeSet_not_isDiag he⟩

private theorem edgeSet_ncard : edgeSet.ncard = 15 := by
  simp [edgeSet]

private theorem graph_connected : graph.Connected := by
  have h01 : graph.Reachable 0 1 :=
    SimpleGraph.Adj.reachable (by simp [graph, edgeSet])
  have h02 : graph.Reachable 0 2 := h01.trans <|
    SimpleGraph.Adj.reachable (by simp [graph, edgeSet])
  have h03 : graph.Reachable 0 3 := h02.trans <|
    SimpleGraph.Adj.reachable (by simp [graph, edgeSet])
  have h04 : graph.Reachable 0 4 := h03.trans <|
    SimpleGraph.Adj.reachable (by simp [graph, edgeSet])
  have h05 : graph.Reachable 0 5 := h04.trans <|
    SimpleGraph.Adj.reachable (by simp [graph, edgeSet])
  have h06 : graph.Reachable 0 6 := h05.trans <|
    SimpleGraph.Adj.reachable (by simp [graph, edgeSet])
  have h07 : graph.Reachable 0 7 := h06.trans <|
    SimpleGraph.Adj.reachable (by simp [graph, edgeSet])
  have h08 : graph.Reachable 0 8 := h07.trans <|
    SimpleGraph.Adj.reachable (by simp [graph, edgeSet])
  have h09 : graph.Reachable 0 9 := h08.trans <|
    SimpleGraph.Adj.reachable (by simp [graph, edgeSet])
  have h10 : graph.Reachable 0 10 := h09.trans <|
    SimpleGraph.Adj.reachable (by simp [graph, edgeSet])
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, ?_⟩
  intro v
  fin_cases v
  · exact SimpleGraph.Reachable.rfl
  · exact h01
  · exact h02
  · exact h03
  · exact h04
  · exact h05
  · exact h06
  · exact h07
  · exact h08
  · exact h09
  · exact h10
  · exact SimpleGraph.Adj.reachable (by simp [graph, edgeSet])
  · exact SimpleGraph.Adj.reachable (by simp [graph, edgeSet])
  · exact SimpleGraph.Adj.reachable (by simp [graph, edgeSet])
  · exact h10.trans (SimpleGraph.Adj.reachable (by simp [graph, edgeSet]))
  · exact h10.trans (SimpleGraph.Adj.reachable (by simp [graph, edgeSet]))

theorem graph_isTree : graph.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨graph_connected, ?_⟩
  rw [_root_.Nat.card_coe_set_eq, graph_edgeSet, edgeSet_ncard, Nat.card_fin]

/-- Unit weights turn quotient graph distance into an actual `PosIntTree`
distance, while the separate component masses below encode order eighteen. -/
def tree : PosIntTree 16 where
  graph := graph
  isTree := graph_isTree
  weight := fun _ => 1
  weight_pos := by intro e; omega

def leftLeaf : Fin 3 → Fin 16 := ![11, 12, 13]
def rightLeaf : Fin 2 → Fin 16 := ![14, 15]

@[simp] theorem leftLeaf_adj_zero (i : Fin 3) :
    graph.Adj (leftLeaf i) 0 := by
  fin_cases i <;> simp [leftLeaf, graph, edgeSet]

@[simp] theorem ten_adj_rightLeaf (j : Fin 2) :
    graph.Adj 10 (rightLeaf j) := by
  fin_cases j <;> simp [rightLeaf, graph, edgeSet]

/-- The unique displayed leaf-to-leaf route in the actual quotient tree. -/
def routeWalk (z : Fin 3 × Fin 2) :
    graph.Walk (leftLeaf z.1) (rightLeaf z.2) :=
  .cons (leftLeaf_adj_zero z.1)
    (.cons (by simp [graph, edgeSet] : graph.Adj 0 1)
      (.cons (by simp [graph, edgeSet] : graph.Adj 1 2)
        (.cons (by simp [graph, edgeSet] : graph.Adj 2 3)
          (.cons (by simp [graph, edgeSet] : graph.Adj 3 4)
            (.cons (by simp [graph, edgeSet] : graph.Adj 4 5)
              (.cons (by simp [graph, edgeSet] : graph.Adj 5 6)
                (.cons (by simp [graph, edgeSet] : graph.Adj 6 7)
                  (.cons (by simp [graph, edgeSet] : graph.Adj 7 8)
                    (.cons (by simp [graph, edgeSet] : graph.Adj 8 9)
                      (.cons (by simp [graph, edgeSet] : graph.Adj 9 10)
                        (.cons (ten_adj_rightLeaf z.2) .nil)))))))))))

def route (z : Fin 3 × Fin 2) :
    graph.Path (leftLeaf z.1) (rightLeaf z.2) :=
  ⟨routeWalk z, by
    rcases z with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      simp [routeWalk, leftLeaf, rightLeaf, SimpleGraph.Walk.isPath_def]⟩

def leafPair (z : Fin 3 × Fin 2) : VertexPair 16 :=
  ⟨(leftLeaf z.1, rightLeaf z.2), by
    rcases z with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> decide⟩

/-- Each of the six displayed component pairs has actual quotient distance
twelve, derived from its path rather than entered as a distance table. -/
theorem leafPair_distance (z : Fin 3 × Fin 2) :
    tree.pairDist (leafPair z) = 12 := by
  change tree.dist (leftLeaf z.1) (rightLeaf z.2) = 12
  calc
    tree.dist (leftLeaf z.1) (rightLeaf z.2) =
        tree.walkWeight (route z).1 :=
      (tree.path_walkWeight_eq_dist (route z)).symm
    _ = 12 := by
      rcases z with ⟨i, j⟩
      fin_cases i <;> fin_cases j <;>
        simp [route, routeWalk, leftLeaf, rightLeaf, PosIntTree.walkWeight,
          PosIntTree.weightOfPair, tree, graph, edgeSet]

/-- Enlarge one nonleaf component of each quotient color from one to two. -/
def mass (v : Fin 16) : ℕ :=
  if v = 0 ∨ v = 1 then 2 else 1

/-- Color zero contains the even vertices of the central path; all attached
leaves lie in color one. -/
def colorZero (v : Fin 16) : Prop := v.1 ≤ 10 ∧ Even v.1

private instance colorZero_decidable (v : Fin 16) : Decidable (colorZero v) := by
  unfold colorZero
  infer_instance

def colorZeroVertices : Finset (Fin 16) :=
  Finset.univ.filter colorZero

def colorOneVertices : Finset (Fin 16) :=
  Finset.univ.filter fun v => ¬ colorZero v

theorem total_mass : (∑ v : Fin 16, mass v) = 18 := by
  decide

theorem color_mass_split :
    (∑ v ∈ colorZeroVertices, mass v) = 7 ∧
      (∑ v ∈ colorOneVertices, mass v) = 11 := by
  decide

theorem leaf_masses (z : Fin 3 × Fin 2) :
    mass (leftLeaf z.1) = 1 ∧ mass (rightLeaf z.2) = 1 := by
  rcases z with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> decide

def leafDemand (z : Fin 3 × Fin 2) : ℕ :=
  mass (leftLeaf z.1) * mass (rightLeaf z.2)

theorem leafDemand_eq_one (z : Fin 3 × Fin 2) : leafDemand z = 1 := by
  rw [leafDemand, (leaf_masses z).1, (leaf_masses z).2]

theorem six_leaf_demands : (∑ z : Fin 3 × Fin 2, leafDemand z) = 6 := by
  simp [leafDemand_eq_one]

/-- Actual quotient-topology strictness bundle: all six distance-twelve leaf
pairs separately fit the five-rank tail, but their joint demand does not. -/
theorem actual_quotient_shared_tail_strictness :
    graph.IsTree ∧
    (∑ v : Fin 16, mass v) = 18 ∧
    (∑ v ∈ colorZeroVertices, mass v) = 7 ∧
    (∑ v ∈ colorOneVertices, mass v) = 11 ∧
    (∀ z : Fin 3 × Fin 2,
      tree.pairDist (leafPair z) = 12 ∧
      leafDemand z = 1 ∧ leafDemand z ≤ strictnessTail.card) ∧
    (∑ z : Fin 3 × Fin 2, leafDemand z) = 6 ∧
    strictnessTail.card = 5 ∧
    ¬ ((∑ z : Fin 3 × Fin 2, leafDemand z) ≤ strictnessTail.card) := by
  refine ⟨graph_isTree, total_mass, color_mass_split.1,
    color_mass_split.2, ?_, six_leaf_demands, by decide, ?_⟩
  · intro z
    refine ⟨leafPair_distance z, leafDemand_eq_one z, ?_⟩
    rw [leafDemand_eq_one]
    decide
  · rw [six_leaf_demands]
    decide

end SharedTailStrictness

/-- Six individually feasible unit demands compete for only five common
even ranks.  This is the exact abstract strictness statement attached to the
16-component quotient construction in the report. -/
theorem shared_tail_strictness_witness :
    (∀ _z : Fin 3 × Fin 2, 1 ≤ strictnessTail.card) ∧
    (∑ _z : Fin 3 × Fin 2, 1) = 6 ∧
    strictnessTail.card = 5 ∧
    ¬ ((∑ _z : Fin 3 × Fin 2, 1) ≤ strictnessTail.card) := by
  decide

end

end LeechTrees.PathMulticut
