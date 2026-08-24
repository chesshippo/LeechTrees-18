import LeechTrees.OddQuotient.PairPartition
import LeechTrees.ParityTail
import LeechTrees.QHop.Kernel

/-!
# Odd-quotient capacity and exact signed-moment merges

This module formalizes G008 and the G024(a) correction.  The quotient
capacity endpoint is attached to an actual order-18 `IsLeech` distance map.
For an actual pair of F9 even components, all route information is computed
from the canonical path in the odd-edge quotient.  Its bridge weights are
transported through the exact quotient-edge equivalence; positivity,
oddness, distinctness, the route lower bound, parity, and the named-pair
injection are all derived from current graph APIs.  The capacity, diameter,
and weight-one conclusions are therefore conclusions rather than fields.
-/

open scoped BigOperators

namespace LeechTrees.OddCapacity

open LeechTrees.Foundation
open LeechTrees.ParityTail
open LeechTrees.OddQuotient

noncomputable section

theorem sum_first_odds (ell : ℕ) :
    (∑ j ∈ Finset.range ell, (1 + 2 * j)) = ell ^ 2 := by
  induction ell with
  | zero => simp
  | succ ell ih =>
      rw [Finset.sum_range_succ, ih]
      ring

theorem sum_odd_tail_without_one (ell : ℕ) :
    (∑ j ∈ Finset.range ell, (3 + 2 * j)) = ell * (ell + 2) := by
  induction ell with
  | zero => simp
  | succ ell ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Distinct positive odd integers have sum at least `ell^2`. -/
theorem distinct_positive_odd_sum_ge_square
    (S : Finset ℕ) (ell : ℕ) (hcard : S.card = ell)
    (hpositive : ∀ w ∈ S, 0 < w) (hodd : ∀ w ∈ S, Odd w) :
    ell ^ 2 ≤ ∑ w ∈ S, w := by
  have hspacing := parity_spacing_lower_moment S 1 1 ell 1
    (by omega) hcard
    (fun w hw => hpositive w hw)
    (fun w hw => Nat.odd_iff.mp (hodd w hw))
  simpa [parityStart, sum_first_odds] using hspacing

/-- If weight one is absent, the corresponding sharp lower bound is
`3+5+...+(2 ell+1)=ell(ell+2)`. -/
theorem distinct_positive_odd_sum_ge_without_one
    (S : Finset ℕ) (ell : ℕ) (hcard : S.card = ell)
    (hpositive : ∀ w ∈ S, 0 < w) (hodd : ∀ w ∈ S, Odd w)
    (hone : 1 ∉ S) :
    ell * (ell + 2) ≤ ∑ w ∈ S, w := by
  have hlower : ∀ w ∈ S, 3 ≤ w := by
    intro w hw
    have hwpos := hpositive w hw
    have hwodd := Nat.odd_iff.mp (hodd w hw)
    have hwne : w ≠ 1 := fun h => hone (h ▸ hw)
    omega
  have hspacing := parity_spacing_lower_moment S 3 1 ell 1
    (by omega) hcard hlower
    (fun w hw => Nat.odd_iff.mp (hodd w hw))
  simpa [parityStart, sum_odd_tail_without_one] using hspacing

/-! ## Actual F9 quotient-path adapter -/

/-- Weight of an actual quotient edge, transported back through the exact
odd-bridge/quotient-edge equivalence.  The value off the quotient edge set is
irrelevant and is set to zero only so the function can map a walk's edge
list. -/
noncomputable def quotientWeightOfPair {n : ℕ} (T : PosIntTree n)
    (e : Sym2 (EvenComponent T)) : ℕ := by
  classical
  exact if h : e ∈ (quotientGraph T).edgeSet then
      T.weight (((oddBridgeQuotientEdgeEquiv T).symm ⟨e, h⟩).1)
    else 0

@[simp] theorem quotientWeightOfPair_of_edge {n : ℕ}
    (T : PosIntTree n) (e : (quotientGraph T).edgeSet) :
    quotientWeightOfPair T e.1 =
      T.weight (((oddBridgeQuotientEdgeEquiv T).symm e).1) := by
  classical
  simp [quotientWeightOfPair]

theorem quotientWeightOfPair_of_adj {n : ℕ} (T : PosIntTree n)
    {C D : EvenComponent T} (h : (quotientGraph T).Adj C D) :
    quotientWeightOfPair T s(C, D) =
      T.weight (orientedBridgeOfAdj T h).bridge.1 := by
  let qe : (quotientGraph T).edgeSet := ⟨s(C, D), by
    rw [SimpleGraph.mem_edgeSet]
    exact h⟩
  let b := orientedBridgeOfAdj T h
  have hb : (oddBridgeQuotientEdgeEquiv T).symm qe = b.bridge := by
    apply (oddBridgeQuotientEdgeEquiv T).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    exact b.component_pair.symm
  simpa [qe, b, hb] using quotientWeightOfPair_of_edge T qe

/-- The actual odd physical weights encountered by a quotient walk. -/
noncomputable def quotientWalkWeightList {n : ℕ} (T : PosIntTree n)
    {C D : EvenComponent T} (p : (quotientGraph T).Walk C D) : List ℕ :=
  p.edges.map (quotientWeightOfPair T)

theorem quotientWalkWeightList_length {n : ℕ} (T : PosIntTree n)
    {C D : EvenComponent T} (p : (quotientGraph T).Walk C D) :
    (quotientWalkWeightList T p).length = p.length := by
  simp [quotientWalkWeightList]

theorem quotientWalkWeightList_positive {n : ℕ} (T : PosIntTree n)
    {C D : EvenComponent T} (p : (quotientGraph T).Walk C D) :
    ∀ w ∈ quotientWalkWeightList T p, 0 < w := by
  intro w hw
  rw [quotientWalkWeightList, List.mem_map] at hw
  obtain ⟨e, he, rfl⟩ := hw
  let qe : (quotientGraph T).edgeSet :=
    ⟨e, p.edges_subset_edgeSet he⟩
  have hpos := T.weight_pos (((oddBridgeQuotientEdgeEquiv T).symm qe).1)
  change 0 < quotientWeightOfPair T qe.1
  rw [quotientWeightOfPair_of_edge]
  exact hpos

theorem quotientWalkWeightList_odd {n : ℕ} (T : PosIntTree n)
    {C D : EvenComponent T} (p : (quotientGraph T).Walk C D) :
    ∀ w ∈ quotientWalkWeightList T p, Odd w := by
  intro w hw
  rw [quotientWalkWeightList, List.mem_map] at hw
  obtain ⟨e, he, rfl⟩ := hw
  let qe : (quotientGraph T).edgeSet :=
    ⟨e, p.edges_subset_edgeSet he⟩
  have hodd := ((oddBridgeQuotientEdgeEquiv T).symm qe).2
  change Odd (quotientWeightOfPair T qe.1)
  rw [quotientWeightOfPair_of_edge]
  exact hodd

theorem quotientPathWeightList_nodup {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) {C D : EvenComponent T}
    (p : (quotientGraph T).Path C D) :
    (quotientWalkWeightList T p.1).Nodup := by
  unfold quotientWalkWeightList
  apply (List.nodup_map_iff_inj_on p.2.isTrail.edges_nodup).2
  intro e he f hf hw
  let qe : (quotientGraph T).edgeSet :=
    ⟨e, p.1.edges_subset_edgeSet he⟩
  let qf : (quotientGraph T).edgeSet :=
    ⟨f, p.1.edges_subset_edgeSet hf⟩
  let be := (oddBridgeQuotientEdgeEquiv T).symm qe
  let bf := (oddBridgeQuotientEdgeEquiv T).symm qf
  have hweights : T.weight be.1 = T.weight bf.1 := by
    change quotientWeightOfPair T qe.1 = quotientWeightOfPair T qf.1 at hw
    rw [quotientWeightOfPair_of_edge, quotientWeightOfPair_of_edge] at hw
    exact hw
  have hedges : be.1 = bf.1 := t1_edge_weight_injective hL hweights
  have hbridges : be = bf := Subtype.ext hedges
  have hquotient : qe = qf :=
    (oddBridgeQuotientEdgeEquiv T).symm.injective hbridges
  exact congrArg Subtype.val hquotient

/-- The sum of the actual bridge weights is bounded by the exact route
distance.  This is derived from the existing recursive route formula; no
route lower bound is accepted as input. -/
theorem quotientWalkWeightList_sum_le_route {n : ℕ} (T : PosIntTree n)
    {C D : EvenComponent T} (p : (quotientGraph T).Walk C D)
    (x : ComponentVertex T C) (y : ComponentVertex T D) :
    (quotientWalkWeightList T p).sum ≤
      2 * routeCost T p x y + p.length := by
  induction p with
  | nil => simp [quotientWalkWeightList]
  | @cons C D E h p ih =>
      have htail := ih (orientedBridgeOfAdj T h).targetPort y
      have hweight := bridge_weight_eq_two_mul_half_add_one T
        (orientedBridgeOfAdj T h).bridge
      rw [routeCost_cons]
      simp only [quotientWalkWeightList, SimpleGraph.Walk.edges_cons,
        List.map_cons, List.sum_cons, SimpleGraph.Walk.length_cons]
      rw [quotientWeightOfPair_of_adj]
      change T.weight (orientedBridgeOfAdj T h).bridge.1 +
          (quotientWalkWeightList T p).sum ≤
        2 * (rho T x (orientedBridgeOfAdj T h).sourcePort +
          bridgeHalfWeight T (orientedBridgeOfAdj T h).bridge +
          routeCost T p (orientedBridgeOfAdj T h).targetPort y) +
          (p.length + 1)
      rw [hweight]
      omega

namespace ActualComponentPair

variable {T : PosIntTree 18} (q : QuotientComponentPair T)

/-- Number of actual odd quotient edges separating the two components. -/
def ell : ℕ := (quotientPath T q.left q.right).1.length

/-- Exact list and set of odd physical bridge weights on the canonical
quotient path. -/
noncomputable def bridgeWeightList : List ℕ :=
  quotientWalkWeightList T (quotientPath T q.left q.right).1

noncomputable def bridgeWeightSet : Finset ℕ := (bridgeWeightList q).toFinset

/-- Actual injection of the Cartesian component block into global unordered
named-vertex pairs, obtained from the F9 pair partition equivalence. -/
noncomputable def pairIndex :
    (ComponentVertex T q.left × ComponentVertex T q.right) ↪ VertexPair 18 where
  toFun x := indexToPair T (.inr ⟨q, x⟩)
  inj' := by
    intro x y hxy
    have hsum :
        (Sum.inr ⟨q, x⟩ : WithinIndex T ⊕ CrossIndex T) =
          Sum.inr ⟨q, y⟩ :=
      (vertexPairIndexEquiv T).symm.injective hxy
    have hsigma : (⟨q, x⟩ : CrossIndex T) = ⟨q, y⟩ :=
      Sum.inr.inj hsum
    cases hsigma
    rfl

theorem pairDist_pairIndex
    (x : ComponentVertex T q.left × ComponentVertex T q.right) :
    T.pairDist (pairIndex q x) = T.dist x.1.1 x.2.1 := by
  change T.pairDist (indexToPair T (.inr ⟨q, x⟩)) = _
  unfold indexToPair
  exact T.pairDist_pairOfDistinct _ _ _

/-- Actual distance-value block of the named component pair. -/
noncomputable def crossDistances : Finset ℕ :=
  Finset.univ.image fun x => T.pairDist (pairIndex q x)

theorem bridgeWeightList_length : (bridgeWeightList q).length = ell q := by
  exact quotientWalkWeightList_length T (quotientPath T q.left q.right).1

theorem bridgeWeightList_nodup (hL : IsLeech T) :
    (bridgeWeightList q).Nodup :=
  quotientPathWeightList_nodup hL (quotientPath T q.left q.right)

theorem bridgeWeightList_positive : ∀ w ∈ bridgeWeightList q, 0 < w :=
  quotientWalkWeightList_positive T (quotientPath T q.left q.right).1

theorem bridgeWeightList_odd : ∀ w ∈ bridgeWeightList q, Odd w :=
  quotientWalkWeightList_odd T (quotientPath T q.left q.right).1

theorem bridgeWeightSet_card (hL : IsLeech T) :
    (bridgeWeightSet q).card = ell q := by
  rw [bridgeWeightSet,
    List.toFinset_card_of_nodup (bridgeWeightList_nodup q hL),
    bridgeWeightList_length q]

theorem bridgeWeightSet_positive : ∀ w ∈ bridgeWeightSet q, 0 < w := by
  intro w hw
  exact bridgeWeightList_positive q w (by simpa [bridgeWeightSet] using hw)

theorem bridgeWeightSet_odd : ∀ w ∈ bridgeWeightSet q, Odd w := by
  intro w hw
  exact bridgeWeightList_odd q w (by simpa [bridgeWeightSet] using hw)

theorem bridgeWeightSet_sum_eq (hL : IsLeech T) :
    (∑ w ∈ bridgeWeightSet q, w) = (bridgeWeightList q).sum := by
  simpa [bridgeWeightSet] using
    (List.sum_toFinset id (bridgeWeightList_nodup q hL))

theorem bridge_sum_ge_square (hL : IsLeech T) :
    ell q ^ 2 ≤ ∑ w ∈ bridgeWeightSet q, w :=
  distinct_positive_odd_sum_ge_square (bridgeWeightSet q) (ell q)
    (bridgeWeightSet_card q hL) (bridgeWeightSet_positive q)
      (bridgeWeightSet_odd q)

theorem bridge_sum_le_pairDist (hL : IsLeech T)
    (x : ComponentVertex T q.left × ComponentVertex T q.right) :
    (∑ w ∈ bridgeWeightSet q, w) ≤ T.pairDist (pairIndex q x) := by
  rw [bridgeWeightSet_sum_eq q hL, pairDist_pairIndex q]
  have hroute := quotientWalkWeightList_sum_le_route T
    (quotientPath T q.left q.right).1 x.1 x.2
  have hdist := dist_eq_two_mul_routeCost_add_length T
    (quotientPath T q.left q.right).1
    (quotientPath T q.left q.right).2 x.1 x.2
  rw [hdist]
  exact hroute

theorem pairDist_mod_two
    (x : ComponentVertex T q.left × ComponentVertex T q.right) :
    T.pairDist (pairIndex q x) % 2 = ell q % 2 := by
  rw [pairDist_pairIndex q]
  have hdist := dist_eq_two_mul_canonicalRouteHalfRank_add_mod T x.1 x.2
  rw [hdist]
  unfold ell
  omega

theorem crossDistances_card (hL : IsLeech T) :
    (crossDistances q).card =
      Fintype.card (ComponentVertex T q.left) *
        Fintype.card (ComponentVertex T q.right) := by
  calc
    (crossDistances q).card =
        Fintype.card
          (ComponentVertex T q.left × ComponentVertex T q.right) := by
      apply Finset.card_image_of_injective
      intro x y hxy
      exact (pairIndex q).injective (hL.pairDist_injective hxy)
    _ = Fintype.card (ComponentVertex T q.left) *
        Fintype.card (ComponentVertex T q.right) := Fintype.card_prod _ _

theorem crossDistances_subset_square_parity_tail (hL : IsLeech T) :
    crossDistances q ⊆ parityTail 153 (ell q ^ 2) (ell q % 2) := by
  intro d hd
  rcases Finset.mem_image.mp hd with ⟨x, -, rfl⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, pairDist_mod_two q x⟩
  · exact (bridge_sum_ge_square q hL).trans (bridge_sum_le_pairDist q hL x)
  · have htarget := hL.pairDist_le_target (pairIndex q x)
    norm_num [targetN] at htarget ⊢
    exact htarget

/-- Pairwise odd-quotient distance capacity before evaluating the tail. -/
theorem distance_capacity_tail (hL : IsLeech T) :
    Fintype.card (ComponentVertex T q.left) *
      Fintype.card (ComponentVertex T q.right) ≤
      (parityTail 153 (ell q ^ 2) (ell q % 2)).card := by
  rw [← crossDistances_card q hL]
  exact Finset.card_le_card (crossDistances_subset_square_parity_tail q hL)

theorem square_parity_tail_card (ell : ℕ) (hell : ell ≤ 12) :
    (parityTail 153 (ell ^ 2) (ell % 2)).card =
      77 - ell ^ 2 / 2 := by
  interval_cases ell <;> decide

/-- Quotient diameter at order 18 is at most twelve. -/
theorem quotient_distance_le_twelve (hL : IsLeech T) : ell q ≤ 12 := by
  let x : ComponentVertex T q.left × ComponentVertex T q.right :=
    (⟨componentRep T q.left, componentOf_componentRep T q.left⟩,
      ⟨componentRep T q.right, componentOf_componentRep T q.right⟩)
  have hlower := (bridge_sum_ge_square q hL).trans
    (bridge_sum_le_pairDist q hL x)
  have hupper := hL.pairDist_le_target (pairIndex q x)
  norm_num [targetN, Nat.choose] at hupper
  nlinarith

/-- The audited order-18 pairwise capacity
`m_i m_j ≤ 77-floor(ell^2/2)`. -/
theorem order18_distance_capacity (hL : IsLeech T) :
    Fintype.card (ComponentVertex T q.left) *
      Fintype.card (ComponentVertex T q.right) ≤
      77 - ell q ^ 2 / 2 := by
  rw [← square_parity_tail_card (ell q) (quotient_distance_le_twelve q hL)]
  exact distance_capacity_tail q hL

/-- Every length-twelve odd-quotient path contains physical weight one. -/
theorem length_twelve_contains_weight_one
    (hL : IsLeech T) (hell : ell q = 12) :
    1 ∈ bridgeWeightSet q := by
  by_contra hone
  have hlower := distinct_positive_odd_sum_ge_without_one
    (bridgeWeightSet q) (ell q) (bridgeWeightSet_card q hL)
      (bridgeWeightSet_positive q) (bridgeWeightSet_odd q) hone
  let x : ComponentVertex T q.left × ComponentVertex T q.right :=
    (⟨componentRep T q.left, componentOf_componentRep T q.left⟩,
      ⟨componentRep T q.right, componentOf_componentRep T q.right⟩)
  have hroute := bridge_sum_le_pairDist q hL x
  have hupper := hL.pairDist_le_target (pairIndex q x)
  norm_num [targetN, Nat.choose] at hupper
  rw [hell] at hlower
  norm_num at hlower
  omega

end ActualComponentPair

/-! ## G024(a): exact correction to the reversed below-`q_2` inference -/

/-- A value is the semantic second odd physical rank when it is attained by
an odd physical edge, weight one is attained, and it is a lower bound for
every non-unit odd physical edge. -/
def IsSecondOddPhysicalRank {n : ℕ} (T : PosIntTree n) (q : ℕ) : Prop :=
  (∃ e : T.Edge, Odd (T.weight e) ∧ T.weight e = q) ∧
  q ≠ 1 ∧
  (∃ e : T.Edge, T.weight e = 1) ∧
  ∀ e : T.Edge, Odd (T.weight e) → T.weight e ≠ 1 → q ≤ T.weight e

namespace ArchivedOrder6

open SimpleGraph

/-- The audited five-edge topology, with vertices `0,...,5` representing the
paper labels `1,...,6`. -/
def edgeSet : Set (Sym2 (Fin 6)) :=
  {s(0, 1), s(0, 2), s(0, 5), s(5, 3), s(5, 4)}

def graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet edgeSet

private theorem graph_connected : graph.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨(0 : Fin 6), ?_⟩
  intro v
  fin_cases v
  · exact SimpleGraph.Reachable.rfl
  · exact SimpleGraph.Adj.reachable (by simp [graph, edgeSet])
  · exact SimpleGraph.Adj.reachable (by simp [graph, edgeSet])
  · exact
      (SimpleGraph.Adj.reachable
        (show graph.Adj (0 : Fin 6) 5 by simp [graph, edgeSet])).trans
      (SimpleGraph.Adj.reachable
        (show graph.Adj (5 : Fin 6) 3 by simp [graph, edgeSet]))
  · exact
      (SimpleGraph.Adj.reachable
        (show graph.Adj (0 : Fin 6) 5 by simp [graph, edgeSet])).trans
      (SimpleGraph.Adj.reachable
        (show graph.Adj (5 : Fin 6) 4 by simp [graph, edgeSet]))
  · exact SimpleGraph.Adj.reachable (by simp [graph, edgeSet])

@[simp] private theorem graph_edgeSet : graph.edgeSet = edgeSet := by
  rw [graph, SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  simp only [Set.mem_diff, Set.mem_setOf_eq]
  constructor
  · exact And.left
  · intro he
    refine ⟨he, ?_⟩
    simp only [edgeSet, Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with h | h | h | h | h <;> subst e <;> decide

private theorem graph_isTree : graph.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨graph_connected, ?_⟩
  rw [graph_edgeSet]
  simp [edgeSet,
    show s((0 : Fin 6), (1 : Fin 6)) ≠ s((0 : Fin 6), (2 : Fin 6)) by decide,
    show s((0 : Fin 6), (1 : Fin 6)) ≠ s((0 : Fin 6), (5 : Fin 6)) by decide,
    show s((0 : Fin 6), (1 : Fin 6)) ≠ s((5 : Fin 6), (3 : Fin 6)) by decide,
    show s((0 : Fin 6), (1 : Fin 6)) ≠ s((5 : Fin 6), (4 : Fin 6)) by decide,
    show s((0 : Fin 6), (2 : Fin 6)) ≠ s((0 : Fin 6), (5 : Fin 6)) by decide,
    show s((0 : Fin 6), (2 : Fin 6)) ≠ s((5 : Fin 6), (3 : Fin 6)) by decide,
    show s((0 : Fin 6), (2 : Fin 6)) ≠ s((5 : Fin 6), (4 : Fin 6)) by decide,
    show s((0 : Fin 6), (5 : Fin 6)) ≠ s((5 : Fin 6), (3 : Fin 6)) by decide,
    show s((0 : Fin 6), (5 : Fin 6)) ≠ s((5 : Fin 6), (4 : Fin 6)) by decide,
    show s((5 : Fin 6), (3 : Fin 6)) ≠ s((5 : Fin 6), (4 : Fin 6)) by decide]

/-- The audited edge assignment
`12(1),13(2),16(5),46(4),56(8)`. -/
def rawWeight (e : Sym2 (Fin 6)) : ℕ :=
  if e = s(0, 1) then 1
  else if e = s(0, 2) then 2
  else if e = s(0, 5) then 5
  else if e = s(5, 3) then 4
  else if e = s(5, 4) then 8
  else 1

/-- The explicit archived positive integral weighted tree. -/
def tree : PosIntTree 6 where
  graph := graph
  isTree := graph_isTree
  weight e := rawWeight e.1
  weight_pos := by
    intro e
    by_cases h01 : e.1 = s(0, 1) <;>
      by_cases h02 : e.1 = s(0, 2) <;>
      by_cases h05 : e.1 = s(0, 5) <;>
      by_cases h53 : e.1 = s(5, 3) <;>
      by_cases h54 : e.1 = s(5, 4) <;>
      simp [rawWeight, h01, h02, h05, h53, h54]

private theorem adj01 : graph.Adj 0 1 := by simp [graph, edgeSet]
private theorem adj02 : graph.Adj 0 2 := by simp [graph, edgeSet]
private theorem adj05 : graph.Adj 0 5 := by simp [graph, edgeSet]
private theorem adj53 : graph.Adj 5 3 := by simp [graph, edgeSet]
private theorem adj54 : graph.Adj 5 4 := by simp [graph, edgeSet]

private def e01 : tree.Edge := ⟨s(0, 1), by
  rw [SimpleGraph.mem_edgeSet]
  exact adj01⟩
private def e02 : tree.Edge := ⟨s(0, 2), by
  rw [SimpleGraph.mem_edgeSet]
  exact adj02⟩
private def e05 : tree.Edge := ⟨s(0, 5), by
  rw [SimpleGraph.mem_edgeSet]
  exact adj05⟩
private def e53 : tree.Edge := ⟨s(5, 3), by
  rw [SimpleGraph.mem_edgeSet]
  exact adj53⟩
private def e54 : tree.Edge := ⟨s(5, 4), by
  rw [SimpleGraph.mem_edgeSet]
  exact adj54⟩

@[simp] private theorem weightOfPair_01 : tree.weightOfPair s(0, 1) = 1 := by
  rw [show s(0, 1) = e01.1 from rfl, tree.weightOfPair_edge]
  simp [tree, rawWeight, e01]

@[simp] private theorem weightOfPair_02 : tree.weightOfPair s(0, 2) = 2 := by
  rw [show s(0, 2) = e02.1 from rfl, tree.weightOfPair_edge]
  simp [tree, rawWeight, e02]

@[simp] private theorem weightOfPair_05 : tree.weightOfPair s(0, 5) = 5 := by
  rw [show s(0, 5) = e05.1 from rfl, tree.weightOfPair_edge]
  simp [tree, rawWeight, e05]

@[simp] private theorem weightOfPair_53 : tree.weightOfPair s(5, 3) = 4 := by
  rw [show s(5, 3) = e53.1 from rfl, tree.weightOfPair_edge]
  simp [tree, rawWeight, e53]

@[simp] private theorem weightOfPair_54 : tree.weightOfPair s(5, 4) = 8 := by
  rw [show s(5, 4) = e54.1 from rfl, tree.weightOfPair_edge]
  simp [tree, rawWeight, e54]

@[simp] private theorem weightOfPair_35 : tree.weightOfPair s(3, 5) = 4 := by
  rw [Sym2.eq_swap]
  exact weightOfPair_53

@[simp] private theorem weightOfPair_45 : tree.weightOfPair s(4, 5) = 8 := by
  rw [Sym2.eq_swap]
  exact weightOfPair_54

private def path01 : graph.Path 0 1 :=
  ⟨.cons adj01 .nil, by simp [SimpleGraph.Walk.isPath_def]⟩
private def path02 : graph.Path 0 2 :=
  ⟨.cons adj02 .nil, by simp [SimpleGraph.Walk.isPath_def]⟩
private def path03 : graph.Path 0 3 :=
  ⟨.cons adj05 (.cons adj53 .nil), by simp [SimpleGraph.Walk.isPath_def]⟩
private def path04 : graph.Path 0 4 :=
  ⟨.cons adj05 (.cons adj54 .nil), by simp [SimpleGraph.Walk.isPath_def]⟩
private def path05 : graph.Path 0 5 :=
  ⟨.cons adj05 .nil, by simp [SimpleGraph.Walk.isPath_def]⟩
private def path12 : graph.Path 1 2 :=
  ⟨.cons adj01.symm (.cons adj02 .nil), by simp [SimpleGraph.Walk.isPath_def]⟩
private def path13 : graph.Path 1 3 :=
  ⟨.cons adj01.symm (.cons adj05 (.cons adj53 .nil)),
    by simp [SimpleGraph.Walk.isPath_def]⟩
private def path14 : graph.Path 1 4 :=
  ⟨.cons adj01.symm (.cons adj05 (.cons adj54 .nil)),
    by simp [SimpleGraph.Walk.isPath_def]⟩
private def path15 : graph.Path 1 5 :=
  ⟨.cons adj01.symm (.cons adj05 .nil), by simp [SimpleGraph.Walk.isPath_def]⟩
private def path23 : graph.Path 2 3 :=
  ⟨.cons adj02.symm (.cons adj05 (.cons adj53 .nil)),
    by simp [SimpleGraph.Walk.isPath_def]⟩
private def path24 : graph.Path 2 4 :=
  ⟨.cons adj02.symm (.cons adj05 (.cons adj54 .nil)),
    by simp [SimpleGraph.Walk.isPath_def]⟩
private def path25 : graph.Path 2 5 :=
  ⟨.cons adj02.symm (.cons adj05 .nil), by simp [SimpleGraph.Walk.isPath_def]⟩
private def path34 : graph.Path 3 4 :=
  ⟨.cons adj53.symm (.cons adj54 .nil), by simp [SimpleGraph.Walk.isPath_def]⟩
private def path35 : graph.Path 3 5 :=
  ⟨.cons adj53.symm .nil, by simp [SimpleGraph.Walk.isPath_def]⟩
private def path45 : graph.Path 4 5 :=
  ⟨.cons adj54.symm .nil, by simp [SimpleGraph.Walk.isPath_def]⟩

private theorem pairDist_eq_walkWeight {u v : Fin 6} (huv : u < v)
    (p : graph.Path u v) :
    tree.pairDist (⟨(u, v), huv⟩ : VertexPair 6) = tree.walkWeight p.1 := by
  change tree.dist u v = tree.walkWeight p.1
  exact (tree.path_walkWeight_eq_dist p).symm

@[simp] theorem pairDist_01 :
    tree.pairDist (⟨(0, 1), by decide⟩ : VertexPair 6) = 1 := by
  rw [pairDist_eq_walkWeight (by decide) path01]
  simp [PosIntTree.walkWeight, path01]

@[simp] theorem pairDist_02 :
    tree.pairDist (⟨(0, 2), by decide⟩ : VertexPair 6) = 2 := by
  rw [pairDist_eq_walkWeight (by decide) path02]
  simp [PosIntTree.walkWeight, path02]

@[simp] theorem pairDist_03 :
    tree.pairDist (⟨(0, 3), by decide⟩ : VertexPair 6) = 9 := by
  rw [pairDist_eq_walkWeight (by decide) path03]
  simp [PosIntTree.walkWeight, path03]

@[simp] theorem pairDist_04 :
    tree.pairDist (⟨(0, 4), by decide⟩ : VertexPair 6) = 13 := by
  rw [pairDist_eq_walkWeight (by decide) path04]
  simp [PosIntTree.walkWeight, path04]

@[simp] theorem pairDist_05 :
    tree.pairDist (⟨(0, 5), by decide⟩ : VertexPair 6) = 5 := by
  rw [pairDist_eq_walkWeight (by decide) path05]
  simp [PosIntTree.walkWeight, path05]

@[simp] theorem pairDist_12 :
    tree.pairDist (⟨(1, 2), by decide⟩ : VertexPair 6) = 3 := by
  rw [pairDist_eq_walkWeight (by decide) path12]
  simp [PosIntTree.walkWeight, path12, Sym2.eq_swap]

@[simp] theorem pairDist_13 :
    tree.pairDist (⟨(1, 3), by decide⟩ : VertexPair 6) = 10 := by
  rw [pairDist_eq_walkWeight (by decide) path13]
  simp [PosIntTree.walkWeight, path13, Sym2.eq_swap]

@[simp] theorem pairDist_14 :
    tree.pairDist (⟨(1, 4), by decide⟩ : VertexPair 6) = 14 := by
  rw [pairDist_eq_walkWeight (by decide) path14]
  simp [PosIntTree.walkWeight, path14, Sym2.eq_swap]

@[simp] theorem pairDist_15 :
    tree.pairDist (⟨(1, 5), by decide⟩ : VertexPair 6) = 6 := by
  rw [pairDist_eq_walkWeight (by decide) path15]
  simp [PosIntTree.walkWeight, path15, Sym2.eq_swap]

@[simp] theorem pairDist_23 :
    tree.pairDist (⟨(2, 3), by decide⟩ : VertexPair 6) = 11 := by
  rw [pairDist_eq_walkWeight (by decide) path23]
  simp [PosIntTree.walkWeight, path23, Sym2.eq_swap]

@[simp] theorem pairDist_24 :
    tree.pairDist (⟨(2, 4), by decide⟩ : VertexPair 6) = 15 := by
  rw [pairDist_eq_walkWeight (by decide) path24]
  simp [PosIntTree.walkWeight, path24, Sym2.eq_swap]

@[simp] theorem pairDist_25 :
    tree.pairDist (⟨(2, 5), by decide⟩ : VertexPair 6) = 7 := by
  rw [pairDist_eq_walkWeight (by decide) path25]
  simp [PosIntTree.walkWeight, path25, Sym2.eq_swap]

@[simp] theorem pairDist_34 :
    tree.pairDist (⟨(3, 4), by decide⟩ : VertexPair 6) = 12 := by
  rw [pairDist_eq_walkWeight (by decide) path34]
  simp [PosIntTree.walkWeight, path34, Sym2.eq_swap]

@[simp] theorem pairDist_35 :
    tree.pairDist (⟨(3, 5), by decide⟩ : VertexPair 6) = 4 := by
  rw [pairDist_eq_walkWeight (by decide) path35]
  simp [PosIntTree.walkWeight, path35]

@[simp] theorem pairDist_45 :
    tree.pairDist (⟨(4, 5), by decide⟩ : VertexPair 6) = 8 := by
  rw [pairDist_eq_walkWeight (by decide) path45]
  simp [PosIntTree.walkWeight, path45]

/-- Transparent table used only to package the fifteen explicit path
calculations into the indexed spectrum statement. -/
def distanceTable (p : VertexPair 6) : ℕ :=
  if p.left = 0 ∧ p.right = 1 then 1
  else if p.left = 0 ∧ p.right = 2 then 2
  else if p.left = 0 ∧ p.right = 3 then 9
  else if p.left = 0 ∧ p.right = 4 then 13
  else if p.left = 0 ∧ p.right = 5 then 5
  else if p.left = 1 ∧ p.right = 2 then 3
  else if p.left = 1 ∧ p.right = 3 then 10
  else if p.left = 1 ∧ p.right = 4 then 14
  else if p.left = 1 ∧ p.right = 5 then 6
  else if p.left = 2 ∧ p.right = 3 then 11
  else if p.left = 2 ∧ p.right = 4 then 15
  else if p.left = 2 ∧ p.right = 5 then 7
  else if p.left = 3 ∧ p.right = 4 then 12
  else if p.left = 3 ∧ p.right = 5 then 4
  else 8

theorem pairDist_eq_distanceTable (p : VertexPair 6) :
    tree.pairDist p = distanceTable p := by
  rcases p with ⟨⟨u, v⟩, huv⟩
  fin_cases u <;> fin_cases v
  all_goals norm_num at huv
  all_goals simp [distanceTable, VertexPair.left, VertexPair.right]

theorem distanceTable_injective : Function.Injective distanceTable := by decide

theorem distanceTable_mem_target :
    ∀ p : VertexPair 6, distanceTable p ∈ Finset.Icc 1 (targetN 6) := by decide

/-- The explicit archived construction is an actual order-6 Leech tree. -/
theorem isLeech : IsLeech tree := by
  refine ⟨?_, ?_⟩
  · intro p
    rw [pairDist_eq_distanceTable]
    exact distanceTable_mem_target p
  · apply (Fintype.bijective_iff_injective_and_card _).2
    constructor
    · intro p q hpq
      apply distanceTable_injective
      rw [← pairDist_eq_distanceTable p, ← pairDist_eq_distanceTable q]
      exact congrArg Subtype.val hpq
    · exact (by decide)

/-- Full spectrum computed from the fifteen explicit tree paths. -/
theorem fullSpectrum :
    Finset.univ.image tree.pairDist = Finset.Icc 1 15 := by
  calc
    Finset.univ.image tree.pairDist =
        Finset.univ.image distanceTable := by
      apply Finset.image_congr
      intro p _
      exact pairDist_eq_distanceTable p
    _ = Finset.Icc 1 15 := by decide

/-- Physical weights computed from the five actual graph edges. -/
def physicalWeights : Finset ℕ := Finset.univ.image tree.weight

@[simp] private theorem weight_e01 : tree.weight e01 = 1 := by
  simp [tree, rawWeight, e01]

@[simp] private theorem weight_e02 : tree.weight e02 = 2 := by
  simp [tree, rawWeight, e02]

@[simp] private theorem weight_e05 : tree.weight e05 = 5 := by
  simp [tree, rawWeight, e05]

@[simp] private theorem weight_e53 : tree.weight e53 = 4 := by
  simp [tree, rawWeight, e53]

@[simp] private theorem weight_e54 : tree.weight e54 = 8 := by
  simp [tree, rawWeight, e54]

private theorem weight_cases (e : tree.Edge) :
    tree.weight e = 1 ∨ tree.weight e = 2 ∨ tree.weight e = 4 ∨
      tree.weight e = 5 ∨ tree.weight e = 8 := by
  change rawWeight e.1 = 1 ∨ rawWeight e.1 = 2 ∨ rawWeight e.1 = 4 ∨
    rawWeight e.1 = 5 ∨ rawWeight e.1 = 8
  by_cases h01 : e.1 = s(0, 1) <;>
    by_cases h02 : e.1 = s(0, 2) <;>
    by_cases h05 : e.1 = s(0, 5) <;>
    by_cases h53 : e.1 = s(5, 3) <;>
    by_cases h54 : e.1 = s(5, 4) <;>
    simp [rawWeight, h01, h02, h05, h53, h54]

theorem physicalWeights_eq : physicalWeights = {1, 2, 4, 5, 8} := by
  ext w
  simp only [physicalWeights, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨e, rfl⟩
    exact weight_cases e
  · intro hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact ⟨e01, weight_e01⟩
    · exact ⟨e02, weight_e02⟩
    · exact ⟨e53, weight_e53⟩
    · exact ⟨e05, weight_e05⟩
    · exact ⟨e54, weight_e54⟩

/-- Actual odd physical-weight image of the archived tree. -/
def oddPhysicalWeights : Finset ℕ :=
  (Finset.univ.filter fun e : tree.Edge => Odd (tree.weight e)).image tree.weight

theorem oddPhysicalWeights_eq : oddPhysicalWeights = {1, 5} := by
  ext w
  simp only [oddPhysicalWeights, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨e, heOdd, rfl⟩
    rcases weight_cases e with h | h | h | h | h
    · exact Or.inl h
    · rw [h] at heOdd
      norm_num at heOdd
    · rw [h] at heOdd
      norm_num at heOdd
    · exact Or.inr h
    · rw [h] at heOdd
      norm_num at heOdd
  · intro hw
    rcases hw with rfl | rfl
    · exact ⟨e01, by rw [weight_e01]; decide, weight_e01⟩
    · exact ⟨e05, by rw [weight_e05]; decide, weight_e05⟩

/-- The physical weight-five edge, retained as an actual graph edge rather
than merely as the number five. -/
def q2Bridge : tree.Edge := e05

@[simp] theorem q2Bridge_weight : tree.weight q2Bridge = 5 := by
  change tree.weight e05 = 5
  exact weight_e05

/-- Semantic second-odd-rank certificate: the weight-five physical edge is
odd and attained, weight one is attained, and every non-unit odd physical
edge has weight at least five. -/
theorem q2Bridge_is_second_odd_physical_rank :
    IsSecondOddPhysicalRank tree (tree.weight q2Bridge) := by
  refine ⟨⟨q2Bridge, ?_, rfl⟩, by simp, ⟨e01, weight_e01⟩, ?_⟩
  · rw [q2Bridge_weight]
    decide
  intro e heOdd heOne
  have hmem : tree.weight e ∈ oddPhysicalWeights := by
    rw [oddPhysicalWeights, Finset.mem_image]
    exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ e, heOdd⟩, rfl⟩
  rw [oddPhysicalWeights_eq] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h
  · exact (heOne h).elim
  · simp [h]

/-- The computed semantic second odd physical rank. -/
def q₂ : ℕ := tree.weight q2Bridge

@[simp] theorem q₂_eq_five : q₂ = 5 := q2Bridge_weight

/-- Quotient color of two named vertices: an even number of actual odd
quotient bridges lies on their canonical component path. -/
def SameOddQuotientColor (p : VertexPair 6) : Prop :=
  Even ((quotientPath tree (componentOf tree p.left)
    (componentOf tree p.right)).1.length)

/-- The quotient-color definition agrees with parity of the actual weighted
tree distance.  This follows from the exact F9 canonical-route identity. -/
@[simp] theorem sameOddQuotientColor_iff_even_pairDist (p : VertexPair 6) :
    SameOddQuotientColor p ↔ Even (tree.pairDist p) := by
  let x : ComponentVertex tree (componentOf tree p.left) := ⟨p.left, rfl⟩
  let y : ComponentVertex tree (componentOf tree p.right) := ⟨p.right, rfl⟩
  have hdist := dist_eq_two_mul_canonicalRouteHalfRank_add_mod tree x y
  change tree.pairDist p =
      2 * routeHalfRank tree
        (quotientPath tree (componentOf tree p.left)
          (componentOf tree p.right)).1 x y +
      (quotientPath tree (componentOf tree p.left)
        (componentOf tree p.right)).1.length % 2 at hdist
  unfold SameOddQuotientColor
  rw [Nat.even_iff, Nat.even_iff]
  omega

private theorem pathEdges_eq_explicit {u v : Fin 6}
    (p : graph.Path u v) :
    tree.pathEdges u v = p.1.edges.toFinset := by
  unfold PosIntTree.pathEdges
  rw [← tree.path_unique p]

@[simp] private theorem componentOf_0_eq_2 :
    componentOf tree 0 = componentOf tree 2 := by
  have h := evenEdge_components_eq tree e02 (by decide)
  simpa [PosIntTree.edgeLeft, PosIntTree.edgeRight, e02] using h

@[simp] private theorem componentOf_3_eq_5 :
    componentOf tree 3 = componentOf tree 5 := by
  have h := evenEdge_components_eq tree e53 (by decide)
  simpa [PosIntTree.edgeLeft, PosIntTree.edgeRight, e53] using h

@[simp] private theorem componentOf_4_eq_5 :
    componentOf tree 4 = componentOf tree 5 := by
  have h := evenEdge_components_eq tree e54 (by decide)
  simpa [PosIntTree.edgeLeft, PosIntTree.edgeRight, e54] using h

private theorem e01_mem_pathEdges_15 :
    e01.1 ∈ tree.pathEdges 1 5 := by
  rw [pathEdges_eq_explicit path15]
  simp [path15, e01]

@[simp] private theorem componentOf_1_ne_5 :
    componentOf tree 1 ≠ componentOf tree 5 := by
  intro hcomp
  have heven := path_edge_even_of_component_eq tree hcomp e01_mem_pathEdges_15
  have hodd : Odd (tree.weightOfPair e01.1) := by
    rw [show e01.1 = s(0, 1) from rfl, weightOfPair_01]
    decide
  exact (Nat.not_odd_iff_even.mpr heven) hodd

@[simp] private theorem componentOf_1_ne_3 :
    componentOf tree 1 ≠ componentOf tree 3 := by
  intro h
  exact componentOf_1_ne_5 (h.trans componentOf_3_eq_5)

@[simp] private theorem componentOf_1_ne_4 :
    componentOf tree 1 ≠ componentOf tree 4 := by
  intro h
  exact componentOf_1_ne_5 (h.trans componentOf_4_eq_5)

@[simp] private theorem not_evenForest_reachable_1_5 :
    ¬(evenForest tree).Reachable 1 5 := by
  intro h
  exact componentOf_1_ne_5 ((componentOf_eq_iff tree 1 5).mpr h)

@[simp] theorem q2Bridge_mem_pathEdges_13 :
    q2Bridge.1 ∈ tree.pathEdges 1 3 := by
  rw [pathEdges_eq_explicit path13]
  simp [path13, q2Bridge, e05]

@[simp] theorem q2Bridge_mem_pathEdges_14 :
    q2Bridge.1 ∈ tree.pathEdges 1 4 := by
  rw [pathEdges_eq_explicit path14]
  simp [path14, q2Bridge, e05]

@[simp] theorem q2Bridge_mem_pathEdges_15 :
    q2Bridge.1 ∈ tree.pathEdges 1 5 := by
  rw [pathEdges_eq_explicit path15]
  simp [path15, q2Bridge, e05]

/-- The semantic same-color cross block: endpoints lie in distinct actual
even components, their quotient components have the same bipartite color,
and their tree path crosses the actual second-odd bridge. -/
noncomputable def sameColorCrossPairs : Finset (VertexPair 6) := by
  classical
  exact Finset.univ.filter fun p =>
    componentOf tree p.left ≠ componentOf tree p.right ∧
      SameOddQuotientColor p ∧
      q2Bridge.1 ∈ tree.pathEdges p.left p.right

/-- The semantic filter evaluates to exactly the three audited named pairs;
this theorem is the missing graph/quotient link in the original draft. -/
theorem sameColorCrossPairs_eq :
    sameColorCrossPairs =
      { ⟨(1, 3), by decide⟩,
        ⟨(1, 4), by decide⟩,
        ⟨(1, 5), by decide⟩ } := by
  ext p
  rcases p with ⟨⟨u, v⟩, huv⟩
  simp only [sameColorCrossPairs, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  fin_cases u <;> fin_cases v
  all_goals norm_num at huv
  all_goals simp [VertexPair.left, VertexPair.right]
  all_goals norm_num

def sameColorCrossDistances : Finset ℕ :=
  sameColorCrossPairs.image tree.pairDist

theorem sameColorCrossDistances_eq :
    sameColorCrossDistances = {6, 10, 14} := by
  rw [sameColorCrossDistances, sameColorCrossPairs_eq]
  ext d
  simp [or_comm, or_left_comm]

end ArchivedOrder6

abbrev archivedOrder6PhysicalWeights : Finset ℕ :=
  ArchivedOrder6.physicalWeights

abbrev archivedOrder6SameColorCrossDistances : Finset ℕ :=
  ArchivedOrder6.sameColorCrossDistances

abbrev archivedOrder6Q₂ : ℕ := ArchivedOrder6.q₂

def nonphysicalEvenBelow (q : ℕ) (physical : Finset ℕ) : Finset ℕ :=
  ((Finset.Ico 1 q).filter fun d => d % 2 = 0) \ physical

/-- The archived order-6 witness has a nonempty same-color cross block but
no nonphysical even rank below `q_2=5`; hence the reversed implication is
false. -/
theorem archived_order6_refutes_reversed_below_q2 :
    IsSecondOddPhysicalRank ArchivedOrder6.tree archivedOrder6Q₂ ∧
    archivedOrder6Q₂ = 5 ∧
    archivedOrder6SameColorCrossDistances.Nonempty ∧
    nonphysicalEvenBelow archivedOrder6Q₂ archivedOrder6PhysicalWeights = ∅ ∧
    ¬(archivedOrder6SameColorCrossDistances.Nonempty →
      (nonphysicalEvenBelow archivedOrder6Q₂
        archivedOrder6PhysicalWeights).Nonempty) := by
  refine ⟨ArchivedOrder6.q2Bridge_is_second_odd_physical_rank,
    ArchivedOrder6.q₂_eq_five, ?_⟩
  change ArchivedOrder6.sameColorCrossDistances.Nonempty ∧
    nonphysicalEvenBelow ArchivedOrder6.q₂ ArchivedOrder6.physicalWeights = ∅ ∧
    ¬(ArchivedOrder6.sameColorCrossDistances.Nonempty →
      (nonphysicalEvenBelow ArchivedOrder6.q₂
        ArchivedOrder6.physicalWeights).Nonempty)
  rw [ArchivedOrder6.q₂_eq_five, ArchivedOrder6.physicalWeights_eq,
    ArchivedOrder6.sameColorCrossDistances_eq]
  decide

theorem archivedOrder6Distances_eq_target :
    Finset.univ.image ArchivedOrder6.tree.pairDist = Finset.Icc 1 15 :=
  ArchivedOrder6.fullSpectrum

end

end LeechTrees.OddCapacity

namespace LeechTrees.SignedMomentMerge

open LeechTrees.ParityTail

noncomputable section

/-- Signed power moment of a finite indexed family of rooted depths. -/
def signedMoment {A : Type*} [Fintype A]
    (depth : A → ℕ) (j : ℕ) : ℤ :=
  ∑ a : A, paritySign (depth a) * (depth a : ℤ) ^ j

/-- Actual signed cross moment when every cross distance is `a+b`. -/
def crossSignedMoment {A B : Type*} [Fintype A] [Fintype B]
    (depthA : A → ℕ) (depthB : B → ℕ) (j : ℕ) : ℤ :=
  ∑ x : A × B,
    paritySign (depthA x.1 + depthB x.2) *
      ((depthA x.1 + depthB x.2 : ℕ) : ℤ) ^ j

/-- Binomial convolution of two rooted signed-moment sequences. -/
def signedMomentConvolution {A B : Type*} [Fintype A] [Fintype B]
    (depthA : A → ℕ) (depthB : B → ℕ) (j : ℕ) : ℤ :=
  ∑ q ∈ Finset.range (j + 1),
    (Nat.choose j q : ℤ) * signedMoment depthA q *
      signedMoment depthB (j - q)

private theorem sum_sum_range_move_front
    {A B M : Type*} [Fintype A] [Fintype B] [AddCommMonoid M]
    (n : ℕ) (f : A → B → ℕ → M) :
    (∑ a : A, ∑ b : B, ∑ q ∈ Finset.range n, f a b q) =
      ∑ q ∈ Finset.range n, ∑ a : A, ∑ b : B, f a b q := by
  calc
    _ = ∑ a : A, ∑ q ∈ Finset.range n, ∑ b : B, f a b q := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ q ∈ Finset.range n, ∑ a : A, ∑ b : B, f a b q := by
      rw [Finset.sum_comm]

/-- Exact binomial factorization of the actual cross block. -/
theorem crossSignedMoment_eq_convolution
    {A B : Type*} [Fintype A] [Fintype B]
    (depthA : A → ℕ) (depthB : B → ℕ) (j : ℕ) :
    crossSignedMoment depthA depthB j =
      signedMomentConvolution depthA depthB j := by
  classical
  unfold crossSignedMoment signedMomentConvolution signedMoment
  rw [Fintype.sum_prod_type]
  simp_rw [← paritySign_add, Nat.cast_add, add_pow]
  simp_rw [Finset.mul_sum]
  rw [sum_sum_range_move_front]
  apply Finset.sum_congr rfl
  intro q _
  calc
    (∑ x : A, ∑ y : B,
        paritySign (depthA x) * paritySign (depthB y) *
          ((depthA x : ℤ) ^ q * (depthB y : ℤ) ^ (j - q) *
            (Nat.choose j q : ℤ))) =
        (Nat.choose j q : ℤ) *
          (∑ x : A, ∑ y : B,
            (paritySign (depthA x) * (depthA x : ℤ) ^ q) *
              (paritySign (depthB y) * (depthB y : ℤ) ^ (j - q))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = (Nat.choose j q : ℤ) *
          ((∑ x : A, paritySign (depthA x) * (depthA x : ℤ) ^ q) *
            ∑ y : B, paritySign (depthB y) * (depthB y : ℤ) ^ (j - q)) := by
      exact congrArg (fun z : ℤ => (Nat.choose j q : ℤ) * z)
        (Fintype.sum_mul_sum
          (fun x : A => paritySign (depthA x) * (depthA x : ℤ) ^ q)
          (fun y : B =>
            paritySign (depthB y) * (depthB y : ℤ) ^ (j - q))).symm
    _ = ((Nat.choose j q : ℤ) *
          ∑ x : A, paritySign (depthA x) * (depthA x : ℤ) ^ q) *
            ∑ y : B, paritySign (depthB y) * (depthB y : ℤ) ^ (j - q) := by
      ring
    _ = (∑ x : A, (Nat.choose j q : ℤ) *
          (paritySign (depthA x) * (depthA x : ℤ) ^ q)) *
            ∑ y : B, paritySign (depthB y) * (depthB y : ℤ) ^ (j - q) := by
      congr 1
      rw [Finset.mul_sum]
    _ = ∑ y : B,
          (∑ x : A, (Nat.choose j q : ℤ) *
            (paritySign (depthA x) * (depthA x : ℤ) ^ q)) *
              (paritySign (depthB y) * (depthB y : ℤ) ^ (j - q)) := by
      rw [Finset.mul_sum]

/-- The actual rooted moment of a family shifted by bridge weight `w`. -/
def shiftedSignedMoment {B : Type*} [Fintype B]
    (depthB : B → ℕ) (w j : ℕ) : ℤ :=
  ∑ b : B, paritySign (w + depthB b) *
    ((w + depthB b : ℕ) : ℤ) ^ j

/-- Exact all-degree rooted shift formula. -/
theorem shiftedSignedMoment_eq
    {B : Type*} [Fintype B] (depthB : B → ℕ) (w j : ℕ) :
    shiftedSignedMoment depthB w j =
      paritySign w *
        ∑ q ∈ Finset.range (j + 1),
          (Nat.choose j q : ℤ) * (w : ℤ) ^ (j - q) *
            signedMoment depthB q := by
  classical
  unfold shiftedSignedMoment signedMoment
  simp_rw [Nat.add_comm w, ← paritySign_add, Nat.cast_add, add_pow]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Rooted moment on the actual disjoint merge, rooted on the `A` side. -/
def mergedRootedSignedMoment
    {A B : Type*} [Fintype A] [Fintype B]
    (depthA : A → ℕ) (depthB : B → ℕ) (w j : ℕ) : ℤ :=
  ∑ x : A ⊕ B,
    match x with
    | Sum.inl a => paritySign (depthA a) * (depthA a : ℤ) ^ j
    | Sum.inr b => paritySign (w + depthB b) *
        ((w + depthB b : ℕ) : ℤ) ^ j

/-- Formula (14), rooted part, for the exact disjoint merge. -/
theorem mergedRootedSignedMoment_eq
    {A B : Type*} [Fintype A] [Fintype B]
    (depthA : A → ℕ) (depthB : B → ℕ) (w j : ℕ) :
    mergedRootedSignedMoment depthA depthB w j =
      signedMoment depthA j + paritySign w *
        ∑ q ∈ Finset.range (j + 1),
          (Nat.choose j q : ℤ) * (w : ℤ) ^ (j - q) *
            signedMoment depthB q := by
  rw [mergedRootedSignedMoment, Fintype.sum_sum_type,
    ← shiftedSignedMoment, shiftedSignedMoment_eq]
  rfl

/-- Pair moment of the exact merge: internal pairs of `A`, internal pairs of
`B`, and the actual Cartesian cross block. -/
def mergedPairSignedMoment
    {A B PairA PairB : Type*}
    [Fintype A] [Fintype B] [Fintype PairA] [Fintype PairB]
    (depthA : A → ℕ) (depthB : B → ℕ)
    (pairDepthA : PairA → ℕ) (pairDepthB : PairB → ℕ)
    (w j : ℕ) : ℤ :=
  signedMoment pairDepthA j + signedMoment pairDepthB j +
    crossSignedMoment depthA (fun b => w + depthB b) j

/-- Formula (14), pair part, in an equivalent nested-binomial form.  The
nested coefficients are the usual trinomial coefficients. -/
theorem mergedPairSignedMoment_eq
    {A B PairA PairB : Type*}
    [Fintype A] [Fintype B] [Fintype PairA] [Fintype PairB]
    (depthA : A → ℕ) (depthB : B → ℕ)
    (pairDepthA : PairA → ℕ) (pairDepthB : PairB → ℕ)
    (w j : ℕ) :
    mergedPairSignedMoment depthA depthB pairDepthA pairDepthB w j =
      signedMoment pairDepthA j + signedMoment pairDepthB j +
      paritySign w *
        ∑ q ∈ Finset.range (j + 1),
          (Nat.choose j q : ℤ) * signedMoment depthA q *
            (∑ r ∈ Finset.range (j - q + 1),
              (Nat.choose (j - q) r : ℤ) *
                (w : ℤ) ^ (j - q - r) * signedMoment depthB r) := by
  unfold mergedPairSignedMoment
  rw [crossSignedMoment_eq_convolution]
  unfold signedMomentConvolution
  apply congrArg (fun z => signedMoment pairDepthA j +
    signedMoment pairDepthB j + z)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  have hshift :
      signedMoment (fun b => w + depthB b) (j - q) =
        paritySign w *
          ∑ r ∈ Finset.range (j - q + 1),
            (Nat.choose (j - q) r : ℤ) * (w : ℤ) ^ (j - q - r) *
              signedMoment depthB r := by
    change shiftedSignedMoment depthB w (j - q) = _
    exact shiftedSignedMoment_eq depthB w (j - q)
  rw [hshift]
  ring

end

end LeechTrees.SignedMomentMerge
