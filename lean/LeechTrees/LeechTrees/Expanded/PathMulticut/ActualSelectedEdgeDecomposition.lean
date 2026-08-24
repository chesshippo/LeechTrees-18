import LeechTrees.OddQuotient.QuotientPolynomials
import LeechTrees.Expanded.PathMulticut.SelectedEdgeDecomposition

/-!
# Actual arbitrary-selected-edge decomposition

For a selected physical-edge set `F`, `selectedMarker T F` keeps the exact
underlying tree and gives selected edges marker weight one and all other
edges marker weight two.  Its odd-edge quotient is therefore literally the
forest obtained by deleting `F`.  The quotient components, canonical route,
and all ports below are thus constructed from `T` and `F`; no pair partition
or distance equation is supplied as a hypothesis.

All displayed ranks are measured in the original metric of `T`, never in the
marker metric.  This is the graph-level endpoint behind G005.
-/

open scoped BigOperators Polynomial

namespace LeechTrees.PathMulticut

open LeechTrees.Foundation
open LeechTrees.OddQuotient

noncomputable section

/-- Same physical tree, with odd marker weights exactly on `F`. -/
def selectedMarker {n : ℕ} (T : PosIntTree n) (F : Finset T.Edge) :
    PosIntTree n where
  graph := T.graph
  isTree := T.isTree
  weight := fun e => if e ∈ F then 1 else 2
  weight_pos := by
    intro e
    split_ifs <;> omega

@[simp] theorem selectedMarker_graph {n : ℕ} (T : PosIntTree n)
    (F : Finset T.Edge) : (selectedMarker T F).graph = T.graph := rfl

@[simp] theorem selectedMarker_weight {n : ℕ} (T : PosIntTree n)
    (F : Finset T.Edge) (e : T.Edge) :
    (selectedMarker T F).weight e = if e ∈ F then 1 else 2 := rfl

theorem selectedMarker_odd_iff_mem {n : ℕ} (T : PosIntTree n)
    (F : Finset T.Edge) (e : T.Edge) :
    Odd ((selectedMarker T F).weight e) ↔ e ∈ F := by
  by_cases he : e ∈ F <;> simp [selectedMarker, he]

/-- The underlying unordered edge pairs of the selected physical edges. -/
def selectedPairSet {n : ℕ} (T : PosIntTree n) (F : Finset T.Edge) :
    Set (Sym2 (Fin n)) := Subtype.val '' (↑F : Set T.Edge)

/-- The marker even forest is exactly the original graph with the selected
physical edges deleted.  This is the promised identification of its quotient
components with the actual components of `T \ F`. -/
theorem selectedMarker_evenForest_eq_delete {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge) :
    evenForest (selectedMarker T F) =
      T.graph.deleteEdges (selectedPairSet T F) := by
  ext u v
  rw [evenForest_adj_iff, SimpleGraph.deleteEdges_adj]
  constructor
  · rintro ⟨huv, heven⟩
    refine ⟨huv, ?_⟩
    intro hsel
    obtain ⟨e, heF, heval⟩ := hsel
    have hedge : s(u, v) ∈ T.graph.edgeSet := by
      rw [SimpleGraph.mem_edgeSet]
      exact huv
    have hodd : Odd ((selectedMarker T F).weightOfPair s(u, v)) := by
      rw [← heval, (selectedMarker T F).weightOfPair_edge]
      exact (selectedMarker_odd_iff_mem T F e).2 heF
    exact Nat.not_odd_iff_even.mpr heven hodd
  · rintro ⟨huv, hnot⟩
    refine ⟨huv, ?_⟩
    have hedge : s(u, v) ∈ T.graph.edgeSet := by
      rw [SimpleGraph.mem_edgeSet]
      exact huv
    let e : T.Edge := ⟨s(u, v), hedge⟩
    have heF : e ∉ F := by
      intro he
      exact hnot ⟨e, he, rfl⟩
    rw [show s(u, v) = e.1 from rfl,
      (selectedMarker T F).weightOfPair_edge]
    exact Nat.not_odd_iff_even.mp <| fun hodd =>
      heF ((selectedMarker_odd_iff_mem T F e).1 hodd)

/-- Two named vertices lie in the same actual component of `T \ F` exactly
when their canonical path contains none of the selected physical edges. -/
theorem selected_componentOf_eq_iff_no_selected_path {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge) (u v : Fin n) :
    componentOf (selectedMarker T F) u =
        componentOf (selectedMarker T F) v ↔
      ∀ e ∈ F, e.1 ∉ T.pathEdges u v := by
  let M := selectedMarker T F
  constructor
  · intro hcomp e heF hePath
    have heven : Even (M.weightOfPair e.1) :=
      path_edge_even_of_component_eq M hcomp (by
        simpa [M, selectedMarker, PosIntTree.pathEdges] using hePath)
    have hodd : Odd (M.weightOfPair e.1) := by
      rw [M.weightOfPair_edge]
      exact (selectedMarker_odd_iff_mem T F e).2 heF
    exact Nat.not_odd_iff_even.mpr heven hodd
  · intro hnone
    apply componentOf_eq_of_path_all_even M
    intro edgeValue hedgeValue
    have hedgeT : edgeValue ∈ T.pathEdges u v := by
      simpa [M, selectedMarker, PosIntTree.pathEdges] using hedgeValue
    let e : T.Edge := T.edgeOfPathMem edgeValue hedgeT
    have heNot : e ∉ F := by
      intro heF
      exact hnone e heF (by simpa [e] using hedgeT)
    rw [show edgeValue = e.1 from rfl, M.weightOfPair_edge]
    simp [M, selectedMarker, heNot]

/-- Actual components after deleting the arbitrary selected set `F`. -/
abbrev SelectedComponent {n : ℕ} (T : PosIntTree n) (F : Finset T.Edge) :=
  EvenComponent (selectedMarker T F)

abbrev SelectedComponentVertex {n : ℕ} (T : PosIntTree n)
    (F : Finset T.Edge) (C : SelectedComponent T F) :=
  ComponentVertex (selectedMarker T F) C

abbrev SelectedComponentPair {n : ℕ} (T : PosIntTree n)
    (F : Finset T.Edge) :=
  QuotientComponentPair (selectedMarker T F)

abbrev SelectedWithinIndex {n : ℕ} (T : PosIntTree n)
    (F : Finset T.Edge) :=
  WithinIndex (selectedMarker T F)

abbrev SelectedCrossIndex {n : ℕ} (T : PosIntTree n)
    (F : Finset T.Edge) :=
  CrossIndex (selectedMarker T F)

private theorem selectedBridge_distance_decomposition {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    {C D : SelectedComponent T F}
    (b : OrientedBridge (selectedMarker T F) C D) {u v : Fin n}
    (hu : (T.cutGraph b.bridge.1).Reachable u b.sourcePortVertex)
    (hv : (T.cutGraph b.bridge.1).Reachable v b.targetPortVertex) :
    T.dist u v = T.dist u b.sourcePortVertex + T.weight b.bridge.1 +
      T.dist b.targetPortVertex v := by
  have hend :
      s(T.edgeLeft b.bridge.1, T.edgeRight b.bridge.1) =
        s(b.sourcePortVertex, b.targetPortVertex) :=
    (T.edge_eq_mk_endpoints b.bridge.1).symm.trans b.edge_eq_ports
  rcases Sym2.eq_iff.mp hend with hdirect | hswap
  · have huLeft : T.LeftCut b.bridge.1 u := by
      change (T.cutGraph b.bridge.1).Reachable u (T.edgeLeft b.bridge.1)
      simpa [hdirect.1] using hu
    have hvRight : T.RightCut b.bridge.1 v := by
      change (T.cutGraph b.bridge.1).Reachable v (T.edgeRight b.bridge.1)
      simpa [hdirect.2] using hv
    simpa [hdirect.1, hdirect.2] using
      T.cross_distance_decomposition b.bridge.1 huLeft hvRight
  · have hvLeft : T.LeftCut b.bridge.1 v := by
      change (T.cutGraph b.bridge.1).Reachable v (T.edgeLeft b.bridge.1)
      simpa [hswap.1] using hv
    have huRight : T.RightCut b.bridge.1 u := by
      change (T.cutGraph b.bridge.1).Reachable u (T.edgeRight b.bridge.1)
      simpa [hswap.2] using hu
    have hrev :=
      T.cross_distance_decomposition b.bridge.1 hvLeft huRight
    calc
      T.dist u v = T.dist v u := T.dist_comm u v
      _ = T.dist v (T.edgeLeft b.bridge.1) + T.weight b.bridge.1 +
          T.dist (T.edgeRight b.bridge.1) u := hrev
      _ = T.dist u b.sourcePortVertex + T.weight b.bridge.1 +
          T.dist b.targetPortVertex v := by
        rw [T.dist_comm v (T.edgeLeft b.bridge.1),
          T.dist_comm (T.edgeRight b.bridge.1) u,
          hswap.1, hswap.2]
        omega

/-- Original-metric contribution of a selected quotient walk before its
terminal endpoint depth.  Every recursive term is an actual port separation
or an actual selected physical-edge weight. -/
noncomputable def selectedRouteInterior {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge) :
    {C D : SelectedComponent T F} →
      (p : (quotientGraph (selectedMarker T F)).Walk C D) →
      SelectedComponentVertex T F C → ℕ
  | _, _, .nil, _ => 0
  | _, _, .cons h p, x =>
      let b := orientedBridgeOfAdj (selectedMarker T F) h
      T.dist x.1 b.sourcePortVertex + T.weight b.bridge.1 +
        selectedRouteInterior T F p b.targetPort

/-- Full original-metric cost along a selected quotient walk. -/
noncomputable def selectedRouteCost {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    {C D : SelectedComponent T F}
    (p : (quotientGraph (selectedMarker T F)).Walk C D)
    (x : SelectedComponentVertex T F C)
    (y : SelectedComponentVertex T F D) : ℕ :=
  selectedRouteInterior T F p x +
    T.dist (routeTerminal (selectedMarker T F) p x) y.1

@[simp] theorem selectedRouteCost_nil {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    {C : SelectedComponent T F}
    (x y : SelectedComponentVertex T F C) :
    selectedRouteCost T F (.nil :
      (quotientGraph (selectedMarker T F)).Walk C C) x y =
        T.dist x.1 y.1 := by
  simp [selectedRouteCost, selectedRouteInterior]

theorem selectedRouteCost_cons {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    {C D E : SelectedComponent T F}
    (h : (quotientGraph (selectedMarker T F)).Adj C D)
    (p : (quotientGraph (selectedMarker T F)).Walk D E)
    (x : SelectedComponentVertex T F C)
    (y : SelectedComponentVertex T F E) :
    selectedRouteCost T F (.cons h p) x y =
      let b := orientedBridgeOfAdj (selectedMarker T F) h
      T.dist x.1 b.sourcePortVertex + T.weight b.bridge.1 +
        selectedRouteCost T F p b.targetPort y := by
  simp [selectedRouteCost, selectedRouteInterior, add_assoc]

/-- The actual original-tree distance is the cost of every simple route in
the selected-edge quotient. -/
theorem dist_eq_selectedRouteCost {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    {C D : SelectedComponent T F}
    (p : (quotientGraph (selectedMarker T F)).Walk C D) (hp : p.IsPath)
    (x : SelectedComponentVertex T F C)
    (y : SelectedComponentVertex T F D) :
    T.dist x.1 y.1 = selectedRouteCost T F p x y := by
  induction p with
  | nil => simp
  | @cons C D E h p ih =>
      have hpTail : p.IsPath := hp.of_cons
      have havoid : s(C, D) ∉ p.edges :=
        ((SimpleGraph.Walk.cons_isTrail_iff h p).mp hp.isTrail).2
      let M := selectedMarker T F
      let b := orientedBridgeOfAdj M h
      have htailDelete : (quotientCutGraph M b.bridge).Reachable D E := by
        rw [quotientCutGraph, b.component_pair]
        exact (SimpleGraph.reachable_delete_edges_iff_exists_walk).2
          ⟨p, havoid⟩
      have htailMarker : (M.cutGraph b.bridge.1).Reachable
          b.targetPortVertex y.1 :=
        quotientCut_reachable_lift M b.bridge htailDelete
          b.target_component y.2
      have hsourceMarker : (M.cutGraph b.bridge.1).Reachable
          x.1 b.sourcePortVertex :=
        oddCut_reachable_of_component_eq M b.bridge
          (x.2.trans b.source_component.symm)
      have htail : (T.cutGraph b.bridge.1).Reachable
          b.targetPortVertex y.1 := by
        simpa [M, selectedMarker, PosIntTree.cutGraph] using htailMarker
      have hsource : (T.cutGraph b.bridge.1).Reachable
          x.1 b.sourcePortVertex := by
        simpa [M, selectedMarker, PosIntTree.cutGraph] using hsourceMarker
      have hsplit := selectedBridge_distance_decomposition T F b
        hsource htail.symm
      have hrest := ih hpTail b.targetPort y
      change T.dist b.targetPortVertex y.1 =
        selectedRouteCost T F p b.targetPort y at hrest
      calc
        T.dist x.1 y.1 = T.dist x.1 b.sourcePortVertex +
            T.weight b.bridge.1 + T.dist b.targetPortVertex y.1 := hsplit
        _ = selectedRouteCost T F (.cons h p) x y := by
          rw [hrest, selectedRouteCost_cons]

/-- Actual first port of a selected component-pair route. -/
noncomputable def selectedSourcePort {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) :
    SelectedComponentVertex T F q.left :=
  canonicalSourcePort (selectedMarker T F) q

/-- Actual last port of a selected component-pair route. -/
noncomputable def selectedTargetPort {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) :
    SelectedComponentVertex T F q.right :=
  canonicalTargetPort (selectedMarker T F) q

/-- Original-metric distance between the two actual exit ports, including
all selected bridges and all intermediate component port separations. -/
noncomputable def selectedRouteLength {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) : ℕ :=
  let M := selectedMarker T F
  let R := canonicalRouteData M q
  let b := orientedBridgeOfAdj M R.head
  T.weight b.bridge.1 + selectedRouteInterior T F R.tail b.targetPort

/-- Exact graph/model endpoint: every cross-component distance is the route
length plus the two original-metric rooted depths at the constructed ports. -/
theorem selected_cross_distance_decomposition {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    (q : SelectedComponentPair T F)
    (x : SelectedComponentVertex T F q.left)
    (y : SelectedComponentVertex T F q.right) :
    T.dist x.1 y.1 = selectedRouteLength T F q +
      T.dist x.1 (selectedSourcePort T F q).1 +
      T.dist y.1 (selectedTargetPort T F q).1 := by
  let M := selectedMarker T F
  let R := canonicalRouteData M q
  let b := orientedBridgeOfAdj M R.head
  have hroute := dist_eq_selectedRouteCost T F
    (canonicalRouteWalk M q) (canonicalRouteWalk_isPath M q) x y
  simp only [canonicalRouteWalk] at hroute
  rw [selectedRouteCost_cons] at hroute
  change T.dist x.1 y.1 =
    T.dist x.1 b.sourcePortVertex + T.weight b.bridge.1 +
      (selectedRouteInterior T F R.tail b.targetPort +
        T.dist (routeTerminal M R.tail b.targetPort) y.1) at hroute
  change T.dist x.1 y.1 =
    (T.weight b.bridge.1 + selectedRouteInterior T F R.tail b.targetPort) +
      T.dist x.1 b.sourcePortVertex +
      T.dist y.1 (routeTerminal M R.tail b.targetPort) at ⊢
  rw [T.dist_comm y.1]
  omega

noncomputable def selectedInternalRank {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    {C : SelectedComponent T F}
    (p : InternalPair (selectedMarker T F) C) : ℕ :=
  T.dist p.1.1.1 p.1.2.1

noncomputable def selectedLeftDepth {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    (q : SelectedComponentPair T F)
    (x : SelectedComponentVertex T F q.left) : ℕ :=
  T.dist x.1 (selectedSourcePort T F q).1

noncomputable def selectedRightDepth {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    (q : SelectedComponentPair T F)
    (y : SelectedComponentVertex T F q.right) : ℕ :=
  T.dist y.1 (selectedTargetPort T F q).1

noncomputable def selectedCrossRank {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    (q : SelectedComponentPair T F)
    (z : SelectedComponentVertex T F q.left ×
      SelectedComponentVertex T F q.right) : ℕ :=
  selectedRouteLength T F q + selectedLeftDepth T F q z.1 +
    selectedRightDepth T F q z.2

private theorem selected_indexToPair_cross_dist {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    (z : SelectedCrossIndex T F) :
    T.pairDist (indexToPair (selectedMarker T F) (.inr z)) =
      T.dist z.2.1.1 z.2.2.1 := by
  have hs := indexToPair_cross_sym2 (selectedMarker T F) z
  rcases Sym2.eq_iff.mp hs with h | h
  · unfold PosIntTree.pairDist
    rw [h.1, h.2]
  · unfold PosIntTree.pairDist
    rw [h.1, h.2, T.dist_comm]

/-- Pointwise correctness of the actual selected-edge partition, measured in
the original tree metric. -/
theorem selected_pair_partition_rank {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    (z : SelectedWithinIndex T F ⊕ SelectedCrossIndex T F) :
    T.pairDist (indexToPair (selectedMarker T F) z) =
      Sum.elim
        (fun x => selectedInternalRank T F x.2)
        (fun x => selectedCrossRank T F x.1 x.2) z := by
  cases z with
  | inl z =>
      rcases z with ⟨C, p⟩
      rfl
  | inr z =>
      rw [selected_indexToPair_cross_dist]
      exact selected_cross_distance_decomposition T F z.1 z.2.1 z.2.2

noncomputable def selectedInternalPoly {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    (C : SelectedComponent T F) : ℕ[X] :=
  rankPoly (selectedInternalRank T F :
    InternalPair (selectedMarker T F) C → ℕ)

noncomputable def selectedRootedLeftPoly {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) : ℕ[X] :=
  rankPoly (selectedLeftDepth T F q)

noncomputable def selectedRootedRightPoly {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) : ℕ[X] :=
  rankPoly (selectedRightDepth T F q)

noncomputable def selectedCrossPoly {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) : ℕ[X] :=
  Polynomial.monomial (selectedRouteLength T F q) 1 *
    selectedRootedLeftPoly T F q * selectedRootedRightPoly T F q

/-- G005, graph-level form: arbitrary actual selected-edge deletion, actual
components, actual ports, and original-metric route lengths give the exact
multiplicity-preserving gluing polynomial. -/
theorem actual_selectedEdge_gluing_polynomial {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge) :
    rankPoly T.pairDist =
      (∑ C : SelectedComponent T F, selectedInternalPoly T F C) +
      ∑ q : SelectedComponentPair T F, selectedCrossPoly T F q := by
  let M := selectedMarker T F
  let splitRank : SelectedWithinIndex T F ⊕ SelectedCrossIndex T F → ℕ :=
    Sum.elim
      (fun x => selectedInternalRank T F x.2)
      (fun x => selectedCrossRank T F x.1 x.2)
  have hreindex : rankPoly T.pairDist = rankPoly splitRank := by
    apply rankPoly_equiv (vertexPairIndexEquiv M) T.pairDist splitRank
    intro p
    have h := selected_pair_partition_rank T F
      ((vertexPairIndexEquiv M) p)
    have hinv :
        indexToPair M ((vertexPairIndexEquiv M) p) = p :=
      (vertexPairIndexEquiv M).left_inv p
    rw [hinv] at h
    simpa [M, splitRank] using h.symm
  rw [hreindex, rankPoly_sum, rankPoly_sigma, rankPoly_sigma]
  apply congrArg₂ (· + ·)
  · rfl
  · apply Finset.sum_congr rfl
    intro q hq
    exact rankPoly_shift_add_product
      (selectedRouteLength T F q)
      (selectedLeftDepth T F q)
      (selectedRightDepth T F q)

/-- The Leech target form of the same actual decomposition. -/
theorem actual_selectedEdge_gluing_eq_target {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) (F : Finset T.Edge) :
    (∑ C : SelectedComponent T F, selectedInternalPoly T F C) +
      ∑ q : SelectedComponentPair T F, selectedCrossPoly T F q =
        ∑ d ∈ Finset.Icc 1 (targetN n), Polynomial.monomial d 1 := by
  classical
  calc
    (∑ C : SelectedComponent T F, selectedInternalPoly T F C) +
        ∑ q : SelectedComponentPair T F, selectedCrossPoly T F q =
        rankPoly T.pairDist := (actual_selectedEdge_gluing_polynomial T F).symm
    _ = rankPoly (fun d : ↥(Finset.Icc 1 (targetN n)) => d.1) := by
      apply rankPoly_equiv hL.spectrumEquiv T.pairDist
        (fun d : ↥(Finset.Icc 1 (targetN n)) => d.1)
      intro p
      rfl
    _ = ∑ d ∈ Finset.Icc 1 (targetN n), Polynomial.monomial d 1 := by
      simpa only [rankPoly] using
        (Finset.sum_attach (Finset.Icc 1 (targetN n))
          (fun d => Polynomial.monomial d 1))

/-- Internal 0/1 and global-disjointness consequence, expressed without
support-set deduplication: after the actual indexed partition, the rank map is
injective in every summand and across all distinct summands. -/
theorem actual_selectedEdge_splitRank_injective {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) (F : Finset T.Edge) :
    Function.Injective
      (Sum.elim
        (fun x : SelectedWithinIndex T F => selectedInternalRank T F x.2)
        (fun x : SelectedCrossIndex T F =>
          selectedCrossRank T F x.1 x.2)) := by
  intro x y hxy
  let M := selectedMarker T F
  have hp : indexToPair M x = indexToPair M y := by
    apply hL.pairDist_injective
    rw [selected_pair_partition_rank T F x,
      selected_pair_partition_rank T F y]
    exact hxy
  exact (vertexPairIndexEquiv M).symm.injective hp

end

end LeechTrees.PathMulticut
