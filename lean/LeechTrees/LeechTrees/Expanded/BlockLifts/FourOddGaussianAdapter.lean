import LeechTrees.OddQuotient.F9Endpoints
import LeechTrees.OddQuotient.TwoPortCoordinates
import LeechTrees.Expanded.BlockLifts.BlockLiftObstructions
import LeechTrees.Expanded.BlockLifts.GaussianScalarCertificates
import Mathlib

/-!
# Actual four-odd-edge Gaussian quotient adapter

This file starts with an existing order-18 `PosIntTree`, its exact
`IsLeech` spectrum, and exactly four actual odd physical edges.  It derives
the five actual even components, their quotient-tree shape and colour
budgets, the component imbalances, and the identity
`xᵀ K_Q x = 18 + 2 i`.

No Gaussian expansion, target value, component order, colour budget, or
quotient shape is stored as an input field.
-/

open scoped BigOperators

namespace LeechTrees.AdditionalBlockLifts

open LeechTrees.Foundation
open LeechTrees.OddQuotient

/-! ## A path metric carrying the complete half-weight phase -/

/-- Sum of `floor(weight/2)` over the actual physical path.  Odd bridge
half-weights, even internal half-weights, and every port-to-port separation
are therefore all retained. -/
noncomputable def floorPathMetric {n : ℕ} (T : PosIntTree n)
    (u v : Fin n) : ℕ :=
  ∑ e ∈ T.pathEdges u v, T.weightOfPair e / 2

private theorem finsetSum_toFinset_eq_listSum_local
    {α : Type*} [DecidableEq α] (f : α → ℕ) (l : List α)
    (hl : l.Nodup) :
    (∑ x ∈ l.toFinset, f x) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.nodup_cons] at hl
      simp [hl.1, ih hl.2]

namespace PosIntTree

noncomputable def walkLabelSum {n : ℕ} (T : PosIntTree n)
    (label : Sym2 (Fin n) → ℕ) {u v : Fin n}
    (p : T.graph.Walk u v) : ℕ :=
  (p.edges.map label).sum

theorem path_walkLabelSum {n : ℕ} (T : PosIntTree n)
    (label : Sym2 (Fin n) → ℕ) {u v : Fin n}
    (p : T.graph.Path u v) :
    (∑ e ∈ T.pathEdges u v, label e) = walkLabelSum T label p.1 := by
  classical
  rw [T.path_unique p]
  unfold PosIntTree.pathEdges PosIntTree.walkLabelSum
  exact finsetSum_toFinset_eq_listSum_local _ _ (T.pathEdges_nodup u v)

/-- The cut decomposition is valid for an arbitrary edge label on the same
actual tree topology. -/
theorem pathLabelSum_cross_decomposition
    {n : ℕ} (T : PosIntTree n) (label : Sym2 (Fin n) → ℕ)
    (e : T.Edge) {u v : Fin n}
    (hu : T.LeftCut e u) (hv : T.RightCut e v) :
    (∑ f ∈ T.pathEdges u v, label f) =
      (∑ f ∈ T.pathEdges u (T.edgeLeft e), label f) +
        label s(T.edgeLeft e, T.edgeRight e) +
          ∑ f ∈ T.pathEdges (T.edgeRight e) v, label f := by
  classical
  change (T.cutGraph e).Reachable u (T.edgeLeft e) at hu
  change (T.cutGraph e).Reachable v (T.edgeRight e) at hv
  obtain ⟨qL, hqL⟩ := hu.exists_isPath
  obtain ⟨qR, hqR⟩ := hv.symm.exists_isPath
  let pL : T.graph.Path u (T.edgeLeft e) :=
    ⟨qL.mapLe (T.cutGraph_le e), hqL.mapLe (T.cutGraph_le e)⟩
  let pR : T.graph.Path (T.edgeRight e) v :=
    ⟨qR.mapLe (T.cutGraph_le e), hqR.mapLe (T.cutGraph_le e)⟩
  have hdisjoint : pL.1.support.Disjoint pR.1.support := by
    rw [List.disjoint_left]
    intro x hxL hxR
    have hxLq : x ∈ qL.support := by simpa [pL] using hxL
    have hxRq : x ∈ qR.support := by simpa [pR] using hxR
    have hxa : (T.cutGraph e).Reachable x (T.edgeLeft e) :=
      (qL.dropUntil x hxLq).reachable
    have hbx : (T.cutGraph e).Reachable (T.edgeRight e) x :=
      (qR.takeUntil x hxRq).reachable
    exact T.cut_endpoints_not_reachable e (hxa.symm.trans hbx.symm)
  have hbnot : T.edgeRight e ∉ pL.1.support := by
    intro hb
    exact (List.disjoint_left.mp hdisjoint hb) pR.1.start_mem_support
  let pLE : T.graph.Walk u (T.edgeRight e) := pL.1.concat (T.edge_adj e)
  have hpLE : pLE.IsPath := pL.2.concat hbnot (T.edge_adj e)
  let route : T.graph.Walk u v := pLE.append pR.1
  have hroute : route.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append,
      List.nodup_append]
    refine ⟨hpLE.support_nodup, pR.2.support_nodup.tail, ?_⟩
    intro x hx y hy hxy
    subst y
    have hx' : x ∈ pL.1.support ∨ x = T.edgeRight e := by
      simpa [pLE] using hx
    rcases hx' with hxL | rfl
    · exact (List.disjoint_left.mp hdisjoint hxL) (List.mem_of_mem_tail hy)
    · have hnodup := pR.2.support_nodup
      have hcons : (T.edgeRight e :: pR.1.support.tail).Nodup := by
        rw [← pR.1.support_eq_cons]
        exact hnodup
      exact (List.nodup_cons.mp hcons).1 hy
  calc
    (∑ f ∈ T.pathEdges u v, label f) =
        walkLabelSum T label route :=
      path_walkLabelSum T label ⟨route, hroute⟩
    _ = walkLabelSum T label pL.1 +
        label s(T.edgeLeft e, T.edgeRight e) +
          walkLabelSum T label pR.1 := by
      simp [route, pLE, walkLabelSum, add_assoc]
    _ = (∑ f ∈ T.pathEdges u (T.edgeLeft e), label f) +
        label s(T.edgeLeft e, T.edgeRight e) +
          ∑ f ∈ T.pathEdges (T.edgeRight e) v, label f := by
      rw [path_walkLabelSum T label pL, path_walkLabelSum T label pR]

end PosIntTree

/-- Relabel the same underlying physical tree by `floor(weight/2)+1`.
The added unit makes weight-one edges positive without changing paths. -/
noncomputable def floorPlusOneTree {n : ℕ} (T : PosIntTree n) :
    PosIntTree n where
  graph := T.graph
  isTree := T.isTree
  weight e := T.weight e / 2 + 1
  weight_pos e := by omega

/-- The unit-weight copy of the same physical tree. -/
noncomputable def unitCopyTree {n : ℕ} (T : PosIntTree n) : PosIntTree n where
  graph := T.graph
  isTree := T.isTree
  weight _ := 1
  weight_pos _ := by omega

private theorem sameGraph_pathEdges
    {n : ℕ} (T U : PosIntTree n) (hgraph : U.graph = T.graph)
    (u v : Fin n) : U.pathEdges u v = T.pathEdges u v := by
  cases T
  cases U
  cases hgraph
  rfl

theorem floorPlusOne_dist
    {n : ℕ} (T : PosIntTree n) (u v : Fin n) :
    (floorPlusOneTree T).dist u v =
      floorPathMetric T u v + (unitCopyTree T).dist u v := by
  classical
  have hp := sameGraph_pathEdges T (floorPlusOneTree T) rfl u v
  have hu := sameGraph_pathEdges T (unitCopyTree T) rfl u v
  unfold PosIntTree.dist floorPathMetric
  rw [hp, hu]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  rw [← T.weight_edgeOfPathMem e he]
  rw [← (floorPlusOneTree T).weight_edgeOfPathMem e (by simpa [hp] using he)]
  rw [← (unitCopyTree T).weight_edgeOfPathMem e (by simpa [hu] using he)]
  rfl

/-- The floor-weight path metric has the same root-parity cocycle as every
weighted tree metric.  This proof is not an assumed phase law: it subtracts
the root-path parity laws of two honest positive relabellings of the same
physical tree. -/
theorem floorPathMetric_root_even
    {n : ℕ} (T : PosIntTree n) (r u v : Fin n) :
    Even (floorPathMetric T r u + floorPathMetric T u v +
      floorPathMetric T r v) := by
  have hplus := (floorPlusOneTree T).root_path_even r u v
  have hunit := (unitCopyTree T).root_path_even r u v
  rw [floorPlusOne_dist, floorPlusOne_dist, floorPlusOne_dist] at hplus
  rw [Nat.even_iff] at hplus hunit ⊢
  omega

/-- Multiplicative sign form of the preceding actual path lemma. -/
theorem floorPathSign_factor
    {n : ℕ} (T : PosIntTree n) (r u v : Fin n) :
    weightParitySign (floorPathMetric T r v) =
      weightParitySign (floorPathMetric T r u) *
        weightParitySign (floorPathMetric T u v) := by
  have h := floorPathMetric_root_even T r u v
  rw [Nat.even_iff] at h
  have hmod : floorPathMetric T r v % 2 =
      (floorPathMetric T r u + floorPathMetric T u v) % 2 := by
    omega
  rw [weightParitySign_eq_of_mod_two_eq _ _ hmod]
  exact weightParitySign_add _ _

/-- Inside an actual even component the floor-weight path metric is exactly
the integral halved metric `rho`. -/
theorem floorPathMetric_eq_rho
    {n : ℕ} (T : PosIntTree n) {C : EvenComponent T}
    (u v : ComponentVertex T C) :
    floorPathMetric T u.1 v.1 = rho T u v := by
  classical
  unfold floorPathMetric rho PosIntTree.dist
  have hall : ∀ e ∈ T.pathEdges u.1 v.1, Even (T.weightOfPair e) := by
    intro e he
    exact path_edge_even_of_component_eq T (u.2.trans v.2.symm) he
  exact (Nat.sum_div (fun e he => by
    rcases hall e he with ⟨r, hr⟩
    exact ⟨r, by omega⟩)).symm

/-- The recursive quotient route cost is not a surrogate: it is exactly the
sum of `floor(weight/2)` along the underlying physical path. -/
theorem floorPathMetric_eq_routeCost
    {n : ℕ} (T : PosIntTree n) {C D : EvenComponent T}
    (p : (quotientGraph T).Walk C D) (hp : p.IsPath)
    (u : ComponentVertex T C) (v : ComponentVertex T D) :
    floorPathMetric T u.1 v.1 = routeCost T p u v := by
  induction p with
  | nil =>
      simpa [routeCost] using floorPathMetric_eq_rho T u v
  | @cons C D E h p ih =>
      let b := orientedBridgeOfAdj T h
      have hpTail : p.IsPath := hp.of_cons
      have havoid : s(C, D) ∉ p.edges :=
        ((SimpleGraph.Walk.cons_isTrail_iff h p).mp hp.isTrail).2
      have htailDelete : (quotientCutGraph T b.bridge).Reachable D E := by
        rw [quotientCutGraph, b.component_pair]
        exact (SimpleGraph.reachable_delete_edges_iff_exists_walk).2
          ⟨p, havoid⟩
      have hvCut : (T.cutGraph b.bridge.1).Reachable
          v.1 b.targetPortVertex :=
        (quotientCut_reachable_lift T b.bridge htailDelete
          b.target_component v.2).symm
      have hsourceCut := oddCut_reachable_of_component_eq T b.bridge
        (u.2.trans b.source_component.symm)
      have hfloorSplit :
          floorPathMetric T u.1 v.1 =
            floorPathMetric T u.1 b.sourcePortVertex +
              T.weight b.bridge.1 / 2 +
                floorPathMetric T b.targetPortVertex v.1 := by
        have hports :
            s(T.edgeLeft b.bridge.1, T.edgeRight b.bridge.1) =
              s(b.sourcePortVertex, b.targetPortVertex) :=
          (T.edge_eq_mk_endpoints b.bridge.1).symm.trans b.edge_eq_ports
        have hedgePorts : T.weightOfPair
            s(b.sourcePortVertex, b.targetPortVertex) =
              T.weight b.bridge.1 := by
          rw [← b.edge_eq_ports]
          exact T.weightOfPair_edge b.bridge.1
        rcases Sym2.eq_iff.mp hports with hdirect | hswap
        · have huLeft : T.LeftCut b.bridge.1 u.1 := by
            unfold PosIntTree.LeftCut
            simpa [hdirect.1] using hsourceCut
          have hvRight : T.RightCut b.bridge.1 v.1 := by
            unfold PosIntTree.RightCut
            simpa [hdirect.2] using hvCut
          have hs := PosIntTree.pathLabelSum_cross_decomposition T
            (fun e => T.weightOfPair e / 2) b.bridge.1 huLeft hvRight
          simpa [floorPathMetric, hedgePorts, hdirect.1, hdirect.2] using hs
        · have hvLeft : T.LeftCut b.bridge.1 v.1 := by
            unfold PosIntTree.LeftCut
            simpa [hswap.1] using hvCut
          have huRight : T.RightCut b.bridge.1 u.1 := by
            unfold PosIntTree.RightCut
            simpa [hswap.2] using hsourceCut
          have hs := PosIntTree.pathLabelSum_cross_decomposition T
            (fun e => T.weightOfPair e / 2) b.bridge.1 hvLeft huRight
          simpa [floorPathMetric, hedgePorts, Sym2.eq_swap,
            hswap.1, hswap.2,
            T.pathEdges_comm, add_comm, add_left_comm, add_assoc] using hs
      rw [hfloorSplit]
      change floorPathMetric T u.1 b.sourcePort.1 + T.weight b.bridge.1 / 2 +
          floorPathMetric T b.targetPort.1 v.1 =
        routeCost T (SimpleGraph.Walk.cons h p) u v
      rw [floorPathMetric_eq_rho T u b.sourcePort,
        ih hpTail b.targetPort v, routeCost_cons]
      rfl

/-! ## Actual component orders, imbalances, and gauge -/

noncomputable def componentReference {n : ℕ} (T : PosIntTree n)
    (C : EvenComponent T) : ComponentVertex T C :=
  ⟨componentRep T C, componentOf_componentRep T C⟩

noncomputable def componentOrder {n : ℕ} (T : PosIntTree n)
    (C : EvenComponent T) : ℕ :=
  Fintype.card (ComponentVertex T C)

noncomputable def componentDelta {n : ℕ} (T : PosIntTree n)
    (C : EvenComponent T) : ℤ :=
  ∑ v : ComponentVertex T C,
    weightParitySign (rho T (componentReference T C) v)

/-- Root component gauge, defined from the actual full half-weight path
phase.  It absorbs bridge half-weights and every actual port depth. -/
noncomputable def componentSigma {n : ℕ} (T : PosIntTree n)
    (R C : EvenComponent T) : ℤ :=
  weightParitySign (floorPathMetric T
    (componentReference T R).1 (componentReference T C).1)

noncomputable def componentCoordinate {n : ℕ} (T : PosIntTree n)
    (R C : EvenComponent T) : ℤ :=
  componentSigma T R C * componentDelta T C

theorem componentSigma_sign
    {n : ℕ} (T : PosIntTree n) (R C : EvenComponent T) :
    componentSigma T R C = 1 ∨ componentSigma T R C = -1 := by
  unfold componentSigma weightParitySign
  split_ifs <;> simp

/-- The actual gauge makes the reference-to-reference phase a product of
the two component signs. -/
theorem component_reference_phase
    {n : ℕ} (T : PosIntTree n) (R C D : EvenComponent T) :
    weightParitySign (floorPathMetric T
        (componentReference T C).1 (componentReference T D).1) =
      componentSigma T R C * componentSigma T R D := by
  have hfactor := floorPathSign_factor T (componentReference T R).1
    (componentReference T C).1 (componentReference T D).1
  unfold componentSigma at hfactor ⊢
  have hsign : weightParitySign (floorPathMetric T
      (componentReference T R).1 (componentReference T C).1) = 1 ∨
      weightParitySign (floorPathMetric T
        (componentReference T R).1 (componentReference T C).1) = -1 := by
    unfold weightParitySign
    split_ifs <;> simp
  rcases hsign with hsign | hsign <;> rw [hsign] at hfactor ⊢ <;>
    norm_num at hfactor ⊢ <;> linarith

private theorem sum_sign_abs_le_card
    {α : Type*} [Fintype α] (s : α → ℤ)
    (hs : ∀ a, s a = 1 ∨ s a = -1) :
    |∑ a, s a| ≤ Fintype.card α := by
  calc
    |∑ a, s a| ≤ ∑ a, |s a| :=
      Finset.abs_sum_le_sum_abs s Finset.univ
    _ = ∑ _a : α, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro a ha
      rcases hs a with h | h <;> simp [h]
    _ = Fintype.card α := by simp

private theorem sum_sign_mod_two_card
    {α : Type*} [Fintype α] (s : α → ℤ)
    (hs : ∀ a, s a = 1 ∨ s a = -1) :
    (∑ a, s a) % 2 = (Fintype.card α : ℤ) % 2 := by
  calc
    (∑ a, s a) % 2 = (∑ a, (1 : ℤ)) % 2 := by
      apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
      rw [← Finset.sum_sub_distrib]
      apply Int.dvd_iff_emod_eq_zero.mp
      exact Finset.dvd_sum fun a ha => by
        rcases hs a with h | h <;> rw [h] <;> norm_num
    _ = (Fintype.card α : ℤ) % 2 := by simp

theorem componentDatum_valid
    {n : ℕ} (T : PosIntTree n) (R C : EvenComponent T) :
    ScalarDatum.Valid
      ⟨componentCoordinate T R C, componentOrder T C⟩ := by
  have hnonempty : Nonempty (ComponentVertex T C) :=
    ⟨componentReference T C⟩
  have hdeltaSigns : ∀ v : ComponentVertex T C,
      weightParitySign (rho T (componentReference T C) v) = 1 ∨
        weightParitySign (rho T (componentReference T C) v) = -1 := by
    intro v
    unfold weightParitySign
    split_ifs <;> simp
  have hσ := componentSigma_sign T R C
  constructor
  · unfold componentOrder
    exact Fintype.card_pos_iff.mpr hnonempty
  constructor
  · unfold componentCoordinate componentDelta componentOrder
    rcases hσ with hσ | hσ <;> rw [hσ] <;>
      simp only [one_mul, neg_one_mul, abs_neg] <;>
      exact sum_sign_abs_le_card _ hdeltaSigns
  · unfold componentCoordinate componentDelta componentOrder
    rcases hσ with hσ | hσ
    · rw [hσ, one_mul]
      exact sum_sign_mod_two_card _ hdeltaSigns
    · rw [hσ, neg_one_mul]
      have h := sum_sign_mod_two_card _ hdeltaSigns
      change (-∑ v : ComponentVertex T C,
        weightParitySign (rho T (componentReference T C) v)) % 2 =
          (Fintype.card (ComponentVertex T C) : ℤ) % 2
      omega

/-! ## Five components, quotient shape, and colour budgets -/

def ExactlyFourOddEdges (T : PosIntTree 18) : Prop :=
  Fintype.card (OddBridge T) = 4

theorem fourOdd_evenComponent_card
    (T : PosIntTree 18) (h4 : ExactlyFourOddEdges T) :
    Fintype.card (EvenComponent T) = 5 := by
  classical
  unfold ExactlyFourOddEdges at h4
  have hedge : Fintype.card (OddBridge T) =
      Fintype.card (quotientGraph T).edgeSet :=
    Fintype.card_congr (oddBridgeQuotientEdgeEquiv T)
  have htree := (quotientGraph_isTree T).card_edgeFinset
  simp only [SimpleGraph.edgeFinset_card] at htree
  omega

noncomputable def fourOddComponentEquiv
    (T : PosIntTree 18) (h4 : ExactlyFourOddEdges T) :
    Fin 5 ≃ EvenComponent T :=
  (Fintype.equivFinOfCardEq (fourOdd_evenComponent_card T h4)).symm

/-- Degree predicates are an exact symbolic trichotomy for a connected
five-vertex tree: maximum degree two is `P5`, maximum degree three is the
fork, and degree four is `K1,4`. -/
inductive FiveTreeShape : Type
  | p5 | fork | star
  deriving DecidableEq, Repr

noncomputable def HasFiveTreeShape {V : Type*} [Fintype V]
    (G : SimpleGraph V) : FiveTreeShape → Prop := by
  classical
  exact fun
    | .p5 => ∀ v, G.degree v ≤ 2
    | .fork => (∃ v, G.degree v = 3) ∧ ∀ v, G.degree v ≤ 3
    | .star => ∃ v, G.degree v = 4

theorem fiveTree_shape_trichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hcard : Fintype.card V = 5) :
    ∃ shape, HasFiveTreeShape G shape := by
  classical
  by_cases h4 : ∃ v, G.degree v = 4
  · exact ⟨.star, by simpa [HasFiveTreeShape] using h4⟩
  by_cases h3 : ∃ v, G.degree v = 3
  · refine ⟨.fork, h3, ?_⟩
    intro v
    have hv := G.degree_lt_card_verts v
    rw [hcard] at hv
    have hv4 : G.degree v ≠ 4 := fun hv4 => h4 ⟨v, hv4⟩
    omega
  · refine ⟨.p5, ?_⟩
    intro v
    have hv := G.degree_lt_card_verts v
    rw [hcard] at hv
    have hv4 : G.degree v ≠ 4 := fun hv4 => h4 ⟨v, hv4⟩
    have hv3 : G.degree v ≠ 3 := fun hv3 => h3 ⟨v, hv3⟩
    omega

theorem fourOdd_quotient_shape
    (T : PosIntTree 18) (h4 : ExactlyFourOddEdges T) :
    ∃ shape, HasFiveTreeShape (quotientGraph T) shape := by
  classical
  exact fiveTree_shape_trichotomy (quotientGraph T)
    (fourOdd_evenComponent_card T h4)

/-! ### Exact canonical reindexing of the five-vertex quotient

The degree trichotomy above records only the unlabeled shape.  For the
shape-specific Gaussian equations we need more: a permutation taking the
actual quotient adjacency to the literal `P5`, fork, or star matrix.  The
following finite lemma is a proof-producing classification of the 1024
simple Boolean graphs on five vertices.  It returns an actual permutation;
it records no census count and assumes no shape witness. -/

abbrev FiveGraphBoolCode :=
  { adj : Fin 5 → Fin 5 → Bool //
    (∀ u v, adj u v = adj v u) ∧ (∀ u, ¬ adj u u) }

def FiveGraphBoolCode.graph (c : FiveGraphBoolCode) :
    SimpleGraph (Fin 5) :=
  SimpleGraph.mk' c

private instance (c : FiveGraphBoolCode) : DecidableRel c.graph.Adj := by
  intro u v
  change Decidable (c.1 u v = true)
  infer_instance

/-- The ten independent unordered edges of a loopless symmetric graph on
five vertices.  This is the finite carrier used by the relabeling check. -/
private abbrev FiveGraphEdgeCode := Fin 10 → Bool

private def FiveGraphEdgeCode.e01 (c : FiveGraphEdgeCode) : Bool := c 0
private def FiveGraphEdgeCode.e02 (c : FiveGraphEdgeCode) : Bool := c 1
private def FiveGraphEdgeCode.e03 (c : FiveGraphEdgeCode) : Bool := c 2
private def FiveGraphEdgeCode.e04 (c : FiveGraphEdgeCode) : Bool := c 3
private def FiveGraphEdgeCode.e12 (c : FiveGraphEdgeCode) : Bool := c 4
private def FiveGraphEdgeCode.e13 (c : FiveGraphEdgeCode) : Bool := c 5
private def FiveGraphEdgeCode.e14 (c : FiveGraphEdgeCode) : Bool := c 6
private def FiveGraphEdgeCode.e23 (c : FiveGraphEdgeCode) : Bool := c 7
private def FiveGraphEdgeCode.e24 (c : FiveGraphEdgeCode) : Bool := c 8
private def FiveGraphEdgeCode.e34 (c : FiveGraphEdgeCode) : Bool := c 9

/-- Decode the ten unordered edge bits into the full symmetric adjacency
table expected by `FiveGraphBoolCode`. -/
private def FiveGraphEdgeCode.fullCode (c : FiveGraphEdgeCode) :
    FiveGraphBoolCode := by
  refine ⟨![![false, c.e01, c.e02, c.e03, c.e04],
      ![c.e01, false, c.e12, c.e13, c.e14],
      ![c.e02, c.e12, false, c.e23, c.e24],
      ![c.e03, c.e13, c.e23, false, c.e34],
      ![c.e04, c.e14, c.e24, c.e34, false]], ?_, ?_⟩
  · intro u v
    fin_cases u <;> fin_cases v <;> rfl
  · intro u
    fin_cases u <;> simp

/-- Read the ten independent edge bits from an arbitrary five-vertex graph. -/
private noncomputable def fiveGraphEdgeCodeOfGraph
    (G : SimpleGraph (Fin 5)) : FiveGraphEdgeCode := by
  classical
  exact ![decide (G.Adj 0 1), decide (G.Adj 0 2),
    decide (G.Adj 0 3), decide (G.Adj 0 4),
    decide (G.Adj 1 2), decide (G.Adj 1 3),
    decide (G.Adj 1 4), decide (G.Adj 2 3),
    decide (G.Adj 2 4), decide (G.Adj 3 4)]

/-- Encoding and then decoding the ten unordered edges reconstructs the
original loopless symmetric graph. -/
private theorem fiveGraphEdgeCodeOfGraph_graph
    (G : SimpleGraph (Fin 5)) :
    (fiveGraphEdgeCodeOfGraph G).fullCode.graph = G := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [FiveGraphBoolCode.graph, FiveGraphEdgeCode.fullCode,
      FiveGraphEdgeCode.e01, FiveGraphEdgeCode.e02, FiveGraphEdgeCode.e03,
      FiveGraphEdgeCode.e04, FiveGraphEdgeCode.e12, FiveGraphEdgeCode.e13,
      FiveGraphEdgeCode.e14, FiveGraphEdgeCode.e23, FiveGraphEdgeCode.e24,
      FiveGraphEdgeCode.e34, fiveGraphEdgeCodeOfGraph, G.adj_comm] <;>
    exact G.adj_comm _ _

private abbrev fiveGraphEdgeCodeClassified (c : FiveGraphEdgeCode) : Prop :=
  (c.fullCode.graph.Connected ∧ c.fullCode.graph.edgeFinset.card = 4) →
    (∃ p : Equiv.Perm (Fin 5), ∀ i j,
      c.fullCode.graph.Adj (p i) (p j) ↔ p5Distance i j = 1) ∨
    (∃ p : Equiv.Perm (Fin 5), ∀ i j,
      c.fullCode.graph.Adj (p i) (p j) ↔ forkDistance i j = 1) ∨
    (∃ p : Equiv.Perm (Fin 5), ∀ i j,
      c.fullCode.graph.Adj (p i) (p j) ↔ starDistance i j = 1)

private def FiveGraphEdgeCode.withPrefix
    (b₀ b₁ b₂ b₃ : Bool) (t : Fin 6 → Bool) : FiveGraphEdgeCode :=
  ![b₀, b₁, b₂, b₃, t 0, t 1, t 2, t 3, t 4, t 5]

private def FiveGraphEdgeCode.withPrefix5
    (b₀ b₁ b₂ b₃ b₄ : Bool) (t : Fin 5 → Bool) : FiveGraphEdgeCode :=
  ![b₀, b₁, b₂, b₃, b₄, t 0, t 1, t 2, t 3, t 4]

private def FiveGraphEdgeCode.withPrefix6
    (b₀ b₁ b₂ b₃ b₄ b₅ : Bool) (t : Fin 4 → Bool) : FiveGraphEdgeCode :=
  ![b₀, b₁, b₂, b₃, b₄, b₅, t 0, t 1, t 2, t 3]

private def FiveGraphEdgeCode.literal
    (b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : Bool) : FiveGraphEdgeCode :=
  ![b₀, b₁, b₂, b₃, b₄, b₅, b₆, b₇, b₈, b₉]

/-- A bounded Boolean reachability certificate tailored to the five-vertex
classifier.  Unlike the general connectivity decision procedure, its
reduction footprint is fixed and small on a literal ten-edge code. -/
private def fiveReachBool (c : FiveGraphEdgeCode) :
    Nat → Fin 5 → Fin 5 → Bool
  | 0, u, v => decide (u = v)
  | k + 1, u, v =>
      decide (u = v) ||
        (c.fullCode.1 u 0 && fiveReachBool c k 0 v) ||
        (c.fullCode.1 u 1 && fiveReachBool c k 1 v) ||
        (c.fullCode.1 u 2 && fiveReachBool c k 2 v) ||
        (c.fullCode.1 u 3 && fiveReachBool c k 3 v) ||
        (c.fullCode.1 u 4 && fiveReachBool c k 4 v)

private theorem fiveReachBool_of_walk (c : FiveGraphEdgeCode)
    {u v : Fin 5} (p : c.fullCode.graph.Walk u v) :
    fiveReachBool c p.length u v = true := by
  induction p with
  | nil => simp [fiveReachBool]
  | @cons u w v h p ih =>
      change c.fullCode.1 u w = true at h
      rw [SimpleGraph.Walk.length_cons]
      rw [fiveReachBool.eq_def]
      simp only [Bool.or_eq_true, Bool.and_eq_true]
      fin_cases w
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨h, ih⟩))))
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨h, ih⟩)))
      · exact Or.inl (Or.inl (Or.inr ⟨h, ih⟩))
      · exact Or.inl (Or.inr ⟨h, ih⟩)
      · exact Or.inr ⟨h, ih⟩

private theorem fiveReachBool_step (c : FiveGraphEdgeCode)
    {k : Nat} {u v : Fin 5}
    (h : fiveReachBool c k u v = true) :
    fiveReachBool c (k + 1) u v = true := by
  induction k generalizing u with
  | zero =>
      have huv : u = v := of_decide_eq_true h
      subst u
      rw [fiveReachBool.eq_def]
      simp
  | succ k ih =>
      rw [fiveReachBool.eq_def] at h ⊢
      simp only [Bool.or_eq_true, Bool.and_eq_true] at h ⊢
      rcases h with h | h4
      · rcases h with h | h3
        · rcases h with h | h2
          · rcases h with h | h1
            · rcases h with hEq | h0
              · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hEq))))
              · exact Or.inl (Or.inl (Or.inl (Or.inl
                  (Or.inr ⟨h0.1, ih h0.2⟩))))
            · exact Or.inl (Or.inl (Or.inl
                (Or.inr ⟨h1.1, ih h1.2⟩)))
          · exact Or.inl (Or.inl (Or.inr ⟨h2.1, ih h2.2⟩))
        · exact Or.inl (Or.inr ⟨h3.1, ih h3.2⟩)
      · exact Or.inr ⟨h4.1, ih h4.2⟩

private theorem fiveReachBool_mono (c : FiveGraphEdgeCode)
    {k l : Nat} {u v : Fin 5} (hkl : k ≤ l)
    (h : fiveReachBool c k u v = true) :
    fiveReachBool c l u v = true := by
  induction l generalizing k with
  | zero =>
      have hk : k = 0 := Nat.eq_zero_of_le_zero hkl
      subst k
      exact h
  | succ l ih =>
      rcases Nat.eq_or_lt_of_le hkl with hEq | hLt
      · subst k
        exact h
      · exact fiveReachBool_step c (ih (Nat.le_of_lt_succ hLt) h)

private theorem fiveConnected_reachBool4 (c : FiveGraphEdgeCode)
    (hG : c.fullCode.graph.Connected) :
    ∀ v, fiveReachBool c 4 0 v = true := by
  intro v
  obtain ⟨p, hp⟩ := hG.exists_isPath 0 v
  exact fiveReachBool_mono c (by
      have hlt := hp.length_lt
      norm_num at hlt
      omega)
    (fiveReachBool_of_walk c p)

private abbrev fiveGraphEdgeCodeBoolClassified
    (c : FiveGraphEdgeCode) : Prop :=
  ((∀ v, fiveReachBool c 4 0 v = true) ∧
      c.fullCode.graph.edgeFinset.card = 4) →
    (∃ p : Equiv.Perm (Fin 5), ∀ i j,
      c.fullCode.graph.Adj (p i) (p j) ↔ p5Distance i j = 1) ∨
    (∃ p : Equiv.Perm (Fin 5), ∀ i j,
      c.fullCode.graph.Adj (p i) (p j) ↔ forkDistance i j = 1) ∨
    (∃ p : Equiv.Perm (Fin 5), ∀ i j,
      c.fullCode.graph.Adj (p i) (p j) ↔ starDistance i j = 1)

private theorem fiveGraphEdgeCodeClassified_ofBool
    (c : FiveGraphEdgeCode)
    (h : fiveGraphEdgeCodeBoolClassified c) :
    fiveGraphEdgeCodeClassified c := by
  intro hc
  exact h ⟨fiveConnected_reachBool4 c hc.1, hc.2⟩

private theorem fiveGraphClassified10_0000000000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000000001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000000010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000000011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000000100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000000101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000000110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000000111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000001000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000001001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000001010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000001011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000001100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000001101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000001110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000001111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000010000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000010001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000010010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000010011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000010100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000010101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000010110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000010111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000011000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000011001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000011010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000011011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000011100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000011101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000011110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000011111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false false true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000100000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000100001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000100010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000100011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000100100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000100101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000100110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000100111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000101000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000101001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000101010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000101011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000101100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000101101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000101110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000101111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000110000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000110001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000110010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000110011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000110100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000110101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000110110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000110111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000111000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000111001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000111010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000111011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000111100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000111101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000111110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0000111111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false false true true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide

private theorem fiveGraphClassified10_0001000000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001000001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001000010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001000011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001000100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001000101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001000110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001000111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001001000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001001001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001001010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001001011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inr ⟨Equiv.ofBijective ![4, 0, 1, 2, 3] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0001001100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001001101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![4, 0, 1, 3, 2] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0001001110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![4, 0, 1, 2, 3] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0001001111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001010000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001010001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001010010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001010011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![4, 0, 2, 3, 1] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0001010100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001010101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![3, 1, 2, 4, 0] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0001010110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![0, 4, 2, 3, 1] (by decide), by decide⟩
private theorem fiveGraphClassified10_0001010111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001011000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001011001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001011010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![4, 0, 2, 1, 3] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0001011011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001011100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![0, 4, 1, 3, 2] (by decide), by decide⟩
private theorem fiveGraphClassified10_0001011101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001011110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001011111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true false true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001100000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001100001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001100010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001100011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![4, 0, 3, 2, 1] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0001100100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001100101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![0, 4, 3, 2, 1] (by decide), by decide⟩
private theorem fiveGraphClassified10_0001100110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![2, 1, 3, 4, 0] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0001100111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001101000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001101001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![4, 0, 3, 1, 2] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0001101010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001101011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001101100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![0, 4, 1, 2, 3] (by decide), by decide⟩
private theorem fiveGraphClassified10_0001101101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001101110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001101111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001110000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001110001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![0, 4, 3, 1, 2] (by decide), by decide⟩
private theorem fiveGraphClassified10_0001110010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![0, 4, 2, 1, 3] (by decide), by decide⟩
private theorem fiveGraphClassified10_0001110011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001110100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001110101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001110110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001110111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001111000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![1, 2, 3, 4, 0] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0001111001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001111010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001111011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001111100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001111101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001111110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0001111111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false false true true true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide

private theorem fiveGraphClassified10_0010000000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010000001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010000010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010000011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010000100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010000101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010000110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010000111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010001000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010001001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010001010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010001011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![4, 1, 2, 3, 0] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0010001100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010001101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![3, 0, 2, 4, 1] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0010001110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![0, 3, 2, 4, 1] (by decide), by decide⟩
private theorem fiveGraphClassified10_0010001111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010010000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010010001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010010010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010010011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![3, 0, 1, 4, 2] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0010010100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010010101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inr ⟨Equiv.ofBijective ![3, 0, 1, 2, 4] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0010010110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![3, 0, 1, 2, 4] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0010010111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010011000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010011001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010011010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![0, 3, 1, 4, 2] (by decide), by decide⟩
private theorem fiveGraphClassified10_0010011011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010011100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![3, 0, 2, 1, 4] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0010011101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010011110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010011111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false false true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010100000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010100001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010100010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010100011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![0, 3, 4, 2, 1] (by decide), by decide⟩
private theorem fiveGraphClassified10_0010100100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010100101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![3, 0, 4, 2, 1] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0010100110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![2, 1, 4, 3, 0] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0010100111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010101000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010101001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![0, 3, 4, 1, 2] (by decide), by decide⟩
private theorem fiveGraphClassified10_0010101010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010101011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010101100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![0, 3, 2, 1, 4] (by decide), by decide⟩
private theorem fiveGraphClassified10_0010101101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010101110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010101111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010110000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010110001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![3, 0, 4, 1, 2] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0010110010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![0, 3, 1, 2, 4] (by decide), by decide⟩
private theorem fiveGraphClassified10_0010110011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010110100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010110101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010110110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010110111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010111000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![1, 2, 4, 3, 0] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0010111001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010111010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010111011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010111100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010111101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010111110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0010111111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true false true true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide

private theorem fiveGraphClassified10_0011000000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011000001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011000010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011000011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011000100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011000101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011000110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011000111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011001000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011001001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011001010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![4, 1, 2, 0, 3] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0011001011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011001100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![1, 4, 0, 3, 2] (by decide), by decide⟩
private theorem fiveGraphClassified10_0011001101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011001110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011001111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011010000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011010001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011010010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![1, 3, 0, 4, 2] (by decide), by decide⟩
private theorem fiveGraphClassified10_0011010011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011010100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![3, 1, 2, 0, 4] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0011010101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011010110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011010111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011011000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011011001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011011010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011011011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011011100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011011101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011011110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011011111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true false true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011100000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011100001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011100010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![1, 2, 4, 0, 3] (by decide), by decide⟩
private theorem fiveGraphClassified10_0011100011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011100100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![1, 2, 3, 0, 4] (by decide), by decide⟩
private theorem fiveGraphClassified10_0011100101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011100110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011100111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011101000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![2, 1, 4, 0, 3] (by decide), by decide⟩
private theorem fiveGraphClassified10_0011101001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011101010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011101011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011101100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011101101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011101110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011101111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011110000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![2, 1, 3, 0, 4] (by decide), by decide⟩
private theorem fiveGraphClassified10_0011110001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011110010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011110011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011110100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011110101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011110110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011110111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011111000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011111001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011111010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011111011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011111100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011111101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011111110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0011111111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false false true true true true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide

private theorem fiveGraphClassified10_0100000000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100000001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100000010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100000011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100000100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100000101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100000110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100000111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100001000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100001001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100001010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100001011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![4, 1, 3, 2, 0] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0100001100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100001101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![0, 2, 3, 4, 1] (by decide), by decide⟩
private theorem fiveGraphClassified10_0100001110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![2, 0, 3, 4, 1] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0100001111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100010000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100010001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100010010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100010011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![0, 2, 4, 3, 1] (by decide), by decide⟩
private theorem fiveGraphClassified10_0100010100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100010101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![3, 1, 4, 2, 0] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0100010110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![2, 0, 4, 3, 1] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0100010111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100011000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100011001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100011010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![0, 2, 4, 1, 3] (by decide), by decide⟩
private theorem fiveGraphClassified10_0100011011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100011100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![0, 2, 3, 1, 4] (by decide), by decide⟩
private theorem fiveGraphClassified10_0100011101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100011110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100011111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false false true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100100000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100100001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100100010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100100011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![2, 0, 1, 4, 3] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0100100100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100100101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![2, 0, 1, 3, 4] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0100100110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inr ⟨Equiv.ofBijective ![2, 0, 1, 3, 4] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0100100111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100101000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100101001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![0, 2, 1, 4, 3] (by decide), by decide⟩
private theorem fiveGraphClassified10_0100101010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100101011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100101100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![2, 0, 3, 1, 4] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0100101101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100101110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100101111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100110000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100110001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![0, 2, 1, 3, 4] (by decide), by decide⟩
private theorem fiveGraphClassified10_0100110010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![2, 0, 4, 1, 3] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0100110011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100110100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100110101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100110110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100110111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100111000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![1, 3, 4, 2, 0] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0100111001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100111010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100111011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100111100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100111101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100111110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0100111111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false false true true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide

private theorem fiveGraphClassified10_0101000000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101000001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101000010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101000011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101000100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101000101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101000110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101000111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101001000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101001001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![4, 1, 3, 0, 2] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0101001010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101001011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101001100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![1, 4, 0, 2, 3] (by decide), by decide⟩
private theorem fiveGraphClassified10_0101001101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101001110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101001111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101010000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101010001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![1, 3, 4, 0, 2] (by decide), by decide⟩
private theorem fiveGraphClassified10_0101010010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101010011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101010100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![1, 3, 2, 0, 4] (by decide), by decide⟩
private theorem fiveGraphClassified10_0101010101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101010110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101010111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101011000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![2, 0, 4, 1, 3] (by decide), by decide⟩
private theorem fiveGraphClassified10_0101011001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101011010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101011011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101011100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101011101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101011110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101011111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true false true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101100000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101100001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![1, 2, 0, 4, 3] (by decide), by decide⟩
private theorem fiveGraphClassified10_0101100010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101100011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101100100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![2, 1, 3, 0, 4] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0101100101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101100110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101100111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101101000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101101001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101101010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101101011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101101100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101101101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101101110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101101111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101110000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![3, 1, 2, 0, 4] (by decide), by decide⟩
private theorem fiveGraphClassified10_0101110001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101110010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101110011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101110100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101110101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101110110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101110111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101111000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101111001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101111010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101111011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101111100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101111101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101111110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0101111111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true false true true true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide

private theorem fiveGraphClassified10_0110000000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110000001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110000010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110000011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110000100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110000101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110000110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110000111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110001000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110001001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![1, 4, 3, 0, 2] (by decide), by decide⟩
private theorem fiveGraphClassified10_0110001010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![1, 4, 2, 0, 3] (by decide), by decide⟩
private theorem fiveGraphClassified10_0110001011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110001100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110001101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110001110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110001111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110010000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110010001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![3, 1, 4, 0, 2] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0110010010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![1, 3, 0, 2, 4] (by decide), by decide⟩
private theorem fiveGraphClassified10_0110010011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110010100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110010101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110010110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110010111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110011000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![2, 0, 3, 1, 4] (by decide), by decide⟩
private theorem fiveGraphClassified10_0110011001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110011010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110011011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110011100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110011101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110011110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110011111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false false true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110100000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110100001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![1, 2, 0, 3, 4] (by decide), by decide⟩
private theorem fiveGraphClassified10_0110100010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![2, 1, 4, 0, 3] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0110100011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110100100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110100101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110100110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110100111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110101000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![3, 0, 2, 1, 4] (by decide), by decide⟩
private theorem fiveGraphClassified10_0110101001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110101010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110101011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110101100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110101101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110101110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110101111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110110000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110110001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110110010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110110011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110110100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110110101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110110110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110110111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110111000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110111001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110111010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110111011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110111100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110111101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110111110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0110111111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true false true true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide

private theorem fiveGraphClassified10_0111000000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111000001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111000010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111000011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111000100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111000101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111000110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111000111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111001000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![0, 2, 3, 4, 1] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0111001001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111001010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111001011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111001100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111001101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111001110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111001111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111010000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![0, 2, 4, 3, 1] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0111010001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111010010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111010011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111010100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111010101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111010110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111010111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111011000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111011001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111011010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111011011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111011100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111011101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111011110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111011111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true false true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111100000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![0, 3, 4, 2, 1] (by decide), by decide⟩)
private theorem fiveGraphClassified10_0111100001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111100010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111100011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111100100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111100101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111100110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111100111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111101000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111101001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111101010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111101011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111101100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111101101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111101110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111101111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111110000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111110001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111110010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111110011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111110100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111110101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111110110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111110111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111111000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111111001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111111010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111111011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111111100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111111101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111111110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_0111111111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal false true true true true true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide

private theorem fiveGraphClassified10_1000000000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000000001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000000010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000000011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000000100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000000101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000000110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000000111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000001000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000001001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000001010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000001011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![4, 2, 3, 1, 0] (by decide), by decide⟩)
private theorem fiveGraphClassified10_1000001100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000001101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![0, 1, 4, 3, 2] (by decide), by decide⟩
private theorem fiveGraphClassified10_1000001110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![0, 1, 4, 2, 3] (by decide), by decide⟩
private theorem fiveGraphClassified10_1000001111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000010000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000010001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000010010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000010011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![0, 1, 3, 4, 2] (by decide), by decide⟩
private theorem fiveGraphClassified10_1000010100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000010101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![3, 2, 4, 1, 0] (by decide), by decide⟩)
private theorem fiveGraphClassified10_1000010110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![0, 1, 3, 2, 4] (by decide), by decide⟩
private theorem fiveGraphClassified10_1000010111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000011000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000011001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000011010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![1, 0, 3, 4, 2] (by decide), by decide⟩)
private theorem fiveGraphClassified10_1000011011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000011100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![1, 0, 4, 3, 2] (by decide), by decide⟩)
private theorem fiveGraphClassified10_1000011101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000011110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000011111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false false true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000100000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000100001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000100010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000100011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![0, 1, 2, 4, 3] (by decide), by decide⟩
private theorem fiveGraphClassified10_1000100100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000100101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![0, 1, 2, 3, 4] (by decide), by decide⟩
private theorem fiveGraphClassified10_1000100110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![2, 3, 4, 1, 0] (by decide), by decide⟩)
private theorem fiveGraphClassified10_1000100111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000101000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000101001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![1, 0, 2, 4, 3] (by decide), by decide⟩)
private theorem fiveGraphClassified10_1000101010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000101011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000101100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![1, 0, 4, 2, 3] (by decide), by decide⟩)
private theorem fiveGraphClassified10_1000101101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000101110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000101111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000110000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000110001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![1, 0, 2, 3, 4] (by decide), by decide⟩)
private theorem fiveGraphClassified10_1000110010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![1, 0, 3, 2, 4] (by decide), by decide⟩)
private theorem fiveGraphClassified10_1000110011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000110100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000110101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000110110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000110111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000111000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inr ⟨Equiv.ofBijective ![1, 0, 2, 3, 4] (by decide), by decide⟩)
private theorem fiveGraphClassified10_1000111001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000111010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000111011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000111100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000111101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000111110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1000111111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false false true true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide

private theorem fiveGraphClassified10_1001000000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001000001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001000010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001000011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![4, 2, 3, 0, 1] (by decide), by decide⟩)
private theorem fiveGraphClassified10_1001000100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001000101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![1, 0, 4, 3, 2] (by decide), by decide⟩
private theorem fiveGraphClassified10_1001000110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![1, 0, 4, 2, 3] (by decide), by decide⟩
private theorem fiveGraphClassified10_1001000111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001001000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001001001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001001010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001001011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001001100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001001101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001001110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001001111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001010000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001010001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001010010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![2, 4, 0, 1, 3] (by decide), by decide⟩
private theorem fiveGraphClassified10_1001010011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001010100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![2, 3, 1, 0, 4] (by decide), by decide⟩
private theorem fiveGraphClassified10_1001010101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001010110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001010111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001011000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001011001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001011010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001011011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001011100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001011101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001011110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001011111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true false true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001100000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001100001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![2, 1, 0, 4, 3] (by decide), by decide⟩
private theorem fiveGraphClassified10_1001100010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001100011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001100100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![3, 2, 1, 0, 4] (by decide), by decide⟩
private theorem fiveGraphClassified10_1001100101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001100110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001100111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001101000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001101001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001101010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001101011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001101100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001101101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001101110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001101111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001110000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![1, 2, 3, 0, 4] (by decide), by decide⟩)
private theorem fiveGraphClassified10_1001110001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001110010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001110011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001110100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001110101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001110110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001110111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001111000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001111001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001111010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001111011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001111100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001111101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001111110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1001111111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false false true true true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide

private theorem fiveGraphClassified10_1010000000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010000001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010000010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010000011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![1, 0, 3, 4, 2] (by decide), by decide⟩
private theorem fiveGraphClassified10_1010000100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010000101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![3, 2, 4, 0, 1] (by decide), by decide⟩)
private theorem fiveGraphClassified10_1010000110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![1, 0, 3, 2, 4] (by decide), by decide⟩
private theorem fiveGraphClassified10_1010000111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010001000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010001001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010001010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![2, 4, 1, 0, 3] (by decide), by decide⟩
private theorem fiveGraphClassified10_1010001011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010001100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![2, 3, 0, 1, 4] (by decide), by decide⟩
private theorem fiveGraphClassified10_1010001101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010001110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010001111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010010000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010010001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010010010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010010011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010010100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010010101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010010110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010010111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010011000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010011001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010011010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010011011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010011100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010011101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010011110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010011111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false false true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010100000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010100001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![2, 1, 0, 3, 4] (by decide), by decide⟩
private theorem fiveGraphClassified10_1010100010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![3, 0, 1, 2, 4] (by decide), by decide⟩
private theorem fiveGraphClassified10_1010100011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010100100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010100101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010100110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010100111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010101000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![1, 2, 4, 0, 3] (by decide), by decide⟩)
private theorem fiveGraphClassified10_1010101001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010101010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010101011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010101100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010101101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010101110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010101111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010110000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010110001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010110010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010110011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010110100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010110101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010110110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010110111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010111000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010111001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010111010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010111011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010111100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010111101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010111110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1010111111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true false true true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide

private theorem fiveGraphClassified10_1011000000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011000001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011000010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![0, 1, 3, 4, 2] (by decide), by decide⟩)
private theorem fiveGraphClassified10_1011000011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011000100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![0, 1, 4, 3, 2] (by decide), by decide⟩)
private theorem fiveGraphClassified10_1011000101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011000110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011000111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011001000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011001001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011001010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011001011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011001100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011001101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011001110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011001111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011010000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011010001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011010010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011010011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011010100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011010101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011010110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011010111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011011000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011011001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011011010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011011011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011011100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011011101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011011110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011011111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true false true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011100000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![0, 3, 4, 1, 2] (by decide), by decide⟩)
private theorem fiveGraphClassified10_1011100001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011100010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011100011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011100100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011100101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011100110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011100111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011101000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011101001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011101010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011101011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011101100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011101101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011101110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011101111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011110000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011110001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011110010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011110011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011110100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011110101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011110110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011110111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011111000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011111001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011111010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011111011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011111100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011111101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011111110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1011111111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true false true true true true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide

private theorem fiveGraphClassified10_1100000000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100000001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100000010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100000011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![1, 0, 2, 4, 3] (by decide), by decide⟩
private theorem fiveGraphClassified10_1100000100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100000101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![1, 0, 2, 3, 4] (by decide), by decide⟩
private theorem fiveGraphClassified10_1100000110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![2, 3, 4, 0, 1] (by decide), by decide⟩)
private theorem fiveGraphClassified10_1100000111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100001000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100001001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![2, 0, 1, 4, 3] (by decide), by decide⟩
private theorem fiveGraphClassified10_1100001010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100001011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100001100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![3, 2, 0, 1, 4] (by decide), by decide⟩
private theorem fiveGraphClassified10_1100001101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100001110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100001111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100010000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100010001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![2, 0, 1, 3, 4] (by decide), by decide⟩
private theorem fiveGraphClassified10_1100010010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inl ⟨Equiv.ofBijective ![3, 1, 0, 2, 4] (by decide), by decide⟩
private theorem fiveGraphClassified10_1100010011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100010100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100010101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100010110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100010111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100011000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![1, 3, 4, 0, 2] (by decide), by decide⟩)
private theorem fiveGraphClassified10_1100011001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100011010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100011011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100011100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100011101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100011110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100011111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false false true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100100000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100100001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100100010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100100011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100100100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100100101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100100110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100100111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100101000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100101001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100101010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100101011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100101100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100101101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100101110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100101111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100110000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100110001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100110010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100110011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100110100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100110101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100110110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100110111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100111000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100111001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100111010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100111011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100111100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100111101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100111110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1100111111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false false true true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide

private theorem fiveGraphClassified10_1101000000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101000001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![0, 1, 2, 4, 3] (by decide), by decide⟩)
private theorem fiveGraphClassified10_1101000010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101000011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101000100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![0, 1, 4, 2, 3] (by decide), by decide⟩)
private theorem fiveGraphClassified10_1101000101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101000110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101000111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101001000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101001001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101001010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101001011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101001100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101001101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101001110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101001111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101010000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![0, 2, 4, 1, 3] (by decide), by decide⟩)
private theorem fiveGraphClassified10_1101010001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101010010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101010011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101010100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101010101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101010110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101010111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101011000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101011001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101011010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101011011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101011100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101011101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101011110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101011111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true false true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101100000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101100001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101100010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101100011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101100100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101100101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101100110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101100111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101101000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101101001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101101010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101101011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101101100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101101101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101101110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101101111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101110000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101110001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101110010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101110011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101110100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101110101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101110110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101110111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101111000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101111001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101111010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101111011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101111100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101111101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101111110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1101111111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true false true true true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide

private theorem fiveGraphClassified10_1110000000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110000001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![0, 1, 2, 3, 4] (by decide), by decide⟩)
private theorem fiveGraphClassified10_1110000010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![0, 1, 3, 2, 4] (by decide), by decide⟩)
private theorem fiveGraphClassified10_1110000011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110000100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110000101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110000110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110000111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110001000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inl ⟨Equiv.ofBijective ![0, 2, 3, 1, 4] (by decide), by decide⟩)
private theorem fiveGraphClassified10_1110001001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110001010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110001011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110001100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110001101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110001110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110001111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110010000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110010001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110010010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110010011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110010100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110010101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110010110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110010111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110011000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110011001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110011010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110011011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110011100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110011101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110011110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110011111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false false true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110100000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110100001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110100010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110100011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110100100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110100101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110100110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110100111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110101000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110101001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110101010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110101011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110101100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110101101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110101110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110101111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110110000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110110001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110110010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110110011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110110100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110110101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110110110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110110111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110111000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110111001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110111010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110111011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110111100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110111101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110111110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1110111111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true false true true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide

private theorem fiveGraphClassified10_1111000000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  intro _
  exact Or.inr (Or.inr ⟨Equiv.ofBijective ![0, 1, 2, 3, 4] (by decide), by decide⟩)
private theorem fiveGraphClassified10_1111000001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111000010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111000011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111000100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111000101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111000110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111000111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111001000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111001001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111001010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111001011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111001100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111001101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111001110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111001111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111010000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111010001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111010010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111010011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111010100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111010101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111010110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111010111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111011000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111011001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111011010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111011011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111011100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111011101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111011110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111011111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true false true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111100000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true false false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111100001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true false false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111100010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true false false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111100011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true false false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111100100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true false false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111100101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true false false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111100110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true false false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111100111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true false false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111101000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true false true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111101001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true false true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111101010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true false true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111101011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true false true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111101100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true false true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111101101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true false true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111101110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true false true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111101111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true false true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111110000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true true false false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111110001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true true false false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111110010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true true false false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111110011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true true false false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111110100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true true false true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111110101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true true false true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111110110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true true false true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111110111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true true false true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111111000 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true true true false false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111111001 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true true true false false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111111010 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true true true false true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111111011 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true true true false true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111111100 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true true true true false false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111111101 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true true true true false true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111111110 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true true true true true false) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide
private theorem fiveGraphClassified10_1111111111 :
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.literal true true true true true true true true true true) := by
  apply fiveGraphEdgeCodeClassified_ofBool
  decide

private theorem fiveGraphClassified6_000000 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false false false false false false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false false false false false false t =
      FiveGraphEdgeCode.literal false false false false false false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0000000000
  · exact fiveGraphClassified10_0000000001
  · exact fiveGraphClassified10_0000000010
  · exact fiveGraphClassified10_0000000011
  · exact fiveGraphClassified10_0000000100
  · exact fiveGraphClassified10_0000000101
  · exact fiveGraphClassified10_0000000110
  · exact fiveGraphClassified10_0000000111
  · exact fiveGraphClassified10_0000001000
  · exact fiveGraphClassified10_0000001001
  · exact fiveGraphClassified10_0000001010
  · exact fiveGraphClassified10_0000001011
  · exact fiveGraphClassified10_0000001100
  · exact fiveGraphClassified10_0000001101
  · exact fiveGraphClassified10_0000001110
  · exact fiveGraphClassified10_0000001111
private theorem fiveGraphClassified6_000001 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false false false false false true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false false false false false true t =
      FiveGraphEdgeCode.literal false false false false false true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0000010000
  · exact fiveGraphClassified10_0000010001
  · exact fiveGraphClassified10_0000010010
  · exact fiveGraphClassified10_0000010011
  · exact fiveGraphClassified10_0000010100
  · exact fiveGraphClassified10_0000010101
  · exact fiveGraphClassified10_0000010110
  · exact fiveGraphClassified10_0000010111
  · exact fiveGraphClassified10_0000011000
  · exact fiveGraphClassified10_0000011001
  · exact fiveGraphClassified10_0000011010
  · exact fiveGraphClassified10_0000011011
  · exact fiveGraphClassified10_0000011100
  · exact fiveGraphClassified10_0000011101
  · exact fiveGraphClassified10_0000011110
  · exact fiveGraphClassified10_0000011111
private theorem fiveGraphClassified6_000010 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false false false false true false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false false false false true false t =
      FiveGraphEdgeCode.literal false false false false true false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0000100000
  · exact fiveGraphClassified10_0000100001
  · exact fiveGraphClassified10_0000100010
  · exact fiveGraphClassified10_0000100011
  · exact fiveGraphClassified10_0000100100
  · exact fiveGraphClassified10_0000100101
  · exact fiveGraphClassified10_0000100110
  · exact fiveGraphClassified10_0000100111
  · exact fiveGraphClassified10_0000101000
  · exact fiveGraphClassified10_0000101001
  · exact fiveGraphClassified10_0000101010
  · exact fiveGraphClassified10_0000101011
  · exact fiveGraphClassified10_0000101100
  · exact fiveGraphClassified10_0000101101
  · exact fiveGraphClassified10_0000101110
  · exact fiveGraphClassified10_0000101111
private theorem fiveGraphClassified6_000011 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false false false false true true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false false false false true true t =
      FiveGraphEdgeCode.literal false false false false true true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0000110000
  · exact fiveGraphClassified10_0000110001
  · exact fiveGraphClassified10_0000110010
  · exact fiveGraphClassified10_0000110011
  · exact fiveGraphClassified10_0000110100
  · exact fiveGraphClassified10_0000110101
  · exact fiveGraphClassified10_0000110110
  · exact fiveGraphClassified10_0000110111
  · exact fiveGraphClassified10_0000111000
  · exact fiveGraphClassified10_0000111001
  · exact fiveGraphClassified10_0000111010
  · exact fiveGraphClassified10_0000111011
  · exact fiveGraphClassified10_0000111100
  · exact fiveGraphClassified10_0000111101
  · exact fiveGraphClassified10_0000111110
  · exact fiveGraphClassified10_0000111111
private theorem fiveGraphClassified6_000100 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false false false true false false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false false false true false false t =
      FiveGraphEdgeCode.literal false false false true false false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0001000000
  · exact fiveGraphClassified10_0001000001
  · exact fiveGraphClassified10_0001000010
  · exact fiveGraphClassified10_0001000011
  · exact fiveGraphClassified10_0001000100
  · exact fiveGraphClassified10_0001000101
  · exact fiveGraphClassified10_0001000110
  · exact fiveGraphClassified10_0001000111
  · exact fiveGraphClassified10_0001001000
  · exact fiveGraphClassified10_0001001001
  · exact fiveGraphClassified10_0001001010
  · exact fiveGraphClassified10_0001001011
  · exact fiveGraphClassified10_0001001100
  · exact fiveGraphClassified10_0001001101
  · exact fiveGraphClassified10_0001001110
  · exact fiveGraphClassified10_0001001111
private theorem fiveGraphClassified6_000101 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false false false true false true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false false false true false true t =
      FiveGraphEdgeCode.literal false false false true false true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0001010000
  · exact fiveGraphClassified10_0001010001
  · exact fiveGraphClassified10_0001010010
  · exact fiveGraphClassified10_0001010011
  · exact fiveGraphClassified10_0001010100
  · exact fiveGraphClassified10_0001010101
  · exact fiveGraphClassified10_0001010110
  · exact fiveGraphClassified10_0001010111
  · exact fiveGraphClassified10_0001011000
  · exact fiveGraphClassified10_0001011001
  · exact fiveGraphClassified10_0001011010
  · exact fiveGraphClassified10_0001011011
  · exact fiveGraphClassified10_0001011100
  · exact fiveGraphClassified10_0001011101
  · exact fiveGraphClassified10_0001011110
  · exact fiveGraphClassified10_0001011111
private theorem fiveGraphClassified6_000110 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false false false true true false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false false false true true false t =
      FiveGraphEdgeCode.literal false false false true true false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0001100000
  · exact fiveGraphClassified10_0001100001
  · exact fiveGraphClassified10_0001100010
  · exact fiveGraphClassified10_0001100011
  · exact fiveGraphClassified10_0001100100
  · exact fiveGraphClassified10_0001100101
  · exact fiveGraphClassified10_0001100110
  · exact fiveGraphClassified10_0001100111
  · exact fiveGraphClassified10_0001101000
  · exact fiveGraphClassified10_0001101001
  · exact fiveGraphClassified10_0001101010
  · exact fiveGraphClassified10_0001101011
  · exact fiveGraphClassified10_0001101100
  · exact fiveGraphClassified10_0001101101
  · exact fiveGraphClassified10_0001101110
  · exact fiveGraphClassified10_0001101111
private theorem fiveGraphClassified6_000111 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false false false true true true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false false false true true true t =
      FiveGraphEdgeCode.literal false false false true true true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0001110000
  · exact fiveGraphClassified10_0001110001
  · exact fiveGraphClassified10_0001110010
  · exact fiveGraphClassified10_0001110011
  · exact fiveGraphClassified10_0001110100
  · exact fiveGraphClassified10_0001110101
  · exact fiveGraphClassified10_0001110110
  · exact fiveGraphClassified10_0001110111
  · exact fiveGraphClassified10_0001111000
  · exact fiveGraphClassified10_0001111001
  · exact fiveGraphClassified10_0001111010
  · exact fiveGraphClassified10_0001111011
  · exact fiveGraphClassified10_0001111100
  · exact fiveGraphClassified10_0001111101
  · exact fiveGraphClassified10_0001111110
  · exact fiveGraphClassified10_0001111111
private theorem fiveGraphClassified6_001000 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false false true false false false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false false true false false false t =
      FiveGraphEdgeCode.literal false false true false false false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0010000000
  · exact fiveGraphClassified10_0010000001
  · exact fiveGraphClassified10_0010000010
  · exact fiveGraphClassified10_0010000011
  · exact fiveGraphClassified10_0010000100
  · exact fiveGraphClassified10_0010000101
  · exact fiveGraphClassified10_0010000110
  · exact fiveGraphClassified10_0010000111
  · exact fiveGraphClassified10_0010001000
  · exact fiveGraphClassified10_0010001001
  · exact fiveGraphClassified10_0010001010
  · exact fiveGraphClassified10_0010001011
  · exact fiveGraphClassified10_0010001100
  · exact fiveGraphClassified10_0010001101
  · exact fiveGraphClassified10_0010001110
  · exact fiveGraphClassified10_0010001111
private theorem fiveGraphClassified6_001001 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false false true false false true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false false true false false true t =
      FiveGraphEdgeCode.literal false false true false false true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0010010000
  · exact fiveGraphClassified10_0010010001
  · exact fiveGraphClassified10_0010010010
  · exact fiveGraphClassified10_0010010011
  · exact fiveGraphClassified10_0010010100
  · exact fiveGraphClassified10_0010010101
  · exact fiveGraphClassified10_0010010110
  · exact fiveGraphClassified10_0010010111
  · exact fiveGraphClassified10_0010011000
  · exact fiveGraphClassified10_0010011001
  · exact fiveGraphClassified10_0010011010
  · exact fiveGraphClassified10_0010011011
  · exact fiveGraphClassified10_0010011100
  · exact fiveGraphClassified10_0010011101
  · exact fiveGraphClassified10_0010011110
  · exact fiveGraphClassified10_0010011111
private theorem fiveGraphClassified6_001010 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false false true false true false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false false true false true false t =
      FiveGraphEdgeCode.literal false false true false true false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0010100000
  · exact fiveGraphClassified10_0010100001
  · exact fiveGraphClassified10_0010100010
  · exact fiveGraphClassified10_0010100011
  · exact fiveGraphClassified10_0010100100
  · exact fiveGraphClassified10_0010100101
  · exact fiveGraphClassified10_0010100110
  · exact fiveGraphClassified10_0010100111
  · exact fiveGraphClassified10_0010101000
  · exact fiveGraphClassified10_0010101001
  · exact fiveGraphClassified10_0010101010
  · exact fiveGraphClassified10_0010101011
  · exact fiveGraphClassified10_0010101100
  · exact fiveGraphClassified10_0010101101
  · exact fiveGraphClassified10_0010101110
  · exact fiveGraphClassified10_0010101111
private theorem fiveGraphClassified6_001011 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false false true false true true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false false true false true true t =
      FiveGraphEdgeCode.literal false false true false true true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0010110000
  · exact fiveGraphClassified10_0010110001
  · exact fiveGraphClassified10_0010110010
  · exact fiveGraphClassified10_0010110011
  · exact fiveGraphClassified10_0010110100
  · exact fiveGraphClassified10_0010110101
  · exact fiveGraphClassified10_0010110110
  · exact fiveGraphClassified10_0010110111
  · exact fiveGraphClassified10_0010111000
  · exact fiveGraphClassified10_0010111001
  · exact fiveGraphClassified10_0010111010
  · exact fiveGraphClassified10_0010111011
  · exact fiveGraphClassified10_0010111100
  · exact fiveGraphClassified10_0010111101
  · exact fiveGraphClassified10_0010111110
  · exact fiveGraphClassified10_0010111111
private theorem fiveGraphClassified6_001100 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false false true true false false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false false true true false false t =
      FiveGraphEdgeCode.literal false false true true false false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0011000000
  · exact fiveGraphClassified10_0011000001
  · exact fiveGraphClassified10_0011000010
  · exact fiveGraphClassified10_0011000011
  · exact fiveGraphClassified10_0011000100
  · exact fiveGraphClassified10_0011000101
  · exact fiveGraphClassified10_0011000110
  · exact fiveGraphClassified10_0011000111
  · exact fiveGraphClassified10_0011001000
  · exact fiveGraphClassified10_0011001001
  · exact fiveGraphClassified10_0011001010
  · exact fiveGraphClassified10_0011001011
  · exact fiveGraphClassified10_0011001100
  · exact fiveGraphClassified10_0011001101
  · exact fiveGraphClassified10_0011001110
  · exact fiveGraphClassified10_0011001111
private theorem fiveGraphClassified6_001101 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false false true true false true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false false true true false true t =
      FiveGraphEdgeCode.literal false false true true false true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0011010000
  · exact fiveGraphClassified10_0011010001
  · exact fiveGraphClassified10_0011010010
  · exact fiveGraphClassified10_0011010011
  · exact fiveGraphClassified10_0011010100
  · exact fiveGraphClassified10_0011010101
  · exact fiveGraphClassified10_0011010110
  · exact fiveGraphClassified10_0011010111
  · exact fiveGraphClassified10_0011011000
  · exact fiveGraphClassified10_0011011001
  · exact fiveGraphClassified10_0011011010
  · exact fiveGraphClassified10_0011011011
  · exact fiveGraphClassified10_0011011100
  · exact fiveGraphClassified10_0011011101
  · exact fiveGraphClassified10_0011011110
  · exact fiveGraphClassified10_0011011111
private theorem fiveGraphClassified6_001110 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false false true true true false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false false true true true false t =
      FiveGraphEdgeCode.literal false false true true true false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0011100000
  · exact fiveGraphClassified10_0011100001
  · exact fiveGraphClassified10_0011100010
  · exact fiveGraphClassified10_0011100011
  · exact fiveGraphClassified10_0011100100
  · exact fiveGraphClassified10_0011100101
  · exact fiveGraphClassified10_0011100110
  · exact fiveGraphClassified10_0011100111
  · exact fiveGraphClassified10_0011101000
  · exact fiveGraphClassified10_0011101001
  · exact fiveGraphClassified10_0011101010
  · exact fiveGraphClassified10_0011101011
  · exact fiveGraphClassified10_0011101100
  · exact fiveGraphClassified10_0011101101
  · exact fiveGraphClassified10_0011101110
  · exact fiveGraphClassified10_0011101111
private theorem fiveGraphClassified6_001111 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false false true true true true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false false true true true true t =
      FiveGraphEdgeCode.literal false false true true true true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0011110000
  · exact fiveGraphClassified10_0011110001
  · exact fiveGraphClassified10_0011110010
  · exact fiveGraphClassified10_0011110011
  · exact fiveGraphClassified10_0011110100
  · exact fiveGraphClassified10_0011110101
  · exact fiveGraphClassified10_0011110110
  · exact fiveGraphClassified10_0011110111
  · exact fiveGraphClassified10_0011111000
  · exact fiveGraphClassified10_0011111001
  · exact fiveGraphClassified10_0011111010
  · exact fiveGraphClassified10_0011111011
  · exact fiveGraphClassified10_0011111100
  · exact fiveGraphClassified10_0011111101
  · exact fiveGraphClassified10_0011111110
  · exact fiveGraphClassified10_0011111111
private theorem fiveGraphClassified6_010000 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false true false false false false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false true false false false false t =
      FiveGraphEdgeCode.literal false true false false false false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0100000000
  · exact fiveGraphClassified10_0100000001
  · exact fiveGraphClassified10_0100000010
  · exact fiveGraphClassified10_0100000011
  · exact fiveGraphClassified10_0100000100
  · exact fiveGraphClassified10_0100000101
  · exact fiveGraphClassified10_0100000110
  · exact fiveGraphClassified10_0100000111
  · exact fiveGraphClassified10_0100001000
  · exact fiveGraphClassified10_0100001001
  · exact fiveGraphClassified10_0100001010
  · exact fiveGraphClassified10_0100001011
  · exact fiveGraphClassified10_0100001100
  · exact fiveGraphClassified10_0100001101
  · exact fiveGraphClassified10_0100001110
  · exact fiveGraphClassified10_0100001111
private theorem fiveGraphClassified6_010001 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false true false false false true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false true false false false true t =
      FiveGraphEdgeCode.literal false true false false false true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0100010000
  · exact fiveGraphClassified10_0100010001
  · exact fiveGraphClassified10_0100010010
  · exact fiveGraphClassified10_0100010011
  · exact fiveGraphClassified10_0100010100
  · exact fiveGraphClassified10_0100010101
  · exact fiveGraphClassified10_0100010110
  · exact fiveGraphClassified10_0100010111
  · exact fiveGraphClassified10_0100011000
  · exact fiveGraphClassified10_0100011001
  · exact fiveGraphClassified10_0100011010
  · exact fiveGraphClassified10_0100011011
  · exact fiveGraphClassified10_0100011100
  · exact fiveGraphClassified10_0100011101
  · exact fiveGraphClassified10_0100011110
  · exact fiveGraphClassified10_0100011111
private theorem fiveGraphClassified6_010010 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false true false false true false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false true false false true false t =
      FiveGraphEdgeCode.literal false true false false true false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0100100000
  · exact fiveGraphClassified10_0100100001
  · exact fiveGraphClassified10_0100100010
  · exact fiveGraphClassified10_0100100011
  · exact fiveGraphClassified10_0100100100
  · exact fiveGraphClassified10_0100100101
  · exact fiveGraphClassified10_0100100110
  · exact fiveGraphClassified10_0100100111
  · exact fiveGraphClassified10_0100101000
  · exact fiveGraphClassified10_0100101001
  · exact fiveGraphClassified10_0100101010
  · exact fiveGraphClassified10_0100101011
  · exact fiveGraphClassified10_0100101100
  · exact fiveGraphClassified10_0100101101
  · exact fiveGraphClassified10_0100101110
  · exact fiveGraphClassified10_0100101111
private theorem fiveGraphClassified6_010011 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false true false false true true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false true false false true true t =
      FiveGraphEdgeCode.literal false true false false true true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0100110000
  · exact fiveGraphClassified10_0100110001
  · exact fiveGraphClassified10_0100110010
  · exact fiveGraphClassified10_0100110011
  · exact fiveGraphClassified10_0100110100
  · exact fiveGraphClassified10_0100110101
  · exact fiveGraphClassified10_0100110110
  · exact fiveGraphClassified10_0100110111
  · exact fiveGraphClassified10_0100111000
  · exact fiveGraphClassified10_0100111001
  · exact fiveGraphClassified10_0100111010
  · exact fiveGraphClassified10_0100111011
  · exact fiveGraphClassified10_0100111100
  · exact fiveGraphClassified10_0100111101
  · exact fiveGraphClassified10_0100111110
  · exact fiveGraphClassified10_0100111111
private theorem fiveGraphClassified6_010100 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false true false true false false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false true false true false false t =
      FiveGraphEdgeCode.literal false true false true false false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0101000000
  · exact fiveGraphClassified10_0101000001
  · exact fiveGraphClassified10_0101000010
  · exact fiveGraphClassified10_0101000011
  · exact fiveGraphClassified10_0101000100
  · exact fiveGraphClassified10_0101000101
  · exact fiveGraphClassified10_0101000110
  · exact fiveGraphClassified10_0101000111
  · exact fiveGraphClassified10_0101001000
  · exact fiveGraphClassified10_0101001001
  · exact fiveGraphClassified10_0101001010
  · exact fiveGraphClassified10_0101001011
  · exact fiveGraphClassified10_0101001100
  · exact fiveGraphClassified10_0101001101
  · exact fiveGraphClassified10_0101001110
  · exact fiveGraphClassified10_0101001111
private theorem fiveGraphClassified6_010101 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false true false true false true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false true false true false true t =
      FiveGraphEdgeCode.literal false true false true false true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0101010000
  · exact fiveGraphClassified10_0101010001
  · exact fiveGraphClassified10_0101010010
  · exact fiveGraphClassified10_0101010011
  · exact fiveGraphClassified10_0101010100
  · exact fiveGraphClassified10_0101010101
  · exact fiveGraphClassified10_0101010110
  · exact fiveGraphClassified10_0101010111
  · exact fiveGraphClassified10_0101011000
  · exact fiveGraphClassified10_0101011001
  · exact fiveGraphClassified10_0101011010
  · exact fiveGraphClassified10_0101011011
  · exact fiveGraphClassified10_0101011100
  · exact fiveGraphClassified10_0101011101
  · exact fiveGraphClassified10_0101011110
  · exact fiveGraphClassified10_0101011111
private theorem fiveGraphClassified6_010110 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false true false true true false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false true false true true false t =
      FiveGraphEdgeCode.literal false true false true true false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0101100000
  · exact fiveGraphClassified10_0101100001
  · exact fiveGraphClassified10_0101100010
  · exact fiveGraphClassified10_0101100011
  · exact fiveGraphClassified10_0101100100
  · exact fiveGraphClassified10_0101100101
  · exact fiveGraphClassified10_0101100110
  · exact fiveGraphClassified10_0101100111
  · exact fiveGraphClassified10_0101101000
  · exact fiveGraphClassified10_0101101001
  · exact fiveGraphClassified10_0101101010
  · exact fiveGraphClassified10_0101101011
  · exact fiveGraphClassified10_0101101100
  · exact fiveGraphClassified10_0101101101
  · exact fiveGraphClassified10_0101101110
  · exact fiveGraphClassified10_0101101111
private theorem fiveGraphClassified6_010111 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false true false true true true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false true false true true true t =
      FiveGraphEdgeCode.literal false true false true true true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0101110000
  · exact fiveGraphClassified10_0101110001
  · exact fiveGraphClassified10_0101110010
  · exact fiveGraphClassified10_0101110011
  · exact fiveGraphClassified10_0101110100
  · exact fiveGraphClassified10_0101110101
  · exact fiveGraphClassified10_0101110110
  · exact fiveGraphClassified10_0101110111
  · exact fiveGraphClassified10_0101111000
  · exact fiveGraphClassified10_0101111001
  · exact fiveGraphClassified10_0101111010
  · exact fiveGraphClassified10_0101111011
  · exact fiveGraphClassified10_0101111100
  · exact fiveGraphClassified10_0101111101
  · exact fiveGraphClassified10_0101111110
  · exact fiveGraphClassified10_0101111111
private theorem fiveGraphClassified6_011000 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false true true false false false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false true true false false false t =
      FiveGraphEdgeCode.literal false true true false false false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0110000000
  · exact fiveGraphClassified10_0110000001
  · exact fiveGraphClassified10_0110000010
  · exact fiveGraphClassified10_0110000011
  · exact fiveGraphClassified10_0110000100
  · exact fiveGraphClassified10_0110000101
  · exact fiveGraphClassified10_0110000110
  · exact fiveGraphClassified10_0110000111
  · exact fiveGraphClassified10_0110001000
  · exact fiveGraphClassified10_0110001001
  · exact fiveGraphClassified10_0110001010
  · exact fiveGraphClassified10_0110001011
  · exact fiveGraphClassified10_0110001100
  · exact fiveGraphClassified10_0110001101
  · exact fiveGraphClassified10_0110001110
  · exact fiveGraphClassified10_0110001111
private theorem fiveGraphClassified6_011001 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false true true false false true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false true true false false true t =
      FiveGraphEdgeCode.literal false true true false false true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0110010000
  · exact fiveGraphClassified10_0110010001
  · exact fiveGraphClassified10_0110010010
  · exact fiveGraphClassified10_0110010011
  · exact fiveGraphClassified10_0110010100
  · exact fiveGraphClassified10_0110010101
  · exact fiveGraphClassified10_0110010110
  · exact fiveGraphClassified10_0110010111
  · exact fiveGraphClassified10_0110011000
  · exact fiveGraphClassified10_0110011001
  · exact fiveGraphClassified10_0110011010
  · exact fiveGraphClassified10_0110011011
  · exact fiveGraphClassified10_0110011100
  · exact fiveGraphClassified10_0110011101
  · exact fiveGraphClassified10_0110011110
  · exact fiveGraphClassified10_0110011111
private theorem fiveGraphClassified6_011010 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false true true false true false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false true true false true false t =
      FiveGraphEdgeCode.literal false true true false true false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0110100000
  · exact fiveGraphClassified10_0110100001
  · exact fiveGraphClassified10_0110100010
  · exact fiveGraphClassified10_0110100011
  · exact fiveGraphClassified10_0110100100
  · exact fiveGraphClassified10_0110100101
  · exact fiveGraphClassified10_0110100110
  · exact fiveGraphClassified10_0110100111
  · exact fiveGraphClassified10_0110101000
  · exact fiveGraphClassified10_0110101001
  · exact fiveGraphClassified10_0110101010
  · exact fiveGraphClassified10_0110101011
  · exact fiveGraphClassified10_0110101100
  · exact fiveGraphClassified10_0110101101
  · exact fiveGraphClassified10_0110101110
  · exact fiveGraphClassified10_0110101111
private theorem fiveGraphClassified6_011011 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false true true false true true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false true true false true true t =
      FiveGraphEdgeCode.literal false true true false true true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0110110000
  · exact fiveGraphClassified10_0110110001
  · exact fiveGraphClassified10_0110110010
  · exact fiveGraphClassified10_0110110011
  · exact fiveGraphClassified10_0110110100
  · exact fiveGraphClassified10_0110110101
  · exact fiveGraphClassified10_0110110110
  · exact fiveGraphClassified10_0110110111
  · exact fiveGraphClassified10_0110111000
  · exact fiveGraphClassified10_0110111001
  · exact fiveGraphClassified10_0110111010
  · exact fiveGraphClassified10_0110111011
  · exact fiveGraphClassified10_0110111100
  · exact fiveGraphClassified10_0110111101
  · exact fiveGraphClassified10_0110111110
  · exact fiveGraphClassified10_0110111111
private theorem fiveGraphClassified6_011100 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false true true true false false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false true true true false false t =
      FiveGraphEdgeCode.literal false true true true false false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0111000000
  · exact fiveGraphClassified10_0111000001
  · exact fiveGraphClassified10_0111000010
  · exact fiveGraphClassified10_0111000011
  · exact fiveGraphClassified10_0111000100
  · exact fiveGraphClassified10_0111000101
  · exact fiveGraphClassified10_0111000110
  · exact fiveGraphClassified10_0111000111
  · exact fiveGraphClassified10_0111001000
  · exact fiveGraphClassified10_0111001001
  · exact fiveGraphClassified10_0111001010
  · exact fiveGraphClassified10_0111001011
  · exact fiveGraphClassified10_0111001100
  · exact fiveGraphClassified10_0111001101
  · exact fiveGraphClassified10_0111001110
  · exact fiveGraphClassified10_0111001111
private theorem fiveGraphClassified6_011101 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false true true true false true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false true true true false true t =
      FiveGraphEdgeCode.literal false true true true false true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0111010000
  · exact fiveGraphClassified10_0111010001
  · exact fiveGraphClassified10_0111010010
  · exact fiveGraphClassified10_0111010011
  · exact fiveGraphClassified10_0111010100
  · exact fiveGraphClassified10_0111010101
  · exact fiveGraphClassified10_0111010110
  · exact fiveGraphClassified10_0111010111
  · exact fiveGraphClassified10_0111011000
  · exact fiveGraphClassified10_0111011001
  · exact fiveGraphClassified10_0111011010
  · exact fiveGraphClassified10_0111011011
  · exact fiveGraphClassified10_0111011100
  · exact fiveGraphClassified10_0111011101
  · exact fiveGraphClassified10_0111011110
  · exact fiveGraphClassified10_0111011111
private theorem fiveGraphClassified6_011110 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false true true true true false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false true true true true false t =
      FiveGraphEdgeCode.literal false true true true true false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0111100000
  · exact fiveGraphClassified10_0111100001
  · exact fiveGraphClassified10_0111100010
  · exact fiveGraphClassified10_0111100011
  · exact fiveGraphClassified10_0111100100
  · exact fiveGraphClassified10_0111100101
  · exact fiveGraphClassified10_0111100110
  · exact fiveGraphClassified10_0111100111
  · exact fiveGraphClassified10_0111101000
  · exact fiveGraphClassified10_0111101001
  · exact fiveGraphClassified10_0111101010
  · exact fiveGraphClassified10_0111101011
  · exact fiveGraphClassified10_0111101100
  · exact fiveGraphClassified10_0111101101
  · exact fiveGraphClassified10_0111101110
  · exact fiveGraphClassified10_0111101111
private theorem fiveGraphClassified6_011111 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 false true true true true true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 false true true true true true t =
      FiveGraphEdgeCode.literal false true true true true true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_0111110000
  · exact fiveGraphClassified10_0111110001
  · exact fiveGraphClassified10_0111110010
  · exact fiveGraphClassified10_0111110011
  · exact fiveGraphClassified10_0111110100
  · exact fiveGraphClassified10_0111110101
  · exact fiveGraphClassified10_0111110110
  · exact fiveGraphClassified10_0111110111
  · exact fiveGraphClassified10_0111111000
  · exact fiveGraphClassified10_0111111001
  · exact fiveGraphClassified10_0111111010
  · exact fiveGraphClassified10_0111111011
  · exact fiveGraphClassified10_0111111100
  · exact fiveGraphClassified10_0111111101
  · exact fiveGraphClassified10_0111111110
  · exact fiveGraphClassified10_0111111111
private theorem fiveGraphClassified6_100000 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true false false false false false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true false false false false false t =
      FiveGraphEdgeCode.literal true false false false false false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1000000000
  · exact fiveGraphClassified10_1000000001
  · exact fiveGraphClassified10_1000000010
  · exact fiveGraphClassified10_1000000011
  · exact fiveGraphClassified10_1000000100
  · exact fiveGraphClassified10_1000000101
  · exact fiveGraphClassified10_1000000110
  · exact fiveGraphClassified10_1000000111
  · exact fiveGraphClassified10_1000001000
  · exact fiveGraphClassified10_1000001001
  · exact fiveGraphClassified10_1000001010
  · exact fiveGraphClassified10_1000001011
  · exact fiveGraphClassified10_1000001100
  · exact fiveGraphClassified10_1000001101
  · exact fiveGraphClassified10_1000001110
  · exact fiveGraphClassified10_1000001111
private theorem fiveGraphClassified6_100001 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true false false false false true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true false false false false true t =
      FiveGraphEdgeCode.literal true false false false false true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1000010000
  · exact fiveGraphClassified10_1000010001
  · exact fiveGraphClassified10_1000010010
  · exact fiveGraphClassified10_1000010011
  · exact fiveGraphClassified10_1000010100
  · exact fiveGraphClassified10_1000010101
  · exact fiveGraphClassified10_1000010110
  · exact fiveGraphClassified10_1000010111
  · exact fiveGraphClassified10_1000011000
  · exact fiveGraphClassified10_1000011001
  · exact fiveGraphClassified10_1000011010
  · exact fiveGraphClassified10_1000011011
  · exact fiveGraphClassified10_1000011100
  · exact fiveGraphClassified10_1000011101
  · exact fiveGraphClassified10_1000011110
  · exact fiveGraphClassified10_1000011111
private theorem fiveGraphClassified6_100010 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true false false false true false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true false false false true false t =
      FiveGraphEdgeCode.literal true false false false true false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1000100000
  · exact fiveGraphClassified10_1000100001
  · exact fiveGraphClassified10_1000100010
  · exact fiveGraphClassified10_1000100011
  · exact fiveGraphClassified10_1000100100
  · exact fiveGraphClassified10_1000100101
  · exact fiveGraphClassified10_1000100110
  · exact fiveGraphClassified10_1000100111
  · exact fiveGraphClassified10_1000101000
  · exact fiveGraphClassified10_1000101001
  · exact fiveGraphClassified10_1000101010
  · exact fiveGraphClassified10_1000101011
  · exact fiveGraphClassified10_1000101100
  · exact fiveGraphClassified10_1000101101
  · exact fiveGraphClassified10_1000101110
  · exact fiveGraphClassified10_1000101111
private theorem fiveGraphClassified6_100011 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true false false false true true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true false false false true true t =
      FiveGraphEdgeCode.literal true false false false true true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1000110000
  · exact fiveGraphClassified10_1000110001
  · exact fiveGraphClassified10_1000110010
  · exact fiveGraphClassified10_1000110011
  · exact fiveGraphClassified10_1000110100
  · exact fiveGraphClassified10_1000110101
  · exact fiveGraphClassified10_1000110110
  · exact fiveGraphClassified10_1000110111
  · exact fiveGraphClassified10_1000111000
  · exact fiveGraphClassified10_1000111001
  · exact fiveGraphClassified10_1000111010
  · exact fiveGraphClassified10_1000111011
  · exact fiveGraphClassified10_1000111100
  · exact fiveGraphClassified10_1000111101
  · exact fiveGraphClassified10_1000111110
  · exact fiveGraphClassified10_1000111111
private theorem fiveGraphClassified6_100100 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true false false true false false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true false false true false false t =
      FiveGraphEdgeCode.literal true false false true false false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1001000000
  · exact fiveGraphClassified10_1001000001
  · exact fiveGraphClassified10_1001000010
  · exact fiveGraphClassified10_1001000011
  · exact fiveGraphClassified10_1001000100
  · exact fiveGraphClassified10_1001000101
  · exact fiveGraphClassified10_1001000110
  · exact fiveGraphClassified10_1001000111
  · exact fiveGraphClassified10_1001001000
  · exact fiveGraphClassified10_1001001001
  · exact fiveGraphClassified10_1001001010
  · exact fiveGraphClassified10_1001001011
  · exact fiveGraphClassified10_1001001100
  · exact fiveGraphClassified10_1001001101
  · exact fiveGraphClassified10_1001001110
  · exact fiveGraphClassified10_1001001111
private theorem fiveGraphClassified6_100101 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true false false true false true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true false false true false true t =
      FiveGraphEdgeCode.literal true false false true false true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1001010000
  · exact fiveGraphClassified10_1001010001
  · exact fiveGraphClassified10_1001010010
  · exact fiveGraphClassified10_1001010011
  · exact fiveGraphClassified10_1001010100
  · exact fiveGraphClassified10_1001010101
  · exact fiveGraphClassified10_1001010110
  · exact fiveGraphClassified10_1001010111
  · exact fiveGraphClassified10_1001011000
  · exact fiveGraphClassified10_1001011001
  · exact fiveGraphClassified10_1001011010
  · exact fiveGraphClassified10_1001011011
  · exact fiveGraphClassified10_1001011100
  · exact fiveGraphClassified10_1001011101
  · exact fiveGraphClassified10_1001011110
  · exact fiveGraphClassified10_1001011111
private theorem fiveGraphClassified6_100110 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true false false true true false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true false false true true false t =
      FiveGraphEdgeCode.literal true false false true true false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1001100000
  · exact fiveGraphClassified10_1001100001
  · exact fiveGraphClassified10_1001100010
  · exact fiveGraphClassified10_1001100011
  · exact fiveGraphClassified10_1001100100
  · exact fiveGraphClassified10_1001100101
  · exact fiveGraphClassified10_1001100110
  · exact fiveGraphClassified10_1001100111
  · exact fiveGraphClassified10_1001101000
  · exact fiveGraphClassified10_1001101001
  · exact fiveGraphClassified10_1001101010
  · exact fiveGraphClassified10_1001101011
  · exact fiveGraphClassified10_1001101100
  · exact fiveGraphClassified10_1001101101
  · exact fiveGraphClassified10_1001101110
  · exact fiveGraphClassified10_1001101111
private theorem fiveGraphClassified6_100111 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true false false true true true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true false false true true true t =
      FiveGraphEdgeCode.literal true false false true true true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1001110000
  · exact fiveGraphClassified10_1001110001
  · exact fiveGraphClassified10_1001110010
  · exact fiveGraphClassified10_1001110011
  · exact fiveGraphClassified10_1001110100
  · exact fiveGraphClassified10_1001110101
  · exact fiveGraphClassified10_1001110110
  · exact fiveGraphClassified10_1001110111
  · exact fiveGraphClassified10_1001111000
  · exact fiveGraphClassified10_1001111001
  · exact fiveGraphClassified10_1001111010
  · exact fiveGraphClassified10_1001111011
  · exact fiveGraphClassified10_1001111100
  · exact fiveGraphClassified10_1001111101
  · exact fiveGraphClassified10_1001111110
  · exact fiveGraphClassified10_1001111111
private theorem fiveGraphClassified6_101000 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true false true false false false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true false true false false false t =
      FiveGraphEdgeCode.literal true false true false false false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1010000000
  · exact fiveGraphClassified10_1010000001
  · exact fiveGraphClassified10_1010000010
  · exact fiveGraphClassified10_1010000011
  · exact fiveGraphClassified10_1010000100
  · exact fiveGraphClassified10_1010000101
  · exact fiveGraphClassified10_1010000110
  · exact fiveGraphClassified10_1010000111
  · exact fiveGraphClassified10_1010001000
  · exact fiveGraphClassified10_1010001001
  · exact fiveGraphClassified10_1010001010
  · exact fiveGraphClassified10_1010001011
  · exact fiveGraphClassified10_1010001100
  · exact fiveGraphClassified10_1010001101
  · exact fiveGraphClassified10_1010001110
  · exact fiveGraphClassified10_1010001111
private theorem fiveGraphClassified6_101001 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true false true false false true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true false true false false true t =
      FiveGraphEdgeCode.literal true false true false false true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1010010000
  · exact fiveGraphClassified10_1010010001
  · exact fiveGraphClassified10_1010010010
  · exact fiveGraphClassified10_1010010011
  · exact fiveGraphClassified10_1010010100
  · exact fiveGraphClassified10_1010010101
  · exact fiveGraphClassified10_1010010110
  · exact fiveGraphClassified10_1010010111
  · exact fiveGraphClassified10_1010011000
  · exact fiveGraphClassified10_1010011001
  · exact fiveGraphClassified10_1010011010
  · exact fiveGraphClassified10_1010011011
  · exact fiveGraphClassified10_1010011100
  · exact fiveGraphClassified10_1010011101
  · exact fiveGraphClassified10_1010011110
  · exact fiveGraphClassified10_1010011111
private theorem fiveGraphClassified6_101010 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true false true false true false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true false true false true false t =
      FiveGraphEdgeCode.literal true false true false true false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1010100000
  · exact fiveGraphClassified10_1010100001
  · exact fiveGraphClassified10_1010100010
  · exact fiveGraphClassified10_1010100011
  · exact fiveGraphClassified10_1010100100
  · exact fiveGraphClassified10_1010100101
  · exact fiveGraphClassified10_1010100110
  · exact fiveGraphClassified10_1010100111
  · exact fiveGraphClassified10_1010101000
  · exact fiveGraphClassified10_1010101001
  · exact fiveGraphClassified10_1010101010
  · exact fiveGraphClassified10_1010101011
  · exact fiveGraphClassified10_1010101100
  · exact fiveGraphClassified10_1010101101
  · exact fiveGraphClassified10_1010101110
  · exact fiveGraphClassified10_1010101111
private theorem fiveGraphClassified6_101011 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true false true false true true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true false true false true true t =
      FiveGraphEdgeCode.literal true false true false true true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1010110000
  · exact fiveGraphClassified10_1010110001
  · exact fiveGraphClassified10_1010110010
  · exact fiveGraphClassified10_1010110011
  · exact fiveGraphClassified10_1010110100
  · exact fiveGraphClassified10_1010110101
  · exact fiveGraphClassified10_1010110110
  · exact fiveGraphClassified10_1010110111
  · exact fiveGraphClassified10_1010111000
  · exact fiveGraphClassified10_1010111001
  · exact fiveGraphClassified10_1010111010
  · exact fiveGraphClassified10_1010111011
  · exact fiveGraphClassified10_1010111100
  · exact fiveGraphClassified10_1010111101
  · exact fiveGraphClassified10_1010111110
  · exact fiveGraphClassified10_1010111111
private theorem fiveGraphClassified6_101100 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true false true true false false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true false true true false false t =
      FiveGraphEdgeCode.literal true false true true false false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1011000000
  · exact fiveGraphClassified10_1011000001
  · exact fiveGraphClassified10_1011000010
  · exact fiveGraphClassified10_1011000011
  · exact fiveGraphClassified10_1011000100
  · exact fiveGraphClassified10_1011000101
  · exact fiveGraphClassified10_1011000110
  · exact fiveGraphClassified10_1011000111
  · exact fiveGraphClassified10_1011001000
  · exact fiveGraphClassified10_1011001001
  · exact fiveGraphClassified10_1011001010
  · exact fiveGraphClassified10_1011001011
  · exact fiveGraphClassified10_1011001100
  · exact fiveGraphClassified10_1011001101
  · exact fiveGraphClassified10_1011001110
  · exact fiveGraphClassified10_1011001111
private theorem fiveGraphClassified6_101101 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true false true true false true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true false true true false true t =
      FiveGraphEdgeCode.literal true false true true false true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1011010000
  · exact fiveGraphClassified10_1011010001
  · exact fiveGraphClassified10_1011010010
  · exact fiveGraphClassified10_1011010011
  · exact fiveGraphClassified10_1011010100
  · exact fiveGraphClassified10_1011010101
  · exact fiveGraphClassified10_1011010110
  · exact fiveGraphClassified10_1011010111
  · exact fiveGraphClassified10_1011011000
  · exact fiveGraphClassified10_1011011001
  · exact fiveGraphClassified10_1011011010
  · exact fiveGraphClassified10_1011011011
  · exact fiveGraphClassified10_1011011100
  · exact fiveGraphClassified10_1011011101
  · exact fiveGraphClassified10_1011011110
  · exact fiveGraphClassified10_1011011111
private theorem fiveGraphClassified6_101110 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true false true true true false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true false true true true false t =
      FiveGraphEdgeCode.literal true false true true true false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1011100000
  · exact fiveGraphClassified10_1011100001
  · exact fiveGraphClassified10_1011100010
  · exact fiveGraphClassified10_1011100011
  · exact fiveGraphClassified10_1011100100
  · exact fiveGraphClassified10_1011100101
  · exact fiveGraphClassified10_1011100110
  · exact fiveGraphClassified10_1011100111
  · exact fiveGraphClassified10_1011101000
  · exact fiveGraphClassified10_1011101001
  · exact fiveGraphClassified10_1011101010
  · exact fiveGraphClassified10_1011101011
  · exact fiveGraphClassified10_1011101100
  · exact fiveGraphClassified10_1011101101
  · exact fiveGraphClassified10_1011101110
  · exact fiveGraphClassified10_1011101111
private theorem fiveGraphClassified6_101111 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true false true true true true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true false true true true true t =
      FiveGraphEdgeCode.literal true false true true true true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1011110000
  · exact fiveGraphClassified10_1011110001
  · exact fiveGraphClassified10_1011110010
  · exact fiveGraphClassified10_1011110011
  · exact fiveGraphClassified10_1011110100
  · exact fiveGraphClassified10_1011110101
  · exact fiveGraphClassified10_1011110110
  · exact fiveGraphClassified10_1011110111
  · exact fiveGraphClassified10_1011111000
  · exact fiveGraphClassified10_1011111001
  · exact fiveGraphClassified10_1011111010
  · exact fiveGraphClassified10_1011111011
  · exact fiveGraphClassified10_1011111100
  · exact fiveGraphClassified10_1011111101
  · exact fiveGraphClassified10_1011111110
  · exact fiveGraphClassified10_1011111111
private theorem fiveGraphClassified6_110000 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true true false false false false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true true false false false false t =
      FiveGraphEdgeCode.literal true true false false false false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1100000000
  · exact fiveGraphClassified10_1100000001
  · exact fiveGraphClassified10_1100000010
  · exact fiveGraphClassified10_1100000011
  · exact fiveGraphClassified10_1100000100
  · exact fiveGraphClassified10_1100000101
  · exact fiveGraphClassified10_1100000110
  · exact fiveGraphClassified10_1100000111
  · exact fiveGraphClassified10_1100001000
  · exact fiveGraphClassified10_1100001001
  · exact fiveGraphClassified10_1100001010
  · exact fiveGraphClassified10_1100001011
  · exact fiveGraphClassified10_1100001100
  · exact fiveGraphClassified10_1100001101
  · exact fiveGraphClassified10_1100001110
  · exact fiveGraphClassified10_1100001111
private theorem fiveGraphClassified6_110001 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true true false false false true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true true false false false true t =
      FiveGraphEdgeCode.literal true true false false false true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1100010000
  · exact fiveGraphClassified10_1100010001
  · exact fiveGraphClassified10_1100010010
  · exact fiveGraphClassified10_1100010011
  · exact fiveGraphClassified10_1100010100
  · exact fiveGraphClassified10_1100010101
  · exact fiveGraphClassified10_1100010110
  · exact fiveGraphClassified10_1100010111
  · exact fiveGraphClassified10_1100011000
  · exact fiveGraphClassified10_1100011001
  · exact fiveGraphClassified10_1100011010
  · exact fiveGraphClassified10_1100011011
  · exact fiveGraphClassified10_1100011100
  · exact fiveGraphClassified10_1100011101
  · exact fiveGraphClassified10_1100011110
  · exact fiveGraphClassified10_1100011111
private theorem fiveGraphClassified6_110010 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true true false false true false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true true false false true false t =
      FiveGraphEdgeCode.literal true true false false true false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1100100000
  · exact fiveGraphClassified10_1100100001
  · exact fiveGraphClassified10_1100100010
  · exact fiveGraphClassified10_1100100011
  · exact fiveGraphClassified10_1100100100
  · exact fiveGraphClassified10_1100100101
  · exact fiveGraphClassified10_1100100110
  · exact fiveGraphClassified10_1100100111
  · exact fiveGraphClassified10_1100101000
  · exact fiveGraphClassified10_1100101001
  · exact fiveGraphClassified10_1100101010
  · exact fiveGraphClassified10_1100101011
  · exact fiveGraphClassified10_1100101100
  · exact fiveGraphClassified10_1100101101
  · exact fiveGraphClassified10_1100101110
  · exact fiveGraphClassified10_1100101111
private theorem fiveGraphClassified6_110011 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true true false false true true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true true false false true true t =
      FiveGraphEdgeCode.literal true true false false true true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1100110000
  · exact fiveGraphClassified10_1100110001
  · exact fiveGraphClassified10_1100110010
  · exact fiveGraphClassified10_1100110011
  · exact fiveGraphClassified10_1100110100
  · exact fiveGraphClassified10_1100110101
  · exact fiveGraphClassified10_1100110110
  · exact fiveGraphClassified10_1100110111
  · exact fiveGraphClassified10_1100111000
  · exact fiveGraphClassified10_1100111001
  · exact fiveGraphClassified10_1100111010
  · exact fiveGraphClassified10_1100111011
  · exact fiveGraphClassified10_1100111100
  · exact fiveGraphClassified10_1100111101
  · exact fiveGraphClassified10_1100111110
  · exact fiveGraphClassified10_1100111111
private theorem fiveGraphClassified6_110100 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true true false true false false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true true false true false false t =
      FiveGraphEdgeCode.literal true true false true false false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1101000000
  · exact fiveGraphClassified10_1101000001
  · exact fiveGraphClassified10_1101000010
  · exact fiveGraphClassified10_1101000011
  · exact fiveGraphClassified10_1101000100
  · exact fiveGraphClassified10_1101000101
  · exact fiveGraphClassified10_1101000110
  · exact fiveGraphClassified10_1101000111
  · exact fiveGraphClassified10_1101001000
  · exact fiveGraphClassified10_1101001001
  · exact fiveGraphClassified10_1101001010
  · exact fiveGraphClassified10_1101001011
  · exact fiveGraphClassified10_1101001100
  · exact fiveGraphClassified10_1101001101
  · exact fiveGraphClassified10_1101001110
  · exact fiveGraphClassified10_1101001111
private theorem fiveGraphClassified6_110101 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true true false true false true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true true false true false true t =
      FiveGraphEdgeCode.literal true true false true false true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1101010000
  · exact fiveGraphClassified10_1101010001
  · exact fiveGraphClassified10_1101010010
  · exact fiveGraphClassified10_1101010011
  · exact fiveGraphClassified10_1101010100
  · exact fiveGraphClassified10_1101010101
  · exact fiveGraphClassified10_1101010110
  · exact fiveGraphClassified10_1101010111
  · exact fiveGraphClassified10_1101011000
  · exact fiveGraphClassified10_1101011001
  · exact fiveGraphClassified10_1101011010
  · exact fiveGraphClassified10_1101011011
  · exact fiveGraphClassified10_1101011100
  · exact fiveGraphClassified10_1101011101
  · exact fiveGraphClassified10_1101011110
  · exact fiveGraphClassified10_1101011111
private theorem fiveGraphClassified6_110110 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true true false true true false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true true false true true false t =
      FiveGraphEdgeCode.literal true true false true true false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1101100000
  · exact fiveGraphClassified10_1101100001
  · exact fiveGraphClassified10_1101100010
  · exact fiveGraphClassified10_1101100011
  · exact fiveGraphClassified10_1101100100
  · exact fiveGraphClassified10_1101100101
  · exact fiveGraphClassified10_1101100110
  · exact fiveGraphClassified10_1101100111
  · exact fiveGraphClassified10_1101101000
  · exact fiveGraphClassified10_1101101001
  · exact fiveGraphClassified10_1101101010
  · exact fiveGraphClassified10_1101101011
  · exact fiveGraphClassified10_1101101100
  · exact fiveGraphClassified10_1101101101
  · exact fiveGraphClassified10_1101101110
  · exact fiveGraphClassified10_1101101111
private theorem fiveGraphClassified6_110111 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true true false true true true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true true false true true true t =
      FiveGraphEdgeCode.literal true true false true true true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1101110000
  · exact fiveGraphClassified10_1101110001
  · exact fiveGraphClassified10_1101110010
  · exact fiveGraphClassified10_1101110011
  · exact fiveGraphClassified10_1101110100
  · exact fiveGraphClassified10_1101110101
  · exact fiveGraphClassified10_1101110110
  · exact fiveGraphClassified10_1101110111
  · exact fiveGraphClassified10_1101111000
  · exact fiveGraphClassified10_1101111001
  · exact fiveGraphClassified10_1101111010
  · exact fiveGraphClassified10_1101111011
  · exact fiveGraphClassified10_1101111100
  · exact fiveGraphClassified10_1101111101
  · exact fiveGraphClassified10_1101111110
  · exact fiveGraphClassified10_1101111111
private theorem fiveGraphClassified6_111000 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true true true false false false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true true true false false false t =
      FiveGraphEdgeCode.literal true true true false false false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1110000000
  · exact fiveGraphClassified10_1110000001
  · exact fiveGraphClassified10_1110000010
  · exact fiveGraphClassified10_1110000011
  · exact fiveGraphClassified10_1110000100
  · exact fiveGraphClassified10_1110000101
  · exact fiveGraphClassified10_1110000110
  · exact fiveGraphClassified10_1110000111
  · exact fiveGraphClassified10_1110001000
  · exact fiveGraphClassified10_1110001001
  · exact fiveGraphClassified10_1110001010
  · exact fiveGraphClassified10_1110001011
  · exact fiveGraphClassified10_1110001100
  · exact fiveGraphClassified10_1110001101
  · exact fiveGraphClassified10_1110001110
  · exact fiveGraphClassified10_1110001111
private theorem fiveGraphClassified6_111001 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true true true false false true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true true true false false true t =
      FiveGraphEdgeCode.literal true true true false false true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1110010000
  · exact fiveGraphClassified10_1110010001
  · exact fiveGraphClassified10_1110010010
  · exact fiveGraphClassified10_1110010011
  · exact fiveGraphClassified10_1110010100
  · exact fiveGraphClassified10_1110010101
  · exact fiveGraphClassified10_1110010110
  · exact fiveGraphClassified10_1110010111
  · exact fiveGraphClassified10_1110011000
  · exact fiveGraphClassified10_1110011001
  · exact fiveGraphClassified10_1110011010
  · exact fiveGraphClassified10_1110011011
  · exact fiveGraphClassified10_1110011100
  · exact fiveGraphClassified10_1110011101
  · exact fiveGraphClassified10_1110011110
  · exact fiveGraphClassified10_1110011111
private theorem fiveGraphClassified6_111010 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true true true false true false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true true true false true false t =
      FiveGraphEdgeCode.literal true true true false true false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1110100000
  · exact fiveGraphClassified10_1110100001
  · exact fiveGraphClassified10_1110100010
  · exact fiveGraphClassified10_1110100011
  · exact fiveGraphClassified10_1110100100
  · exact fiveGraphClassified10_1110100101
  · exact fiveGraphClassified10_1110100110
  · exact fiveGraphClassified10_1110100111
  · exact fiveGraphClassified10_1110101000
  · exact fiveGraphClassified10_1110101001
  · exact fiveGraphClassified10_1110101010
  · exact fiveGraphClassified10_1110101011
  · exact fiveGraphClassified10_1110101100
  · exact fiveGraphClassified10_1110101101
  · exact fiveGraphClassified10_1110101110
  · exact fiveGraphClassified10_1110101111
private theorem fiveGraphClassified6_111011 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true true true false true true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true true true false true true t =
      FiveGraphEdgeCode.literal true true true false true true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1110110000
  · exact fiveGraphClassified10_1110110001
  · exact fiveGraphClassified10_1110110010
  · exact fiveGraphClassified10_1110110011
  · exact fiveGraphClassified10_1110110100
  · exact fiveGraphClassified10_1110110101
  · exact fiveGraphClassified10_1110110110
  · exact fiveGraphClassified10_1110110111
  · exact fiveGraphClassified10_1110111000
  · exact fiveGraphClassified10_1110111001
  · exact fiveGraphClassified10_1110111010
  · exact fiveGraphClassified10_1110111011
  · exact fiveGraphClassified10_1110111100
  · exact fiveGraphClassified10_1110111101
  · exact fiveGraphClassified10_1110111110
  · exact fiveGraphClassified10_1110111111
private theorem fiveGraphClassified6_111100 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true true true true false false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true true true true false false t =
      FiveGraphEdgeCode.literal true true true true false false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1111000000
  · exact fiveGraphClassified10_1111000001
  · exact fiveGraphClassified10_1111000010
  · exact fiveGraphClassified10_1111000011
  · exact fiveGraphClassified10_1111000100
  · exact fiveGraphClassified10_1111000101
  · exact fiveGraphClassified10_1111000110
  · exact fiveGraphClassified10_1111000111
  · exact fiveGraphClassified10_1111001000
  · exact fiveGraphClassified10_1111001001
  · exact fiveGraphClassified10_1111001010
  · exact fiveGraphClassified10_1111001011
  · exact fiveGraphClassified10_1111001100
  · exact fiveGraphClassified10_1111001101
  · exact fiveGraphClassified10_1111001110
  · exact fiveGraphClassified10_1111001111
private theorem fiveGraphClassified6_111101 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true true true true false true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true true true true false true t =
      FiveGraphEdgeCode.literal true true true true false true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1111010000
  · exact fiveGraphClassified10_1111010001
  · exact fiveGraphClassified10_1111010010
  · exact fiveGraphClassified10_1111010011
  · exact fiveGraphClassified10_1111010100
  · exact fiveGraphClassified10_1111010101
  · exact fiveGraphClassified10_1111010110
  · exact fiveGraphClassified10_1111010111
  · exact fiveGraphClassified10_1111011000
  · exact fiveGraphClassified10_1111011001
  · exact fiveGraphClassified10_1111011010
  · exact fiveGraphClassified10_1111011011
  · exact fiveGraphClassified10_1111011100
  · exact fiveGraphClassified10_1111011101
  · exact fiveGraphClassified10_1111011110
  · exact fiveGraphClassified10_1111011111
private theorem fiveGraphClassified6_111110 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true true true true true false t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true true true true true false t =
      FiveGraphEdgeCode.literal true true true true true false (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1111100000
  · exact fiveGraphClassified10_1111100001
  · exact fiveGraphClassified10_1111100010
  · exact fiveGraphClassified10_1111100011
  · exact fiveGraphClassified10_1111100100
  · exact fiveGraphClassified10_1111100101
  · exact fiveGraphClassified10_1111100110
  · exact fiveGraphClassified10_1111100111
  · exact fiveGraphClassified10_1111101000
  · exact fiveGraphClassified10_1111101001
  · exact fiveGraphClassified10_1111101010
  · exact fiveGraphClassified10_1111101011
  · exact fiveGraphClassified10_1111101100
  · exact fiveGraphClassified10_1111101101
  · exact fiveGraphClassified10_1111101110
  · exact fiveGraphClassified10_1111101111
private theorem fiveGraphClassified6_111111 : ∀ t : Fin 4 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix6 true true true true true true t) := by
  intro t
  have hc : FiveGraphEdgeCode.withPrefix6 true true true true true true t =
      FiveGraphEdgeCode.literal true true true true true true (t 0) (t 1) (t 2) (t 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₆ : t 0 <;> cases h₇ : t 1 <;>
    cases h₈ : t 2 <;> cases h₉ : t 3
  · exact fiveGraphClassified10_1111110000
  · exact fiveGraphClassified10_1111110001
  · exact fiveGraphClassified10_1111110010
  · exact fiveGraphClassified10_1111110011
  · exact fiveGraphClassified10_1111110100
  · exact fiveGraphClassified10_1111110101
  · exact fiveGraphClassified10_1111110110
  · exact fiveGraphClassified10_1111110111
  · exact fiveGraphClassified10_1111111000
  · exact fiveGraphClassified10_1111111001
  · exact fiveGraphClassified10_1111111010
  · exact fiveGraphClassified10_1111111011
  · exact fiveGraphClassified10_1111111100
  · exact fiveGraphClassified10_1111111101
  · exact fiveGraphClassified10_1111111110
  · exact fiveGraphClassified10_1111111111

private theorem fiveGraphClassified5_00000 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 false false false false false t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 false false false false false t =
      FiveGraphEdgeCode.withPrefix6 false false false false false (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_000000 u
  · exact fiveGraphClassified6_000001 u
private theorem fiveGraphClassified5_00001 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 false false false false true t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 false false false false true t =
      FiveGraphEdgeCode.withPrefix6 false false false false true (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_000010 u
  · exact fiveGraphClassified6_000011 u
private theorem fiveGraphClassified5_00010 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 false false false true false t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 false false false true false t =
      FiveGraphEdgeCode.withPrefix6 false false false true false (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_000100 u
  · exact fiveGraphClassified6_000101 u
private theorem fiveGraphClassified5_00011 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 false false false true true t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 false false false true true t =
      FiveGraphEdgeCode.withPrefix6 false false false true true (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_000110 u
  · exact fiveGraphClassified6_000111 u
private theorem fiveGraphClassified5_00100 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 false false true false false t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 false false true false false t =
      FiveGraphEdgeCode.withPrefix6 false false true false false (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_001000 u
  · exact fiveGraphClassified6_001001 u
private theorem fiveGraphClassified5_00101 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 false false true false true t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 false false true false true t =
      FiveGraphEdgeCode.withPrefix6 false false true false true (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_001010 u
  · exact fiveGraphClassified6_001011 u
private theorem fiveGraphClassified5_00110 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 false false true true false t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 false false true true false t =
      FiveGraphEdgeCode.withPrefix6 false false true true false (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_001100 u
  · exact fiveGraphClassified6_001101 u
private theorem fiveGraphClassified5_00111 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 false false true true true t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 false false true true true t =
      FiveGraphEdgeCode.withPrefix6 false false true true true (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_001110 u
  · exact fiveGraphClassified6_001111 u
private theorem fiveGraphClassified5_01000 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 false true false false false t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 false true false false false t =
      FiveGraphEdgeCode.withPrefix6 false true false false false (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_010000 u
  · exact fiveGraphClassified6_010001 u
private theorem fiveGraphClassified5_01001 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 false true false false true t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 false true false false true t =
      FiveGraphEdgeCode.withPrefix6 false true false false true (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_010010 u
  · exact fiveGraphClassified6_010011 u
private theorem fiveGraphClassified5_01010 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 false true false true false t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 false true false true false t =
      FiveGraphEdgeCode.withPrefix6 false true false true false (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_010100 u
  · exact fiveGraphClassified6_010101 u
private theorem fiveGraphClassified5_01011 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 false true false true true t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 false true false true true t =
      FiveGraphEdgeCode.withPrefix6 false true false true true (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_010110 u
  · exact fiveGraphClassified6_010111 u
private theorem fiveGraphClassified5_01100 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 false true true false false t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 false true true false false t =
      FiveGraphEdgeCode.withPrefix6 false true true false false (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_011000 u
  · exact fiveGraphClassified6_011001 u
private theorem fiveGraphClassified5_01101 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 false true true false true t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 false true true false true t =
      FiveGraphEdgeCode.withPrefix6 false true true false true (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_011010 u
  · exact fiveGraphClassified6_011011 u
private theorem fiveGraphClassified5_01110 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 false true true true false t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 false true true true false t =
      FiveGraphEdgeCode.withPrefix6 false true true true false (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_011100 u
  · exact fiveGraphClassified6_011101 u
private theorem fiveGraphClassified5_01111 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 false true true true true t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 false true true true true t =
      FiveGraphEdgeCode.withPrefix6 false true true true true (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_011110 u
  · exact fiveGraphClassified6_011111 u
private theorem fiveGraphClassified5_10000 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 true false false false false t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 true false false false false t =
      FiveGraphEdgeCode.withPrefix6 true false false false false (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_100000 u
  · exact fiveGraphClassified6_100001 u
private theorem fiveGraphClassified5_10001 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 true false false false true t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 true false false false true t =
      FiveGraphEdgeCode.withPrefix6 true false false false true (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_100010 u
  · exact fiveGraphClassified6_100011 u
private theorem fiveGraphClassified5_10010 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 true false false true false t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 true false false true false t =
      FiveGraphEdgeCode.withPrefix6 true false false true false (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_100100 u
  · exact fiveGraphClassified6_100101 u
private theorem fiveGraphClassified5_10011 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 true false false true true t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 true false false true true t =
      FiveGraphEdgeCode.withPrefix6 true false false true true (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_100110 u
  · exact fiveGraphClassified6_100111 u
private theorem fiveGraphClassified5_10100 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 true false true false false t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 true false true false false t =
      FiveGraphEdgeCode.withPrefix6 true false true false false (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_101000 u
  · exact fiveGraphClassified6_101001 u
private theorem fiveGraphClassified5_10101 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 true false true false true t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 true false true false true t =
      FiveGraphEdgeCode.withPrefix6 true false true false true (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_101010 u
  · exact fiveGraphClassified6_101011 u
private theorem fiveGraphClassified5_10110 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 true false true true false t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 true false true true false t =
      FiveGraphEdgeCode.withPrefix6 true false true true false (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_101100 u
  · exact fiveGraphClassified6_101101 u
private theorem fiveGraphClassified5_10111 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 true false true true true t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 true false true true true t =
      FiveGraphEdgeCode.withPrefix6 true false true true true (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_101110 u
  · exact fiveGraphClassified6_101111 u
private theorem fiveGraphClassified5_11000 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 true true false false false t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 true true false false false t =
      FiveGraphEdgeCode.withPrefix6 true true false false false (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_110000 u
  · exact fiveGraphClassified6_110001 u
private theorem fiveGraphClassified5_11001 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 true true false false true t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 true true false false true t =
      FiveGraphEdgeCode.withPrefix6 true true false false true (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_110010 u
  · exact fiveGraphClassified6_110011 u
private theorem fiveGraphClassified5_11010 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 true true false true false t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 true true false true false t =
      FiveGraphEdgeCode.withPrefix6 true true false true false (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_110100 u
  · exact fiveGraphClassified6_110101 u
private theorem fiveGraphClassified5_11011 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 true true false true true t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 true true false true true t =
      FiveGraphEdgeCode.withPrefix6 true true false true true (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_110110 u
  · exact fiveGraphClassified6_110111 u
private theorem fiveGraphClassified5_11100 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 true true true false false t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 true true true false false t =
      FiveGraphEdgeCode.withPrefix6 true true true false false (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_111000 u
  · exact fiveGraphClassified6_111001 u
private theorem fiveGraphClassified5_11101 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 true true true false true t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 true true true false true t =
      FiveGraphEdgeCode.withPrefix6 true true true false true (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_111010 u
  · exact fiveGraphClassified6_111011 u
private theorem fiveGraphClassified5_11110 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 true true true true false t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 true true true true false t =
      FiveGraphEdgeCode.withPrefix6 true true true true false (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_111100 u
  · exact fiveGraphClassified6_111101 u
private theorem fiveGraphClassified5_11111 : ∀ t : Fin 5 → Bool,
    fiveGraphEdgeCodeClassified (FiveGraphEdgeCode.withPrefix5 true true true true true t) := by
  intro t
  let u : Fin 4 → Bool := ![t 1, t 2, t 3, t 4]
  have ht : FiveGraphEdgeCode.withPrefix5 true true true true true t =
      FiveGraphEdgeCode.withPrefix6 true true true true true (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified6_111110 u
  · exact fiveGraphClassified6_111111 u
private theorem fiveGraphClassified_0000 : ∀ t : Fin 6 → Bool,
    fiveGraphEdgeCodeClassified (.withPrefix false false false false t) := by
  intro t
  let u : Fin 5 → Bool := ![t 1, t 2, t 3, t 4, t 5]
  have ht : FiveGraphEdgeCode.withPrefix false false false false t =
      FiveGraphEdgeCode.withPrefix5 false false false false (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified5_00000 u
  · exact fiveGraphClassified5_00001 u
private theorem fiveGraphClassified_0001 : ∀ t : Fin 6 → Bool,
    fiveGraphEdgeCodeClassified (.withPrefix false false false true t) := by
  intro t
  let u : Fin 5 → Bool := ![t 1, t 2, t 3, t 4, t 5]
  have ht : FiveGraphEdgeCode.withPrefix false false false true t =
      FiveGraphEdgeCode.withPrefix5 false false false true (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified5_00010 u
  · exact fiveGraphClassified5_00011 u
private theorem fiveGraphClassified_0010 : ∀ t : Fin 6 → Bool,
    fiveGraphEdgeCodeClassified (.withPrefix false false true false t) := by
  intro t
  let u : Fin 5 → Bool := ![t 1, t 2, t 3, t 4, t 5]
  have ht : FiveGraphEdgeCode.withPrefix false false true false t =
      FiveGraphEdgeCode.withPrefix5 false false true false (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified5_00100 u
  · exact fiveGraphClassified5_00101 u
private theorem fiveGraphClassified_0011 : ∀ t : Fin 6 → Bool,
    fiveGraphEdgeCodeClassified (.withPrefix false false true true t) := by
  intro t
  let u : Fin 5 → Bool := ![t 1, t 2, t 3, t 4, t 5]
  have ht : FiveGraphEdgeCode.withPrefix false false true true t =
      FiveGraphEdgeCode.withPrefix5 false false true true (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified5_00110 u
  · exact fiveGraphClassified5_00111 u
private theorem fiveGraphClassified_0100 : ∀ t : Fin 6 → Bool,
    fiveGraphEdgeCodeClassified (.withPrefix false true false false t) := by
  intro t
  let u : Fin 5 → Bool := ![t 1, t 2, t 3, t 4, t 5]
  have ht : FiveGraphEdgeCode.withPrefix false true false false t =
      FiveGraphEdgeCode.withPrefix5 false true false false (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified5_01000 u
  · exact fiveGraphClassified5_01001 u
private theorem fiveGraphClassified_0101 : ∀ t : Fin 6 → Bool,
    fiveGraphEdgeCodeClassified (.withPrefix false true false true t) := by
  intro t
  let u : Fin 5 → Bool := ![t 1, t 2, t 3, t 4, t 5]
  have ht : FiveGraphEdgeCode.withPrefix false true false true t =
      FiveGraphEdgeCode.withPrefix5 false true false true (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified5_01010 u
  · exact fiveGraphClassified5_01011 u
private theorem fiveGraphClassified_0110 : ∀ t : Fin 6 → Bool,
    fiveGraphEdgeCodeClassified (.withPrefix false true true false t) := by
  intro t
  let u : Fin 5 → Bool := ![t 1, t 2, t 3, t 4, t 5]
  have ht : FiveGraphEdgeCode.withPrefix false true true false t =
      FiveGraphEdgeCode.withPrefix5 false true true false (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified5_01100 u
  · exact fiveGraphClassified5_01101 u
private theorem fiveGraphClassified_0111 : ∀ t : Fin 6 → Bool,
    fiveGraphEdgeCodeClassified (.withPrefix false true true true t) := by
  intro t
  let u : Fin 5 → Bool := ![t 1, t 2, t 3, t 4, t 5]
  have ht : FiveGraphEdgeCode.withPrefix false true true true t =
      FiveGraphEdgeCode.withPrefix5 false true true true (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified5_01110 u
  · exact fiveGraphClassified5_01111 u
private theorem fiveGraphClassified_1000 : ∀ t : Fin 6 → Bool,
    fiveGraphEdgeCodeClassified (.withPrefix true false false false t) := by
  intro t
  let u : Fin 5 → Bool := ![t 1, t 2, t 3, t 4, t 5]
  have ht : FiveGraphEdgeCode.withPrefix true false false false t =
      FiveGraphEdgeCode.withPrefix5 true false false false (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified5_10000 u
  · exact fiveGraphClassified5_10001 u
private theorem fiveGraphClassified_1001 : ∀ t : Fin 6 → Bool,
    fiveGraphEdgeCodeClassified (.withPrefix true false false true t) := by
  intro t
  let u : Fin 5 → Bool := ![t 1, t 2, t 3, t 4, t 5]
  have ht : FiveGraphEdgeCode.withPrefix true false false true t =
      FiveGraphEdgeCode.withPrefix5 true false false true (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified5_10010 u
  · exact fiveGraphClassified5_10011 u
private theorem fiveGraphClassified_1010 : ∀ t : Fin 6 → Bool,
    fiveGraphEdgeCodeClassified (.withPrefix true false true false t) := by
  intro t
  let u : Fin 5 → Bool := ![t 1, t 2, t 3, t 4, t 5]
  have ht : FiveGraphEdgeCode.withPrefix true false true false t =
      FiveGraphEdgeCode.withPrefix5 true false true false (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified5_10100 u
  · exact fiveGraphClassified5_10101 u
private theorem fiveGraphClassified_1011 : ∀ t : Fin 6 → Bool,
    fiveGraphEdgeCodeClassified (.withPrefix true false true true t) := by
  intro t
  let u : Fin 5 → Bool := ![t 1, t 2, t 3, t 4, t 5]
  have ht : FiveGraphEdgeCode.withPrefix true false true true t =
      FiveGraphEdgeCode.withPrefix5 true false true true (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified5_10110 u
  · exact fiveGraphClassified5_10111 u
private theorem fiveGraphClassified_1100 : ∀ t : Fin 6 → Bool,
    fiveGraphEdgeCodeClassified (.withPrefix true true false false t) := by
  intro t
  let u : Fin 5 → Bool := ![t 1, t 2, t 3, t 4, t 5]
  have ht : FiveGraphEdgeCode.withPrefix true true false false t =
      FiveGraphEdgeCode.withPrefix5 true true false false (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified5_11000 u
  · exact fiveGraphClassified5_11001 u
private theorem fiveGraphClassified_1101 : ∀ t : Fin 6 → Bool,
    fiveGraphEdgeCodeClassified (.withPrefix true true false true t) := by
  intro t
  let u : Fin 5 → Bool := ![t 1, t 2, t 3, t 4, t 5]
  have ht : FiveGraphEdgeCode.withPrefix true true false true t =
      FiveGraphEdgeCode.withPrefix5 true true false true (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified5_11010 u
  · exact fiveGraphClassified5_11011 u
private theorem fiveGraphClassified_1110 : ∀ t : Fin 6 → Bool,
    fiveGraphEdgeCodeClassified (.withPrefix true true true false t) := by
  intro t
  let u : Fin 5 → Bool := ![t 1, t 2, t 3, t 4, t 5]
  have ht : FiveGraphEdgeCode.withPrefix true true true false t =
      FiveGraphEdgeCode.withPrefix5 true true true false (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified5_11100 u
  · exact fiveGraphClassified5_11101 u
private theorem fiveGraphClassified_1111 : ∀ t : Fin 6 → Bool,
    fiveGraphEdgeCodeClassified (.withPrefix true true true true t) := by
  intro t
  let u : Fin 5 → Bool := ![t 1, t 2, t 3, t 4, t 5]
  have ht : FiveGraphEdgeCode.withPrefix true true true true t =
      FiveGraphEdgeCode.withPrefix5 true true true true (t 0) u := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  cases h : t 0
  · exact fiveGraphClassified5_11110 u
  · exact fiveGraphClassified5_11111 u

/-- The proof-producing finite kernel ranges over exactly `2^10`
unordered-edge codes, partitioned into sixteen independently checked
64-code blocks so that no kernel reduction needs an enlarged heartbeat. -/
private theorem finFive_tree_shape_permutation_edgeCode :
    ∀ c : FiveGraphEdgeCode, fiveGraphEdgeCodeClassified c := by
  intro c
  let t : Fin 6 → Bool := ![c 4, c 5, c 6, c 7, c 8, c 9]
  have hc : c = .withPrefix (c 0) (c 1) (c 2) (c 3) t := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  cases h₀ : c 0 <;> cases h₁ : c 1 <;>
    cases h₂ : c 2 <;> cases h₃ : c 3
  · exact fiveGraphClassified_0000 t
  · exact fiveGraphClassified_0001 t
  · exact fiveGraphClassified_0010 t
  · exact fiveGraphClassified_0011 t
  · exact fiveGraphClassified_0100 t
  · exact fiveGraphClassified_0101 t
  · exact fiveGraphClassified_0110 t
  · exact fiveGraphClassified_0111 t
  · exact fiveGraphClassified_1000 t
  · exact fiveGraphClassified_1001 t
  · exact fiveGraphClassified_1010 t
  · exact fiveGraphClassified_1011 t
  · exact fiveGraphClassified_1100 t
  · exact fiveGraphClassified_1101 t
  · exact fiveGraphClassified_1110 t
  · exact fiveGraphClassified_1111 t

/-- Exact five-tree relabeling kernel.  Connectedness and four edges are the
tree criterion on five vertices; the conclusion supplies a concrete
permutation matching one of the three literal distance-one matrices. -/
private theorem finFive_tree_shape_permutation :
    ∀ c : FiveGraphBoolCode,
      (c.graph.Connected ∧ c.graph.edgeFinset.card = 4) →
        (∃ p : Equiv.Perm (Fin 5), ∀ i j,
          c.graph.Adj (p i) (p j) ↔ p5Distance i j = 1) ∨
        (∃ p : Equiv.Perm (Fin 5), ∀ i j,
          c.graph.Adj (p i) (p j) ↔ forkDistance i j = 1) ∨
        (∃ p : Equiv.Perm (Fin 5), ∀ i j,
          c.graph.Adj (p i) (p j) ↔ starDistance i j = 1) := by
  intro c
  let d := fiveGraphEdgeCodeOfGraph c.graph
  have hgraph : d.fullCode.graph = c.graph := by
    exact fiveGraphEdgeCodeOfGraph_graph c.graph
  intro hcondition
  have hdcondition : d.fullCode.graph.Connected ∧
      d.fullCode.graph.edgeFinset.card = 4 := by
    constructor
    · simpa only [hgraph] using hcondition.1
    · have hedge : d.fullCode.graph.edgeFinset = c.graph.edgeFinset := by
        ext e
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset, hgraph]
      rw [hedge]
      exact hcondition.2
  have hd := finFive_tree_shape_permutation_edgeCode d hdcondition
  simpa only [hgraph] using hd

noncomputable def fiveGraphBoolCodeOf (G : SimpleGraph (Fin 5)) :
    FiveGraphBoolCode := by
  classical
  refine ⟨fun u v => decide (G.Adj u v), ?_, ?_⟩
  · intro u v
    simp [G.adj_comm]
  · intro u
    simp

@[simp] theorem fiveGraphBoolCodeOf_graph
    (G : SimpleGraph (Fin 5)) :
    (fiveGraphBoolCodeOf G).graph = G := by
  classical
  ext u v
  simp [FiveGraphBoolCode.graph, fiveGraphBoolCodeOf]

/-- A canonical frame is stronger than a coarse degree shape: it contains
the actual component relabeling and its exact adjacency matrix. -/
inductive ActualFiveTreeFrame (T : PosIntTree 18) : Type
  | p5 (relabel : Fin 5 ≃ EvenComponent T)
      (adjacency : ∀ i j,
        (quotientGraph T).Adj (relabel i) (relabel j) ↔
          p5Distance i j = 1)
  | fork (relabel : Fin 5 ≃ EvenComponent T)
      (adjacency : ∀ i j,
        (quotientGraph T).Adj (relabel i) (relabel j) ↔
          forkDistance i j = 1)
  | star (relabel : Fin 5 ≃ EvenComponent T)
      (adjacency : ∀ i j,
        (quotientGraph T).Adj (relabel i) (relabel j) ↔
          starDistance i j = 1)

/-- The actual four-odd quotient supplies a canonical frame.  The caller
provides only the physical odd-edge count; the permutation and shape are
derived from the quotient tree. -/
theorem exists_actualFiveTreeFrame
    (T : PosIntTree 18) (h4 : ExactlyFourOddEdges T) :
    Nonempty (ActualFiveTreeFrame T) := by
  classical
  let G := quotientGraph T
  let hcard : Fintype.card (EvenComponent T) = 5 :=
    fourOdd_evenComponent_card T h4
  let H : SimpleGraph (Fin 5) := G.overFin hcard
  let base : Fin 5 ≃ EvenComponent T :=
    (G.overFinIso hcard).symm.toEquiv
  let code := fiveGraphBoolCodeOf H
  have hHtree : H.IsTree :=
    (G.overFinIso hcard).isTree_iff.mp (quotientGraph_isTree T)
  have hHedges : H.edgeFinset.card = 4 := by
    have h := hHtree.card_edgeFinset
    norm_num at h ⊢
    omega
  have hcode : code.graph = H := by
    exact fiveGraphBoolCodeOf_graph H
  have hcondition : code.graph.Connected ∧
      code.graph.edgeFinset.card = 4 := by
    constructor
    · simpa only [hcode] using hHtree.isConnected
    · have hedge : code.graph.edgeFinset = H.edgeFinset := by
        ext e
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset, hcode]
      rw [hedge]
      exact hHedges
  rcases finFive_tree_shape_permutation code hcondition with
      ⟨p, hp⟩ | ⟨p, hp⟩ | ⟨p, hp⟩
  · let e : Fin 5 ≃ EvenComponent T := p.trans base
    refine ⟨.p5 e ?_⟩
    intro i j
    have hij := hp i j
    rw [hcode] at hij
    simpa [e, base, H, G, SimpleGraph.overFin] using hij
  · let e : Fin 5 ≃ EvenComponent T := p.trans base
    refine ⟨.fork e ?_⟩
    intro i j
    have hij := hp i j
    rw [hcode] at hij
    simpa [e, base, H, G, SimpleGraph.overFin] using hij
  · let e : Fin 5 ≃ EvenComponent T := p.trans base
    refine ⟨.star e ?_⟩
    intro i j
    have hij := hp i j
    rw [hcode] at hij
    simpa [e, base, H, G, SimpleGraph.overFin] using hij

noncomputable def vertexComponentEquiv {n : ℕ} (T : PosIntTree n) :
    Fin n ≃ Σ C : EvenComponent T, ComponentVertex T C where
  toFun v := ⟨componentOf T v, ⟨v, rfl⟩⟩
  invFun z := z.2.1
  left_inv _ := rfl
  right_inv z := by
    cases z with
    | mk C v =>
        cases v with
        | mk v hv =>
            subst C
            rfl

theorem componentOrder_sum {n : ℕ} (T : PosIntTree n) :
    ∑ C, componentOrder T C = n := by
  classical
  unfold componentOrder
  rw [← Fintype.card_sigma]
  simpa using Fintype.card_congr (vertexComponentEquiv T).symm

noncomputable def baseComponentColor
    (T : PosIntTree 18) (C : EvenComponent T) : Bool :=
  decide (T.dist 0 (componentReference T C).1 % 2 = 0)

theorem component_vertex_rootParity
    (T : PosIntTree 18) (C : EvenComponent T)
    (v : ComponentVertex T C) :
    T.dist 0 v.1 % 2 = T.dist 0 (componentReference T C).1 % 2 := by
  have heven := dist_even_of_component_eq T
    (v.2.trans (componentReference T C).2.symm)
  have hroot := T.root_path_even 0 v.1 (componentReference T C).1
  rw [Nat.even_iff] at heven hroot
  omega

theorem baseColor_order_eq_parityClass
    (T : PosIntTree 18) :
    (∑ C, if baseComponentColor T C then componentOrder T C else 0) =
      T.parityClassSize 0 := by
  classical
  unfold PosIntTree.parityClassSize componentOrder baseComponentColor
  rw [Fintype.card_subtype]
  let selected : Finset (EvenComponent T) :=
    Finset.univ.filter fun C =>
      decide (T.dist 0 (componentReference T C).1 % 2 = 0)
  have hfiber := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin 18)) selected (componentOf T)
  have hparity (i : Fin 18) :
      T.dist 0 (componentReference T (componentOf T i)).1 % 2 =
        T.dist 0 i % 2 := by
    exact (component_vertex_rootParity T (componentOf T i) ⟨i, rfl⟩).symm
  simpa [selected, Fintype.card_subtype, Finset.sum_filter, hparity] using hfiber

noncomputable def sevenColor
    (T : PosIntTree 18) (_hL : IsLeech T) : EvenComponent T → Bool :=
  if _h : T.parityClassSize 0 = 7 then baseComponentColor T
  else fun C => !(baseComponentColor T C)

theorem sevenColor_budgets
    (T : PosIntTree 18) (hL : IsLeech T) :
    (∑ C, if sevenColor T hL C then componentOrder T C else 0) = 7 ∧
    (∑ C, if sevenColor T hL C then 0 else componentOrder T C) = 11 := by
  classical
  have hpartition :
      (∑ C, if baseComponentColor T C then componentOrder T C else 0) +
        (∑ C, if baseComponentColor T C then 0 else componentOrder T C) = 18 := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ C, ((if baseComponentColor T C then componentOrder T C else 0) +
        (if baseComponentColor T C then 0 else componentOrder T C))) =
          ∑ C, componentOrder T C := by
            apply Finset.sum_congr rfl
            intro C hC
            cases baseComponentColor T C <;> simp
      _ = 18 := componentOrder_sum T
  rcases t3_order18_class_sizes hL 0 with h7 | h11
  · rw [sevenColor, dif_pos h7]
    have hbase := baseColor_order_eq_parityClass T
    rw [h7] at hbase
    constructor
    · exact hbase
    · omega
  · have hn7 : T.parityClassSize 0 ≠ 7 := by omega
    rw [sevenColor, dif_neg hn7]
    have hbase := baseColor_order_eq_parityClass T
    rw [h11] at hbase
    constructor
    · calc
        (∑ C, if !(baseComponentColor T C) then componentOrder T C else 0) =
            ∑ C, if baseComponentColor T C then 0 else componentOrder T C := by
          apply Finset.sum_congr rfl
          intro C hC
          cases baseComponentColor T C <;> simp
        _ = 7 := by omega
    · calc
        (∑ C, if !(baseComponentColor T C) then 0 else componentOrder T C) =
            ∑ C, if baseComponentColor T C then componentOrder T C else 0 := by
          apply Finset.sum_congr rfl
          intro C hC
          cases baseComponentColor T C <;> simp
        _ = 11 := hbase

/-- Adjacent actual quotient components lie in opposite root-parity
classes.  The proof uses the one-edge quotient path and hence derives the
colouring from the underlying physical odd bridge. -/
theorem baseComponentColor_adjacent
    (T : PosIntTree 18) {C D : EvenComponent T}
    (h : (quotientGraph T).Adj C D) :
    baseComponentColor T C ≠ baseComponentColor T D := by
  let p : (quotientGraph T).Path C D := SimpleGraph.Path.singleton h
  have hdist := dist_eq_two_mul_routeCost_add_length T p.1 p.2
    (componentReference T C) (componentReference T D)
  have hodd : T.dist (componentReference T C).1
      (componentReference T D).1 % 2 = 1 := by
    rw [hdist]
    simp [p, SimpleGraph.Path.singleton]
  have hroot := T.root_path_even 0 (componentReference T C).1
    (componentReference T D).1
  rw [Nat.even_iff] at hroot
  have hparity : T.dist 0 (componentReference T C).1 % 2 ≠
      T.dist 0 (componentReference T D).1 % 2 := by
    omega
  unfold baseComponentColor
  by_cases hC : T.dist 0 (componentReference T C).1 % 2 = 0
  · have hD : T.dist 0 (componentReference T D).1 % 2 = 1 := by
      have hDlt := Nat.mod_lt (T.dist 0 (componentReference T D).1)
        (by omega : 0 < 2)
      omega
    simp [hC, hD]
  · have hC' : T.dist 0 (componentReference T C).1 % 2 = 1 := by
      have hClt := Nat.mod_lt (T.dist 0 (componentReference T C).1)
        (by omega : 0 < 2)
      omega
    have hD : T.dist 0 (componentReference T D).1 % 2 = 0 := by
      have hDlt := Nat.mod_lt (T.dist 0 (componentReference T D).1)
        (by omega : 0 < 2)
      omega
    simp [hC, hD]

/-- The budget-normalized seven-colour is still the actual quotient-tree
bipartition: normalization can only complement every colour at once. -/
theorem sevenColor_adjacent
    (T : PosIntTree 18) (hL : IsLeech T)
    {C D : EvenComponent T} (h : (quotientGraph T).Adj C D) :
    sevenColor T hL C ≠ sevenColor T hL D := by
  have hbase := baseComponentColor_adjacent T h
  by_cases h7 : T.parityClassSize 0 = 7
  · rw [sevenColor, dif_pos h7]
    exact hbase
  · rw [sevenColor, dif_neg h7]
    cases hC : baseComponentColor T C <;>
      cases hD : baseComponentColor T D <;> simp_all

/-! ## Actual alternating sums and the Gaussian quadratic form -/

noncomputable def quotientDistance {n : ℕ} (T : PosIntTree n)
    (C D : EvenComponent T) : ℕ :=
  (quotientPath T C D).1.length

/-! ### Literal metrics supplied by an actual five-tree frame -/

private theorem quotientDistance_eq_pathLength
    {n : ℕ} (T : PosIntTree n) {C D : EvenComponent T}
    (q : (quotientGraph T).Path C D) :
    quotientDistance T C D = q.1.length := by
  unfold quotientDistance
  rw [← quotientPath_unique T q]

private theorem quotientDistance_eq_zero
    {n : ℕ} (T : PosIntTree n) (C : EvenComponent T) :
    quotientDistance T C C = 0 := by
  let q : (quotientGraph T).Path C C := ⟨SimpleGraph.Walk.nil, by simp⟩
  calc
    quotientDistance T C C = q.1.length :=
      quotientDistance_eq_pathLength T q
    _ = 0 := by rfl

private theorem quotientDistance_eq_one_of_adj
    {n : ℕ} (T : PosIntTree n) {C D : EvenComponent T}
    (hCD : (quotientGraph T).Adj C D) :
    quotientDistance T C D = 1 := by
  let q : (quotientGraph T).Path C D := SimpleGraph.Path.singleton hCD
  calc
    quotientDistance T C D = q.1.length :=
      quotientDistance_eq_pathLength T q
    _ = 1 := by simp [q, SimpleGraph.Path.singleton]

private theorem quotientDistance_eq_two_of_chain
    {n : ℕ} (T : PosIntTree n) {C D E : EvenComponent T}
    (hCD : (quotientGraph T).Adj C D)
    (hDE : (quotientGraph T).Adj D E) (hCE : C ≠ E) :
    quotientDistance T C E = 2 := by
  let walk : (quotientGraph T).Walk C E :=
    SimpleGraph.Walk.cons hCD
      (SimpleGraph.Walk.cons hDE SimpleGraph.Walk.nil)
  have hpath : walk.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simp [walk, hCD.ne, hDE.ne, hCE]
  let q : (quotientGraph T).Path C E := ⟨walk, hpath⟩
  calc
    quotientDistance T C E = q.1.length :=
      quotientDistance_eq_pathLength T q
    _ = 2 := by simp [q, walk]

private theorem quotientDistance_eq_three_of_chain
    {n : ℕ} (T : PosIntTree n) {C D E F : EvenComponent T}
    (hCD : (quotientGraph T).Adj C D)
    (hDE : (quotientGraph T).Adj D E)
    (hEF : (quotientGraph T).Adj E F)
    (hCE : C ≠ E) (hCF : C ≠ F) (hDF : D ≠ F) :
    quotientDistance T C F = 3 := by
  let walk : (quotientGraph T).Walk C F :=
    SimpleGraph.Walk.cons hCD
      (SimpleGraph.Walk.cons hDE
        (SimpleGraph.Walk.cons hEF SimpleGraph.Walk.nil))
  have hpath : walk.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simp [walk, hCD.ne, hDE.ne, hEF.ne, hCE, hCF, hDF]
  let q : (quotientGraph T).Path C F := ⟨walk, hpath⟩
  calc
    quotientDistance T C F = q.1.length :=
      quotientDistance_eq_pathLength T q
    _ = 3 := by simp [q, walk]

private theorem quotientDistance_eq_four_of_chain
    {n : ℕ} (T : PosIntTree n) {A B C D E : EvenComponent T}
    (hAB : (quotientGraph T).Adj A B)
    (hBC : (quotientGraph T).Adj B C)
    (hCD : (quotientGraph T).Adj C D)
    (hDE : (quotientGraph T).Adj D E)
    (hAC : A ≠ C) (hAD : A ≠ D) (hAE : A ≠ E)
    (hBD : B ≠ D) (hBE : B ≠ E) (hCE : C ≠ E) :
    quotientDistance T A E = 4 := by
  let walk : (quotientGraph T).Walk A E :=
    SimpleGraph.Walk.cons hAB
      (SimpleGraph.Walk.cons hBC
        (SimpleGraph.Walk.cons hCD
          (SimpleGraph.Walk.cons hDE SimpleGraph.Walk.nil)))
  have hpath : walk.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simp [walk, hAB.ne, hBC.ne, hCD.ne, hDE.ne,
      hAC, hAD, hAE, hBD, hBE, hCE]
  let q : (quotientGraph T).Path A E := ⟨walk, hpath⟩
  calc
    quotientDistance T A E = q.1.length :=
      quotientDistance_eq_pathLength T q
    _ = 4 := by simp [q, walk]

/-- An actual relabeling with the literal P5 adjacency has exactly the
literal P5 path metric.  Every entry is obtained from an exhibited simple
path in the actual quotient tree. -/
theorem quotientDistance_eq_p5_of_frame
    (T : PosIntTree 18) (e : Fin 5 ≃ EvenComponent T)
    (hadj : ∀ i j,
      (quotientGraph T).Adj (e i) (e j) ↔ p5Distance i j = 1)
    (i j : Fin 5) :
    quotientDistance T (e i) (e j) = p5Distance i j := by
  have hne : ∀ {u v : Fin 5}, u ≠ v → e u ≠ e v := by
    intro u v huv h
    exact huv (e.injective h)
  have h01 := (hadj 0 1).2 (by decide)
  have h12 := (hadj 1 2).2 (by decide)
  have h23 := (hadj 2 3).2 (by decide)
  have h34 := (hadj 3 4).2 (by decide)
  fin_cases i <;> fin_cases j
  · simpa [p5Distance] using quotientDistance_eq_zero T (e 0)
  · simpa [p5Distance] using quotientDistance_eq_one_of_adj T h01
  · simpa [p5Distance] using
      quotientDistance_eq_two_of_chain T h01 h12 (hne (by decide))
  · simpa [p5Distance] using
      quotientDistance_eq_three_of_chain T h01 h12 h23
        (hne (by decide)) (hne (by decide)) (hne (by decide))
  · simpa [p5Distance] using
      quotientDistance_eq_four_of_chain T h01 h12 h23 h34
        (hne (by decide)) (hne (by decide)) (hne (by decide))
        (hne (by decide)) (hne (by decide)) (hne (by decide))
  · simpa [p5Distance] using quotientDistance_eq_one_of_adj T h01.symm
  · simpa [p5Distance] using quotientDistance_eq_zero T (e 1)
  · simpa [p5Distance] using quotientDistance_eq_one_of_adj T h12
  · simpa [p5Distance] using
      quotientDistance_eq_two_of_chain T h12 h23 (hne (by decide))
  · simpa [p5Distance] using
      quotientDistance_eq_three_of_chain T h12 h23 h34
        (hne (by decide)) (hne (by decide)) (hne (by decide))
  · simpa [p5Distance] using
      quotientDistance_eq_two_of_chain T h12.symm h01.symm (hne (by decide))
  · simpa [p5Distance] using quotientDistance_eq_one_of_adj T h12.symm
  · simpa [p5Distance] using quotientDistance_eq_zero T (e 2)
  · simpa [p5Distance] using quotientDistance_eq_one_of_adj T h23
  · simpa [p5Distance] using
      quotientDistance_eq_two_of_chain T h23 h34 (hne (by decide))
  · simpa [p5Distance] using
      quotientDistance_eq_three_of_chain T h23.symm h12.symm h01.symm
        (hne (by decide)) (hne (by decide)) (hne (by decide))
  · simpa [p5Distance] using
      quotientDistance_eq_two_of_chain T h23.symm h12.symm (hne (by decide))
  · simpa [p5Distance] using quotientDistance_eq_one_of_adj T h23.symm
  · simpa [p5Distance] using quotientDistance_eq_zero T (e 3)
  · simpa [p5Distance] using quotientDistance_eq_one_of_adj T h34
  · simpa [p5Distance] using
      quotientDistance_eq_four_of_chain T h34.symm h23.symm h12.symm h01.symm
        (hne (by decide)) (hne (by decide)) (hne (by decide))
        (hne (by decide)) (hne (by decide)) (hne (by decide))
  · simpa [p5Distance] using
      quotientDistance_eq_three_of_chain T h34.symm h23.symm h12.symm
        (hne (by decide)) (hne (by decide)) (hne (by decide))
  · simpa [p5Distance] using
      quotientDistance_eq_two_of_chain T h34.symm h23.symm (hne (by decide))
  · simpa [p5Distance] using quotientDistance_eq_one_of_adj T h34.symm
  · simpa [p5Distance] using quotientDistance_eq_zero T (e 4)

/-- An actual relabeling with fork adjacency has the literal fork metric. -/
theorem quotientDistance_eq_fork_of_frame
    (T : PosIntTree 18) (e : Fin 5 ≃ EvenComponent T)
    (hadj : ∀ i j,
      (quotientGraph T).Adj (e i) (e j) ↔ forkDistance i j = 1)
    (i j : Fin 5) :
    quotientDistance T (e i) (e j) = forkDistance i j := by
  have hne : ∀ {u v : Fin 5}, u ≠ v → e u ≠ e v := by
    intro u v huv h
    exact huv (e.injective h)
  have h01 := (hadj 0 1).2 (by decide)
  have h02 := (hadj 0 2).2 (by decide)
  have h03 := (hadj 0 3).2 (by decide)
  have h34 := (hadj 3 4).2 (by decide)
  fin_cases i <;> fin_cases j
  · simpa [forkDistance] using quotientDistance_eq_zero T (e 0)
  · simpa [forkDistance] using quotientDistance_eq_one_of_adj T h01
  · simpa [forkDistance] using quotientDistance_eq_one_of_adj T h02
  · simpa [forkDistance] using quotientDistance_eq_one_of_adj T h03
  · simpa [forkDistance] using
      quotientDistance_eq_two_of_chain T h03 h34 (hne (by decide))
  · simpa [forkDistance] using quotientDistance_eq_one_of_adj T h01.symm
  · simpa [forkDistance] using quotientDistance_eq_zero T (e 1)
  · simpa [forkDistance] using
      quotientDistance_eq_two_of_chain T h01.symm h02 (hne (by decide))
  · simpa [forkDistance] using
      quotientDistance_eq_two_of_chain T h01.symm h03 (hne (by decide))
  · simpa [forkDistance] using
      quotientDistance_eq_three_of_chain T h01.symm h03 h34
        (hne (by decide)) (hne (by decide)) (hne (by decide))
  · simpa [forkDistance] using quotientDistance_eq_one_of_adj T h02.symm
  · simpa [forkDistance] using
      quotientDistance_eq_two_of_chain T h02.symm h01 (hne (by decide))
  · simpa [forkDistance] using quotientDistance_eq_zero T (e 2)
  · simpa [forkDistance] using
      quotientDistance_eq_two_of_chain T h02.symm h03 (hne (by decide))
  · simpa [forkDistance] using
      quotientDistance_eq_three_of_chain T h02.symm h03 h34
        (hne (by decide)) (hne (by decide)) (hne (by decide))
  · simpa [forkDistance] using quotientDistance_eq_one_of_adj T h03.symm
  · simpa [forkDistance] using
      quotientDistance_eq_two_of_chain T h03.symm h01 (hne (by decide))
  · simpa [forkDistance] using
      quotientDistance_eq_two_of_chain T h03.symm h02 (hne (by decide))
  · simpa [forkDistance] using quotientDistance_eq_zero T (e 3)
  · simpa [forkDistance] using quotientDistance_eq_one_of_adj T h34
  · simpa [forkDistance] using
      quotientDistance_eq_two_of_chain T h34.symm h03.symm (hne (by decide))
  · simpa [forkDistance] using
      quotientDistance_eq_three_of_chain T h34.symm h03.symm h01
        (hne (by decide)) (hne (by decide)) (hne (by decide))
  · simpa [forkDistance] using
      quotientDistance_eq_three_of_chain T h34.symm h03.symm h02
        (hne (by decide)) (hne (by decide)) (hne (by decide))
  · simpa [forkDistance] using quotientDistance_eq_one_of_adj T h34.symm
  · simpa [forkDistance] using quotientDistance_eq_zero T (e 4)

/-- An actual relabeling with star adjacency has the literal star metric. -/
theorem quotientDistance_eq_star_of_frame
    (T : PosIntTree 18) (e : Fin 5 ≃ EvenComponent T)
    (hadj : ∀ i j,
      (quotientGraph T).Adj (e i) (e j) ↔ starDistance i j = 1)
    (i j : Fin 5) :
    quotientDistance T (e i) (e j) = starDistance i j := by
  have hne : ∀ {u v : Fin 5}, u ≠ v → e u ≠ e v := by
    intro u v huv h
    exact huv (e.injective h)
  have h01 := (hadj 0 1).2 (by decide)
  have h02 := (hadj 0 2).2 (by decide)
  have h03 := (hadj 0 3).2 (by decide)
  have h04 := (hadj 0 4).2 (by decide)
  fin_cases i <;> fin_cases j
  · simpa [starDistance] using quotientDistance_eq_zero T (e 0)
  · simpa [starDistance] using quotientDistance_eq_one_of_adj T h01
  · simpa [starDistance] using quotientDistance_eq_one_of_adj T h02
  · simpa [starDistance] using quotientDistance_eq_one_of_adj T h03
  · simpa [starDistance] using quotientDistance_eq_one_of_adj T h04
  · simpa [starDistance] using quotientDistance_eq_one_of_adj T h01.symm
  · simpa [starDistance] using quotientDistance_eq_zero T (e 1)
  · simpa [starDistance] using
      quotientDistance_eq_two_of_chain T h01.symm h02 (hne (by decide))
  · simpa [starDistance] using
      quotientDistance_eq_two_of_chain T h01.symm h03 (hne (by decide))
  · simpa [starDistance] using
      quotientDistance_eq_two_of_chain T h01.symm h04 (hne (by decide))
  · simpa [starDistance] using quotientDistance_eq_one_of_adj T h02.symm
  · simpa [starDistance] using
      quotientDistance_eq_two_of_chain T h02.symm h01 (hne (by decide))
  · simpa [starDistance] using quotientDistance_eq_zero T (e 2)
  · simpa [starDistance] using
      quotientDistance_eq_two_of_chain T h02.symm h03 (hne (by decide))
  · simpa [starDistance] using
      quotientDistance_eq_two_of_chain T h02.symm h04 (hne (by decide))
  · simpa [starDistance] using quotientDistance_eq_one_of_adj T h03.symm
  · simpa [starDistance] using
      quotientDistance_eq_two_of_chain T h03.symm h01 (hne (by decide))
  · simpa [starDistance] using
      quotientDistance_eq_two_of_chain T h03.symm h02 (hne (by decide))
  · simpa [starDistance] using quotientDistance_eq_zero T (e 3)
  · simpa [starDistance] using
      quotientDistance_eq_two_of_chain T h03.symm h04 (hne (by decide))
  · simpa [starDistance] using quotientDistance_eq_one_of_adj T h04.symm
  · simpa [starDistance] using
      quotientDistance_eq_two_of_chain T h04.symm h01 (hne (by decide))
  · simpa [starDistance] using
      quotientDistance_eq_two_of_chain T h04.symm h02 (hne (by decide))
  · simpa [starDistance] using
      quotientDistance_eq_two_of_chain T h04.symm h03 (hne (by decide))
  · simpa [starDistance] using quotientDistance_eq_zero T (e 4)

noncomputable def evenPairAlternating (T : PosIntTree 18) : ℤ :=
  ∑ p : EvenVertexPair T, weightParitySign (T.pairDist p.1 / 2)

noncomputable def oddPairAlternating (T : PosIntTree 18) : ℤ :=
  ∑ p : OddVertexPair T, weightParitySign (T.pairDist p.1 / 2)

theorem leech_evenPairAlternating (T : PosIntTree 18) (hL : IsLeech T) :
    evenPairAlternating T = 0 := by
  unfold evenPairAlternating
  calc
    _ = ∑ k : {k : ℕ // k ∈ Finset.Icc 1 76},
        weightParitySign k.1 := by
          apply Fintype.sum_equiv
            (LeechTrees.OddQuotient.IsLeech.evenHalfRankEquiv hL)
          intro p
          rw [LeechTrees.OddQuotient.IsLeech.evenHalfRankEquiv_val]
    _ = 0 := by
      rw [← Finset.sum_subtype (Finset.Icc 1 76) (fun _ => Iff.rfl)
        weightParitySign]
      norm_num [weightParitySign, Finset.sum_Icc_succ_top]

theorem leech_oddPairAlternating (T : PosIntTree 18) (hL : IsLeech T) :
    oddPairAlternating T = 1 := by
  unfold oddPairAlternating
  calc
    _ = ∑ k : Fin 77, weightParitySign k.1 := by
          apply Fintype.sum_equiv
            (LeechTrees.OddQuotient.IsLeech.oddHalfRankEquiv hL)
          intro p
          rw [LeechTrees.OddQuotient.IsLeech.oddHalfRankEquiv_val]
    _ = 1 := by
      norm_num [weightParitySign, Fin.sum_univ_succ]

private theorem sum_product_eq_diagonal_add_ordered
    {α : Type*} [Fintype α] [LinearOrder α]
    (f : α → α → ℤ) (hsym : ∀ a b, f a b = f b a) :
    (∑ a, ∑ b, f a b) =
      (∑ a, f a a) +
        2 * ∑ p : {z : α × α // z.1 < z.2}, f p.1.1 p.1.2 := by
  classical
  rw [← Fintype.sum_prod_type']
  let diag : Finset (α × α) := Finset.univ.filter fun z => z.1 = z.2
  let lower : Finset (α × α) := Finset.univ.filter fun z => z.1 < z.2
  let upper : Finset (α × α) := Finset.univ.filter fun z => z.2 < z.1
  have hcover : (Finset.univ : Finset (α × α)) = diag ∪ lower ∪ upper := by
    ext z
    simp only [diag, lower, upper, Finset.mem_univ, Finset.mem_union,
      Finset.mem_filter, true_and]
    constructor
    · intro _
      rcases lt_trichotomy z.1 z.2 with h | h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · intro _
      trivial
  have hdisj₁ : Disjoint diag lower := by
    rw [Finset.disjoint_left]
    intro z hz hzl
    simp only [diag, lower, Finset.mem_filter, Finset.mem_univ,
      true_and] at hz hzl
    exact (ne_of_lt hzl) hz
  have hdisj₂ : Disjoint (diag ∪ lower) upper := by
    rw [Finset.disjoint_left]
    intro z hz hzu
    rcases Finset.mem_union.mp hz with hz | hz
    · simp only [diag, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      simp only [upper, Finset.mem_filter, Finset.mem_univ, true_and] at hzu
      exact (ne_of_lt hzu) hz.symm
    · simp only [lower, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      simp only [upper, Finset.mem_filter, Finset.mem_univ, true_and] at hzu
      exact (not_lt_of_ge hz.le) hzu
  have hdiag : (∑ z ∈ diag, f z.1 z.2) = ∑ a, f a a := by
    apply Finset.sum_bij (fun z _ => z.1)
    · simp
    · intro z₁ hz₁ z₂ hz₂ h
      simp only [diag, Finset.mem_filter, Finset.mem_univ, true_and] at hz₁ hz₂
      apply Prod.ext
      · exact h
      · simpa [hz₁, hz₂] using h
    · intro a ha
      exact ⟨(a, a), by simp [diag], rfl⟩
    · intro z hz
      simp only [diag, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      simp [hz]
  have hlower : (∑ z ∈ lower, f z.1 z.2) =
      ∑ p : {z : α × α // z.1 < z.2}, f p.1.1 p.1.2 := by
    exact Finset.sum_subtype lower (fun z => by simp [lower])
      (fun z => f z.1 z.2)
  have hupper : (∑ z ∈ upper, f z.1 z.2) =
      ∑ z ∈ lower, f z.1 z.2 := by
    apply Finset.sum_bij (fun z _ => (z.2, z.1))
    · simp [lower, upper]
    · intro a ha b hb h
      exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    · intro z hz
      exact ⟨(z.2, z.1), by simpa [lower, upper] using hz, rfl⟩
    · intro z hz
      exact hsym _ _
  rw [hcover, Finset.sum_union hdisj₂, Finset.sum_union hdisj₁,
    hdiag, hupper, hlower]
  ring

private theorem sum_product_eq_diagonal_add_componentPairs
    (T : PosIntTree 18) (f : EvenComponent T → EvenComponent T → ℤ)
    (hsym : ∀ C D, f C D = f D C) :
    (∑ C, ∑ D, f C D) =
      (∑ C, f C C) +
        2 * ∑ q : QuotientComponentPair T, f q.left q.right := by
  classical
  letI : LinearOrder (EvenComponent T) :=
    LinearOrder.lift' (componentRep T) (componentRep_injective T)
  simpa only [QuotientComponentPair.left, QuotientComponentPair.right] using
    (sum_product_eq_diagonal_add_ordered f hsym)

private theorem sum_square_eq_diagonal_add_unordered
    {α : Type*} [Fintype α] [LinearOrder α] (s : α → ℤ) :
    (∑ a, s a) ^ 2 =
      (∑ a, s a ^ 2) +
        2 * ∑ p : {z : α × α // z.1 < z.2}, s p.1.1 * s p.1.2 := by
  classical
  calc
    (∑ a, s a) ^ 2 = ∑ a, ∑ b, s a * s b := by
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
    _ = _ := by
      simpa only [pow_two] using
        (sum_product_eq_diagonal_add_ordered
          (fun a b => s a * s b) (fun a b => mul_comm _ _))

/-- Squaring one actual component imbalance gives its diagonal order plus
twice its internal alternating half-rank sum. -/
theorem componentDelta_square
    (T : PosIntTree 18) (C : EvenComponent T) :
    componentDelta T C ^ 2 = componentOrder T C +
      2 * ∑ p : InternalPair T C,
        weightParitySign (internalRank T p) := by
  classical
  unfold componentDelta componentOrder internalRank
  rw [sum_square_eq_diagonal_add_unordered]
  apply congrArg₂ (· + ·)
  · simp [weightParitySign]
  · apply congrArg (2 * ·)
    apply Finset.sum_congr rfl
    intro p hp
    rw [← floorPathMetric_eq_rho T (componentReference T C) p.1.1,
      ← floorPathMetric_eq_rho T (componentReference T C) p.1.2,
      ← floorPathMetric_eq_rho T p.1.1 p.1.2]
    rw [floorPathSign_factor T (componentReference T C).1 p.1.1 p.1.2]
    have hs : weightParitySign
        (floorPathMetric T (componentReference T C).1 p.1.1) *
        weightParitySign
          (floorPathMetric T (componentReference T C).1 p.1.1) = 1 := by
      unfold weightParitySign
      split <;> norm_num
    rw [← mul_assoc, hs, one_mul]

/-- Cross-component endpoint factorisation through the actual gauge.  This
is the graph/model adapter missing from a bare scalar `K_Q` formula. -/
theorem crossBlock_alternating_factor
    (T : PosIntTree 18) (R : EvenComponent T)
    (q : QuotientComponentPair T) :
    (∑ z : ComponentVertex T q.left × ComponentVertex T q.right,
      weightParitySign (crossRank T q z)) =
      weightParitySign (quotientDistance T q.left q.right / 2) *
        componentCoordinate T R q.left * componentCoordinate T R q.right := by
  classical
  have hroute : ∀ z : ComponentVertex T q.left × ComponentVertex T q.right,
      floorPathMetric T z.1.1 z.2.1 =
        routeCost T (canonicalRouteWalk T q) z.1 z.2 := by
    intro z
    exact floorPathMetric_eq_routeCost T _ (canonicalRouteWalk_isPath T q) _ _
  have hlength : quotientDistance T q.left q.right =
      (canonicalRouteWalk T q).length := by
    unfold quotientDistance
    rw [canonicalRouteWalk_eq_quotientPath]
  have hcross : ∀ z : ComponentVertex T q.left × ComponentVertex T q.right,
      crossRank T q z = quotientDistance T q.left q.right / 2 +
        routeCost T (canonicalRouteWalk T q) z.1 z.2 := by
    intro z
    rw [hlength]
    have htarget := rho_comm T
      (routeTerminal T (canonicalRouteData T q).tail
        (orientedBridgeOfAdj T (canonicalRouteData T q).head).targetPort) z.2
    simp only [crossRank, canonicalRouteShift, canonicalSourcePort,
      canonicalTargetPort, canonicalRouteWalk, routeShift, routeCost,
      routeInteriorCost_cons, routeTerminal_cons]
    rw [htarget]
    omega
  have hrank : ∀ z : ComponentVertex T q.left × ComponentVertex T q.right,
      weightParitySign (crossRank T q z) =
        weightParitySign (quotientDistance T q.left q.right / 2) *
          weightParitySign (floorPathMetric T z.1.1 z.2.1) := by
    intro z
    rw [hcross z, weightParitySign_add, ← hroute z]
  have hterm (u : ComponentVertex T q.left)
      (v : ComponentVertex T q.right) :
      weightParitySign (floorPathMetric T u.1 v.1) =
        weightParitySign (floorPathMetric T
          (componentReference T q.left).1 u.1) *
        weightParitySign (floorPathMetric T
          (componentReference T q.left).1
          (componentReference T q.right).1) *
        weightParitySign (floorPathMetric T
          (componentReference T q.right).1 v.1) := by
    have hfirst := floorPathSign_factor T
      (componentReference T q.left).1 u.1 v.1
    have hsecond := floorPathSign_factor T
      (componentReference T q.left).1
      (componentReference T q.right).1 v.1
    have hs : weightParitySign (floorPathMetric T
        (componentReference T q.left).1 u.1) *
        weightParitySign (floorPathMetric T
          (componentReference T q.left).1 u.1) = 1 := by
      unfold weightParitySign
      split <;> norm_num
    calc
      _ = 1 * weightParitySign (floorPathMetric T u.1 v.1) := by ring
      _ = (weightParitySign (floorPathMetric T
          (componentReference T q.left).1 u.1) *
          weightParitySign (floorPathMetric T
            (componentReference T q.left).1 u.1)) *
          weightParitySign (floorPathMetric T u.1 v.1) := by rw [hs]
      _ = weightParitySign (floorPathMetric T
          (componentReference T q.left).1 u.1) *
          weightParitySign (floorPathMetric T
            (componentReference T q.left).1 v.1) := by rw [hfirst]; ring
      _ = _ := by rw [hsecond]; ring
  have hleft : (∑ u : ComponentVertex T q.left,
      weightParitySign (floorPathMetric T
        (componentReference T q.left).1 u.1)) = componentDelta T q.left := by
    unfold componentDelta
    apply Finset.sum_congr rfl
    intro u hu
    rw [floorPathMetric_eq_rho T (componentReference T q.left) u]
  have hright : (∑ v : ComponentVertex T q.right,
      weightParitySign (floorPathMetric T
        (componentReference T q.right).1 v.1)) = componentDelta T q.right := by
    unfold componentDelta
    apply Finset.sum_congr rfl
    intro v hv
    rw [floorPathMetric_eq_rho T (componentReference T q.right) v]
  have hsum : (∑ z : ComponentVertex T q.left × ComponentVertex T q.right,
      weightParitySign (floorPathMetric T z.1.1 z.2.1)) =
      componentCoordinate T R q.left * componentCoordinate T R q.right := by
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ u : ComponentVertex T q.left,
          ∑ v : ComponentVertex T q.right,
            weightParitySign (floorPathMetric T
              (componentReference T q.left).1 u.1) *
            weightParitySign (floorPathMetric T
              (componentReference T q.left).1
              (componentReference T q.right).1) *
            weightParitySign (floorPathMetric T
              (componentReference T q.right).1 v.1) := by
          apply Finset.sum_congr rfl
          intro u hu
          apply Finset.sum_congr rfl
          intro v hv
          exact hterm u v
      _ = ∑ u : ComponentVertex T q.left,
          (weightParitySign (floorPathMetric T
            (componentReference T q.left).1 u.1) *
            weightParitySign (floorPathMetric T
              (componentReference T q.left).1
              (componentReference T q.right).1)) *
            (∑ v : ComponentVertex T q.right,
              weightParitySign (floorPathMetric T
                (componentReference T q.right).1 v.1)) := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [Finset.mul_sum]
      _ = (∑ u : ComponentVertex T q.left,
          weightParitySign (floorPathMetric T
            (componentReference T q.left).1 u.1)) *
          weightParitySign (floorPathMetric T
            (componentReference T q.left).1
            (componentReference T q.right).1) *
          (∑ v : ComponentVertex T q.right,
            weightParitySign (floorPathMetric T
              (componentReference T q.right).1 v.1)) := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
      _ = _ := by
          rw [hleft, hright, component_reference_phase T R q.left q.right]
          unfold componentCoordinate
          ring
  simp_rw [hrank]
  rw [← Finset.mul_sum, hsum]
  ring

theorem componentCoordinate_square
    (T : PosIntTree 18) (R C : EvenComponent T) :
    componentCoordinate T R C ^ 2 = componentDelta T C ^ 2 := by
  rcases componentSigma_sign T R C with h | h <;>
    simp [componentCoordinate, h]

/-- The existing exact odd/even pair-block equivalences also preserve the
alternating half-rank weight, not just polynomial coefficients. -/
theorem evenPairAlternating_eq_blocks (T : PosIntTree 18) :
    evenPairAlternating T =
      (∑ z : WithinIndex T, weightParitySign (internalRank T z.2)) +
        ∑ z : EvenCrossIndex T,
          weightParitySign (crossRank T z.1.1 z.2) := by
  unfold evenPairAlternating
  calc
    _ = ∑ z : WithinIndex T ⊕ EvenCrossIndex T,
        weightParitySign (evenBlockRank T z) := by
          apply Fintype.sum_equiv (evenPairBlockEquiv T)
          intro p
          rw [evenPairBlockEquiv_rank]
    _ = _ := by
      rw [Fintype.sum_sum_type]
      rfl

theorem oddPairAlternating_eq_blocks (T : PosIntTree 18) :
    oddPairAlternating T =
      ∑ z : OddCrossIndex T,
        weightParitySign (crossRank T z.1.1 z.2) := by
  unfold oddPairAlternating
  apply Fintype.sum_equiv (oddPairBlockEquiv T)
  intro p
  simpa only [oddBlockRank] using
    congrArg weightParitySign (oddPairBlockEquiv_rank T p).symm

theorem iPow_of_even_quotientDistance
    (T : PosIntTree 18) (q : EvenQuotientComponentPair T) :
    iPowReal (quotientDistance T q.1.left q.1.right) =
        weightParitySign (quotientDistance T q.1.left q.1.right / 2) ∧
      iPowImag (quotientDistance T q.1.left q.1.right) = 0 := by
  have hp : quotientDistance T q.1.left q.1.right % 2 = 0 := by
    simpa [quotientDistance, quotientPairParity,
      canonicalRouteWalk_eq_quotientPath] using q.2
  unfold iPowReal iPowImag weightParitySign
  have hmod := Nat.mod_add_div
    (quotientDistance T q.1.left q.1.right) 4
  have hlt : quotientDistance T q.1.left q.1.right % 4 < 4 :=
    Nat.mod_lt _ (by omega)
  interval_cases h : quotientDistance T q.1.left q.1.right % 4 <;>
    norm_num [h, hp] at hmod ⊢ <;> omega

theorem iPow_of_odd_quotientDistance
    (T : PosIntTree 18) (q : OddQuotientComponentPair T) :
    iPowReal (quotientDistance T q.1.left q.1.right) = 0 ∧
      iPowImag (quotientDistance T q.1.left q.1.right) =
        weightParitySign (quotientDistance T q.1.left q.1.right / 2) := by
  have hp : quotientDistance T q.1.left q.1.right % 2 = 1 := by
    simpa [quotientDistance, quotientPairParity,
      canonicalRouteWalk_eq_quotientPath] using q.2
  unfold iPowReal iPowImag weightParitySign
  have hmod := Nat.mod_add_div
    (quotientDistance T q.1.left q.1.right) 4
  have hlt : quotientDistance T q.1.left q.1.right % 4 < 4 :=
    Nat.mod_lt _ (by omega)
  interval_cases h : quotientDistance T q.1.left q.1.right % 4 <;>
    norm_num [h, hp] at hmod ⊢ <;> omega

/-- Ordered matrix sums split into diagonal components and the exact
unordered `QuotientComponentPair` index. -/
theorem gaussian_componentPair_expansion
    (T : PosIntTree 18) (x : EvenComponent T → ℤ) :
    gaussianReal (quotientDistance T) x =
        (∑ C, x C ^ 2) +
          2 * ∑ q : QuotientComponentPair T,
            x q.left * x q.right *
              iPowReal (quotientDistance T q.left q.right) ∧
      gaussianImag (quotientDistance T) x =
          2 * ∑ q : QuotientComponentPair T,
            x q.left * x q.right *
              iPowImag (quotientDistance T q.left q.right) := by
  classical
  have hsym : ∀ C D, quotientDistance T C D = quotientDistance T D C := by
    intro C D
    unfold quotientDistance
    let p : (quotientGraph T).Path D C :=
      ⟨(quotientPath T C D).1.reverse, (quotientPath T C D).2.reverse⟩
    have hp : p = quotientPath T D C := quotientPath_unique T p
    rw [← hp]
    simp [p]
  have hself : ∀ C, quotientDistance T C C = 0 := by
    intro C
    unfold quotientDistance
    let p : (quotientGraph T).Path C C := ⟨.nil, by simp⟩
    have hp : p = quotientPath T C C := quotientPath_unique T p
    rw [← hp]
    rfl
  unfold gaussianReal gaussianImag
  constructor
  · have h := sum_product_eq_diagonal_add_componentPairs T
        (fun C D => x C * x D * iPowReal (quotientDistance T C D))
        (fun C D => by
          dsimp
          rw [hsym C D]
          ring)
    simpa [hself, pow_two, iPowReal] using h
  · have h := sum_product_eq_diagonal_add_componentPairs T
        (fun C D => x C * x D * iPowImag (quotientDistance T C D))
        (fun C D => by
          dsimp
          rw [hsym C D]
          ring)
    simpa [hself, iPowImag] using h

/-- Full actual quotient expansion.  It is proved by the exact
within/cross pair partition, `componentDelta_square`, and
`crossBlock_alternating_factor`; no target Gaussian value is assumed. -/
theorem actual_quotient_gaussian_expansion
    (T : PosIntTree 18) (R : EvenComponent T) :
    gaussianReal (quotientDistance T) (componentCoordinate T R) =
      18 + 2 * evenPairAlternating T ∧
    gaussianImag (quotientDistance T) (componentCoordinate T R) =
      2 * oddPairAlternating T := by
  classical
  have hmatrix := gaussian_componentPair_expansion T
    (componentCoordinate T R)
  have hdiag : (∑ C, componentCoordinate T R C ^ 2) =
      18 + 2 * ∑ z : WithinIndex T,
        weightParitySign (internalRank T z.2) := by
    simp_rw [componentCoordinate_square, componentDelta_square]
    rw [Finset.sum_add_distrib, Fintype.sum_sigma]
    have horder : (∑ C, (componentOrder T C : ℤ)) = 18 := by
      exact_mod_cast componentOrder_sum T
    rw [horder]
    rw [Finset.mul_sum]
  have hevenCross :
      (∑ q : EvenQuotientComponentPair T,
        componentCoordinate T R q.1.left *
          componentCoordinate T R q.1.right *
            iPowReal (quotientDistance T q.1.left q.1.right)) =
      ∑ z : EvenCrossIndex T,
        weightParitySign (crossRank T z.1.1 z.2) := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro q hq
    rw [(iPow_of_even_quotientDistance T q).1]
    rw [crossBlock_alternating_factor T R q.1]
    ring
  have hoddCross :
      (∑ q : OddQuotientComponentPair T,
        componentCoordinate T R q.1.left *
          componentCoordinate T R q.1.right *
            iPowImag (quotientDistance T q.1.left q.1.right)) =
      ∑ z : OddCrossIndex T,
        weightParitySign (crossRank T z.1.1 z.2) := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro q hq
    rw [(iPow_of_odd_quotientDistance T q).2]
    rw [crossBlock_alternating_factor T R q.1]
    ring
  have hrealSplit :
      (∑ q : QuotientComponentPair T,
        componentCoordinate T R q.left * componentCoordinate T R q.right *
          iPowReal (quotientDistance T q.left q.right)) =
      ∑ q : EvenQuotientComponentPair T,
        componentCoordinate T R q.1.left * componentCoordinate T R q.1.right *
          iPowReal (quotientDistance T q.1.left q.1.right) := by
    rw [← Finset.sum_subtype
      (Finset.univ.filter fun q : QuotientComponentPair T =>
        quotientPairParity T q = 0) (fun _ => by simp)
      (fun q => componentCoordinate T R q.left * componentCoordinate T R q.right *
        iPowReal (quotientDistance T q.left q.right))]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases he : quotientPairParity T q = 0
    · simp [he]
    · have ho : quotientPairParity T q = 1 := by
        have := quotientPairParity_lt_two T q
        omega
      have hz := (iPow_of_odd_quotientDistance T ⟨q, ho⟩).1
      simp [he, hz]
  have himagSplit :
      (∑ q : QuotientComponentPair T,
        componentCoordinate T R q.left * componentCoordinate T R q.right *
          iPowImag (quotientDistance T q.left q.right)) =
      ∑ q : OddQuotientComponentPair T,
        componentCoordinate T R q.1.left * componentCoordinate T R q.1.right *
          iPowImag (quotientDistance T q.1.left q.1.right) := by
    rw [← Finset.sum_subtype
      (Finset.univ.filter fun q : QuotientComponentPair T =>
        quotientPairParity T q = 1) (fun _ => by simp)
      (fun q => componentCoordinate T R q.left * componentCoordinate T R q.right *
        iPowImag (quotientDistance T q.left q.right))]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases ho : quotientPairParity T q = 1
    · simp [ho]
    · have he : quotientPairParity T q = 0 := by
        have := quotientPairParity_lt_two T q
        omega
      have hz := (iPow_of_even_quotientDistance T ⟨q, he⟩).2
      simp [ho, hz]
  rw [hmatrix.1, hmatrix.2, hdiag, hrealSplit, himagSplit,
    hevenCross, hoddCross, evenPairAlternating_eq_blocks,
    oddPairAlternating_eq_blocks]
  constructor <;> ring

/-- Actual-tree G022 identity before choosing a five-component labelling. -/
theorem actual_fourOdd_gaussian_identity
    (T : PosIntTree 18) (hL : IsLeech T)
    (R : EvenComponent T) :
    gaussianReal (quotientDistance T) (componentCoordinate T R) = 18 ∧
      gaussianImag (quotientDistance T) (componentCoordinate T R) = 2 := by
  have h := actual_quotient_gaussian_expansion T R
  rw [leech_evenPairAlternating T hL, leech_oddPairAlternating T hL] at h
  norm_num at h ⊢
  exact h

/-! ## Reindexed, queryable G022 endpoint -/

/-- The audited domain transported along any exact relabeling of the five
actual even components.  This lets a shape frame and its domain constraints
use the very same equivalence. -/
noncomputable def actualFourOddDomainAt
    (T : PosIntTree 18) (hL : IsLeech T)
    (e : Fin 5 ≃ EvenComponent T) : FourOddGaussianDomain :=
  let R := e 0
  { order := fun j => componentOrder T (e j)
    imbalance := fun j => componentCoordinate T R (e j)
    color := fun j => sevenColor T hL (e j)
    eachValid := by
      intro j
      exact componentDatum_valid T R (e j)
    colorSeven := by
      have h := (sevenColor_budgets T hL).1
      exact (Equiv.sum_comp e (fun C =>
        if sevenColor T hL C then componentOrder T C else 0)).trans h
    colorEleven := by
      have h := (sevenColor_budgets T hL).2
      exact (Equiv.sum_comp e (fun C =>
        if sevenColor T hL C then 0 else componentOrder T C)).trans h }

/-- The original canonical presentation is the domain at the component
equivalence obtained directly from the four odd physical edges. -/
noncomputable def actualFourOddDomain
    (T : PosIntTree 18) (hL : IsLeech T)
    (h4 : ExactlyFourOddEdges T) : FourOddGaussianDomain :=
  actualFourOddDomainAt T hL (fourOddComponentEquiv T h4)

theorem gaussian_equiv
    {V W : Type*} [Fintype V] [Fintype W]
    (e : V ≃ W) (distance : W → W → ℕ) (x : W → ℤ) :
    gaussianReal (fun u v => distance (e u) (e v)) (fun u => x (e u)) =
        gaussianReal distance x ∧
      gaussianImag (fun u v => distance (e u) (e v)) (fun u => x (e u)) =
        gaussianImag distance x := by
  unfold gaussianReal gaussianImag
  constructor
  · apply Fintype.sum_equiv e
    intro u
    apply Fintype.sum_equiv e
    intro v
    rfl
  · apply Fintype.sum_equiv e
    intro u
    apply Fintype.sum_equiv e
    intro v
    rfl

/-! ### Actual shape-specific K-form certificates -/

/-- Component coordinates in the exact shape relabeling, gauged at the
vertex in role zero. -/
noncomputable def actualFrameCoordinate
    (T : PosIntTree 18) (e : Fin 5 ≃ EvenComponent T) : Fin 5 → ℤ :=
  fun j => componentCoordinate T (e 0) (e j)

/-- The four noncentral coordinates of an actual star frame. -/
noncomputable def actualStarLeafCoordinate
    (T : PosIntTree 18) (e : Fin 5 ≃ EvenComponent T) : Fin 4 → ℤ :=
  fun j => actualFrameCoordinate T e j.succ

/-- Fully derived P5 alternative: it includes the actual quotient-distance
transport, the literal symbolic K-form expansion, and its target values. -/
def ActualP5KExpansion (T : PosIntTree 18) (hL : IsLeech T) : Prop :=
  ∃ e : Fin 5 ≃ EvenComponent T,
    (actualFourOddDomainAt T hL e).order =
      (fun j => componentOrder T (e j)) ∧
    (actualFourOddDomainAt T hL e).imbalance =
      actualFrameCoordinate T e ∧
    (actualFourOddDomainAt T hL e).color =
      (fun j => sevenColor T hL (e j)) ∧
    (∀ i j, quotientDistance T (e i) (e j) = p5Distance i j) ∧
    gaussianReal p5Distance (actualFrameCoordinate T e) =
      p5Real (actualFrameCoordinate T e) ∧
    gaussianImag p5Distance (actualFrameCoordinate T e) =
      2 * p5ImagHalf (actualFrameCoordinate T e) ∧
    p5Real (actualFrameCoordinate T e) = 18 ∧
    p5ImagHalf (actualFrameCoordinate T e) = 1

/-- Fully derived fork alternative. -/
def ActualForkKExpansion (T : PosIntTree 18) (hL : IsLeech T) : Prop :=
  ∃ e : Fin 5 ≃ EvenComponent T,
    (actualFourOddDomainAt T hL e).order =
      (fun j => componentOrder T (e j)) ∧
    (actualFourOddDomainAt T hL e).imbalance =
      actualFrameCoordinate T e ∧
    (actualFourOddDomainAt T hL e).color =
      (fun j => sevenColor T hL (e j)) ∧
    (∀ i j, quotientDistance T (e i) (e j) = forkDistance i j) ∧
    gaussianReal forkDistance (actualFrameCoordinate T e) =
      forkReal (actualFrameCoordinate T e) ∧
    gaussianImag forkDistance (actualFrameCoordinate T e) =
      2 * forkImagHalf (actualFrameCoordinate T e) ∧
    forkReal (actualFrameCoordinate T e) = 18 ∧
    forkImagHalf (actualFrameCoordinate T e) = 1

/-- Fully derived star alternative.  The four leaf variables come from the
same actual relabeling as the central coordinate. -/
def ActualStarKExpansion (T : PosIntTree 18) (hL : IsLeech T) : Prop :=
  ∃ e : Fin 5 ≃ EvenComponent T,
    (actualFourOddDomainAt T hL e).order =
      (fun j => componentOrder T (e j)) ∧
    (actualFourOddDomainAt T hL e).imbalance =
      actualFrameCoordinate T e ∧
    (actualFourOddDomainAt T hL e).color =
      (fun j => sevenColor T hL (e j)) ∧
    (∀ i j, quotientDistance T (e i) (e j) = starDistance i j) ∧
    gaussianReal starDistance (actualFrameCoordinate T e) =
      starReal (actualFrameCoordinate T e 0)
        (actualStarLeafCoordinate T e) ∧
    gaussianImag starDistance (actualFrameCoordinate T e) =
      2 * starImagHalf (actualFrameCoordinate T e 0)
        (actualStarLeafCoordinate T e) ∧
    starReal (actualFrameCoordinate T e 0)
      (actualStarLeafCoordinate T e) = 18 ∧
    starImagHalf (actualFrameCoordinate T e 0)
      (actualStarLeafCoordinate T e) = 1

private theorem actualFrame_gaussian_target
    (T : PosIntTree 18) (hL : IsLeech T)
    (e : Fin 5 ≃ EvenComponent T) (d : Fin 5 → Fin 5 → ℕ)
    (hd : ∀ i j, quotientDistance T (e i) (e j) = d i j) :
    gaussianReal d (actualFrameCoordinate T e) = 18 ∧
      gaussianImag d (actualFrameCoordinate T e) = 2 := by
  have hactual := actual_fourOdd_gaussian_identity T hL (e 0)
  have hreindex := gaussian_equiv e (quotientDistance T)
    (componentCoordinate T (e 0))
  have hreal :
      gaussianReal
          (fun i j => quotientDistance T (e i) (e j))
          (actualFrameCoordinate T e) = 18 := by
    exact (by
      simpa only [actualFrameCoordinate] using hreindex.1.trans hactual.1)
  have himag :
      gaussianImag
          (fun i j => quotientDistance T (e i) (e j))
          (actualFrameCoordinate T e) = 2 := by
    exact (by
      simpa only [actualFrameCoordinate] using hreindex.2.trans hactual.2)
  have hdfun :
      (fun i j => quotientDistance T (e i) (e j)) = d := by
    funext i j
    exact hd i j
  rw [hdfun] at hreal himag
  exact ⟨hreal, himag⟩

private theorem actualFrameCoordinate_starVector
    (T : PosIntTree 18) (e : Fin 5 ≃ EvenComponent T) :
    (![actualFrameCoordinate T e 0,
        actualStarLeafCoordinate T e 0,
        actualStarLeafCoordinate T e 1,
        actualStarLeafCoordinate T e 2,
        actualStarLeafCoordinate T e 3] : Fin 5 → ℤ) =
      actualFrameCoordinate T e := by
  funext j
  fin_cases j <;> rfl

/-- Acceptance endpoint for the repaired G022 shape layer.  Starting only
from the actual Leech tree and its four physical odd edges, it derives an
actual quotient relabeling and one of the three literal audited K-form
expansions.  No distance matrix or expansion is supplied by the caller. -/
theorem G022_actual_shape_specific_K_expansion
    (T : PosIntTree 18) (hL : IsLeech T)
    (h4 : ExactlyFourOddEdges T) :
    ActualP5KExpansion T hL ∨ ActualForkKExpansion T hL ∨
      ActualStarKExpansion T hL := by
  classical
  obtain ⟨frame⟩ := exists_actualFiveTreeFrame T h4
  cases frame with
  | p5 e hadj =>
      left
      have hd := quotientDistance_eq_p5_of_frame T e hadj
      have ht := actualFrame_gaussian_target T hL e p5Distance hd
      have he := p5_KForm_expansion (actualFrameCoordinate T e)
      refine ⟨e, rfl, rfl, rfl, hd, he.1, he.2, ?_, ?_⟩
      · exact he.1.symm.trans ht.1
      · have htwo := he.2.symm.trans ht.2
        omega
  | fork e hadj =>
      right
      left
      have hd := quotientDistance_eq_fork_of_frame T e hadj
      have ht := actualFrame_gaussian_target T hL e forkDistance hd
      have he := fork_KForm_expansion (actualFrameCoordinate T e)
      refine ⟨e, rfl, rfl, rfl, hd, he.1, he.2, ?_, ?_⟩
      · exact he.1.symm.trans ht.1
      · have htwo := he.2.symm.trans ht.2
        omega
  | star e hadj =>
      right
      right
      have hd := quotientDistance_eq_star_of_frame T e hadj
      have ht := actualFrame_gaussian_target T hL e starDistance hd
      have he := star_KForm_expansion
        (actualFrameCoordinate T e 0) (actualStarLeafCoordinate T e)
      dsimp only at he
      rw [actualFrameCoordinate_starVector T e] at he
      refine ⟨e, rfl, rfl, rfl, hd, he.1, he.2, ?_, ?_⟩
      · exact he.1.symm.trans ht.1
      · have htwo := he.2.symm.trans ht.2
        omega

/-- Final noncircular G022 endpoint: an actual four-odd order-18 Leech tree
would produce five reindexed quotient variables in the exact audited domain,
one of the three symbolic five-tree shapes, and the literal matrix identity
`xᵀK_Qx=(18,2)`. -/
theorem G022_actual_fourOdd_quotient_identity_domain_shape
    (T : PosIntTree 18) (hL : IsLeech T)
    (h4 : ExactlyFourOddEdges T) :
    let e := fourOddComponentEquiv T h4
    let R := e 0
    let x : Fin 5 → ℤ := fun j => componentCoordinate T R (e j)
    let d : Fin 5 → Fin 5 → ℕ := fun u v => quotientDistance T (e u) (e v)
    (quotientGraph T).IsTree ∧
      Fintype.card (EvenComponent T) = 5 ∧
      (∀ {C D}, (quotientGraph T).Adj C D →
        sevenColor T hL C ≠ sevenColor T hL D) ∧
      (actualFourOddDomain T hL h4).order =
        (fun j => componentOrder T (e j)) ∧
      (actualFourOddDomain T hL h4).imbalance = x ∧
      gaussianReal d x = 18 ∧ gaussianImag d x = 2 ∧
      (∃ shape, HasFiveTreeShape (quotientGraph T) shape) ∧
      (ActualP5KExpansion T hL ∨ ActualForkKExpansion T hL ∨
        ActualStarKExpansion T hL) := by
  dsimp only
  refine ⟨quotientGraph_isTree T, fourOdd_evenComponent_card T h4,
    ?_, rfl, rfl, ?_, ?_, fourOdd_quotient_shape T h4,
      G022_actual_shape_specific_K_expansion T hL h4⟩
  · intro C D h
    exact sevenColor_adjacent T hL h
  · have h := (actual_fourOdd_gaussian_identity T hL
      ((fourOddComponentEquiv T h4) 0)).1
    exact (gaussian_equiv (fourOddComponentEquiv T h4)
      (quotientDistance T)
      (componentCoordinate T ((fourOddComponentEquiv T h4) 0))).1.trans h
  · have h := (actual_fourOdd_gaussian_identity T hL
      ((fourOddComponentEquiv T h4) 0)).2
    exact (gaussian_equiv (fourOddComponentEquiv T h4)
      (quotientDistance T)
      (componentCoordinate T ((fourOddComponentEquiv T h4) 0))).2.trans h

end LeechTrees.AdditionalBlockLifts
