import LeechTrees.OddQuotient.Components

/-!
# The odd quotient, actual bridge ports, and route distances

This file contracts the connected components of `evenForest T` only at the
level of a new simple graph.  Its edges are the images of the indexed actual
odd physical edges.  Injectivity of that image is proved from the one-edge
cut of the original tree, so the simple quotient loses no bridge
multiplicity.

The last section orients the unique actual bridge underlying each quotient
adjacency.  A recursive route cost then records every actual endpoint port
and, at every intermediate quotient component, the scaled distance from the
previous exit port to the next entry port.  All results are forward
identities for an existing positive integral tree; no realization converse
is stated.
-/

namespace LeechTrees.OddQuotient

open LeechTrees.Foundation

variable {n : ℕ}

/-! ## The indexed odd-edge image -/

/-- The unordered pair of even components joined by an actual odd physical
edge.  Keeping the odd edge as the argument retains its physical index. -/
noncomputable def quotientEdgePair (T : PosIntTree n) (e : OddBridge T) :
    Sym2 (EvenComponent T) :=
  Sym2.map (componentOf T) e.1.1

@[simp] theorem quotientEdgePair_eq (T : PosIntTree n) (e : OddBridge T) :
    quotientEdgePair T e =
      s(componentOf T (T.edgeLeft e.1),
        componentOf T (T.edgeRight e.1)) := by
  rw [quotientEdgePair, T.edge_eq_mk_endpoints e.1,
    Sym2.map_pair_eq]

/-- A mapped odd edge is never a diagonal component pair. -/
theorem quotientEdgePair_not_isDiag (T : PosIntTree n) (e : OddBridge T) :
    ¬(quotientEdgePair T e).IsDiag := by
  rw [quotientEdgePair_eq, Sym2.mk_isDiag_iff]
  exact oddBridge_components_ne T e

/-- The even forest avoids every fixed actual odd edge, hence lies in its
one-edge cut graph. -/
theorem evenForest_le_oddCut (T : PosIntTree n) (e : OddBridge T) :
    evenForest T ≤ T.cutGraph e.1 := by
  classical
  intro u v huv
  rw [PosIntTree.cutGraph, SimpleGraph.deleteEdges_adj]
  have h := (evenForest_adj_iff T).mp huv
  refine ⟨h.1, ?_⟩
  simp only [Set.mem_singleton_iff]
  intro heq
  have hw : T.weightOfPair s(u, v) = T.weight e.1 := by
    rw [heq]
    exact T.weightOfPair_edge e.1
  have heven : Even (T.weight e.1) := by
    rw [← hw]
    exact h.2
  exact (Nat.not_odd_iff_even.mpr heven) e.2

/-- Vertices in one even component remain connected after any fixed odd
physical edge is deleted. -/
theorem oddCut_reachable_of_component_eq
    (T : PosIntTree n) (e : OddBridge T) {u v : Fin n}
    (hcomp : componentOf T u = componentOf T v) :
    (T.cutGraph e.1).Reachable u v :=
  ((componentOf_eq_iff T u v).mp hcomp).mono
    (evenForest_le_oddCut T e)

/-- Two odd physical edges with the same ordered component ends are the same
physical edge. -/
private theorem oddBridge_eq_of_direct_component_ends
    (T : PosIntTree n) (e f : OddBridge T)
    (hleft : componentOf T (T.edgeLeft e.1) =
      componentOf T (T.edgeLeft f.1))
    (hright : componentOf T (T.edgeRight e.1) =
      componentOf T (T.edgeRight f.1)) :
    e = f := by
  have hfLeft : T.LeftCut e.1 (T.edgeLeft f.1) := by
    change (T.cutGraph e.1).Reachable
      (T.edgeLeft f.1) (T.edgeLeft e.1)
    exact (oddCut_reachable_of_component_eq T e hleft).symm
  have hfRight : T.RightCut e.1 (T.edgeRight f.1) := by
    change (T.cutGraph e.1).Reachable
      (T.edgeRight f.1) (T.edgeRight e.1)
    exact (oddCut_reachable_of_component_eq T e hright).symm
  have hemem : e.1.1 ∈
      T.pathEdges (T.edgeLeft f.1) (T.edgeRight f.1) :=
    (T.mem_pathEdges_iff_opposite_cuts e.1 _ _).2
      (Or.inl ⟨hfLeft, hfRight⟩)
  rw [T.pathEdges_edge f.1] at hemem
  exact Subtype.ext (Subtype.ext (Finset.mem_singleton.mp hemem))

/-- The corresponding no-parallel-edge statement with the ends swapped. -/
private theorem oddBridge_eq_of_swapped_component_ends
    (T : PosIntTree n) (e f : OddBridge T)
    (hleft : componentOf T (T.edgeLeft e.1) =
      componentOf T (T.edgeRight f.1))
    (hright : componentOf T (T.edgeRight e.1) =
      componentOf T (T.edgeLeft f.1)) :
    e = f := by
  have hfRight : T.LeftCut e.1 (T.edgeRight f.1) := by
    change (T.cutGraph e.1).Reachable
      (T.edgeRight f.1) (T.edgeLeft e.1)
    exact (oddCut_reachable_of_component_eq T e hleft).symm
  have hfLeft : T.RightCut e.1 (T.edgeLeft f.1) := by
    change (T.cutGraph e.1).Reachable
      (T.edgeLeft f.1) (T.edgeRight e.1)
    exact (oddCut_reachable_of_component_eq T e hright).symm
  have hemem : e.1.1 ∈
      T.pathEdges (T.edgeRight f.1) (T.edgeLeft f.1) :=
    (T.mem_pathEdges_iff_opposite_cuts e.1 _ _).2
      (Or.inl ⟨hfRight, hfLeft⟩)
  rw [T.pathEdges_comm (T.edgeRight f.1) (T.edgeLeft f.1),
    T.pathEdges_edge f.1] at hemem
  exact Subtype.ext (Subtype.ext (Finset.mem_singleton.mp hemem))

/-- No two distinct actual odd bridges collapse to one quotient edge.  This
is the multiplicity-safety theorem for the simple quotient. -/
theorem quotientEdgePair_injective (T : PosIntTree n) :
    Function.Injective (quotientEdgePair T) := by
  intro e f hef
  rw [quotientEdgePair_eq, quotientEdgePair_eq] at hef
  rcases Sym2.eq_iff.mp hef with hdirect | hswap
  · exact oddBridge_eq_of_direct_component_ends T e f
      hdirect.1 hdirect.2
  · exact oddBridge_eq_of_swapped_component_ends T e f
      hswap.1 hswap.2

/-! ## The quotient graph and its actual-edge equivalence -/

/-- The simple graph whose edge set is exactly the range of the indexed
actual odd physical edges under component contraction. -/
noncomputable def quotientGraph (T : PosIntTree n) :
    SimpleGraph (EvenComponent T) :=
  SimpleGraph.fromEdgeSet (Set.range (quotientEdgePair T))

/-- No diagonal is lost when `fromEdgeSet` forms the simple quotient. -/
theorem quotientGraph_edgeSet (T : PosIntTree n) :
    (quotientGraph T).edgeSet = Set.range (quotientEdgePair T) := by
  rw [quotientGraph, SimpleGraph.edgeSet_fromEdgeSet]
  apply sdiff_eq_left.mpr
  rw [Set.disjoint_left]
  intro q hq hdiag
  obtain ⟨e, rfl⟩ := hq
  exact quotientEdgePair_not_isDiag T e hdiag

@[simp] theorem quotientGraph_adj_iff (T : PosIntTree n)
    (C D : EvenComponent T) :
    (quotientGraph T).Adj C D ↔
      ∃ e : OddBridge T, quotientEdgePair T e = s(C, D) := by
  constructor
  · intro h
    have hm : s(C, D) ∈ (quotientGraph T).edgeSet := by
      rwa [SimpleGraph.mem_edgeSet]
    rw [quotientGraph_edgeSet] at hm
    exact hm
  · rintro ⟨e, he⟩
    rw [← SimpleGraph.mem_edgeSet, quotientGraph_edgeSet]
    exact ⟨e, he⟩

/-- The quotient edge carried by one indexed actual odd bridge. -/
noncomputable def quotientEdgeOfOddBridge
    (T : PosIntTree n) (e : OddBridge T) :
    (quotientGraph T).edgeSet :=
  ⟨quotientEdgePair T e, by
    rw [quotientGraph_edgeSet]
    exact Set.mem_range_self e⟩

/-- Actual odd physical edges and quotient edges are equivalent, rather than
merely having the same support. -/
noncomputable def oddBridgeQuotientEdgeEquiv (T : PosIntTree n) :
    OddBridge T ≃ (quotientGraph T).edgeSet :=
  Equiv.ofBijective (quotientEdgeOfOddBridge T) <| by
    constructor
    · intro e f hef
      apply quotientEdgePair_injective T
      exact congrArg Subtype.val hef
    · intro q
      have hq : q.1 ∈ Set.range (quotientEdgePair T) := by
        rw [← quotientGraph_edgeSet T]
        exact q.2
      obtain ⟨e, he⟩ := hq
      exact ⟨e, Subtype.ext he⟩

/-! ## Actual named ports for an oriented quotient adjacency -/

/-- An actual odd bridge oriented from quotient component `C` to quotient
component `D`.  The two port vertices are actual named vertices of `Fin n`;
`edge_eq_ports` says that they are the physical endpoints of `bridge`. -/
structure OrientedBridge (T : PosIntTree n)
    (C D : EvenComponent T) where
  bridge : OddBridge T
  sourcePortVertex : Fin n
  targetPortVertex : Fin n
  edge_eq_ports : bridge.1.1 = s(sourcePortVertex, targetPortVertex)
  source_component : componentOf T sourcePortVertex = C
  target_component : componentOf T targetPortVertex = D
  component_pair : quotientEdgePair T bridge = s(C, D)

namespace OrientedBridge

def sourcePort {T : PosIntTree n} {C D : EvenComponent T}
    (b : OrientedBridge T C D) : ComponentVertex T C :=
  ⟨b.sourcePortVertex, b.source_component⟩

def targetPort {T : PosIntTree n} {C D : EvenComponent T}
    (b : OrientedBridge T C D) : ComponentVertex T D :=
  ⟨b.targetPortVertex, b.target_component⟩

end OrientedBridge

/-- Every quotient adjacency supplies its unique indexed physical odd bridge
with the correct actual endpoint port in each incident component. -/
theorem exists_orientedBridge_of_adj (T : PosIntTree n)
    {C D : EvenComponent T} (h : (quotientGraph T).Adj C D) :
    Nonempty (OrientedBridge T C D) := by
  obtain ⟨e, he⟩ := (quotientGraph_adj_iff T C D).mp h
  have hend := he
  rw [quotientEdgePair_eq] at hend
  rcases Sym2.eq_iff.mp hend with hdirect | hswap
  · exact ⟨{
      bridge := e
      sourcePortVertex := T.edgeLeft e.1
      targetPortVertex := T.edgeRight e.1
      edge_eq_ports := T.edge_eq_mk_endpoints e.1
      source_component := hdirect.1
      target_component := hdirect.2
      component_pair := he }⟩
  · exact ⟨{
      bridge := e
      sourcePortVertex := T.edgeRight e.1
      targetPortVertex := T.edgeLeft e.1
      edge_eq_ports := (T.edge_eq_mk_endpoints e.1).trans
        Sym2.eq_swap
      source_component := hswap.2
      target_component := hswap.1
      component_pair := he }⟩

/-- The proof-irrelevant chosen orientation of the actual bridge underlying a
quotient adjacency.  Uniqueness follows from `quotientEdgePair_injective`. -/
noncomputable def orientedBridgeOfAdj (T : PosIntTree n)
    {C D : EvenComponent T} (h : (quotientGraph T).Adj C D) :
    OrientedBridge T C D :=
  Classical.choice (exists_orientedBridge_of_adj T h)

/-- The nonnegative half-parameter `q` in the odd physical weight `2*q+1`. -/
def bridgeHalfWeight (T : PosIntTree n) (e : OddBridge T) : ℕ :=
  T.weight e.1 / 2

/-- Every actual odd bridge weight is exactly `2*q+1`. -/
theorem bridge_weight_eq_two_mul_half_add_one
    (T : PosIntTree n) (e : OddBridge T) :
    T.weight e.1 = 2 * bridgeHalfWeight T e + 1 := by
  exact (Nat.two_mul_div_two_add_one_of_odd e.2).symm

/-! ## Connectivity and acyclicity of the quotient -/

/-- A fixed named representative of each even component. -/
noncomputable def componentRep (T : PosIntTree n) (C : EvenComponent T) :
    Fin n :=
  Classical.choose (componentOf_surjective T C)

@[simp] theorem componentOf_componentRep
    (T : PosIntTree n) (C : EvenComponent T) :
    componentOf T (componentRep T C) = C :=
  Classical.choose_spec (componentOf_surjective T C)

/-- One original physical adjacency contracts either to equality or to one
actual odd quotient edge. -/
theorem quotient_reachable_of_adj (T : PosIntTree n) {u v : Fin n}
    (h : T.graph.Adj u v) :
    (quotientGraph T).Reachable (componentOf T u) (componentOf T v) := by
  classical
  by_cases hcomp : componentOf T u = componentOf T v
  · rw [hcomp]
  · have hoddPair : Odd (T.weightOfPair s(u, v)) := by
      rw [← Nat.not_even_iff_odd]
      intro heven
      have hevAdj : (evenForest T).Adj u v :=
        (evenForest_adj_iff T).2 ⟨h, heven⟩
      apply hcomp
      simpa [componentOf] using
        SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hevAdj
    let e : T.Edge := ⟨s(u, v), by
      simpa only [SimpleGraph.mem_edgeSet] using h⟩
    have hodd : Odd (T.weight e) := by
      rw [← T.weightOfPair_edge e]
      exact hoddPair
    let b : OddBridge T := ⟨e, hodd⟩
    have hb : quotientEdgePair T b =
        s(componentOf T u, componentOf T v) := by
      simp [quotientEdgePair, b, e, Sym2.map_pair_eq]
    exact ((quotientGraph_adj_iff T _ _).2 ⟨b, hb⟩).reachable

/-- Original reachability descends to quotient reachability, with even edges
contracted to stationary steps. -/
theorem quotient_reachable_of_reachable (T : PosIntTree n) {u v : Fin n}
    (h : T.graph.Reachable u v) :
    (quotientGraph T).Reachable (componentOf T u) (componentOf T v) := by
  apply h.elim
  intro p
  induction p with
  | nil => exact SimpleGraph.Reachable.rfl
  | @cons u v w huv p ih =>
      exact (quotient_reachable_of_adj T huv).trans (ih p.reachable)

/-- Contracting all even components leaves a connected quotient. -/
theorem quotientGraph_connected (T : PosIntTree n) :
    (quotientGraph T).Connected := by
  letI : Nonempty (EvenComponent T) :=
    T.isTree.isConnected.nonempty.map (componentOf T)
  refine ⟨?_⟩
  intro C D
  obtain ⟨u, rfl⟩ := componentOf_surjective T C
  obtain ⟨v, rfl⟩ := componentOf_surjective T D
  exact quotient_reachable_of_reachable T (T.isTree.isConnected u v)

/-- The quotient with one specified mapped odd edge deleted. -/
noncomputable def quotientCutGraph
    (T : PosIntTree n) (e : OddBridge T) :
    SimpleGraph (EvenComponent T) :=
  (quotientGraph T).deleteEdges {quotientEdgePair T e}

@[simp] theorem quotientCutGraph_adj_iff
    (T : PosIntTree n) (e : OddBridge T)
    {C D : EvenComponent T} :
    (quotientCutGraph T e).Adj C D ↔
      (quotientGraph T).Adj C D ∧
        s(C, D) ≠ quotientEdgePair T e := by
  rw [quotientCutGraph, SimpleGraph.deleteEdges_adj]
  simp only [Set.mem_singleton_iff]

/-- A different oriented odd bridge remains an adjacency in the original
one-edge cut graph. -/
theorem oddCut_adj_of_orientedBridge_ne
    (T : PosIntTree n) (cut : OddBridge T)
    {C D : EvenComponent T} (b : OrientedBridge T C D)
    (hne : b.bridge ≠ cut) :
    (T.cutGraph cut.1).Adj b.sourcePortVertex b.targetPortVertex := by
  classical
  rw [PosIntTree.cutGraph, SimpleGraph.deleteEdges_adj]
  constructor
  · rw [← SimpleGraph.mem_edgeSet, ← b.edge_eq_ports]
    exact b.bridge.1.2
  · simp only [Set.mem_singleton_iff]
    intro heq
    apply hne
    exact Subtype.ext (Subtype.ext (b.edge_eq_ports.trans heq))

/-- A single quotient-cut step lifts, between fixed component
representatives, to reachability in the corresponding original one-edge
cut. -/
theorem quotientCut_step_lift
    (T : PosIntTree n) (cut : OddBridge T)
    {C D : EvenComponent T} (h : (quotientCutGraph T cut).Adj C D) :
    (T.cutGraph cut.1).Reachable (componentRep T C) (componentRep T D) := by
  have h' := (quotientCutGraph_adj_iff T cut).mp h
  let b := orientedBridgeOfAdj T h'.1
  have hbne : b.bridge ≠ cut := by
    intro heq
    apply h'.2
    calc
      s(C, D) = quotientEdgePair T b.bridge := b.component_pair.symm
      _ = quotientEdgePair T cut := congrArg (quotientEdgePair T) heq
  have hsource : (T.cutGraph cut.1).Reachable
      (componentRep T C) b.sourcePortVertex :=
    oddCut_reachable_of_component_eq T cut
      ((componentOf_componentRep T C).trans b.source_component.symm)
  have hbridge : (T.cutGraph cut.1).Reachable
      b.sourcePortVertex b.targetPortVertex :=
    (oddCut_adj_of_orientedBridge_ne T cut b hbne).reachable
  have htarget : (T.cutGraph cut.1).Reachable
      b.targetPortVertex (componentRep T D) :=
    oddCut_reachable_of_component_eq T cut
      (b.target_component.trans (componentOf_componentRep T D).symm)
  exact hsource.trans (hbridge.trans htarget)

/-- A quotient walk avoiding one quotient edge lifts to original
reachability avoiding its indexed physical odd bridge. -/
theorem quotientCut_reachable_rep_lift
    (T : PosIntTree n) (cut : OddBridge T)
    {C D : EvenComponent T}
    (h : (quotientCutGraph T cut).Reachable C D) :
    (T.cutGraph cut.1).Reachable (componentRep T C) (componentRep T D) := by
  apply h.elim
  intro p
  induction p with
  | nil => exact SimpleGraph.Reachable.rfl
  | @cons C D E hCD p ih =>
      exact (quotientCut_step_lift T cut hCD).trans (ih p.reachable)

/-- The preceding lift with arbitrary named vertices at the two endpoint
components. -/
theorem quotientCut_reachable_lift
    (T : PosIntTree n) (cut : OddBridge T)
    {C D : EvenComponent T}
    (h : (quotientCutGraph T cut).Reachable C D)
    {u v : Fin n} (hu : componentOf T u = C)
    (hv : componentOf T v = D) :
    (T.cutGraph cut.1).Reachable u v := by
  have hstart : (T.cutGraph cut.1).Reachable u (componentRep T C) :=
    oddCut_reachable_of_component_eq T cut
      (hu.trans (componentOf_componentRep T C).symm)
  have hend : (T.cutGraph cut.1).Reachable (componentRep T D) v :=
    oddCut_reachable_of_component_eq T cut
      ((componentOf_componentRep T D).trans hv.symm)
  exact hstart.trans ((quotientCut_reachable_rep_lift T cut h).trans hend)

/-- Every indexed quotient edge is a bridge. -/
theorem quotientEdgePair_isBridge
    (T : PosIntTree n) (e : OddBridge T) :
    (quotientGraph T).IsBridge (quotientEdgePair T e) := by
  rw [quotientEdgePair_eq, SimpleGraph.isBridge_iff]
  constructor
  · exact (quotientGraph_adj_iff T _ _).2
      ⟨e, quotientEdgePair_eq T e⟩
  · intro hreach
    have hcut : (quotientCutGraph T e).Reachable
        (componentOf T (T.edgeLeft e.1))
        (componentOf T (T.edgeRight e.1)) := by
      simpa [quotientCutGraph, quotientEdgePair_eq] using hreach
    have hlift := quotientCut_reachable_lift T e hcut
      (u := T.edgeLeft e.1) (v := T.edgeRight e.1) rfl rfl
    exact T.cut_endpoints_not_reachable e.1 hlift

/-- The odd quotient is acyclic because every one of its indexed edges is a
bridge. -/
theorem quotientGraph_isAcyclic (T : PosIntTree n) :
    (quotientGraph T).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_edge_isBridge]
  intro q hq
  rw [quotientGraph_edgeSet] at hq
  obtain ⟨e, rfl⟩ := hq
  exact quotientEdgePair_isBridge T e

/-- Deleting all actual odd physical edges and contracting the resulting
even components produces a genuine tree. -/
theorem quotientGraph_isTree (T : PosIntTree n) :
    (quotientGraph T).IsTree :=
  ⟨quotientGraph_connected T, quotientGraph_isAcyclic T⟩

/-- The canonical quotient path between two even components. -/
noncomputable def quotientPath (T : PosIntTree n)
    (C D : EvenComponent T) : (quotientGraph T).Path C D := by
  let p := Classical.choose ((quotientGraph_isTree T).existsUnique_path C D)
  exact ⟨p, (Classical.choose_spec
    ((quotientGraph_isTree T).existsUnique_path C D)).1⟩

/-- Uniqueness of the canonical quotient path. -/
theorem quotientPath_unique (T : PosIntTree n)
    {C D : EvenComponent T} (p : (quotientGraph T).Path C D) :
    p = quotientPath T C D :=
  (quotientGraph_isTree T).IsAcyclic.path_unique p (quotientPath T C D)

/-! ## Route distances with every intermediate actual-port separation -/

/-- Orientation-neutral one-bridge distance decomposition.  The supplied
ports must be the two actual physical endpoints, but may be listed in either
orientation. -/
theorem orientedBridge_distance_decomposition
    (T : PosIntTree n) {C D : EvenComponent T}
    (b : OrientedBridge T C D) {u v : Fin n}
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
      change (T.cutGraph b.bridge.1).Reachable u
        (T.edgeLeft b.bridge.1)
      simpa [hdirect.1] using hu
    have hvRight : T.RightCut b.bridge.1 v := by
      change (T.cutGraph b.bridge.1).Reachable v
        (T.edgeRight b.bridge.1)
      simpa [hdirect.2] using hv
    simpa [hdirect.1, hdirect.2] using
      T.cross_distance_decomposition b.bridge.1 huLeft hvRight
  · have hvLeft : T.LeftCut b.bridge.1 v := by
      change (T.cutGraph b.bridge.1).Reachable v
        (T.edgeLeft b.bridge.1)
      simpa [hswap.1] using hv
    have huRight : T.RightCut b.bridge.1 u := by
      change (T.cutGraph b.bridge.1).Reachable u
        (T.edgeRight b.bridge.1)
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

/-- The terminal actual port reached by an oriented quotient walk.  For the
empty walk it is the supplied vertex; for a nonempty walk it is the target
port of the last actual bridge. -/
noncomputable def routeTerminal (T : PosIntTree n) :
    {C D : EvenComponent T} →
      (p : (quotientGraph T).Walk C D) →
      ComponentVertex T C → ComponentVertex T D
  | _, _, .nil, x => x
  | _, _, .cons h p, _ =>
      routeTerminal T p (orientedBridgeOfAdj T h).targetPort

/-- The route contribution before the final endpoint depth.  Recursion makes
the intermediate term explicit: after crossing one bridge, the next call
starts at its actual target port, so the next `rho` is exactly the separation
to the following bridge's actual source port. -/
noncomputable def routeInteriorCost (T : PosIntTree n) :
    {C D : EvenComponent T} →
      (p : (quotientGraph T).Walk C D) →
      ComponentVertex T C → ℕ
  | _, _, .nil, _ => 0
  | _, _, .cons h p, x =>
      rho T x (orientedBridgeOfAdj T h).sourcePort +
        bridgeHalfWeight T (orientedBridgeOfAdj T h).bridge +
        routeInteriorCost T p (orientedBridgeOfAdj T h).targetPort

/-- The full scaled contribution of a quotient walk, including both endpoint
depths and every intermediate actual-port separation. -/
noncomputable def routeCost (T : PosIntTree n)
    {C D : EvenComponent T} (p : (quotientGraph T).Walk C D)
    (x : ComponentVertex T C) (y : ComponentVertex T D) : ℕ :=
  routeInteriorCost T p x + rho T (routeTerminal T p x) y

@[simp] theorem routeTerminal_nil (T : PosIntTree n)
    {C : EvenComponent T} (x : ComponentVertex T C) :
    routeTerminal T (.nil : (quotientGraph T).Walk C C) x = x := rfl

@[simp] theorem routeTerminal_cons (T : PosIntTree n)
    {C D E : EvenComponent T} (h : (quotientGraph T).Adj C D)
    (p : (quotientGraph T).Walk D E) (x : ComponentVertex T C) :
    routeTerminal T (.cons h p) x =
      routeTerminal T p (orientedBridgeOfAdj T h).targetPort := rfl

@[simp] theorem routeInteriorCost_nil (T : PosIntTree n)
    {C : EvenComponent T} (x : ComponentVertex T C) :
    routeInteriorCost T (.nil : (quotientGraph T).Walk C C) x = 0 := rfl

@[simp] theorem routeInteriorCost_cons (T : PosIntTree n)
    {C D E : EvenComponent T} (h : (quotientGraph T).Adj C D)
    (p : (quotientGraph T).Walk D E) (x : ComponentVertex T C) :
    routeInteriorCost T (.cons h p) x =
      rho T x (orientedBridgeOfAdj T h).sourcePort +
        bridgeHalfWeight T (orientedBridgeOfAdj T h).bridge +
        routeInteriorCost T p (orientedBridgeOfAdj T h).targetPort := rfl

@[simp] theorem routeCost_nil (T : PosIntTree n)
    {C : EvenComponent T} (x y : ComponentVertex T C) :
    routeCost T (.nil : (quotientGraph T).Walk C C) x y = rho T x y := by
  simp [routeCost]

/-- The recursive route-cost equation.  On two consecutive calls its first
term inside the next component is the actual exit-to-entry port separation. -/
theorem routeCost_cons (T : PosIntTree n)
    {C D E : EvenComponent T} (h : (quotientGraph T).Adj C D)
    (p : (quotientGraph T).Walk D E)
    (x : ComponentVertex T C) (y : ComponentVertex T E) :
    routeCost T (.cons h p) x y =
      rho T x (orientedBridgeOfAdj T h).sourcePort +
        bridgeHalfWeight T (orientedBridgeOfAdj T h).bridge +
        routeCost T p (orientedBridgeOfAdj T h).targetPort y := by
  simp [routeCost, add_assoc]

/-- The first explicit two-step expansion.  Repeated use gives one displayed
`rho(exit,entry)` term for every intermediate quotient component. -/
theorem routeCost_cons_cons (T : PosIntTree n)
    {C₀ C₁ C₂ E : EvenComponent T}
    (h₁ : (quotientGraph T).Adj C₀ C₁)
    (h₂ : (quotientGraph T).Adj C₁ C₂)
    (p : (quotientGraph T).Walk C₂ E)
    (x : ComponentVertex T C₀) (y : ComponentVertex T E) :
    routeCost T (.cons h₁ (.cons h₂ p)) x y =
      rho T x (orientedBridgeOfAdj T h₁).sourcePort +
      bridgeHalfWeight T (orientedBridgeOfAdj T h₁).bridge +
      rho T (orientedBridgeOfAdj T h₁).targetPort
        (orientedBridgeOfAdj T h₂).sourcePort +
      bridgeHalfWeight T (orientedBridgeOfAdj T h₂).bridge +
      routeCost T p (orientedBridgeOfAdj T h₂).targetPort y := by
  rw [routeCost_cons, routeCost_cons]
  omega

/-- Direct route addition before taking a half-rank: a quotient path with
`k` actual odd bridges has raw distance `2 * routeCost + k`. -/
theorem dist_eq_two_mul_routeCost_add_length
    (T : PosIntTree n) {C D : EvenComponent T}
    (p : (quotientGraph T).Walk C D) (hp : p.IsPath)
    (x : ComponentVertex T C) (y : ComponentVertex T D) :
    T.dist x.1 y.1 = 2 * routeCost T p x y + p.length := by
  induction p with
  | nil =>
      simpa using dist_eq_two_mul_rho T x y
  | @cons C D E h p ih =>
      have hpTail : p.IsPath := hp.of_cons
      have havoid : s(C, D) ∉ p.edges :=
        ((SimpleGraph.Walk.cons_isTrail_iff h p).mp hp.isTrail).2
      let b := orientedBridgeOfAdj T h
      have htailDelete : (quotientCutGraph T b.bridge).Reachable D E := by
        rw [quotientCutGraph, b.component_pair]
        exact (SimpleGraph.reachable_delete_edges_iff_exists_walk).2
          ⟨p, havoid⟩
      have htailCut : (T.cutGraph b.bridge.1).Reachable
          b.targetPortVertex y.1 :=
        quotientCut_reachable_lift T b.bridge htailDelete
          b.target_component y.2
      have hsourceCut : (T.cutGraph b.bridge.1).Reachable
          x.1 b.sourcePortVertex :=
        oddCut_reachable_of_component_eq T b.bridge
          (x.2.trans b.source_component.symm)
      have hsplit := orientedBridge_distance_decomposition T b
        hsourceCut htailCut.symm
      have hstart := dist_eq_two_mul_rho T x b.sourcePort
      change T.dist x.1 b.sourcePortVertex =
        2 * rho T x b.sourcePort at hstart
      have hweight := bridge_weight_eq_two_mul_half_add_one T b.bridge
      have htail := ih hpTail b.targetPort y
      change T.dist b.targetPortVertex y.1 =
        2 * routeCost T p b.targetPort y + p.length at htail
      calc
        T.dist x.1 y.1 = T.dist x.1 b.sourcePortVertex +
            T.weight b.bridge.1 + T.dist b.targetPortVertex y.1 := hsplit
        _ = 2 * routeCost T (SimpleGraph.Walk.cons h p) x y +
            (SimpleGraph.Walk.cons h p).length := by
          rw [hstart, hweight, htail, routeCost_cons]
          simp only [SimpleGraph.Walk.length, b]
          omega

/-- The coefficient exponent attached to an indexed endpoint pair.  It is
the full route cost plus `floor(k/2)`. -/
noncomputable def routeHalfRank (T : PosIntTree n)
    {C D : EvenComponent T} (p : (quotientGraph T).Walk C D)
    (x : ComponentVertex T C) (y : ComponentVertex T D) : ℕ :=
  routeCost T p x y + p.length / 2

/-- Universal quotient-path half-rank identity. -/
theorem dist_eq_two_mul_routeHalfRank_add_mod
    (T : PosIntTree n) {C D : EvenComponent T}
    (p : (quotientGraph T).Walk C D) (hp : p.IsPath)
    (x : ComponentVertex T C) (y : ComponentVertex T D) :
    T.dist x.1 y.1 =
      2 * routeHalfRank T p x y + p.length % 2 := by
  have hraw := dist_eq_two_mul_routeCost_add_length T p hp x y
  have hmod := Nat.mod_add_div p.length 2
  rw [hraw, routeHalfRank]
  omega

/-- Canonical-path specialization of the universal half-rank identity. -/
theorem dist_eq_two_mul_canonicalRouteHalfRank_add_mod
    (T : PosIntTree n) {C D : EvenComponent T}
    (x : ComponentVertex T C) (y : ComponentVertex T D) :
    T.dist x.1 y.1 =
      2 * routeHalfRank T (quotientPath T C D).1 x y +
        (quotientPath T C D).1.length % 2 :=
  dist_eq_two_mul_routeHalfRank_add_mod T (quotientPath T C D).1
    (quotientPath T C D).2 x y

/-- The route shift independent of the two endpoint vertices.  The recursive
interior cost starts at the first bridge's actual exit port, so all of its
positive-length component terms are actual intermediate port separations. -/
noncomputable def routeShift (T : PosIntTree n)
    {C D E : EvenComponent T} (h : (quotientGraph T).Adj C D)
    (p : (quotientGraph T).Walk D E) : ℕ :=
  bridgeHalfWeight T (orientedBridgeOfAdj T h).bridge +
    routeInteriorCost T p (orientedBridgeOfAdj T h).targetPort +
    (.cons h p : (quotientGraph T).Walk C E).length / 2

/-- Endpoint-rooted form of the universal route identity.  This is the
division-free statement underlying the shifted product of the two rooted
endpoint enumerators. -/
theorem dist_eq_endpoint_rhos_routeShift
    (T : PosIntTree n) {C D E : EvenComponent T}
    (h : (quotientGraph T).Adj C D)
    (p : (quotientGraph T).Walk D E)
    (hp : (.cons h p : (quotientGraph T).Walk C E).IsPath)
    (x : ComponentVertex T C) (y : ComponentVertex T E) :
    T.dist x.1 y.1 =
      2 * (rho T x (orientedBridgeOfAdj T h).sourcePort +
        routeShift T h p +
        rho T
          (routeTerminal T p (orientedBridgeOfAdj T h).targetPort) y) +
      (.cons h p : (quotientGraph T).Walk C E).length % 2 := by
  have hhalf := dist_eq_two_mul_routeHalfRank_add_mod T
    (.cons h p) hp x y
  rw [hhalf, routeHalfRank, routeCost_cons]
  simp only [routeCost, routeShift]
  omega

/-- With two consecutive quotient edges, `routeShift` visibly contains the
scaled separation between the first actual exit port and the second actual
entry port.  Recursing gives every intermediate separation. -/
theorem routeShift_cons (T : PosIntTree n)
    {C₀ C₁ C₂ E : EvenComponent T}
    (h₁ : (quotientGraph T).Adj C₀ C₁)
    (h₂ : (quotientGraph T).Adj C₁ C₂)
    (p : (quotientGraph T).Walk C₂ E) :
    routeShift T h₁ (.cons h₂ p) =
      bridgeHalfWeight T (orientedBridgeOfAdj T h₁).bridge +
      rho T (orientedBridgeOfAdj T h₁).targetPort
        (orientedBridgeOfAdj T h₂).sourcePort +
      bridgeHalfWeight T (orientedBridgeOfAdj T h₂).bridge +
      routeInteriorCost T p (orientedBridgeOfAdj T h₂).targetPort +
      (.cons h₁ (.cons h₂ p) :
        (quotientGraph T).Walk C₀ E).length / 2 := by
  simp only [routeShift, routeInteriorCost_cons]
  omega

end LeechTrees.OddQuotient
