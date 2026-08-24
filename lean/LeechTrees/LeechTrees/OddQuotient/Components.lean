import LeechTrees.Foundations

/-!
# Odd-edge deletion and even components

This file is the first layer of the odd-quotient representation.  It deletes
exactly the actual odd physical edges of an existing positive integral tree,
uses reachability in the resulting spanning forest as the component relation,
and defines the component metric by halving actual full-tree distances.

Nothing in this file is a realization criterion or a converse construction.
-/

namespace LeechTrees.OddQuotient

open LeechTrees.Foundation

variable {n : ℕ}

/-- The spanning forest obtained by deleting exactly the physical edges of
odd weight.  Nonedges have `weightOfPair = 0`, so allowing the deletion set to
range over every unordered vertex pair does not remove any additional edge. -/
noncomputable def evenForest (T : PosIntTree n) : SimpleGraph (Fin n) :=
  T.graph.deleteEdges {e | Odd (T.weightOfPair e)}

@[simp] theorem evenForest_adj_iff (T : PosIntTree n) {u v : Fin n} :
    (evenForest T).Adj u v ↔
      T.graph.Adj u v ∧ Even (T.weightOfPair s(u, v)) := by
  rw [evenForest, SimpleGraph.deleteEdges_adj]
  simp only [Set.mem_setOf_eq]
  rw [Nat.not_odd_iff_even]

/-- The even forest is a spanning subgraph of the original tree. -/
theorem evenForest_le (T : PosIntTree n) : evenForest T ≤ T.graph :=
  SimpleGraph.deleteEdges_le _

/-- Deleting the odd edges of a tree leaves an acyclic spanning forest. -/
theorem evenForest_isAcyclic (T : PosIntTree n) :
    (evenForest T).IsAcyclic :=
  T.isTree.IsAcyclic.anti (evenForest_le T)

/-- The canonical type of components after all odd physical edges are
deleted. -/
abbrev EvenComponent (T : PosIntTree n) :=
  (evenForest T).ConnectedComponent

noncomputable instance evenComponentFintype (T : PosIntTree n) :
    Fintype (EvenComponent T) :=
  Fintype.ofFinite _

noncomputable instance evenComponentDecidableEq (T : PosIntTree n) :
    DecidableEq (EvenComponent T) :=
  Classical.decEq _

/-- The even component containing a named vertex. -/
def componentOf (T : PosIntTree n) (v : Fin n) : EvenComponent T :=
  (evenForest T).connectedComponentMk v

@[simp] theorem componentOf_eq_iff (T : PosIntTree n) (u v : Fin n) :
    componentOf T u = componentOf T v ↔
      (evenForest T).Reachable u v :=
  SimpleGraph.ConnectedComponent.eq

/-- Every even component contains an actual named vertex. -/
theorem componentOf_surjective (T : PosIntTree n) :
    Function.Surjective (componentOf T) := by
  intro C
  obtain ⟨v, rfl⟩ := C.exists_rep
  exact ⟨v, rfl⟩

/-- The named vertices in one fixed even component. -/
abbrev ComponentVertex (T : PosIntTree n) (C : EvenComponent T) :=
  {v : Fin n // componentOf T v = C}

/-- Every connected component of the even forest is itself a tree. -/
theorem evenComponent_isTree (T : PosIntTree n) (C : EvenComponent T) :
    C.toSimpleGraph.IsTree :=
  (evenForest_isAcyclic T).isTree_connectedComponent C

/-- If two named vertices lie in the same even component, every edge of their
canonical path in the original tree has even physical weight. -/
theorem path_edge_even_of_component_eq
    (T : PosIntTree n) {u v : Fin n}
    (hcomp : componentOf T u = componentOf T v)
    {e : Sym2 (Fin n)} (he : e ∈ T.pathEdges u v) :
    Even (T.weightOfPair e) := by
  have hr : (evenForest T).Reachable u v :=
    (componentOf_eq_iff T u v).mp hcomp
  obtain ⟨p, hp⟩ := hr.exists_isPath
  let pT : T.graph.Path u v :=
    ⟨p.mapLe (evenForest_le T), hp.mapLe (evenForest_le T)⟩
  have hcanon : pT = T.path u v := T.path_unique pT
  have heCanon : e ∈ (T.path u v).1.edges := by
    simpa [PosIntTree.pathEdges] using he
  have hePT : e ∈ pT.1.edges := by
    rw [hcanon]
    exact heCanon
  have heP : e ∈ p.edges := by
    simpa [pT] using hePT
  induction e using Sym2.ind with
  | _ x y =>
      have hadj : (evenForest T).Adj x y := p.adj_of_mem_edges heP
      exact (evenForest_adj_iff T).mp hadj |>.2

/-- Conversely, an original canonical path using only even physical edges is
a walk in the even forest, so its endpoints lie in the same component. -/
theorem componentOf_eq_of_path_all_even
    (T : PosIntTree n) {u v : Fin n}
    (hall : ∀ e ∈ T.pathEdges u v, Even (T.weightOfPair e)) :
    componentOf T u = componentOf T v := by
  apply (componentOf_eq_iff T u v).mpr
  change (T.graph.deleteEdges {e | Odd (T.weightOfPair e)}).Reachable u v
  refine ⟨(T.path u v).1.toDeleteEdges {e | Odd (T.weightOfPair e)} ?_⟩
  intro e he
  have heFinset : e ∈ T.pathEdges u v := by
    simpa [PosIntTree.pathEdges] using he
  exact (Nat.not_odd_iff_even.mpr (hall e heFinset))

/-- Exact path characterization of the components obtained by deleting all
odd physical edges. -/
theorem componentOf_eq_iff_path_all_even
    (T : PosIntTree n) (u v : Fin n) :
    componentOf T u = componentOf T v ↔
      ∀ e ∈ T.pathEdges u v, Even (T.weightOfPair e) := by
  constructor
  · intro h e he
    exact path_edge_even_of_component_eq T h he
  · exact componentOf_eq_of_path_all_even T

/-- Distances inside one even component are even in the original tree. -/
theorem dist_even_of_component_eq
    (T : PosIntTree n) {u v : Fin n}
    (hcomp : componentOf T u = componentOf T v) :
    Even (T.dist u v) := by
  let oddOnPath :=
    (T.pathEdges u v).filter fun e => Odd (T.weightOfPair e)
  have hfilter : oddOnPath = ∅ := by
    classical
    dsimp only [oddOnPath]
    apply Finset.filter_eq_empty_iff.mpr
    intro e he
    have heven := path_edge_even_of_component_eq T hcomp he
    exact Nat.not_odd_iff_even.mpr heven
  change Even (∑ e ∈ T.pathEdges u v, T.weightOfPair e)
  rw [Finset.even_sum_iff_even_card_odd]
  change Even oddOnPath.card
  rw [hfilter]
  simp

/-- The scaled integral metric inside one even component. -/
noncomputable def rho (T : PosIntTree n) {C : EvenComponent T}
    (u v : ComponentVertex T C) : ℕ :=
  T.dist u.1 v.1 / 2

/-- Halving is exact inside an even component. -/
theorem dist_eq_two_mul_rho (T : PosIntTree n) {C : EvenComponent T}
    (u v : ComponentVertex T C) :
    T.dist u.1 v.1 = 2 * rho T u v := by
  have hcomp : componentOf T u.1 = componentOf T v.1 := u.2.trans v.2.symm
  exact (Nat.two_mul_div_two_of_even
    (dist_even_of_component_eq T hcomp)).symm

@[simp] theorem rho_self (T : PosIntTree n) {C : EvenComponent T}
    (u : ComponentVertex T C) : rho T u u = 0 := by
  simp [rho]

theorem rho_comm (T : PosIntTree n) {C : EvenComponent T}
    (u v : ComponentVertex T C) : rho T u v = rho T v u := by
  simp only [rho]
  rw [T.dist_comm]

/-- The indexed type of actual odd physical edges. -/
abbrev OddBridge (T : PosIntTree n) :=
  {e : T.Edge // Odd (T.weight e)}

/-- An odd physical edge cannot have both endpoints in one even component. -/
theorem oddBridge_components_ne (T : PosIntTree n) (e : OddBridge T) :
    componentOf T (T.edgeLeft e.1) ≠
      componentOf T (T.edgeRight e.1) := by
  intro hcomp
  have hemem : e.1.1 ∈
      T.pathEdges (T.edgeLeft e.1) (T.edgeRight e.1) := by
    rw [T.pathEdges_edge e.1]
    simp
  have hevenPair := path_edge_even_of_component_eq T hcomp hemem
  have heven : Even (T.weight e.1) := by
    simpa using hevenPair
  exact (Nat.not_odd_iff_even.mpr heven) e.2

/-- The endpoints of an even physical edge lie in the same even component. -/
theorem evenEdge_components_eq (T : PosIntTree n) (e : T.Edge)
    (heven : Even (T.weight e)) :
    componentOf T (T.edgeLeft e) =
      componentOf T (T.edgeRight e) := by
  apply componentOf_eq_of_path_all_even T
  intro f hf
  rw [T.pathEdges_edge e] at hf
  have hfe : f = e.1 := Finset.mem_singleton.mp hf
  subst f
  simpa using heven

/-- For an actual physical edge, odd weight is equivalent to joining two
different even components. -/
theorem odd_weight_iff_components_ne (T : PosIntTree n) (e : T.Edge) :
    Odd (T.weight e) ↔
      componentOf T (T.edgeLeft e) ≠
        componentOf T (T.edgeRight e) := by
  constructor
  · intro hodd
    exact oddBridge_components_ne T ⟨e, hodd⟩
  · intro hne
    rw [← Nat.not_even_iff_odd]
    intro heven
    exact hne (evenEdge_components_eq T e heven)

end LeechTrees.OddQuotient
