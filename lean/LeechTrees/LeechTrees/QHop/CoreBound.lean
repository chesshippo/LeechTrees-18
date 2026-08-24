import LeechTrees.QHop.Adapter

open scoped BigOperators

namespace LeechTrees.QHop

open LeechTrees.Foundation
open SimpleGraph

namespace RootedCut

variable {n : ℕ} (T : PosIntTree n) (r : Fin n)

noncomputable local instance propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The component of `T - e` which does not contain the chosen root. -/
noncomputable def Away (e : T.Edge) (x : Fin n) : Prop :=
  if T.LeftCut e r then T.RightCut e x else T.LeftCut e x

/-- The endpoint of `e` in its away-from-root component. -/
noncomputable def child (e : T.Edge) : Fin n :=
  if T.LeftCut e r then T.edgeRight e else T.edgeLeft e

/-- The endpoint of `e` in its root component. -/
noncomputable def parent (e : T.Edge) : Fin n :=
  if T.LeftCut e r then T.edgeLeft e else T.edgeRight e

theorem root_not_away (e : T.Edge) : ¬Away T r e r := by
  unfold Away
  by_cases h : T.LeftCut e r
  · simp [h, (T.leftCut_iff_not_rightCut e r).mp h]
  · simp [h]

theorem child_away (e : T.Edge) : Away T r e (child T r e) := by
  unfold Away child
  by_cases h : T.LeftCut e r
  · simp [h, T.edgeRight_mem_RightCut e]
  · simp [h, T.edgeLeft_mem_LeftCut e]

theorem parent_not_away (e : T.Edge) : ¬Away T r e (parent T r e) := by
  unfold Away parent
  by_cases h : T.LeftCut e r
  · simp [h, (T.leftCut_iff_not_rightCut e (T.edgeLeft e)).mp
      (T.edgeLeft_mem_LeftCut e)]
  · have hr : T.RightCut e r := (T.rightCut_iff_not_leftCut e r).2 h
    have hp : ¬T.LeftCut e (T.edgeRight e) :=
      (T.rightCut_iff_not_leftCut e (T.edgeRight e)).mp
        (T.edgeRight_mem_RightCut e)
    simp [h, hp]

theorem parent_child_edge (e : T.Edge) :
    s(parent T r e, child T r e) = e.1 := by
  unfold parent child
  by_cases h : T.LeftCut e r
  · simp [h, T.edge_eq_mk_endpoints e]
  · simp [h, Sym2.eq_swap, T.edge_eq_mk_endpoints e]

theorem parent_adj_child (e : T.Edge) :
    T.graph.Adj (parent T r e) (child T r e) := by
  rw [← SimpleGraph.mem_edgeSet, parent_child_edge]
  exact e.2

theorem away_iff_mem_pathEdges (e : T.Edge) (x : Fin n) :
    Away T r e x ↔ e.1 ∈ T.pathEdges r x := by
  unfold Away
  rw [T.mem_pathEdges_iff_opposite_cuts]
  by_cases h : T.LeftCut e r
  · have hnr : ¬T.RightCut e r := (T.leftCut_iff_not_rightCut e r).mp h
    simp [h, hnr]
  · have hr : T.RightCut e r := (T.rightCut_iff_not_leftCut e r).2 h
    simp [h, hr]

theorem child_mem_root_path_support_of_away (e : T.Edge) {x : Fin n}
    (hx : Away T r e x) : child T r e ∈ (T.path r x).1.support := by
  have hefin := (away_iff_mem_pathEdges T r e x).mp hx
  have he : e.1 ∈ (T.path r x).1.edges := by
    simpa [PosIntTree.pathEdges] using hefin
  rw [← parent_child_edge T r e] at he
  exact (T.path r x).1.snd_mem_support_of_mem_edges he

theorem pathEdges_subset_of_mem_support {x z : Fin n}
    (hz : z ∈ (T.path r x).1.support) :
    T.pathEdges r z ⊆ T.pathEdges r x := by
  let q := (T.path r x).1.takeUntil z hz
  have hqpath : q.IsPath := (T.path r x).2.takeUntil hz
  have hqeq : (⟨q, hqpath⟩ : T.graph.Path r z) = T.path r z := T.path_unique _
  intro e he
  have heq : e ∈ q.edges := by
    have : e ∈ (T.path r z).1.edges := by
      simpa [PosIntTree.pathEdges] using he
    rwa [← congrArg (fun p : T.graph.Path r z ↦ p.1.edges) hqeq] at this
  have := (T.path r x).1.edges_takeUntil_subset hz heq
  simpa [PosIntTree.pathEdges] using this

theorem away_mono_of_child_away (e f : T.Edge)
    (hchild : Away T r e (child T r f)) :
    ∀ x : Fin n, Away T r f x → Away T r e x := by
  intro x hx
  have hc : child T r f ∈ (T.path r x).1.support :=
    child_mem_root_path_support_of_away T r f hx
  have hsub := pathEdges_subset_of_mem_support T r hc
  apply (away_iff_mem_pathEdges T r e x).mpr
  exact hsub ((away_iff_mem_pathEdges T r e (child T r f)).mp hchild)

theorem child_not_mem_parent_path (e : T.Edge) :
    child T r e ∉ (T.path r (parent T r e)).1.support := by
  intro hc
  have hsub := pathEdges_subset_of_mem_support T r hc
  have hechild : e.1 ∈ T.pathEdges r (child T r e) :=
    (away_iff_mem_pathEdges T r e (child T r e)).mp (child_away T r e)
  have heparent := hsub hechild
  exact parent_not_away T r e
    ((away_iff_mem_pathEdges T r e (parent T r e)).mpr heparent)

theorem root_child_path_eq_concat (e : T.Edge) :
    T.path r (child T r e) =
      ⟨(T.path r (parent T r e)).1.concat (parent_adj_child T r e),
        (T.path r (parent T r e)).2.concat (child_not_mem_parent_path T r e)
          (parent_adj_child T r e)⟩ := by
  exact T.path_unique _ |>.symm

theorem child_injective : Function.Injective (child T r) := by
  intro e f hchild
  have heq := congrArg (fun p ↦ p.1.edges) (root_child_path_eq_concat T r e)
  have hfq := congrArg (fun p ↦ p.1.edges) (root_child_path_eq_concat T r f)
  have hcanon : (T.path r (child T r e)).1.edges =
      (T.path r (child T r f)).1.edges := by rw [hchild]
  have hedges :
      (T.path r (parent T r e)).1.edges ++ [e.1] =
        (T.path r (parent T r f)).1.edges ++ [f.1] := by
    calc
      (T.path r (parent T r e)).1.edges ++ [e.1] =
          (T.path r (child T r e)).1.edges := by
        simpa [SimpleGraph.Walk.edges_concat, parent_child_edge T r e] using heq.symm
      _ = (T.path r (child T r f)).1.edges := hcanon
      _ = (T.path r (parent T r f)).1.edges ++ [f.1] := by
        simpa [SimpleGraph.Walk.edges_concat, parent_child_edge T r f] using hfq
  have hlast := congrArg List.getLast? hedges
  have hef : e.1 = f.1 := by
    simpa using hlast
  exact Subtype.ext hef

theorem child_away_of_takeUntil_length_le (e f : T.Edge) {x : Fin n}
    (he : Away T r e x) (hf : Away T r f x)
    (hlen :
      ((T.path r x).1.takeUntil (child T r e)
          (child_mem_root_path_support_of_away T r e he)).length ≤
      ((T.path r x).1.takeUntil (child T r f)
          (child_mem_root_path_support_of_away T r f hf)).length) :
    Away T r e (child T r f) := by
  let P := (T.path r x).1
  let hce : child T r e ∈ P.support :=
    child_mem_root_path_support_of_away T r e he
  let hcf : child T r f ∈ P.support :=
    child_mem_root_path_support_of_away T r f hf
  let qe := P.takeUntil (child T r e) hce
  let qf := P.takeUntil (child T r f) hcf
  have hceAt : P.getVert qe.length = child T r e := by
    exact P.getVert_length_takeUntil hce
  have hqfAt : qf.getVert qe.length = P.getVert qe.length := by
    exact P.getVert_takeUntil hcf hlen
  have hceqf : child T r e ∈ qf.support := by
    rw [← hceAt, ← hqfAt]
    exact qf.getVert_mem_support qe.length
  have hqfpath : qf.IsPath := (T.path r x).2.takeUntil hcf
  have hqfeq : (⟨qf, hqfpath⟩ : T.graph.Path r (child T r f)) =
      T.path r (child T r f) := T.path_unique _
  have hcecanon : child T r e ∈ (T.path r (child T r f)).1.support := by
    rw [← congrArg (fun p ↦ p.1.support) hqfeq]
    exact hceqf
  have hsub := pathEdges_subset_of_mem_support T r hcecanon
  apply (away_iff_mem_pathEdges T r e (child T r f)).mpr
  exact hsub ((away_iff_mem_pathEdges T r e (child T r e)).mp (child_away T r e))

theorem child_away_comparable_of_common (e f : T.Edge) {x : Fin n}
    (he : Away T r e x) (hf : Away T r f x) :
    Away T r e (child T r f) ∨ Away T r f (child T r e) := by
  let le := ((T.path r x).1.takeUntil (child T r e)
    (child_mem_root_path_support_of_away T r e he)).length
  let lf := ((T.path r x).1.takeUntil (child T r f)
    (child_mem_root_path_support_of_away T r f hf)).length
  rcases Nat.le_total le lf with h | h
  · exact Or.inl (child_away_of_takeUntil_length_le T r e f he hf h)
  · exact Or.inr (child_away_of_takeUntil_length_le T r f e hf he h)

theorem away_laminar (e f : T.Edge) :
    (∀ x, Away T r e x → Away T r f x) ∨
    (∀ x, Away T r f x → Away T r e x) ∨
    (∀ x, ¬(Away T r e x ∧ Away T r f x)) := by
  by_cases hcommon : ∃ x, Away T r e x ∧ Away T r f x
  · obtain ⟨x, he, hf⟩ := hcommon
    rcases child_away_comparable_of_common T r e f he hf with hef | hfe
    · exact Or.inr (Or.inl (away_mono_of_child_away T r e f hef))
    · exact Or.inl (away_mono_of_child_away T r f e hfe)
  · right
    right
    push_neg at hcommon
    intro x hx
    exact hcommon x hx.1 hx.2

noncomputable instance awayFintype (e : T.Edge) :
    Fintype {x : Fin n // Away T r e x} := Fintype.ofFinite _

theorem away_card (e : T.Edge) :
    Fintype.card {x : Fin n // Away T r e x} =
      if T.LeftCut e r then n - T.cutSize e else T.cutSize e := by
  classical
  by_cases h : T.LeftCut e r
  · simp only [Away, if_pos h]
    exact T.rightVertex_card e
  · simp only [Away, if_neg h]
    rfl

theorem selected_away_card_ge {k : ℕ} (e : T.Edge)
    (hsel : k ≤ min (T.cutSize e) (n - T.cutSize e)) :
    k ≤ Fintype.card {x : Fin n // Away T r e x} := by
  rw [away_card]
  have hleft : k ≤ T.cutSize e := hsel.trans (Nat.min_le_left _ _)
  have hright : k ≤ n - T.cutSize e := hsel.trans (Nat.min_le_right _ _)
  split <;> assumption

theorem selected_away_card_le_sub {k : ℕ} (e : T.Edge)
    (hsel : k ≤ min (T.cutSize e) (n - T.cutSize e)) :
    Fintype.card {x : Fin n // Away T r e x} ≤ n - k := by
  rw [away_card]
  have hleft : k ≤ T.cutSize e := hsel.trans (Nat.min_le_left _ _)
  have hright : k ≤ n - T.cutSize e := hsel.trans (Nat.min_le_right _ _)
  have hu := T.cutSize_lt_order e
  split <;> omega

noncomputable def depth (e : T.Edge) : ℕ := (T.path r (child T r e)).1.length

theorem depth_lt_of_child_away_of_ne (e f : T.Edge)
    (haway : Away T r e (child T r f)) (hne : e ≠ f) :
    depth T r e < depth T r f := by
  let P := (T.path r (child T r f)).1
  have hc : child T r e ∈ P.support :=
    child_mem_root_path_support_of_away T r e haway
  let q := P.takeUntil (child T r e) hc
  have hqpath : q.IsPath := (T.path r (child T r f)).2.takeUntil hc
  have hqeq : (⟨q, hqpath⟩ : T.graph.Path r (child T r e)) =
      T.path r (child T r e) := T.path_unique _
  have hchildren : child T r e ≠ child T r f := by
    intro h
    exact hne (child_injective T r h)
  have hlt : q.length < P.length := P.length_takeUntil_lt hc hchildren
  have hlen : q.length = depth T r e := by
    exact congrArg (fun p ↦ p.1.length) hqeq
  simpa [depth, P, hlen] using hlt

end RootedCut

end LeechTrees.QHop
