import LeechTrees.Foundations

open scoped BigOperators

namespace LeechTrees.OddEdges.T12Adapter.CutLemma

open LeechTrees.Foundation

variable {n : ℕ} (T : PosIntTree n)

private theorem rootMem_iff_leftCut_xor (e : T.Edge) (r v : Fin n) :
    e.1 ∈ T.pathEdges r v ↔
      (T.LeftCut e r ∧ ¬ T.LeftCut e v) ∨
      (¬ T.LeftCut e r ∧ T.LeftCut e v) := by
  rw [T.mem_pathEdges_iff_opposite_cuts e r v]
  rw [T.rightCut_iff_not_leftCut e r,
    T.rightCut_iff_not_leftCut e v]

private theorem path_support_cut_reachable (e : T.Edge) {u v w : Fin n}
    (huv : (T.cutGraph e).Reachable u v)
    (hw : w ∈ (T.path u v).1.support) :
    (T.cutGraph e).Reachable u w := by
  classical
  have hefin : e.1 ∉ T.pathEdges u v :=
    (T.cut_reachable_iff_not_mem_pathEdges e u v).1 huv
  have hewalk : e.1 ∉ (T.path u v).1.edges := by
    simpa [PosIntTree.pathEdges] using hefin
  let before := (T.path u v).1.takeUntil w hw
  have hbefore : e.1 ∉ before.edges := by
    intro he
    exact hewalk ((T.path u v).1.edges_takeUntil_subset hw he)
  exact ⟨before.toDeleteEdge e.1 hbefore⟩

private theorem LeftCut_of_mem_path_support (e : T.Edge) {u v w : Fin n}
    (hu : T.LeftCut e u) (hv : T.LeftCut e v)
    (hw : w ∈ (T.path u v).1.support) :
    T.LeftCut e w := by
  unfold PosIntTree.LeftCut at hu hv ⊢
  have huv : (T.cutGraph e).Reachable u v := hu.trans hv.symm
  have huw := path_support_cut_reachable T e huv hw
  exact huw.symm.trans hu

private theorem RightCut_of_mem_path_support (e : T.Edge) {u v w : Fin n}
    (hu : T.RightCut e u) (hv : T.RightCut e v)
    (hw : w ∈ (T.path u v).1.support) :
    T.RightCut e w := by
  unfold PosIntTree.RightCut at hu hv ⊢
  have huv : (T.cutGraph e).Reachable u v := hu.trans hv.symm
  have huw := path_support_cut_reachable T e huv hw
  exact huw.symm.trans hu

private theorem distinct_edge_endpoints_same_cut (e f : T.Edge) (hef : e ≠ f) :
    (T.LeftCut e (T.edgeLeft f) ∧ T.LeftCut e (T.edgeRight f)) ∨
    (T.RightCut e (T.edgeLeft f) ∧ T.RightCut e (T.edgeRight f)) := by
  have hefval : e.1 ≠ f.1 := fun h => hef (Subtype.ext h)
  have havoid : e.1 ∉ T.pathEdges (T.edgeLeft f) (T.edgeRight f) := by
    rw [T.pathEdges_edge f]
    simpa using hefval
  have hreach : (T.cutGraph e).Reachable (T.edgeLeft f) (T.edgeRight f) :=
    (T.cut_reachable_iff_not_mem_pathEdges e _ _).2 havoid
  rcases T.cut_cover e (T.edgeLeft f) with hl | hr
  · left
    exact ⟨hl, hreach.symm.trans hl⟩
  · right
    exact ⟨hr, hreach.symm.trans hr⟩

/-- For two distinct edges, at least one of the four intersections of their
two deletion cuts is empty. -/
theorem one_of_four_cut_cells_empty (e f : T.Edge) (hef : e ≠ f) :
    (∀ v, ¬(T.LeftCut e v ∧ T.LeftCut f v)) ∨
    (∀ v, ¬(T.LeftCut e v ∧ T.RightCut f v)) ∨
    (∀ v, ¬(T.RightCut e v ∧ T.LeftCut f v)) ∨
    (∀ v, ¬(T.RightCut e v ∧ T.RightCut f v)) := by
  classical
  rcases distinct_edge_endpoints_same_cut T e f hef with hfl | hfr
  · by_cases hRL : ∃ v, T.RightCut e v ∧ T.LeftCut f v
    · by_cases hRR : ∃ v, T.RightCut e v ∧ T.RightCut f v
      · rcases hRL with ⟨u, huE, huF⟩
        rcases hRR with ⟨v, hvE, hvF⟩
        have hfpath : f.1 ∈ T.pathEdges u v :=
          (T.mem_pathEdges_iff_opposite_cuts f u v).2 (Or.inl ⟨huF, hvF⟩)
        have hflist : f.1 ∈ (T.path u v).1.edges := by
          simpa [PosIntTree.pathEdges] using hfpath
        have hleftSupport : T.edgeLeft f ∈ (T.path u v).1.support := by
          rw [T.edge_eq_mk_endpoints f] at hflist
          exact (T.path u v).1.fst_mem_support_of_mem_edges hflist
        have hrightAtLeft : T.RightCut e (T.edgeLeft f) :=
          RightCut_of_mem_path_support T e huE hvE hleftSupport
        exact (T.LeftCut_disjoint_RightCut e (T.edgeLeft f)
          ⟨hfl.1, hrightAtLeft⟩).elim
      · exact Or.inr (Or.inr (Or.inr (by simpa only [not_exists] using hRR)))
    · exact Or.inr (Or.inr (Or.inl (by simpa only [not_exists] using hRL)))
  · by_cases hLL : ∃ v, T.LeftCut e v ∧ T.LeftCut f v
    · by_cases hLR : ∃ v, T.LeftCut e v ∧ T.RightCut f v
      · rcases hLL with ⟨u, huE, huF⟩
        rcases hLR with ⟨v, hvE, hvF⟩
        have hfpath : f.1 ∈ T.pathEdges u v :=
          (T.mem_pathEdges_iff_opposite_cuts f u v).2 (Or.inl ⟨huF, hvF⟩)
        have hflist : f.1 ∈ (T.path u v).1.edges := by
          simpa [PosIntTree.pathEdges] using hfpath
        have hleftSupport : T.edgeLeft f ∈ (T.path u v).1.support := by
          rw [T.edge_eq_mk_endpoints f] at hflist
          exact (T.path u v).1.fst_mem_support_of_mem_edges hflist
        have hleftAtLeft : T.LeftCut e (T.edgeLeft f) :=
          LeftCut_of_mem_path_support T e huE hvE hleftSupport
        exact (T.LeftCut_disjoint_RightCut e (T.edgeLeft f)
          ⟨hleftAtLeft, hfr.1⟩).elim
      · exact Or.inr (Or.inl (by simpa only [not_exists] using hLR))
    · exact Or.inl (by simpa only [not_exists] using hLL)

/-- Rooted descendant sets of distinct tree edges are laminar: among the
three cells `e only`, `f only`, and `both`, at least one is empty.  Here
membership means membership in the unique path from the fixed root. -/
theorem one_of_three_root_path_cells_empty (e f : T.Edge) (hef : e ≠ f)
    (r : Fin n) :
    (∀ v, ¬(e.1 ∈ T.pathEdges r v ∧ f.1 ∉ T.pathEdges r v)) ∨
    (∀ v, ¬(e.1 ∉ T.pathEdges r v ∧ f.1 ∈ T.pathEdges r v)) ∨
    (∀ v, ¬(e.1 ∈ T.pathEdges r v ∧ f.1 ∈ T.pathEdges r v)) := by
  classical
  rcases T.cut_cover e r with her | her <;>
    rcases T.cut_cover f r with hfr | hfr
  · have heMem : ∀ v, e.1 ∈ T.pathEdges r v ↔ T.RightCut e v := by
      intro v
      rw [rootMem_iff_leftCut_xor T e r v,
        T.rightCut_iff_not_leftCut e v]
      simp [her]
    have heNot : ∀ v, e.1 ∉ T.pathEdges r v ↔ T.LeftCut e v := by
      intro v
      rw [not_congr (heMem v), T.leftCut_iff_not_rightCut e v]
    have hfMem : ∀ v, f.1 ∈ T.pathEdges r v ↔ T.RightCut f v := by
      intro v
      rw [rootMem_iff_leftCut_xor T f r v,
        T.rightCut_iff_not_leftCut f v]
      simp [hfr]
    have hfNot : ∀ v, f.1 ∉ T.pathEdges r v ↔ T.LeftCut f v := by
      intro v
      rw [not_congr (hfMem v), T.leftCut_iff_not_rightCut f v]
    rcases one_of_four_cut_cells_empty T e f hef with hLL | hLR | hRL | hRR
    · exact (hLL r ⟨her, hfr⟩).elim
    · exact Or.inr (Or.inl (fun v h => hLR v ⟨(heNot v).1 h.1, (hfMem v).1 h.2⟩))
    · exact Or.inl (fun v h => hRL v ⟨(heMem v).1 h.1, (hfNot v).1 h.2⟩)
    · exact Or.inr (Or.inr (fun v h => hRR v ⟨(heMem v).1 h.1, (hfMem v).1 h.2⟩))
  · have hnfr : ¬T.LeftCut f r := (T.rightCut_iff_not_leftCut f r).1 hfr
    have heMem : ∀ v, e.1 ∈ T.pathEdges r v ↔ T.RightCut e v := by
      intro v
      rw [rootMem_iff_leftCut_xor T e r v,
        T.rightCut_iff_not_leftCut e v]
      simp [her]
    have heNot : ∀ v, e.1 ∉ T.pathEdges r v ↔ T.LeftCut e v := by
      intro v
      rw [not_congr (heMem v), T.leftCut_iff_not_rightCut e v]
    have hfMem : ∀ v, f.1 ∈ T.pathEdges r v ↔ T.LeftCut f v := by
      intro v
      rw [rootMem_iff_leftCut_xor T f r v]
      simp [hnfr]
    have hfNot : ∀ v, f.1 ∉ T.pathEdges r v ↔ T.RightCut f v := by
      intro v
      rw [not_congr (hfMem v), T.rightCut_iff_not_leftCut f v]
    rcases one_of_four_cut_cells_empty T e f hef with hLL | hLR | hRL | hRR
    · exact Or.inr (Or.inl (fun v h => hLL v ⟨(heNot v).1 h.1, (hfMem v).1 h.2⟩))
    · exact (hLR r ⟨her, hfr⟩).elim
    · exact Or.inr (Or.inr (fun v h => hRL v ⟨(heMem v).1 h.1, (hfMem v).1 h.2⟩))
    · exact Or.inl (fun v h => hRR v ⟨(heMem v).1 h.1, (hfNot v).1 h.2⟩)
  · have hner : ¬T.LeftCut e r := (T.rightCut_iff_not_leftCut e r).1 her
    have heMem : ∀ v, e.1 ∈ T.pathEdges r v ↔ T.LeftCut e v := by
      intro v
      rw [rootMem_iff_leftCut_xor T e r v]
      simp [hner]
    have heNot : ∀ v, e.1 ∉ T.pathEdges r v ↔ T.RightCut e v := by
      intro v
      rw [not_congr (heMem v), T.rightCut_iff_not_leftCut e v]
    have hfMem : ∀ v, f.1 ∈ T.pathEdges r v ↔ T.RightCut f v := by
      intro v
      rw [rootMem_iff_leftCut_xor T f r v,
        T.rightCut_iff_not_leftCut f v]
      simp [hfr]
    have hfNot : ∀ v, f.1 ∉ T.pathEdges r v ↔ T.LeftCut f v := by
      intro v
      rw [not_congr (hfMem v), T.leftCut_iff_not_rightCut f v]
    rcases one_of_four_cut_cells_empty T e f hef with hLL | hLR | hRL | hRR
    · exact Or.inl (fun v h => hLL v ⟨(heMem v).1 h.1, (hfNot v).1 h.2⟩)
    · exact Or.inr (Or.inr (fun v h => hLR v ⟨(heMem v).1 h.1, (hfMem v).1 h.2⟩))
    · exact (hRL r ⟨her, hfr⟩).elim
    · exact Or.inr (Or.inl (fun v h => hRR v ⟨(heNot v).1 h.1, (hfMem v).1 h.2⟩))
  · have hner : ¬T.LeftCut e r := (T.rightCut_iff_not_leftCut e r).1 her
    have hnfr : ¬T.LeftCut f r := (T.rightCut_iff_not_leftCut f r).1 hfr
    have heMem : ∀ v, e.1 ∈ T.pathEdges r v ↔ T.LeftCut e v := by
      intro v
      rw [rootMem_iff_leftCut_xor T e r v]
      simp [hner]
    have heNot : ∀ v, e.1 ∉ T.pathEdges r v ↔ T.RightCut e v := by
      intro v
      rw [not_congr (heMem v), T.rightCut_iff_not_leftCut e v]
    have hfMem : ∀ v, f.1 ∈ T.pathEdges r v ↔ T.LeftCut f v := by
      intro v
      rw [rootMem_iff_leftCut_xor T f r v]
      simp [hnfr]
    have hfNot : ∀ v, f.1 ∉ T.pathEdges r v ↔ T.RightCut f v := by
      intro v
      rw [not_congr (hfMem v), T.rightCut_iff_not_leftCut f v]
    rcases one_of_four_cut_cells_empty T e f hef with hLL | hLR | hRL | hRR
    · exact Or.inr (Or.inr (fun v h => hLL v ⟨(heMem v).1 h.1, (hfMem v).1 h.2⟩))
    · exact Or.inl (fun v h => hLR v ⟨(heMem v).1 h.1, (hfNot v).1 h.2⟩)
    · exact Or.inr (Or.inl (fun v h => hRL v ⟨(heNot v).1 h.1, (hfMem v).1 h.2⟩))
    · exact (hRR r ⟨her, hfr⟩).elim

end LeechTrees.OddEdges.T12Adapter.CutLemma
