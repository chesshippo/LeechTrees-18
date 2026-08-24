import LeechTrees.QHop.CoreBound

open scoped BigOperators

namespace LeechTrees.QHop

open LeechTrees.Foundation
open SimpleGraph

namespace RootedCut

variable {n : ℕ} (T : PosIntTree n) (r : Fin n)

noncomputable def awayVertices (e : T.Edge) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (Away T r e)

@[simp] theorem mem_awayVertices (e : T.Edge) (x : Fin n) :
    x ∈ awayVertices T r e ↔ Away T r e x := by
  simp [awayVertices]

theorem card_awayVertices (e : T.Edge) :
    (awayVertices T r e).card = Fintype.card {x : Fin n // Away T r e x} := by
  classical
  simpa [awayVertices] using (Fintype.card_subtype (Away T r e)).symm

theorem awayVertices_subset_iff (e f : T.Edge) :
    awayVertices T r e ⊆ awayVertices T r f ↔
      ∀ x, Away T r e x → Away T r f x := by
  simp only [Finset.subset_iff, mem_awayVertices]

theorem awayVertices_disjoint_iff (e f : T.Edge) :
    Disjoint (awayVertices T r e) (awayVertices T r f) ↔
      ∀ x, ¬(Away T r e x ∧ Away T r f x) := by
  rw [Finset.disjoint_left]
  simp only [mem_awayVertices]
  tauto

theorem awayVertices_laminar (e f : T.Edge) :
    awayVertices T r e ⊆ awayVertices T r f ∨
    awayVertices T r f ⊆ awayVertices T r e ∨
    Disjoint (awayVertices T r e) (awayVertices T r f) := by
  rcases away_laminar T r e f with h | h | h
  · exact Or.inl ((awayVertices_subset_iff T r e f).2 h)
  · exact Or.inr (Or.inl ((awayVertices_subset_iff T r f e).2 h))
  · exact Or.inr (Or.inr ((awayVertices_disjoint_iff T r e f).2 h))

theorem pathEdges_parent_child (e : T.Edge) :
    T.pathEdges (parent T r e) (child T r e) = {e.1} := by
  have hp : SimpleGraph.Path.singleton (parent_adj_child T r e) =
      T.path (parent T r e) (child T r e) := T.path_unique _
  rw [PosIntTree.pathEdges, ← hp]
  simp [SimpleGraph.Path.singleton, parent_child_edge T r e]

theorem edge_eq_of_away_child_not_parent (e f : T.Edge)
    (hc : Away T r e (child T r f))
    (hp : ¬Away T r e (parent T r f)) : e = f := by
  have hemem : e.1 ∈ T.pathEdges (parent T r f) (child T r f) := by
    rw [T.mem_pathEdges_iff_opposite_cuts]
    unfold Away at hc hp
    by_cases hroot : T.LeftCut e r
    · rw [if_pos hroot] at hc hp
      have hparent : T.LeftCut e (parent T r f) :=
        (T.leftCut_iff_not_rightCut e (parent T r f)).2 hp
      exact Or.inl ⟨hparent, hc⟩
    · rw [if_neg hroot] at hc hp
      have hparent : T.RightCut e (parent T r f) :=
        (T.rightCut_iff_not_leftCut e (parent T r f)).2 hp
      exact Or.inr ⟨hparent, hc⟩
  rw [pathEdges_parent_child T r f] at hemem
  exact Subtype.ext (Finset.mem_singleton.mp hemem)

theorem edge_eq_of_awayVertices_eq (e f : T.Edge)
    (h : awayVertices T r e = awayVertices T r f) : e = f := by
  apply edge_eq_of_away_child_not_parent T r e f
  · have : child T r f ∈ awayVertices T r f := by
      exact (mem_awayVertices T r f _).2 (child_away T r f)
    rw [← h] at this
    exact (mem_awayVertices T r e _).1 this
  · intro hp
    have : parent T r f ∈ awayVertices T r e :=
      (mem_awayVertices T r e _).2 hp
    rw [h] at this
    exact parent_not_away T r f ((mem_awayVertices T r f _).1 this)

noncomputable def selectedEdges (k : ℕ) : Finset T.Edge := by
  classical
  exact Finset.univ.filter
    (fun e : T.Edge => k ≤ min (T.cutSize e) (n - T.cutSize e))

@[simp] theorem mem_selectedEdges (k : ℕ) (e : T.Edge) :
    e ∈ selectedEdges T k ↔
      k ≤ min (T.cutSize e) (n - T.cutSize e) := by
  simp [selectedEdges]

noncomputable def childVertices (C : Finset T.Edge) : Finset (Fin n) := by
  classical
  exact C.image (child T r)

theorem card_childVertices (C : Finset T.Edge) :
    (childVertices T r C).card = C.card := by
  classical
  exact Finset.card_image_of_injective C (child_injective T r)

theorem root_not_mem_childVertices (C : Finset T.Edge) :
    r ∉ childVertices T r C := by
  classical
  intro hr
  obtain ⟨e, he, hchild⟩ := Finset.mem_image.mp hr
  have haway := child_away T r e
  rw [hchild] at haway
  exact root_not_away T r e haway

theorem reserve_disjoint_childVertices_of_depth_max
    (C : Finset T.Edge) (e : T.Edge)
    (hmax : ∀ f ∈ C, depth T r f ≤ depth T r e) :
    Disjoint (childVertices T r C)
      ((awayVertices T r e).erase (child T r e)) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxI hxR
  obtain ⟨f, hf, hfx⟩ := Finset.mem_image.mp hxI
  have hxA : x ∈ awayVertices T r e := Finset.mem_of_mem_erase hxR
  have haway : Away T r e (child T r f) := by
    rw [hfx]
    exact (mem_awayVertices T r e x).1 hxA
  have hne : e ≠ f := by
    intro hef
    subst f
    exact (Finset.ne_of_mem_erase hxR) hfx.symm
  have hlt := depth_lt_of_child_away_of_ne T r e f haway hne
  exact (Nat.not_lt_of_ge (hmax f hf)) hlt

theorem card_reserve_ge_pred {k : ℕ} (e : T.Edge)
    (hsel : k ≤ min (T.cutSize e) (n - T.cutSize e)) :
    k - 1 ≤ ((awayVertices T r e).erase (child T r e)).card := by
  have hchild : child T r e ∈ awayVertices T r e :=
    (mem_awayVertices T r e _).2 (child_away T r e)
  have hcard := selected_away_card_ge T r e hsel
  rw [← card_awayVertices T r e] at hcard
  rw [Finset.card_erase_of_mem hchild]
  omega

end RootedCut

open RootedCut

/-- The exact tree-level core count needed by the order-18 T6 adapter.
The proof is purely structural and includes the empty selected-core case. -/
theorem order18_core_count_add (T : PosIntTree 18) (k : ℕ)
    (hk : 1 ≤ k) (hk9 : k ≤ 9) :
    (Finset.univ.filter
        (fun e : T.Edge => k ≤ min (T.cutSize e) (18 - T.cutSize e))).card +
      2 * k ≤ 19 := by
  classical
  change (selectedEdges T k).card + 2 * k ≤ 19
  let r : Fin 18 := 0
  let C : Finset T.Edge := selectedEdges T k
  let I : Finset (Fin 18) := childVertices T r C
  change C.card + 2 * k ≤ 19
  by_cases hCempty : C = ∅
  · rw [hCempty]
    simp
    omega
  have hCne : C.Nonempty := Finset.nonempty_iff_ne_empty.mpr hCempty
  obtain ⟨e, heC, heMax⟩ :=
    Finset.exists_max_image C (depth T r) hCne
  let Ae : Finset (Fin 18) := awayVertices T r e
  let Re : Finset (Fin 18) := Ae.erase (child T r e)
  have heSel : k ≤ min (T.cutSize e) (18 - T.cutSize e) := by
    exact (mem_selectedEdges T k e).1 heC
  have hReGe : k - 1 ≤ Re.card := by
    simpa [Re, Ae] using card_reserve_ge_pred T r e heSel
  have hIe : Disjoint I Re := by
    simpa [I, Re, Ae] using
      reserve_disjoint_childVertices_of_depth_max T r C e heMax
  have hIcard : I.card = C.card := by
    simpa [I] using card_childVertices T r C
  by_cases hbranch :
      ∃ f ∈ C, Disjoint Ae (awayVertices T r f)
  · let D : Finset T.Edge :=
      C.filter (fun f => Disjoint Ae (awayVertices T r f))
    have hDne : D.Nonempty := by
      obtain ⟨f, hfC, hfDisj⟩ := hbranch
      exact ⟨f, by simp [D, hfC, hfDisj]⟩
    obtain ⟨f, hfD, hfMax⟩ :=
      Finset.exists_max_image D (depth T r) hDne
    have hfC : f ∈ C := (Finset.mem_filter.mp hfD).1
    have hefDisj : Disjoint Ae (awayVertices T r f) :=
      (Finset.mem_filter.mp hfD).2
    let Af : Finset (Fin 18) := awayVertices T r f
    let Rf : Finset (Fin 18) := Af.erase (child T r f)
    have hfSel : k ≤ min (T.cutSize f) (18 - T.cutSize f) := by
      exact (mem_selectedEdges T k f).1 hfC
    have hRfGe : k - 1 ≤ Rf.card := by
      simpa [Rf, Af] using card_reserve_ge_pred T r f hfSel
    have hIf : Disjoint I Rf := by
      rw [Finset.disjoint_left]
      intro x hxI hxRf
      obtain ⟨g, hgC, hgx⟩ := Finset.mem_image.mp hxI
      have hxAf : x ∈ Af := Finset.mem_of_mem_erase hxRf
      have hfgAway : Away T r f (child T r g) := by
        rw [hgx]
        exact (mem_awayVertices T r f x).1 (by simpa [Af] using hxAf)
      have hAgAf : awayVertices T r g ⊆ Af := by
        have hmono := away_mono_of_child_away T r f g hfgAway
        simpa [Af] using (awayVertices_subset_iff T r g f).2 hmono
      have hegDisj : Disjoint Ae (awayVertices T r g) := by
        exact Finset.disjoint_of_subset_right hAgAf (by simpa [Af] using hefDisj)
      have hgD : g ∈ D := by
        simp [D, hgC, hegDisj]
      have hne : f ≠ g := by
        intro hfg
        subst g
        exact (Finset.ne_of_mem_erase hxRf) hgx.symm
      have hlt := depth_lt_of_child_away_of_ne T r f g hfgAway hne
      exact (Nat.not_lt_of_ge (hfMax g hgD)) hlt
    have hReRf : Disjoint Re Rf := by
      have h0 : Disjoint Re Af :=
        Finset.disjoint_of_subset_left (by simpa [Re, Ae] using Finset.erase_subset (child T r e) Ae)
          (by simpa [Af] using hefDisj)
      exact Finset.disjoint_of_subset_right
        (by simpa [Rf] using Finset.erase_subset (child T r f) Af) h0
    have hrRe : r ∉ Re := by
      intro hr
      have hrAe : r ∈ Ae := Finset.mem_of_mem_erase hr
      exact root_not_away T r e
        ((mem_awayVertices T r e r).1 (by simpa [Ae] using hrAe))
    have hrRf : r ∉ Rf := by
      intro hr
      have hrAf : r ∈ Af := Finset.mem_of_mem_erase hr
      exact root_not_away T r f
        ((mem_awayVertices T r f r).1 (by simpa [Af] using hrAf))
    have hRroot : Disjoint (Re ∪ Rf) ({r} : Finset (Fin 18)) := by
      rw [Finset.disjoint_singleton_right]
      simp [hrRe, hrRf]
    have hIroot : Disjoint I ({r} : Finset (Fin 18)) := by
      rw [Finset.disjoint_singleton_right]
      simpa [I] using root_not_mem_childVertices T r C
    let R : Finset (Fin 18) := (Re ∪ Rf) ∪ {r}
    have hIR : Disjoint I R := by
      rw [show R = (Re ∪ Rf) ∪ {r} by rfl,
        Finset.disjoint_union_right, Finset.disjoint_union_right]
      exact ⟨⟨hIe, hIf⟩, hIroot⟩
    have hRcard : R.card = Re.card + Rf.card + 1 := by
      rw [show R = (Re ∪ Rf) ∪ {r} by rfl,
        Finset.card_union_of_disjoint hRroot,
        Finset.card_union_of_disjoint hReRf]
      simp
    have htotal : I.card + R.card ≤ 18 := by
      have h := Finset.card_le_univ (I ∪ R)
      rw [Finset.card_union_of_disjoint hIR] at h
      simpa using h
    omega
  · have heSub : ∀ g ∈ C, Ae ⊆ awayVertices T r g := by
      intro g hgC
      rcases awayVertices_laminar T r e g with heg | hge | hdisj
      · simpa [Ae] using heg
      · by_cases hsame : g = e
        · subst g
          exact Finset.Subset.rfl
        · have hchildg : child T r g ∈ awayVertices T r g :=
            (mem_awayVertices T r g _).2 (child_away T r g)
          have haway : Away T r e (child T r g) := by
            exact (mem_awayVertices T r e _).1 (hge hchildg)
          have hlt := depth_lt_of_child_away_of_ne T r e g haway (Ne.symm hsame)
          exact (Nat.not_lt_of_ge (heMax g hgC) hlt).elim
      · exact (hbranch ⟨g, hgC, by simpa [Ae] using hdisj⟩).elim
    obtain ⟨a, haC, haMin⟩ :=
      Finset.exists_min_image C (depth T r) hCne
    let Aa : Finset (Fin 18) := awayVertices T r a
    have hAllSub : ∀ g ∈ C, awayVertices T r g ⊆ Aa := by
      intro g hgC
      rcases awayVertices_laminar T r a g with hag | hga | hdisj
      · by_cases hsame : a = g
        · subst g
          exact Finset.Subset.rfl
        · have hchilda : child T r a ∈ awayVertices T r a :=
            (mem_awayVertices T r a _).2 (child_away T r a)
          have haway : Away T r g (child T r a) := by
            exact (mem_awayVertices T r g _).1 (hag hchilda)
          have hlt := depth_lt_of_child_away_of_ne T r g a haway (Ne.symm hsame)
          exact (Nat.not_lt_of_ge (haMin g hgC) hlt).elim
      · simpa [Aa] using hga
      · have hchilde : child T r e ∈ Ae := by
          exact (mem_awayVertices T r e _).2 (child_away T r e)
        have hea : Ae ⊆ awayVertices T r a := heSub a haC
        have heg : Ae ⊆ awayVertices T r g := heSub g hgC
        exact (Finset.disjoint_left.mp hdisj (hea hchilde)) (heg hchilde) |>.elim
    have hAeAa : Ae ⊆ Aa := by
      simpa [Aa] using heSub a haC
    have hISub : I ⊆ Aa := by
      intro x hxI
      obtain ⟨g, hgC, hgx⟩ := Finset.mem_image.mp hxI
      rw [← hgx]
      exact hAllSub g hgC
        ((mem_awayVertices T r g _).2 (child_away T r g))
    let Ba : Finset (Fin 18) := Aaᶜ
    have hIBa : Disjoint I Ba := by
      rw [Finset.disjoint_left]
      intro x hxI hxBa
      have hxAa : x ∈ Aa := hISub hxI
      have hxNot : x ∉ Aa := by simpa [Ba] using hxBa
      exact hxNot hxAa
    have hReBa : Disjoint Re Ba := by
      rw [Finset.disjoint_left]
      intro x hxRe hxBa
      have hxAe : x ∈ Ae := Finset.mem_of_mem_erase hxRe
      have hxAa : x ∈ Aa := hAeAa hxAe
      have hxNot : x ∉ Aa := by simpa [Ba] using hxBa
      exact hxNot hxAa
    have haSel : k ≤ min (T.cutSize a) (18 - T.cutSize a) :=
      (mem_selectedEdges T k a).1 haC
    have haUpper : Aa.card ≤ 18 - k := by
      have h := selected_away_card_le_sub T r a haSel
      rw [← card_awayVertices T r a] at h
      simpa [Aa] using h
    have hBaCard : Ba.card = 18 - Aa.card := by
      simpa [Ba] using Finset.card_compl Aa
    have hBaGe : k ≤ Ba.card := by omega
    let R : Finset (Fin 18) := Re ∪ Ba
    have hIR : Disjoint I R := by
      rw [show R = Re ∪ Ba by rfl, Finset.disjoint_union_right]
      exact ⟨hIe, hIBa⟩
    have hRcard : R.card = Re.card + Ba.card := by
      rw [show R = Re ∪ Ba by rfl,
        Finset.card_union_of_disjoint hReBa]
    have htotal : I.card + R.card ≤ 18 := by
      have h := Finset.card_le_univ (I ∪ R)
      rw [Finset.card_union_of_disjoint hIR] at h
      simpa using h
    omega

end LeechTrees.QHop
