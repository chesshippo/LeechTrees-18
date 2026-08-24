import LeechTrees.Expanded.Q2Bounds.Q2Bounds
import Mathlib.Algebra.Polynomial.Div

/-!
# Actual quotient profiles for the q₂ bounds

This module closes the profile hypotheses left visible in `Q2Bounds`.
Everything is computed from the actual even components of an `IsLeech` tree:
root parity partitions the components, the quotient-tree edge count supplies
`r+1` components, and a concentration inequality bounds the internal pairs.
-/

open scoped BigOperators Polynomial

namespace LeechTrees.OddQuotient.Q2Bounds.GraphProfiles

open LeechTrees.Foundation

variable {n : ℕ}

/-! ## Finite concentration and exact internal-pair cardinality -/

private theorem two_mul_choose_two (m : ℕ) :
    2 * Nat.choose m 2 = m * (m - 1) := by
  rw [Nat.choose_two_right]
  apply Nat.mul_div_cancel'
  by_cases hm : Even m
  · rcases hm with ⟨q, hq⟩
    exact ⟨q * (m - 1), by rw [hq]; ring⟩
  · rcases Nat.not_even_iff_odd.mp hm with ⟨q, hq⟩
    have hmpos : 0 < m := by omega
    have hm1 : m - 1 = q + q := by omega
    refine ⟨m * q, ?_⟩
    rw [hm1]
    ring

/-- Among positive component sizes with fixed total, the number of internal
pairs is maximized by concentrating every excess vertex in one component. -/
theorem sum_choose_two_le_concentrated
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) (hpos : ∀ i, 0 < m i) :
    (∑ i, Nat.choose (m i) 2) ≤
      Nat.choose ((∑ i, m i) - Fintype.card ι + 1) 2 := by
  classical
  let y : ι → ℕ := fun i => m i - 1
  let Y : ℕ := ∑ i, y i
  have hmy (i : ι) : m i = y i + 1 := by
    dsimp [y]
    exact (Nat.sub_add_cancel (hpos i)).symm
  have hsum : (∑ i, m i) = Y + Fintype.card ι := by
    simp_rw [hmy]
    simp [Y, Finset.sum_add_distrib]
  have hsquares : (∑ i, y i ^ 2) ≤ Y ^ 2 := by
    simpa [Y] using
      (Finset.sum_sq_le_sq_sum_of_nonneg
        (s := (Finset.univ : Finset ι))
        (f := y) (fun _ _ => Nat.zero_le _))
  have hdouble :
      2 * (∑ i, Nat.choose (m i) 2) =
        (∑ i, (y i ^ 2 + y i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [two_mul_choose_two, hmy]
    simp only [Nat.add_sub_cancel]
    ring
  have htarget :
      2 * Nat.choose ((∑ i, m i) - Fintype.card ι + 1) 2 =
        Y ^ 2 + Y := by
    have harg : (∑ i, m i) - Fintype.card ι + 1 = Y + 1 := by omega
    rw [harg, two_mul_choose_two]
    simp only [Nat.add_sub_cancel]
    ring
  have hlinear : (∑ i, y i) = Y := rfl
  have htwice :
      2 * (∑ i, Nat.choose (m i) 2) ≤
        2 * Nat.choose ((∑ i, m i) - Fintype.card ι + 1) 2 := by
    rw [hdouble, htarget, Finset.sum_add_distrib, hlinear]
    omega
  omega

/-- Increasing ordered pairs are the non-diagonal part of the symmetric
square. -/
noncomputable def strictPairSym2Equiv (α : Type*) [LinearOrder α] :
    {p : α × α // p.1 < p.2} ≃ {z : Sym2 α // ¬z.IsDiag} where
  toFun p := ⟨s(p.1.1, p.1.2), by
    simpa only [Sym2.mk_isDiag_iff] using ne_of_lt p.2⟩
  invFun z := by
    let p := Sym2.sortEquiv z.1
    have hne : p.1.1 ≠ p.1.2 := by
      intro h
      apply z.2
      have hinv := Sym2.sortEquiv.symm_apply_apply z.1
      change Sym2.mk p.1 = z.1 at hinv
      rw [← hinv, Sym2.isDiag_iff_proj_eq]
      exact h
    exact ⟨p.1, lt_of_le_of_ne p.2 hne⟩
  left_inv := by
    rintro ⟨⟨a, b⟩, hab⟩
    apply Subtype.ext
    simp [Sym2.sortEquiv, hab.le]
  right_inv := by
    intro z
    apply Subtype.ext
    change Sym2.mk (Sym2.sortEquiv z.1).1 = z.1
    exact Sym2.sortEquiv.symm_apply_apply z.1

theorem card_internalPair (T : PosIntTree n) (C : EvenComponent T) :
    Fintype.card (InternalPair T C) =
      Nat.choose (Fintype.card (ComponentVertex T C)) 2 := by
  calc
    Fintype.card (InternalPair T C) =
        Fintype.card
          {z : Sym2 (ComponentVertex T C) // ¬z.IsDiag} :=
      Fintype.card_congr (strictPairSym2Equiv (ComponentVertex T C))
    _ = Nat.choose (Fintype.card (ComponentVertex T C)) 2 :=
      Sym2.card_subtype_not_diag

theorem card_withinIndex (T : PosIntTree n) :
    Fintype.card (WithinIndex T) =
      ∑ C : EvenComponent T,
        Nat.choose (Fintype.card (ComponentVertex T C)) 2 := by
  simp only [WithinIndex, Fintype.card_sigma, card_internalPair]

theorem componentVertex_card_pos (T : PosIntTree n) (C : EvenComponent T) :
    0 < Fintype.card (ComponentVertex T C) := by
  obtain ⟨v, hv⟩ := componentOf_surjective T C
  exact Fintype.card_pos_iff.mpr ⟨⟨v, hv⟩⟩

/-! ## Actual root-parity component profile -/

noncomputable def componentParity
    (T : PosIntTree n) (root : Fin n) (C : EvenComponent T) : ℕ :=
  T.dist root (componentRep T C) % 2

theorem componentParity_lt_two
    (T : PosIntTree n) (root : Fin n) (C : EvenComponent T) :
    componentParity T root C < 2 := by
  exact Nat.mod_lt _ (by omega)

theorem componentParity_eq_vertexParity
    (T : PosIntTree n) (root : Fin n) (C : EvenComponent T)
    (v : ComponentVertex T C) :
    componentParity T root C = T.dist root v.1 % 2 := by
  have hcomp : componentOf T v.1 = componentOf T (componentRep T C) :=
    v.2.trans (componentOf_componentRep T C).symm
  have hbetween := dist_even_of_component_eq T hcomp
  have hroot := T.root_path_even root v.1 (componentRep T C)
  rw [Nat.even_iff] at hbetween hroot
  unfold componentParity
  omega

abbrev ParityComponent
    (T : PosIntTree n) (root : Fin n) (p : ℕ) :=
  {C : EvenComponent T // componentParity T root C = p}

/-- The vertices contained in parity-`p` even components are exactly the
actual root-parity-`p` vertices. -/
noncomputable def parityComponentVertexEquiv
    (T : PosIntTree n) (root : Fin n) (p : ℕ) :
    (Σ C : ParityComponent T root p, ComponentVertex T C.1) ≃
      {v : Fin n // T.dist root v % 2 = p} where
  toFun z := ⟨z.2.1, by
    rw [← componentParity_eq_vertexParity T root z.1.1 z.2]
    exact z.1.2⟩
  invFun v :=
    ⟨⟨componentOf T v.1, by
        rw [componentParity_eq_vertexParity T root
          (componentOf T v.1) ⟨v.1, rfl⟩]
        exact v.2⟩,
      ⟨v.1, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨C, hC⟩, ⟨v, hv⟩⟩
    have hCeq : componentOf T v = C := hv
    subst C
    rfl
  right_inv := by
    intro v
    apply Subtype.ext
    rfl

theorem parityComponent_size_sum
    (T : PosIntTree n) (root : Fin n) (p : ℕ) :
    (∑ C : ParityComponent T root p,
        Fintype.card (ComponentVertex T C.1)) =
      Fintype.card {v : Fin n // T.dist root v % 2 = p} := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (parityComponentVertexEquiv T root p)

private noncomputable def componentParityPartitionInv
    (T : PosIntTree n) (root : Fin n) (C : EvenComponent T) :
    ParityComponent T root 0 ⊕ ParityComponent T root 1 := by
  classical
  by_cases h : componentParity T root C = 0
  · exact .inl ⟨C, h⟩
  · exact .inr ⟨C, by
      have hlt := componentParity_lt_two T root C
      omega⟩

noncomputable def componentParityPartitionEquiv
    (T : PosIntTree n) (root : Fin n) :
    ParityComponent T root 0 ⊕ ParityComponent T root 1 ≃
      EvenComponent T where
  toFun
    | .inl C => C.1
    | .inr C => C.1
  invFun := componentParityPartitionInv T root
  left_inv := by
    intro C
    cases C with
    | inl C => simp [componentParityPartitionInv, C.2]
    | inr C =>
        have hne : componentParity T root C.1 ≠ 0 := by omega
        simp [componentParityPartitionInv, hne]
  right_inv := by
    intro C
    by_cases h : componentParity T root C = 0 <;>
      simp [componentParityPartitionInv, h]

theorem parityComponent_count_add
    (T : PosIntTree n) (root : Fin n) :
    Fintype.card (ParityComponent T root 0) +
        Fintype.card (ParityComponent T root 1) =
      Fintype.card (EvenComponent T) := by
  rw [← Fintype.card_sum]
  exact Fintype.card_congr (componentParityPartitionEquiv T root)

theorem parityComponent_internal_sum
    (T : PosIntTree n) (root : Fin n) :
    (∑ C : EvenComponent T,
        Nat.choose (Fintype.card (ComponentVertex T C)) 2) =
      (∑ C : ParityComponent T root 0,
        Nat.choose (Fintype.card (ComponentVertex T C.1)) 2) +
      (∑ C : ParityComponent T root 1,
        Nat.choose (Fintype.card (ComponentVertex T C.1)) 2) := by
  calc
    (∑ C : EvenComponent T,
        Nat.choose (Fintype.card (ComponentVertex T C)) 2) =
        ∑ C : ParityComponent T root 0 ⊕ ParityComponent T root 1,
          Nat.choose (Fintype.card
            (ComponentVertex T (componentParityPartitionEquiv T root C))) 2 := by
      apply Fintype.sum_equiv (componentParityPartitionEquiv T root).symm
      intro C
      exact congrArg
        (fun D : EvenComponent T =>
          Nat.choose (Fintype.card (ComponentVertex T D)) 2)
        ((componentParityPartitionEquiv T root).apply_symm_apply C).symm
    _ = _ := by
      rw [Fintype.sum_sum_type]
      rfl

/-- Exact quotient-tree component count: deleting `r` actual odd bridges
creates `r+1` even components. -/
theorem oddBridge_card_add_one_eq_component_card (T : PosIntTree n) :
    Fintype.card (OddBridge T) + 1 = Fintype.card (EvenComponent T) := by
  letI : Fintype (quotientGraph T).edgeSet := Fintype.ofFinite _
  have hedge :
      Fintype.card (OddBridge T) =
        Fintype.card (quotientGraph T).edgeSet :=
    Fintype.card_congr (oddBridgeQuotientEdgeEquiv T)
  have htree := (quotientGraph_isTree T).card_edgeFinset
  simp only [SimpleGraph.edgeFinset_card] at htree
  omega

theorem parityComponent_card_pos_of_vertex_card_pos
    (T : PosIntTree n) (root : Fin n) (p : ℕ)
    (hpos : 0 < Fintype.card {v : Fin n // T.dist root v % 2 = p}) :
    0 < Fintype.card (ParityComponent T root p) := by
  rw [Fintype.card_pos_iff] at hpos ⊢
  rcases hpos with ⟨v⟩
  exact ⟨((parityComponentVertexEquiv T root p).symm v).1⟩

theorem card_le_size_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) (hpos : ∀ i, 0 < m i) :
    Fintype.card ι ≤ ∑ i, m i := by
  calc
    Fintype.card ι = ∑ _i : ι, 1 := by simp
    _ ≤ ∑ i : ι, m i := Finset.sum_le_sum fun i _ => hpos i

/-- Every one component has size at most the concentrated-profile maximum. -/
theorem one_size_le_concentrated
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) (hpos : ∀ i, 0 < m i) (i : ι) :
    m i ≤ (∑ j, m j) - Fintype.card ι + 1 := by
  classical
  have hrest : (Finset.univ.erase i).card ≤
      ∑ j ∈ Finset.univ.erase i, m j := by
    calc
      (Finset.univ.erase i).card = ∑ _j ∈ Finset.univ.erase i, 1 := by simp
      _ ≤ ∑ j ∈ Finset.univ.erase i, m j :=
        Finset.sum_le_sum fun j _ => hpos j
  have hsplit : (∑ j, m j) = m i + ∑ j ∈ Finset.univ.erase i, m j := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), Nat.add_comm]
  have hcardPos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  have hcard : (Finset.univ.erase i).card + 1 = Fintype.card ι := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
    exact Nat.sub_add_cancel hcardPos
  omega

/-! ## Order-18 profile and unconditional G/H graph endpoints -/

noncomputable def order18SmallComponentCount
    (T : PosIntTree 18) (root : Fin 18) : ℕ :=
  if T.parityClassSize root = 7 then
    Fintype.card (ParityComponent T root 0)
  else Fintype.card (ParityComponent T root 1)

noncomputable def order18LargeComponentCount
    (T : PosIntTree 18) (root : Fin 18) : ℕ :=
  if T.parityClassSize root = 7 then
    Fintype.card (ParityComponent T root 1)
  else Fintype.card (ParityComponent T root 0)

theorem order18_component_profile
    {T : PosIntTree 18} (hL : IsLeech T) (root : Fin 18) :
    let r := Fintype.card (OddBridge T)
    let k := order18SmallComponentCount T root
    let l := order18LargeComponentCount T root
    k + l = r + 1 ∧ 1 ≤ k ∧ k ≤ 7 ∧ 1 ≤ l ∧ l ≤ 11 := by
  classical
  have hclass := t3_order18_class_sizes hL root
  have hsum0 := parityComponent_size_sum T root 0
  have hsum1 := parityComponent_size_sum T root 1
  have hcount := parityComponent_count_add T root
  have hquot := oddBridge_card_add_one_eq_component_card T
  have hpos0 := fun C : ParityComponent T root 0 =>
    componentVertex_card_pos T C.1
  have hpos1 := fun C : ParityComponent T root 1 =>
    componentVertex_card_pos T C.1
  rcases hclass with h7 | h11
  · have hcard0 :
        Fintype.card {v : Fin 18 // T.dist root v % 2 = 0} = 7 := by
      simpa [PosIntTree.parityClassSize] using h7
    have hcard1 :
        Fintype.card {v : Fin 18 // T.dist root v % 2 = 1} = 11 := by
      have hcomp := Fintype.card_subtype_compl
        (fun v : Fin 18 => T.dist root v % 2 = 0)
      have hequiv :
          {v : Fin 18 // ¬T.dist root v % 2 = 0} ≃
            {v : Fin 18 // T.dist root v % 2 = 1} :=
        Equiv.subtypeEquivRight fun v => by
          have hlt := Nat.mod_lt (T.dist root v) (by omega : 0 < 2)
          omega
      have := Fintype.card_congr hequiv
      norm_num [hcard0] at hcomp
      omega
    simp only [order18SmallComponentCount, order18LargeComponentCount, h7,
      if_pos]
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩
    · exact parityComponent_card_pos_of_vertex_card_pos T root 0 (by
        rw [hcard0]
        omega)
    · have := card_le_size_sum
        (fun C : ParityComponent T root 0 =>
          Fintype.card (ComponentVertex T C.1)) hpos0
      rw [hsum0, hcard0] at this
      exact this
    · exact parityComponent_card_pos_of_vertex_card_pos T root 1 (by
        rw [hcard1]
        omega)
    · have := card_le_size_sum
        (fun C : ParityComponent T root 1 =>
          Fintype.card (ComponentVertex T C.1)) hpos1
      rw [hsum1, hcard1] at this
      exact this
  · have hne7 : T.parityClassSize root ≠ 7 := by omega
    have hcard0 :
        Fintype.card {v : Fin 18 // T.dist root v % 2 = 0} = 11 := by
      simpa [PosIntTree.parityClassSize] using h11
    have hcard1 :
        Fintype.card {v : Fin 18 // T.dist root v % 2 = 1} = 7 := by
      have hcomp := Fintype.card_subtype_compl
        (fun v : Fin 18 => T.dist root v % 2 = 0)
      have hequiv :
          {v : Fin 18 // ¬T.dist root v % 2 = 0} ≃
            {v : Fin 18 // T.dist root v % 2 = 1} :=
        Equiv.subtypeEquivRight fun v => by
          have hlt := Nat.mod_lt (T.dist root v) (by omega : 0 < 2)
          omega
      have := Fintype.card_congr hequiv
      norm_num [hcard0] at hcomp
      omega
    simp only [order18SmallComponentCount, order18LargeComponentCount,
      hne7, if_false]
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩
    · exact parityComponent_card_pos_of_vertex_card_pos T root 1 (by
        rw [hcard1]
        omega)
    · have := card_le_size_sum
        (fun C : ParityComponent T root 1 =>
          Fintype.card (ComponentVertex T C.1)) hpos1
      rw [hsum1, hcard1] at this
      exact this
    · exact parityComponent_card_pos_of_vertex_card_pos T root 0 (by
        rw [hcard0]
        omega)
    · have := card_le_size_sum
        (fun C : ParityComponent T root 0 =>
          Fintype.card (ComponentVertex T C.1)) hpos0
      rw [hsum0, hcard0] at this
      exact this

theorem order18_component_profile_feasible
    {T : PosIntTree 18} (hL : IsLeech T) (root : Fin 18) :
    FeasibleColorSplit 7 11 (Fintype.card (OddBridge T))
      (order18SmallComponentCount T root) := by
  have hp := order18_component_profile hL root
  dsimp only at hp
  rcases hp with ⟨hkl, hk1, hk7, hl1, hl11⟩
  unfold FeasibleColorSplit
  constructor
  · exact hk1
  constructor
  · exact hk7
  constructor <;> omega

/-- The fixed-profile internal-pair upper bound is derived from the actual
component sizes; it is not an input assumption. -/
theorem order18_withinIndex_profile_bound
    {T : PosIntTree 18} (hL : IsLeech T) (root : Fin 18) :
    let r := Fintype.card (OddBridge T)
    let k := order18SmallComponentCount T root
    Fintype.card (WithinIndex T) ≤
      Nat.choose (8 - k) 2 + Nat.choose (11 + k - r) 2 := by
  classical
  have hclass := t3_order18_class_sizes hL root
  have hsplit := parityComponent_internal_sum T root
  have hwithin := card_withinIndex T
  have hsum0 := parityComponent_size_sum T root 0
  have hsum1 := parityComponent_size_sum T root 1
  have hcount := parityComponent_count_add T root
  have hquot := oddBridge_card_add_one_eq_component_card T
  have hprofile := order18_component_profile hL root
  dsimp only at hprofile
  rcases hprofile with ⟨hkl, hk1, hk7, hl1, hl11⟩
  have hb0 := sum_choose_two_le_concentrated
    (fun C : ParityComponent T root 0 =>
      Fintype.card (ComponentVertex T C.1))
    (fun C => componentVertex_card_pos T C.1)
  have hb1 := sum_choose_two_le_concentrated
    (fun C : ParityComponent T root 1 =>
      Fintype.card (ComponentVertex T C.1))
    (fun C => componentVertex_card_pos T C.1)
  rcases hclass with h7 | h11
  · have hcard0 :
        Fintype.card {v : Fin 18 // T.dist root v % 2 = 0} = 7 := by
      simpa [PosIntTree.parityClassSize] using h7
    have hcard1 :
        Fintype.card {v : Fin 18 // T.dist root v % 2 = 1} = 11 := by
      have hc := Fintype.card_subtype_compl
        (fun v : Fin 18 => T.dist root v % 2 = 0)
      have he :
          {v : Fin 18 // ¬T.dist root v % 2 = 0} ≃
            {v : Fin 18 // T.dist root v % 2 = 1} :=
        Equiv.subtypeEquivRight fun v => by
          have := Nat.mod_lt (T.dist root v) (by omega : 0 < 2)
          omega
      have := Fintype.card_congr he
      norm_num [hcard0] at hc
      omega
    rw [hsum0, hcard0] at hb0
    rw [hsum1, hcard1] at hb1
    have hkl' := hkl
    have hk7' := hk7
    have hl11' := hl11
    simp only [order18SmallComponentCount, order18LargeComponentCount,
      h7, if_true] at hkl' hk7' hl11'
    have hk0le : Fintype.card (ParityComponent T root 0) ≤ 7 := hk7'
    have hk1le : Fintype.card (ParityComponent T root 1) ≤ 11 := hl11'
    have hcomponents :
        Fintype.card (ParityComponent T root 0) +
            Fintype.card (ParityComponent T root 1) =
          Fintype.card (OddBridge T) + 1 := by
      omega
    have hb0arg :
        7 - Fintype.card (ParityComponent T root 0) + 1 =
          8 - Fintype.card (ParityComponent T root 0) := by
      omega
    have hb1arg :
        11 - Fintype.card (ParityComponent T root 1) + 1 =
          11 + Fintype.card (ParityComponent T root 0) -
            Fintype.card (OddBridge T) := by
      omega
    rw [hb0arg] at hb0
    rw [hb1arg] at hb1
    rw [hwithin, hsplit]
    simp only [order18SmallComponentCount, h7, if_true]
    exact Nat.add_le_add hb0 hb1
  · have hne7 : T.parityClassSize root ≠ 7 := by omega
    have hcard0 :
        Fintype.card {v : Fin 18 // T.dist root v % 2 = 0} = 11 := by
      simpa [PosIntTree.parityClassSize] using h11
    have hcard1 :
        Fintype.card {v : Fin 18 // T.dist root v % 2 = 1} = 7 := by
      have hc := Fintype.card_subtype_compl
        (fun v : Fin 18 => T.dist root v % 2 = 0)
      have he :
          {v : Fin 18 // ¬T.dist root v % 2 = 0} ≃
            {v : Fin 18 // T.dist root v % 2 = 1} :=
        Equiv.subtypeEquivRight fun v => by
          have := Nat.mod_lt (T.dist root v) (by omega : 0 < 2)
          omega
      have := Fintype.card_congr he
      norm_num [hcard0] at hc
      omega
    rw [hsum0, hcard0] at hb0
    rw [hsum1, hcard1] at hb1
    have hkl' := hkl
    have hk7' := hk7
    have hl11' := hl11
    simp only [order18SmallComponentCount, order18LargeComponentCount,
      hne7, if_false] at hkl' hk7' hl11'
    have hk0le : Fintype.card (ParityComponent T root 0) ≤ 11 := hl11'
    have hk1le : Fintype.card (ParityComponent T root 1) ≤ 7 := hk7'
    have hcomponents :
        Fintype.card (ParityComponent T root 0) +
            Fintype.card (ParityComponent T root 1) =
          Fintype.card (OddBridge T) + 1 := by
      omega
    have hb0arg :
        11 - Fintype.card (ParityComponent T root 0) + 1 =
          11 + Fintype.card (ParityComponent T root 1) -
            Fintype.card (OddBridge T) := by
      omega
    have hb1arg :
        7 - Fintype.card (ParityComponent T root 1) + 1 =
          8 - Fintype.card (ParityComponent T root 1) := by
      omega
    rw [hb0arg] at hb0
    rw [hb1arg] at hb1
    rw [hwithin, hsplit]
    simp only [order18SmallComponentCount, hne7, if_false]
    calc
      _ ≤ Nat.choose
            (11 + Fintype.card (ParityComponent T root 1) -
              Fintype.card (OddBridge T)) 2 +
          Nat.choose (8 - Fintype.card (ParityComponent T root 1)) 2 :=
        Nat.add_le_add hb0 hb1
      _ = _ := Nat.add_comm _ _

theorem order18_evenPair_card
    {T : PosIntTree 18} (hL : IsLeech T) :
    Fintype.card (EvenVertexPair T) = 76 := by
  letI : Fintype {k : ℕ // k ∈ Finset.Icc 1 (targetN 18 / 2)} :=
    Fintype.ofFinite _
  calc
    Fintype.card (EvenVertexPair T) =
        Fintype.card {k : ℕ // k ∈ Finset.Icc 1 (targetN 18 / 2)} :=
      Fintype.card_congr
        (LeechTrees.OddQuotient.IsLeech.evenHalfRankEquiv hL)
    _ = 76 := by norm_num [targetN, Nat.choose]

theorem order18_evenCross_card_add_within
    {T : PosIntTree 18} (hL : IsLeech T) :
    Fintype.card (EvenCrossIndex T) + Fintype.card (WithinIndex T) = 76 := by
  have hcard := Fintype.card_congr (evenPairBlockEquiv T)
  rw [Fintype.card_sum, order18_evenPair_card hL] at hcard
  omega

/-- The G floor now has no profile hypothesis: it follows from the actual
7/11 component sizes and `r+1` quotient components. -/
theorem order18G_le_evenCross_card
    {T : PosIntTree 18} (hL : IsLeech T) (root : Fin 18)
    (hr3 : 3 ≤ Fintype.card (OddBridge T))
    (hr15 : Fintype.card (OddBridge T) ≤ 15) :
    order18G (Fintype.card (OddBridge T)) ≤
      Fintype.card (EvenCrossIndex T) := by
  let r := Fintype.card (OddBridge T)
  let k := order18SmallComponentCount T root
  change 3 ≤ r at hr3
  change r ≤ 15 at hr15
  have hfeas := order18_component_profile_feasible hL root
  change FeasibleColorSplit 7 11 r k at hfeas
  have hI := order18_withinIndex_profile_bound hL root
  change Fintype.card (WithinIndex T) ≤
      Nat.choose (8 - k) 2 + Nat.choose (11 + k - r) 2 at hI
  have hE := order18_evenCross_card_add_within hL
  have hH := order18G_lower_bound hr3 hr15 hfeas
  rcases hfeas with ⟨hk1, hk7, hl1, hl11⟩
  change order18G r ≤ Fintype.card (EvenCrossIndex T)
  let l := r + 1 - k
  change 1 ≤ l at hl1
  change l ≤ 11 at hl11
  change order18G r ≤ colorCrossFloor 7 k + colorCrossFloor 11 l at hH
  have hlargeArg : 11 + k - r = 12 - l := by
    dsimp only [l]
    omega
  rw [hlargeArg] at hI
  have hsmallIdentity :
      colorCrossFloor 7 k + Nat.choose (8 - k) 2 = 21 := by
    interval_cases k <;> norm_num [colorCrossFloor, Nat.choose]
  have hlargeIdentity :
      colorCrossFloor 11 l + Nat.choose (12 - l) 2 = 55 := by
    interval_cases l <;> norm_num [colorCrossFloor, Nat.choose]
  omega

/-- Unconditional actual-graph G endpoint. -/
theorem order18_actual_graph_primary_cap
    {T : PosIntTree 18} (hL : IsLeech T) (root : Fin 18)
    (D : SecondOddBridgeData T)
    (hr3 : 3 ≤ Fintype.card (OddBridge T))
    (hr15 : Fintype.card (OddBridge T) ≤ 15) :
    D.q₂ ≤ order18PrimaryCap (Fintype.card (OddBridge T)) := by
  exact order18_graph_primary_cap hL D _
    (order18G_le_evenCross_card hL root hr3 hr15)

/-- Canonical graph-facing G endpoint for the actual second odd physical
weight.  Unlike the threshold-level theorem above, the conclusion is stated
directly for `secondOddWeight`. -/
theorem order18_canonical_actual_graph_primary_cap
    {T : PosIntTree 18} (hL : IsLeech T) (root : Fin 18)
    (h₂ : HasNonunitOddBridge T)
    (hr3 : 3 ≤ Fintype.card (OddBridge T))
    (hr15 : Fintype.card (OddBridge T) ≤ 15) :
    secondOddWeight h₂ ≤
      order18PrimaryCap (Fintype.card (OddBridge T)) := by
  simpa only [canonicalSecondOddBridgeData_q₂] using
    order18_actual_graph_primary_cap hL root
      (canonicalSecondOddBridgeData hL (by decide) h₂) hr3 hr15

/-! The unit-component product is derived next; this closes H as well. -/

theorem unit_components_have_opposite_parity
    {T : PosIntTree n} (root : Fin n) (D : SecondOddBridgeData T) :
    (componentParity T root (componentOf T (T.edgeLeft D.unit.1)) = 0 ∧
      componentParity T root (componentOf T (T.edgeRight D.unit.1)) = 1) ∨
    (componentParity T root (componentOf T (T.edgeLeft D.unit.1)) = 1 ∧
      componentParity T root (componentOf T (T.edgeRight D.unit.1)) = 0) := by
  have hleft := componentParity_eq_vertexParity T root
    (componentOf T (T.edgeLeft D.unit.1)) ⟨T.edgeLeft D.unit.1, rfl⟩
  have hright := componentParity_eq_vertexParity T root
    (componentOf T (T.edgeRight D.unit.1)) ⟨T.edgeRight D.unit.1, rfl⟩
  have hroot := T.root_path_even root
    (T.edgeLeft D.unit.1) (T.edgeRight D.unit.1)
  have hedge : T.dist (T.edgeLeft D.unit.1) (T.edgeRight D.unit.1) = 1 := by
    change T.pairDist (T.edgePair D.unit.1) = 1
    rw [T.edgePair_dist, D.unit_weight]
  rw [Nat.even_iff, hedge] at hroot
  have hoppositeVertex :
      (T.dist root (T.edgeLeft D.unit.1) % 2 = 0 ∧
        T.dist root (T.edgeRight D.unit.1) % 2 = 1) ∨
      (T.dist root (T.edgeLeft D.unit.1) % 2 = 1 ∧
        T.dist root (T.edgeRight D.unit.1) % 2 = 0) := by
    have hleftMod := Nat.mod_lt (T.dist root (T.edgeLeft D.unit.1))
      (by omega : 0 < 2)
    have hrightMod := Nat.mod_lt (T.dist root (T.edgeRight D.unit.1))
      (by omega : 0 < 2)
    omega
  have hl := componentParity_lt_two T root
    (componentOf T (T.edgeLeft D.unit.1))
  have hr := componentParity_lt_two T root
    (componentOf T (T.edgeRight D.unit.1))
  rw [hleft, hright]
  exact hoppositeVertex

theorem order18_unitRectangle_profile_bound
    {T : PosIntTree 18} (hL : IsLeech T) (root : Fin 18)
    (D : SecondOddBridgeData T) :
    let r := Fintype.card (OddBridge T)
    let k := order18SmallComponentCount T root
    Fintype.card (UnitLeftComponentVertex D) *
        Fintype.card (UnitRightComponentVertex D) ≤
      (8 - k) * (11 + k - r) := by
  classical
  have hprofile := order18_component_profile hL root
  dsimp only at hprofile
  rcases hprofile with ⟨hkl, hk1, hk7, hl1, hl11⟩
  have hclass := t3_order18_class_sizes hL root
  have hopposite := unit_components_have_opposite_parity root D
  have hsum0 := parityComponent_size_sum T root 0
  have hsum1 := parityComponent_size_sum T root 1
  have hcount := parityComponent_count_add T root
  have hquot := oddBridge_card_add_one_eq_component_card T
  rcases hclass with h7 | h11
  · have hcard0 :
        Fintype.card {v : Fin 18 // T.dist root v % 2 = 0} = 7 := by
      simpa [PosIntTree.parityClassSize] using h7
    have hcard1 :
        Fintype.card {v : Fin 18 // T.dist root v % 2 = 1} = 11 := by
      have hc := Fintype.card_subtype_compl
        (fun v : Fin 18 => T.dist root v % 2 = 0)
      have he :
          {v : Fin 18 // ¬T.dist root v % 2 = 0} ≃
            {v : Fin 18 // T.dist root v % 2 = 1} :=
        Equiv.subtypeEquivRight fun v => by
          have := Nat.mod_lt (T.dist root v) (by omega : 0 < 2)
          omega
      have := Fintype.card_congr he
      norm_num [hcard0] at hc
      omega
    have hkl' := hkl
    have hk7' := hk7
    have hl11' := hl11
    simp only [order18SmallComponentCount, order18LargeComponentCount,
      h7, if_true] at hkl' hk7' hl11'
    have hk0le : Fintype.card (ParityComponent T root 0) ≤ 7 := hk7'
    have hk1le : Fintype.card (ParityComponent T root 1) ≤ 11 := hl11'
    have hcomponents :
        Fintype.card (ParityComponent T root 0) +
            Fintype.card (ParityComponent T root 1) =
          Fintype.card (OddBridge T) + 1 := by
      omega
    have bound0 (C : ParityComponent T root 0) :
        Fintype.card (ComponentVertex T C.1) ≤
          8 - Fintype.card (ParityComponent T root 0) := by
      have hb := one_size_le_concentrated
        (fun C : ParityComponent T root 0 =>
          Fintype.card (ComponentVertex T C.1))
        (fun C => componentVertex_card_pos T C.1) C
      rw [hsum0, hcard0] at hb
      omega
    have bound1 (C : ParityComponent T root 1) :
        Fintype.card (ComponentVertex T C.1) ≤
          12 - Fintype.card (ParityComponent T root 1) := by
      have hb := one_size_le_concentrated
        (fun C : ParityComponent T root 1 =>
          Fintype.card (ComponentVertex T C.1))
        (fun C => componentVertex_card_pos T C.1) C
      rw [hsum1, hcard1] at hb
      omega
    have hlargeFactor :
        12 - Fintype.card (ParityComponent T root 1) =
          11 + Fintype.card (ParityComponent T root 0) -
            Fintype.card (OddBridge T) := by
      omega
    rcases hopposite with h | h
    · have hx := bound0 ⟨_, h.1⟩
      have hy := bound1 ⟨_, h.2⟩
      rw [hlargeFactor] at hy
      simp only [UnitLeftComponentVertex, UnitRightComponentVertex,
        order18SmallComponentCount, h7, if_true]
      exact Nat.mul_le_mul hx hy
    · have hx := bound1 ⟨_, h.1⟩
      have hy := bound0 ⟨_, h.2⟩
      rw [hlargeFactor] at hx
      simp only [UnitLeftComponentVertex, UnitRightComponentVertex,
        order18SmallComponentCount, h7, if_true]
      simpa only [Nat.mul_comm] using Nat.mul_le_mul hx hy
  · have hne7 : T.parityClassSize root ≠ 7 := by omega
    have hcard0 :
        Fintype.card {v : Fin 18 // T.dist root v % 2 = 0} = 11 := by
      simpa [PosIntTree.parityClassSize] using h11
    have hcard1 :
        Fintype.card {v : Fin 18 // T.dist root v % 2 = 1} = 7 := by
      have hc := Fintype.card_subtype_compl
        (fun v : Fin 18 => T.dist root v % 2 = 0)
      have he :
          {v : Fin 18 // ¬T.dist root v % 2 = 0} ≃
            {v : Fin 18 // T.dist root v % 2 = 1} :=
        Equiv.subtypeEquivRight fun v => by
          have := Nat.mod_lt (T.dist root v) (by omega : 0 < 2)
          omega
      have := Fintype.card_congr he
      norm_num [hcard0] at hc
      omega
    have hkl' := hkl
    have hk7' := hk7
    have hl11' := hl11
    simp only [order18SmallComponentCount, order18LargeComponentCount,
      hne7, if_false] at hkl' hk7' hl11'
    have hk0le : Fintype.card (ParityComponent T root 0) ≤ 11 := hl11'
    have hk1le : Fintype.card (ParityComponent T root 1) ≤ 7 := hk7'
    have hcomponents :
        Fintype.card (ParityComponent T root 0) +
            Fintype.card (ParityComponent T root 1) =
          Fintype.card (OddBridge T) + 1 := by
      omega
    have bound0 (C : ParityComponent T root 0) :
        Fintype.card (ComponentVertex T C.1) ≤
          12 - Fintype.card (ParityComponent T root 0) := by
      have hb := one_size_le_concentrated
        (fun C : ParityComponent T root 0 =>
          Fintype.card (ComponentVertex T C.1))
        (fun C => componentVertex_card_pos T C.1) C
      rw [hsum0, hcard0] at hb
      omega
    have bound1 (C : ParityComponent T root 1) :
        Fintype.card (ComponentVertex T C.1) ≤
          8 - Fintype.card (ParityComponent T root 1) := by
      have hb := one_size_le_concentrated
        (fun C : ParityComponent T root 1 =>
          Fintype.card (ComponentVertex T C.1))
        (fun C => componentVertex_card_pos T C.1) C
      rw [hsum1, hcard1] at hb
      omega
    have hlargeFactor :
        12 - Fintype.card (ParityComponent T root 0) =
          11 + Fintype.card (ParityComponent T root 1) -
            Fintype.card (OddBridge T) := by
      omega
    rcases hopposite with h | h
    · have hx := bound0 ⟨_, h.1⟩
      have hy := bound1 ⟨_, h.2⟩
      rw [hlargeFactor] at hx
      simp only [UnitLeftComponentVertex, UnitRightComponentVertex,
        order18SmallComponentCount, hne7, if_false]
      simpa only [Nat.mul_comm] using Nat.mul_le_mul hx hy
    · have hx := bound1 ⟨_, h.1⟩
      have hy := bound0 ⟨_, h.2⟩
      rw [hlargeFactor] at hy
      simp only [UnitLeftComponentVertex, UnitRightComponentVertex,
        order18SmallComponentCount, hne7, if_false]
      exact Nat.mul_le_mul hx hy

/-- Unconditional actual-graph H endpoint. -/
theorem order18_actual_graph_companion_cap
    {T : PosIntTree 18} (hL : IsLeech T) (root : Fin 18)
    (D : SecondOddBridgeData T)
    (hr3 : 3 ≤ Fintype.card (OddBridge T))
    (hr15 : Fintype.card (OddBridge T) ≤ 15) :
    D.q₂ ≤ order18CompanionCap (Fintype.card (OddBridge T)) := by
  let r := Fintype.card (OddBridge T)
  let k := order18SmallComponentCount T root
  have hprofile := order18_component_profile hL root
  dsimp only at hprofile
  rcases hprofile with ⟨hkl, hk1, hk7, hl1, hl11⟩
  have hwithin := order18_withinIndex_profile_bound hL root
  have hunit := order18_unitRectangle_profile_bound hL root D
  change Fintype.card (WithinIndex T) ≤
      Nat.choose (8 - k) 2 + Nat.choose (11 + k - r) 2 at hwithin
  change Fintype.card (UnitLeftComponentVertex D) *
      Fintype.card (UnitRightComponentVertex D) ≤
        (8 - k) * (11 + k - r) at hunit
  exact order18_graph_companion_cap hL D r k hr3 hr15
    (order18_component_profile_feasible hL root) hwithin hunit

/-- Canonical graph-facing H endpoint for the actual second odd physical
weight, with both profile inputs derived from the graph. -/
theorem order18_canonical_actual_graph_companion_cap
    {T : PosIntTree 18} (hL : IsLeech T) (root : Fin 18)
    (h₂ : HasNonunitOddBridge T)
    (hr3 : 3 ≤ Fintype.card (OddBridge T))
    (hr15 : Fintype.card (OddBridge T) ≤ 15) :
    secondOddWeight h₂ ≤
      order18CompanionCap (Fintype.card (OddBridge T)) := by
  simpa only [canonicalSecondOddBridgeData_q₂] using
    order18_actual_graph_companion_cap hL root
      (canonicalSecondOddBridgeData hL (by decide) h₂) hr3 hr15

end LeechTrees.OddQuotient.Q2Bounds.GraphProfiles
