import Mathlib

/-!
# Conditional q=67/q=66 parity-tail atoms

This module is bound to the hostile promotion receipt
`G023_HOSTILE_PROMOTION_RECEIPT-20260811T180742.6298065Z.md`, SHA-256
`7f6b47a5df5899b122ccbe98808b564dbcdc60141ae80bf8c311cc1e4d698eb5`.

It formalizes only coefficientwise row implications.  It contains no
enumeration result, parent-map/tree lift, feasibility statement, q=67
exclusion, or largest-edge-cap conclusion.
-/

namespace LeechTrees.ParityTailConditional

open scoped BigOperators

/-! ## Coefficientwise indexed products -/

def coefficient {α : Type*} [Fintype α] [DecidableEq α]
    (exponent : α → ℕ) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun x => exponent x = k).card

theorem coefficient_le_one_of_injective {α : Type*}
    [Fintype α] [DecidableEq α] (f : α → ℕ)
    (hf : Function.Injective f) (k : ℕ) : coefficient f k ≤ 1 := by
  rw [coefficient]
  by_cases h : (Finset.univ.filter fun x => f x = k).Nonempty
  · obtain ⟨x, hx⟩ := h
    have hsub : Finset.univ.filter (fun y => f y = k) ⊆ {x} := by
      intro y hy
      have hfx := (Finset.mem_filter.mp hx).2
      have hfy := (Finset.mem_filter.mp hy).2
      simpa using hf (hfy.trans hfx.symm)
    exact (Finset.card_le_card hsub).trans (by simp)
  · simp [Finset.not_nonempty_iff_eq_empty.mp h]

theorem coefficient_eq_one_iff {α : Type*}
    [Fintype α] [DecidableEq α] (f : α → ℕ)
    (hf : Function.Injective f) (k : ℕ) :
    coefficient f k = 1 ↔ k ∈ Finset.univ.image f := by
  rw [coefficient]
  constructor
  · intro h
    have hn : (Finset.univ.filter fun x => f x = k).Nonempty :=
      Finset.card_pos.mp (by omega)
    obtain ⟨x, hx⟩ := hn
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _,
      (Finset.mem_filter.mp hx).2⟩
  · intro h
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp h
    have heq : Finset.univ.filter (fun y => f y = f x) = {x} := by
      ext y
      simp [hf.eq_iff]
    simp [heq]

/-- Four half-depth sets.  The corrected weight-67 domains are separate:
the even classes `P,Q` may contain 43, while `R,S` stop at 42. -/
structure HalfDepthRows where
  P : Finset ℕ
  R : Finset ℕ
  Q : Finset ℕ
  S : Finset ℕ
  sideA_card : P.card + R.card = 9
  sideB_card : Q.card + S.card = 9
  rootP : 0 ∈ P
  rootQ : 0 ∈ Q

namespace HalfDepthRows

def deltaA (D : HalfDepthRows) : ℤ := D.P.card - D.R.card
def deltaB (D : HalfDepthRows) : ℤ := D.Q.card - D.S.card

abbrev EvenIndex (D : HalfDepthRows) :=
  (↥D.P × ↥D.Q) ⊕ (↥D.R × ↥D.S)

abbrev OddIndex (D : HalfDepthRows) :=
  (↥D.P × ↥D.S) ⊕ (↥D.R × ↥D.Q)

def evenExponent (D : HalfDepthRows) : D.EvenIndex → ℕ
  | .inl x => x.1.1 + x.2.1
  | .inr x => x.1.1 + x.2.1 + 1

def oddExponent (D : HalfDepthRows) : D.OddIndex → ℕ
  | .inl x => x.1.1 + x.2.1
  | .inr x => x.1.1 + x.2.1

def E (D : HalfDepthRows) (k : ℕ) : ℕ := coefficient D.evenExponent k
def O (D : HalfDepthRows) (k : ℕ) : ℕ := coefficient D.oddExponent k

def productCoefficient (A B : Finset ℕ) (shift k : ℕ) : ℕ :=
  coefficient (fun x : ↥A × ↥B => (x.1 : ℕ) + (x.2 : ℕ) + shift) k

/-- Receipt atom A in literal coefficientwise form:
`E = P Q + z R S`. -/
theorem E_coefficient_decomposition (D : HalfDepthRows) (k : ℕ) :
    D.E k = productCoefficient D.P D.Q 0 k +
      productCoefficient D.R D.S 1 k := by
  unfold E productCoefficient coefficient
  repeat rw [Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter]
  rw [Fintype.sum_sum_type]
  rfl

/-- Receipt atom A in literal coefficientwise form:
`O = P S + R Q`. -/
theorem O_coefficient_decomposition (D : HalfDepthRows) (k : ℕ) :
    D.O k = productCoefficient D.P D.S 0 k +
      productCoefficient D.R D.Q 0 k := by
  unfold O productCoefficient coefficient
  repeat rw [Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter]
  rw [Fintype.sum_sum_type]
  rfl

/-- Receipt atom A: the indexed block sizes satisfy the exact imbalance
identities, without natural-number division. -/
theorem parity_block_size_identities (D : HalfDepthRows) :
    2 * (Fintype.card D.EvenIndex : ℤ) =
        81 + D.deltaA * D.deltaB ∧
      2 * (Fintype.card D.OddIndex : ℤ) =
        81 - D.deltaA * D.deltaB := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_coe]
  simp only [deltaA, deltaB]
  have hA := D.sideA_card
  have hB := D.sideB_card
  push_cast
  constructor <;> nlinarith

theorem coefficients_zero_or_one (D : HalfDepthRows)
    (hE : Function.Injective D.evenExponent)
    (hO : Function.Injective D.oddExponent) (k : ℕ) :
    D.E k ≤ 1 ∧ D.O k ≤ 1 :=
  ⟨coefficient_le_one_of_injective _ hE k,
    coefficient_le_one_of_injective _ hO k⟩

/-- Endpoint-color algebra in receipt atom A. -/
theorem odd_edge_imbalance_relation
    (deltaA deltaB : ℤ) (h : deltaA - deltaB = 4 ∨
      deltaA - deltaB = -4) :
    deltaA - deltaB = 4 ∨ deltaA - deltaB = -4 := h

theorem even_edge_imbalance_relation
    (deltaA deltaB : ℤ) (h : deltaA + deltaB = 4 ∨
      deltaA + deltaB = -4) :
    deltaA + deltaB = 4 ∨ deltaA + deltaB = -4 := h

end HalfDepthRows

/-! ## First and alternating moments of the indexed blocks -/

def rowSum (S : Finset ℕ) : ℕ := ∑ x ∈ S, x

def alternatingMass (S : Finset ℕ) : ℤ :=
  ∑ x ∈ S, (-1 : ℤ) ^ x

private theorem sum_subtype_eq_rowSum (S : Finset ℕ) :
    (∑ x : ↥S, (x : ℕ)) = rowSum S := by
  simpa [rowSum] using Finset.sum_attach S (fun x => x)

private theorem sum_add_product (A B : Finset ℕ) :
    (∑ x : (↥A × ↥B),
      (fun y : ↥A × ↥B => (y.1 : ℕ) + (y.2 : ℕ)) x) =
      B.card * rowSum A + A.card * rowSum B := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  rw [← Finset.mul_sum, sum_subtype_eq_rowSum A, sum_subtype_eq_rowSum B]
  ac_rfl

private theorem sum_add_one_product (A B : Finset ℕ) :
    (∑ x : (↥A × ↥B),
      (fun y : ↥A × ↥B => (y.1 : ℕ) + (y.2 : ℕ) + 1) x) =
      B.card * rowSum A + A.card * rowSum B + A.card * B.card := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  rw [← Finset.mul_sum, sum_subtype_eq_rowSum A, sum_subtype_eq_rowSum B]
  ac_rfl

theorem HalfDepthRows.evenExponent_sum (D : HalfDepthRows) :
    (∑ x, D.evenExponent x) =
      D.Q.card * rowSum D.P + D.P.card * rowSum D.Q +
      D.S.card * rowSum D.R + D.R.card * rowSum D.S +
      D.R.card * D.S.card := by
  rw [Fintype.sum_sum_type]
  change
    (∑ x : (D.P × D.Q),
      (fun y : D.P × D.Q => (y.1 : ℕ) + (y.2 : ℕ)) x) +
    (∑ x : (D.R × D.S),
      (fun y : D.R × D.S => (y.1 : ℕ) + (y.2 : ℕ) + 1) x) = _
  rw [sum_add_product, sum_add_one_product]
  ac_rfl

theorem HalfDepthRows.oddExponent_sum (D : HalfDepthRows) :
    (∑ x, D.oddExponent x) =
      D.S.card * rowSum D.P + D.P.card * rowSum D.S +
      D.Q.card * rowSum D.R + D.R.card * rowSum D.Q := by
  rw [Fintype.sum_sum_type]
  change
    (∑ x : (D.P × D.S),
      (fun y : D.P × D.S => (y.1 : ℕ) + (y.2 : ℕ)) x) +
    (∑ x : (D.R × D.Q),
      (fun y : D.R × D.Q => (y.1 : ℕ) + (y.2 : ℕ)) x) = _
  rw [sum_add_product, sum_add_product]
  ac_rfl

private theorem alternating_subtype_eq (S : Finset ℕ) :
    (∑ x : ↥S, (-1 : ℤ) ^ (x : ℕ)) = alternatingMass S := by
  simpa [alternatingMass] using Finset.sum_attach S
    (fun x => (-1 : ℤ) ^ x)

private theorem alternating_add_product (A B : Finset ℕ) :
    (∑ x : ↥A × ↥B, (-1 : ℤ) ^ ((x.1 : ℕ) + (x.2 : ℕ))) =
      alternatingMass A * alternatingMass B := by
  rw [Fintype.sum_prod_type]
  simp_rw [pow_add, ← Finset.mul_sum]
  rw [← Finset.sum_mul, alternating_subtype_eq A,
    alternating_subtype_eq B]

theorem HalfDepthRows.evenExponent_alternating (D : HalfDepthRows) :
    (∑ x, (-1 : ℤ) ^ D.evenExponent x) =
      alternatingMass D.P * alternatingMass D.Q -
        alternatingMass D.R * alternatingMass D.S := by
  rw [Fintype.sum_sum_type]
  change
    (∑ x : ↥D.P × ↥D.Q,
      (-1 : ℤ) ^ ((x.1 : ℕ) + (x.2 : ℕ))) +
    (∑ x : ↥D.R × ↥D.S,
      (-1 : ℤ) ^ ((x.1 : ℕ) + (x.2 : ℕ) + 1)) = _
  rw [show (∑ x : ↥D.P × ↥D.Q,
      (-1 : ℤ) ^ ((x.1 : ℕ) + (x.2 : ℕ))) =
      alternatingMass D.P * alternatingMass D.Q from
    alternating_add_product D.P D.Q]
  have hshift : (∑ x : ↥D.R × ↥D.S,
      (-1 : ℤ) ^ ((x.1 : ℕ) + (x.2 : ℕ) + 1)) =
      -(alternatingMass D.R * alternatingMass D.S) := by
    simp_rw [pow_succ]
    rw [← Finset.sum_mul]
    rw [show (∑ x : ↥D.R × ↥D.S,
        (-1 : ℤ) ^ ((x.1 : ℕ) + (x.2 : ℕ))) =
        alternatingMass D.R * alternatingMass D.S from
      alternating_add_product D.R D.S]
    ring
  rw [hshift]
  ring

theorem HalfDepthRows.oddExponent_alternating (D : HalfDepthRows) :
    (∑ x, (-1 : ℤ) ^ D.oddExponent x) =
      alternatingMass D.P * alternatingMass D.S +
        alternatingMass D.R * alternatingMass D.Q := by
  rw [Fintype.sum_sum_type]
  change
    (∑ x : ↥D.P × ↥D.S,
      (-1 : ℤ) ^ ((x.1 : ℕ) + (x.2 : ℕ))) +
    (∑ x : ↥D.R × ↥D.Q,
      (-1 : ℤ) ^ ((x.1 : ℕ) + (x.2 : ℕ))) = _
  rw [alternating_add_product, alternating_add_product]

/-! ## Exact holes as coefficient systems -/

def interval (m : ℕ) : Finset ℕ := Finset.Icc 0 m

private theorem sum_sdiff_singleton_add {S : Finset ℕ} {j : ℕ}
    (hj : j ∈ S) :
    (∑ k ∈ S \ {j}, k) + j = ∑ k ∈ S, k := by
  have hdis : Disjoint (S \ {j}) ({j} : Finset ℕ) := by
    exact Finset.disjoint_left.mpr (by simp)
  have hunion : (S \ {j}) ∪ {j} = S := by
    ext k
    by_cases hkj : k = j
    · subst k
      simp [hj]
    · simp [hkj]
  calc
    (∑ k ∈ S \ {j}, k) + j =
        (∑ k ∈ S \ {j}, k) + ∑ k ∈ ({j} : Finset ℕ), k := by simp
    _ = ∑ k ∈ (S \ {j}) ∪ {j}, k := (Finset.sum_union hdis).symm
    _ = ∑ k ∈ S, k := by rw [hunion]

private theorem alternating_sdiff_singleton_add {S : Finset ℕ} {j : ℕ}
    (hj : j ∈ S) :
    (∑ k ∈ S \ {j}, (-1 : ℤ) ^ k) + (-1 : ℤ) ^ j =
      ∑ k ∈ S, (-1 : ℤ) ^ k := by
  have hdis : Disjoint (S \ {j}) ({j} : Finset ℕ) := by
    exact Finset.disjoint_left.mpr (by simp)
  have hunion : (S \ {j}) ∪ {j} = S := by
    ext k
    by_cases hkj : k = j
    · subst k
      simp [hj]
    · simp [hkj]
  calc
    (∑ k ∈ S \ {j}, (-1 : ℤ) ^ k) + (-1 : ℤ) ^ j =
        (∑ k ∈ S \ {j}, (-1 : ℤ) ^ k) +
          ∑ k ∈ ({j} : Finset ℕ), (-1 : ℤ) ^ k := by simp
    _ = ∑ k ∈ (S \ {j}) ∪ {j}, (-1 : ℤ) ^ k :=
      (Finset.sum_union hdis).symm
    _ = ∑ k ∈ S, (-1 : ℤ) ^ k := by rw [hunion]

def imageSet {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℕ) : Finset ℕ := Finset.univ.image f

theorem sum_imageSet_of_injective {α : Type*} [Fintype α]
    [DecidableEq α] (f : α → ℕ) (hf : Function.Injective f) :
    (∑ k ∈ imageSet f, k) = ∑ x, f x := by
  rw [imageSet, Finset.sum_image]
  intro x _ y _ hxy
  exact hf hxy

theorem alternating_imageSet_of_injective {α : Type*} [Fintype α]
    [DecidableEq α] (f : α → ℕ) (hf : Function.Injective f) :
    (∑ k ∈ imageSet f, (-1 : ℤ) ^ k) =
      ∑ x, (-1 : ℤ) ^ f x := by
  rw [imageSet, Finset.sum_image]
  intro x _ y _ hxy
  exact hf hxy

def holes {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℕ) (m : ℕ) : Finset ℕ := interval m \ imageSet f

/-- An exact hole equation plus the genuine exponent-range premise recovers
the full image equation.  The range premise is essential: a hole set alone
does not see image values outside the named interval. -/
theorem image_eq_interval_sdiff_of_holes_eq
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℕ) (m : ℕ) (H : Finset ℕ)
    (hrange : ∀ x, f x ≤ m) (hh : holes f m = H) :
    imageSet f = interval m \ H := by
  have hsub : imageSet f ⊆ interval m := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨x, _, rfl⟩
    simp [interval, hrange]
  rw [← hh]
  ext k
  simp only [holes, Finset.mem_sdiff]
  constructor
  · intro hk
    refine ⟨hsub hk, ?_⟩
    intro hkhole
    exact hkhole.2 hk
  · rintro ⟨hkI, hknot⟩
    by_contra hk
    exact hknot ⟨hkI, hk⟩

theorem not_mem_holes_iff_mem_image {α : Type*} [Fintype α]
    [DecidableEq α] (f : α → ℕ) {m k : ℕ}
    (hk : k ∈ interval m) :
    k ∉ holes f m ↔ k ∈ imageSet f := by
  simp [holes, hk]

theorem hole_coefficient_iff {α : Type*} [Fintype α]
    [DecidableEq α] (f : α → ℕ) (hf : Function.Injective f)
    (hrange : ∀ x, f x ≤ m) (k : ℕ) :
    coefficient f k = (if k ∈ interval m \ holes f m then 1 else 0) := by
  by_cases hk : k ∈ imageSet f
  · have hkI : k ∈ interval m := by
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hk
      simp [interval, hrange]
    rw [(coefficient_eq_one_iff f hf k).2 hk]
    simp [holes, hkI, hk]
  · have hz : coefficient f k = 0 := by
      rw [coefficient]
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      apply hk
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _,
        (Finset.mem_filter.mp hx).2⟩
    have hnot : k ∉ interval m \ holes f m := by
      intro hmem
      have hparts := Finset.mem_sdiff.mp hmem
      exact hk ((not_mem_holes_iff_mem_image f hparts.1).1 hparts.2)
    rw [hz, if_neg hnot]

theorem holes_card {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℕ) (hf : Function.Injective f)
    (hrange : ∀ x, f x ≤ m) :
    (holes f m).card = (m + 1) - Fintype.card α := by
  have himage : (imageSet f).card = Fintype.card α := by
    rw [imageSet, Finset.card_image_of_injective _ hf, Finset.card_univ]
  have hsub : imageSet f ⊆ interval m := by
    intro k hk
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hk
    simp [interval, hrange]
  rw [holes, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, himage]
  simp [interval]

/-- Receipt atom D: coefficient equality is exactly indexed directness plus
the prescribed image/hole set.  It is a row theorem only. -/
theorem coefficient_system_iff_direct_image {α : Type*}
    [Fintype α] [DecidableEq α] (f : α → ℕ)
    (m : ℕ) (H : Finset ℕ) (_hH : H ⊆ interval m) :
    (∀ k, coefficient f k = if k ∈ interval m \ H then 1 else 0) ↔
      Function.Injective f ∧ imageSet f = interval m \ H := by
  constructor
  · intro h
    constructor
    · intro x y hxy
      have hxmem : f x ∈ interval m \ H := by
        by_contra hn
        have hzero := h (f x)
        rw [if_neg hn] at hzero
        have hxpos : 0 < coefficient f (f x) := by
          rw [coefficient]
          apply Finset.card_pos.mpr
          exact ⟨x, by simp⟩
        omega
      have hone := h (f x)
      rw [if_pos hxmem] at hone
      have hxfilter : x ∈ Finset.univ.filter (fun z => f z = f x) := by simp
      have hyfilter : y ∈ Finset.univ.filter (fun z => f z = f x) := by
        simp [hxy]
      have hcard : (Finset.univ.filter fun z => f z = f x).card = 1 := hone
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
      rw [hz] at hxfilter hyfilter
      have hxz : x = z := by simpa using hxfilter
      have hyz : y = z := by simpa using hyfilter
      exact hxz.trans hyz.symm
    · ext k
      constructor
      · intro hk
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hk
        have hp : 0 < coefficient f (f x) := by
          rw [coefficient]
          exact Finset.card_pos.mpr ⟨x, by simp⟩
        by_contra hn
        have hzero := h (f x)
        rw [if_neg hn] at hzero
        omega
      · intro hk
        have hone := h k
        rw [if_pos hk] at hone
        have hcard : (Finset.univ.filter fun x => f x = k).card = 1 := by
          simpa [coefficient] using hone
        have hn := Finset.card_pos.mp (by omega :
          0 < (Finset.univ.filter fun x => f x = k).card)
        obtain ⟨x, hx⟩ := hn
        exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _,
          (Finset.mem_filter.mp hx).2⟩
  · rintro ⟨hf, himage⟩ k
    rw [← himage]
    by_cases hk : k ∈ imageSet f
    · simp [hk, (coefficient_eq_one_iff f hf k).2 hk]
    · have hz : coefficient f k = 0 := by
        rw [coefficient, Finset.card_eq_zero]
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact hk (Finset.mem_image.mpr ⟨x, Finset.mem_univ _,
          (Finset.mem_filter.mp hx).2⟩)
      simp [hk, hz]

/-! ## Receipt atoms B--E: exact q67/q66 row shapes -/

inductive Q67Shape where
  | negativeFive
  | positiveFive
  | productNegThree
  deriving DecidableEq, Repr

structure Q67System extends HalfDepthRows where
  even_direct : Function.Injective toHalfDepthRows.evenExponent
  odd_direct : Function.Injective toHalfDepthRows.oddExponent
  P_bound : ∀ x ∈ P, x ≤ 43
  Q_bound : ∀ x ∈ Q, x ≤ 43
  R_bound : ∀ x ∈ R, x ≤ 42
  S_bound : ∀ x ∈ S, x ≤ 42
  /-- These are genuine tail-range hypotheses on indexed sums.  They cannot
  be inferred from the four individual bounds above. -/
  even_range : ∀ x, toHalfDepthRows.evenExponent x ≤ 43
  odd_range : ∀ x, toHalfDepthRows.oddExponent x ≤ 42
  imbalance_relation :
    toHalfDepthRows.deltaA - toHalfDepthRows.deltaB = 4 ∨
      toHalfDepthRows.deltaA - toHalfDepthRows.deltaB = -4
  product_bound :
    -3 ≤ toHalfDepthRows.deltaA * toHalfDepthRows.deltaB ∧
      toHalfDepthRows.deltaA * toHalfDepthRows.deltaB ≤ 5

namespace Q67System

/-- Queryable corrected atom-D bounds.  In particular `P,Q` are allowed to
contain 43; only `R,S` stop at 42. -/
theorem corrected_half_depth_bounds (D : Q67System) :
    D.P ⊆ Finset.Icc 0 43 ∧ D.Q ⊆ Finset.Icc 0 43 ∧
      D.R ⊆ Finset.Icc 0 42 ∧ D.S ⊆ Finset.Icc 0 42 := by
  constructor
  · intro x hx
    simp [D.P_bound x hx]
  constructor
  · intro x hx
    simp [D.Q_bound x hx]
  constructor
  · intro x hx
    simp [D.R_bound x hx]
  · intro x hx
    simp [D.S_bound x hx]

def shape (D : Q67System) : Q67Shape :=
  if D.deltaA * D.deltaB = 5 then
    if D.deltaA < 0 then .negativeFive else .positiveFive
  else .productNegThree

/-- Receipt atom B, arithmetic part: up to side exchange the only rooted
imbalance/cardinality shapes are the two product-5 mirrors and product -3. -/
theorem three_shape_disjunction (D : Q67System) :
    ((D.deltaA = -1 ∧ D.deltaB = -5) ∨
      (D.deltaA = -5 ∧ D.deltaB = -1)) ∨
    ((D.deltaA = 1 ∧ D.deltaB = 5) ∨
      (D.deltaA = 5 ∧ D.deltaB = 1)) ∨
    D.deltaA * D.deltaB = -3 := by
  have hsideA := D.sideA_card
  have hsideB := D.sideB_card
  have hPA : D.P.card ≤ 9 := by omega
  have hQA : D.Q.card ≤ 9 := by omega
  have hprod := D.product_bound
  have himbalance := D.imbalance_relation
  have hAform : D.deltaA = 2 * (D.P.card : ℤ) - 9 := by
    simp only [HalfDepthRows.deltaA]
    omega
  have hBform : D.deltaB = 2 * (D.Q.card : ℤ) - 9 := by
    simp only [HalfDepthRows.deltaB]
    omega
  rw [hAform, hBform] at hprod himbalance ⊢
  rcases himbalance with himbalance | himbalance <;>
    interval_cases hP : D.P.card <;>
    norm_num at hprod himbalance ⊢ <;> omega

theorem complete_delta_shapes (D : Q67System) :
    (D.deltaA = -1 ∧ D.deltaB = -5) ∨
    (D.deltaA = -5 ∧ D.deltaB = -1) ∨
    (D.deltaA = 1 ∧ D.deltaB = 5) ∨
    (D.deltaA = 5 ∧ D.deltaB = 1) ∨
    (D.deltaA = 1 ∧ D.deltaB = -3) ∨
    (D.deltaA = -3 ∧ D.deltaB = 1) ∨
    (D.deltaA = 3 ∧ D.deltaB = -1) ∨
    (D.deltaA = -1 ∧ D.deltaB = 3) := by
  have hsideA := D.sideA_card
  have hsideB := D.sideB_card
  have hP : D.P.card ≤ 9 := by omega
  have hQ : D.Q.card ≤ 9 := by omega
  have hprod := D.product_bound
  have himbalance := D.imbalance_relation
  have hAform : D.deltaA = 2 * (D.P.card : ℤ) - 9 := by
    simp only [HalfDepthRows.deltaA]
    omega
  have hBform : D.deltaB = 2 * (D.Q.card : ℤ) - 9 := by
    simp only [HalfDepthRows.deltaB]
    omega
  rw [hAform, hBform] at hprod himbalance ⊢
  rcases himbalance with himbalance | himbalance <;>
    interval_cases hp : D.P.card <;>
    norm_num at hprod himbalance ⊢ <;> omega

/-- The dimensions attached to each oriented imbalance pair.  These lemmas
make the two product-five shift placements visibly distinct. -/
theorem dimensions_of_negative_five (D : Q67System)
    (hA : D.deltaA = -1) (hB : D.deltaB = -5) :
      D.P.card = 4 ∧ D.R.card = 5 ∧
      D.Q.card = 2 ∧ D.S.card = 7 := by
  have hsideA := D.sideA_card
  have hsideB := D.sideB_card
  simp only [HalfDepthRows.deltaA, HalfDepthRows.deltaB] at hA hB
  omega

theorem dimensions_of_positive_five (D : Q67System)
    (hA : D.deltaA = 1) (hB : D.deltaB = 5) :
      D.P.card = 5 ∧ D.R.card = 4 ∧
      D.Q.card = 7 ∧ D.S.card = 2 := by
  have hsideA := D.sideA_card
  have hsideB := D.sideB_card
  simp only [HalfDepthRows.deltaA, HalfDepthRows.deltaB] at hA hB
  omega

theorem dimensions_of_product_neg_three_representative (D : Q67System)
    (hA : D.deltaA = 1) (hB : D.deltaB = -3) :
      D.P.card = 5 ∧ D.R.card = 4 ∧
      D.Q.card = 3 ∧ D.S.card = 6 := by
  have hsideA := D.sideA_card
  have hsideB := D.sideB_card
  simp only [HalfDepthRows.deltaA, HalfDepthRows.deltaB] at hA hB
  omega

theorem product_five_one_hole (D : Q67System)
    (hp : D.deltaA * D.deltaB = 5) :
    (holes D.evenExponent 43).card = 1 ∧
      (holes D.oddExponent 42).card = 5 := by
  have hsizes := D.parity_block_size_identities
  have hecard : Fintype.card D.EvenIndex = 43 := by omega
  have hocard : Fintype.card D.OddIndex = 38 := by omega
  constructor
  · rw [holes_card D.evenExponent D.even_direct]
    · omega
    · exact D.even_range
  · rw [holes_card D.oddExponent D.odd_direct]
    · omega
    · exact D.odd_range

theorem product_neg_three_holes (D : Q67System)
    (hp : D.deltaA * D.deltaB = -3) :
    (holes D.oddExponent 42).card = 1 ∧
      (holes D.evenExponent 43).card = 5 := by
  have hsizes := D.parity_block_size_identities
  have hecard : Fintype.card D.EvenIndex = 39 := by omega
  have hocard : Fintype.card D.OddIndex = 42 := by omega
  constructor
  · rw [holes_card D.oddExponent D.odd_direct]
    · omega
    · exact D.odd_range
  · rw [holes_card D.evenExponent D.even_direct]
    · omega
    · exact D.even_range

/-- Exact atom-B hole presentation.  In the product-five branches the even
block has a unique nonconstant hole and the coupled odd block has five holes. -/
theorem product_five_exact_hole_system (D : Q67System)
    (hp : D.deltaA * D.deltaB = 5) :
    ∃ j ∈ Finset.Icc 1 43,
      holes D.evenExponent 43 = {j} ∧
      (holes D.oddExponent 42).card = 5 := by
  have hc := D.product_five_one_hole hp
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc.1
  refine ⟨j, ?_, hj, hc.2⟩
  have hjmem : j ∈ holes D.evenExponent 43 := by simp [hj]
  have hjI : j ∈ interval 43 := (Finset.mem_sdiff.mp hjmem).1
  have hjne : j ≠ 0 := by
    intro hzero
    subst j
    exact (Finset.mem_sdiff.mp hjmem).2 <| by
      let x : D.EvenIndex :=
        Sum.inl (⟨0, D.rootP⟩, ⟨0, D.rootQ⟩)
      exact Finset.mem_image.mpr
        ⟨x, Finset.mem_univ _, by simp [x, HalfDepthRows.evenExponent]⟩
  simpa [interval] using And.intro (by omega : 1 ≤ j)
    (Finset.mem_Icc.mp hjI).2

/-- In the product-minus-three branches the odd block has one hole (possibly
zero), while the even complementary block has five nonconstant holes. -/
theorem product_neg_three_exact_hole_system (D : Q67System)
    (hp : D.deltaA * D.deltaB = -3) :
    ∃ j ∈ Finset.Icc 0 42,
      holes D.oddExponent 42 = {j} ∧
      (holes D.evenExponent 43).card = 5 ∧
      0 ∉ holes D.evenExponent 43 := by
  have hc := D.product_neg_three_holes hp
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc.1
  refine ⟨j, ?_, hj, hc.2, ?_⟩
  · have hjmem : j ∈ holes D.oddExponent 42 := by simp [hj]
    exact (Finset.mem_sdiff.mp hjmem).1
  · intro hzero
    exact (Finset.mem_sdiff.mp hzero).2 <| by
      let x : D.EvenIndex :=
        Sum.inl (⟨0, D.rootP⟩, ⟨0, D.rootQ⟩)
      exact Finset.mem_image.mpr
        ⟨x, Finset.mem_univ _, by simp [x, HalfDepthRows.evenExponent]⟩

theorem zero_mem_odd_image_iff (D : Q67System) :
    0 ∈ imageSet D.oddExponent ↔ 0 ∈ D.R ∨ 0 ∈ D.S := by
  constructor
  · intro hmem
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp (by
      simpa only [imageSet] using hmem)
    rcases x with x | x
    · right
      simp only [HalfDepthRows.oddExponent] at hx
      have hz : x.2.1 = 0 := Nat.eq_zero_of_add_eq_zero_left hx
      simpa only [hz] using x.2.2
    · left
      simp only [HalfDepthRows.oddExponent] at hx
      have hz : x.1.1 = 0 := Nat.eq_zero_of_add_eq_zero_right hx
      simpa only [hz] using x.1.2
  · rintro (hR | hS)
    · let x : D.OddIndex :=
        Sum.inr (⟨0, hR⟩, ⟨0, D.rootQ⟩)
      exact Finset.mem_image.mpr
        ⟨x, Finset.mem_univ _, by simp [x, HalfDepthRows.oddExponent]⟩
    · let x : D.OddIndex :=
        Sum.inl (⟨0, D.rootP⟩, ⟨0, hS⟩)
      exact Finset.mem_image.mpr
        ⟨x, Finset.mem_univ _, by simp [x, HalfDepthRows.oddExponent]⟩

/-- The exact row-level boundary content behind receipt atom C.  The actual
tree adapter identifies the right-hand memberships with incidence of the
unique weight-two/weight-one edge and with the diameter path. -/
theorem product_five_boundary_memberships (D : Q67System) {j : ℕ}
    (hholes : holes D.evenExponent 43 = {j})
    (_hj : j ∈ Finset.Icc 1 43) :
    (j ≠ 1 ↔ 1 ∈ imageSet D.evenExponent) ∧
      (j ≠ 43 ↔ 43 ∈ imageSet D.evenExponent) := by
  constructor
  · calc
      j ≠ 1 ↔ 1 ∉ ({j} : Finset ℕ) := by simp [ne_comm]
      _ ↔ 1 ∉ holes D.evenExponent 43 := by rw [hholes]
      _ ↔ 1 ∈ imageSet D.evenExponent :=
        not_mem_holes_iff_mem_image _ (by simp [interval])
  · calc
      j ≠ 43 ↔ 43 ∉ ({j} : Finset ℕ) := by simp [ne_comm]
      _ ↔ 43 ∉ holes D.evenExponent 43 := by rw [hholes]
      _ ↔ 43 ∈ imageSet D.evenExponent :=
        not_mem_holes_iff_mem_image _ (by simp [interval])

theorem product_neg_three_boundary_membership (D : Q67System) {j : ℕ}
    (hholes : holes D.oddExponent 42 = {j})
    (_hj : j ∈ Finset.Icc 0 42) :
    j ≠ 0 ↔ 0 ∈ D.R ∨ 0 ∈ D.S := by
  calc
    j ≠ 0 ↔ 0 ∉ ({j} : Finset ℕ) := by simp [ne_comm]
    _ ↔ 0 ∉ holes D.oddExponent 42 := by rw [hholes]
    _ ↔ 0 ∈ imageSet D.oddExponent :=
      not_mem_holes_iff_mem_image _ (by simp [interval])
    _ ↔ 0 ∈ D.R ∨ 0 ∈ D.S := D.zero_mem_odd_image_iff

/-- Receipt equation (25), derived from the exact indexed image rather than
from collapsed support. -/
theorem negative_five_derivative_checksum (D : Q67System) {j : ℕ}
    (hA : D.deltaA = -1) (hB : D.deltaB = -5)
    (hj : j ∈ interval 43)
    (himage : imageSet D.evenExponent = interval 43 \ {j}) :
    2 * rowSum D.P + 4 * rowSum D.Q +
        7 * rowSum D.R + 5 * rowSum D.S + 35 = 946 - j := by
  have hdims := D.dimensions_of_negative_five hA hB
  have hfull : ∑ k ∈ interval 43, k = 946 := by decide
  have hremove := sum_sdiff_singleton_add hj
  have hindexed : (∑ x, D.evenExponent x) = 946 - j := by
    have himageSum := sum_imageSet_of_injective
      D.evenExponent D.even_direct
    rw [himage] at himageSum
    omega
  rw [D.evenExponent_sum] at hindexed
  rcases hdims with ⟨hP, hR, hQ, hS⟩
  rw [hP, hR, hQ, hS] at hindexed
  omega

/-- Receipt equation (26). -/
theorem product_neg_three_derivative_checksum (D : Q67System) {j : ℕ}
    (hA : D.deltaA = 1) (hB : D.deltaB = -3)
    (hj : j ∈ interval 42)
    (himage : imageSet D.oddExponent = interval 42 \ {j}) :
    6 * rowSum D.P + 5 * rowSum D.S +
        3 * rowSum D.R + 4 * rowSum D.Q = 903 - j := by
  have hdims := D.dimensions_of_product_neg_three_representative hA hB
  have hfull : ∑ k ∈ interval 42, k = 903 := by decide
  have hremove := sum_sdiff_singleton_add hj
  have hindexed : (∑ x, D.oddExponent x) = 903 - j := by
    have himageSum := sum_imageSet_of_injective
      D.oddExponent D.odd_direct
    rw [himage] at himageSum
    omega
  rw [D.oddExponent_sum] at hindexed
  rcases hdims with ⟨hP, hR, hQ, hS⟩
  rw [hP, hR, hQ, hS] at hindexed
  omega

/-- Receipt equation (27), including the minus sign caused by the shifted
odd-odd summand. -/
theorem product_five_alternating_checksum (D : Q67System) {j : ℕ}
    (hj : j ∈ interval 43)
    (himage : imageSet D.evenExponent = interval 43 \ {j}) :
    alternatingMass D.P * alternatingMass D.Q -
        alternatingMass D.R * alternatingMass D.S =
      (-1 : ℤ) ^ (j + 1) := by
  have hfull : ∑ k ∈ interval 43, (-1 : ℤ) ^ k = 0 := by
    decide
  have hremove := alternating_sdiff_singleton_add hj
  have hindexed : (∑ x, (-1 : ℤ) ^ D.evenExponent x) =
      -((-1 : ℤ) ^ j) := by
    have himageSum := alternating_imageSet_of_injective
      D.evenExponent D.even_direct
    rw [himage] at himageSum
    omega
  rw [D.evenExponent_alternating] at hindexed
  rw [pow_succ]
  norm_num
  exact hindexed

/-- Receipt equation (28). -/
theorem product_neg_three_alternating_checksum (D : Q67System) {j : ℕ}
    (hj : j ∈ interval 42)
    (himage : imageSet D.oddExponent = interval 42 \ {j}) :
    alternatingMass D.P * alternatingMass D.S +
        alternatingMass D.R * alternatingMass D.Q =
      1 - (-1 : ℤ) ^ j := by
  have hfull : ∑ k ∈ interval 42, (-1 : ℤ) ^ k = 1 := by
    decide
  have hremove := alternating_sdiff_singleton_add hj
  have hindexed : (∑ x, (-1 : ℤ) ^ D.oddExponent x) =
      1 - (-1 : ℤ) ^ j := by
    have himageSum := alternating_imageSet_of_injective
      D.oddExponent D.odd_direct
    rw [himage] at himageSum
    omega
  simpa [D.oddExponent_alternating] using hindexed

/-- Atom D in coupled form: once the finite hole sets are fixed, the two
coefficient systems are equivalent to exact indexed images.  This is a finite
row specification, not an enumeration or a tree-lift theorem. -/
theorem corrected_coupled_coefficient_reduction (D : Q67System)
    (HE HO : Finset ℕ) (hHE : HE ⊆ interval 43)
    (hHO : HO ⊆ interval 42) :
    ((∀ k, D.E k = if k ∈ interval 43 \ HE then 1 else 0) ∧
      (∀ k, D.O k = if k ∈ interval 42 \ HO then 1 else 0)) ↔
    (imageSet D.evenExponent = interval 43 \ HE ∧
      imageSet D.oddExponent = interval 42 \ HO) := by
  change
    ((∀ k, coefficient D.evenExponent k =
        if k ∈ interval 43 \ HE then 1 else 0) ∧
      (∀ k, coefficient D.oddExponent k =
        if k ∈ interval 42 \ HO then 1 else 0)) ↔ _
  rw [coefficient_system_iff_direct_image D.evenExponent 43 HE hHE,
    coefficient_system_iff_direct_image D.oddExponent 42 HO hHO]
  simp [D.even_direct, D.odd_direct]

end Q67System

structure Q66System extends HalfDepthRows where
  even_direct : Function.Injective toHalfDepthRows.evenExponent
  odd_direct : Function.Injective toHalfDepthRows.oddExponent
  all_bound : ∀ x, x ∈ P ∨ x ∈ R ∨ x ∈ Q ∨ x ∈ S → x ≤ 43
  /-- As at q=67, individual half-depth bounds do not imply sum-range. -/
  even_range : ∀ x, toHalfDepthRows.evenExponent x ≤ 43
  odd_range : ∀ x, toHalfDepthRows.oddExponent x ≤ 43
  imbalance_relation :
    toHalfDepthRows.deltaA + toHalfDepthRows.deltaB = 4 ∨
      toHalfDepthRows.deltaA + toHalfDepthRows.deltaB = -4
  product_cases :
    toHalfDepthRows.deltaA * toHalfDepthRows.deltaB = -5 ∨
      toHalfDepthRows.deltaA * toHalfDepthRows.deltaB = 3

namespace Q66System

theorem branch_shapes (D : Q66System) :
    D.deltaA * D.deltaB = -5 ∨ D.deltaA * D.deltaB = 3 :=
  D.product_cases

theorem complete_branch_delta_shapes (D : Q66System) :
    ((D.deltaA = 1 ∧ D.deltaB = -5) ∨
      (D.deltaA = 5 ∧ D.deltaB = -1) ∨
      (D.deltaA = -1 ∧ D.deltaB = 5) ∨
      (D.deltaA = -5 ∧ D.deltaB = 1)) ∨
    ((D.deltaA = 1 ∧ D.deltaB = 3) ∨
      (D.deltaA = 3 ∧ D.deltaB = 1) ∨
      (D.deltaA = -1 ∧ D.deltaB = -3) ∨
      (D.deltaA = -3 ∧ D.deltaB = -1)) := by
  have hsideA := D.sideA_card
  have hsideB := D.sideB_card
  have hP : D.P.card ≤ 9 := by omega
  have hQ : D.Q.card ≤ 9 := by omega
  have hproducts := D.product_cases
  have himbalance := D.imbalance_relation
  have hAform : D.deltaA = 2 * (D.P.card : ℤ) - 9 := by
    simp only [HalfDepthRows.deltaA]
    omega
  have hBform : D.deltaB = 2 * (D.Q.card : ℤ) - 9 := by
    simp only [HalfDepthRows.deltaB]
    omega
  rw [hAform, hBform] at hproducts himbalance ⊢
  rcases himbalance with himbalance | himbalance <;>
    interval_cases hp : D.P.card <;>
    norm_num at hproducts himbalance ⊢ <;> omega

theorem negative_five_dimensions (D : Q66System)
    (hA : D.deltaA = 1) (hB : D.deltaB = -5) :
      D.P.card = 5 ∧ D.R.card = 4 ∧
      D.Q.card = 2 ∧ D.S.card = 7 := by
  have hsideA := D.sideA_card
  have hsideB := D.sideB_card
  simp only [HalfDepthRows.deltaA, HalfDepthRows.deltaB] at hA hB
  omega

theorem positive_product_three_dimensions (D : Q66System)
    (hA : D.deltaA = 1) (hB : D.deltaB = 3) :
      D.P.card = 5 ∧ D.R.card = 4 ∧
      D.Q.card = 6 ∧ D.S.card = 3 := by
  have hsideA := D.sideA_card
  have hsideB := D.sideB_card
  simp only [HalfDepthRows.deltaA, HalfDepthRows.deltaB] at hA hB
  omega

theorem negative_product_three_dimensions (D : Q66System)
    (hA : D.deltaA = -1) (hB : D.deltaB = -3) :
      D.P.card = 4 ∧ D.R.card = 5 ∧
      D.Q.card = 3 ∧ D.S.card = 6 := by
  have hsideA := D.sideA_card
  have hsideB := D.sideB_card
  simp only [HalfDepthRows.deltaA, HalfDepthRows.deltaB] at hA hB
  omega

/-- Receipt atom E: exact one-hole and two-hole cardinalities of the two branches. -/
theorem branch_hole_counts (D : Q66System) :
    (D.deltaA * D.deltaB = -5 →
      (holes D.oddExponent 43).card = 1 ∧
        (holes D.evenExponent 43).card = 6) ∧
    (D.deltaA * D.deltaB = 3 →
      (holes D.evenExponent 43).card = 2 ∧
        (holes D.oddExponent 43).card = 5) := by
  have hsizes := D.parity_block_size_identities
  constructor <;> intro hp
  · have he : Fintype.card D.EvenIndex = 38 := by omega
    have ho : Fintype.card D.OddIndex = 43 := by omega
    constructor
    · rw [holes_card D.oddExponent D.odd_direct]
      · omega
      · exact D.odd_range
    · rw [holes_card D.evenExponent D.even_direct]
      · omega
      · exact D.even_range
  · have he : Fintype.card D.EvenIndex = 42 := by omega
    have ho : Fintype.card D.OddIndex = 39 := by omega
    constructor
    · rw [holes_card D.evenExponent D.even_direct]
      · omega
      · exact D.even_range
    · rw [holes_card D.oddExponent D.odd_direct]
      · omega
      · exact D.odd_range

/-- Atom E, including the exact allowed hole indices. -/
theorem negative_five_exact_holes (D : Q66System)
    (hp : D.deltaA * D.deltaB = -5) :
    ∃ j ∈ Finset.Icc 0 43,
      holes D.oddExponent 43 = {j} ∧
      (holes D.evenExponent 43).card = 6 ∧
      0 ∉ holes D.evenExponent 43 := by
  have hc := D.branch_hole_counts.1 hp
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc.1
  refine ⟨j, ?_, hj, hc.2, ?_⟩
  · have hjmem : j ∈ holes D.oddExponent 43 := by simp [hj]
    exact (Finset.mem_sdiff.mp hjmem).1
  · intro hzero
    exact (Finset.mem_sdiff.mp hzero).2 <| by
      let x : D.EvenIndex :=
        Sum.inl (⟨0, D.rootP⟩, ⟨0, D.rootQ⟩)
      exact Finset.mem_image.mpr
        ⟨x, Finset.mem_univ _, by simp [x, HalfDepthRows.evenExponent]⟩

theorem product_three_exact_holes (D : Q66System)
    (hp : D.deltaA * D.deltaB = 3) :
    ∃ j₁ j₂ : ℕ,
      j₁ ∈ Finset.Icc 1 43 ∧ j₂ ∈ Finset.Icc 1 43 ∧
      j₁ ≠ j₂ ∧ holes D.evenExponent 43 = {j₁, j₂} ∧
      (holes D.oddExponent 43).card = 5 := by
  have hc := D.branch_hole_counts.2 hp
  have htwo := Finset.card_eq_two.mp hc.1
  obtain ⟨j₁, j₂, hjne, hj⟩ := htwo
  have hmem₁ : j₁ ∈ holes D.evenExponent 43 := by simp [hj]
  have hmem₂ : j₂ ∈ holes D.evenExponent 43 := by simp [hj]
  have hnonzero : ∀ j ∈ holes D.evenExponent 43, j ≠ 0 := by
    intro j hjh hzero
    subst j
    exact (Finset.mem_sdiff.mp hjh).2 <| by
      let x : D.EvenIndex :=
        Sum.inl (⟨0, D.rootP⟩, ⟨0, D.rootQ⟩)
      exact Finset.mem_image.mpr
        ⟨x, Finset.mem_univ _, by simp [x, HalfDepthRows.evenExponent]⟩
  refine ⟨j₁, j₂, ?_, ?_, hjne, hj, hc.2⟩
  · have hI := (Finset.mem_sdiff.mp hmem₁).1
    exact Finset.mem_Icc.mpr
      ⟨Nat.one_le_iff_ne_zero.mpr (hnonzero j₁ hmem₁),
        (Finset.mem_Icc.mp hI).2⟩
  · have hI := (Finset.mem_sdiff.mp hmem₂).1
    exact Finset.mem_Icc.mpr
      ⟨Nat.one_le_iff_ne_zero.mpr (hnonzero j₂ hmem₂),
        (Finset.mem_Icc.mp hI).2⟩

theorem zero_mem_odd_image_iff (D : Q66System) :
    0 ∈ imageSet D.oddExponent ↔ 0 ∈ D.R ∨ 0 ∈ D.S := by
  constructor
  · intro hmem
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp (by
      simpa only [imageSet] using hmem)
    rcases x with x | x
    · right
      simp only [HalfDepthRows.oddExponent] at hx
      have hz : x.2.1 = 0 := Nat.eq_zero_of_add_eq_zero_left hx
      simpa only [hz] using x.2.2
    · left
      simp only [HalfDepthRows.oddExponent] at hx
      have hz : x.1.1 = 0 := Nat.eq_zero_of_add_eq_zero_right hx
      simpa only [hz] using x.1.2
  · rintro (hR | hS)
    · let x : D.OddIndex :=
        Sum.inr (⟨0, hR⟩, ⟨0, D.rootQ⟩)
      exact Finset.mem_image.mpr
        ⟨x, Finset.mem_univ _, by simp [x, HalfDepthRows.oddExponent]⟩
    · let x : D.OddIndex :=
        Sum.inl (⟨0, D.rootP⟩, ⟨0, hS⟩)
      exact Finset.mem_image.mpr
        ⟨x, Finset.mem_univ _, by simp [x, HalfDepthRows.oddExponent]⟩

theorem negative_five_boundary_memberships (D : Q66System) {j : ℕ}
    (hholes : holes D.oddExponent 43 = {j})
    (_hj : j ∈ Finset.Icc 0 43) :
    (j ≠ 0 ↔ 0 ∈ D.R ∨ 0 ∈ D.S) ∧
      (j ≠ 43 ↔ 43 ∈ imageSet D.oddExponent) := by
  constructor
  · calc
      j ≠ 0 ↔ 0 ∉ ({j} : Finset ℕ) := by simp [ne_comm]
      _ ↔ 0 ∉ holes D.oddExponent 43 := by rw [hholes]
      _ ↔ 0 ∈ imageSet D.oddExponent :=
        not_mem_holes_iff_mem_image _ (by simp [interval])
      _ ↔ 0 ∈ D.R ∨ 0 ∈ D.S := D.zero_mem_odd_image_iff
  · calc
      j ≠ 43 ↔ 43 ∉ ({j} : Finset ℕ) := by simp [ne_comm]
      _ ↔ 43 ∉ holes D.oddExponent 43 := by rw [hholes]
      _ ↔ 43 ∈ imageSet D.oddExponent :=
        not_mem_holes_iff_mem_image _ (by simp [interval])

theorem product_three_low_boundary_membership (D : Q66System)
    {j₁ j₂ : ℕ} (hholes : holes D.evenExponent 43 = {j₁, j₂})
    (_hj₁ : j₁ ∈ Finset.Icc 1 43) (_hj₂ : j₂ ∈ Finset.Icc 1 43) :
    (1 ∉ ({j₁, j₂} : Finset ℕ)) ↔
      1 ∈ imageSet D.evenExponent := by
  calc
    1 ∉ ({j₁, j₂} : Finset ℕ) ↔
        1 ∉ holes D.evenExponent 43 := by rw [hholes]
    _ ↔ 1 ∈ imageSet D.evenExponent :=
      not_mem_holes_iff_mem_image _ (by simp [interval])

theorem coupled_coefficient_reduction (D : Q66System)
    (HE HO : Finset ℕ) (hHE : HE ⊆ interval 43)
    (hHO : HO ⊆ interval 43) :
    ((∀ k, D.E k = if k ∈ interval 43 \ HE then 1 else 0) ∧
      (∀ k, D.O k = if k ∈ interval 43 \ HO then 1 else 0)) ↔
    (imageSet D.evenExponent = interval 43 \ HE ∧
      imageSet D.oddExponent = interval 43 \ HO) := by
  change
    ((∀ k, coefficient D.evenExponent k =
        if k ∈ interval 43 \ HE then 1 else 0) ∧
      (∀ k, coefficient D.oddExponent k =
        if k ∈ interval 43 \ HO then 1 else 0)) ↔ _
  rw [coefficient_system_iff_direct_image D.evenExponent 43 HE hHE,
    coefficient_system_iff_direct_image D.oddExponent 43 HO hHO]
  simp [D.even_direct, D.odd_direct]

end Q66System

/-! ## Receipt atoms F--G: raw seven-hole direct sum -/

structure SevenHoleRows where
  DA : Finset ℕ
  DB : Finset ℕ
  cardA : DA.card = 9
  cardB : DB.card = 9
  zeroA : 0 ∈ DA
  zeroB : 0 ∈ DB
  add_injective : Function.Injective
    (fun x : ↥DA × ↥DB => x.1.1 + x.2.1)
  sum_le : ∀ a ∈ DA, ∀ b ∈ DB, a + b ≤ 87

namespace SevenHoleRows

def addExponent (D : SevenHoleRows) (x : ↥D.DA × ↥D.DB) : ℕ :=
  x.1.1 + x.2.1

def H (D : SevenHoleRows) : Finset ℕ := holes D.addExponent 87

theorem H_card (D : SevenHoleRows) : D.H.card = 7 := by
  rw [H, holes_card D.addExponent D.add_injective]
  · simp [D.cardA, D.cardB]
  · intro x
    exact D.sum_le _ x.1.2 _ x.2.2

theorem H_subset_one_87 (D : SevenHoleRows) :
    D.H ⊆ Finset.Icc 1 87 := by
  intro h hh
  have hI : h ∈ interval 87 := (Finset.mem_sdiff.mp hh).1
  have hnimg := (Finset.mem_sdiff.mp hh).2
  rw [Finset.mem_Icc]
  refine ⟨?_, (Finset.mem_Icc.mp hI).2⟩
  by_contra hz
  have : h = 0 := by omega
  subst h
  apply hnimg
  exact Finset.mem_image.mpr
    ⟨(⟨0, D.zeroA⟩, ⟨0, D.zeroB⟩), Finset.mem_univ _, by simp [addExponent]⟩

/-- Receipt atom F: coefficientwise seven-hole identity. -/
theorem coefficient_identity (D : SevenHoleRows) (k : ℕ) :
    coefficient D.addExponent k =
      if k ∈ interval 87 \ D.H then 1 else 0 := by
  apply hole_coefficient_iff D.addExponent D.add_injective
  intro x
  exact D.sum_le _ x.1.2 _ x.2.2

theorem difference_rigidity (D : SevenHoleRows)
    {a a' b b' : ℕ} (ha : a ∈ D.DA) (ha' : a' ∈ D.DA)
    (hb : b ∈ D.DB) (hb' : b' ∈ D.DB)
    (hdiff : (a : ℤ) - a' = (b : ℤ) - b') :
    a = a' ∧ b = b' := by
  have hsum : a + b' = a' + b := by omega
  let x : ↥D.DA × ↥D.DB := (⟨a, ha⟩, ⟨b', hb'⟩)
  let y : ↥D.DA × ↥D.DB := (⟨a', ha'⟩, ⟨b, hb⟩)
  have hpair : x = y := D.add_injective (by simpa [x, y] using hsum)
  have hfirst : a = a' := congrArg (fun z => z.1.1) hpair
  have hsecond : b' = b := congrArg (fun z => z.2.1) hpair
  exact ⟨hfirst, hsecond.symm⟩

theorem row_intersection_eq_zero (D : SevenHoleRows) :
    D.DA ∩ D.DB = {0} := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨hxA, hxB⟩
    have hrig := D.difference_rigidity hxA D.zeroA hxB D.zeroB
      (by norm_num : (x : ℤ) - 0 = (x : ℤ) - 0)
    exact hrig.1
  · intro hx
    subst x
    exact ⟨D.zeroA, D.zeroB⟩

def differenceSet (S : Finset ℕ) : Finset ℤ :=
  (S ×ˢ S).image fun x => (x.1 : ℤ) - x.2

/-- The full ordered difference-set assertion in receipt atom F. -/
theorem difference_intersection_eq_zero (D : SevenHoleRows) :
    differenceSet D.DA ∩ differenceSet D.DB = {0} := by
  ext z
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨hzA, hzB⟩
    rcases Finset.mem_image.mp (by simpa only [differenceSet] using hzA) with
      ⟨aa, haa, hza⟩
    rcases Finset.mem_image.mp (by simpa only [differenceSet] using hzB) with
      ⟨bb, hbb, hzb⟩
    have hrig := D.difference_rigidity
      (Finset.mem_product.mp haa).1 (Finset.mem_product.mp haa).2
      (Finset.mem_product.mp hbb).1 (Finset.mem_product.mp hbb).2
      (by omega)
    omega
  · intro hz
    subst z
    constructor
    · change 0 ∈ differenceSet D.DA
      apply Finset.mem_image.mpr
      exact ⟨(0, 0), by simp [D.zeroA], by norm_num⟩
    · change 0 ∈ differenceSet D.DB
      apply Finset.mem_image.mpr
      exact ⟨(0, 0), by simp [D.zeroB], by norm_num⟩

/-- Receipt atom F checksum; this exact identity implies `sum H ≡ 3 mod 9`. -/
theorem hole_sum_identity (D : SevenHoleRows) :
    ∑ h ∈ D.H, h =
      3828 - 9 * ((∑ a ∈ D.DA, a) + (∑ b ∈ D.DB, b)) := by
  -- The image is direct, so summing its 81 exponents counts every row
  -- entry nine times.  The hole set is its complement in `[0,87]`.
  have himage : (imageSet D.addExponent).card = 81 := by
    rw [imageSet]
    change (Finset.univ.image
      (fun x : ↥D.DA × ↥D.DB => x.1.1 + x.2.1)).card = 81
    rw [Finset.card_image_of_injective _ D.add_injective, Finset.card_univ]
    simp [D.cardA, D.cardB]
  have hpartition : imageSet D.addExponent ∪ D.H = interval 87 := by
    ext k
    by_cases hk : k ∈ imageSet D.addExponent
    · have hkI : k ∈ interval 87 := by
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hk
        rw [interval, Finset.mem_Icc]
        exact ⟨by omega, by
          change x.1.1 + x.2.1 ≤ 87
          exact D.sum_le _ x.1.2 _ x.2.2⟩
      simp [H, holes, hk, hkI]
    · simp [H, holes, hk]
  have hdis : Disjoint (imageSet D.addExponent) D.H := by
    rw [Finset.disjoint_left]
    intro k hk hkh
    exact (Finset.mem_sdiff.mp hkh).2 hk
  have hsumUniverse : ∑ k ∈ interval 87, k = 3828 := by decide
  have hsumImage : ∑ k ∈ imageSet D.addExponent, k =
      9 * ((∑ a ∈ D.DA, a) + (∑ b ∈ D.DB, b)) := by
    calc
      (∑ k ∈ imageSet D.addExponent, k) =
          ∑ x, D.addExponent x :=
        sum_imageSet_of_injective D.addExponent D.add_injective
      _ = D.DB.card * rowSum D.DA +
          D.DA.card * rowSum D.DB := sum_add_product D.DA D.DB
      _ = 9 * ((∑ a ∈ D.DA, a) + (∑ b ∈ D.DB, b)) := by
        simp [rowSum, D.cardA, D.cardB]
        ring
  rw [← hsumUniverse, ← hpartition, Finset.sum_union hdis, hsumImage]
  omega

theorem hole_sum_mod_nine (D : SevenHoleRows) :
    (∑ h ∈ D.H, h) % 9 = 3 := by
  have hnonempty : D.H.Nonempty := Finset.card_pos.mp (by
    rw [D.H_card]
    norm_num)
  have hsumpos : 0 < ∑ h ∈ D.H, h :=
    Finset.sum_pos
      (fun h hh => (Finset.mem_Icc.mp (D.H_subset_one_87 hh)).1)
      hnonempty
  rw [D.hole_sum_identity] at hsumpos ⊢
  omega

/-- Specialized receipt congruence (45). -/
theorem six_even_one_odd_congruence
    (K : Finset ℕ) (j : ℕ) (_hK : K.card = 6)
    (hraw : (∑ k ∈ K, 2 * k) + (2 * j + 1) ≡ 3 [MOD 9]) :
    (∑ k ∈ K, k) + j ≡ 1 [MOD 9] := by
  rw [Nat.ModEq] at hraw ⊢
  have hKmul : (∑ k ∈ K, 2 * k) = 2 * (∑ k ∈ K, k) :=
    (Finset.mul_sum K (fun k : ℕ => k) 2).symm
  rw [hKmul] at hraw
  omega

/-- Specialized receipt congruence (46). -/
theorem two_even_five_odd_congruence
    (J H5 : Finset ℕ) (_hJ : J.card = 2) (hH : H5.card = 5)
    (hraw : (∑ j ∈ J, 2 * j) + (∑ h ∈ H5, (2 * h + 1)) ≡ 3 [MOD 9]) :
    (∑ j ∈ J, j) + (∑ h ∈ H5, h) ≡ 8 [MOD 9] := by
  rw [Nat.ModEq] at hraw ⊢
  have hsplit : (∑ h ∈ H5, (2 * h + 1)) =
      (∑ h ∈ H5, 2 * h) + (∑ h ∈ H5, 1) :=
    by simpa only [] using (Finset.sum_add_distrib (s := H5)
      (f := fun h : ℕ => 2 * h) (g := fun _h : ℕ => 1))
  have hJmul : (∑ j ∈ J, 2 * j) = 2 * (∑ j ∈ J, j) :=
    (Finset.mul_sum J (fun j : ℕ => j) 2).symm
  have hHmul : (∑ h ∈ H5, 2 * h) = 2 * (∑ h ∈ H5, h) :=
    (Finset.mul_sum H5 (fun h : ℕ => h) 2).symm
  have hHone : (∑ _h ∈ H5, 1) = H5.card := by simp
  rw [hsplit, hJmul, hHmul, hHone, hH] at hraw
  norm_num at hraw
  omega

def residueCount (S : Finset ℕ) (m : ℕ) (r : ZMod m) : ℕ :=
  (S.filter fun x : ℕ => (x : ZMod m) = r).card

abbrev ResidueElement (S : Finset ℕ) (m : ℕ) (r : ZMod m) :=
  ↥(S.filter fun x : ℕ => (x : ZMod m) = r)

abbrev ResiduePair (D : SevenHoleRows) (m : ℕ) (r : ZMod m) :=
  ↥((D.DA ×ˢ D.DB).filter fun x : ℕ × ℕ =>
    ((x.1 + x.2 : ℕ) : ZMod m) = r)

private theorem prod_heq_of_heq
    {α α' β β' : Type} {a : α} {a' : α'} {b : β} {b' : β'}
    (ha : a ≍ a') (hb : b ≍ b') : (a, b) ≍ (a', b') := by
  cases ha
  cases hb
  rfl

def cyclicConvolution (D : SevenHoleRows) (m : ℕ) [NeZero m]
    (r : ZMod m) : ℕ :=
  ∑ i : ZMod m,
    residueCount D.DA m i * residueCount D.DB m (r - i)

/-- The sigma type behind cyclic convolution is exactly the residue-filtered
Cartesian product.  This prevents a collapsed-support interpretation. -/
noncomputable def convolutionEquiv (D : SevenHoleRows) (m : ℕ) [NeZero m]
    (r : ZMod m) :
    (Σ i : ZMod m,
      ResidueElement D.DA m i × ResidueElement D.DB m (r - i)) ≃
      ResiduePair D m r where
  toFun x := by
    refine ⟨(x.2.1.1, x.2.2.1), ?_⟩
    rw [Finset.mem_filter]
    constructor
    · exact Finset.mem_product.mpr
        ⟨(Finset.mem_filter.mp x.2.1.2).1,
          (Finset.mem_filter.mp x.2.2.2).1⟩
    · have hsum : (x.2.1.1 : ZMod m) + (x.2.2.1 : ZMod m) = r := by
        rw [(Finset.mem_filter.mp x.2.1.2).2,
          (Finset.mem_filter.mp x.2.2.2).2]
        abel
      simpa only [Nat.cast_add] using hsum
  invFun x := by
    let i : ZMod m := (x.1.1 : ZMod m)
    have hA : x.1.1 ∈ D.DA :=
      (Finset.mem_product.mp (Finset.mem_filter.mp x.2).1).1
    have hB : x.1.2 ∈ D.DB :=
      (Finset.mem_product.mp (Finset.mem_filter.mp x.2).1).2
    have hsum : (x.1.1 : ZMod m) + (x.1.2 : ZMod m) = r :=
      by simpa only [Nat.cast_add] using (Finset.mem_filter.mp x.2).2
    refine ⟨i,
      ⟨x.1.1, Finset.mem_filter.mpr ⟨hA, rfl⟩⟩,
      ⟨x.1.2, Finset.mem_filter.mpr ⟨hB, ?_⟩⟩⟩
    change (x.1.2 : ZMod m) = r - (x.1.1 : ZMod m)
    rw [eq_sub_iff_add_eq]
    simpa [add_comm] using hsum
  left_inv x := by
    rcases x with ⟨i, a, b⟩
    have hi : (a.1 : ZMod m) = i := (Finset.mem_filter.mp a.2).2
    let a' : ResidueElement D.DA m (a.1 : ZMod m) :=
      ⟨a.1, Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp a.2).1, rfl⟩⟩
    let b' : ResidueElement D.DB m (r - (a.1 : ZMod m)) :=
      ⟨b.1, Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp b.2).1, by
          simpa only [hi] using (Finset.mem_filter.mp b.2).2⟩⟩
    apply Sigma.ext
    · exact hi
    · change (a', b') ≍ (a, b)
      have ha : a' ≍ a :=
        (Subtype.heq_iff_coe_eq (fun z => by simp only [Finset.mem_filter, hi])).2 rfl
      have hb : b' ≍ b :=
        (Subtype.heq_iff_coe_eq (fun z => by simp only [Finset.mem_filter, hi])).2 rfl
      exact prod_heq_of_heq ha hb
  right_inv x := by
    apply Subtype.ext
    rfl

theorem cyclicConvolution_eq_pair_count (D : SevenHoleRows)
    (m : ℕ) [NeZero m] (r : ZMod m) :
    D.cyclicConvolution m r = Fintype.card (ResiduePair D m r) := by
  rw [cyclicConvolution]
  calc
    (∑ i : ZMod m,
        residueCount D.DA m i * residueCount D.DB m (r - i)) =
        Fintype.card (Σ i : ZMod m,
          ResidueElement D.DA m i × ResidueElement D.DB m (r - i)) := by
      rw [Fintype.card_sigma]
      apply Finset.sum_congr rfl
      intro i _
      simp [residueCount]
    _ = Fintype.card (ResiduePair D m r) :=
      Fintype.card_congr (convolutionEquiv D m r)

private theorem raw_sum_injective (D : SevenHoleRows) :
    Set.InjOn (fun x : ℕ × ℕ => x.1 + x.2) (D.DA ×ˢ D.DB) := by
  intro x hx y hy hsum
  have hx' : x.1 ∈ D.DA ∧ x.2 ∈ D.DB := by simpa using hx
  have hy' : y.1 ∈ D.DA ∧ y.2 ∈ D.DB := by simpa using hy
  let xs : ↥D.DA × ↥D.DB :=
    (⟨x.1, hx'.1⟩, ⟨x.2, hx'.2⟩)
  let ys : ↥D.DA × ↥D.DB :=
    (⟨y.1, hy'.1⟩, ⟨y.2, hy'.2⟩)
  have hxy : xs = ys := D.add_injective (by simpa [xs, ys] using hsum)
  exact Prod.ext
    (congrArg (fun z => z.1.1) hxy)
    (congrArg (fun z => z.2.1) hxy)

private theorem filtered_pair_image (D : SevenHoleRows)
    (m : ℕ) (r : ZMod m) :
    (((D.DA ×ˢ D.DB).filter fun x : ℕ × ℕ =>
        ((x.1 + x.2 : ℕ) : ZMod m) = r).image
      (fun x => x.1 + x.2)) =
      (imageSet D.addExponent).filter fun k : ℕ => (k : ZMod m) = r := by
  ext k
  constructor
  · intro hk
    rcases Finset.mem_image.mp hk with ⟨x, hx, rfl⟩
    have hx' := Finset.mem_filter.mp hx
    rw [Finset.mem_filter]
    refine ⟨?_, hx'.2⟩
    let y : ↥D.DA × ↥D.DB :=
      (⟨x.1, (Finset.mem_product.mp hx'.1).1⟩,
        ⟨x.2, (Finset.mem_product.mp hx'.1).2⟩)
    exact Finset.mem_image.mpr
      ⟨y, Finset.mem_univ _, by simp [y, addExponent]⟩
  · intro hk
    have hk' := Finset.mem_filter.mp hk
    rcases Finset.mem_image.mp hk'.1 with ⟨y, _, hy⟩
    refine Finset.mem_image.mpr ⟨(y.1.1, y.2.1), ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_product.mpr ⟨y.1.2, y.2.2⟩, ?_⟩
      have hsum : (y.1.1 : ZMod m) + (y.2.1 : ZMod m) = r := by
        calc
          (y.1.1 : ZMod m) + (y.2.1 : ZMod m) =
              ((D.addExponent y : ℕ) : ZMod m) := by
            simp only [addExponent, Nat.cast_add]
          _ = (k : ZMod m) := by rw [hy]
          _ = r := hk'.2
      simpa only [Nat.cast_add] using hsum
    · simpa [addExponent] using hy

theorem pair_residue_count_eq_image_residue (D : SevenHoleRows)
    (m : ℕ) (r : ZMod m) :
    Fintype.card (ResiduePair D m r) =
      residueCount (imageSet D.addExponent) m r := by
  rw [Fintype.card_coe, residueCount]
  let P := (D.DA ×ˢ D.DB).filter fun x : ℕ × ℕ =>
    ((x.1 + x.2 : ℕ) : ZMod m) = r
  have hcard : (P.image fun x => x.1 + x.2).card = P.card := by
    have hsubset : (↑P : Set (ℕ × ℕ)) ⊆
        (↑D.DA : Set ℕ) ×ˢ (↑D.DB : Set ℕ) := by
      intro x hx
      have hxprod := Finset.mem_product.mp (Finset.mem_filter.mp hx).1
      exact ⟨hxprod.1, hxprod.2⟩
    exact Finset.card_image_of_injOn
      (Set.InjOn.mono hsubset D.raw_sum_injective)
  rw [D.filtered_pair_image m r] at hcard
  simpa only [P] using hcard.symm

private theorem residueCount_union (A B : Finset ℕ) (m : ℕ)
    (r : ZMod m) (hdis : Disjoint A B) :
    residueCount (A ∪ B) m r =
      residueCount A m r + residueCount B m r := by
  have hdis' : Disjoint
      (A.filter fun x : ℕ => (x : ZMod m) = r)
      (B.filter fun x : ℕ => (x : ZMod m) = r) :=
    hdis.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  change ((A ∪ B).filter fun x : ℕ => (x : ZMod m) = r).card =
    (A.filter fun x : ℕ => (x : ZMod m) = r).card +
      (B.filter fun x : ℕ => (x : ZMod m) = r).card
  rw [Finset.filter_union, Finset.card_union_of_disjoint hdis']

private theorem named_interval_residue_count (m : ℕ)
    (hm : m = 4 ∨ m = 8 ∨ m = 11) (r : ZMod m) :
    residueCount (interval 87) m r = 88 / m := by
  rcases hm with rfl | rfl | rfl <;> fin_cases r <;>
    norm_num [residueCount, interval] <;> decide

/-- Receipt atom G in the intrinsic `ZMod m` form.  The convolution counts
indexed pairs, and the hole count supplies the exact residue deficit. -/
theorem residue_convolution (D : SevenHoleRows) (m : ℕ)
    [NeZero m] (hm : m = 4 ∨ m = 8 ∨ m = 11) (r : ZMod m) :
    D.cyclicConvolution m r + residueCount D.H m r = 88 / m := by
  have hsub : imageSet D.addExponent ⊆ interval 87 := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨x, _, rfl⟩
    rw [interval, Finset.mem_Icc]
    exact ⟨by omega, by
      change x.1.1 + x.2.1 ≤ 87
      exact D.sum_le _ x.1.2 _ x.2.2⟩
  have hpart : imageSet D.addExponent ∪ D.H = interval 87 := by
    simp [H, holes, Finset.union_sdiff_of_subset hsub]
  have hdis : Disjoint (imageSet D.addExponent) D.H := by
    exact Finset.disjoint_left.mpr fun k hk hkh =>
      (Finset.mem_sdiff.mp hkh).2 hk
  have hres := residueCount_union (imageSet D.addExponent) D.H m r hdis
  rw [hpart] at hres
  rw [D.cyclicConvolution_eq_pair_count,
    D.pair_residue_count_eq_image_residue]
  rw [← hres]
  exact named_interval_residue_count m hm r

end SevenHoleRows

/-! ## Receipt atom G: depth-span arithmetic -/

theorem depth_span_bounds
    (a7 a8 b7 b8 : ℕ)
    (ha : 36 ≤ a7 + a8) (hb : 36 ≤ b7 + b8)
    (haOrder : a7 < a8) (hbOrder : b7 < b8)
    (hcross : a8 + b8 ≤ 87) :
    19 ≤ a8 ∧ 19 ≤ b8 ∧ a8 + b8 ≤ 87 := by omega

/-! ## Receipt atom H: Gaussian mod-4 norm prefilter -/

/-- Squared Gaussian character norm of a mod-four count row. -/
def gaussianNorm (d0 d1 d2 d3 : ℕ) : ℤ :=
  ((d0 : ℤ) - d2) ^ 2 + ((d1 : ℤ) - d3) ^ 2

private theorem even_odd_square_norm
    {u v : ℤ} (hu : Even u) (hv : Odd v) :
    0 < u ^ 2 + v ^ 2 ∧ (u ^ 2 + v ^ 2) % 4 = 1 := by
  rcases hu with ⟨a, ha⟩
  rcases hv with ⟨b, hb⟩
  have hvne : v ≠ 0 := by
    rw [hb]
    omega
  constructor
  · nlinarith [sq_nonneg u, sq_pos_of_ne_zero hvne]
  · have hform : u ^ 2 + v ^ 2 =
        4 * (a ^ 2 + b ^ 2 + b) + 1 := by
      rw [ha, hb]
      ring
    rw [hform, Int.add_emod, Int.mul_emod]
    norm_num

theorem gaussianNorm_pos_mod_four
    (d0 d1 d2 d3 : ℕ) (hsum : d0 + d1 + d2 + d3 = 9) :
    0 < gaussianNorm d0 d1 d2 d3 ∧
      gaussianNorm d0 d1 d2 d3 % 4 = 1 := by
  let u : ℤ := (d0 : ℤ) - d2
  let v : ℤ := (d1 : ℤ) - d3
  have huv : u + v = 2 * ((d0 : ℤ) + d1) - 9 := by
    dsimp [u, v]
    omega
  rcases Int.even_or_odd u with hu | hu <;>
    rcases Int.even_or_odd v with hv | hv
  · rcases hu with ⟨a, ha⟩
    rcases hv with ⟨b, hb⟩
    omega
  · simpa [gaussianNorm, u, v] using even_odd_square_norm hu hv
  · have h := even_odd_square_norm hv hu
    simpa [gaussianNorm, u, v, add_comm] using h
  · rcases hu with ⟨a, ha⟩
    rcases hv with ⟨b, hb⟩
    omega

/-- Gaussian norm multiplicativity in the exact real/imaginary coordinates
used after evaluating the seven-hole identity at `i`. -/
theorem gaussian_norm_multiplicative
    (uA vA uB vB hReal hImag : ℤ)
    (hreal : uA * uB - vA * vB = -hReal)
    (himag : uA * vB + vA * uB = -hImag) :
    (uA ^ 2 + vA ^ 2) * (uB ^ 2 + vB ^ 2) =
      hReal ^ 2 + hImag ^ 2 := by
  calc
    (uA ^ 2 + vA ^ 2) * (uB ^ 2 + vB ^ 2) =
        (uA * uB - vA * vB) ^ 2 +
          (uA * vB + vA * uB) ^ 2 := by ring
    _ = (-hReal) ^ 2 + (-hImag) ^ 2 := by rw [hreal, himag]
    _ = hReal ^ 2 + hImag ^ 2 := by ring

private theorem sum_zmod_four (f : ZMod 4 → ℕ) :
    (∑ i : ZMod 4, f i) = f 0 + f 1 + f 2 + f 3 := by
  change (∑ i : Fin 4, f i) = _
  simp [Fin.sum_univ_succ, add_assoc]

private theorem zmod_four_neg_one : (-1 : ZMod 4) = 3 := by decide
private theorem zmod_four_neg_two : (-2 : ZMod 4) = 2 := by decide
private theorem zmod_four_neg_three : (-3 : ZMod 4) = 1 := by decide

/-- The modulus-four convolution evaluated in the real Gaussian coordinate.
This is the missing bridge from atom G's residue equations to atom H. -/
theorem SevenHoleRows.gaussian_real_equation (D : SevenHoleRows) :
    ((residueCount D.DA 4 0 : ℤ) - residueCount D.DA 4 2) *
        ((residueCount D.DB 4 0 : ℤ) - residueCount D.DB 4 2) -
      ((residueCount D.DA 4 1 : ℤ) - residueCount D.DA 4 3) *
        ((residueCount D.DB 4 1 : ℤ) - residueCount D.DB 4 3) =
      -((residueCount D.H 4 0 : ℤ) - residueCount D.H 4 2) := by
  have h0 := D.residue_convolution 4 (Or.inl rfl) (0 : ZMod 4)
  have h2 := D.residue_convolution 4 (Or.inl rfl) (2 : ZMod 4)
  simp only [SevenHoleRows.cyclicConvolution, sum_zmod_four] at h0 h2
  norm_num at h0 h2
  simp only [zmod_four_neg_one, zmod_four_neg_two,
    zmod_four_neg_three] at h0 h2
  have h0Z := congrArg (fun x : ℕ => (x : ℤ)) h0
  have h2Z := congrArg (fun x : ℕ => (x : ℤ)) h2
  push_cast at h0Z h2Z
  ring_nf at h0Z h2Z ⊢
  omega

/-- The corresponding imaginary Gaussian coordinate. -/
theorem SevenHoleRows.gaussian_imag_equation (D : SevenHoleRows) :
    ((residueCount D.DA 4 0 : ℤ) - residueCount D.DA 4 2) *
        ((residueCount D.DB 4 1 : ℤ) - residueCount D.DB 4 3) +
      ((residueCount D.DA 4 1 : ℤ) - residueCount D.DA 4 3) *
        ((residueCount D.DB 4 0 : ℤ) - residueCount D.DB 4 2) =
      -((residueCount D.H 4 1 : ℤ) - residueCount D.H 4 3) := by
  have h1 := D.residue_convolution 4 (Or.inl rfl) (1 : ZMod 4)
  have h3 := D.residue_convolution 4 (Or.inl rfl) (3 : ZMod 4)
  simp only [SevenHoleRows.cyclicConvolution, sum_zmod_four] at h1 h3
  norm_num at h1 h3
  simp only [zmod_four_neg_one, zmod_four_neg_two] at h1 h3
  have h1Z := congrArg (fun x : ℕ => (x : ℤ)) h1
  have h3Z := congrArg (fun x : ℕ => (x : ℤ)) h3
  push_cast at h1Z h3Z
  ring_nf at h1Z h3Z ⊢
  omega

theorem SevenHoleRows.gaussian_norm_product (D : SevenHoleRows) :
    gaussianNorm (residueCount D.DA 4 0) (residueCount D.DA 4 1)
        (residueCount D.DA 4 2) (residueCount D.DA 4 3) *
      gaussianNorm (residueCount D.DB 4 0) (residueCount D.DB 4 1)
        (residueCount D.DB 4 2) (residueCount D.DB 4 3) =
      gaussianNorm (residueCount D.H 4 0) (residueCount D.H 4 1)
        (residueCount D.H 4 2) (residueCount D.H 4 3) := by
  exact gaussian_norm_multiplicative _ _ _ _ _ _
    D.gaussian_real_equation D.gaussian_imag_equation

private theorem residueCount_sum (S : Finset ℕ) (m : ℕ) [NeZero m] :
    ∑ r : ZMod m, SevenHoleRows.residueCount S m r = S.card := by
  classical
  unfold SevenHoleRows.residueCount
  rw [← Finset.card_biUnion]
  · congr 1
    ext x
    simp
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    have hi := (Finset.mem_filter.mp hxi).2
    have hj := (Finset.mem_filter.mp hxj).2
    exact hij (hi.symm.trans hj)

theorem SevenHoleRows.row_residue_sums_four (D : SevenHoleRows) :
    residueCount D.DA 4 0 + residueCount D.DA 4 1 +
        residueCount D.DA 4 2 + residueCount D.DA 4 3 = 9 ∧
      residueCount D.DB 4 0 + residueCount D.DB 4 1 +
        residueCount D.DB 4 2 + residueCount D.DB 4 3 = 9 := by
  have hA := residueCount_sum D.DA 4
  have hB := residueCount_sum D.DB 4
  norm_num [Fin.sum_univ_succ] at hA hB
  simpa [D.cardA, D.cardB, add_assoc] using And.intro hA hB

theorem SevenHoleRows.row_gaussian_norms_pos_mod_four (D : SevenHoleRows) :
    (0 < gaussianNorm (residueCount D.DA 4 0) (residueCount D.DA 4 1)
        (residueCount D.DA 4 2) (residueCount D.DA 4 3) ∧
      gaussianNorm (residueCount D.DA 4 0) (residueCount D.DA 4 1)
        (residueCount D.DA 4 2) (residueCount D.DA 4 3) % 4 = 1) ∧
    (0 < gaussianNorm (residueCount D.DB 4 0) (residueCount D.DB 4 1)
        (residueCount D.DB 4 2) (residueCount D.DB 4 3) ∧
      gaussianNorm (residueCount D.DB 4 0) (residueCount D.DB 4 1)
        (residueCount D.DB 4 2) (residueCount D.DB 4 3) % 4 = 1) := by
  exact ⟨gaussianNorm_pos_mod_four _ _ _ _ D.row_residue_sums_four.1,
    gaussianNorm_pos_mod_four _ _ _ _ D.row_residue_sums_four.2⟩

theorem negative_five_hole_norm_values
    (h0 h1 h2 h3 : ℕ)
    (heven : h0 + h2 = 6) (hodd : h1 + h3 = 1) :
    gaussianNorm h0 h1 h2 h3 = 1 ∨
      gaussianNorm h0 h1 h2 h3 = 5 ∨
      gaussianNorm h0 h1 h2 h3 = 17 ∨
      gaussianNorm h0 h1 h2 h3 = 37 := by
  have h0le : h0 ≤ 6 := by omega
  have h1le : h1 ≤ 1 := by omega
  have h2eq : h2 = 6 - h0 := by omega
  have h3eq : h3 = 1 - h1 := by omega
  rw [h2eq, h3eq]
  interval_cases h0 <;> interval_cases h1 <;> norm_num [gaussianNorm]

theorem product_three_hole_norm_values
    (h0 h1 h2 h3 : ℕ)
    (heven : h0 + h2 = 2) (hodd : h1 + h3 = 5) :
    gaussianNorm h0 h1 h2 h3 = 1 ∨
      gaussianNorm h0 h1 h2 h3 = 5 ∨
      gaussianNorm h0 h1 h2 h3 = 9 ∨
      gaussianNorm h0 h1 h2 h3 = 13 ∨
      gaussianNorm h0 h1 h2 h3 = 25 ∨
      gaussianNorm h0 h1 h2 h3 = 29 := by
  have h0le : h0 ≤ 2 := by omega
  have h1le : h1 ≤ 5 := by omega
  have h2eq : h2 = 2 - h0 := by omega
  have h3eq : h3 = 5 - h1 := by omega
  rw [h2eq, h3eq]
  interval_cases h0 <;> interval_cases h1 <;> norm_num [gaussianNorm]

theorem norm_factor_prefilter_neg_five
    (nuA nuB holeNorm : ℕ)
    (hA : 0 < nuA ∧ nuA % 4 = 1)
    (hB : 0 < nuB ∧ nuB % 4 = 1)
    (hprod : nuA * nuB = holeNorm)
    (hhole : holeNorm = 1 ∨ holeNorm = 5 ∨
      holeNorm = 17 ∨ holeNorm = 37) :
    nuA = 1 ∨ nuB = 1 := by
  rcases hhole with rfl | rfl | rfl | rfl
  all_goals have hAle : nuA ≤ 37 := by nlinarith [hB.1]
  all_goals have hAnonneg : 0 ≤ nuA := le_of_lt hA.1
  all_goals interval_cases nuA
  all_goals norm_num at *
  all_goals omega

theorem norm_factor_prefilter_three
    (nuA nuB holeNorm : ℕ)
    (hA : 0 < nuA ∧ nuA % 4 = 1)
    (hB : 0 < nuB ∧ nuB % 4 = 1)
    (hprod : nuA * nuB = holeNorm)
    (hhole : holeNorm = 1 ∨ holeNorm = 5 ∨ holeNorm = 9 ∨
      holeNorm = 13 ∨ holeNorm = 25 ∨ holeNorm = 29) :
    nuA = 1 ∨ nuB = 1 ∨
      (holeNorm = 25 ∧ nuA = 5 ∧ nuB = 5) := by
  rcases hhole with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals have hAle : nuA ≤ 29 := by nlinarith [hB.1]
  all_goals have hAnonneg : 0 ≤ nuA := le_of_lt hA.1
  all_goals interval_cases nuA
  all_goals norm_num at *
  all_goals omega

/-- The exceptional norm-25 branch forces the receipt's exact hole-residue
profile. -/
theorem norm_twenty_five_hole_profile
    (h0 h1 h2 h3 : ℕ)
    (heven : h0 + h2 = 2) (hodd : h1 + h3 = 5)
    (hnorm : ((h0 : ℤ) - h2) ^ 2 + ((h1 : ℤ) - h3) ^ 2 = 25) :
    h0 = 1 ∧ h2 = 1 ∧
      ((h1 = 5 ∧ h3 = 0) ∨ (h1 = 0 ∧ h3 = 5)) := by
  have h0le : h0 ≤ 2 := by omega
  have h1le : h1 ≤ 5 := by omega
  have h2eq : h2 = 2 - h0 := by omega
  have h3eq : h3 = 5 - h1 := by omega
  rw [h2eq, h3eq] at hnorm ⊢
  interval_cases h0 <;> interval_cases h1
  all_goals norm_num at *

private theorem integer_norm_prefilter_neg_five
    (nuA nuB holeNorm : ℤ)
    (hA : 0 < nuA ∧ nuA % 4 = 1)
    (hB : 0 < nuB ∧ nuB % 4 = 1)
    (hprod : nuA * nuB = holeNorm)
    (hhole : holeNorm = 1 ∨ holeNorm = 5 ∨
      holeNorm = 17 ∨ holeNorm = 37) :
    nuA = 1 ∨ nuB = 1 := by
  rcases hhole with rfl | rfl | rfl | rfl
  all_goals have hAle : nuA ≤ 37 := by nlinarith [hB.1]
  all_goals have hAnonneg : 0 ≤ nuA := le_of_lt hA.1
  all_goals interval_cases nuA
  all_goals norm_num at *
  all_goals omega

private theorem integer_norm_prefilter_three
    (nuA nuB holeNorm : ℤ)
    (hA : 0 < nuA ∧ nuA % 4 = 1)
    (hB : 0 < nuB ∧ nuB % 4 = 1)
    (hprod : nuA * nuB = holeNorm)
    (hhole : holeNorm = 1 ∨ holeNorm = 5 ∨ holeNorm = 9 ∨
      holeNorm = 13 ∨ holeNorm = 25 ∨ holeNorm = 29) :
    nuA = 1 ∨ nuB = 1 ∨
      (holeNorm = 25 ∧ nuA = 5 ∧ nuB = 5) := by
  rcases hhole with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals have hAle : nuA ≤ 29 := by nlinarith [hB.1]
  all_goals have hAnonneg : 0 ≤ nuA := le_of_lt hA.1
  all_goals interval_cases nuA
  all_goals norm_num at *
  all_goals omega

/-- Atom H, negative-five branch, now composed from the actual modulus-four
convolution rather than accepting the norm product as a premise. -/
theorem SevenHoleRows.negative_five_gaussian_prefilter
    (D : SevenHoleRows)
    (heven : residueCount D.H 4 0 + residueCount D.H 4 2 = 6)
    (hodd : residueCount D.H 4 1 + residueCount D.H 4 3 = 1) :
    gaussianNorm (residueCount D.DA 4 0) (residueCount D.DA 4 1)
        (residueCount D.DA 4 2) (residueCount D.DA 4 3) = 1 ∨
      gaussianNorm (residueCount D.DB 4 0) (residueCount D.DB 4 1)
        (residueCount D.DB 4 2) (residueCount D.DB 4 3) = 1 := by
  let nuA := gaussianNorm (residueCount D.DA 4 0) (residueCount D.DA 4 1)
    (residueCount D.DA 4 2) (residueCount D.DA 4 3)
  let nuB := gaussianNorm (residueCount D.DB 4 0) (residueCount D.DB 4 1)
    (residueCount D.DB 4 2) (residueCount D.DB 4 3)
  let nuH := gaussianNorm (residueCount D.H 4 0) (residueCount D.H 4 1)
    (residueCount D.H 4 2) (residueCount D.H 4 3)
  have hvals : nuH = 1 ∨ nuH = 5 ∨ nuH = 17 ∨ nuH = 37 :=
    negative_five_hole_norm_values _ _ _ _ heven hodd
  have hpos := D.row_gaussian_norms_pos_mod_four
  exact integer_norm_prefilter_neg_five nuA nuB nuH hpos.1 hpos.2
    D.gaussian_norm_product hvals

/-- Atom H, product-three branch, including the unique norm-25 exception and
its forced hole-residue profile. -/
theorem SevenHoleRows.product_three_gaussian_prefilter
    (D : SevenHoleRows)
    (heven : residueCount D.H 4 0 + residueCount D.H 4 2 = 2)
    (hodd : residueCount D.H 4 1 + residueCount D.H 4 3 = 5) :
    gaussianNorm (residueCount D.DA 4 0) (residueCount D.DA 4 1)
        (residueCount D.DA 4 2) (residueCount D.DA 4 3) = 1 ∨
      gaussianNorm (residueCount D.DB 4 0) (residueCount D.DB 4 1)
        (residueCount D.DB 4 2) (residueCount D.DB 4 3) = 1 ∨
      (gaussianNorm (residueCount D.H 4 0) (residueCount D.H 4 1)
          (residueCount D.H 4 2) (residueCount D.H 4 3) = 25 ∧
        gaussianNorm (residueCount D.DA 4 0) (residueCount D.DA 4 1)
          (residueCount D.DA 4 2) (residueCount D.DA 4 3) = 5 ∧
        gaussianNorm (residueCount D.DB 4 0) (residueCount D.DB 4 1)
          (residueCount D.DB 4 2) (residueCount D.DB 4 3) = 5 ∧
        residueCount D.H 4 0 = 1 ∧ residueCount D.H 4 2 = 1 ∧
          ((residueCount D.H 4 1 = 5 ∧ residueCount D.H 4 3 = 0) ∨
           (residueCount D.H 4 1 = 0 ∧ residueCount D.H 4 3 = 5))) := by
  let nuA := gaussianNorm (residueCount D.DA 4 0) (residueCount D.DA 4 1)
    (residueCount D.DA 4 2) (residueCount D.DA 4 3)
  let nuB := gaussianNorm (residueCount D.DB 4 0) (residueCount D.DB 4 1)
    (residueCount D.DB 4 2) (residueCount D.DB 4 3)
  let nuH := gaussianNorm (residueCount D.H 4 0) (residueCount D.H 4 1)
    (residueCount D.H 4 2) (residueCount D.H 4 3)
  have hvals : nuH = 1 ∨ nuH = 5 ∨ nuH = 9 ∨ nuH = 13 ∨
      nuH = 25 ∨ nuH = 29 :=
    product_three_hole_norm_values _ _ _ _ heven hodd
  have hpos := D.row_gaussian_norms_pos_mod_four
  rcases integer_norm_prefilter_three nuA nuB nuH hpos.1 hpos.2
      D.gaussian_norm_product hvals with hA | hB | hex
  · exact Or.inl hA
  · exact Or.inr (Or.inl hB)
  · right; right
    refine ⟨hex.1, hex.2.1, hex.2.2, ?_⟩
    exact norm_twenty_five_hole_profile _ _ _ _ heven hodd hex.1

end LeechTrees.ParityTailConditional
