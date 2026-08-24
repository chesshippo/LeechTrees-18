import LeechTrees.Foundations
import LeechTrees.Expanded.BlockLifts.OddCompleteBlock
import Mathlib.Data.ZMod.Basic
import Mathlib

/-!
# Actual odd complete-star-block architecture

The architecture below contains only the source construction: an actual
positive weighted quotient tree, one rooted `K_(1,q-1)` over every quotient
vertex, the prescribed pendant residues, and an exact bijection from all
constructed pairs to the target interval.  In particular it contains no
Fourier coefficient, common moment, or forced special-weight equation.

The first-moment equality is derived by a finite cyclic coefficient
calculation.  This is the coefficient form of differentiating the exact
pair polynomial and evaluating at every nontrivial `q`-th root, but avoids
introducing complex roots of unity into the architecture theorem.
-/

open scoped BigOperators

namespace LeechTrees.AdditionalBlockLifts

open LeechTrees.Foundation

abbrev CompleteBlockVertex (q : ℕ) := Fin q

abbrev CompleteBlockPair (q : ℕ) :=
  {z : Fin q × Fin q // z.1 < z.2}

/-- Internal pairs in one block, followed by the full Cartesian block for
each unordered pair of distinct quotient roots. -/
abbrev CompleteBlockPairIndex (q : ℕ) :=
  (Fin q × CompleteBlockPair q) ⊕
    (VertexPair q × (Fin q × Fin q))

def completeBlockH (q : ℕ) : ℕ := q * (q ^ 2 - 1) / 2

def completeBlockN (q : ℕ) : ℕ := q * completeBlockH q

/-! ## Cyclic first-moment algebra -/

section Cyclic

variable {q : ℕ} [NeZero q]

/-- The partner involution in a prescribed additive-residue fibre. -/
noncomputable def residuePartner (ρ : Fin q ≃ ZMod q) (r : ZMod q) :
    Fin q ≃ Fin q where
  toFun a := ρ.symm (r - ρ a)
  invFun a := ρ.symm (r - ρ a)
  left_inv a := by
    apply ρ.injective
    simp
  right_inv a := by
    apply ρ.injective
    simp

omit [NeZero q] in
@[simp] theorem residuePartner_residue
    (ρ : Fin q ≃ ZMod q) (r : ZMod q) (a : Fin q) :
    ρ (residuePartner ρ r a) = r - ρ a := by
  simp [residuePartner]

omit [NeZero q] in
@[simp] theorem residuePartner_involutive
    (ρ : Fin q ≃ ZMod q) (r : ZMod q) (a : Fin q) :
    residuePartner ρ r (residuePartner ρ r a) = a := by
  exact (residuePartner ρ r).left_inv a

/-- A finite involution partitions into two-element orbits and fixed
points.  The displayed formula keeps one representative of every
two-element orbit, selected by the ambient linear order. -/
private theorem involution_weight_partition
    {α : Type*} [Fintype α] [LinearOrder α]
    (f : α → α) (hf : ∀ a, f (f a) = a) (w : α → ℤ) :
    (∑ a, w a) =
      (∑ a, if a < f a then w a + w (f a) else 0) +
        ∑ a, if a = f a then w a else 0 := by
  classical
  let lower : Finset α := Finset.univ.filter fun a => a < f a
  let fixed : Finset α := Finset.univ.filter fun a => a = f a
  let upper : Finset α := Finset.univ.filter fun a => f a < a
  have hcover : (Finset.univ : Finset α) = lower ∪ fixed ∪ upper := by
    ext a
    simp only [lower, fixed, upper, Finset.mem_univ, Finset.mem_union,
      Finset.mem_filter, true_and]
    constructor
    · intro _
      rcases lt_trichotomy a (f a) with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    · intro _
      trivial
  have hlf : Disjoint lower fixed := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [lower, fixed, Finset.mem_filter, Finset.mem_univ,
      true_and] at ha hb
    exact (ne_of_lt ha) hb
  have hlu : Disjoint lower upper := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [lower, upper, Finset.mem_filter, Finset.mem_univ,
      true_and] at ha hb
    exact (not_lt_of_ge ha.le) hb
  have hfu : Disjoint fixed upper := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [fixed, upper, Finset.mem_filter, Finset.mem_univ,
      true_and] at ha hb
    exact (ne_of_lt hb) ha.symm
  have hupper : (∑ a ∈ upper, w a) = ∑ a ∈ lower, w (f a) := by
    apply Finset.sum_bij (fun a _ => f a)
    · intro a ha
      simp only [upper, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      simp only [lower, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [hf a] using ha
    · intro a₁ ha₁ a₂ ha₂ h
      have := congrArg f h
      simpa [hf a₁, hf a₂] using this
    · intro b hb
      simp only [lower, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      refine ⟨f b, ?_, ?_⟩
      · simp only [upper, Finset.mem_filter, Finset.mem_univ, true_and]
        simp only [hf b]
        exact hb
      · exact hf b
    · intro a ha
      rw [hf a]
  calc
    (∑ a, w a) = ∑ a ∈ lower ∪ fixed ∪ upper, w a := by rw [← hcover]
    _ = (∑ a ∈ lower, w a) + (∑ a ∈ fixed, w a) +
        ∑ a ∈ upper, w a := by
      rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hlu, hfu⟩)]
      rw [Finset.sum_union hlf]
    _ = (∑ a ∈ lower, w a) + (∑ a ∈ fixed, w a) +
        ∑ a ∈ lower, w (f a) := by rw [hupper]
    _ = (∑ a ∈ lower, (fun x => w x + w (f x)) a) +
        ∑ a ∈ fixed, w a := by
      rw [Finset.sum_add_distrib]
      abel
    _ = (∑ a, if a < f a then w a + w (f a) else 0) +
        ∑ a, if a = f a then w a else 0 := by
      unfold lower fixed
      rw [Finset.sum_filter, Finset.sum_filter]

/-- The weighted internal-pair moment in residue `r`. -/
def withinResidueMoment
    (ρ : Fin q ≃ ZMod q) (w : Fin q → ℕ) (r : ZMod q) : ℤ :=
  ∑ p : CompleteBlockPair q,
    if ρ p.1.1 + ρ p.1.2 = r then
      (w p.1.1 : ℤ) + w p.1.2 else 0

/-- The diagonal correction appearing when ordered pairs are divided by
the endpoint-swap involution. -/
def diagonalResidueMoment
    (dρ : Fin q ≃ ZMod q) (w : Fin q → ℕ) (r : ZMod q) : ℤ :=
  ∑ a, if dρ a = r then (w a : ℤ) else 0

omit [NeZero q] in
/-- Exact unordered-pair coefficient identity
`within(r)+diagonal(r)=sum(weights)`.  Here `dρ a=2ρ a` is supplied as a
literal residue identity, not as a moment assumption. -/
theorem within_add_diagonal_eq_total
    (ρ dρ : Fin q ≃ ZMod q) (w : Fin q → ℕ)
    (hdρ : ∀ a, dρ a = ρ a + ρ a) (r : ZMod q) :
    withinResidueMoment ρ w r + diagonalResidueMoment dρ w r =
      ∑ a, (w a : ℤ) := by
  classical
  let f : Fin q → Fin q := residuePartner ρ r
  have hf : ∀ a, f (f a) = a := residuePartner_involutive ρ r
  have hpair : withinResidueMoment ρ w r =
      ∑ a, if a < f a then (w a : ℤ) + w (f a) else 0 := by
    unfold withinResidueMoment
    let e :
        {a : Fin q // a < f a} ≃
          {p : CompleteBlockPair q // ρ p.1.1 + ρ p.1.2 = r} :=
      { toFun := fun a =>
          ⟨⟨(a.1, f a.1), a.2⟩, by
            change ρ a.1 + ρ (residuePartner ρ r a.1) = r
            simp [f]⟩
        invFun := fun p => ⟨p.1.1.1, by
          change p.1.1.1 < residuePartner ρ r p.1.1.1
          apply p.1.2.trans_eq
          apply ρ.injective
          rw [residuePartner_residue]
          exact (eq_sub_iff_add_eq).2 (by simpa [add_comm] using p.2)⟩
        left_inv := by intro a; apply Subtype.ext; rfl
        right_inv := by
          intro p
          apply Subtype.ext
          apply Subtype.ext
          apply Prod.ext
          · rfl
          · apply ρ.injective
            rw [residuePartner_residue]
            exact ((eq_sub_iff_add_eq).2
              (by simpa [add_comm] using p.2)).symm }
    calc
      (∑ p : CompleteBlockPair q,
          if ρ p.1.1 + ρ p.1.2 = r then
            (w p.1.1 : ℤ) + w p.1.2 else 0) =
          ∑ z : {p : CompleteBlockPair q // ρ p.1.1 + ρ p.1.2 = r},
            (fun z : {p : CompleteBlockPair q //
                ρ p.1.1 + ρ p.1.2 = r} =>
              (w (↑z : CompleteBlockPair q).1.1 : ℤ) +
                w (↑z : CompleteBlockPair q).1.2) z := by
            rw [← Finset.sum_filter]
            symm
            simpa only [Finset.subtype_univ] using
              (Finset.sum_subtype_eq_sum_filter
                (s := (Finset.univ : Finset (CompleteBlockPair q)))
                (p := fun p => ρ p.1.1 + ρ p.1.2 = r)
                (fun p => (w p.1.1 : ℤ) + w p.1.2))
      _ = ∑ b : {a : Fin q // a < f a},
          (fun b : {a : Fin q // a < f a} =>
            (w (↑b : Fin q) : ℤ) + w (f (↑b : Fin q))) b := by
            symm
            exact Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = ∑ a, if a < f a then (w a : ℤ) + w (f a) else 0 := by
            rw [← Finset.sum_filter]
            simpa only [Finset.subtype_univ] using
              (Finset.sum_subtype_eq_sum_filter
                (s := (Finset.univ : Finset (Fin q)))
                (p := fun a => a < f a)
                (fun a => (w a : ℤ) + w (f a)))
  have hdiag : diagonalResidueMoment dρ w r =
      ∑ a, if a = f a then (w a : ℤ) else 0 := by
    unfold diagonalResidueMoment
    apply Finset.sum_congr rfl
    intro a ha
    congr 1
    apply propext
    constructor
    · intro h
      apply ρ.injective
      rw [residuePartner_residue]
      calc
        ρ a = (ρ a + ρ a) - ρ a := by abel
        _ = dρ a - ρ a := by rw [hdρ a]
        _ = r - ρ a := by rw [h]
    · intro h
      have hp := congrArg ρ h
      rw [residuePartner_residue] at hp
      rw [hdρ a]
      calc
        ρ a + ρ a = ρ a + (r - ρ a) :=
          congrArg (fun x => ρ a + x) hp
        _ = r := by abel
  rw [hpair, hdiag]
  linarith [involution_weight_partition f hf (fun a => (w a : ℤ))]

/-- The weighted cross-block moment.  The full quotient distance `δ` is
retained in the integer weight and only its cast is used in the fibre. -/
def crossResidueMoment
    (ρ : Fin q ≃ ZMod q) (w₁ w₂ : Fin q → ℕ) (δ : ℕ)
    (r : ZMod q) : ℤ :=
  ∑ a, ∑ b,
    if ρ a + ρ b + (δ : ZMod q) = r then
      (w₁ a : ℤ) + δ + w₂ b else 0

omit [NeZero q] in
/-- Every cross-block differentiated coefficient is residue-independent.
The proof explicitly reindexes the unique second endpoint in each cyclic
fibre; no quotient topology or quotient weight is discarded. -/
theorem crossResidueMoment_independent
    (ρ : Fin q ≃ ZMod q) (w₁ w₂ : Fin q → ℕ) (δ : ℕ)
    (r s : ZMod q) :
    crossResidueMoment ρ w₁ w₂ δ r =
      crossResidueMoment ρ w₁ w₂ δ s := by
  classical
  have hformula : ∀ t : ZMod q,
      crossResidueMoment ρ w₁ w₂ δ t =
        (∑ a, (w₁ a : ℤ)) + (q : ℤ) * δ + ∑ b, (w₂ b : ℤ) := by
    intro t
    let partner : Fin q ≃ Fin q := residuePartner ρ (t - (δ : ZMod q))
    unfold crossResidueMoment
    calc
      (∑ a, ∑ b,
          if ρ a + ρ b + (δ : ZMod q) = t then
            (w₁ a : ℤ) + δ + w₂ b else 0) =
          ∑ a, ((w₁ a : ℤ) + δ + w₂ (partner a)) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.sum_eq_single (partner a)]
            · have hp : ρ a + ρ (partner a) + (δ : ZMod q) = t := by
                change ρ a + ρ (residuePartner ρ (t - (δ : ZMod q)) a) +
                  (δ : ZMod q) = t
                rw [residuePartner_residue]
                abel
              rw [if_pos hp]
            · intro b hb hne
              rw [if_neg]
              intro hcondition
              apply hne
              change b = residuePartner ρ (t - (δ : ZMod q)) a
              apply ρ.injective
              rw [residuePartner_residue]
              rw [← hcondition]
              abel
            · simp
      _ = (∑ a, (w₁ a : ℤ)) + (q : ℤ) * δ +
          ∑ a, (w₂ (partner a) : ℤ) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
            simp only [Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul]
      _ = (∑ a, (w₁ a : ℤ)) + (q : ℤ) * δ +
          ∑ b, (w₂ b : ℤ) := by
            congr 1
            exact Fintype.sum_equiv partner (fun a => (w₂ (partner a) : ℤ))
              (fun b => (w₂ b : ℤ)) (fun _ => rfl)
  rw [hformula r, hformula s]

end Cyclic

/-! ## Exact rooted-star construction -/

/-- Base architecture, before any differentiated or Fourier consequence.
`residue` and `doubleResidue` merely record the two permutations forced by
the nonzero even pendant residues when `q` is odd. -/
structure OddCompleteStarArchitecture (q : ℕ) [NeZero q] where
  q_gt_one : 1 < q
  q_odd : q % 2 = 1
  quotient : PosIntTree q
  offset : Fin q → Fin q → ℕ
  root_offset : ∀ i, offset i 0 = 0
  leaf_pos : ∀ i a, a ≠ 0 → 0 < offset i a
  target_zero_moment_identity :
    (∑ k : Fin (completeBlockN q),
      if (((k.1 + 1 : ℕ) : ZMod q) = 0) then
        ((k.1 + 1 : ℕ) : ℤ) else 0) =
      targetZeroResidueMoment q (completeBlockH q)
  target_last_moment_identity :
    (∑ k : Fin (completeBlockN q),
      if (((k.1 + 1 : ℕ) : ZMod q) = -1) then
        ((k.1 + 1 : ℕ) : ℤ) else 0) =
      targetNonzeroResidueMoment q (completeBlockH q) (q - 1)
  even_residue : ∀ i a, a ≠ 0 →
    offset i a % (2 * q) = 2 * a.1
  residue : Fin q ≃ ZMod q
  residue_label : ∀ a, residue a = (2 * a.1 : ℕ)
  residue_value : ∀ i a, residue a = (offset i a : ZMod q)
  doubleResidue : Fin q ≃ ZMod q
  doubleResidue_value : ∀ a, doubleResidue a = residue a + residue a
  doubleResidue_zero : doubleResidue 0 = 0
  targetEquiv : CompleteBlockPairIndex q ≃ Fin (completeBlockN q)
  targetEquiv_value : ∀ p,
    (targetEquiv p).1 + 1 =
      match p with
      | .inl z => offset z.1 z.2.1.1 + offset z.1 z.2.1.2
      | .inr z =>
          offset z.1.left z.2.1 + quotient.dist z.1.left z.1.right +
            offset z.1.right z.2.2

namespace OddCompleteStarArchitecture

variable {q : ℕ} [NeZero q]

noncomputable def pairDistance (A : OddCompleteStarArchitecture q) :
    CompleteBlockPairIndex q → ℕ
  | .inl z => A.offset z.1 z.2.1.1 + A.offset z.1 z.2.1.2
  | .inr z =>
      A.offset z.1.left z.2.1 + A.quotient.dist z.1.left z.1.right +
        A.offset z.1.right z.2.2

theorem pairDistance_target (A : OddCompleteStarArchitecture q) (p) :
    A.pairDistance p = (A.targetEquiv p).1 + 1 := by
  rw [A.targetEquiv_value]
  rfl

/-- Sum of constructed pair distances in one residue of `ZMod q`. -/
noncomputable def pairResidueMoment
    (A : OddCompleteStarArchitecture q) (r : ZMod q) : ℤ :=
  ∑ p, if (A.pairDistance p : ZMod q) = r then
    (A.pairDistance p : ℤ) else 0

def specialVertex (A : OddCompleteStarArchitecture q) : Fin q :=
  A.doubleResidue.symm (-1)

def specialIndex (A : OddCompleteStarArchitecture q) : ℕ :=
  (A.specialVertex).1

def specialWeight (A : OddCompleteStarArchitecture q) (i : Fin q) : ℤ :=
  A.offset i A.specialVertex

def specialLift (A : OddCompleteStarArchitecture q) (i : Fin q) : ℤ :=
  A.offset i A.specialVertex / (2 * q)

theorem specialVertex_ne_zero (A : OddCompleteStarArchitecture q) :
    A.specialVertex ≠ 0 := by
  letI : Fact (1 < q) := ⟨A.q_gt_one⟩
  intro h
  have hminus : (-1 : ZMod q) = 0 := by
    simpa [specialVertex, A.doubleResidue_zero] using
      congrArg A.doubleResidue h
  exact one_ne_zero (neg_eq_zero.mp hminus)

theorem specialIndex_pos (A : OddCompleteStarArchitecture q) :
    0 < A.specialIndex := by
  exact Fin.pos_iff_ne_zero.mpr A.specialVertex_ne_zero

/-- The special vertex selected abstractly by the doubled-residue
permutation is the audited least positive solution of `4a=-1 (mod q)`.
This is derived from the literal residue labelling. -/
theorem specialIndex_eq_oddSpecialIndex (A : OddCompleteStarArchitecture q) :
    A.specialIndex = oddSpecialIndex q := by
  let a₀ : Fin q :=
    ⟨oddSpecialIndex q, (oddSpecialIndex_spec q A.q_gt_one A.q_odd).2.1⟩
  have ha₀ : A.doubleResidue a₀ = (-1 : ZMod q) := by
    rw [A.doubleResidue_value, A.residue_label]
    have hs := (oddSpecialIndex_spec q A.q_gt_one A.q_odd).2.2
    have hfour : ((4 * a₀.1 : ℕ) : ZMod q) = ((q - 1 : ℕ) : ZMod q) := by
      apply (ZMod.natCast_eq_natCast_iff' (4 * a₀.1) (q - 1) q).2
      have hqpos : 0 < q := lt_trans Nat.zero_lt_one A.q_gt_one
      have hqsub : q - 1 < q := Nat.sub_lt hqpos Nat.zero_lt_one
      rw [Nat.mod_eq_of_lt hqsub]
      simpa [a₀] using hs
    have hlast : ((q - 1 : ℕ) : ZMod q) = -1 := by
      have hone : 1 ≤ q := Nat.le_of_lt A.q_gt_one
      rw [Nat.cast_sub hone]
      simp
    calc
      ((2 * a₀.1 : ℕ) : ZMod q) + ((2 * a₀.1 : ℕ) : ZMod q) =
          ((4 * a₀.1 : ℕ) : ZMod q) := by push_cast; ring
      _ = ((q - 1 : ℕ) : ZMod q) := hfour
      _ = -1 := hlast
  have hvertex : A.specialVertex = a₀ := by
    apply A.doubleResidue.injective
    simpa [specialVertex] using ha₀.symm
  exact congrArg Fin.val hvertex

theorem specialWeight_lift_formula (A : OddCompleteStarArchitecture q)
    (i : Fin q) :
    A.specialWeight i =
      2 * (A.specialIndex : ℤ) + 2 * (q : ℤ) * A.specialLift i := by
  have hres := A.even_residue i A.specialVertex A.specialVertex_ne_zero
  have hdecomp := Nat.mod_add_div (A.offset i A.specialVertex) (2 * q)
  rw [hres] at hdecomp
  unfold specialWeight specialLift specialIndex
  exact_mod_cast hdecomp.symm

theorem specialLift_nonnegative (A : OddCompleteStarArchitecture q)
    (i : Fin q) : 0 ≤ A.specialLift i := by
  unfold specialLift
  exact Int.ediv_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)

theorem pairDistance_injective (A : OddCompleteStarArchitecture q) :
    Function.Injective A.pairDistance := by
  intro p r h
  apply A.targetEquiv.injective
  apply Fin.ext
  rw [A.pairDistance_target p, A.pairDistance_target r] at h
  omega

private def specialPair (A : OddCompleteStarArchitecture q) (i : Fin q) :
    CompleteBlockPairIndex q :=
  .inl (i, ⟨(0, A.specialVertex), Fin.pos_iff_ne_zero.mpr
    A.specialVertex_ne_zero⟩)

theorem specialWeight_distinct (A : OddCompleteStarArchitecture q) :
    Function.Injective A.specialWeight := by
  intro i j hij
  have hp : A.specialPair i = A.specialPair j := by
    apply A.pairDistance_injective
    unfold specialWeight at hij
    simpa [specialPair, pairDistance, A.root_offset] using hij
  simpa [specialPair] using congrArg
    (fun p => p.elim (fun z => z.1) (fun _ => 0)) hp

/-- The source architecture itself gives the two differentiated coefficient
equations.  Internal blocks use `within_add_diagonal_eq_total`; every cross
block cancels by `crossResidueMoment_independent`. -/
theorem pairResidueMoment_zero_sub_last
    (A : OddCompleteStarArchitecture q) :
    A.pairResidueMoment 0 - A.pairResidueMoment (-1) =
      ∑ i, A.specialWeight i := by
  classical
  have hwithin : ∀ i : Fin q,
      withinResidueMoment A.residue (A.offset i) 0 -
          withinResidueMoment A.residue (A.offset i) (-1) =
        A.specialWeight i := by
    intro i
    have h0 := within_add_diagonal_eq_total A.residue A.doubleResidue
      (A.offset i) A.doubleResidue_value 0
    have hlast := within_add_diagonal_eq_total A.residue A.doubleResidue
      (A.offset i) A.doubleResidue_value (-1)
    have hdiag0 : diagonalResidueMoment A.doubleResidue (A.offset i) 0 = 0 := by
      unfold diagonalResidueMoment
      rw [Finset.sum_eq_single 0]
      · simp [A.root_offset]
      · intro a ha hne
        simp only [Finset.mem_univ] at ha
        rw [if_neg]
        intro hh
        exact hne (A.doubleResidue.injective
          (hh.trans A.doubleResidue_zero.symm))
      · simp
    have hdiagLast :
        diagonalResidueMoment A.doubleResidue (A.offset i) (-1) =
          A.specialWeight i := by
      unfold diagonalResidueMoment specialWeight specialVertex
      rw [Finset.sum_eq_single (A.doubleResidue.symm (-1))]
      · simp
      · intro a ha hne
        simp only [Finset.mem_univ] at ha
        rw [if_neg]
        intro hh
        exact hne (A.doubleResidue.injective (by simpa using hh))
      · simp
    rw [hdiag0] at h0
    rw [hdiagLast] at hlast
    linarith
  have hcross : ∀ z : VertexPair q,
      crossResidueMoment A.residue (A.offset z.left) (A.offset z.right)
          (A.quotient.dist z.left z.right) 0 =
        crossResidueMoment A.residue (A.offset z.left) (A.offset z.right)
          (A.quotient.dist z.left z.right) (-1) := by
    intro z
    exact crossResidueMoment_independent A.residue _ _ _ 0 (-1)
  unfold pairResidueMoment
  simp only [pairDistance, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Nat.cast_add]
  simp_rw [← A.residue_value]
  have hresidueOrder (a b : Fin q) (δ : ℕ) (r : ZMod q) :
      A.residue a + (δ : ZMod q) + A.residue b = r ↔
        A.residue a + A.residue b + (δ : ZMod q) = r := by
    constructor <;> intro h <;> linear_combination h
  simp_rw [hresidueOrder]
  change
    ((∑ i, withinResidueMoment A.residue (A.offset i) 0) +
        ∑ z : VertexPair q,
          crossResidueMoment A.residue (A.offset z.left) (A.offset z.right)
            (A.quotient.dist z.left z.right) 0) -
      ((∑ i, withinResidueMoment A.residue (A.offset i) (-1)) +
        ∑ z : VertexPair q,
          crossResidueMoment A.residue (A.offset z.left) (A.offset z.right)
            (A.quotient.dist z.left z.right) (-1)) = _
  calc
    _ = ((∑ i, withinResidueMoment A.residue (A.offset i) 0) -
          ∑ i, withinResidueMoment A.residue (A.offset i) (-1)) +
        ((∑ z : VertexPair q,
            crossResidueMoment A.residue (A.offset z.left) (A.offset z.right)
              (A.quotient.dist z.left z.right) 0) -
          ∑ z : VertexPair q,
            crossResidueMoment A.residue (A.offset z.left) (A.offset z.right)
              (A.quotient.dist z.left z.right) (-1)) := by ring
    _ = (∑ i, (fun j => withinResidueMoment A.residue (A.offset j) 0 -
          withinResidueMoment A.residue (A.offset j) (-1)) i) +
        ∑ z : VertexPair q,
          (crossResidueMoment A.residue (A.offset z.left) (A.offset z.right)
              (A.quotient.dist z.left z.right) 0 -
            crossResidueMoment A.residue (A.offset z.left) (A.offset z.right)
              (A.quotient.dist z.left z.right) (-1)) := by
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    _ = _ := by
      rw [show (∑ i, (fun j =>
            withinResidueMoment A.residue (A.offset j) 0 -
              withinResidueMoment A.residue (A.offset j) (-1)) i) =
          ∑ i, A.specialWeight i by
            apply Finset.sum_congr rfl
            intro i hi
            exact hwithin i]
      rw [show (∑ z : VertexPair q,
            (crossResidueMoment A.residue (A.offset z.left) (A.offset z.right)
                (A.quotient.dist z.left z.right) 0 -
              crossResidueMoment A.residue (A.offset z.left) (A.offset z.right)
                (A.quotient.dist z.left z.right) (-1))) = 0 by
            apply Finset.sum_eq_zero
            intro z hz
            rw [hcross z, sub_self]]
      exact add_zero _

private theorem completeBlockN_eq_q_mul_H (q : ℕ) :
    completeBlockN q = q * completeBlockH q := rfl

/-- Target interval coefficient at residue zero. -/
theorem target_zero_moment (A : OddCompleteStarArchitecture q) :
    A.pairResidueMoment 0 =
      targetZeroResidueMoment q (completeBlockH q) := by
  classical
  unfold pairResidueMoment
  apply Eq.trans (Fintype.sum_equiv A.targetEquiv
    (fun p => if (A.pairDistance p : ZMod q) = 0 then
      (A.pairDistance p : ℤ) else 0)
    (fun k : Fin (completeBlockN q) =>
      if (((k.1 + 1 : ℕ) : ZMod q) = 0) then ((k.1 + 1 : ℕ) : ℤ) else 0)
    (fun p => by
      dsimp only
      rw [A.pairDistance_target]))
  exact A.target_zero_moment_identity

/-- Target interval coefficient at residue `q-1`, represented by `-1`. -/
theorem target_last_moment (A : OddCompleteStarArchitecture q) :
    A.pairResidueMoment (-1) =
      targetNonzeroResidueMoment q (completeBlockH q) (q - 1) := by
  classical
  unfold pairResidueMoment
  apply Eq.trans (Fintype.sum_equiv A.targetEquiv
    (fun p => if (A.pairDistance p : ZMod q) = -1 then
      (A.pairDistance p : ℤ) else 0)
    (fun k : Fin (completeBlockN q) =>
      if (((k.1 + 1 : ℕ) : ZMod q) = -1) then ((k.1 + 1 : ℕ) : ℤ) else 0)
    (fun p => by
      dsimp only
      rw [A.pairDistance_target]))
  exact A.target_last_moment_identity

/-- The actual construction forces the special pendant sum.  Both target
moments and the cyclic cancellation are derived above. -/
theorem forced_special_sum (A : OddCompleteStarArchitecture q) :
    (∑ i, A.specialWeight i) = completeBlockH q := by
  have hcyclic := A.pairResidueMoment_zero_sub_last
  rw [A.target_zero_moment, A.target_last_moment] at hcyclic
  have heven : Even ((q : ℤ) * (completeBlockH q : ℤ) *
      ((completeBlockH q : ℤ) - 1)) := by
    simpa [mul_assoc] using
      (Int.even_mul_pred_self (completeBlockH q : ℤ)).mul_left (q : ℤ)
  have htarget := target_last_residue_moment_difference
    (q : ℤ) (completeBlockH q : ℤ) heven
  exact_mod_cast hcyclic.symm.trans htarget

/-- Every field of the abstract first-moment image is now derived from the
base construction.  In particular neither residue equation occurs among
the fields of `OddCompleteStarArchitecture`. -/
noncomputable def toFirstMomentModel
    (A : OddCompleteStarArchitecture q) :
    OddCompleteBlockFirstMomentModel q where
  H := completeBlockH q
  specialWeight := A.specialWeight
  lift := A.specialLift
  commonMoment := A.pairResidueMoment 0
  targetSize := by
    unfold completeBlockH
    have hqpos : 0 < q := lt_trans Nat.zero_lt_one A.q_gt_one
    have heven : Even (q * (q ^ 2 - 1)) := by
      rw [Nat.even_mul]
      by_cases hqeven : Even q
      · exact Or.inl hqeven
      · right
        rw [Nat.even_sub (Nat.one_le_pow 2 q hqpos)]
        rw [Nat.even_pow' (by norm_num : 2 ≠ 0)]
        simp [hqeven]
    have hsq : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q hqpos
    have hnat := Nat.two_mul_div_two_of_even heven
    calc
      2 * ((q * (q ^ 2 - 1) / 2 : ℕ) : ℤ) =
          ((2 * (q * (q ^ 2 - 1) / 2) : ℕ) : ℤ) := by norm_num
      _ = ((q * (q ^ 2 - 1) : ℕ) : ℤ) := by rw [hnat]
      _ = (q : ℤ) * ((q : ℤ) ^ 2 - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub hsq, Nat.cast_pow, Nat.cast_one]
  zeroResidueEquation := A.target_zero_moment
  lastResidueEquation := by
    have hcyclic := A.pairResidueMoment_zero_sub_last
    rw [A.target_last_moment] at hcyclic
    linarith
  specialLift := by
    intro i
    rw [← A.specialIndex_eq_oddSpecialIndex]
    exact A.specialWeight_lift_formula i
  liftNonnegative := A.specialLift_nonnegative
  specialDistinct := A.specialWeight_distinct

/-- Actual G018 endpoint.  The contradiction is between the derived target
moment and the minimum sum of the `q` distinct positive lifts in the one
special nonzero even residue class. -/
theorem no_odd_complete_star_architecture_target_spectrum
    (A : OddCompleteStarArchitecture q) : False := by
  exact no_odd_complete_star_block_first_moment_model q A.q_gt_one A.q_odd
    A.toFirstMomentModel

/-- User-facing quantifier form, with `NeZero q` derived from `q>1`. -/
theorem no_odd_complete_star_architecture
    (q : ℕ) (hq : 1 < q) (hqOdd : q % 2 = 1) :
    letI : NeZero q := ⟨by omega⟩
    IsEmpty (OddCompleteStarArchitecture q) := by
  letI : NeZero q := ⟨by omega⟩
  constructor
  intro A
  exact A.no_odd_complete_star_architecture_target_spectrum

end OddCompleteStarArchitecture

end LeechTrees.AdditionalBlockLifts
