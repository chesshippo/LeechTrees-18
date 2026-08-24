import Mathlib

/-!
# Odd-parameter complete-star-block obstruction

This module is the symbolic first-moment proof of claim G018.  Its endpoint
is restricted to the architecture of `q` rooted `K_(1,q-1)` blocks carrying
all nonzero even residues modulo `2q`, with arbitrary positive root-tree
distances.  The root-tree terms enter only through a residue-independent
first-moment constant, exactly as in the differentiated block polynomial.
-/

open scoped BigOperators

namespace LeechTrees.AdditionalBlockLifts

/-! ## Target residue moments -/

/-- Sum of the members of `1,...,qH` congruent to zero modulo `q`. -/
def targetZeroResidueMoment (q H : ℤ) : ℤ :=
  q * H * (H + 1) / 2

/-- Sum of the members of `1,...,qH` congruent to `r`, for `1<=r<q`. -/
def targetNonzeroResidueMoment (q H r : ℤ) : ℤ :=
  q * H * (H - 1) / 2 + H * r

/-- The exact target first-moment difference. -/
theorem target_residue_moment_difference
    (q H r : ℤ)
    (hEven : Even (q * H * (H - 1))) :
    targetZeroResidueMoment q H -
        targetNonzeroResidueMoment q H r = H * (q - r) := by
  obtain ⟨k, hk⟩ := hEven
  unfold targetZeroResidueMoment targetNonzeroResidueMoment
  have hminus : q * H * (H - 1) / 2 = k := by
    apply Int.ediv_eq_of_eq_mul_left (by norm_num : (2 : ℤ) ≠ 0)
    calc
      q * H * (H - 1) = k + k := hk
      _ = k * 2 := by ring
  have hplus : q * H * (H + 1) / 2 = k + q * H := by
    apply Int.ediv_eq_of_eq_mul_left (by norm_num : (2 : ℤ) ≠ 0)
    calc
      q * H * (H + 1) = q * H * (H - 1) + 2 * (q * H) := by ring
      _ = (k + k) + 2 * (q * H) := by rw [hk]
      _ = (k + q * H) * 2 := by ring
  rw [hminus, hplus]
  ring

/-- The special `r=q-1` difference is exactly `H`. -/
theorem target_last_residue_moment_difference
    (q H : ℤ) (hEven : Even (q * H * (H - 1))) :
    targetZeroResidueMoment q H -
        targetNonzeroResidueMoment q H (q - 1) = H := by
  rw [target_residue_moment_difference q H (q - 1) hEven]
  ring

/-! ## The special residue and the distinct-lift bound -/

/-- The unique least positive `a<q` used by `4a=-1 (mod q)`, written without
an inverse. -/
def oddSpecialIndex (q : ℕ) : ℕ :=
  if q % 4 = 1 then (q - 1) / 4 else (3 * q - 1) / 4

theorem oddSpecialIndex_spec
    (q : ℕ) (hq : 1 < q) (hqOdd : q % 2 = 1) :
    0 < oddSpecialIndex q ∧ oddSpecialIndex q < q ∧
      (4 * oddSpecialIndex q) % q = q - 1 := by
  have hmod4 : q % 4 = 1 ∨ q % 4 = 3 := by omega
  rcases hmod4 with h1 | h3
  · have hdecomp := Nat.mod_add_div q 4
    have hindex : (q - 1) / 4 = q / 4 := by omega
    have hmul : 4 * ((q - 1) / 4) = q - 1 := by omega
    unfold oddSpecialIndex
    rw [if_pos h1]
    refine ⟨by omega, by omega, ?_⟩
    rw [hmul]
    exact Nat.mod_eq_of_lt (by omega)
  · have hn1 : q % 4 ≠ 1 := by omega
    have hdecomp := Nat.mod_add_div q 4
    have hindex : (3 * q - 1) / 4 = 3 * (q / 4) + 2 := by omega
    have hmul : 4 * ((3 * q - 1) / 4) = 3 * q - 1 := by omega
    unfold oddSpecialIndex
    rw [if_neg hn1]
    refine ⟨by omega, by omega, ?_⟩
    rw [hmul]
    rw [show 3 * q - 1 = 2 * q + (q - 1) by omega]
    simp [Nat.add_mod]

/-- Sharp lower bound for `q` distinct nonnegative lift indices. -/
theorem distinct_nonnegative_lifts_lower_bound
    (q : ℕ) (k : Fin q → ℤ)
    (hkNonneg : ∀ i, 0 ≤ k i)
    (hkInjective : Function.Injective k) :
    (q : ℤ) * ((q : ℤ) - 1) / 2 ≤ ∑ i, k i := by
  classical
  let s : Finset ℤ := Finset.univ.image k
  have hsCard : s.card = q := by
    dsimp [s]
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro i hi j hj hij
      exact hkInjective hij
  have hsNonneg : ∀ x ∈ s, (0 : ℤ) ≤ x := by
    intro x hx
    simp only [s, Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact hkNonneg i
  have hLower := Finset.sum_range_le_sum hsNonneg
  rw [hsCard] at hLower
  have hRange :
      (∑ n ∈ Finset.range q, ((0 : ℤ) + n)) =
        (q : ℤ) * ((q : ℤ) - 1) / 2 := by
    simp only [zero_add]
    rw [← Nat.cast_sum]
    rw [Finset.sum_range_id, Int.natCast_ediv, Nat.cast_mul]
    cases q with
    | zero => norm_num
    | succ q =>
        rw [Nat.cast_sub (by omega)]
        norm_num
  rw [hRange] at hLower
  calc
    (q : ℤ) * ((q : ℤ) - 1) / 2 ≤ ∑ x ∈ s, x := hLower
    _ = ∑ i, k i := by
      dsimp [s]
      rw [Finset.sum_image]
      intro i hi j hj hij
      exact hkInjective hij

/-- The `q` positive, distinct weights in one fixed residue class modulo
`2q` have the audited minimum-lift sum. -/
theorem special_pendant_sum_lower_bound
    (q a : ℕ) (p k : Fin q → ℤ)
    (hp : ∀ i, p i = 2 * (a : ℤ) + 2 * (q : ℤ) * k i)
    (hkNonneg : ∀ i, 0 ≤ k i)
    (hpInjective : Function.Injective p) :
    2 * (a : ℤ) * q + (q : ℤ) ^ 2 * ((q : ℤ) - 1) ≤
      ∑ i, p i := by
  have hkInjective : Function.Injective k := by
    intro i j hij
    apply hpInjective
    rw [hp i, hp j, hij]
  have hkLower := distinct_nonnegative_lifts_lower_bound q k hkNonneg hkInjective
  calc
    2 * (a : ℤ) * q + (q : ℤ) ^ 2 * ((q : ℤ) - 1) =
        (q : ℤ) * (2 * a) +
          2 * (q : ℤ) * ((q : ℤ) * ((q : ℤ) - 1) / 2) := by
            have hEven : Even ((q : ℤ) * ((q : ℤ) - 1)) :=
              Int.even_mul_pred_self q
            obtain ⟨z, hz⟩ := hEven
            have hhalf :
                (q : ℤ) * ((q : ℤ) - 1) / 2 = z := by
              apply Int.ediv_eq_of_eq_mul_left (by norm_num : (2 : ℤ) ≠ 0)
              calc
                (q : ℤ) * ((q : ℤ) - 1) = z + z := hz
                _ = z * 2 := by ring
            rw [hhalf]
            nlinarith [hz]
    _ ≤ (q : ℤ) * (2 * a) + 2 * (q : ℤ) * (∑ i, k i) := by
      gcongr
    _ = ∑ i, p i := by
      simp_rw [hp]
      simp [Finset.sum_add_distrib, Finset.mul_sum]

/-! ## Exact differentiated block-moment model -/

/-- The exact information retained after differentiating the complete-block
pair polynomial and collecting coefficients by residue.  `commonMoment` is
the sum of all cross-block terms and the residue-independent part of all
internal terms.  The two displayed equations are derived, respectively, at
residue zero and residue `q-1`; they do not assume a contradiction or a
forced special-weight sum. -/
structure OddCompleteBlockFirstMomentModel (q : ℕ) where
  H : ℤ
  specialWeight : Fin q → ℤ
  lift : Fin q → ℤ
  commonMoment : ℤ
  targetSize : 2 * H = (q : ℤ) * ((q : ℤ) ^ 2 - 1)
  zeroResidueEquation :
    commonMoment = targetZeroResidueMoment q H
  lastResidueEquation :
    commonMoment - (∑ i, specialWeight i) =
      targetNonzeroResidueMoment q H ((q : ℤ) - 1)
  specialLift : ∀ i,
    specialWeight i =
      2 * (oddSpecialIndex q : ℤ) + 2 * (q : ℤ) * lift i
  liftNonnegative : ∀ i, 0 ≤ lift i
  specialDistinct : Function.Injective specialWeight

/-- The exact residue equations force the special pendant-weight sum `H`. -/
theorem odd_complete_block_forced_special_sum
    (q : ℕ) (M : OddCompleteBlockFirstMomentModel q) :
    (∑ i, M.specialWeight i) = M.H := by
  obtain ⟨z, hz⟩ := Int.even_mul_pred_self M.H
  have hEven : Even ((q : ℤ) * M.H * (M.H - 1)) := by
    refine ⟨(q : ℤ) * z, ?_⟩
    calc
      (q : ℤ) * M.H * (M.H - 1) = (q : ℤ) * (M.H * (M.H - 1)) := by ring
      _ = (q : ℤ) * (z + z) := by rw [hz]
      _ = (q : ℤ) * z + (q : ℤ) * z := by ring
  have hdiff := target_last_residue_moment_difference (q : ℤ) M.H hEven
  rw [← M.zeroResidueEquation, ← M.lastResidueEquation] at hdiff
  linarith

/-- Universal contradiction at the exact differentiated complete-block
model.  This is the topology-independent endpoint: quotient shape, weights,
residues, and lifts have disappeared only because their full derivative
contribution is the common residue term recorded above. -/
theorem no_odd_complete_star_block_first_moment_model
    (q : ℕ) (hq : 1 < q) (hqOdd : q % 2 = 1)
    (M : OddCompleteBlockFirstMomentModel q) :
    False := by
  have ha := oddSpecialIndex_spec q hq hqOdd
  have hLower := special_pendant_sum_lower_bound q (oddSpecialIndex q)
    M.specialWeight M.lift M.specialLift M.liftNonnegative M.specialDistinct
  have hSum := odd_complete_block_forced_special_sum q M
  rw [hSum] at hLower
  have hqPos : (0 : ℤ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have haPos : (0 : ℤ) < oddSpecialIndex q := by exact_mod_cast ha.1
  have hGap :
      (q : ℤ) * ((q : ℤ) ^ 2 - 1) <
        2 * (2 * (oddSpecialIndex q : ℤ) * q +
          (q : ℤ) ^ 2 * ((q : ℤ) - 1)) := by
    nlinarith [sq_nonneg ((q : ℤ) - 1)]
  nlinarith [M.targetSize]

/-- Named G018 endpoint.  `OddCompleteBlockFirstMomentModel` is exactly the
residue-moment image of the complete-star-block distance polynomial, so no
model induced by a target spectrum can exist for odd `q>1`. -/
theorem no_odd_complete_star_block_target_spectrum
    (q : ℕ) (hq : 1 < q) (hqOdd : q % 2 = 1) :
    IsEmpty (OddCompleteBlockFirstMomentModel q) := by
  constructor
  intro M
  exact no_odd_complete_star_block_first_moment_model q hq hqOdd M

end LeechTrees.AdditionalBlockLifts
