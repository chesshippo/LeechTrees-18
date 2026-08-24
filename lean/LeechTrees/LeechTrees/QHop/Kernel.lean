import Mathlib

/-!
# Order-18 largest-edge and hop obstructions

This module closes the finite/numerical parts of paper claims T6 and T7.
It deliberately keeps the adapter to the common weighted-tree foundation in
one final section.  In particular, the public obstruction lemmas below do not
take the `11372` cap, the `903` short-sum lower bound, the multiplicity
identity, or the boundary penalty as hypotheses.
-/

open scoped BigOperators

namespace LeechTrees.QHop

/-! ## Elementary extremal sums of distinct natural numbers -/

/-- The `i`th value of a strictly increasing natural-valued tuple is at least
`i`. -/
theorem fin_index_le_of_strictMono {n : ℕ} (f : Fin (n + 1) → ℕ)
    (hf : StrictMono f) (i : Fin (n + 1)) : (i : ℕ) ≤ f i := by
  induction i using Fin.induction with
  | zero => exact Nat.zero_le _
  | succ i ih =>
      have hstep : f i.castSucc < f i.succ := hf (Fin.castSucc_lt_succ i)
      simpa using Nat.succ_le_of_lt (lt_of_le_of_lt ih hstep)

/-- Among `m` distinct natural numbers, the sum is at least
`0 + 1 + ... + (m-1)`. -/
theorem distinctNat_sum_lower (s : Finset ℕ) :
    s.card * (s.card - 1) / 2 ≤ ∑ x ∈ s, x := by
  cases hcard : s.card with
  | zero => simp
  | succ n =>
      let f : Fin (n + 1) → ℕ := s.orderEmbOfFin hcard
      have hpoint : ∀ i : Fin (n + 1), (i : ℕ) ≤ f i :=
        fin_index_le_of_strictMono f (s.orderEmbOfFin hcard).strictMono
      have hsum : (∑ i : Fin (n + 1), (i : ℕ)) ≤
          ∑ i : Fin (n + 1), f i := by
        exact Finset.sum_le_sum fun i _ ↦ hpoint i
      calc
        (n + 1) * (n + 1 - 1) / 2 =
            ∑ i : Fin (n + 1), (i : ℕ) := by
          calc
            (n + 1) * (n + 1 - 1) / 2 = ∑ i ∈ Finset.range (n + 1), i :=
              (Finset.sum_range_id (n + 1)).symm
            _ = ∑ i : Fin (n + 1), (i : ℕ) := by
              simpa using
                (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ i) (n + 1)).symm
        _ ≤ ∑ i : Fin (n + 1), f i := hsum
        _ = ∑ x ∈ Finset.map (s.orderEmbOfFin hcard).toEmbedding Finset.univ, x := by
          simpa [f] using
            (Finset.sum_map Finset.univ (s.orderEmbOfFin hcard).toEmbedding id).symm
        _ = ∑ x ∈ s, x := by rw [s.map_orderEmbOfFin_univ hcard]

/-- Positive distinct naturals start at `1`, so their sum is at least
`1 + ... + card`. -/
theorem distinctPositiveNat_sum_lower
    (s : Finset ℕ) (hpositive : ∀ x ∈ s, 0 < x) :
    s.card * (s.card + 1) / 2 ≤ ∑ x ∈ s, x := by
  let shifted : Finset ℕ := s.image (fun x ↦ x - 1)
  have hinj : Set.InjOn (fun x : ℕ ↦ x - 1) s := by
    intro x hx y hy hxy
    have hxpos := hpositive x hx
    have hypos := hpositive y hy
    have hxback : x - 1 + 1 = x := Nat.sub_add_cancel hxpos
    have hyback : y - 1 + 1 = y := Nat.sub_add_cancel hypos
    change x - 1 = y - 1 at hxy
    omega
  have hcard : shifted.card = s.card := by
    simpa [shifted] using Finset.card_image_iff.mpr hinj
  have hsum_shifted :
      (∑ y ∈ shifted, y) = ∑ x ∈ s, (x - 1) := by
    classical
    exact Finset.sum_image hinj
  have hpartition :
      (∑ y ∈ shifted, y) + s.card = ∑ x ∈ s, x := by
    rw [hsum_shifted,
      show s.card = ∑ x ∈ s, (1 : ℕ) by simp,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    have hxpos := hpositive x hx
    omega
  have hlower := distinctNat_sum_lower shifted
  rw [hcard] at hlower
  have harith : s.card * (s.card + 1) / 2 =
      s.card * (s.card - 1) / 2 + s.card := by
    calc
      s.card * (s.card + 1) / 2 =
          (s.card + 1) * s.card / 2 := by rw [Nat.mul_comm]
      _ = ∑ i ∈ Finset.range (s.card + 1), i :=
        (Finset.sum_range_id (s.card + 1)).symm
      _ = (∑ i ∈ Finset.range s.card, i) + s.card := by
        rw [Finset.sum_range_succ]
      _ = s.card * (s.card - 1) / 2 + s.card := by
        rw [Finset.sum_range_id]
  omega

/-- The largest possible sum of `r` distinct weights drawn from `0,...,18`.
For example `topWeightSum 17 = 170`; the separate presence of weights one
and two will improve the full 17-edge sum by two. -/
def topWeightSum (r : ℕ) : ℕ := ∑ i ∈ Finset.range r, (18 - i)

theorem topWeightSum_mono : Monotone topWeightSum := by
  intro a b hab
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hab)

/-- A finite set of distinct natural weights bounded by 18 has sum no larger
than the sum of the same number of largest members of `0,...,18`. -/
theorem distinctWeights_sum_le_top
    (s : Finset ℕ) (hupper : ∀ x ∈ s, x ≤ 18) :
    (∑ x ∈ s, x) ≤ topWeightSum s.card := by
  let reflected : Finset ℕ := s.image (fun x ↦ 18 - x)
  have hinj : Set.InjOn (fun x : ℕ ↦ 18 - x) s := by
    intro x hx y hy hxy
    have hxle := hupper x hx
    have hyle := hupper y hy
    have hxback : 18 - x + x = 18 := Nat.sub_add_cancel hxle
    have hyback : 18 - y + y = 18 := Nat.sub_add_cancel hyle
    change 18 - x = 18 - y at hxy
    omega
  have hcard : reflected.card = s.card := by
    simpa [reflected] using Finset.card_image_iff.mpr hinj
  have hsum_reflected :
      (∑ y ∈ reflected, y) = ∑ x ∈ s, (18 - x) := by
    classical
    exact Finset.sum_image hinj
  have hpartition :
      (∑ y ∈ reflected, y) + (∑ x ∈ s, x) = 18 * s.card := by
    rw [hsum_reflected, ← Finset.sum_add_distrib]
    calc
      (∑ x ∈ s, ((18 - x) + x)) =
          ∑ x ∈ s, (18 + 0 * x) := by
        exact Finset.sum_congr rfl (fun x hx ↦ by
          have hxle := hupper x hx
          omega)
      _ = 18 * s.card := by simp [Nat.mul_comm]
  have hlower := distinctNat_sum_lower reflected
  rw [hcard] at hlower
  have htop_identity :
      topWeightSum s.card + s.card * (s.card - 1) / 2 = 18 * s.card := by
    unfold topWeightSum
    rw [← Finset.sum_range_id s.card, ← Finset.sum_add_distrib]
    calc
      (∑ i ∈ Finset.range s.card,
          ((18 - i) + i)) =
          ∑ i ∈ Finset.range s.card, (18 + 0 * i) := by
        exact Finset.sum_congr rfl (fun i hi ↦ by
          have hi' : i < s.card := Finset.mem_range.mp hi
          have hcard_le : s.card ≤ 19 := by
            have hs_subset : s ⊆ Finset.range 19 := by
              intro x hx
              have hxle := hupper x hx
              exact Finset.mem_range.mpr (by omega)
            exact le_trans (Finset.card_le_card hs_subset) (by simp)
          omega)
      _ = 18 * s.card := by simp [Nat.mul_comm]
  omega

/-! ## The order-18 cut-profile obstruction -/

/-- Structural output of the selected-core quotient argument.  `leftMass`
and `rightMass` are the masses of two distinct quotient leaves; `restMass`
is the sum of the other positive quotient-vertex masses.  This is a graph
adapter object, not a numerical core-count assumption. -/
structure CoreMassWitness (selectedEdges k : ℕ) : Type where
  leftMass : ℕ
  rightMass : ℕ
  restMass : ℕ
  left_ge : k ≤ leftMass
  right_ge : k ≤ rightMass
  rest_ge : selectedEdges - 1 ≤ restMass
  total : leftMass + rightMass + restMass = 18

/-- Minimal cut-profile interface furnished by an actual order-18 tree.
The `coreMass` field records the quotient components and their masses; the
cardinality inequality used in T6 is proved below rather than stored here. -/
structure Order18CutProfile (E : Type*) [Fintype E] [DecidableEq E] where
  smallerSide : E → ℕ
  smallerSide_pos : ∀ e, 0 < smallerSide e
  smallerSide_le_nine : ∀ e, smallerSide e ≤ 9
  coreMass : ∀ (k : ℕ), 1 ≤ k → k ≤ 9 →
    (Finset.univ.filter (fun e ↦ k ≤ smallerSide e)).Nonempty →
      CoreMassWitness
        (Finset.univ.filter (fun e ↦ k ≤ smallerSide e)).card k

namespace Order18CutProfile

variable {E : Type*} [Fintype E] [DecidableEq E]

def core (D : Order18CutProfile E) (k : ℕ) : Finset E :=
  Finset.univ.filter (fun e ↦ k ≤ D.smallerSide e)

/-- The selected-core quotient masses imply the corrected, empty-case-safe
core count in subtraction-free form. -/
theorem core_count_add (D : Order18CutProfile E) (k : ℕ)
    (hk : 1 ≤ k) (hk9 : k ≤ 9) :
    (D.core k).card + 2 * k ≤ 19 := by
  by_cases hempty : D.core k = ∅
  · simp [hempty]
    omega
  · have hnonempty : (D.core k).Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    let W := D.coreMass k hk hk9 (by simpa [core] using hnonempty)
    have hleft := W.left_ge
    have hright := W.right_ge
    have hrest : (D.core k).card - 1 ≤ W.restMass := by
      simpa [core] using W.rest_ge
    have htotal := W.total
    omega

end Order18CutProfile

/-- All primitive data about an order-18 Leech tree needed by the T6
numerical argument.  The adapter from the shared foundation must derive every
field from the actual tree and `IsLeech`; none is the result-critical 11372
cap or its rearrangement. -/
structure Order18LeechCutData (E : Type*) [Fintype E] [DecidableEq E] where
  cut : Order18CutProfile E
  edge_count : Fintype.card E = 17
  weight : E → ℕ
  weight_pos : ∀ e, 0 < weight e
  weight_injective : Function.Injective weight
  weight_one : ∃ e, weight e = 1
  weight_two : ∃ e, weight e = 2
  checksum :
    (∑ e, (cut.smallerSide e * (18 - cut.smallerSide e)) * weight e) = 11781

namespace Order18LeechCutData

variable {E : Type*} [Fintype E] [DecidableEq E]

def largestPhysicalWeight (D : Order18LeechCutData E) : ℕ :=
  Finset.univ.sup D.weight

theorem weight_le_largest (D : Order18LeechCutData E) (e : E) :
    D.weight e ≤ D.largestPhysicalWeight := by
  exact Finset.le_sup (Finset.mem_univ e)

def levelWeightSum (D : Order18LeechCutData E) (k : ℕ) : ℕ :=
  ∑ e ∈ D.cut.core k, D.weight e

/-- The coefficient `s(18-s)` is the sum of the nine odd layer increments
through level `s`. -/
theorem cutCoefficient_eq_layers (s : ℕ) (hs : 0 < s) (hs9 : s ≤ 9) :
    s * (18 - s) =
      (if 1 ≤ s then 17 else 0) +
      (if 2 ≤ s then 15 else 0) +
      (if 3 ≤ s then 13 else 0) +
      (if 4 ≤ s then 11 else 0) +
      (if 5 ≤ s then 9 else 0) +
      (if 6 ≤ s then 7 else 0) +
      (if 7 ≤ s then 5 else 0) +
      (if 8 ≤ s then 3 else 0) +
      (if 9 ≤ s then 1 else 0) := by
  interval_cases s <;> norm_num

theorem indicatorLayer_sum (D : Order18LeechCutData E) (k a : ℕ) :
    (∑ e, (if k ≤ D.cut.smallerSide e then a else 0) * D.weight e) =
      a * D.levelWeightSum k := by
  classical
  unfold levelWeightSum Order18CutProfile.core
  rw [Finset.mul_sum]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : k ≤ D.cut.smallerSide e <;> simp [h]

/-- Layer-cake form of the cut checksum.  This is the rearrangement step in
a threshold-count form: it keeps the common actual edge index throughout. -/
theorem checksum_eq_levelWeightSums (D : Order18LeechCutData E) :
    (∑ e, (D.cut.smallerSide e * (18 - D.cut.smallerSide e)) * D.weight e) =
      17 * D.levelWeightSum 1 +
      15 * D.levelWeightSum 2 +
      13 * D.levelWeightSum 3 +
      11 * D.levelWeightSum 4 +
       9 * D.levelWeightSum 5 +
       7 * D.levelWeightSum 6 +
       5 * D.levelWeightSum 7 +
       3 * D.levelWeightSum 8 +
           D.levelWeightSum 9 := by
  classical
  calc
    (∑ e, (D.cut.smallerSide e * (18 - D.cut.smallerSide e)) * D.weight e) =
        ∑ e, (((if 1 ≤ D.cut.smallerSide e then 17 else 0) +
          (if 2 ≤ D.cut.smallerSide e then 15 else 0) +
          (if 3 ≤ D.cut.smallerSide e then 13 else 0) +
          (if 4 ≤ D.cut.smallerSide e then 11 else 0) +
          (if 5 ≤ D.cut.smallerSide e then 9 else 0) +
          (if 6 ≤ D.cut.smallerSide e then 7 else 0) +
          (if 7 ≤ D.cut.smallerSide e then 5 else 0) +
          (if 8 ≤ D.cut.smallerSide e then 3 else 0) +
          (if 9 ≤ D.cut.smallerSide e then 1 else 0)) * D.weight e) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [cutCoefficient_eq_layers (D.cut.smallerSide e)
        (D.cut.smallerSide_pos e) (D.cut.smallerSide_le_nine e)]
    _ = 17 * D.levelWeightSum 1 +
        15 * D.levelWeightSum 2 +
        13 * D.levelWeightSum 3 +
        11 * D.levelWeightSum 4 +
         9 * D.levelWeightSum 5 +
         7 * D.levelWeightSum 6 +
         5 * D.levelWeightSum 7 +
         3 * D.levelWeightSum 8 +
             D.levelWeightSum 9 := by
      simp_rw [add_mul]
      repeat' rw [Finset.sum_add_distrib]
      rw [D.indicatorLayer_sum 1 17, D.indicatorLayer_sum 2 15,
        D.indicatorLayer_sum 3 13, D.indicatorLayer_sum 4 11,
        D.indicatorLayer_sum 5 9, D.indicatorLayer_sum 6 7,
        D.indicatorLayer_sum 7 5, D.indicatorLayer_sum 8 3,
        D.indicatorLayer_sum 9 1]
      simp

/-- Values of weights on a level core, as a finset. -/
def levelWeightValues (D : Order18LeechCutData E) (k : ℕ) : Finset ℕ :=
  (D.cut.core k).image D.weight

theorem card_levelWeightValues (D : Order18LeechCutData E) (k : ℕ) :
    (D.levelWeightValues k).card = (D.cut.core k).card := by
  apply Finset.card_image_iff.mpr
  exact D.weight_injective.injOn

theorem sum_levelWeightValues (D : Order18LeechCutData E) (k : ℕ) :
    (∑ w ∈ D.levelWeightValues k, w) = D.levelWeightSum k := by
  classical
  exact Finset.sum_image D.weight_injective.injOn

/-- Each noninitial level sum is bounded by the appropriate top-weight sum,
using the proved core count and distinct actual physical weights. -/
theorem levelWeightSum_le_top (D : Order18LeechCutData E)
    (hall : ∀ e, D.weight e ≤ 18)
    (k : ℕ) (hk : 1 ≤ k) (hk9 : k ≤ 9) :
    D.levelWeightSum k ≤ topWeightSum (19 - 2 * k) := by
  have hupper : ∀ w ∈ D.levelWeightValues k, w ≤ 18 := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨e, _, rfl⟩
    exact hall e
  have hraw := distinctWeights_sum_le_top (D.levelWeightValues k) hupper
  rw [sum_levelWeightValues, card_levelWeightValues] at hraw
  have hcount_add := D.cut.core_count_add k hk hk9
  have hcount : (D.cut.core k).card ≤ 19 - 2 * k := by omega
  exact hraw.trans (topWeightSum_mono hcount)

/-- Seventeen distinct positive weights at most 18 that contain weights one
and two have total at most 168 (the maximal vector omits 3). -/
theorem allWeights_sum_le_168 (D : Order18LeechCutData E)
    (hall : ∀ e, D.weight e ≤ 18) :
    (∑ e, D.weight e) ≤ 168 := by
  classical
  let values : Finset ℕ := Finset.univ.image D.weight
  let ambient : Finset ℕ := Finset.Icc 1 18
  have hvalues_card : values.card = 17 := by
    rw [Finset.card_image_iff.mpr D.weight_injective.injOn,
      Finset.card_univ, D.edge_count]
  have hambient_card : ambient.card = 18 := by decide
  have hsubset : values ⊆ ambient := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨e, _, rfl⟩
    exact Finset.mem_Icc.mpr ⟨D.weight_pos e, hall e⟩
  have hmissing_card : (ambient \ values).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsubset, hambient_card, hvalues_card]
  obtain ⟨missing, hmissing_eq⟩ := Finset.card_eq_one.mp hmissing_card
  have hmissing_mem : missing ∈ ambient \ values := by simp [hmissing_eq]
  have hmissing_ge : 3 ≤ missing := by
    have hmU := (Finset.mem_sdiff.mp hmissing_mem).1
    have hmnot := (Finset.mem_sdiff.mp hmissing_mem).2
    have hone : 1 ∈ values := by
      rcases D.weight_one with ⟨e, he⟩
      exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, he⟩
    have htwo : 2 ∈ values := by
      rcases D.weight_two with ⟨e, he⟩
      exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, he⟩
    have hmBounds := Finset.mem_Icc.mp hmU
    have hm1 : missing ≠ 1 := fun hm ↦ hmnot (hm ▸ hone)
    have hm2 : missing ≠ 2 := fun hm ↦ hmnot (hm ▸ htwo)
    omega
  have hsum_partition :
      (∑ w ∈ ambient \ values, w) + (∑ w ∈ values, w) =
        ∑ w ∈ ambient, w := by
    rw [← Finset.sum_union (Finset.sdiff_disjoint),
      Finset.sdiff_union_of_subset hsubset]
  have hmissing_sum : ∑ w ∈ ambient \ values, w = missing := by
    simp [hmissing_eq]
  have hambient_sum : ∑ w ∈ ambient, w = 171 := by decide
  have hvalues_sum : (∑ w ∈ values, w) = ∑ e, D.weight e := by
    exact Finset.sum_image D.weight_injective.injOn
  omega

/-- Full internally derived `Q ≤ 18` checksum cap. -/
theorem checksum_le_11372_of_largest_le_18 (D : Order18LeechCutData E)
    (hQ : D.largestPhysicalWeight ≤ 18) :
    (∑ e, (D.cut.smallerSide e * (18 - D.cut.smallerSide e)) * D.weight e)
      ≤ 11372 := by
  have hall : ∀ e, D.weight e ≤ 18 := fun e ↦
    (D.weight_le_largest e).trans hQ
  have h1 : D.levelWeightSum 1 ≤ 168 := by
    have hcore_one : D.cut.core 1 = Finset.univ := by
      ext e
      have hside_one : 1 ≤ D.cut.smallerSide e := D.cut.smallerSide_pos e
      simp [Order18CutProfile.core, hside_one]
    simpa [levelWeightSum, hcore_one] using D.allWeights_sum_le_168 hall
  have h2 := D.levelWeightSum_le_top hall 2 (by decide) (by decide)
  have h3 := D.levelWeightSum_le_top hall 3 (by decide) (by decide)
  have h4 := D.levelWeightSum_le_top hall 4 (by decide) (by decide)
  have h5 := D.levelWeightSum_le_top hall 5 (by decide) (by decide)
  have h6 := D.levelWeightSum_le_top hall 6 (by decide) (by decide)
  have h7 := D.levelWeightSum_le_top hall 7 (by decide) (by decide)
  have h8 := D.levelWeightSum_le_top hall 8 (by decide) (by decide)
  have h9 := D.levelWeightSum_le_top hall 9 (by decide) (by decide)
  norm_num [topWeightSum] at h2 h3 h4 h5 h6 h7 h8 h9
  rw [D.checksum_eq_levelWeightSums]
  omega

/-- Claim-level T6 conclusion for the exact actual-edge profile: the maximum
physical edge weight is at least 19. -/
theorem largestPhysicalWeight_ge_19 (D : Order18LeechCutData E) :
    19 ≤ D.largestPhysicalWeight := by
  by_contra hnot
  have hQ : D.largestPhysicalWeight ≤ 18 := by omega
  have hcap := D.checksum_le_11372_of_largest_le_18 hQ
  rw [D.checksum] at hcap
  omega

end Order18LeechCutData

/-! ## The 42-short-sum obstruction -/

/-- The 42 intervals of one, two, or three consecutive gaps on a 15-edge
path, listed explicitly so their cardinality and multiplicities reduce in the
kernel without an interval-indexing API. -/
def shortSums (g : Fin 15 → ℕ) : List ℕ :=
  [g 0, g 1, g 2, g 3, g 4, g 5, g 6, g 7, g 8, g 9,
   g 10, g 11, g 12, g 13, g 14,
   g 0 + g 1, g 1 + g 2, g 2 + g 3, g 3 + g 4,
   g 4 + g 5, g 5 + g 6, g 6 + g 7, g 7 + g 8,
   g 8 + g 9, g 9 + g 10, g 10 + g 11, g 11 + g 12,
   g 12 + g 13, g 13 + g 14,
   g 0 + g 1 + g 2, g 1 + g 2 + g 3, g 2 + g 3 + g 4,
   g 3 + g 4 + g 5, g 4 + g 5 + g 6, g 5 + g 6 + g 7,
   g 6 + g 7 + g 8, g 7 + g 8 + g 9, g 8 + g 9 + g 10,
   g 9 + g 10 + g 11, g 10 + g 11 + g 12,
   g 11 + g 12 + g 13, g 12 + g 13 + g 14]

@[simp] theorem shortSums_length (g : Fin 15 → ℕ) :
    (shortSums g).length = 42 := by
  simp [shortSums]

/-- Exact multiplicity identity for the 42 selected intervals.  The
subtraction-free form is intentionally used over naturals. -/
theorem shortSums_multiplicity (g : Fin 15 → ℕ) :
    (shortSums g).sum + (3 * g 0 + g 1 + g 13 + 3 * g 14) =
      6 * (∑ i, g i) := by
  simp [shortSums, Fin.sum_univ_succ]
  ring

/-- Forty-two distinct positive natural numbers have total at least 903. -/
theorem fortyTwoDistinctPositive_sum_ge
    (xs : List ℕ) (hlen : xs.length = 42)
    (hnodup : xs.Nodup) (hpositive : ∀ x ∈ xs, 0 < x) :
    903 ≤ xs.sum := by
  let s := xs.toFinset
  have hcard : s.card = 42 := by
    exact (List.toFinset_card_of_nodup hnodup).trans hlen
  have hsum : (∑ x ∈ s, x) = xs.sum := by
    simpa [s] using (List.sum_toFinset id hnodup)
  have hspositive : ∀ x ∈ s, 0 < x := by
    intro x hx
    exact hpositive x (by simpa [s] using hx)
  have hlower := distinctPositiveNat_sum_lower s hspositive
  rw [hcard] at hlower
  norm_num at hlower
  simpa [hsum] using hlower

/-- The four boundary gaps force the weighted penalty 16. -/
theorem boundaryPenalty_ge_sixteen
    (a b c d : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    16 ≤ 3 * a + b + c + 3 * d := by
  omega

/-- Dependency-closed 15-gap numerical obstruction.  Its only inputs are the
primitive path facts: positive gaps, global distinctness of the 42 interval
sums, and endpoint length at most 153. -/
theorem no_fifteen_gap_sequence
    (g : Fin 15 → ℕ)
    (hpositive : ∀ i, 0 < g i)
    (hshort_nodup : (shortSums g).Nodup)
    (hlength : (∑ i, g i) ≤ 153) : False := by
  have hshort_positive : ∀ x ∈ shortSums g, 0 < x := by
    intro x hx
    have hp0 := hpositive 0
    have hp1 := hpositive 1
    have hp2 := hpositive 2
    have hp3 := hpositive 3
    have hp4 := hpositive 4
    have hp5 := hpositive 5
    have hp6 := hpositive 6
    have hp7 := hpositive 7
    have hp8 := hpositive 8
    have hp9 := hpositive 9
    have hp10 := hpositive 10
    have hp11 := hpositive 11
    have hp12 := hpositive 12
    have hp13 := hpositive 13
    have hp14 := hpositive 14
    simp only [shortSums, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals omega
  have hsum_lower : 903 ≤ (shortSums g).sum :=
    fortyTwoDistinctPositive_sum_ge (shortSums g) (shortSums_length g)
      hshort_nodup hshort_positive
  have hgap_get (i : Fin 15) :
      (shortSums g).get ⟨i, by simpa using lt_of_lt_of_le i.isLt (by decide : 15 ≤ 42)⟩ = g i := by
    fin_cases i <;> rfl
  have hgap_injective : Function.Injective g := by
    intro i j hij
    have hgeteq :
        (shortSums g).get ⟨i, by simpa using lt_of_lt_of_le i.isLt (by decide : 15 ≤ 42)⟩ =
        (shortSums g).get ⟨j, by simpa using lt_of_lt_of_le j.isLt (by decide : 15 ≤ 42)⟩ := by
      rw [hgap_get i, hgap_get j]
      exact hij
    have hindex := hshort_nodup.get_inj_iff.mp hgeteq
    have hval : (i : ℕ) = (j : ℕ) := by
      exact congrArg (fun z : Fin (shortSums g).length ↦ (z : ℕ)) hindex
    exact Fin.ext hval
  have hpenalty : 16 ≤ 3 * g 0 + g 1 + g 13 + 3 * g 14 := by
    apply boundaryPenalty_ge_sixteen
    · exact hpositive 0
    · exact hpositive 1
    · exact hpositive 13
    · exact hpositive 14
    · exact hgap_injective.ne (by decide)
    · exact hgap_injective.ne (by decide)
    · exact hgap_injective.ne (by decide)
    · exact hgap_injective.ne (by decide)
    · exact hgap_injective.ne (by decide)
    · exact hgap_injective.ne (by decide)
  have hmult := shortSums_multiplicity g
  omega

end LeechTrees.QHop
