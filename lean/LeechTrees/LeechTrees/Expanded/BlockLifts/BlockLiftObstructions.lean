import LeechTrees.CombinatorialCore
import Mathlib

/-!
# Exact block-lift obstructions

This module contains the symbolic content of claim G017.  Every endpoint is
restricted to the named block or gadget architecture.  In particular, none
of the results is an exclusion of arbitrary order-18 weighted trees.
-/

open scoped BigOperators

namespace LeechTrees.AdditionalBlockLifts

/-! ## Two uniformly scaled complete spectra -/

/-- General collision kernel.  A block with complete internal spectrum
`s * {1,...,M}` and a second block with spectrum `t * {1,...,M}` collide at
`s*t` whenever the range bound forces both scale factors to be at most `M`.
The hypotheses `M*s <= N` and `M*t <= N` are the diameter consequences in a
target whose largest distance is `N`. -/
theorem two_scaled_complete_spectra_collision
    (N M s t : ℕ)
    (hM : 0 < M) (hs : 0 < s) (ht : 0 < t)
    (hsRange : M * s ≤ N) (htRange : M * t ≤ N)
    (hCap : N / M ≤ M) :
    ∃ k l : ℕ,
      1 ≤ k ∧ k ≤ M ∧ 1 ≤ l ∧ l ≤ M ∧ s * k = t * l := by
  have hsDiv : s ≤ N / M := by
    apply (Nat.le_div_iff_mul_le hM).2
    simpa [Nat.mul_comm] using hsRange
  have htDiv : t ≤ N / M := by
    apply (Nat.le_div_iff_mul_le hM).2
    simpa [Nat.mul_comm] using htRange
  refine ⟨t, s, ht, htDiv.trans hCap, hs, hsDiv.trans hCap, ?_⟩
  exact Nat.mul_comm s t

/-- The numerical order-18/order-six instance: two positive scales whose
fifteen-term spectra fit below 153 have a common represented distance. -/
theorem two_scaled_orderSix_blocks_collide
    (s t : ℕ) (hs : 0 < s) (ht : 0 < t)
    (hsRange : 15 * s ≤ 153) (htRange : 15 * t ≤ 153) :
    ∃ k l : ℕ,
      1 ≤ k ∧ k ≤ 15 ∧ 1 ≤ l ∧ l ≤ 15 ∧ s * k = t * l := by
  exact two_scaled_complete_spectra_collision 153 15 s t (by omega)
    hs ht hsRange htRange (by norm_num)

/-! ## Exact three-block parity gate -/

/-- Allowed absolute imbalance of an arbitrary six-vertex block. -/
def SixVertexMagnitude (d : ℤ) : Prop :=
  d = 0 ∨ d = 2 ∨ d = 4 ∨ d = 6

/-- The topology-free sign gate when the two bridge parities are still free. -/
def ThreeBlockParityFeasible (d₁ d₂ d₃ : ℤ) : Prop :=
  ∃ ε₁ ε₂ ε₃ : ℤ,
    (ε₁ = 1 ∨ ε₁ = -1) ∧
    (ε₂ = 1 ∨ ε₂ = -1) ∧
    (ε₃ = 1 ∨ ε₃ = -1) ∧
    |ε₁ * d₁ + ε₂ * d₂ + ε₃ * d₃| = 4

/-- The seven nondecreasing magnitude profiles in the exact order-18 gate. -/
def IsSevenFeasibleProfile (d₁ d₂ d₃ : ℤ) : Prop :=
  (d₁ = 0 ∧ d₂ = 0 ∧ d₃ = 4) ∨
  (d₁ = 0 ∧ d₂ = 2 ∧ d₃ = 2) ∨
  (d₁ = 0 ∧ d₂ = 2 ∧ d₃ = 6) ∨
  (d₁ = 2 ∧ d₂ = 2 ∧ d₃ = 4) ∨
  (d₁ = 2 ∧ d₂ = 4 ∧ d₃ = 6) ∨
  (d₁ = 4 ∧ d₂ = 4 ∧ d₃ = 4) ∨
  (d₁ = 4 ∧ d₂ = 6 ∧ d₃ = 6)

/-- Exhaustive symbolic classification of the twenty sorted triples from
`{0,2,4,6}`. -/
theorem three_six_vertex_magnitude_profiles
    (d₁ d₂ d₃ : ℤ)
    (h₁ : SixVertexMagnitude d₁)
    (h₂ : SixVertexMagnitude d₂)
    (h₃ : SixVertexMagnitude d₃)
    (hSorted : d₁ ≤ d₂ ∧ d₂ ≤ d₃) :
    ThreeBlockParityFeasible d₁ d₂ d₃ ↔
      IsSevenFeasibleProfile d₁ d₂ d₃ := by
  constructor
  · rintro ⟨ε₁, ε₂, ε₃, hε₁, hε₂, hε₃, hsum⟩
    rcases hSorted with ⟨h₁₂, h₂₃⟩
    rcases h₁ with rfl | rfl | rfl | rfl <;>
      rcases h₂ with rfl | rfl | rfl | rfl <;>
      rcases h₃ with rfl | rfl | rfl | rfl <;>
      rcases hε₁ with rfl | rfl <;>
      rcases hε₂ with rfl | rfl <;>
      rcases hε₃ with rfl | rfl
    all_goals norm_num at hsum
    all_goals norm_num at h₁₂
    all_goals norm_num at h₂₃
    all_goals norm_num [IsSevenFeasibleProfile]
  · intro h
    rcases h with h | h | h | h | h | h | h
    · rcases h with ⟨rfl, rfl, rfl⟩
      exact ⟨1, 1, 1, Or.inl rfl, Or.inl rfl, Or.inl rfl, by norm_num⟩
    · rcases h with ⟨rfl, rfl, rfl⟩
      exact ⟨1, 1, 1, Or.inl rfl, Or.inl rfl, Or.inl rfl, by norm_num⟩
    · rcases h with ⟨rfl, rfl, rfl⟩
      exact ⟨1, -1, 1, Or.inl rfl, Or.inr rfl, Or.inl rfl, by norm_num⟩
    · rcases h with ⟨rfl, rfl, rfl⟩
      exact ⟨1, -1, 1, Or.inl rfl, Or.inr rfl, Or.inl rfl, by norm_num⟩
    · rcases h with ⟨rfl, rfl, rfl⟩
      exact ⟨1, -1, 1, Or.inl rfl, Or.inr rfl, Or.inl rfl, by norm_num⟩
    · rcases h with ⟨rfl, rfl, rfl⟩
      exact ⟨1, 1, -1, Or.inl rfl, Or.inl rfl, Or.inr rfl, by norm_num⟩
    · rcases h with ⟨rfl, rfl, rfl⟩
      exact ⟨1, 1, -1, Or.inl rfl, Or.inl rfl, Or.inr rfl, by norm_num⟩

/-- Each uniformly scaled order-six witness contributes signed imbalance
`±2` at odd scale or `±6` at even scale.  Three such contributions cannot
have absolute total four. -/
theorem three_scaled_six_blocks_fail_order18_parity
    (x₁ x₂ x₃ : ℤ)
    (h₁ : x₁ = 2 ∨ x₁ = -2 ∨ x₁ = 6 ∨ x₁ = -6)
    (h₂ : x₂ = 2 ∨ x₂ = -2 ∨ x₂ = 6 ∨ x₂ = -6)
    (h₃ : x₃ = 2 ∨ x₃ = -2 ∨ x₃ = 6 ∨ x₃ = -6) :
    |x₁ + x₂ + x₃| ≠ 4 := by
  rcases h₁ with rfl | rfl | rfl | rfl <;>
    rcases h₂ with rfl | rfl | rfl | rfl <;>
    rcases h₃ with rfl | rfl | rfl | rfl <;> norm_num

/-- Indexed `3×3` difference criterion.  It is deliberately phrased with
functions rather than support sets, so repeated rooted depths retain their
multiplicity. -/
theorem threeByThree_sums_injective_iff_difference
    (α β : Fin 3 → ℤ) :
    Function.Injective (LeechTrees.crossSum α β) ↔
      ∀ a a' b b',
        α a - α a' = β b' - β b → a = a' ∧ b = b' :=
  LeechTrees.crossSum_injective_iff α β

/-! ## Recursive center-gadget parity obstruction -/

/-- Sign `(-1)^b`, with `true` representing odd parity. -/
def paritySign (b : Bool) : ℤ := if b then -1 else 1

/-- Parity sign of a natural edge weight. -/
def weightParitySign (w : ℕ) : ℤ := if w % 2 = 1 then -1 else 1

@[simp] theorem weightParitySign_eq_paritySign (w : ℕ) :
    weightParitySign w = paritySign (decide (w % 2 = 1)) := by
  simp [weightParitySign, paritySign]

/-- Multiplicativity of the parity sign. -/
theorem weightParitySign_add (u v : ℕ) :
    weightParitySign (u + v) =
      weightParitySign u * weightParitySign v := by
  have hu : u % 2 = 0 ∨ u % 2 = 1 := by omega
  have hv : v % 2 = 0 ∨ v % 2 = 1 := by omega
  rcases hu with hu | hu <;> rcases hv with hv | hv <;>
    simp [weightParitySign, hu, hv, Nat.add_mod]

/-- A congruence modulo two gives the same parity sign. -/
theorem weightParitySign_eq_of_mod_two_eq
    (u v : ℕ) (h : u % 2 = v % 2) :
    weightParitySign u = weightParitySign v := by
  simp [weightParitySign, h]

@[simp] theorem paritySign_sq (b : Bool) : paritySign b * paritySign b = 1 := by
  cases b <;> norm_num [paritySign]

/-- Edge propagation makes `tau(v) * (-1)^b(v)` constant along a walk. -/
theorem gaugeInvariant_of_walk
    {V : Type*} (G : SimpleGraph V)
    (b : V → Bool) (τ : V → ℤ)
    (edgeRule : ∀ ⦃u v⦄, G.Adj u v →
      τ v = τ u * paritySign (b u) * paritySign (b v))
    {u v : V} (p : G.Walk u v) :
    τ v * paritySign (b v) = τ u * paritySign (b u) := by
  induction p with
  | nil => rfl
  | @cons u v w huv p ih =>
      calc
        τ w * paritySign (b w) = τ v * paritySign (b v) := ih
        _ = (τ u * paritySign (b u) * paritySign (b v)) *
              paritySign (b v) := by rw [edgeRule huv]
        _ = τ u * paritySign (b u) := by
          rw [mul_assoc, paritySign_sq, mul_one]

/-- On a connected macro graph, the bridge parity rule has the unique
vertex-gauge form used in the digit-lift obstruction. -/
theorem connected_center_bridge_gauge
    {V : Type*} [Nonempty V]
    (G : SimpleGraph V) (hG : G.Connected)
    (b : V → Bool) (τ : V → ℤ)
    (edgeRule : ∀ ⦃u v⦄, G.Adj u v →
      τ v = τ u * paritySign (b u) * paritySign (b v)) :
    ∃ κ : ℤ, ∀ v, τ v = κ * paritySign (b v) := by
  classical
  let root : V := Classical.choice inferInstance
  refine ⟨τ root * paritySign (b root), ?_⟩
  intro v
  obtain ⟨p⟩ := hG root v
  have hInv := gaugeInvariant_of_walk G b τ edgeRule p
  calc
    τ v = (τ v * paritySign (b v)) * paritySign (b v) := by
      rw [mul_assoc, paritySign_sq, mul_one]
    _ = (τ root * paritySign (b root)) * paritySign (b v) := by rw [hInv]

/-- Local center-rooted three-vertex imbalance: one at odd scale, three at
even scale. -/
def centerGadgetLocalImbalance (scaleOdd : Bool) : ℤ :=
  if scaleOdd then 1 else 3

/-- The gauged contribution is `-1` for an odd scale and `3` for an even
scale. -/
@[simp] theorem paritySign_mul_local (b : Bool) :
    paritySign b * centerGadgetLocalImbalance b =
      if b then -1 else 3 := by
  cases b <;> norm_num [paritySign, centerGadgetLocalImbalance]

/-- Six terms, each `-1` or `3`, can never sum to `±4`. -/
theorem six_center_gadget_contributions_ne_four
    (b : Fin 6 → Bool) :
    (∑ i, (if b i then (-1 : ℤ) else 3)) ≠ 4 ∧
    (∑ i, (if b i then (-1 : ℤ) else 3)) ≠ -4 := by
  classical
  let e : ℕ := (Finset.univ.filter fun i => b i = false).card
  have he : e ≤ 6 := by
    dsimp [e]
    simpa using Finset.card_filter_le (s := (Finset.univ : Finset (Fin 6)))
      (p := fun i => b i = false)
  have hcount :
      (∑ i : Fin 6, if b i = false then (1 : ℤ) else 0) = (e : ℤ) := by
    dsimp [e]
    exact Finset.sum_boole (R := ℤ)
      (fun i : Fin 6 => b i = false) Finset.univ
  have hsum : (∑ i, (if b i then (-1 : ℤ) else 3)) = 4 * (e : ℤ) - 6 := by
    calc
      (∑ i, (if b i then (-1 : ℤ) else 3)) =
          ∑ i, (4 * (if b i = false then (1 : ℤ) else 0) - 1) := by
            apply Finset.sum_congr rfl
            intro i _hi
            cases b i <;> norm_num
      _ = 4 * (∑ i, if b i = false then (1 : ℤ) else 0) -
          ∑ _i : Fin 6, (1 : ℤ) := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = 4 * (e : ℤ) - 6 := by norm_num [hcount]
  constructor <;> rw [hsum] <;> omega

/-- Exact topology-independent endpoint for the recursive six-gadget center
lift.  `b i` is the parity of scale `s_i`; `edgeRule` is precisely the sign
form of `q_ij ≡ s_i+s_j (mod 2)`.  Connectivity is the only graph property
used, so the theorem covers every six-vertex macro tree. -/
theorem center_digit_lift_parity_obstruction_every_connected_macro_graph
    (G : SimpleGraph (Fin 6)) (hG : G.Connected)
    (b : Fin 6 → Bool) (τ : Fin 6 → ℤ)
    (hτ : ∀ i, τ i = 1 ∨ τ i = -1)
    (edgeRule : ∀ ⦃u v⦄, G.Adj u v →
      τ v = τ u * paritySign (b u) * paritySign (b v)) :
    let Δ := ∑ i, τ i * centerGadgetLocalImbalance (b i)
    Δ ≠ 4 ∧ Δ ≠ -4 := by
  obtain ⟨κ, hκ⟩ := connected_center_bridge_gauge G hG b τ edgeRule
  have hκsign : κ = 1 ∨ κ = -1 := by
    have hroot := hτ 0
    have hk := hκ 0
    rcases hroot with hroot | hroot <;> cases h : b 0 <;>
      simp [paritySign, h, hroot] at hk ⊢ <;> omega
  dsimp only
  have hsum : (∑ i, τ i * centerGadgetLocalImbalance (b i)) =
      κ * ∑ i, (if b i then (-1 : ℤ) else 3) := by
    calc
      (∑ i, τ i * centerGadgetLocalImbalance (b i)) =
          ∑ i, κ * (if b i then (-1 : ℤ) else 3) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hκ i]
            simp [mul_assoc]
      _ = κ * ∑ i, (if b i then (-1 : ℤ) else 3) := by
        rw [Finset.mul_sum]
  have hbase := six_center_gadget_contributions_ne_four b
  rcases hκsign with rfl | rfl <;> simp only [one_mul, neg_one_mul] at hsum ⊢ <;>
    omega

/-- The same endpoint with literal scale and bridge-weight inputs.  The only
assumption on a macro edge is the audited congruence
`q_uv ≡ scale_u+scale_v (mod 2)`. -/
theorem center_digit_lift_of_bridge_congruence_impossible
    (G : SimpleGraph (Fin 6)) (hG : G.Connected)
    (scale : Fin 6 → ℕ) (bridgeWeight : Fin 6 → Fin 6 → ℕ)
    (τ : Fin 6 → ℤ)
    (hτ : ∀ i, τ i = 1 ∨ τ i = -1)
    (bridgeParity : ∀ ⦃u v⦄, G.Adj u v →
      bridgeWeight u v % 2 = (scale u + scale v) % 2)
    (globalSignRule : ∀ ⦃u v⦄, G.Adj u v →
      τ v = τ u * weightParitySign (bridgeWeight u v)) :
    let Δ := ∑ i, τ i *
      centerGadgetLocalImbalance (decide (scale i % 2 = 1))
    Δ ≠ 4 ∧ Δ ≠ -4 := by
  apply center_digit_lift_parity_obstruction_every_connected_macro_graph
    G hG (fun i => decide (scale i % 2 = 1)) τ hτ
  intro u v huv
  rw [globalSignRule huv]
  rw [weightParitySign_eq_of_mod_two_eq _ _ (bridgeParity huv)]
  rw [weightParitySign_add]
  simp only [weightParitySign_eq_paritySign]
  exact (mul_assoc _ _ _).symm

/-! ## Exact 153-form three-block model -/

/-- Forty-five within-block indices plus three Cartesian `6×6` cross blocks. -/
abbrev ThreeBlockIndex :=
  (Fin 3 × Fin 15) ⊕
    ((Fin 6 × Fin 6) ⊕ ((Fin 6 × Fin 6) ⊕ (Fin 6 × Fin 6)))

theorem threeBlockIndex_card : Fintype.card ThreeBlockIndex = 153 := by
  calc
    Fintype.card ThreeBlockIndex =
        3 * 15 + (6 * 6 + (6 * 6 + 6 * 6)) := by
      simp only [ThreeBlockIndex, Fintype.card_sum, Fintype.card_prod,
        Fintype.card_fin]
    _ = 153 := by norm_num

/-- Data appearing in the exact outer/middle/outer path decomposition. -/
structure ThreeBlockPathForms where
  internal : Fin 3 → Fin 15 → ℕ
  leftDepth : Fin 6 → ℕ
  middleFromLeft : Fin 6 → ℕ
  middleToRight : Fin 6 → ℕ
  rightDepth : Fin 6 → ℕ
  middlePortSeparation : ℕ
  leftBridge : ℕ
  rightBridge : ℕ

/-- The exact 153 linear forms, retaining the actual middle entry/exit-port
separation. -/
def ThreeBlockPathForms.rank (D : ThreeBlockPathForms) :
    ThreeBlockIndex → ℕ
  | .inl z => D.internal z.1 z.2
  | .inr (.inl z) =>
      D.leftDepth z.1 + D.leftBridge + D.middleFromLeft z.2
  | .inr (.inr (.inl z)) =>
      D.middleToRight z.1 + D.rightBridge + D.rightDepth z.2
  | .inr (.inr (.inr z)) =>
      D.leftDepth z.1 + D.leftBridge + D.middlePortSeparation +
        D.rightBridge + D.rightDepth z.2

/-- Multiplicity-preserving spectrum of the exact 153 indexed forms. -/
def ThreeBlockPathForms.spectrum (D : ThreeBlockPathForms) : Finset ℕ :=
  Finset.univ.image D.rank

/-- Bounds plus `AllDifferent` imply the complete target spectrum, because
there are exactly 153 indexed forms in the 153-element interval. -/
theorem threeBlock_target_of_bounds_injective
    (D : ThreeBlockPathForms)
    (bounds : ∀ i, 1 ≤ D.rank i ∧ D.rank i ≤ 153)
    (allDifferent : Function.Injective D.rank) :
    D.spectrum = Finset.Icc 1 153 := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [ThreeBlockPathForms.spectrum, Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact Finset.mem_Icc.mpr (bounds i)
  · rw [Nat.card_Icc]
    norm_num
    rw [ThreeBlockPathForms.spectrum]
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro x hx y hy hxy
      exact allDifferent hxy

/-- Conversely, an exact target spectrum forces bounds and indexed
injectivity; multiplicities cannot be hidden by taking support. -/
theorem threeBlock_bounds_injective_of_target
    (D : ThreeBlockPathForms)
    (target : D.spectrum = Finset.Icc 1 153) :
    (∀ i, 1 ≤ D.rank i ∧ D.rank i ≤ 153) ∧
      Function.Injective D.rank := by
  constructor
  · intro i
    have hi : D.rank i ∈ D.spectrum := by
      simp [ThreeBlockPathForms.spectrum]
    rw [target] at hi
    exact Finset.mem_Icc.mp hi
  · intro i j hij
    by_contra hne
    have hcardLt : D.spectrum.card < 153 := by
      rw [ThreeBlockPathForms.spectrum]
      have hlt : (Finset.univ.image D.rank).card < Finset.univ.card :=
          lt_of_le_of_ne Finset.card_image_le (by
            intro hcard
            have hinjOn := Finset.card_image_iff.mp hcard
            exact hne (hinjOn (by simp) (by simp) hij))
      simpa [threeBlockIndex_card] using hlt
    rw [target, Nat.card_Icc] at hcardLt
    norm_num at hcardLt

theorem threeBlock_target_iff_bounds_injective
    (D : ThreeBlockPathForms) :
    D.spectrum = Finset.Icc 1 153 ↔
      (∀ i, 1 ≤ D.rank i ∧ D.rank i ≤ 153) ∧
        Function.Injective D.rank := by
  constructor
  · exact threeBlock_bounds_injective_of_target D
  · rintro ⟨hBounds, hInjective⟩
    exact threeBlock_target_of_bounds_injective D hBounds hInjective

/-! ## Exact direct-sum difference prefilter -/

/-- The six exact rooted depth rows of the order-six fixture. -/
def seedDepth : Fin 6 → Fin 6 → ℤ :=
  ![![0, 1, 2, 5, 9, 13],
    ![1, 0, 3, 6, 10, 14],
    ![2, 3, 0, 7, 11, 15],
    ![9, 10, 11, 0, 12, 4],
    ![13, 14, 15, 12, 0, 8],
    ![5, 6, 7, 4, 8, 0]]

def CommonSeedPositiveDifference (d : ℤ) : Prop :=
  d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 7 ∨ d = 8

/-- A fixed witness pair for each fixture port and each of the seven common
positive differences.  The second coordinate indexes `1,2,3,4,5,7,8`. -/
def seedDifferenceWitness : Fin 6 → Fin 7 → Fin 6 × Fin 6 :=
  ![![(1, 0), (2, 0), (3, 2), (4, 3), (3, 0), (4, 2), (5, 3)],
    ![(0, 1), (2, 0), (2, 1), (4, 3), (3, 0), (4, 2), (5, 3)],
    ![(1, 0), (0, 2), (1, 2), (4, 3), (3, 0), (3, 2), (4, 1)],
    ![(1, 0), (2, 0), (4, 0), (5, 3), (0, 5), (2, 5), (4, 5)],
    ![(1, 0), (2, 0), (2, 3), (3, 5), (0, 5), (2, 5), (5, 4)],
    ![(1, 0), (2, 0), (4, 0), (3, 5), (0, 5), (2, 5), (4, 5)]]

/-- Values indexed in the same order as `seedDifferenceWitness`. -/
def commonSeedDifference : Fin 7 → ℤ :=
  ![1, 2, 3, 4, 5, 7, 8]

/-- The literal `6×7` witness table has the advertised differences. -/
theorem seedDifferenceWitness_spec (p : Fin 6) (k : Fin 7) :
    seedDepth p (seedDifferenceWitness p k).1 -
        seedDepth p (seedDifferenceWitness p k).2 = commonSeedDifference k := by
  fin_cases p <;> fin_cases k <;>
    simp [seedDepth, seedDifferenceWitness, commonSeedDifference]

/-- Every fixture port realizes each of the seven common positive depth
differences. -/
theorem seed_common_positive_difference
    (p : Fin 6) (d : ℤ) (hd : CommonSeedPositiveDifference d) :
    ∃ x y : Fin 6, seedDepth p x - seedDepth p y = d := by
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨(seedDifferenceWitness p 0).1,
      (seedDifferenceWitness p 0).2, seedDifferenceWitness_spec p 0⟩
  · exact ⟨(seedDifferenceWitness p 1).1,
      (seedDifferenceWitness p 1).2, seedDifferenceWitness_spec p 1⟩
  · exact ⟨(seedDifferenceWitness p 2).1,
      (seedDifferenceWitness p 2).2, seedDifferenceWitness_spec p 2⟩
  · exact ⟨(seedDifferenceWitness p 3).1,
      (seedDifferenceWitness p 3).2, seedDifferenceWitness_spec p 3⟩
  · exact ⟨(seedDifferenceWitness p 4).1,
      (seedDifferenceWitness p 4).2, seedDifferenceWitness_spec p 4⟩
  · exact ⟨(seedDifferenceWitness p 5).1,
      (seedDifferenceWitness p 5).2, seedDifferenceWitness_spec p 5⟩
  · exact ⟨(seedDifferenceWitness p 6).1,
      (seedDifferenceWitness p 6).2, seedDifferenceWitness_spec p 6⟩

/-- Safe port-independent bridge prefilter.  If the actual indexed cross sums
are injective, the other side cannot realize any scaled common fixture depth
difference.  This uses one jointly indexed rooted row `beta`, never unrelated
marginal depth sets. -/
theorem fixture_bridge_difference_prefilter
    {B : Type*} (p : Fin 6) (s : ℤ) (hs : 0 < s)
    (β : B → ℤ)
    (hInjective : Function.Injective
      (LeechTrees.crossSum (fun x => s * seedDepth p x) β))
    (d : ℤ) (hd : CommonSeedPositiveDifference d)
    (b b' : B) :
    β b' - β b ≠ s * d := by
  intro hbad
  obtain ⟨x, y, hxy⟩ := seed_common_positive_difference p d hd
  have hdiff :
      s * seedDepth p x - s * seedDepth p y = β b' - β b := by
    rw [hbad, ← hxy]
    ring
  have hcollapse :=
    (LeechTrees.crossSum_injective_iff
      (fun x => s * seedDepth p x) β).1 hInjective x y b b' hdiff
  have hdpos : 0 < d := by
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hscaled_ne : s * d ≠ 0 :=
    mul_ne_zero (ne_of_gt hs) (ne_of_gt hdpos)
  apply hscaled_ne
  rw [← hbad, hcollapse.2, sub_self]

/-! ## Three-by-three difference and AP obstruction -/

/-- Explicit multiplicity-preserving list of the nine sums. -/
def nineSums (a₁ a₂ b₁ b₂ : ℕ) : List ℕ :=
  [0, b₁, b₂, a₁, a₁ + b₁, a₁ + b₂,
    a₂, a₂ + b₁, a₂ + b₂]

/-- Finite normalized factorization of a `3×3` sum grid filling
`{0,...,8}` once.  Multiplying all four depths by a positive `h` gives the
general nine-term arithmetic progression statement. -/
theorem normalized_threeByThree_AP_factorization
    (a₁ a₂ b₁ b₂ : ℕ)
    (ha : 0 < a₁ ∧ a₁ < a₂)
    (hb : 0 < b₁ ∧ b₁ < b₂)
    (hmax : a₂ + b₂ ≤ 8)
    (hDistinct : (nineSums a₁ a₂ b₁ b₂).Nodup) :
    (a₁ = 1 ∧ a₂ = 2 ∧ b₁ = 3 ∧ b₂ = 6) ∨
      (a₁ = 3 ∧ a₂ = 6 ∧ b₁ = 1 ∧ b₂ = 2) := by
  rcases ha with ⟨ha₁pos, ha₁₂⟩
  rcases hb with ⟨hb₁pos, hb₁₂⟩
  simp [nineSums] at hDistinct
  omega

/-- Arbitrary-common-difference form of the normalized factorization. -/
theorem scaled_threeByThree_AP_factorization
    (h a₁ a₂ b₁ b₂ : ℕ) (hh : 0 < h)
    (ha : 0 < a₁ ∧ a₁ < a₂)
    (hb : 0 < b₁ ∧ b₁ < b₂)
    (hmax : a₂ + b₂ ≤ 8)
    (hDistinct : (nineSums a₁ a₂ b₁ b₂).Nodup) :
    (h * a₁ = h ∧ h * a₂ = 2 * h ∧
      h * b₁ = 3 * h ∧ h * b₂ = 6 * h) ∨
    (h * a₁ = 3 * h ∧ h * a₂ = 6 * h ∧
      h * b₁ = h ∧ h * b₂ = 2 * h) := by
  have hne : h ≠ 0 := ne_of_gt hh
  rcases normalized_threeByThree_AP_factorization a₁ a₂ b₁ b₂
      ha hb hmax hDistinct with hcase | hcase
  · left
    rcases hcase with ⟨rfl, rfl, rfl, rfl⟩
    constructor
    · apply mul_left_cancel₀ hne
      ring
    constructor
    · ring
    constructor <;> ring
  · right
    rcases hcase with ⟨rfl, rfl, rfl, rfl⟩
    constructor
    · apply mul_left_cancel₀ hne
      ring
    constructor
    · ring
    constructor <;> ring

inductive ThreePathPort
  | middle
  | leaf
  deriving DecidableEq

/-- Internal distances of a rooted three-vertex path whose two positive
root depths, in increasing order, are `d₁<d₂`. -/
def rootedThreePathInternal
    (port : ThreePathPort) (d₁ d₂ : ℕ) : List ℕ :=
  match port with
  | .middle => [d₁, d₂, d₁ + d₂]
  | .leaf => [d₁, d₂ - d₁, d₂]

/-- A single complete nine-term AP cross class is incompatible with globally
distinct pair distances of the two three-vertex gadget subtrees.  The AP
factorization forces equal edges at a leaf port, or a shared internal
distance at two middle ports. -/
theorem no_threeVertex_AP_cross_class
    (h a₁ a₂ b₁ b₂ : ℕ) (_hh : 0 < h)
    (ha₁ : a₁ = h) (ha₂ : a₂ = 2 * h)
    (hb₁ : b₁ = 3 * h) (hb₂ : b₂ = 6 * h)
    (portA portB : ThreePathPort)
    (hInternalDistinct :
      (rootedThreePathInternal portA a₁ a₂ ++
        rootedThreePathInternal portB b₁ b₂).Nodup) :
    False := by
  subst a₁
  subst a₂
  subst b₁
  subst b₂
  cases portA <;> cases portB <;>
    simp [rootedThreePathInternal] at hInternalDistinct <;> omega

/-- Symmetric endpoint combining the normalized AP factorization with the
three-vertex path obstruction. -/
theorem no_normalized_threeVertex_AP_cross_class
    (a₁ a₂ b₁ b₂ : ℕ)
    (ha : 0 < a₁ ∧ a₁ < a₂)
    (hb : 0 < b₁ ∧ b₁ < b₂)
    (hmax : a₂ + b₂ ≤ 8)
    (hCrossDistinct : (nineSums a₁ a₂ b₁ b₂).Nodup)
    (portA portB : ThreePathPort)
    (hInternalDistinct :
      (rootedThreePathInternal portA a₁ a₂ ++
        rootedThreePathInternal portB b₁ b₂).Nodup) :
    False := by
  rcases normalized_threeByThree_AP_factorization a₁ a₂ b₁ b₂
      ha hb hmax hCrossDistinct with h | h
  · rcases h with ⟨rfl, rfl, rfl, rfl⟩
    exact no_threeVertex_AP_cross_class 1 1 2 3 6 (by norm_num)
      rfl rfl rfl rfl portA portB hInternalDistinct
  · rcases h with ⟨rfl, rfl, rfl, rfl⟩
    exact no_threeVertex_AP_cross_class 1 1 2 3 6 (by norm_num)
      rfl rfl rfl rfl portB portA
        (List.nodup_append_comm.mp hInternalDistinct)

end LeechTrees.AdditionalBlockLifts
