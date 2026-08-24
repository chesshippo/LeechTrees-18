import Mathlib

/-!
# LeechTrees: combinatorial core

This file isolates algebraic and finite-combinatorial lemmas used in the
Leech-tree work.  It intentionally does not claim existence or nonexistence
of an order-18 Leech tree.  The graph-theoretic step that instantiates the
abstract incidence data below is kept outside this minimal layer.

The source contains no `axiom`, `sorry`, or `admit` declarations.
-/

open scoped BigOperators

namespace LeechTrees

/-! ## The distances 1 and 2 must be physical -/

/-- A nonempty positive integral path of total weight one has one edge. -/
theorem positive_path_sum_one_is_single_edge
    {weights : List ℕ}
    (positive : ∀ w ∈ weights, 0 < w)
    (total : weights.sum = 1) :
    weights.length = 1 := by
  cases weights with
  | nil => simp at total
  | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          have hx : 0 < x := positive x (by simp)
          have hy : 0 < y := positive y (by simp)
          simp only [List.sum_cons] at total
          omega

/-- If all physical edge weights are distinct, a positive integral path of
total weight two also has one edge. -/
theorem positive_nodup_path_sum_two_is_single_edge
    {weights : List ℕ}
    (positive : ∀ w ∈ weights, 0 < w)
    (nodup : weights.Nodup)
    (total : weights.sum = 2) :
    weights.length = 1 := by
  cases weights with
  | nil => simp at total
  | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          have hx : 0 < x := positive x (by simp)
          have hy : 0 < y := positive y (by simp)
          have hxy : x = 1 ∧ y = 1 := by
            simp only [List.sum_cons] at total
            omega
          have hnot : x ∉ y :: ys := (List.nodup_cons.mp nodup).1
          have hin : x ∈ y :: ys := by simp [hxy.1, hxy.2]
          exact (hnot hin).elim

/-! ## Taylor parity arithmetic -/

/-- Discriminant identity when the number of odd target ranks is half of an
even total number of ranks. -/
theorem parity_discriminant_even_case
    (n a : ℤ)
    (h : 4 * a * (n - a) = n * (n - 1)) :
    (n - 2 * a) ^ 2 = n := by
  nlinarith

/-- Discriminant identity when the number of odd target ranks is the ceiling
of half of an odd total number of ranks. -/
theorem parity_discriminant_odd_case
    (n a : ℤ)
    (h : 4 * a * (n - a) = n * (n - 1) + 2) :
    (n - 2 * a) ^ 2 = n - 2 := by
  nlinarith

/-- Arithmetic core of Taylor's necessary order condition.  The disjunction
in the hypothesis is exactly the parity equation after clearing denominators,
according to the parity of `choose(n,2)`. -/
theorem taylor_order_condition_of_parity_equation
    (n a : ℤ)
    (h : 4 * a * (n - a) = n * (n - 1) ∨
         4 * a * (n - a) = n * (n - 1) + 2) :
    ∃ t : ℤ, n = t ^ 2 ∨ n = t ^ 2 + 2 := by
  rcases h with heven | hodd
  · refine ⟨n - 2 * a, Or.inl ?_⟩
    exact (parity_discriminant_even_case n a heven).symm
  · refine ⟨n - 2 * a, Or.inr ?_⟩
    have hd := parity_discriminant_odd_case n a hodd
    nlinarith

/-- The order-18 parity equation has precisely the two class sizes 7 and 11. -/
theorem order18_parity_class_sizes
    (a : ℤ)
    (h : a * (18 - a) = 77) :
    a = 7 ∨ a = 11 := by
  have hfactor : (a - 7) * (a - 11) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with h7 | h11
  · left
    nlinarith
  · right
    nlinarith

/-! ## Abstract path-incidence double counting -/

section Incidence

variable {Pair Edge : Type*} [Fintype Pair] [Fintype Edge]

/-- Sum of edge weights in one abstract path row.  In a tree application,
`incidence p e` is zero or one according as pair-path `p` uses edge `e`. -/
def weightedRow
    (incidence : Pair → Edge → ℕ)
    (weight : Edge → ℕ)
    (p : Pair) : ℕ :=
  ∑ e, incidence p e * weight e

/-- Number of row occurrences of one edge, allowing the same general
nonnegative-incidence interface as `weightedRow`. -/
def columnCount
    (incidence : Pair → Edge → ℕ)
    (e : Edge) : ℕ :=
  ∑ p, incidence p e

/-- The finite sum interchange behind the cut checksum. -/
theorem sum_weightedRows_eq_sum_columnCounts
    (incidence : Pair → Edge → ℕ)
    (weight : Edge → ℕ) :
    (∑ p, weightedRow incidence weight p) =
      ∑ e, columnCount incidence e * weight e := by
  classical
  calc
    (∑ p, weightedRow incidence weight p) =
        ∑ p, ∑ e, incidence p e * weight e := rfl
    _ = ∑ e, ∑ p, incidence p e * weight e := by
      rw [Finset.sum_comm]
    _ = ∑ e, columnCount incidence e * weight e := by
      apply Finset.sum_congr rfl
      intro e _
      unfold columnCount
      rw [Finset.sum_mul]

/-- Abstract cut-checksum theorem.  For a tree, instantiate `Pair` by
unordered vertex pairs and `cut e` by `s_e (n-s_e)`. -/
theorem cutChecksum
    (incidence : Pair → Edge → ℕ)
    (weight cut : Edge → ℕ)
    (target : Pair → ℕ)
    (row_spec : ∀ p, weightedRow incidence weight p = target p)
    (column_spec : ∀ e, columnCount incidence e = cut e) :
    (∑ e, cut e * weight e) = ∑ p, target p := by
  classical
  calc
    (∑ e, cut e * weight e) =
        ∑ e, columnCount incidence e * weight e := by
      apply Finset.sum_congr rfl
      intro e _
      rw [column_spec e]
    _ = ∑ p, weightedRow incidence weight p :=
      (sum_weightedRows_eq_sum_columnCounts incidence weight).symm
    _ = ∑ p, target p := by
      apply Finset.sum_congr rfl
      intro p _
      exact row_spec p

end Incidence

/-! ## Signed cut splitting -/

/-- Twice the same-sign cross-pair count is ordinary cross pairs plus the
product of the two signed side imbalances. -/
theorem twice_even_cross_count
    (aPlus aMinus bPlus bMinus : ℤ) :
    2 * (aPlus * bPlus + aMinus * bMinus) =
      (aPlus + aMinus) * (bPlus + bMinus) +
      (aPlus - aMinus) * (bPlus - bMinus) := by
  ring

/-- Twice the opposite-sign cross-pair count is ordinary cross pairs minus
the product of the two signed side imbalances. -/
theorem twice_odd_cross_count
    (aPlus aMinus bPlus bMinus : ℤ) :
    2 * (aPlus * bMinus + aMinus * bPlus) =
      (aPlus + aMinus) * (bPlus + bMinus) -
      (aPlus - aMinus) * (bPlus - bMinus) := by
  ring

/-! ## Every-edge direct sums -/

section DirectSum

variable {A B : Type*}

/-- Indexed rooted direct sum across a physical edge. -/
def crossSum (α : A → ℤ) (β : B → ℤ) (x : A × B) : ℤ :=
  α x.1 + β x.2

/-- A cross-sum collision is exactly an equality of oppositely oriented
root-depth differences. -/
theorem crossSum_eq_iff_difference_eq
    (α : A → ℤ) (β : B → ℤ)
    (a a' : A) (b b' : B) :
    crossSum α β (a, b) = crossSum α β (a', b') ↔
      α a - α a' = β b' - β b := by
  simp only [crossSum]
  constructor <;> intro h <;> linarith

/-- Exact indexed difference criterion for uniqueness of all cross sums. -/
theorem crossSum_injective_iff
    (α : A → ℤ) (β : B → ℤ) :
    Function.Injective (crossSum α β) ↔
      ∀ a a' b b',
        α a - α a' = β b' - β b → a = a' ∧ b = b' := by
  constructor
  · intro hinjective a a' b b' hdifference
    have hsum : crossSum α β (a, b) = crossSum α β (a', b') :=
      (crossSum_eq_iff_difference_eq α β a a' b b').2 hdifference
    have hpairs : (a, b) = (a', b') := hinjective hsum
    exact ⟨congrArg Prod.fst hpairs, congrArg Prod.snd hpairs⟩
  · intro hdifference x y hsum
    rcases x with ⟨a, b⟩
    rcases y with ⟨a', b'⟩
    have hd : α a - α a' = β b' - β b :=
      (crossSum_eq_iff_difference_eq α β a a' b b').1 hsum
    rcases hdifference a a' b b' hd with ⟨ha, hb⟩
    exact Prod.ext ha hb

end DirectSum

/-! ## Block moments and saturated finite tails -/

section BlockMoments

variable {I : Type*} [Fintype I]

/-- First moment after shifting every row-coupled residual by an edge weight. -/
theorem shifted_first_moment
    (w : ℤ) (residual : I → ℤ) :
    (∑ i, (w + residual i)) =
      (Fintype.card I : ℤ) * w + ∑ i, residual i := by
  classical
  simp [Finset.sum_add_distrib]

/-- Second shifted block-moment expansion. -/
theorem shifted_second_moment
    (w : ℤ) (residual : I → ℤ) :
    (∑ i, (w + residual i) ^ 2) =
      (Fintype.card I : ℤ) * w ^ 2 +
      2 * w * (∑ i, residual i) +
      ∑ i, (residual i) ^ 2 := by
  classical
  calc
    (∑ i, (w + residual i) ^ 2) =
        ∑ i, (w ^ 2 + 2 * w * residual i + (residual i) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (Fintype.card I : ℤ) * w ^ 2 +
          2 * w * (∑ i, residual i) +
          ∑ i, (residual i) ^ 2 := by
      simp only [Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      rw [Finset.mul_sum]

/-- Third shifted block-moment expansion. -/
theorem shifted_third_moment
    (w : ℤ) (residual : I → ℤ) :
    (∑ i, (w + residual i) ^ 3) =
      (Fintype.card I : ℤ) * w ^ 3 +
      3 * w ^ 2 * (∑ i, residual i) +
      3 * w * (∑ i, (residual i) ^ 2) +
      ∑ i, (residual i) ^ 3 := by
  classical
  calc
    (∑ i, (w + residual i) ^ 3) =
        ∑ i, (w ^ 3 + 3 * w ^ 2 * residual i +
          3 * w * (residual i) ^ 2 + (residual i) ^ 3) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (Fintype.card I : ℤ) * w ^ 3 +
          3 * w ^ 2 * (∑ i, residual i) +
          3 * w * (∑ i, (residual i) ^ 2) +
          ∑ i, (residual i) ^ 3 := by
      simp only [Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      rw [Finset.mul_sum, Finset.mul_sum]

end BlockMoments

/-- A finite block contained in a target tail and having the same cardinality
is the entire tail.  This is the set-theoretic core of the saturated-tail
corollary. -/
theorem saturatedFiniteBlock
    {X : Type*} [DecidableEq X]
    {block tail : Finset X}
    (contained : block ⊆ tail)
    (same_card : block.card = tail.card) :
    block = tail := by
  apply Finset.eq_of_subset_of_card_le contained
  omega

/-! ## Pigeonhole capacities used by the second odd weight -/

/-- An injective encoding of `R` into an indexed rectangle gives the product
capacity.  In the Leech application, `R` is the set of low odd ranks and the
rectangle consists of endpoint choices across the weight-one edge. -/
theorem card_le_product_of_injective
    {R A B : Type*} [Fintype R] [Fintype A] [Fintype B]
    (encode : R → A × B)
    (injective : Function.Injective encode) :
    Fintype.card R ≤ Fintype.card A * Fintype.card B := by
  simpa only [Fintype.card_prod] using
    Fintype.card_le_of_injective encode injective

/-- Arithmetic conclusion `q₂ ≤ 2 min(I,xy)+1` from the two low-rank
capacities, with `q₂=2t+1`. -/
theorem secondOddWeight_from_two_capacities
    (q₂ t internalCapacity bridgeCapacity : ℕ)
    (definition_of_t : q₂ = 2 * t + 1)
    (internal_bound : t ≤ internalCapacity)
    (bridge_bound : t ≤ bridgeCapacity) :
    q₂ ≤ 2 * min internalCapacity bridgeCapacity + 1 := by
  have hmin : t ≤ min internalCapacity bridgeCapacity :=
    (Nat.le_min).2 ⟨internal_bound, bridge_bound⟩
  omega

/-! ## Small arithmetic certificates for the order-18 paper proofs -/

/-- Final arithmetic step of the 42-short-sums hop obstruction. -/
theorem hop15_arithmetic_contradiction
    (length shortSum boundaryPenalty : ℤ)
    (fortyTwoDistinct : 903 ≤ shortSum)
    (multiplicityIdentity : shortSum = 6 * length - boundaryPenalty)
    (boundaryMinimum : 16 ≤ boundaryPenalty)
    (order18DiameterBound : length ≤ 153) :
    False := by
  omega

/-- Final arithmetic step of the analytic `Q ≥ 19` proof, after the
rearrangement argument supplies the stated cap under `Q ≤ 18`. -/
theorem order18_largest_edge_at_least_19_from_cap
    (largestWeight checksum : ℕ)
    (requiredChecksum : checksum = 11781)
    (cap_if_small : largestWeight ≤ 18 → checksum ≤ 11372) :
    19 ≤ largestWeight := by
  by_contra h
  have hsmall : largestWeight ≤ 18 := by omega
  have hcap := cap_if_small hsmall
  omega

end LeechTrees

