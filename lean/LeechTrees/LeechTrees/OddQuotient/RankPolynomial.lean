import Mathlib

/-!
# Multiplicity-preserving rank polynomials

`rankPoly rank` enumerates a finite *indexed* type.  An index contributes one
monomial, even when several different indices have the same rank.  Thus the
coefficient at `k` is the cardinality of the fibre over `k`; no `Finset.image`
or support-set replacement occurs anywhere in this file.
-/

open scoped BigOperators Polynomial

namespace LeechTrees.OddQuotient

/-- The ordinary generating polynomial of a rank on a finite indexed type.
Every index contributes once, so equal ranks retain their multiplicity. -/
noncomputable def rankPoly {ι : Type*} [Fintype ι]
    (rank : ι → ℕ) : ℕ[X] :=
  ∑ i : ι, Polynomial.monomial (rank i) 1

/-- The coefficient of `rankPoly rank` is exactly the number of indices in
the corresponding rank fibre.  This is the basic multiplicity-safety
statement used by every quotient polynomial below. -/
theorem rankPoly_coeff {ι : Type*} [Fintype ι]
    (rank : ι → ℕ) (k : ℕ) :
    (rankPoly rank).coeff k = Fintype.card {i : ι // rank i = k} := by
  classical
  rw [rankPoly]
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Fintype.card_subtype]
  simp [eq_comm]

/-- Reindexing the underlying finite type preserves the polynomial when it
preserves every indexed rank. -/
theorem rankPoly_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (rankι : ι → ℕ) (rankκ : κ → ℕ)
    (hrank : ∀ i, rankκ (e i) = rankι i) :
    rankPoly rankι = rankPoly rankκ := by
  classical
  unfold rankPoly
  apply Fintype.sum_equiv e
  intro i
  rw [hrank i]

/-- A disjoint indexed union becomes addition of rank polynomials. -/
theorem rankPoly_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (rankι : ι → ℕ) (rankκ : κ → ℕ) :
    rankPoly (Sum.elim rankι rankκ) =
      rankPoly rankι + rankPoly rankκ := by
  classical
  simp [rankPoly, Fintype.sum_sum_type]

/-- A dependent indexed union becomes the sum of the fibre polynomials. -/
theorem rankPoly_sigma {ι : Type*} {κ : ι → Type*}
    [Fintype ι] [∀ i, Fintype (κ i)]
    (rank : (Σ i, κ i) → ℕ) :
    rankPoly rank = ∑ i : ι, rankPoly (fun x : κ i => rank ⟨i, x⟩) := by
  classical
  simp [rankPoly, Fintype.sum_sigma]

/-- Adding a constant shift to all ranks multiplies by its monomial. -/
theorem rankPoly_add_const {ι : Type*} [Fintype ι]
    (shift : ℕ) (rank : ι → ℕ) :
    rankPoly (fun i => shift + rank i) =
      Polynomial.monomial shift 1 * rankPoly rank := by
  classical
  unfold rankPoly
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Polynomial.monomial_mul_monomial]

/-- The indexed Cartesian-product convolution.  Equal sums are deliberately
not deduplicated: polynomial multiplication records their full number of
preimages. -/
theorem rankPoly_add_product {ι κ : Type*} [Fintype ι] [Fintype κ]
    (leftRank : ι → ℕ) (rightRank : κ → ℕ) :
    rankPoly (fun z : ι × κ => leftRank z.1 + rightRank z.2) =
      rankPoly leftRank * rankPoly rightRank := by
  classical
  unfold rankPoly
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp [Polynomial.monomial_mul_monomial]

/-- Shifted Cartesian-product convolution, the algebraic form used for one
odd-quotient component-pair block. -/
theorem rankPoly_shift_add_product {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (shift : ℕ) (leftRank : ι → ℕ) (rightRank : κ → ℕ) :
    rankPoly
        (fun z : ι × κ => shift + leftRank z.1 + rightRank z.2) =
      Polynomial.monomial shift 1 *
        rankPoly leftRank * rankPoly rightRank := by
  calc
    rankPoly
        (fun z : ι × κ => shift + leftRank z.1 + rightRank z.2) =
        rankPoly
          (fun z : ι × κ => shift + (leftRank z.1 + rightRank z.2)) := by
      congr 1
      funext z
      omega
    _ = Polynomial.monomial shift 1 *
          rankPoly (fun z : ι × κ => leftRank z.1 + rightRank z.2) :=
      rankPoly_add_const shift _
    _ = Polynomial.monomial shift 1 *
          (rankPoly leftRank * rankPoly rightRank) := by
      rw [rankPoly_add_product]
    _ = Polynomial.monomial shift 1 *
          rankPoly leftRank * rankPoly rightRank := by
      rw [mul_assoc]

/-- Coefficientwise form of the shifted product.  It exposes the exact
endpoint-pair count behind each coefficient, so a later proof cannot silently
replace the indexed Cartesian product by a support set. -/
theorem coeff_shifted_rankPoly_product {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (shift k : ℕ) (leftRank : ι → ℕ) (rightRank : κ → ℕ) :
    (Polynomial.monomial shift 1 *
        rankPoly leftRank * rankPoly rightRank).coeff k =
      Fintype.card
        {z : ι × κ // shift + leftRank z.1 + rightRank z.2 = k} := by
  rw [← rankPoly_shift_add_product]
  exact rankPoly_coeff _ _

end LeechTrees.OddQuotient
