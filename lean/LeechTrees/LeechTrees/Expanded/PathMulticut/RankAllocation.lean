import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Data.Real.Basic

/-!
# Exact finite rank-allocation bounds

This file isolates the rearrangement argument used by the hop and multicut
constraints.  The score vector may contain negative entries and ties.  The
equality statements are the exact `Monovary` / `Antivary` conditions, so they
retain the paper's "arbitrary permutations inside score ties" qualification.
-/

open scoped BigOperators

namespace LeechTrees.PathMulticut

noncomputable section

/-- Dot product of two vectors indexed by `Fin L`. -/
def rankDot (score rank : Fin L → ℝ) : ℝ :=
  ∑ i, score i * rank i

/-- The increasing/increasing and increasing/decreasing extremal dot products. -/
def upperRankDot (score rank : Fin L → ℝ) : ℝ := rankDot score rank

def lowerRankDot (score rank : Fin L → ℝ) : ℝ :=
  rankDot score (rank ∘ Fin.revPerm)

/-- Sharp two-sided rearrangement for an arbitrary actual permutation.

The right equality says precisely that the ranks assigned by `π` are
nondecreasing in score.  The left equality says precisely that they are
nonincreasing in score.  These formulations remain correct when scores tie.
-/
theorem sharp_rank_rearrangement {L : ℕ}
    (score rank : Fin L → ℝ) (π : Equiv.Perm (Fin L))
    (hscore : Monotone score) (hrank : Monotone rank) :
    lowerRankDot score rank ≤ rankDot score (rank ∘ π) ∧
      rankDot score (rank ∘ π) ≤ upperRankDot score rank ∧
      (rankDot score (rank ∘ π) = upperRankDot score rank ↔
        Monovary score (rank ∘ π)) ∧
      (rankDot score (rank ∘ π) = lowerRankDot score rank ↔
        Antivary score (rank ∘ π)) := by
  let reverseThenActual : Equiv.Perm (Fin L) := π.trans Fin.revPerm
  have hrev : Antitone (rank ∘ Fin.revPerm) := by
    intro i j hij
    exact hrank (Fin.rev_le_rev.mpr hij)
  have hanti : Antivary score (rank ∘ Fin.revPerm) :=
    hscore.antivary hrev
  have hmono : Monovary score rank := hscore.monovary hrank
  have hlower :=
    hanti.sum_mul_le_sum_mul_comp_perm (σ := reverseThenActual)
  have hupper := hmono.sum_mul_comp_perm_le_sum_mul (σ := π)
  have heqUpper := hmono.sum_mul_comp_perm_eq_sum_mul_iff (σ := π)
  have heqLower :=
    hanti.sum_mul_eq_sum_mul_comp_perm_iff (σ := reverseThenActual)
  have hsimplify :
      (rank ∘ Fin.revPerm) ∘ reverseThenActual = rank ∘ π := by
    funext i
    simp [reverseThenActual, Function.comp_def, Fin.revPerm]
  change
    rankDot score (rank ∘ Fin.revPerm) ≤ rankDot score (rank ∘ π) ∧
      rankDot score (rank ∘ π) ≤ rankDot score rank ∧
      (rankDot score (rank ∘ π) = rankDot score rank ↔
        Monovary score (rank ∘ π)) ∧
      (rankDot score (rank ∘ π) = rankDot score (rank ∘ Fin.revPerm) ↔
        Antivary score (rank ∘ π))
  constructor
  · change
      (∑ i, score i * (rank ∘ Fin.revPerm) i) ≤
        ∑ i, score i * (rank ∘ π) i
    calc
      _ ≤ ∑ i, score i *
          ((rank ∘ Fin.revPerm) ∘ reverseThenActual) i := hlower
      _ = _ := by rw [hsimplify]
  constructor
  · simpa [rankDot] using hupper
  constructor
  · simpa [rankDot] using heqUpper
  · have heqLower' :
        rankDot score ((rank ∘ Fin.revPerm) ∘ reverseThenActual) =
            rankDot score (rank ∘ Fin.revPerm) ↔
          Antivary score ((rank ∘ Fin.revPerm) ∘ reverseThenActual) := by
      simpa [rankDot] using heqLower
    rw [hsimplify] at heqLower'
    exact heqLower'

/-- Adding a fixed physical-edge contribution preserves both bounds and both
equality characterizations.  This is the literal form used by the punctured
parity-channel and hop-rank statements. -/
theorem sharp_rank_rearrangement_with_fixed {L : ℕ}
    (fixed : ℝ) (score rank : Fin L → ℝ) (π : Equiv.Perm (Fin L))
    (hscore : Monotone score) (hrank : Monotone rank) :
    fixed + lowerRankDot score rank ≤
        fixed + rankDot score (rank ∘ π) ∧
      fixed + rankDot score (rank ∘ π) ≤
        fixed + upperRankDot score rank ∧
      (fixed + rankDot score (rank ∘ π) =
          fixed + upperRankDot score rank ↔
        Monovary score (rank ∘ π)) ∧
      (fixed + rankDot score (rank ∘ π) =
          fixed + lowerRankDot score rank ↔
        Antivary score (rank ∘ π)) := by
  obtain ⟨hl, hu, heu, hel⟩ :=
    sharp_rank_rearrangement score rank π hscore hrank
  exact ⟨add_le_add_left hl fixed, add_le_add_left hu fixed,
    add_left_cancel_iff.trans heu, add_left_cancel_iff.trans hel⟩

end

end LeechTrees.PathMulticut
