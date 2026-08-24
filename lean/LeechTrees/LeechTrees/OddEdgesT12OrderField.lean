import LeechTrees.OddEdgesGraphAdapter

open scoped BigOperators

namespace LeechTrees.OddEdges.T12Adapter.OrderField

open LeechTrees.Foundation
open LeechTrees.OddEdges.GraphAdapter

theorem coupled_order_case
    {n : ℕ} (T : PosIntTree n) (hL : IsLeech T) (r : Fin n) :
    ∃ s : ℤ,
      (((n : ℤ) = s ^ 2 ∧ oddTargetCount n = evenTargetCount n) ∨
       ((n : ℤ) = s ^ 2 + 2 ∧
          oddTargetCount n = evenTargetCount n + 1)) := by
  let a := T.parityClassSize r
  let s : ℤ := 2 * (a : ℤ) - (n : ℤ)
  have ha : a ≤ n := T.parityClassSize_le_order r
  have hn : 1 ≤ n := by
    have hr := r.isLt
    omega
  have hpar : a * (n - a) = oddTargetCount n := by
    calc
      a * (n - a) = (targetN n + 1) / 2 := t3_parity_equation hL r
      _ = oddTargetCount n := (oddTargetCount_eq (n := n)).symm
  have hsum := oddTargetCount_add_evenTargetCount (n := n)
  have htwice := two_mul_targetN n
  refine ⟨s, ?_⟩
  rcases oddTargetCount_evenTargetCount_case (n := n) with heq | hextra
  · left
    refine ⟨?_, heq⟩
    have hclear : 4 * (a * (n - a)) = n * (n - 1) := by omega
    have hclearInt :
        4 * ((a : ℤ) * ((n : ℤ) - a)) =
          (n : ℤ) * ((n : ℤ) - 1) := by
      exact_mod_cast hclear
    change (n : ℤ) = (2 * (a : ℤ) - (n : ℤ)) ^ 2
    nlinarith
  · right
    refine ⟨?_, hextra⟩
    have hclear : 4 * (a * (n - a)) = n * (n - 1) + 2 := by omega
    have hclearInt :
        4 * ((a : ℤ) * ((n : ℤ) - a)) =
          (n : ℤ) * ((n : ℤ) - 1) + 2 := by
      exact_mod_cast hclear
    change (n : ℤ) = (2 * (a : ℤ) - (n : ℤ)) ^ 2 + 2
    nlinarith

end LeechTrees.OddEdges.T12Adapter.OrderField
