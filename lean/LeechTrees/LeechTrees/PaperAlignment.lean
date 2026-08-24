import LeechTrees.Foundations
import LeechTrees.ParityTail
import LeechTrees.OddEdgesT12Adapter

/-!
# Paper-facing alignment wrappers

This source-only staging module exposes exact already-proved statements under
paper-facing names and adds the immediate order-18 corollary of T12. It does
not alter the legacy thirteen-row theorem denominator and carries no build or
validation claim until included in a later frozen release.
-/

open scoped BigOperators

namespace LeechTrees.PaperAlignment

open LeechTrees.Foundation
open LeechTrees.ParityTail
open LeechTrees.OddEdges.GraphAdapter

/-- Exact paper-facing form of the general root-parity equation used in T3. -/
theorem T3_actual_root_parity_equation {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) (r : Fin n) :
    T.parityClassSize r * (n - T.parityClassSize r) =
      (targetN n + 1) / 2 := by
  exact LeechTrees.Foundation.t3_parity_equation hL r

/-- Exact paper-facing alias for the complete order-18 target count and
degree-one/two/three moment table used in T8. -/
theorem T8_order18_target_counts_and_moments :
    order18EvenTargets.card = 76 ∧
    order18OddTargets.card = 77 ∧
    (∑ t ∈ order18EvenTargets, t) = 5852 ∧
    (∑ t ∈ order18OddTargets, t) = 5929 ∧
    (∑ t ∈ order18EvenTargets, t ^ 2) = 596904 ∧
    (∑ t ∈ order18OddTargets, t ^ 2) = 608685 ∧
    (∑ t ∈ order18EvenTargets, t ^ 3) = 68491808 ∧
    (∑ t ∈ order18OddTargets, t ^ 3) = 70300153 := by
  exact LeechTrees.ParityTail.T8_order18_target_moments

/-- At order 18, the graph-level T12 parity theorem rules out exactly two
odd physical edges because the exact target interval contains 77 odd ranks. -/
theorem T12_order18_no_exactly_two_odd_physical_edges
    (T : PosIntTree 18) (hL : IsLeech T) :
    ¬ ExactlyTwoOddPhysicalEdges T := by
  intro hTwo
  have heven : Even (oddTargetCount 18) :=
    LeechTrees.OddEdges.T12Adapter.t12_two_odd_physical_edges
      T hL (by decide) hTwo
  have hcount : oddTargetCount 18 = 77 := by
    rw [oddTargetCount_eq]
    decide
  have hnot : ¬ Even (oddTargetCount 18) := by
    rw [hcount]
    decide
  exact hnot heven

end LeechTrees.PaperAlignment
