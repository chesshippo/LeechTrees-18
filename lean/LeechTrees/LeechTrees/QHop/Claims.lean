import LeechTrees.QHop.CoreCountAdapter

namespace LeechTrees.QHop

open LeechTrees.Foundation

/-- Paper claim T6: in every order-18 Leech tree, the maximum over the
actual physical edge-weight function is at least nineteen. -/
theorem order18_largestPhysicalEdge_ge_19
    (T : PosIntTree 18) (hL : IsLeech T) :
    19 ≤ largestPhysicalEdge T := by
  have hcore : ∀ (k : ℕ), 1 ≤ k → k ≤ 9 →
      (Finset.univ.filter
        (fun e : T.Edge ↦ k ≤ order18SmallerSide T e)).card + 2 * k ≤ 19 := by
    intro k hk hk9
    simpa [order18SmallerSide] using order18_core_count_add T k hk hk9
  let D := order18CutDataOfCoreCount T hL hcore
  have hD := D.largestPhysicalWeight_ge_19
  change 19 ≤ Finset.univ.sup T.weight
  change 19 ≤ Finset.univ.sup T.weight at hD
  exact hD

end LeechTrees.QHop
