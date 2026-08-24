import LeechTrees.Foundations

/-!
# Three-port named-median guard

This module formalizes G010.  The positive-arm theorem records the exact
arithmetic obstruction for the six distances determined by a genuine named
tripod.  The graph-level endpoint uses actual indexed vertex pairs in a
`PosIntTree`; `IsLeech` supplies distance injectivity, while the certificate
supplies only the named-tripod construction equations and distinctness of the
underlying pairs.

The final section treats the audited zero-arm boundary separately.  In that
case the six-entry tripod list necessarily repeats two values, whereas the
three genuine pair distances are distinct exactly when the two positive arms
differ.
-/

namespace LeechTrees.ThreePortMedian

open LeechTrees.Foundation

noncomputable section

/-- The six median/port and port/port distances of a tripod with arm lengths
`A`, `B`, and `C`. -/
def tripodDistanceList (A B C : ℕ) : List ℕ :=
  [A, B, C, A + B, A + C, B + C]

/-- The exact positive-arm characterization: the six tripod distances are
pairwise distinct precisely when the three arms are pairwise distinct and no
arm is the sum of the other two. -/
theorem positive_tripodDistanceList_nodup_iff
    {A B C : ℕ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) :
    (tripodDistanceList A B C).Nodup ↔
      A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
      A ≠ B + C ∧ B ≠ A + C ∧ C ≠ A + B := by
  simp only [tripodDistanceList, List.nodup_cons, List.mem_cons,
    not_or, List.not_mem_nil, List.nodup_nil]
  constructor
  · aesop
  · rintro ⟨hAB, hAC, hBC, hABC, hBAC, hCAB⟩
    simp [hAB, hAC, hBC, hABC, hBAC, hCAB,
      hA.ne', hB.ne', hC.ne']
    intro h
    apply hAC
    omega

/-- Actual indexed-pair certificate for a named positive tripod.  The six
pairs are construction data, not assumed distance values: the displayed
distance equations say exactly that one has three arms and the three
corresponding through-median port distances. -/
structure ActualPositiveTripod {n : ℕ} (T : PosIntTree n) where
  arm0Pair : VertexPair n
  arm1Pair : VertexPair n
  arm2Pair : VertexPair n
  port01Pair : VertexPair n
  port02Pair : VertexPair n
  port12Pair : VertexPair n
  pairNodup :
    [arm0Pair, arm1Pair, arm2Pair, port01Pair, port02Pair, port12Pair].Nodup
  arm0 : ℕ
  arm1 : ℕ
  arm2 : ℕ
  arm0_pos : 0 < arm0
  arm1_pos : 0 < arm1
  arm2_pos : 0 < arm2
  dist_arm0 : T.pairDist arm0Pair = arm0
  dist_arm1 : T.pairDist arm1Pair = arm1
  dist_arm2 : T.pairDist arm2Pair = arm2
  dist_port01 : T.pairDist port01Pair = arm0 + arm1
  dist_port02 : T.pairDist port02Pair = arm0 + arm2
  dist_port12 : T.pairDist port12Pair = arm1 + arm2

namespace ActualPositiveTripod

variable {n : ℕ} {T : PosIntTree n}

/-- The actual six graph distances carried by a named tripod certificate. -/
def actualDistanceList (D : ActualPositiveTripod T) : List ℕ :=
  [ T.pairDist D.arm0Pair,
    T.pairDist D.arm1Pair,
    T.pairDist D.arm2Pair,
    T.pairDist D.port01Pair,
    T.pairDist D.port02Pair,
    T.pairDist D.port12Pair ]

private theorem pair_ne_of_nodup
    {a b : VertexPair n} {tail : List (VertexPair n)}
    (h : (a :: b :: tail).Nodup) : a ≠ b := by
  intro hab
  exact (List.nodup_cons.mp h).1 (by simp [hab])

/-- `IsLeech` turns distinct actual unordered pairs into the exact arithmetic
guard on the three arms. -/
theorem arm_guard (D : ActualPositiveTripod T) (hL : IsLeech T) :
    D.arm0 ≠ D.arm1 ∧ D.arm0 ≠ D.arm2 ∧ D.arm1 ≠ D.arm2 ∧
    D.arm0 ≠ D.arm1 + D.arm2 ∧
    D.arm1 ≠ D.arm0 + D.arm2 ∧
    D.arm2 ≠ D.arm0 + D.arm1 := by
  have h01 : D.arm0Pair ≠ D.arm1Pair :=
    pair_ne_of_nodup D.pairNodup
  have h02 : D.arm0Pair ≠ D.arm2Pair := by
    intro h
    exact (List.nodup_cons.mp D.pairNodup).1 (by simp [h])
  have h12 : D.arm1Pair ≠ D.arm2Pair := by
    exact pair_ne_of_nodup (List.nodup_cons.mp D.pairNodup).2
  have h0s : D.arm0Pair ≠ D.port12Pair := by
    intro h
    exact (List.nodup_cons.mp D.pairNodup).1 (by simp [h])
  have h1s : D.arm1Pair ≠ D.port02Pair := by
    intro h
    exact (List.nodup_cons.mp (List.nodup_cons.mp D.pairNodup).2).1
      (by simp [h])
  have h2s : D.arm2Pair ≠ D.port01Pair := by
    intro h
    exact
      (List.nodup_cons.mp
        (List.nodup_cons.mp
          (List.nodup_cons.mp D.pairNodup).2).2).1
        (by simp [h])
  constructor
  · intro h
    exact h01 (hL.pairDist_injective (D.dist_arm0.trans (h.trans D.dist_arm1.symm)))
  constructor
  · intro h
    exact h02 (hL.pairDist_injective (D.dist_arm0.trans (h.trans D.dist_arm2.symm)))
  constructor
  · intro h
    exact h12 (hL.pairDist_injective (D.dist_arm1.trans (h.trans D.dist_arm2.symm)))
  constructor
  · intro h
    exact h0s
      (hL.pairDist_injective (D.dist_arm0.trans (h.trans D.dist_port12.symm)))
  constructor
  · intro h
    exact h1s
      (hL.pairDist_injective (D.dist_arm1.trans (h.trans D.dist_port02.symm)))
  · intro h
    exact h2s
      (hL.pairDist_injective (D.dist_arm2.trans (h.trans D.dist_port01.symm)))

/-- Graph-level G010 endpoint: the six actual distances of a positive named
tripod in a Leech tree are pairwise distinct. -/
theorem actualDistanceList_nodup (D : ActualPositiveTripod T) (hL : IsLeech T) :
    D.actualDistanceList.Nodup := by
  rw [actualDistanceList, D.dist_arm0, D.dist_arm1, D.dist_arm2,
    D.dist_port01, D.dist_port02, D.dist_port12]
  exact
    (positive_tripodDistanceList_nodup_iff
      D.arm0_pos D.arm1_pos D.arm2_pos).2 (D.arm_guard hL)

end ActualPositiveTripod

/-! ## Zero-arm boundary -/

/-- The three genuine pair distances when the median is itself one of the
ports and the two remaining arms have lengths `B` and `C`. -/
def boundaryDistanceList (B C : ℕ) : List ℕ := [B, C, B + C]

/-- Substituting a zero arm into the six-entry tripod list always creates
duplicates.  Thus six-value distinctness is invalid at this boundary. -/
theorem zero_arm_sixDistanceList_not_nodup (B C : ℕ) :
    ¬ (tripodDistanceList 0 B C).Nodup := by
  simp [tripodDistanceList]

/-- Correct zero-arm boundary guard: for positive remaining arms, the three
genuine pair distances are distinct exactly when those arms differ. -/
theorem positive_boundaryDistanceList_nodup_iff
    {B C : ℕ} (hB : 0 < B) (hC : 0 < C) :
    (boundaryDistanceList B C).Nodup ↔ B ≠ C := by
  simp only [boundaryDistanceList, List.nodup_cons, List.mem_cons,
    not_or, List.not_mem_nil, List.nodup_nil]
  constructor
  · aesop
  · intro hBC
    simp [hBC, hB.ne', hC.ne']

/-- Actual indexed-pair certificate for the zero-arm path boundary. -/
structure ActualBoundaryPath {n : ℕ} (T : PosIntTree n) where
  firstArmPair : VertexPair n
  secondArmPair : VertexPair n
  endpointPair : VertexPair n
  pairNodup : [firstArmPair, secondArmPair, endpointPair].Nodup
  firstArm : ℕ
  secondArm : ℕ
  firstArm_pos : 0 < firstArm
  secondArm_pos : 0 < secondArm
  dist_first : T.pairDist firstArmPair = firstArm
  dist_second : T.pairDist secondArmPair = secondArm
  dist_endpoints : T.pairDist endpointPair = firstArm + secondArm

namespace ActualBoundaryPath

variable {n : ℕ} {T : PosIntTree n}

def actualDistanceList (D : ActualBoundaryPath T) : List ℕ :=
  [T.pairDist D.firstArmPair,
   T.pairDist D.secondArmPair,
   T.pairDist D.endpointPair]

/-- Graph-level boundary endpoint: the two positive arms differ, and exactly
the three genuine pair distances are pairwise distinct. -/
theorem arm_ne_and_actualDistanceList_nodup
    (D : ActualBoundaryPath T) (hL : IsLeech T) :
    D.firstArm ≠ D.secondArm ∧ D.actualDistanceList.Nodup := by
  have hpairs : D.firstArmPair ≠ D.secondArmPair := by
    intro h
    exact (List.nodup_cons.mp D.pairNodup).1 (by simp [h])
  have harms : D.firstArm ≠ D.secondArm := by
    intro h
    exact hpairs
      (hL.pairDist_injective (D.dist_first.trans (h.trans D.dist_second.symm)))
  refine ⟨harms, ?_⟩
  rw [actualDistanceList, D.dist_first, D.dist_second, D.dist_endpoints]
  exact
    (positive_boundaryDistanceList_nodup_iff
      D.firstArm_pos D.secondArm_pos).2 harms

end ActualBoundaryPath

end

end LeechTrees.ThreePortMedian
