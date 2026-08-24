import LeechTrees.Foundations
import LeechTrees.QHop.Adapter
import LeechTrees.Expanded.BlockLifts.BlockLiftObstructions

/-!
# Graph adapters for the block-lift obstructions

These adapters connect the arithmetic kernels to actual indexed distances of
a positive integral tree.  The extra structures record only construction
data (embedded block vertices, a pair partition, and the route formulas), not
the desired contradiction or target-spectrum conclusion.
-/

open scoped BigOperators

namespace LeechTrees.AdditionalBlockLifts

open LeechTrees.Foundation

/-! ## Actual embedded scaled order-six blocks -/

/-- An actual six-vertex block embedded in an order-18 tree, with every
internal target multiplier `1,...,15` realised by an actual pair of embedded
vertices. -/
structure EmbeddedScaledOrderSixBlock (T : PosIntTree 18) where
  vertex : Fin 6 → Fin 18
  scale : ℕ
  scale_pos : 0 < scale
  realizes : ∀ k : Fin 15,
    ∃ a b : Fin 6, a ≠ b ∧
      T.dist (vertex a) (vertex b) = scale * (k.1 + 1)

/-- Two embedded blocks are vertex-disjoint. -/
def EmbeddedScaledOrderSixBlock.Disjoint
    {T : PosIntTree 18}
    (A B : EmbeddedScaledOrderSixBlock T) : Prop :=
  ∀ a b, A.vertex a ≠ B.vertex b

private theorem embeddedScale_range
    {T : PosIntTree 18} (hL : IsLeech T)
    (A : EmbeddedScaledOrderSixBlock T) :
    15 * A.scale ≤ 153 := by
  obtain ⟨a, b, hab, hdist⟩ := A.realizes ⟨14, by omega⟩
  have hvne : A.vertex a ≠ A.vertex b := by
    intro h
    have hz : T.dist (A.vertex a) (A.vertex b) = 0 := by simp [h]
    rw [hdist] at hz
    have hpos : 0 < A.scale * (14 + 1) :=
      Nat.mul_pos A.scale_pos (by norm_num)
    norm_num at hz hpos
    exact (Nat.ne_of_gt hpos) hz
  let p : VertexPair 18 :=
    VertexPair.ofDistinct (A.vertex a) (A.vertex b) hvne
  have hp := hL.pairDist_le_target p
  have hpdist : T.pairDist p = T.dist (A.vertex a) (A.vertex b) :=
    T.pairDist_pairOfDistinct _ _ hvne
  rw [hpdist, hdist] at hp
  norm_num [Nat.choose, targetN] at hp ⊢
  simpa [Nat.mul_comm] using hp

/-- Exact G017 endpoint: an order-18 Leech tree cannot contain two disjoint
actual embedded uniformly scaled order-six Leech blocks. -/
theorem no_two_disjoint_embedded_scaled_orderSix_blocks
    {T : PosIntTree 18} (hL : IsLeech T)
    (A B : EmbeddedScaledOrderSixBlock T)
    (hDisjoint : A.Disjoint B) :
    False := by
  have hA := embeddedScale_range hL A
  have hB := embeddedScale_range hL B
  obtain ⟨k, l, hkPos, hkMax, hlPos, hlMax, hkl⟩ :=
    two_scaled_orderSix_blocks_collide A.scale B.scale
      A.scale_pos B.scale_pos hA hB
  let ki : Fin 15 := ⟨k - 1, by omega⟩
  let li : Fin 15 := ⟨l - 1, by omega⟩
  obtain ⟨a₁, a₂, haNe, haDist⟩ := A.realizes ki
  obtain ⟨b₁, b₂, hbNe, hbDist⟩ := B.realizes li
  have hki : ki.1 + 1 = k := by dsimp [ki]; omega
  have hli : li.1 + 1 = l := by dsimp [li]; omega
  rw [hki] at haDist
  rw [hli] at hbDist
  have haVertexNe : A.vertex a₁ ≠ A.vertex a₂ := by
    intro h
    have hz : T.dist (A.vertex a₁) (A.vertex a₂) = 0 := by simp [h]
    rw [haDist] at hz
    have hpos : 0 < A.scale * k := Nat.mul_pos A.scale_pos hkPos
    omega
  have hbVertexNe : B.vertex b₁ ≠ B.vertex b₂ := by
    intro h
    have hz : T.dist (B.vertex b₁) (B.vertex b₂) = 0 := by simp [h]
    rw [hbDist] at hz
    have hpos : 0 < B.scale * l := Nat.mul_pos B.scale_pos hlPos
    omega
  let pa : VertexPair 18 :=
    VertexPair.ofDistinct (A.vertex a₁) (A.vertex a₂) haVertexNe
  let pb : VertexPair 18 :=
    VertexPair.ofDistinct (B.vertex b₁) (B.vertex b₂) hbVertexNe
  have hpairDist : T.pairDist pa = T.pairDist pb := by
    rw [T.pairDist_pairOfDistinct, T.pairDist_pairOfDistinct,
      haDist, hbDist, hkl]
  have hpairs : pa = pb := hL.pairDist_injective hpairDist
  have hcases :=
    (LeechTrees.QHop.VertexPair.ofDistinct_eq_iff
      haVertexNe hbVertexNe).mp hpairs
  rcases hcases with hcases | hcases
  · exact hDisjoint a₁ b₁ hcases.1
  · exact hDisjoint a₁ b₂ hcases.1

/-! ## Actual three-copy parity adapter -/

/-- Exact seed distance matrix, now in natural-number form. -/
def orderSixSeedDistance : Fin 6 → Fin 6 → ℕ :=
  ![![0, 1, 2, 9, 13, 5],
    ![1, 0, 3, 10, 14, 6],
    ![2, 3, 0, 11, 15, 7],
    ![9, 10, 11, 0, 12, 4],
    ![13, 14, 15, 12, 0, 8],
    ![5, 6, 7, 4, 8, 0]]

/-- An actual partition of all eighteen vertices into three scaled copies of
the order-six metric. -/
structure ActualThreeScaledSixPartition (T : PosIntTree 18) where
  vertexEquiv : (Fin 3 × Fin 6) ≃ Fin 18
  scale : Fin 3 → ℕ
  scale_pos : ∀ i, 0 < scale i
  scaledMetric : ∀ i x y,
    T.dist (vertexEquiv (i, x)) (vertexEquiv (i, y)) =
      scale i * orderSixSeedDistance x y

noncomputable def ActualThreeScaledSixPartition.blockMass
    {T : PosIntTree 18} (M : ActualThreeScaledSixPartition T)
    (r : Fin 18) (i : Fin 3) : ℤ :=
  ∑ x : Fin 6, weightParitySign (T.dist r (M.vertexEquiv (i, x)))

/-- Root parity signs multiply along an actual tree path. -/
theorem root_weightParitySign_factor
    {n : ℕ} (T : PosIntTree n) (r u v : Fin n) :
    weightParitySign (T.dist r v) =
      weightParitySign (T.dist r u) * weightParitySign (T.dist u v) := by
  have heven := T.root_path_even r u v
  rw [Nat.even_iff] at heven
  have hmod : T.dist r v % 2 = (T.dist r u + T.dist u v) % 2 := by
    omega
  rw [weightParitySign_eq_of_mod_two_eq _ _ hmod]
  exact weightParitySign_add _ _

/-- Direct six-entry calculation of the local scaled seed imbalance. -/
theorem scaled_orderSix_local_mass (s : ℕ) (_hs : 0 < s) :
    (∑ x : Fin 6,
      weightParitySign (s * orderSixSeedDistance 0 x)) =
      if s % 2 = 0 then 6 else -2 := by
  have hsmod : s % 2 = 0 ∨ s % 2 = 1 := by omega
  rcases hsmod with hs0 | hs1
  · norm_num [hs0, orderSixSeedDistance, weightParitySign,
      Fin.sum_univ_succ, Nat.mul_mod]
  · norm_num [hs1, orderSixSeedDistance, weightParitySign,
      Fin.sum_univ_succ, Nat.mul_mod]

/-- Each actual embedded scaled block contributes `±2` or `±6` to the global
root-parity mass. -/
theorem actual_scaled_orderSix_blockMass_cases
    {T : PosIntTree 18} (M : ActualThreeScaledSixPartition T)
    (r : Fin 18) (i : Fin 3) :
    M.blockMass r i = 2 ∨ M.blockMass r i = -2 ∨
      M.blockMass r i = 6 ∨ M.blockMass r i = -6 := by
  have hfactor : M.blockMass r i =
      weightParitySign (T.dist r (M.vertexEquiv (i, 0))) *
        (∑ x : Fin 6,
          weightParitySign (M.scale i * orderSixSeedDistance 0 x)) := by
    unfold ActualThreeScaledSixPartition.blockMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    calc
      weightParitySign (T.dist r (M.vertexEquiv (i, x))) =
          weightParitySign (T.dist r (M.vertexEquiv (i, 0))) *
            weightParitySign
              (T.dist (M.vertexEquiv (i, 0)) (M.vertexEquiv (i, x))) :=
        root_weightParitySign_factor T r
          (M.vertexEquiv (i, 0)) (M.vertexEquiv (i, x))
      _ = weightParitySign (T.dist r (M.vertexEquiv (i, 0))) *
            weightParitySign (M.scale i * orderSixSeedDistance 0 x) := by
        rw [M.scaledMetric]
  rw [scaled_orderSix_local_mass (M.scale i) (M.scale_pos i)] at hfactor
  have href : weightParitySign (T.dist r (M.vertexEquiv (i, 0))) = 1 ∨
      weightParitySign (T.dist r (M.vertexEquiv (i, 0))) = -1 := by
    unfold weightParitySign
    split_ifs <;> simp
  have hsmod : M.scale i % 2 = 0 ∨ M.scale i % 2 = 1 := by omega
  rcases href with href | href
  · rw [href] at hfactor
    rcases hsmod with hs | hs
    · simp [hs] at hfactor
      simp [hfactor]
    · simp [hs] at hfactor
      simp [hfactor]
  · rw [href] at hfactor
    rcases hsmod with hs | hs
    · simp [hs] at hfactor
      simp [hfactor]
    · simp [hs] at hfactor
      simp [hfactor]

private theorem rootParityMass_eq
    {T : PosIntTree 18} (r : Fin 18) :
    (∑ v : Fin 18, weightParitySign (T.dist r v)) =
      2 * (T.parityClassSize r : ℤ) - 18 := by
  classical
  let evenSet : Finset (Fin 18) :=
    Finset.univ.filter fun v => T.dist r v % 2 = 0
  have hEvenCard : evenSet.card = T.parityClassSize r := by
    unfold evenSet PosIntTree.parityClassSize
    rw [Fintype.card_subtype]
  have hsplit : (Finset.univ : Finset (Fin 18)) =
      evenSet ∪ (Finset.univ \ evenSet) := by
    ext v
    simp [evenSet]
  have hdisj : Disjoint evenSet (Finset.univ \ evenSet) :=
    Finset.disjoint_sdiff
  rw [hsplit, Finset.sum_union hdisj]
  have hEvenSum :
      (∑ v ∈ evenSet, weightParitySign (T.dist r v)) = evenSet.card := by
    calc
      (∑ v ∈ evenSet, weightParitySign (T.dist r v)) =
          ∑ _v ∈ evenSet, (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro v hv
        simp only [evenSet, Finset.mem_filter] at hv
        simp [weightParitySign, hv.2]
      _ = evenSet.card := by simp
  have hOddSum :
      (∑ v ∈ (Finset.univ \ evenSet),
        weightParitySign (T.dist r v)) =
        -((Finset.univ \ evenSet).card : ℤ) := by
    calc
      (∑ v ∈ (Finset.univ \ evenSet),
          weightParitySign (T.dist r v)) =
          ∑ _v ∈ (Finset.univ \ evenSet), (-1 : ℤ) := by
            apply Finset.sum_congr rfl
            intro v hv
            have hne : T.dist r v % 2 ≠ 0 := by
              simpa [evenSet] using (Finset.mem_sdiff.mp hv).2
            have hone : T.dist r v % 2 = 1 := by omega
            simp [weightParitySign, hone]
      _ = -((Finset.univ \ evenSet).card : ℤ) := by simp
  rw [hEvenSum, hOddSum]
  have hcard : (Finset.univ \ evenSet).card = 18 - evenSet.card := by
    rw [Finset.card_sdiff]
    simp
  rw [hcard, hEvenCard]
  have hle := T.parityClassSize_le_order r
  omega

/-- Actual G017 parity endpoint: three embedded scaled copies cannot form an
order-18 Leech tree, independently of their bridges or quotient path. -/
theorem no_actual_three_scaled_orderSix_partition
    {T : PosIntTree 18} (hL : IsLeech T)
    (M : ActualThreeScaledSixPartition T) :
    False := by
  let r : Fin 18 := 0
  let x₁ := M.blockMass r 0
  let x₂ := M.blockMass r 1
  let x₃ := M.blockMass r 2
  have h₁ := actual_scaled_orderSix_blockMass_cases M r 0
  have h₂ := actual_scaled_orderSix_blockMass_cases M r 1
  have h₃ := actual_scaled_orderSix_blockMass_cases M r 2
  have hpartition :
      (∑ v : Fin 18, weightParitySign (T.dist r v)) = x₁ + x₂ + x₃ := by
    calc
      (∑ v : Fin 18, weightParitySign (T.dist r v)) =
          ∑ z : Fin 3 × Fin 6,
            weightParitySign (T.dist r (M.vertexEquiv z)) := by
              symm
              apply Fintype.sum_equiv M.vertexEquiv
              intro z
              rfl
      _ = x₁ + x₂ + x₃ := by
        rw [Fintype.sum_prod_type]
        simp [x₁, x₂, x₃, ActualThreeScaledSixPartition.blockMass,
          Fin.sum_univ_succ]
        ring
  have hglobal :
      (∑ v : Fin 18, weightParitySign (T.dist r v)) = 4 ∨
      (∑ v : Fin 18, weightParitySign (T.dist r v)) = -4 := by
    rw [rootParityMass_eq r]
    rcases t3_order18_class_sizes hL r with h7 | h11
    · right
      rw [h7]
      norm_num
    · left
      rw [h11]
      norm_num
  have hnot := three_scaled_six_blocks_fail_order18_parity x₁ x₂ x₃ h₁ h₂ h₃
  rcases hglobal with hglobal | hglobal
  · apply hnot
    rw [← hpartition, hglobal]
    norm_num
  · apply hnot
    rw [← hpartition, hglobal]
    norm_num

/-! ## Actual recursive six-gadget adapter -/

/-- Actual order-18 center-gadget construction.  Index zero in each `Fin 3`
gadget is its center; the other two center depths are `s_i` and `2s_i`.
Every macro bridge is the actual center-to-center path and has the required
parity. -/
structure ActualSixCenterGadgetLift (T : PosIntTree 18) where
  macroGraph : SimpleGraph (Fin 6)
  macroConnected : macroGraph.Connected
  vertexEquiv : (Fin 6 × Fin 3) ≃ Fin 18
  scale : Fin 6 → ℕ
  scale_pos : ∀ i, 0 < scale i
  centerDepth : ∀ i x,
    T.dist (vertexEquiv (i, 0)) (vertexEquiv (i, x)) =
      match x.1 with
      | 0 => 0
      | 1 => scale i
      | _ => 2 * scale i
  bridgeWeight : Fin 6 → Fin 6 → ℕ
  bridgeDistance : ∀ ⦃i j⦄, macroGraph.Adj i j →
    T.dist (vertexEquiv (i, 0)) (vertexEquiv (j, 0)) = bridgeWeight i j
  bridgeParity : ∀ ⦃i j⦄, macroGraph.Adj i j →
    bridgeWeight i j % 2 = (scale i + scale j) % 2

noncomputable def ActualSixCenterGadgetLift.centerSign
    {T : PosIntTree 18} (M : ActualSixCenterGadgetLift T)
    (r : Fin 18) (i : Fin 6) : ℤ :=
  weightParitySign (T.dist r (M.vertexEquiv (i, 0)))

theorem actual_centerGadget_local_mass
    {T : PosIntTree 18} (M : ActualSixCenterGadgetLift T)
    (i : Fin 6) :
    (∑ x : Fin 3,
      weightParitySign
        (T.dist (M.vertexEquiv (i, 0)) (M.vertexEquiv (i, x)))) =
      centerGadgetLocalImbalance (decide (M.scale i % 2 = 1)) := by
  have hs : M.scale i % 2 = 0 ∨ M.scale i % 2 = 1 := by omega
  rcases hs with hs | hs
  · simp [M.centerDepth, centerGadgetLocalImbalance, weightParitySign, hs,
      Fin.sum_univ_succ]
  · simp [M.centerDepth, centerGadgetLocalImbalance, weightParitySign, hs,
      Fin.sum_univ_succ]

/-- The actual global mass is exactly the six-gadget signed sum used by the
abstract parity obstruction. -/
theorem actual_sixCenterGadget_global_mass
    {T : PosIntTree 18} (M : ActualSixCenterGadgetLift T)
    (r : Fin 18) :
    (∑ v : Fin 18, weightParitySign (T.dist r v)) =
      ∑ i : Fin 6, M.centerSign r i *
        centerGadgetLocalImbalance (decide (M.scale i % 2 = 1)) := by
  calc
    (∑ v : Fin 18, weightParitySign (T.dist r v)) =
        ∑ z : Fin 6 × Fin 3,
          weightParitySign (T.dist r (M.vertexEquiv z)) := by
            symm
            apply Fintype.sum_equiv M.vertexEquiv
            intro z
            rfl
    _ = ∑ i : Fin 6, ∑ x : Fin 3,
          weightParitySign (T.dist r (M.vertexEquiv (i, x))) := by
            rw [Fintype.sum_prod_type]
    _ = ∑ i : Fin 6, M.centerSign r i *
          (∑ x : Fin 3,
            weightParitySign
              (T.dist (M.vertexEquiv (i, 0)) (M.vertexEquiv (i, x)))) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            unfold ActualSixCenterGadgetLift.centerSign
            exact root_weightParitySign_factor T r
              (M.vertexEquiv (i, 0)) (M.vertexEquiv (i, x))
    _ = ∑ i : Fin 6, M.centerSign r i *
          centerGadgetLocalImbalance (decide (M.scale i % 2 = 1)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [actual_centerGadget_local_mass M i]

/-- Actual G017 recursive-lift endpoint.  No abstract `edgeRule` remains in
the statement: it is derived from the real tree root parity and the actual
center bridge distances. -/
theorem no_actual_recursive_six_center_gadget_lift
    {T : PosIntTree 18} (hL : IsLeech T)
    (M : ActualSixCenterGadgetLift T) :
    False := by
  let r : Fin 18 := 0
  have hτ : ∀ i, M.centerSign r i = 1 ∨ M.centerSign r i = -1 := by
    intro i
    unfold ActualSixCenterGadgetLift.centerSign weightParitySign
    split_ifs <;> simp
  have hSignRule : ∀ ⦃u v⦄, M.macroGraph.Adj u v →
      M.centerSign r v =
        M.centerSign r u * weightParitySign (M.bridgeWeight u v) := by
    intro u v huv
    unfold ActualSixCenterGadgetLift.centerSign
    rw [root_weightParitySign_factor T r
      (M.vertexEquiv (u, 0)) (M.vertexEquiv (v, 0))]
    rw [M.bridgeDistance huv]
  have hAbstract := center_digit_lift_of_bridge_congruence_impossible
    M.macroGraph M.macroConnected M.scale M.bridgeWeight
    (M.centerSign r) hτ M.bridgeParity hSignRule
  have hmass := actual_sixCenterGadget_global_mass M r
  have hglobal :
      (∑ v : Fin 18, weightParitySign (T.dist r v)) = 4 ∨
      (∑ v : Fin 18, weightParitySign (T.dist r v)) = -4 := by
    rw [rootParityMass_eq r]
    rcases t3_order18_class_sizes hL r with h7 | h11
    · right
      rw [h7]
      norm_num
    · left
      rw [h11]
      norm_num
  rcases hglobal with hglobal | hglobal
  · exact hAbstract.1 (hmass.symm.trans hglobal)
  · exact hAbstract.2 (hmass.symm.trans hglobal)

/-! ## Actual three-block pair partition and exact 153 forms -/

/-- Construction data for three actual connected six-vertex blocks whose
quotient is a path.  `pairEquiv` is the exact 45+36+36+36 partition of actual
unordered vertex pairs; the four formula fields are the unique-path distance
decompositions. -/
structure ActualThreeBlockPathModel (T : PosIntTree 18) where
  forms : ThreeBlockPathForms
  pairEquiv : ThreeBlockIndex ≃ VertexPair 18
  withinFormula : ∀ z : Fin 3 × Fin 15,
    T.pairDist (pairEquiv (.inl z)) = forms.internal z.1 z.2
  leftMiddleFormula : ∀ z : Fin 6 × Fin 6,
    T.pairDist (pairEquiv (.inr (.inl z))) =
      forms.leftDepth z.1 + forms.leftBridge + forms.middleFromLeft z.2
  middleRightFormula : ∀ z : Fin 6 × Fin 6,
    T.pairDist (pairEquiv (.inr (.inr (.inl z)))) =
      forms.middleToRight z.1 + forms.rightBridge + forms.rightDepth z.2
  leftRightFormula : ∀ z : Fin 6 × Fin 6,
    T.pairDist (pairEquiv (.inr (.inr (.inr z)))) =
      forms.leftDepth z.1 + forms.leftBridge +
        forms.middlePortSeparation + forms.rightBridge + forms.rightDepth z.2

/-- Strong topology constructor data.  Unlike `ActualThreeBlockPathModel`,
this structure stores only the actual vertex partition, two physical bridges,
their deletion-side incidences, ports, and the exact pair-index partition.
The 153 linear formulas are derived below from the tree's cut decomposition. -/
structure ActualThreeBlockTopology (T : PosIntTree 18) where
  vertexEquiv : (Fin 3 × Fin 6) ≃ Fin 18
  withinPairEquiv : Fin 15 ≃ VertexPair 6
  leftPort : Fin 6
  middleLeftPort : Fin 6
  middleRightPort : Fin 6
  rightPort : Fin 6
  leftBridge : T.Edge
  rightBridge : T.Edge
  leftBridge_left :
    T.edgeLeft leftBridge = vertexEquiv (0, leftPort)
  leftBridge_right :
    T.edgeRight leftBridge = vertexEquiv (1, middleLeftPort)
  rightBridge_left :
    T.edgeLeft rightBridge = vertexEquiv (1, middleRightPort)
  rightBridge_right :
    T.edgeRight rightBridge = vertexEquiv (2, rightPort)
  block0_left : ∀ x, T.LeftCut leftBridge (vertexEquiv (0, x))
  block1_right : ∀ x, T.RightCut leftBridge (vertexEquiv (1, x))
  block2_right_leftBridge : ∀ x, T.RightCut leftBridge (vertexEquiv (2, x))
  block1_left : ∀ x, T.LeftCut rightBridge (vertexEquiv (1, x))
  block2_right : ∀ x, T.RightCut rightBridge (vertexEquiv (2, x))
  pairEquiv : ThreeBlockIndex ≃ VertexPair 18
  pairEquiv_within : ∀ z : Fin 3 × Fin 15,
    pairEquiv (.inl z) = VertexPair.ofDistinct
      (vertexEquiv (z.1, (withinPairEquiv z.2).left))
      (vertexEquiv (z.1, (withinPairEquiv z.2).right))
      (by
        intro h
        have hh := vertexEquiv.injective h
        exact (ne_of_lt (withinPairEquiv z.2).left_lt_right)
          (Prod.mk.inj hh).2)
  pairEquiv_leftMiddle : ∀ z : Fin 6 × Fin 6,
    pairEquiv (.inr (.inl z)) = VertexPair.ofDistinct
      (vertexEquiv (0, z.1)) (vertexEquiv (1, z.2))
      (by
        intro h
        have hh := vertexEquiv.injective h
        have hfirst := congrArg (fun p : Fin 3 × Fin 6 => p.1) hh
        have hval := congrArg Fin.val hfirst
        norm_num at hval)
  pairEquiv_middleRight : ∀ z : Fin 6 × Fin 6,
    pairEquiv (.inr (.inr (.inl z))) = VertexPair.ofDistinct
      (vertexEquiv (1, z.1)) (vertexEquiv (2, z.2))
      (by
        intro h
        have hh := vertexEquiv.injective h
        have hfirst := congrArg (fun p : Fin 3 × Fin 6 => p.1) hh
        have hval := congrArg Fin.val hfirst
        norm_num at hval)
  pairEquiv_leftRight : ∀ z : Fin 6 × Fin 6,
    pairEquiv (.inr (.inr (.inr z))) = VertexPair.ofDistinct
      (vertexEquiv (0, z.1)) (vertexEquiv (2, z.2))
      (by
        intro h
        have hh := vertexEquiv.injective h
        have hfirst := congrArg (fun p : Fin 3 × Fin 6 => p.1) hh
        have hval := congrArg Fin.val hfirst
        norm_num at hval)

noncomputable def ActualThreeBlockTopology.forms
    {T : PosIntTree 18} (M : ActualThreeBlockTopology T) :
    ThreeBlockPathForms where
  internal i k := T.dist
    (M.vertexEquiv (i, (M.withinPairEquiv k).left))
    (M.vertexEquiv (i, (M.withinPairEquiv k).right))
  leftDepth x := T.dist (M.vertexEquiv (0, x))
    (M.vertexEquiv (0, M.leftPort))
  middleFromLeft x := T.dist (M.vertexEquiv (1, M.middleLeftPort))
    (M.vertexEquiv (1, x))
  middleToRight x := T.dist (M.vertexEquiv (1, x))
    (M.vertexEquiv (1, M.middleRightPort))
  rightDepth x := T.dist (M.vertexEquiv (2, M.rightPort))
    (M.vertexEquiv (2, x))
  middlePortSeparation := T.dist
    (M.vertexEquiv (1, M.middleLeftPort))
    (M.vertexEquiv (1, M.middleRightPort))
  leftBridge := T.weight M.leftBridge
  rightBridge := T.weight M.rightBridge

/-- The route formulas are obtained from the actual two edge cuts. -/
noncomputable def ActualThreeBlockTopology.toPathModel
    {T : PosIntTree 18} (M : ActualThreeBlockTopology T) :
    ActualThreeBlockPathModel T where
  forms := M.forms
  pairEquiv := M.pairEquiv
  withinFormula := by
    intro z
    rw [M.pairEquiv_within z, T.pairDist_pairOfDistinct]
    rfl
  leftMiddleFormula := by
    intro z
    rw [M.pairEquiv_leftMiddle z, T.pairDist_pairOfDistinct]
    have h := T.cross_distance_decomposition M.leftBridge
      (M.block0_left z.1) (M.block1_right z.2)
    rw [M.leftBridge_left, M.leftBridge_right] at h
    exact h
  middleRightFormula := by
    intro z
    rw [M.pairEquiv_middleRight z, T.pairDist_pairOfDistinct]
    have h := T.cross_distance_decomposition M.rightBridge
      (M.block1_left z.1) (M.block2_right z.2)
    rw [M.rightBridge_left, M.rightBridge_right] at h
    exact h
  leftRightFormula := by
    intro z
    rw [M.pairEquiv_leftRight z, T.pairDist_pairOfDistinct]
    have hOuter := T.cross_distance_decomposition M.leftBridge
      (M.block0_left z.1) (M.block2_right_leftBridge z.2)
    have hMiddle := T.cross_distance_decomposition M.rightBridge
      (M.block1_left M.middleLeftPort) (M.block2_right z.2)
    rw [M.leftBridge_left, M.leftBridge_right] at hOuter
    rw [M.rightBridge_left, M.rightBridge_right] at hMiddle
    rw [hOuter, hMiddle]
    dsimp only [ActualThreeBlockTopology.forms]
    omega

theorem ActualThreeBlockPathModel.pairDistance_eq_rank
    {T : PosIntTree 18} (M : ActualThreeBlockPathModel T)
    (i : ThreeBlockIndex) :
    T.pairDist (M.pairEquiv i) = M.forms.rank i := by
  rcases i with z | z
  · exact M.withinFormula z
  · rcases z with z | z
    · exact M.leftMiddleFormula z
    · rcases z with z | z
      · exact M.middleRightFormula z
      · exact M.leftRightFormula z

/-- From an actual Leech spectrum, the 153 construction forms satisfy the
exact bounds and `AllDifferent`. -/
theorem actual_threeBlock_bounds_injective
    {T : PosIntTree 18} (M : ActualThreeBlockPathModel T)
    (hL : IsLeech T) :
    (∀ i, 1 ≤ M.forms.rank i ∧ M.forms.rank i ≤ 153) ∧
      Function.Injective M.forms.rank := by
  constructor
  · intro i
    have hmem := hL.pairDist_mem (M.pairEquiv i)
    rw [M.pairDistance_eq_rank i] at hmem
    simpa [targetN] using Finset.mem_Icc.mp hmem
  · intro i j hij
    apply M.pairEquiv.injective
    apply hL.pairDist_injective
    rw [M.pairDistance_eq_rank i, M.pairDistance_eq_rank j]
    exact hij

/-- Exact target-spectrum reduction for the actual three-block construction.
The converse uses the pair equivalence, so support equality cannot hide a
repeated distance. -/
theorem actual_threeBlock_isLeech_iff_bounds_injective
    {T : PosIntTree 18} (M : ActualThreeBlockPathModel T) :
    IsLeech T ↔
      (∀ i, 1 ≤ M.forms.rank i ∧ M.forms.rank i ≤ 153) ∧
        Function.Injective M.forms.rank := by
  constructor
  · exact actual_threeBlock_bounds_injective M
  · rintro ⟨hBounds, hInjective⟩
    have hSpectrum := threeBlock_target_of_bounds_injective
      M.forms hBounds hInjective
    refine { pairDist_mem := ?_, bijective := ?_ }
    · intro p
      let i := M.pairEquiv.symm p
      have hi := hBounds i
      have heq : M.pairEquiv i = p := M.pairEquiv.apply_symm_apply p
      rw [← heq, M.pairDistance_eq_rank i]
      simpa [targetN] using Finset.mem_Icc.mpr hi
    · constructor
      · intro p q hpq
        let i := M.pairEquiv.symm p
        let j := M.pairEquiv.symm q
        have hp : M.pairEquiv i = p := M.pairEquiv.apply_symm_apply p
        have hq : M.pairEquiv j = q := M.pairEquiv.apply_symm_apply q
        have hrank : M.forms.rank i = M.forms.rank j := by
          calc
            M.forms.rank i = T.pairDist (M.pairEquiv i) :=
              (M.pairDistance_eq_rank i).symm
            _ = T.pairDist p := congrArg T.pairDist hp
            _ = T.pairDist q := congrArg Subtype.val hpq
            _ = T.pairDist (M.pairEquiv j) := (congrArg T.pairDist hq).symm
            _ = M.forms.rank j := M.pairDistance_eq_rank j
        have hij := hInjective hrank
        simpa [i, j] using congrArg M.pairEquiv hij
      · intro k
        have hk : k.1 ∈ M.forms.spectrum := by
          rw [hSpectrum]
          change k.1 ∈ Finset.Icc 1 (targetN 18)
          exact k.2
        simp only [ThreeBlockPathForms.spectrum, Finset.mem_image] at hk
        obtain ⟨i, hi, hrank⟩ := hk
        refine ⟨M.pairEquiv i, ?_⟩
        apply Subtype.ext
        change T.pairDist (M.pairEquiv i) = k.1
        rw [M.pairDistance_eq_rank i, hrank]

/-- Gap-free topology-level 153-form reduction. -/
theorem actual_threeBlock_topology_isLeech_iff
    {T : PosIntTree 18} (M : ActualThreeBlockTopology T) :
    IsLeech T ↔
      (∀ i, 1 ≤ M.forms.rank i ∧ M.forms.rank i ≤ 153) ∧
        Function.Injective M.forms.rank :=
  actual_threeBlock_isLeech_iff_bounds_injective M.toPathModel

end LeechTrees.AdditionalBlockLifts
