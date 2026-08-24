import LeechTrees.ParityTailExactBundle

/-!
# Physical-rank and parity-channel puncturing

This module formalizes G002 and G003 from the structural-progress ledger.
It works with the indexed `PosIntTree` / `IsLeech` model, so every set below
retains the actual pair and edge witnesses used to prove injectivity.

The equality statements distinguish the exact rank-aware tail from the
coarser full parity target.  Equality in the coarse bound therefore includes
the additional condition that the gap between those two allowed sets is
empty; this is the audited equality correction in `NEW_STRUCTURAL_LEMMAS.md`.
-/

open scoped BigOperators

namespace LeechTrees.RankParity

open LeechTrees.Foundation
open LeechTrees.ParityTail
open LeechTrees.ParityTail.GraphAdapterV1

noncomputable section

variable {n : ℕ} (T : PosIntTree n)

/-- The actual set `C_e` of distances whose pair path crosses `e`. -/
def crossDistanceSpectrum (e : T.Edge) : Finset ℕ :=
  Finset.univ.image (T.rootedCrossSum e)

/-- The actual physical-weight set. -/
def physicalWeightSet : Finset ℕ :=
  Finset.univ.image T.weight

/-- Edges at or below `e` in strict physical-weight order. -/
def lowerPhysicalEdgeSet (e : T.Edge) : Finset T.Edge :=
  Finset.univ.filter fun f => T.weight f ≤ T.weight e

/-- Edges strictly later than `e` in physical-weight order. -/
def laterPhysicalEdgeSet (e : T.Edge) : Finset T.Edge :=
  Finset.univ.filter fun f => T.weight e < T.weight f

/-- The one-based physical rank of `e`. -/
def physicalRank (e : T.Edge) : ℕ :=
  (lowerPhysicalEdgeSet T e).card

/-- The set of physical weights at ranks strictly after `e`. -/
def laterPhysicalWeightSet (e : T.Edge) : Finset ℕ :=
  (laterPhysicalEdgeSet T e).image T.weight

/-- The exact physical-rank-punctured target tail for the cut of `e`. -/
def puncturedTail (e : T.Edge) : Finset ℕ :=
  Finset.Icc (T.weight e) (targetN n) \ laterPhysicalWeightSet T e

theorem weight_mem_crossDistanceSpectrum (e : T.Edge) :
    T.weight e ∈ crossDistanceSpectrum T e := by
  let x₀ : T.LeftVertex e × T.RightVertex e :=
    (⟨T.edgeLeft e, T.edgeLeft_mem_LeftCut e⟩,
      ⟨T.edgeRight e, T.edgeRight_mem_RightCut e⟩)
  rw [crossDistanceSpectrum, Finset.mem_image]
  refine ⟨x₀, Finset.mem_univ _, ?_⟩
  simp [x₀, PosIntTree.rootedCrossSum, PosIntTree.leftDepth,
    PosIntTree.rightDepth]

theorem weight_mem_physicalWeightSet (e : T.Edge) :
    T.weight e ∈ physicalWeightSet T := by
  exact Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩

/-- The physical-rank puncture: the crossing block contains exactly its own
physical edge weight and no other physical weight. -/
theorem crossDistanceSpectrum_inter_physicalWeightSet
    {T : PosIntTree n} (hL : IsLeech T) (e : T.Edge) :
    crossDistanceSpectrum T e ∩ physicalWeightSet T = {T.weight e} := by
  classical
  ext k
  constructor
  · intro hk
    rcases Finset.mem_inter.mp hk with ⟨hkC, hkW⟩
    rcases Finset.mem_image.mp hkC with ⟨x, -, hx⟩
    rcases Finset.mem_image.mp hkW with ⟨f, -, hf⟩
    have hpair : T.crossVertexPair e x = T.edgePair f :=
      hL.pairDist_injective <| by
        rw [T.pairDist_crossVertexPair e, T.edgePair_dist f, hx, hf]
    have hcross := T.crossVertexPair_crosses e x
    rw [hpair] at hcross
    simp only [T.edgePair_left, T.edgePair_right, T.pathEdges_edge,
      Finset.mem_singleton] at hcross
    have hef : e = f := Subtype.ext hcross
    rw [Finset.mem_singleton]
    exact hf.symm.trans (congrArg T.weight hef).symm
  · intro hk
    have hk' : k = T.weight e := Finset.mem_singleton.mp hk
    subst k
    exact Finset.mem_inter.mpr
      ⟨weight_mem_crossDistanceSpectrum T e,
        weight_mem_physicalWeightSet T e⟩

theorem crossDistanceSpectrum_subset_targetTail
    {T : PosIntTree n} (hL : IsLeech T) (e : T.Edge) :
    crossDistanceSpectrum T e ⊆ Finset.Icc (T.weight e) (targetN n) := by
  intro k hk
  rcases Finset.mem_image.mp hk with ⟨x, -, rfl⟩
  exact T.rootedCrossSum_mem_target_tail hL e x

theorem laterPhysicalWeightSet_subset_physicalWeightSet (e : T.Edge) :
    laterPhysicalWeightSet T e ⊆ physicalWeightSet T := by
  intro k hk
  rcases Finset.mem_image.mp hk with ⟨f, hf, rfl⟩
  exact weight_mem_physicalWeightSet T f

theorem laterPhysicalWeightSet_subset_targetTail
    {T : PosIntTree n} (hL : IsLeech T) (e : T.Edge) :
    laterPhysicalWeightSet T e ⊆ Finset.Icc (T.weight e) (targetN n) := by
  intro k hk
  rcases Finset.mem_image.mp hk with ⟨f, hf, rfl⟩
  have hlt : T.weight e < T.weight f :=
    (Finset.mem_filter.mp hf).2
  have htarget := t1_edge_weight_mem_target hL f
  exact Finset.mem_Icc.mpr ⟨hlt.le, (Finset.mem_Icc.mp htarget).2⟩

theorem crossDistanceSpectrum_subset_puncturedTail
    {T : PosIntTree n} (hL : IsLeech T) (e : T.Edge) :
    crossDistanceSpectrum T e ⊆ puncturedTail T e := by
  intro k hk
  rw [puncturedTail, Finset.mem_sdiff]
  refine ⟨crossDistanceSpectrum_subset_targetTail hL e hk, ?_⟩
  intro hklater
  have hkphys := laterPhysicalWeightSet_subset_physicalWeightSet T e hklater
  have hown : k = T.weight e := by
    have : k ∈ crossDistanceSpectrum T e ∩ physicalWeightSet T :=
      Finset.mem_inter.mpr ⟨hk, hkphys⟩
    rw [crossDistanceSpectrum_inter_physicalWeightSet hL e,
      Finset.mem_singleton] at this
    exact this
  rcases Finset.mem_image.mp hklater with ⟨f, hf, hfweight⟩
  have hlt := (Finset.mem_filter.mp hf).2
  omega

theorem crossDistanceSpectrum_card
    {T : PosIntTree n} (hL : IsLeech T) (e : T.Edge) :
    (crossDistanceSpectrum T e).card =
      T.cutSize e * (n - T.cutSize e) := by
  calc
    (crossDistanceSpectrum T e).card =
        Fintype.card (T.LeftVertex e × T.RightVertex e) := by
      exact Finset.card_image_of_injective _
        (T.rootedCrossSum_injective hL e)
    _ = Fintype.card (T.LeftVertex e) *
        Fintype.card (T.RightVertex e) := Fintype.card_prod _ _
    _ = T.cutSize e * (n - T.cutSize e) := by
      rw [T.rightVertex_card e]
      rfl

theorem laterPhysicalWeightSet_card
    {T : PosIntTree n} (hL : IsLeech T) (e : T.Edge) :
    (laterPhysicalWeightSet T e).card =
      (laterPhysicalEdgeSet T e).card := by
  exact Finset.card_image_of_injective _ (t1_edge_weight_injective hL)

theorem physicalRank_add_later_card
    {T : PosIntTree n} (hL : IsLeech T) (e : T.Edge) :
    physicalRank T e + (laterPhysicalWeightSet T e).card =
      Fintype.card T.Edge := by
  classical
  have hdisj : Disjoint (lowerPhysicalEdgeSet T e)
      (laterPhysicalEdgeSet T e) := by
    rw [Finset.disjoint_left]
    intro f hfLower hfLater
    have hle := (Finset.mem_filter.mp hfLower).2
    have hlt := (Finset.mem_filter.mp hfLater).2
    omega
  have hunion : lowerPhysicalEdgeSet T e ∪ laterPhysicalEdgeSet T e =
      Finset.univ := by
    ext f
    by_cases h : T.weight f ≤ T.weight e
    · simp [lowerPhysicalEdgeSet, laterPhysicalEdgeSet, h,
        Nat.not_lt_of_ge h]
    · have hlt : T.weight e < T.weight f := Nat.lt_of_not_ge h
      simp [lowerPhysicalEdgeSet, laterPhysicalEdgeSet, h, hlt]
  rw [physicalRank, laterPhysicalWeightSet_card hL e,
    ← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]

theorem puncturedTail_card
    {T : PosIntTree n} (hL : IsLeech T) (e : T.Edge) :
    (puncturedTail T e).card =
      (targetN n - T.weight e + 1) -
        (laterPhysicalWeightSet T e).card := by
  rw [puncturedTail, Finset.card_sdiff_of_subset
    (laterPhysicalWeightSet_subset_targetTail hL e)]
  have hw := (Finset.mem_Icc.mp (t1_edge_weight_mem_target hL e)).2
  simp only [Nat.card_Icc]
  omega

/-- The physical-rank-punctured cut cap in invariant rank language. -/
theorem physicalRank_punctured_cut_cap
    {T : PosIntTree n} (hL : IsLeech T) (e : T.Edge) :
    T.weight e + T.cutSize e * (n - T.cutSize e) +
        (Fintype.card T.Edge - physicalRank T e) ≤
      targetN n + 1 := by
  have hcard := Finset.card_le_card
    (crossDistanceSpectrum_subset_puncturedTail hL e)
  rw [crossDistanceSpectrum_card hL e, puncturedTail_card hL e] at hcard
  have hrank := physicalRank_add_later_card hL e
  have hw := (Finset.mem_Icc.mp (t1_edge_weight_mem_target hL e)).2
  have hlaterCard := Finset.card_le_card
    (laterPhysicalWeightSet_subset_targetTail hL e)
  simp only [Nat.card_Icc] at hlaterCard
  have hrankSub : Fintype.card T.Edge - physicalRank T e =
      (laterPhysicalWeightSet T e).card := by omega
  rw [hrankSub]
  omega

/-- Equality in the punctured cut cap holds exactly when every allowed rank
in the punctured tail is used by the crossing block. -/
theorem physicalRank_punctured_cut_cap_eq_iff
    {T : PosIntTree n} (hL : IsLeech T) (e : T.Edge) :
    T.weight e + T.cutSize e * (n - T.cutSize e) +
        (Fintype.card T.Edge - physicalRank T e) =
          targetN n + 1 ↔
      crossDistanceSpectrum T e = puncturedTail T e := by
  have hsubset := crossDistanceSpectrum_subset_puncturedTail hL e
  have hcross := crossDistanceSpectrum_card hL e
  have htail := puncturedTail_card hL e
  have hrank := physicalRank_add_later_card hL e
  have hw := (Finset.mem_Icc.mp (t1_edge_weight_mem_target hL e)).2
  have hlaterCard := Finset.card_le_card
    (laterPhysicalWeightSet_subset_targetTail hL e)
  simp only [Nat.card_Icc] at hlaterCard
  have hrankSub : Fintype.card T.Edge - physicalRank T e =
      (laterPhysicalWeightSet T e).card := by omega
  rw [hrankSub]
  constructor
  · intro heq
    apply LeechTrees.saturatedFiniteBlock hsubset
    omega
  · intro hsets
    have hcards := congrArg Finset.card hsets
    omega

/-! ## Parity-channel puncturing -/

/-- Physical weights in parity channel `p`. -/
def physicalParityWeightSet (p : ℕ) : Finset ℕ :=
  (physicalWeightSet T).filter fun w => w % 2 = p

/-- Later physical weights in parity channel `p`. -/
def laterPhysicalParityWeightSet (e : T.Edge) (p : ℕ) : Finset ℕ :=
  (laterPhysicalWeightSet T e).filter fun w => w % 2 = p

/-- Exact rank-aware allowed channel in `[w_e,N]`. -/
def exactParityTail (e : T.Edge) (p : ℕ) : Finset ℕ :=
  parityTail (targetN n) (T.weight e) p \
    laterPhysicalParityWeightSet T e p

/-- Coarse channel obtained from the full target parity class after deleting
every other physical weight in that channel. -/
def coarseParityTarget (e : T.Edge) (p : ℕ) : Finset ℕ :=
  targetParityBlock n p \
    (physicalParityWeightSet T p).erase (T.weight e)

/-- The exact unused-rank gap responsible for the coarse-equality caveat. -/
def unusedEarlierParityRanks (e : T.Edge) (p : ℕ) : Finset ℕ :=
  coarseParityTarget T e p \ exactParityTail T e p

theorem crossParityBlock_subset_exactParityTail
    {T : PosIntTree n} (hL : IsLeech T) (e : T.Edge) (p : ℕ) :
    crossParityBlock T e p ⊆ exactParityTail T e p := by
  intro k hk
  rw [exactParityTail, Finset.mem_sdiff]
  refine ⟨crossParityBlock_subset_tail T hL e p hk, ?_⟩
  intro hklater
  have hkC : k ∈ crossDistanceSpectrum T e := by
    rcases Finset.mem_image.mp hk with ⟨x, hx, rfl⟩
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  have hklater' : k ∈ laterPhysicalWeightSet T e :=
    (Finset.mem_filter.mp hklater).1
  exact (Finset.mem_sdiff.mp
    (crossDistanceSpectrum_subset_puncturedTail hL e hkC)).2 hklater'

theorem crossParityBlock_subset_coarseParityTarget
    {T : PosIntTree n} (hL : IsLeech T) (e : T.Edge) (p : ℕ) :
    crossParityBlock T e p ⊆ coarseParityTarget T e p := by
  intro k hk
  rw [coarseParityTarget, Finset.mem_sdiff]
  rcases Finset.mem_image.mp hk with ⟨x, hx, hxk⟩
  have htarget := hL.pairDist_mem (T.crossVertexPair e x)
  have hdist : T.pairDist (T.crossVertexPair e x) = k := by
    rw [T.pairDist_crossVertexPair e, hxk]
  have hpar : k % 2 = p := by
    rw [← hxk]
    exact (Finset.mem_filter.mp hx).2
  refine ⟨Finset.mem_filter.mpr ⟨by simpa [hdist] using htarget, hpar⟩, ?_⟩
  intro hkerase
  have hkphys : k ∈ physicalWeightSet T :=
    (Finset.mem_filter.mp (Finset.mem_of_mem_erase hkerase)).1
  have hkC : k ∈ crossDistanceSpectrum T e :=
    Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hxk⟩
  have hown : k = T.weight e := by
    have : k ∈ crossDistanceSpectrum T e ∩ physicalWeightSet T :=
      Finset.mem_inter.mpr ⟨hkC, hkphys⟩
    rw [crossDistanceSpectrum_inter_physicalWeightSet hL e,
      Finset.mem_singleton] at this
    exact this
  exact (Finset.ne_of_mem_erase hkerase) hown

theorem exactParityTail_subset_coarseParityTarget
    {T : PosIntTree n} (hL : IsLeech T) (e : T.Edge) (p : ℕ) :
    exactParityTail T e p ⊆ coarseParityTarget T e p := by
  intro k hk
  rw [exactParityTail, Finset.mem_sdiff] at hk
  rw [coarseParityTarget, Finset.mem_sdiff]
  have htail := Finset.mem_filter.mp hk.1
  have hwLower : 1 ≤ T.weight e :=
    (Finset.mem_Icc.mp (t1_edge_weight_mem_target hL e)).1
  have hkTarget : k ∈ Finset.Icc 1 (targetN n) := by
    refine Finset.mem_Icc.mpr ⟨?_, (Finset.mem_Icc.mp htail.1).2⟩
    exact hwLower.trans (Finset.mem_Icc.mp htail.1).1
  refine ⟨Finset.mem_filter.mpr ⟨hkTarget, htail.2⟩, ?_⟩
  intro hkerase
  have hkparity := Finset.mem_of_mem_erase hkerase
  have hkphys : k ∈ physicalWeightSet T :=
    (Finset.mem_filter.mp hkparity).1
  rcases Finset.mem_image.mp hkphys with ⟨f, -, hf⟩
  have hkne : k ≠ T.weight e := Finset.ne_of_mem_erase hkerase
  have hle : T.weight e ≤ k := (Finset.mem_Icc.mp htail.1).1
  have hlt : T.weight e < T.weight f := by
    rw [hf]
    exact lt_of_le_of_ne hle (Ne.symm hkne)
  apply hk.2
  rw [laterPhysicalParityWeightSet, Finset.mem_filter]
  exact ⟨Finset.mem_image.mpr
    ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ f, hlt⟩, hf⟩,
      (Finset.mem_filter.mp hkparity).2⟩

theorem exactParityTail_card
    {T : PosIntTree n} (hL : IsLeech T) (e : T.Edge) (p : ℕ) :
    (exactParityTail T e p).card =
      (parityTail (targetN n) (T.weight e) p).card -
        (laterPhysicalParityWeightSet T e p).card := by
  rw [exactParityTail, Finset.card_sdiff_of_subset]
  intro k hk
  have hk' := Finset.mem_filter.mp hk
  have htail := laterPhysicalWeightSet_subset_targetTail hL e hk'.1
  exact Finset.mem_filter.mpr ⟨htail, hk'.2⟩

/-- The rank-aware parity inequalities (odd when `p=1`, even when `p=0`). -/
theorem parityChannel_rankAware_cap
    {T : PosIntTree n} (hL : IsLeech T) (e : T.Edge) (p : ℕ) :
    (crossParityBlock T e p).card ≤
      (parityTail (targetN n) (T.weight e) p).card -
        (laterPhysicalParityWeightSet T e p).card := by
  rw [← exactParityTail_card hL e p]
  exact Finset.card_le_card (crossParityBlock_subset_exactParityTail hL e p)

/-- Exact-channel equality is exactly exhaustion of the punctured channel. -/
theorem parityChannel_rankAware_eq_iff_exhausted
    {T : PosIntTree n} (hL : IsLeech T) (e : T.Edge) (p : ℕ) :
    (crossParityBlock T e p).card = (exactParityTail T e p).card ↔
      crossParityBlock T e p = exactParityTail T e p := by
  constructor
  · intro hcard
    exact LeechTrees.saturatedFiniteBlock
      (crossParityBlock_subset_exactParityTail hL e p) hcard
  · intro hset
    exact congrArg Finset.card hset

/-- The coarse parity inequalities in exact set-cardinality form.  The right
side is `O-r+1_{w odd}` for `p=1`, and `E-(m-r)+1_{w even}` for `p=0`. -/
theorem parityChannel_coarse_cap
    {T : PosIntTree n} (hL : IsLeech T) (e : T.Edge) (p : ℕ) :
    (crossParityBlock T e p).card ≤ (coarseParityTarget T e p).card :=
  Finset.card_le_card (crossParityBlock_subset_coarseParityTarget hL e p)

/-- Corrected coarse equality: the crossing block must exhaust the exact
punctured tail *and* no unused allowed rank of that parity may lie below the
physical rank. -/
theorem parityChannel_coarse_eq_iff_exact_and_no_earlier_gap
    {T : PosIntTree n} (hL : IsLeech T) (e : T.Edge) (p : ℕ) :
    (crossParityBlock T e p).card = (coarseParityTarget T e p).card ↔
      crossParityBlock T e p = exactParityTail T e p ∧
        unusedEarlierParityRanks T e p = ∅ := by
  have hCE := crossParityBlock_subset_exactParityTail hL e p
  have hEK := exactParityTail_subset_coarseParityTarget hL e p
  have hgap : unusedEarlierParityRanks T e p = ∅ ↔
      exactParityTail T e p = coarseParityTarget T e p := by
    rw [unusedEarlierParityRanks, Finset.sdiff_eq_empty_iff_subset]
    constructor
    · intro hKE
      exact Finset.Subset.antisymm hEK hKE
    · intro hEq
      simp [hEq]
  constructor
  · intro hcard
    have hCEcard : (crossParityBlock T e p).card =
        (exactParityTail T e p).card := by
      have h₁ := Finset.card_le_card hCE
      have h₂ := Finset.card_le_card hEK
      omega
    have hEKcard : (exactParityTail T e p).card =
        (coarseParityTarget T e p).card := by omega
    refine ⟨LeechTrees.saturatedFiniteBlock hCE hCEcard, ?_⟩
    apply hgap.mpr
    exact LeechTrees.saturatedFiniteBlock hEK hEKcard
  · rintro ⟨hCEeq, hgapEmpty⟩
    have hEKeq := hgap.mp hgapEmpty
    rw [hCEeq, hEKeq]

/-! ## G003: the signed first moment and centered order-18 consequences -/

private theorem normalized_left_sum
    (T : PosIntTree 18) (r : Fin 18) (e : T.Edge) :
    (∑ u : T.LeftVertex e, normalizedParitySign18 T r u.1) =
      leftImbalance18 T r e := by
  have h := signedMass_eq_count_sub
    (fun u : T.LeftVertex e => normalizedParitySign18 T r u.1)
    (Finset.univ : Finset (T.LeftVertex e))
    (fun u _ => normalizedParitySign18_pm T r u.1)
  calc
    (∑ u : T.LeftVertex e, normalizedParitySign18 T r u.1) =
        signedMass (fun u : T.LeftVertex e =>
          normalizedParitySign18 T r u.1) Finset.univ := by
      simp [signedMass]
    _ = ((leftPositiveDomain18 T r e).card : ℤ) -
          (leftNegativeDomain18 T r e).card := h
    _ = leftImbalance18 T r e := by
      rw [leftPositiveDomain18_card, leftNegativeDomain18_card]
      rfl

private theorem normalized_right_sum
    {T : PosIntTree 18} (hL : IsLeech T) (r : Fin 18) (e : T.Edge) :
    (∑ v : T.RightVertex e, normalizedParitySign18 T r v.1) =
      4 - leftImbalance18 T r e := by
  have h := signedMass_eq_count_sub
    (fun v : T.RightVertex e => normalizedParitySign18 T r v.1)
    (Finset.univ : Finset (T.RightVertex e))
    (fun v _ => normalizedParitySign18_pm T r v.1)
  calc
    (∑ v : T.RightVertex e, normalizedParitySign18 T r v.1) =
        signedMass (fun v : T.RightVertex e =>
          normalizedParitySign18 T r v.1) Finset.univ := by
      simp [signedMass]
    _ = ((rightPositiveDomain18 T r e).card : ℤ) -
          (rightNegativeDomain18 T r e).card := h
    _ = 4 - leftImbalance18 T r e := by
      rw [rightPositiveDomain18_card, rightNegativeDomain18_card]
      have hg := cutGlobalSignEquation18 hL r e
      unfold leftImbalance18 at hg ⊢
      omega

private theorem signed_incidence_sum_eq_cut_product
    {T : PosIntTree 18} (hL : IsLeech T) (r : Fin 18) (e : T.Edge) :
    (∑ q : VertexPair 18,
      normalizedParitySign18 T r q.left *
        normalizedParitySign18 T r q.right *
          (T.pathIncidence q e : ℤ)) =
      leftImbalance18 T r e * (4 - leftImbalance18 T r e) := by
  classical
  let sign := normalizedParitySign18 T r
  calc
    (∑ q : VertexPair 18,
      sign q.left * sign q.right * (T.pathIncidence q e : ℤ)) =
        ∑ q : T.CrossingPair e,
          sign q.1.left * sign q.1.right := by
      simp only [PosIntTree.pathIncidence, Nat.cast_ite, Nat.cast_one,
        Nat.cast_zero, mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (fun _ => by simp) _
    _ = ∑ x : T.LeftVertex e × T.RightVertex e,
          sign x.1.1 * sign x.2.1 := by
      apply Fintype.sum_equiv (T.crossingPairEquiv e).symm
      intro q
      let x := (T.crossingPairEquiv e).symm q
      have hqx : (T.crossingPairEquiv e x).1 = q.1 := by
        exact congrArg Subtype.val ((T.crossingPairEquiv e).apply_symm_apply q)
      have hpair : T.crossVertexPair e x = q.1 := by
        rw [← T.crossingPairEquiv_apply_val e x]
        exact hqx
      calc
        sign q.1.left * sign q.1.right = paritySign (T.pairDist q.1) := by
          simpa [sign, PosIntTree.pairDist] using
            normalizedParitySign18_pair T r q.1.left q.1.right
        _ = paritySign (T.rootedCrossSum e x) := by
          rw [← T.pairDist_crossVertexPair e x, hpair]
        _ = sign x.1.1 * sign x.2.1 := by
          simpa [sign] using (normalizedCrossSign18 T r e x).symm
    _ = (∑ u : T.LeftVertex e, sign u.1) *
          (∑ v : T.RightVertex e, sign v.1) := by
      rw [Fintype.sum_prod_type]
      exact (Fintype.sum_mul_sum
        (fun u : T.LeftVertex e => sign u.1)
        (fun v : T.RightVertex e => sign v.1)).symm
    _ = leftImbalance18 T r e * (4 - leftImbalance18 T r e) := by
      rw [normalized_left_sum, normalized_right_sum hL]

private theorem paritySign_two_mul (m : ℕ) :
    paritySign (2 * m) = 1 := by
  unfold paritySign
  rw [pow_mul]
  norm_num

private theorem paritySign_two_mul_add_one (m : ℕ) :
    paritySign (2 * m + 1) = -1 := by
  unfold paritySign
  rw [pow_add, pow_mul]
  norm_num

private theorem alternating_pair (m : ℕ) :
    paritySign (2 * m + 1) * ((2 * m + 1 : ℕ) : ℤ) +
      paritySign (2 * m + 2) * ((2 * m + 2 : ℕ) : ℤ) = 1 := by
  rw [paritySign_two_mul_add_one,
    show 2 * m + 2 = 2 * (m + 1) by omega,
    paritySign_two_mul]
  push_cast
  ring

private theorem alternating_sum_range_pairs (m : ℕ) :
    (∑ d ∈ Finset.range (2 * m + 1), paritySign d * (d : ℤ)) = (m : ℤ) := by
  induction m with
  | zero => norm_num [paritySign]
  | succ m ih =>
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, ih,
        show (2 * m + 1) + 1 = 2 * m + 2 by omega,
        add_assoc, alternating_pair]
      norm_num

theorem order18_alternating_first_target_moment :
    (∑ d ∈ Finset.Icc 1 153, paritySign d * (d : ℤ)) = -77 := by
  have hsubset : Finset.Icc 1 153 ⊆ Finset.range 154 := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    simp
    omega
  calc
    (∑ d ∈ Finset.Icc 1 153, paritySign d * (d : ℤ)) =
        ∑ d ∈ Finset.range 154, paritySign d * (d : ℤ) := by
      apply Finset.sum_subset hsubset
      intro d hdRange hdNot
      rw [Finset.mem_Icc] at hdNot
      simp at hdRange
      push_neg at hdNot
      have : d = 0 := by omega
      subst d
      norm_num [paritySign]
    _ = -77 := by
      rw [show 154 = (2 * 76 + 1) + 1 by norm_num,
        Finset.sum_range_succ, alternating_sum_range_pairs,
        paritySign_two_mul_add_one]
      norm_num

private theorem normalized_signed_pair_first_moment
    {T : PosIntTree 18} (hL : IsLeech T) (r : Fin 18) :
    (∑ q : VertexPair 18,
      normalizedParitySign18 T r q.left *
        normalizedParitySign18 T r q.right * (T.pairDist q : ℤ)) =
      -77 := by
  calc
    (∑ q : VertexPair 18,
      normalizedParitySign18 T r q.left *
        normalizedParitySign18 T r q.right * (T.pairDist q : ℤ)) =
        ∑ q : VertexPair 18,
          paritySign (T.pairDist q) * (T.pairDist q : ℤ) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [show normalizedParitySign18 T r q.left *
          normalizedParitySign18 T r q.right = paritySign (T.pairDist q) by
        simpa [PosIntTree.pairDist] using
          normalizedParitySign18_pair T r q.left q.right]
    _ = ∑ d : {d : ℕ // d ∈ Finset.Icc 1 (targetN 18)},
          paritySign d.1 * (d.1 : ℤ) := by
      apply Fintype.sum_equiv hL.spectrumEquiv
      intro q
      rfl
    _ = ∑ d ∈ Finset.Icc 1 153, paritySign d * (d : ℤ) := by
      norm_num [targetN]
      symm
      exact Finset.sum_subtype _ (fun _ => Iff.rfl) _
    _ = -77 := order18_alternating_first_target_moment

/-- The exact order-18 graph-level signed first moment. -/
theorem order18_signed_first_moment
    {T : PosIntTree 18} (hL : IsLeech T) (r : Fin 18) :
    (∑ e : T.Edge, (T.weight e : ℤ) * leftImbalance18 T r e *
      (4 - leftImbalance18 T r e)) = -77 := by
  have hpair := normalized_signed_pair_first_moment hL r
  calc
    (∑ e : T.Edge, (T.weight e : ℤ) * leftImbalance18 T r e *
      (4 - leftImbalance18 T r e)) =
        ∑ e : T.Edge, (T.weight e : ℤ) *
          (∑ q : VertexPair 18,
            normalizedParitySign18 T r q.left *
              normalizedParitySign18 T r q.right *
                (T.pathIncidence q e : ℤ)) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [signed_incidence_sum_eq_cut_product hL r e]
      ring
    _ = ∑ q : VertexPair 18,
          normalizedParitySign18 T r q.left *
            normalizedParitySign18 T r q.right * (T.pairDist q : ℤ) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      have hrow := congrArg (fun z : ℕ => (z : ℤ))
        (T.pathIncidence_row q)
      simp only [LeechTrees.weightedRow, Nat.cast_sum, Nat.cast_mul] at hrow
      calc
        (∑ e : T.Edge, (T.weight e : ℤ) *
            (normalizedParitySign18 T r q.left *
              normalizedParitySign18 T r q.right *
                (T.pathIncidence q e : ℤ))) =
            (normalizedParitySign18 T r q.left *
              normalizedParitySign18 T r q.right) *
                ∑ e : T.Edge, (T.pathIncidence q e : ℤ) *
                  (T.weight e : ℤ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e _
          ring
        _ = normalizedParitySign18 T r q.left *
              normalizedParitySign18 T r q.right *
                (T.pairDist q : ℤ) := by
          rw [hrow]
    _ = -77 := hpair

/-- Centered square form of the signed first moment. -/
theorem order18_centered_signed_first_moment
    {T : PosIntTree 18} (hL : IsLeech T) (r : Fin 18) :
    (∑ e : T.Edge, (T.weight e : ℤ) *
      (leftImbalance18 T r e - 2) ^ 2) =
        4 * (∑ e : T.Edge, (T.weight e : ℤ)) + 77 := by
  have h := order18_signed_first_moment hL r
  have hid :
      (∑ e : T.Edge, (T.weight e : ℤ) * leftImbalance18 T r e *
        (4 - leftImbalance18 T r e)) =
      4 * (∑ e : T.Edge, (T.weight e : ℤ)) -
        ∑ e : T.Edge, (T.weight e : ℤ) *
          (leftImbalance18 T r e - 2) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hid] at h
  linarith

theorem order18_sign_reversed_first_moment
    {T : PosIntTree 18} (hL : IsLeech T) (r : Fin 18) :
    (∑ e : T.Edge, (T.weight e : ℤ) * leftImbalance18 T r e *
      (leftImbalance18 T r e - 4)) = 77 := by
  have h := order18_signed_first_moment hL r
  calc
    (∑ e : T.Edge, (T.weight e : ℤ) * leftImbalance18 T r e *
      (leftImbalance18 T r e - 4)) =
        -(∑ e : T.Edge, (T.weight e : ℤ) * leftImbalance18 T r e *
          (4 - leftImbalance18 T r e)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = 77 := by rw [h]; norm_num

/-- Positivity forces at least one cut imbalance outside `[0,4]`. -/
theorem order18_exists_imbalance_outside_zero_four
    {T : PosIntTree 18} (hL : IsLeech T) (r : Fin 18) :
    ∃ e : T.Edge,
      leftImbalance18 T r e < 0 ∨ 4 < leftImbalance18 T r e := by
  by_contra hnone
  push_neg at hnone
  have hnonneg : 0 ≤
      (∑ e : T.Edge, (T.weight e : ℤ) * leftImbalance18 T r e *
        (4 - leftImbalance18 T r e)) := by
    apply Finset.sum_nonneg
    intro e _
    have hw : 0 ≤ (T.weight e : ℤ) := by positivity
    have hx₀ : 0 ≤ leftImbalance18 T r e := hnone e |>.1
    have hx₄ : 0 ≤ 4 - leftImbalance18 T r e := by
      have := hnone e |>.2
      omega
    positivity
  rw [order18_signed_first_moment hL r] at hnonneg
  omega

/-- Side complementation `x ↦ 4-x` preserves the outside-range obstruction. -/
theorem outside_zero_four_complement_iff (x : ℤ) :
    (4 - x < 0 ∨ 4 < 4 - x) ↔ (x < 0 ∨ 4 < x) := by
  omega

end

end LeechTrees.RankParity
