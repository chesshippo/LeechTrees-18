import LeechTrees.Foundations

/-!
# The exact every-edge hole set

This module works over the indexed `IsLeech` model from the frozen
`LeechTrees.Foundations` module.  For an actual physical edge, it defines the
missing rooted cross offsets in the exact interval `0, ..., N - w`, proves
that they are precisely a positive hole set, and identifies their translates
by `w` with the disjoint union of the high internal spectra of the two
deletion components.

All results are one-way necessary consequences of `IsLeech`.  In particular,
no polynomial, Finset, or moment condition below is asserted to realize a
rooted component or a Leech tree.
-/

open scoped BigOperators

namespace LeechTrees.Foundation

variable {n : ℕ}

namespace PosIntTree

variable (T : PosIntTree n)

private theorem sum_prod_left_nat
    {A B : Type*} [Fintype A] [Fintype B] (f : A → ℕ) :
    (∑ x : A × B, f x.1) = Fintype.card B * ∑ a : A, f a := by
  classical
  rw [Fintype.sum_prod_type]
  simp [← Finset.mul_sum]

private theorem sum_prod_right_nat
    {A B : Type*} [Fintype A] [Fintype B] (g : B → ℕ) :
    (∑ x : A × B, g x.2) = Fintype.card A * ∑ b : B, g b := by
  classical
  rw [Fintype.sum_prod_type]
  simp

private theorem sum_prod_mul_nat
    {A B : Type*} [Fintype A] [Fintype B] (f : A → ℕ) (g : B → ℕ) :
    (∑ x : A × B, f x.1 * g x.2) =
      (∑ a : A, f a) * ∑ b : B, g b := by
  rw [Fintype.sum_prod_type]
  exact (Fintype.sum_mul_sum f g).symm

private theorem sum_prod_mul_int
    {A B : Type*} [Fintype A] [Fintype B] (f : A → ℤ) (g : B → ℤ) :
    (∑ x : A × B, f x.1 * g x.2) =
      (∑ a : A, f a) * ∑ b : B, g b := by
  rw [Fintype.sum_prod_type]
  exact (Fintype.sum_mul_sum f g).symm

/-- The offset of a cross-cut distance after removing the physical edge
weight.  Its domain remains the indexed Cartesian product of the two actual
deletion sides. -/
noncomputable def edgeOffset (e : T.Edge)
    (x : T.LeftVertex e × T.RightVertex e) : ℕ :=
  T.leftDepth e x.1 + T.rightDepth e x.2

/-- The full interval of possible offsets for an edge of weight `w`. -/
noncomputable def edgeOffsetInterval (e : T.Edge) : Finset ℕ :=
  Finset.Icc 0 (targetN n - T.weight e)

/-- The value set of the indexed rooted cross offsets.  Injectivity is proved
below from the indexed Leech spectrum; the definition itself does not erase
that proof obligation. -/
noncomputable def crossOffsetSpectrum (e : T.Edge) : Finset ℕ :=
  Finset.univ.image (T.edgeOffset e)

/-- The exact edge-hole set in offset coordinates. -/
noncomputable def edgeHoleSet (e : T.Edge) : Finset ℕ :=
  T.edgeOffsetInterval e \ T.crossOffsetSpectrum e

/-- An indexed vertex pair internal to the endpoint-oriented left deletion
component. -/
def LeftInternalPair (e : T.Edge) (p : VertexPair n) : Prop :=
  T.LeftCut e p.left ∧ T.LeftCut e p.right

/-- An indexed vertex pair internal to the endpoint-oriented right deletion
component. -/
def RightInternalPair (e : T.Edge) (p : VertexPair n) : Prop :=
  T.RightCut e p.left ∧ T.RightCut e p.right

/-- Distances at least `w` of indexed pairs internal to the left side. -/
noncomputable def leftHighInternalSpectrum (e : T.Edge) : Finset ℕ :=
  by
    classical
    exact (Finset.univ.filter fun p : VertexPair n =>
      T.LeftInternalPair e p ∧ T.weight e ≤ T.pairDist p).image T.pairDist

/-- Distances at least `w` of indexed pairs internal to the right side. -/
noncomputable def rightHighInternalSpectrum (e : T.Edge) : Finset ℕ :=
  by
    classical
    exact (Finset.univ.filter fun p : VertexPair n =>
      T.RightInternalPair e p ∧ T.weight e ≤ T.pairDist p).image T.pairDist

/-- The shift by the actual physical edge weight of every exact hole offset. -/
noncomputable def shiftedEdgeHoleSet (e : T.Edge) : Finset ℕ :=
  (T.edgeHoleSet e).image fun h => T.weight e + h

/-- Natural power sum of a finite set.  Degree zero uses Lean's convention
`h ^ 0 = 1`, so it is the cardinality. -/
def finsetMoment (S : Finset ℕ) (k : ℕ) : ℕ :=
  ∑ h ∈ S, h ^ k

/-- Indexed left-rooted depth moment. -/
noncomputable def leftDepthMoment (e : T.Edge) (k : ℕ) : ℕ :=
  ∑ u : T.LeftVertex e, (T.leftDepth e u) ^ k

/-- Indexed right-rooted depth moment. -/
noncomputable def rightDepthMoment (e : T.Edge) (k : ℕ) : ℕ :=
  ∑ v : T.RightVertex e, (T.rightDepth e v) ^ k

/-- The ordinary parity character times a natural power, valued in the
integers so subtraction and signs retain their literal meaning. -/
def signedPower (h k : ℕ) : ℤ :=
  (-1 : ℤ) ^ h * (h : ℤ) ^ k

/-- Alternating power sum of a finite set. -/
def alternatingFinsetMoment (S : Finset ℕ) (k : ℕ) : ℤ :=
  ∑ h ∈ S, signedPower h k

/-- Indexed alternating left-rooted depth moment. -/
noncomputable def leftAlternatingDepthMoment (e : T.Edge) (k : ℕ) : ℤ :=
  ∑ u : T.LeftVertex e, signedPower (T.leftDepth e u) k

/-- Indexed alternating right-rooted depth moment. -/
noncomputable def rightAlternatingDepthMoment (e : T.Edge) (k : ℕ) : ℤ :=
  ∑ v : T.RightVertex e, signedPower (T.rightDepth e v) k

theorem weight_add_edgeOffset (e : T.Edge)
    (x : T.LeftVertex e × T.RightVertex e) :
    T.weight e + T.edgeOffset e x = T.rootedCrossSum e x := by
  simp only [edgeOffset, Foundation.PosIntTree.rootedCrossSum]
  omega

theorem edgeOffset_injective (hL : IsLeech T) (e : T.Edge) :
    Function.Injective (T.edgeOffset e) := by
  intro x y hxy
  apply T.rootedCrossSum_injective hL e
  rw [← T.weight_add_edgeOffset e x, ← T.weight_add_edgeOffset e y, hxy]

theorem edge_weight_le_target (hL : IsLeech T) (e : T.Edge) :
    T.weight e ≤ targetN n := by
  exact (Finset.mem_Icc.mp (t1_edge_weight_mem_target hL e)).2

theorem edgeOffset_mem_interval (hL : IsLeech T) (e : T.Edge)
    (x : T.LeftVertex e × T.RightVertex e) :
    T.edgeOffset e x ∈ T.edgeOffsetInterval e := by
  rw [edgeOffsetInterval, Finset.mem_Icc]
  constructor
  · omega
  · have htail := (Finset.mem_Icc.mp
      (T.rootedCrossSum_mem_target_tail hL e x)).2
    rw [← T.weight_add_edgeOffset e x] at htail
    have hw := T.edge_weight_le_target hL e
    omega

theorem crossOffsetSpectrum_subset_interval (hL : IsLeech T) (e : T.Edge) :
    T.crossOffsetSpectrum e ⊆ T.edgeOffsetInterval e := by
  intro h hh
  rw [crossOffsetSpectrum, Finset.mem_image] at hh
  obtain ⟨x, -, rfl⟩ := hh
  exact T.edgeOffset_mem_interval hL e x

theorem zero_mem_crossOffsetSpectrum (e : T.Edge) :
    0 ∈ T.crossOffsetSpectrum e := by
  classical
  let x0 : T.LeftVertex e × T.RightVertex e :=
    (⟨T.edgeLeft e, T.edgeLeft_mem_LeftCut e⟩,
      ⟨T.edgeRight e, T.edgeRight_mem_RightCut e⟩)
  rw [crossOffsetSpectrum, Finset.mem_image]
  refine ⟨x0, Finset.mem_univ _, ?_⟩
  simp [x0, edgeOffset, Foundation.PosIntTree.leftDepth,
    Foundation.PosIntTree.rightDepth]

theorem edgeHoleSet_subset_positive_interval (_hL : IsLeech T) (e : T.Edge) :
    T.edgeHoleSet e ⊆ Finset.Icc 1 (targetN n - T.weight e) := by
  intro h hh
  rw [edgeHoleSet, Finset.mem_sdiff] at hh
  rw [Finset.mem_Icc]
  have hi := Finset.mem_Icc.mp hh.1
  constructor
  · have hz := T.zero_mem_crossOffsetSpectrum e
    by_contra hnot
    have : h = 0 := by omega
    exact hh.2 (this ▸ hz)
  · exact hi.2

theorem crossOffsetSpectrum_card (hL : IsLeech T) (e : T.Edge) :
    (T.crossOffsetSpectrum e).card =
      T.cutSize e * (n - T.cutSize e) := by
  classical
  calc
    (T.crossOffsetSpectrum e).card =
        Fintype.card (T.LeftVertex e × T.RightVertex e) := by
      exact Finset.card_image_of_injective _ (T.edgeOffset_injective hL e)
    _ = Fintype.card (T.LeftVertex e) * Fintype.card (T.RightVertex e) :=
      Fintype.card_prod _ _
    _ = T.cutSize e * (n - T.cutSize e) := by
      rw [T.rightVertex_card e]
      rfl

theorem edgeOffsetInterval_card (hL : IsLeech T) (e : T.Edge) :
    (T.edgeOffsetInterval e).card = targetN n - T.weight e + 1 := by
  have hw := T.edge_weight_le_target hL e
  simp [edgeOffsetInterval, Nat.card_Icc]

/-- Exact hole count `g_e = L + 1 - s t`, with the side product kept as the
cardinality of the indexed Cartesian cross block. -/
theorem edgeHoleSet_card (hL : IsLeech T) (e : T.Edge) :
    (T.edgeHoleSet e).card =
      (targetN n - T.weight e + 1) -
        T.cutSize e * (n - T.cutSize e) := by
  classical
  rw [edgeHoleSet, Finset.card_sdiff_of_subset
    (T.crossOffsetSpectrum_subset_interval hL e)]
  rw [T.edgeOffsetInterval_card hL e, T.crossOffsetSpectrum_card hL e]

theorem not_crossing_iff_internal (e : T.Edge) (p : VertexPair n) :
    e.1 ∉ T.pathEdges p.left p.right ↔
      T.LeftInternalPair e p ∨ T.RightInternalPair e p := by
  rw [T.mem_pathEdges_iff_opposite_cuts e p.left p.right]
  unfold LeftInternalPair RightInternalPair
  constructor
  · intro h
    rcases T.cut_cover e p.left with hl | hr <;>
      rcases T.cut_cover e p.right with hl' | hr'
    · exact Or.inl ⟨hl, hl'⟩
    · exact (h (Or.inl ⟨hl, hr'⟩)).elim
    · exact (h (Or.inr ⟨hr, hl'⟩)).elim
    · exact Or.inr ⟨hr, hr'⟩
  · rintro (hleft | hright) hcross
    · rcases hcross with hcross | hcross
      · exact T.LeftCut_disjoint_RightCut e p.right ⟨hleft.2, hcross.2⟩
      · exact T.LeftCut_disjoint_RightCut e p.left ⟨hleft.1, hcross.1⟩
    · rcases hcross with hcross | hcross
      · exact T.LeftCut_disjoint_RightCut e p.left ⟨hcross.1, hright.1⟩
      · exact T.LeftCut_disjoint_RightCut e p.right ⟨hcross.2, hright.2⟩

theorem exists_cross_index_of_crossing (e : T.Edge) (p : VertexPair n)
    (hp : e.1 ∈ T.pathEdges p.left p.right) :
    ∃ x : T.LeftVertex e × T.RightVertex e,
      T.crossVertexPair e x = p := by
  let q : T.CrossingPair e := ⟨p, hp⟩
  let x := (T.crossingPairEquiv e).symm q
  refine ⟨x, ?_⟩
  rw [← T.crossingPairEquiv_apply_val e x]
  exact congrArg Subtype.val ((T.crossingPairEquiv e).apply_symm_apply q)

/-- The two high internal spectra are disjoint because they retain their
indexed full-tree pair witnesses and the global pair-distance map is
injective. -/
theorem highInternalSpectra_disjoint (hL : IsLeech T) (e : T.Edge) :
    Disjoint (T.leftHighInternalSpectrum e)
      (T.rightHighInternalSpectrum e) := by
  classical
  rw [Finset.disjoint_left]
  intro k hkL hkR
  rw [leftHighInternalSpectrum, Finset.mem_image] at hkL
  rw [rightHighInternalSpectrum, Finset.mem_image] at hkR
  obtain ⟨p, hp, rfl⟩ := hkL
  obtain ⟨q, hq, hpq⟩ := hkR
  have hp' := (Finset.mem_filter.mp hp).2.1
  have hq' := (Finset.mem_filter.mp hq).2.1
  have heq : p = q := hL.pairDist_injective hpq.symm
  subst q
  exact T.LeftCut_disjoint_RightCut e p.left ⟨hp'.1, hq'.1⟩

/-- The exact translated hole set is the disjoint union of the high internal
distance spectra of the two deletion sides. -/
theorem shiftedEdgeHoleSet_eq_highInternalSpectra
    (hL : IsLeech T) (e : T.Edge) :
    T.shiftedEdgeHoleSet e =
      T.leftHighInternalSpectrum e ∪ T.rightHighInternalSpectrum e := by
  classical
  ext k
  constructor
  · intro hk
    rw [shiftedEdgeHoleSet, Finset.mem_image] at hk
    obtain ⟨h, hh, rfl⟩ := hk
    have hhpos := T.edgeHoleSet_subset_positive_interval hL e hh
    have hhI := Finset.mem_Icc.mp hhpos
    have hw := T.edge_weight_le_target hL e
    have htarget : T.weight e + h ∈ Finset.Icc 1 (targetN n) := by
      rw [Finset.mem_Icc]
      omega
    obtain ⟨p, hp, -⟩ := hL.target_existsUnique (T.weight e + h) htarget
    have hpdist : T.pairDist p = T.weight e + h := hp
    have hnotcross : e.1 ∉ T.pathEdges p.left p.right := by
      intro hcross
      obtain ⟨x, hxp⟩ := T.exists_cross_index_of_crossing e p hcross
      have hoff : T.edgeOffset e x = h := by
        have hroot : T.rootedCrossSum e x = T.weight e + h := by
          rw [← T.pairDist_crossVertexPair e x, hxp, hpdist]
        rw [← T.weight_add_edgeOffset e x] at hroot
        omega
      have hmem : h ∈ T.crossOffsetSpectrum e := by
        rw [crossOffsetSpectrum, Finset.mem_image]
        exact ⟨x, Finset.mem_univ x, hoff⟩
      exact (Finset.mem_sdiff.mp hh).2 hmem
    rcases (T.not_crossing_iff_internal e p).1 hnotcross with hpL | hpR
    · rw [Finset.mem_union, leftHighInternalSpectrum, Finset.mem_image]
      left
      refine ⟨p, ?_, hpdist⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ p, hpL, by omega⟩
    · rw [Finset.mem_union, rightHighInternalSpectrum, Finset.mem_image]
      right
      refine ⟨p, ?_, hpdist⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ p, hpR, by omega⟩
  · intro hk
    rw [Finset.mem_union] at hk
    rcases hk with hkL | hkR
    · rw [leftHighInternalSpectrum, Finset.mem_image] at hkL
      obtain ⟨p, hp, rfl⟩ := hkL
      have hpf := (Finset.mem_filter.mp hp).2
      have htarget := hL.pairDist_mem p
      have hwle : T.weight e ≤ T.pairDist p := hpf.2
      have hsub : T.weight e + (T.pairDist p - T.weight e) = T.pairDist p := by
        omega
      rw [shiftedEdgeHoleSet, Finset.mem_image]
      refine ⟨T.pairDist p - T.weight e, ?_, hsub⟩
      rw [edgeHoleSet, Finset.mem_sdiff]
      constructor
      · rw [edgeOffsetInterval, Finset.mem_Icc]
        exact ⟨Nat.zero_le _, Nat.sub_le_sub_right
          (Finset.mem_Icc.mp htarget).2 (T.weight e)⟩
      · intro hcrossOffset
        rw [crossOffsetSpectrum, Finset.mem_image] at hcrossOffset
        obtain ⟨x, -, hx⟩ := hcrossOffset
        have hdist : T.pairDist (T.crossVertexPair e x) = T.pairDist p := by
          rw [T.pairDist_crossVertexPair e,
            ← T.weight_add_edgeOffset e x, hx, hsub]
        have heq := hL.pairDist_injective hdist
        have hcross := T.crossVertexPair_crosses e x
        rw [heq] at hcross
        exact (T.not_crossing_iff_internal e p).2 (Or.inl hpf.1) hcross
    · rw [rightHighInternalSpectrum, Finset.mem_image] at hkR
      obtain ⟨p, hp, rfl⟩ := hkR
      have hpf := (Finset.mem_filter.mp hp).2
      have htarget := hL.pairDist_mem p
      have hwle : T.weight e ≤ T.pairDist p := hpf.2
      have hsub : T.weight e + (T.pairDist p - T.weight e) = T.pairDist p := by
        omega
      rw [shiftedEdgeHoleSet, Finset.mem_image]
      refine ⟨T.pairDist p - T.weight e, ?_, hsub⟩
      rw [edgeHoleSet, Finset.mem_sdiff]
      constructor
      · rw [edgeOffsetInterval, Finset.mem_Icc]
        exact ⟨Nat.zero_le _, Nat.sub_le_sub_right
          (Finset.mem_Icc.mp htarget).2 (T.weight e)⟩
      · intro hcrossOffset
        rw [crossOffsetSpectrum, Finset.mem_image] at hcrossOffset
        obtain ⟨x, -, hx⟩ := hcrossOffset
        have hdist : T.pairDist (T.crossVertexPair e x) = T.pairDist p := by
          rw [T.pairDist_crossVertexPair e,
            ← T.weight_add_edgeOffset e x, hx, hsub]
        have heq := hL.pairDist_injective hdist
        have hcross := T.crossVertexPair_crosses e x
        rw [heq] at hcross
        exact (T.not_crossing_iff_internal e p).2 (Or.inr hpf.1) hcross

/-- Complement partition underlying every ordinary hole-moment identity. -/
theorem edgeHoleSet_union_crossOffsetSpectrum (hL : IsLeech T) (e : T.Edge) :
    T.edgeHoleSet e ∪ T.crossOffsetSpectrum e = T.edgeOffsetInterval e := by
  classical
  rw [edgeHoleSet, Finset.sdiff_union_of_subset
    (T.crossOffsetSpectrum_subset_interval hL e)]

theorem edgeHoleSet_disjoint_crossOffsetSpectrum (e : T.Edge) :
    Disjoint (T.edgeHoleSet e) (T.crossOffsetSpectrum e) := by
  classical
  exact Finset.sdiff_disjoint

/-- Generic natural-valued moment partition. -/
theorem edgeHoleMoment_add_crossOffsetMoment
    (hL : IsLeech T) (e : T.Edge) (k : ℕ) :
    finsetMoment (T.edgeHoleSet e) k +
        finsetMoment (T.crossOffsetSpectrum e) k =
      finsetMoment (T.edgeOffsetInterval e) k := by
  classical
  unfold finsetMoment
  rw [← Finset.sum_union (T.edgeHoleSet_disjoint_crossOffsetSpectrum e),
    T.edgeHoleSet_union_crossOffsetSpectrum hL e]

theorem crossOffsetMoment_eq_indexed (hL : IsLeech T) (e : T.Edge) (k : ℕ) :
    finsetMoment (T.crossOffsetSpectrum e) k =
      ∑ x : T.LeftVertex e × T.RightVertex e, (T.edgeOffset e x) ^ k := by
  classical
  rw [finsetMoment, crossOffsetSpectrum, Finset.sum_image]
  exact (T.edgeOffset_injective hL e).injOn

/-- Generic alternating complement identity.  This is the finite-set form of
evaluation at `-1` followed by any ordinary power moment. -/
theorem edgeHoleAlternatingMoment_add_crossOffsetMoment
    (hL : IsLeech T) (e : T.Edge) (k : ℕ) :
    alternatingFinsetMoment (T.edgeHoleSet e) k +
        alternatingFinsetMoment (T.crossOffsetSpectrum e) k =
      alternatingFinsetMoment (T.edgeOffsetInterval e) k := by
  classical
  unfold alternatingFinsetMoment
  rw [← Finset.sum_union (T.edgeHoleSet_disjoint_crossOffsetSpectrum e),
    T.edgeHoleSet_union_crossOffsetSpectrum hL e]

theorem crossOffsetAlternatingMoment_eq_indexed
    (hL : IsLeech T) (e : T.Edge) (k : ℕ) :
    alternatingFinsetMoment (T.crossOffsetSpectrum e) k =
      ∑ x : T.LeftVertex e × T.RightVertex e,
        signedPower (T.edgeOffset e x) k := by
  classical
  rw [alternatingFinsetMoment, crossOffsetSpectrum, Finset.sum_image]
  exact (T.edgeOffset_injective hL e).injOn

theorem edgeOffsetMoment_one_expansion (e : T.Edge) :
    (∑ x : T.LeftVertex e × T.RightVertex e, T.edgeOffset e x) =
      Fintype.card (T.RightVertex e) * T.leftDepthMoment e 1 +
      Fintype.card (T.LeftVertex e) * T.rightDepthMoment e 1 := by
  classical
  calc
    (∑ x : T.LeftVertex e × T.RightVertex e, T.edgeOffset e x) =
        (∑ x : T.LeftVertex e × T.RightVertex e, T.leftDepth e x.1) +
          ∑ x : T.LeftVertex e × T.RightVertex e, T.rightDepth e x.2 := by
      simp [edgeOffset, Finset.sum_add_distrib]
    _ = Fintype.card (T.RightVertex e) * T.leftDepthMoment e 1 +
        Fintype.card (T.LeftVertex e) * T.rightDepthMoment e 1 := by
      rw [sum_prod_left_nat, sum_prod_right_nat]
      simp [leftDepthMoment, rightDepthMoment]

theorem edgeOffsetMoment_two_expansion (e : T.Edge) :
    (∑ x : T.LeftVertex e × T.RightVertex e,
        (T.edgeOffset e x) ^ 2) =
      Fintype.card (T.RightVertex e) * T.leftDepthMoment e 2 +
      Fintype.card (T.LeftVertex e) * T.rightDepthMoment e 2 +
      2 * T.leftDepthMoment e 1 * T.rightDepthMoment e 1 := by
  classical
  have hpoint : ∀ x : T.LeftVertex e × T.RightVertex e,
      (T.edgeOffset e x) ^ 2 =
        (T.leftDepth e x.1) ^ 2 + (T.rightDepth e x.2) ^ 2 +
          2 * (T.leftDepth e x.1 * T.rightDepth e x.2) := by
    intro x
    simp only [edgeOffset]
    ring
  calc
    (∑ x : T.LeftVertex e × T.RightVertex e,
        (T.edgeOffset e x) ^ 2) =
        (∑ x : T.LeftVertex e × T.RightVertex e,
          (T.leftDepth e x.1) ^ 2) +
        (∑ x : T.LeftVertex e × T.RightVertex e,
          (T.rightDepth e x.2) ^ 2) +
        2 * (∑ x : T.LeftVertex e × T.RightVertex e,
          T.leftDepth e x.1 * T.rightDepth e x.2) := by
      simp_rw [hpoint, Finset.sum_add_distrib, Finset.mul_sum]
    _ = Fintype.card (T.RightVertex e) * T.leftDepthMoment e 2 +
        Fintype.card (T.LeftVertex e) * T.rightDepthMoment e 2 +
        2 * T.leftDepthMoment e 1 * T.rightDepthMoment e 1 := by
      rw [sum_prod_left_nat (B := T.RightVertex e)
          (fun u : T.LeftVertex e => (T.leftDepth e u) ^ 2),
        sum_prod_right_nat (A := T.LeftVertex e)
          (fun v : T.RightVertex e => (T.rightDepth e v) ^ 2),
        sum_prod_mul_nat (fun u : T.LeftVertex e => T.leftDepth e u)
          (fun v : T.RightVertex e => T.rightDepth e v)]
      simp [leftDepthMoment, rightDepthMoment]
      ring

theorem edgeOffsetMoment_three_expansion (e : T.Edge) :
    (∑ x : T.LeftVertex e × T.RightVertex e,
        (T.edgeOffset e x) ^ 3) =
      Fintype.card (T.RightVertex e) * T.leftDepthMoment e 3 +
      Fintype.card (T.LeftVertex e) * T.rightDepthMoment e 3 +
      3 * T.leftDepthMoment e 2 * T.rightDepthMoment e 1 +
      3 * T.leftDepthMoment e 1 * T.rightDepthMoment e 2 := by
  classical
  have hpoint : ∀ x : T.LeftVertex e × T.RightVertex e,
      (T.edgeOffset e x) ^ 3 =
        (T.leftDepth e x.1) ^ 3 + (T.rightDepth e x.2) ^ 3 +
          3 * ((T.leftDepth e x.1) ^ 2 * T.rightDepth e x.2) +
          3 * (T.leftDepth e x.1 * (T.rightDepth e x.2) ^ 2) := by
    intro x
    simp only [edgeOffset]
    ring
  calc
    (∑ x : T.LeftVertex e × T.RightVertex e,
        (T.edgeOffset e x) ^ 3) =
        (∑ x : T.LeftVertex e × T.RightVertex e,
          (T.leftDepth e x.1) ^ 3) +
        (∑ x : T.LeftVertex e × T.RightVertex e,
          (T.rightDepth e x.2) ^ 3) +
        3 * (∑ x : T.LeftVertex e × T.RightVertex e,
          (T.leftDepth e x.1) ^ 2 * T.rightDepth e x.2) +
        3 * (∑ x : T.LeftVertex e × T.RightVertex e,
          T.leftDepth e x.1 * (T.rightDepth e x.2) ^ 2) := by
      simp_rw [hpoint, Finset.sum_add_distrib, Finset.mul_sum]
    _ = Fintype.card (T.RightVertex e) * T.leftDepthMoment e 3 +
        Fintype.card (T.LeftVertex e) * T.rightDepthMoment e 3 +
        3 * T.leftDepthMoment e 2 * T.rightDepthMoment e 1 +
        3 * T.leftDepthMoment e 1 * T.rightDepthMoment e 2 := by
      rw [sum_prod_left_nat (B := T.RightVertex e)
          (fun u : T.LeftVertex e => (T.leftDepth e u) ^ 3),
        sum_prod_right_nat (A := T.LeftVertex e)
          (fun v : T.RightVertex e => (T.rightDepth e v) ^ 3),
        sum_prod_mul_nat (fun u : T.LeftVertex e => (T.leftDepth e u) ^ 2)
          (fun v : T.RightVertex e => T.rightDepth e v),
        sum_prod_mul_nat (fun u : T.LeftVertex e => T.leftDepth e u)
          (fun v : T.RightVertex e => (T.rightDepth e v) ^ 2)]
      simp [leftDepthMoment, rightDepthMoment]
      ring

theorem edgeOffsetAlternatingMoment_zero_expansion (e : T.Edge) :
    (∑ x : T.LeftVertex e × T.RightVertex e,
        signedPower (T.edgeOffset e x) 0) =
      T.leftAlternatingDepthMoment e 0 *
        T.rightAlternatingDepthMoment e 0 := by
  classical
  have hpoint : ∀ x : T.LeftVertex e × T.RightVertex e,
      signedPower (T.edgeOffset e x) 0 =
        signedPower (T.leftDepth e x.1) 0 *
          signedPower (T.rightDepth e x.2) 0 := by
    intro x
    simp [signedPower, edgeOffset, pow_add]
  simp_rw [hpoint]
  rw [sum_prod_mul_int
    (fun u : T.LeftVertex e => signedPower (T.leftDepth e u) 0)
    (fun v : T.RightVertex e => signedPower (T.rightDepth e v) 0)]
  unfold leftAlternatingDepthMoment rightAlternatingDepthMoment
  rfl

theorem edgeOffsetAlternatingMoment_one_expansion (e : T.Edge) :
    (∑ x : T.LeftVertex e × T.RightVertex e,
        signedPower (T.edgeOffset e x) 1) =
      T.leftAlternatingDepthMoment e 1 *
          T.rightAlternatingDepthMoment e 0 +
        T.leftAlternatingDepthMoment e 0 *
          T.rightAlternatingDepthMoment e 1 := by
  classical
  have hpoint : ∀ x : T.LeftVertex e × T.RightVertex e,
      signedPower (T.edgeOffset e x) 1 =
        signedPower (T.leftDepth e x.1) 1 *
            signedPower (T.rightDepth e x.2) 0 +
          signedPower (T.leftDepth e x.1) 0 *
            signedPower (T.rightDepth e x.2) 1 := by
    intro x
    simp [signedPower, edgeOffset, pow_add]
    ring
  calc
    (∑ x : T.LeftVertex e × T.RightVertex e,
        signedPower (T.edgeOffset e x) 1) =
        (∑ x : T.LeftVertex e × T.RightVertex e,
          signedPower (T.leftDepth e x.1) 1 *
            signedPower (T.rightDepth e x.2) 0) +
        ∑ x : T.LeftVertex e × T.RightVertex e,
          signedPower (T.leftDepth e x.1) 0 *
            signedPower (T.rightDepth e x.2) 1 := by
      simp_rw [hpoint, Finset.sum_add_distrib]
    _ = T.leftAlternatingDepthMoment e 1 *
          T.rightAlternatingDepthMoment e 0 +
        T.leftAlternatingDepthMoment e 0 *
          T.rightAlternatingDepthMoment e 1 := by
      rw [sum_prod_mul_int
          (fun u : T.LeftVertex e => signedPower (T.leftDepth e u) 1)
          (fun v : T.RightVertex e => signedPower (T.rightDepth e v) 0),
        sum_prod_mul_int
          (fun u : T.LeftVertex e => signedPower (T.leftDepth e u) 0)
          (fun v : T.RightVertex e => signedPower (T.rightDepth e v) 1)]
      unfold leftAlternatingDepthMoment rightAlternatingDepthMoment
      rfl

theorem edgeOffsetAlternatingMoment_two_expansion (e : T.Edge) :
    (∑ x : T.LeftVertex e × T.RightVertex e,
        signedPower (T.edgeOffset e x) 2) =
      T.leftAlternatingDepthMoment e 2 *
          T.rightAlternatingDepthMoment e 0 +
        2 * T.leftAlternatingDepthMoment e 1 *
          T.rightAlternatingDepthMoment e 1 +
        T.leftAlternatingDepthMoment e 0 *
          T.rightAlternatingDepthMoment e 2 := by
  classical
  have hpoint : ∀ x : T.LeftVertex e × T.RightVertex e,
      signedPower (T.edgeOffset e x) 2 =
        signedPower (T.leftDepth e x.1) 2 *
            signedPower (T.rightDepth e x.2) 0 +
          2 * (signedPower (T.leftDepth e x.1) 1 *
            signedPower (T.rightDepth e x.2) 1) +
          signedPower (T.leftDepth e x.1) 0 *
            signedPower (T.rightDepth e x.2) 2 := by
    intro x
    simp [signedPower, edgeOffset, pow_add]
    ring
  calc
    (∑ x : T.LeftVertex e × T.RightVertex e,
        signedPower (T.edgeOffset e x) 2) =
        (∑ x : T.LeftVertex e × T.RightVertex e,
          signedPower (T.leftDepth e x.1) 2 *
            signedPower (T.rightDepth e x.2) 0) +
        2 * (∑ x : T.LeftVertex e × T.RightVertex e,
          signedPower (T.leftDepth e x.1) 1 *
            signedPower (T.rightDepth e x.2) 1) +
        (∑ x : T.LeftVertex e × T.RightVertex e,
          signedPower (T.leftDepth e x.1) 0 *
            signedPower (T.rightDepth e x.2) 2) := by
      simp_rw [hpoint, Finset.sum_add_distrib, Finset.mul_sum]
    _ = T.leftAlternatingDepthMoment e 2 *
          T.rightAlternatingDepthMoment e 0 +
        2 * T.leftAlternatingDepthMoment e 1 *
          T.rightAlternatingDepthMoment e 1 +
        T.leftAlternatingDepthMoment e 0 *
          T.rightAlternatingDepthMoment e 2 := by
      rw [sum_prod_mul_int
          (fun u : T.LeftVertex e => signedPower (T.leftDepth e u) 2)
          (fun v : T.RightVertex e => signedPower (T.rightDepth e v) 0),
        sum_prod_mul_int
          (fun u : T.LeftVertex e => signedPower (T.leftDepth e u) 1)
          (fun v : T.RightVertex e => signedPower (T.rightDepth e v) 1),
        sum_prod_mul_int
          (fun u : T.LeftVertex e => signedPower (T.leftDepth e u) 0)
          (fun v : T.RightVertex e => signedPower (T.rightDepth e v) 2)]
      unfold leftAlternatingDepthMoment rightAlternatingDepthMoment
      ring

theorem edgeOffsetAlternatingMoment_three_expansion (e : T.Edge) :
    (∑ x : T.LeftVertex e × T.RightVertex e,
        signedPower (T.edgeOffset e x) 3) =
      T.leftAlternatingDepthMoment e 3 *
          T.rightAlternatingDepthMoment e 0 +
        3 * T.leftAlternatingDepthMoment e 2 *
          T.rightAlternatingDepthMoment e 1 +
        3 * T.leftAlternatingDepthMoment e 1 *
          T.rightAlternatingDepthMoment e 2 +
        T.leftAlternatingDepthMoment e 0 *
          T.rightAlternatingDepthMoment e 3 := by
  classical
  have hpoint : ∀ x : T.LeftVertex e × T.RightVertex e,
      signedPower (T.edgeOffset e x) 3 =
        signedPower (T.leftDepth e x.1) 3 *
            signedPower (T.rightDepth e x.2) 0 +
          3 * (signedPower (T.leftDepth e x.1) 2 *
            signedPower (T.rightDepth e x.2) 1) +
          3 * (signedPower (T.leftDepth e x.1) 1 *
            signedPower (T.rightDepth e x.2) 2) +
          signedPower (T.leftDepth e x.1) 0 *
            signedPower (T.rightDepth e x.2) 3 := by
    intro x
    simp [signedPower, edgeOffset, pow_add]
    ring
  calc
    (∑ x : T.LeftVertex e × T.RightVertex e,
        signedPower (T.edgeOffset e x) 3) =
        (∑ x : T.LeftVertex e × T.RightVertex e,
          signedPower (T.leftDepth e x.1) 3 *
            signedPower (T.rightDepth e x.2) 0) +
        3 * (∑ x : T.LeftVertex e × T.RightVertex e,
          signedPower (T.leftDepth e x.1) 2 *
            signedPower (T.rightDepth e x.2) 1) +
        3 * (∑ x : T.LeftVertex e × T.RightVertex e,
          signedPower (T.leftDepth e x.1) 1 *
            signedPower (T.rightDepth e x.2) 2) +
        (∑ x : T.LeftVertex e × T.RightVertex e,
          signedPower (T.leftDepth e x.1) 0 *
            signedPower (T.rightDepth e x.2) 3) := by
      simp_rw [hpoint, Finset.sum_add_distrib, Finset.mul_sum]
    _ = T.leftAlternatingDepthMoment e 3 *
          T.rightAlternatingDepthMoment e 0 +
        3 * T.leftAlternatingDepthMoment e 2 *
          T.rightAlternatingDepthMoment e 1 +
        3 * T.leftAlternatingDepthMoment e 1 *
          T.rightAlternatingDepthMoment e 2 +
        T.leftAlternatingDepthMoment e 0 *
          T.rightAlternatingDepthMoment e 3 := by
      rw [sum_prod_mul_int
          (fun u : T.LeftVertex e => signedPower (T.leftDepth e u) 3)
          (fun v : T.RightVertex e => signedPower (T.rightDepth e v) 0),
        sum_prod_mul_int
          (fun u : T.LeftVertex e => signedPower (T.leftDepth e u) 2)
          (fun v : T.RightVertex e => signedPower (T.rightDepth e v) 1),
        sum_prod_mul_int
          (fun u : T.LeftVertex e => signedPower (T.leftDepth e u) 1)
          (fun v : T.RightVertex e => signedPower (T.rightDepth e v) 2),
        sum_prod_mul_int
          (fun u : T.LeftVertex e => signedPower (T.leftDepth e u) 0)
          (fun v : T.RightVertex e => signedPower (T.rightDepth e v) 3)]
      unfold leftAlternatingDepthMoment rightAlternatingDepthMoment
      ring

/-- Degree-zero ordinary moment identity (equivalently, the exact hole
cardinality) in additive form. -/
theorem edgeHoleMoment_zero (hL : IsLeech T) (e : T.Edge) :
    finsetMoment (T.edgeHoleSet e) 0 +
        T.cutSize e * (n - T.cutSize e) =
      finsetMoment (T.edgeOffsetInterval e) 0 := by
  simpa [finsetMoment, T.crossOffsetSpectrum_card hL e] using
    T.edgeHoleMoment_add_crossOffsetMoment hL e 0

/-- Degree-one ordinary edge-hole moment identity. -/
theorem edgeHoleMoment_one (hL : IsLeech T) (e : T.Edge) :
    finsetMoment (T.edgeHoleSet e) 1 +
        Fintype.card (T.RightVertex e) * T.leftDepthMoment e 1 +
        Fintype.card (T.LeftVertex e) * T.rightDepthMoment e 1 =
      finsetMoment (T.edgeOffsetInterval e) 1 := by
  have hpartition := T.edgeHoleMoment_add_crossOffsetMoment hL e 1
  rw [T.crossOffsetMoment_eq_indexed hL e 1] at hpartition
  simp only [pow_one] at hpartition
  rw [T.edgeOffsetMoment_one_expansion e] at hpartition
  simpa [add_assoc] using hpartition

/-- Degree-two ordinary edge-hole moment identity. -/
theorem edgeHoleMoment_two (hL : IsLeech T) (e : T.Edge) :
    finsetMoment (T.edgeHoleSet e) 2 +
        Fintype.card (T.RightVertex e) * T.leftDepthMoment e 2 +
        Fintype.card (T.LeftVertex e) * T.rightDepthMoment e 2 +
        2 * T.leftDepthMoment e 1 * T.rightDepthMoment e 1 =
      finsetMoment (T.edgeOffsetInterval e) 2 := by
  have hpartition := T.edgeHoleMoment_add_crossOffsetMoment hL e 2
  rw [T.crossOffsetMoment_eq_indexed hL e 2] at hpartition
  rw [T.edgeOffsetMoment_two_expansion e] at hpartition
  simpa [add_assoc] using hpartition

/-- Degree-three ordinary edge-hole moment identity. -/
theorem edgeHoleMoment_three (hL : IsLeech T) (e : T.Edge) :
    finsetMoment (T.edgeHoleSet e) 3 +
        Fintype.card (T.RightVertex e) * T.leftDepthMoment e 3 +
        Fintype.card (T.LeftVertex e) * T.rightDepthMoment e 3 +
        3 * T.leftDepthMoment e 2 * T.rightDepthMoment e 1 +
        3 * T.leftDepthMoment e 1 * T.rightDepthMoment e 2 =
      finsetMoment (T.edgeOffsetInterval e) 3 := by
  have hpartition := T.edgeHoleMoment_add_crossOffsetMoment hL e 3
  rw [T.crossOffsetMoment_eq_indexed hL e 3] at hpartition
  rw [T.edgeOffsetMoment_three_expansion e] at hpartition
  simpa [add_assoc] using hpartition

/-- Degree-zero alternating edge-hole moment identity. -/
theorem edgeHoleAlternatingMoment_zero (hL : IsLeech T) (e : T.Edge) :
    alternatingFinsetMoment (T.edgeHoleSet e) 0 +
        T.leftAlternatingDepthMoment e 0 *
          T.rightAlternatingDepthMoment e 0 =
      alternatingFinsetMoment (T.edgeOffsetInterval e) 0 := by
  have hpartition :=
    T.edgeHoleAlternatingMoment_add_crossOffsetMoment hL e 0
  rw [T.crossOffsetAlternatingMoment_eq_indexed hL e 0,
    T.edgeOffsetAlternatingMoment_zero_expansion e] at hpartition
  exact hpartition

/-- Degree-one alternating edge-hole moment identity. -/
theorem edgeHoleAlternatingMoment_one (hL : IsLeech T) (e : T.Edge) :
    alternatingFinsetMoment (T.edgeHoleSet e) 1 +
        T.leftAlternatingDepthMoment e 1 *
          T.rightAlternatingDepthMoment e 0 +
        T.leftAlternatingDepthMoment e 0 *
          T.rightAlternatingDepthMoment e 1 =
      alternatingFinsetMoment (T.edgeOffsetInterval e) 1 := by
  have hpartition :=
    T.edgeHoleAlternatingMoment_add_crossOffsetMoment hL e 1
  rw [T.crossOffsetAlternatingMoment_eq_indexed hL e 1,
    T.edgeOffsetAlternatingMoment_one_expansion e] at hpartition
  simpa [add_assoc] using hpartition

/-- Degree-two alternating edge-hole moment identity. -/
theorem edgeHoleAlternatingMoment_two (hL : IsLeech T) (e : T.Edge) :
    alternatingFinsetMoment (T.edgeHoleSet e) 2 +
        T.leftAlternatingDepthMoment e 2 *
          T.rightAlternatingDepthMoment e 0 +
        2 * T.leftAlternatingDepthMoment e 1 *
          T.rightAlternatingDepthMoment e 1 +
        T.leftAlternatingDepthMoment e 0 *
          T.rightAlternatingDepthMoment e 2 =
      alternatingFinsetMoment (T.edgeOffsetInterval e) 2 := by
  have hpartition :=
    T.edgeHoleAlternatingMoment_add_crossOffsetMoment hL e 2
  rw [T.crossOffsetAlternatingMoment_eq_indexed hL e 2,
    T.edgeOffsetAlternatingMoment_two_expansion e] at hpartition
  simpa [add_assoc] using hpartition

/-- Degree-three alternating edge-hole moment identity. -/
theorem edgeHoleAlternatingMoment_three (hL : IsLeech T) (e : T.Edge) :
    alternatingFinsetMoment (T.edgeHoleSet e) 3 +
        T.leftAlternatingDepthMoment e 3 *
          T.rightAlternatingDepthMoment e 0 +
        3 * T.leftAlternatingDepthMoment e 2 *
          T.rightAlternatingDepthMoment e 1 +
        3 * T.leftAlternatingDepthMoment e 1 *
          T.rightAlternatingDepthMoment e 2 +
        T.leftAlternatingDepthMoment e 0 *
          T.rightAlternatingDepthMoment e 3 =
      alternatingFinsetMoment (T.edgeOffsetInterval e) 3 := by
  have hpartition :=
    T.edgeHoleAlternatingMoment_add_crossOffsetMoment hL e 3
  rw [T.crossOffsetAlternatingMoment_eq_indexed hL e 3,
    T.edgeOffsetAlternatingMoment_three_expansion e] at hpartition
  simpa [add_assoc] using hpartition

end PosIntTree

/-- Single claim-level package for the actual every-edge hole theorem.  It
retains the precise Finset, cardinality, translated disjoint internal spectra,
and ordinary and alternating moment identities through degree three. -/
theorem everyEdge_hole_identity
    {T : PosIntTree n} (hL : IsLeech T) (e : T.Edge) :
    T.edgeHoleSet e ⊆ Finset.Icc 1 (targetN n - T.weight e) ∧
    (T.edgeHoleSet e).card =
      (targetN n - T.weight e + 1) -
        T.cutSize e * (n - T.cutSize e) ∧
    T.shiftedEdgeHoleSet e =
      T.leftHighInternalSpectrum e ∪ T.rightHighInternalSpectrum e ∧
    Disjoint (T.leftHighInternalSpectrum e)
      (T.rightHighInternalSpectrum e) ∧
    PosIntTree.finsetMoment (T.edgeHoleSet e) 0 +
        T.cutSize e * (n - T.cutSize e) =
      PosIntTree.finsetMoment (T.edgeOffsetInterval e) 0 ∧
    PosIntTree.finsetMoment (T.edgeHoleSet e) 1 +
        Fintype.card (T.RightVertex e) * T.leftDepthMoment e 1 +
        Fintype.card (T.LeftVertex e) * T.rightDepthMoment e 1 =
      PosIntTree.finsetMoment (T.edgeOffsetInterval e) 1 ∧
    PosIntTree.finsetMoment (T.edgeHoleSet e) 2 +
        Fintype.card (T.RightVertex e) * T.leftDepthMoment e 2 +
        Fintype.card (T.LeftVertex e) * T.rightDepthMoment e 2 +
        2 * T.leftDepthMoment e 1 * T.rightDepthMoment e 1 =
      PosIntTree.finsetMoment (T.edgeOffsetInterval e) 2 ∧
    PosIntTree.finsetMoment (T.edgeHoleSet e) 3 +
        Fintype.card (T.RightVertex e) * T.leftDepthMoment e 3 +
        Fintype.card (T.LeftVertex e) * T.rightDepthMoment e 3 +
        3 * T.leftDepthMoment e 2 * T.rightDepthMoment e 1 +
        3 * T.leftDepthMoment e 1 * T.rightDepthMoment e 2 =
      PosIntTree.finsetMoment (T.edgeOffsetInterval e) 3 ∧
    PosIntTree.alternatingFinsetMoment (T.edgeHoleSet e) 0 +
        T.leftAlternatingDepthMoment e 0 *
          T.rightAlternatingDepthMoment e 0 =
      PosIntTree.alternatingFinsetMoment (T.edgeOffsetInterval e) 0 ∧
    PosIntTree.alternatingFinsetMoment (T.edgeHoleSet e) 1 +
        T.leftAlternatingDepthMoment e 1 *
          T.rightAlternatingDepthMoment e 0 +
        T.leftAlternatingDepthMoment e 0 *
          T.rightAlternatingDepthMoment e 1 =
      PosIntTree.alternatingFinsetMoment (T.edgeOffsetInterval e) 1 ∧
    PosIntTree.alternatingFinsetMoment (T.edgeHoleSet e) 2 +
        T.leftAlternatingDepthMoment e 2 *
          T.rightAlternatingDepthMoment e 0 +
        2 * T.leftAlternatingDepthMoment e 1 *
          T.rightAlternatingDepthMoment e 1 +
        T.leftAlternatingDepthMoment e 0 *
          T.rightAlternatingDepthMoment e 2 =
      PosIntTree.alternatingFinsetMoment (T.edgeOffsetInterval e) 2 ∧
    PosIntTree.alternatingFinsetMoment (T.edgeHoleSet e) 3 +
        T.leftAlternatingDepthMoment e 3 *
          T.rightAlternatingDepthMoment e 0 +
        3 * T.leftAlternatingDepthMoment e 2 *
          T.rightAlternatingDepthMoment e 1 +
        3 * T.leftAlternatingDepthMoment e 1 *
          T.rightAlternatingDepthMoment e 2 +
        T.leftAlternatingDepthMoment e 0 *
          T.rightAlternatingDepthMoment e 3 =
      PosIntTree.alternatingFinsetMoment (T.edgeOffsetInterval e) 3 := by
  exact ⟨T.edgeHoleSet_subset_positive_interval hL e,
    T.edgeHoleSet_card hL e,
    T.shiftedEdgeHoleSet_eq_highInternalSpectra hL e,
    T.highInternalSpectra_disjoint hL e,
    T.edgeHoleMoment_zero hL e,
    T.edgeHoleMoment_one hL e,
    T.edgeHoleMoment_two hL e,
    T.edgeHoleMoment_three hL e,
    T.edgeHoleAlternatingMoment_zero hL e,
    T.edgeHoleAlternatingMoment_one hL e,
    T.edgeHoleAlternatingMoment_two hL e,
    T.edgeHoleAlternatingMoment_three hL e⟩

end LeechTrees.Foundation
