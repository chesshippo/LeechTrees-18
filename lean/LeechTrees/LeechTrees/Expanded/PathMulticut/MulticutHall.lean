import Mathlib.Combinatorics.Hall.Basic
import LeechTrees.ParityTailExactBundle
import LeechTrees.LeafRange
import LeechTrees.Expanded.PathMulticut.PathSegmentStatistics

/-!
# Coupled two-cut moments and capacitated Hall inequalities

The moment envelopes are defined as the genuine finite minima and maxima over
all subsets of the requested cardinality.  Thus the two-cut inequalities do
not hide a relaxation inside their definitions.  The Hall theorem clones each
component-pair demand and proves the exact iff with a single injective rank
allocation.
-/

open scoped BigOperators

namespace LeechTrees.PathMulticut

open LeechTrees.Foundation
open LeechTrees.ParityTail
open LeechTrees.ParityTail.GraphAdapterV1
open LeechTrees.ParityTail.T8Collinear

noncomputable section

/-! ## Exact subset-moment envelopes -/

def powerMoment (p : ℕ) (S : Finset ℕ) : ℤ :=
  ∑ d ∈ S, ((d ^ p : ℕ) : ℤ)

def subsetPowerMoments (U : Finset ℕ) (p k : ℕ) : Finset ℤ :=
  (U.powersetCard k).image (powerMoment p)

/-- Sum of the `k` least available `p`th powers, expressed as the exact finite
minimum.  The impossible-cardinality branch is irrelevant to every theorem
below and is fixed to zero. -/
def lowerPowerEnvelope (U : Finset ℕ) (p k : ℕ) : ℤ :=
  if h : (subsetPowerMoments U p k).Nonempty then
    (subsetPowerMoments U p k).min' h
  else 0

/-- Sum of the `k` greatest available `p`th powers, expressed as the exact
finite maximum. -/
def upperPowerEnvelope (U : Finset ℕ) (p k : ℕ) : ℤ :=
  if h : (subsetPowerMoments U p k).Nonempty then
    (subsetPowerMoments U p k).max' h
  else 0

theorem powerMoment_mem_subsetPowerMoments {U S : Finset ℕ} {p k : ℕ}
    (hsub : S ⊆ U) (hcard : S.card = k) :
    powerMoment p S ∈ subsetPowerMoments U p k := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨S, by simpa [Finset.mem_powersetCard, hcard] using hsub, rfl⟩

theorem lowerPowerEnvelope_le {U S : Finset ℕ} (p : ℕ)
    (hsub : S ⊆ U) :
    lowerPowerEnvelope U p S.card ≤ powerMoment p S := by
  classical
  have hmem := powerMoment_mem_subsetPowerMoments (p := p) hsub rfl
  unfold lowerPowerEnvelope
  split
  · exact Finset.min'_le _ _ hmem
  · exact (by
      exfalso
      exact ‹¬(subsetPowerMoments U p S.card).Nonempty› ⟨_, hmem⟩)

theorem le_upperPowerEnvelope {U S : Finset ℕ} (p : ℕ)
    (hsub : S ⊆ U) :
    powerMoment p S ≤ upperPowerEnvelope U p S.card := by
  classical
  have hmem := powerMoment_mem_subsetPowerMoments (p := p) hsub rfl
  unfold upperPowerEnvelope
  split
  · exact Finset.le_max' _ _ hmem
  · exact (by
      exfalso
      exact ‹¬(subsetPowerMoments U p S.card).Nonempty› ⟨_, hmem⟩)

theorem powerMoment_union {A B : Finset ℕ} (p : ℕ)
    (h : Disjoint A B) :
    powerMoment p (A ∪ B) = powerMoment p A + powerMoment p B := by
  unfold powerMoment
  rw [Finset.sum_union h]

/-- Exact two-cut four-bin outer bounds.  `B11`, `B10`, and `B01` are the
three nonzero membership bins.  Their actual cardinalities are retained, so a
graph adapter may rewrite them to `ab`, `am`, and `bm` without changing this
theorem.
-/
theorem coupled_twoCut_powerMoment_bounds
    (U B11 B10 B01 : Finset ℕ) (p : ℕ)
    (h11U : B11 ⊆ U) (h10U : B10 ⊆ U) (h01U : B01 ⊆ U)
    (h11_10 : Disjoint B11 B10)
    (h11_01 : Disjoint B11 B01)
    (h10_01 : Disjoint B10 B01) :
    lowerPowerEnvelope U p B10.card -
        upperPowerEnvelope U p B01.card ≤
      powerMoment p (B11 ∪ B10) - powerMoment p (B11 ∪ B01) ∧
    powerMoment p (B11 ∪ B10) - powerMoment p (B11 ∪ B01) ≤
      upperPowerEnvelope U p B10.card -
        lowerPowerEnvelope U p B01.card ∧
    lowerPowerEnvelope U p B11.card +
        lowerPowerEnvelope U p ((B11 ∪ B10) ∪ B01).card ≤
      powerMoment p (B11 ∪ B10) + powerMoment p (B11 ∪ B01) ∧
    powerMoment p (B11 ∪ B10) + powerMoment p (B11 ∪ B01) ≤
      upperPowerEnvelope U p B11.card +
        upperPowerEnvelope U p ((B11 ∪ B10) ∪ B01).card := by
  have h10lower := lowerPowerEnvelope_le p h10U
  have h10upper := le_upperPowerEnvelope p h10U
  have h01lower := lowerPowerEnvelope_le p h01U
  have h01upper := le_upperPowerEnvelope p h01U
  have h11lower := lowerPowerEnvelope_le p h11U
  have h11upper := le_upperPowerEnvelope p h11U
  have hUnionSub : (B11 ∪ B10) ∪ B01 ⊆ U := by
    intro x hx
    simp only [Finset.mem_union] at hx
    rcases hx with (hx | hx) | hx
    · exact h11U hx
    · exact h10U hx
    · exact h01U hx
  have hUnionLower := lowerPowerEnvelope_le p hUnionSub
  have hUnionUpper := le_upperPowerEnvelope p hUnionSub
  have h11u10 := powerMoment_union p h11_10
  have h11u01 := powerMoment_union p h11_01
  have hUnionMoment :
      powerMoment p ((B11 ∪ B10) ∪ B01) =
        powerMoment p B11 + powerMoment p B10 + powerMoment p B01 := by
    rw [powerMoment_union p (Finset.disjoint_union_left.mpr
      ⟨h11_01, h10_01⟩), h11u10]
  constructor
  · rw [h11u10, h11u01]
    linarith
  constructor
  · rw [h11u10, h11u01]
    linarith
  constructor
  · rw [h11u10, h11u01]
    rw [hUnionMoment] at hUnionLower
    linarith
  · rw [h11u10, h11u01]
    rw [hUnionMoment] at hUnionUpper
    linarith

/-! ## Actual two-cut four-bin adapter -/

def twoCutPairBin11 {n : ℕ} (T : PosIntTree n) (e f : T.Edge) :
    Finset (VertexPair n) :=
  Finset.univ.filter fun q =>
    e.1 ∈ T.pathEdges q.left q.right ∧
      f.1 ∈ T.pathEdges q.left q.right

def twoCutPairBin10 {n : ℕ} (T : PosIntTree n) (e f : T.Edge) :
    Finset (VertexPair n) :=
  Finset.univ.filter fun q =>
    e.1 ∈ T.pathEdges q.left q.right ∧
      f.1 ∉ T.pathEdges q.left q.right

def twoCutPairBin01 {n : ℕ} (T : PosIntTree n) (e f : T.Edge) :
    Finset (VertexPair n) :=
  Finset.univ.filter fun q =>
    e.1 ∉ T.pathEdges q.left q.right ∧
      f.1 ∈ T.pathEdges q.left q.right

def twoCutPairBin00 {n : ℕ} (T : PosIntTree n) (e f : T.Edge) :
    Finset (VertexPair n) :=
  Finset.univ.filter fun q =>
    e.1 ∉ T.pathEdges q.left q.right ∧
      f.1 ∉ T.pathEdges q.left q.right

def twoCutRankBin11 {n : ℕ} (T : PosIntTree n) (e f : T.Edge) : Finset ℕ :=
  (twoCutPairBin11 T e f).image T.pairDist

def twoCutRankBin10 {n : ℕ} (T : PosIntTree n) (e f : T.Edge) : Finset ℕ :=
  (twoCutPairBin10 T e f).image T.pairDist

def twoCutRankBin01 {n : ℕ} (T : PosIntTree n) (e f : T.Edge) : Finset ℕ :=
  (twoCutPairBin01 T e f).image T.pairDist

def twoCutRankBin00 {n : ℕ} (T : PosIntTree n) (e f : T.Edge) : Finset ℕ :=
  (twoCutPairBin00 T e f).image T.pairDist

/-- The two actual cut blocks are exactly the indicated unions of their
common four-way membership partition. -/
theorem twoCut_pair_block_union {n : ℕ} (T : PosIntTree n)
    (e f : T.Edge) :
    pathSupport T {e} = twoCutPairBin11 T e f ∪ twoCutPairBin10 T e f ∧
    pathSupport T {f} = twoCutPairBin11 T e f ∪ twoCutPairBin01 T e f := by
  classical
  constructor <;> apply Finset.ext <;> intro q <;>
    simp [pathSupport, twoCutPairBin11, twoCutPairBin10,
      twoCutPairBin01] <;> tauto

/-- Value-level form of `twoCut_pair_block_union`, retaining the exact common
`11` bin rather than treating the two cut blocks independently. -/
theorem twoCut_rank_block_union {n : ℕ} (T : PosIntTree n)
    (e f : T.Edge) :
    selectedPathDistanceSet T {e} =
        twoCutRankBin11 T e f ∪ twoCutRankBin10 T e f ∧
    selectedPathDistanceSet T {f} =
        twoCutRankBin11 T e f ∪ twoCutRankBin01 T e f := by
  obtain ⟨he, hf⟩ := twoCut_pair_block_union T e f
  unfold selectedPathDistanceSet twoCutRankBin11 twoCutRankBin10
    twoCutRankBin01
  rw [he, hf, Finset.image_union, Finset.image_union]
  exact ⟨rfl, rfl⟩

/-- Every pair of distinct actual tree edges admits one of the two genuine
`A--M--B` orientations.  The root and nesting direction are constructed from
an actual named pair path containing both edges. -/
theorem exists_twoCut_AMB_orientation {n : ℕ} (T : PosIntTree n)
    (e f : T.Edge) (hef : e ≠ f) :
    ∃ r : Fin n,
      (∀ x, OrientedCut.Away T r f x → OrientedCut.Away T r e x) ∨
      (∀ x, OrientedCut.Away T r e x → OrientedCut.Away T r f x) := by
  obtain ⟨q, he, hf⟩ :=
    LeechTrees.LeafRange.exists_pair_containing_two_edges T e f hef
  have hae : OrientedCut.Away T q.left e q.right :=
    (OrientedCut.away_iff_mem_pathEdges T q.left e q.right).2 he
  have haf : OrientedCut.Away T q.left f q.right :=
    (OrientedCut.away_iff_mem_pathEdges T q.left f q.right).2 hf
  rcases OrientedCut.away_comparable_of_common T q.left e f hae haf with
      hef' | hfe'
  · exact ⟨q.left, Or.inr hef'⟩
  · exact ⟨q.left, Or.inl hfe'⟩

/-- Constructed orientation data for two distinct cuts. -/
structure ActualTwoCutAMBOrientation {n : ℕ} (T : PosIntTree n)
    (e f : T.Edge) where
  root : Fin n
  near : T.Edge
  far : T.Edge
  near_far : (near = e ∧ far = f) ∨ (near = f ∧ far = e)
  far_sub_near : ∀ x,
    OrientedCut.Away T root far x → OrientedCut.Away T root near x

/-- Canonical choice of the actual `A--M--B` orientation; callers do not
supply a nesting premise. -/
noncomputable def actualTwoCutAMBOrientation {n : ℕ} (T : PosIntTree n)
    (e f : T.Edge) (hef : e ≠ f) : ActualTwoCutAMBOrientation T e f := by
  classical
  let hex := exists_twoCut_AMB_orientation T e f hef
  let r := Classical.choose hex
  have hr := Classical.choose_spec hex
  by_cases hfe : ∀ x, OrientedCut.Away T r f x →
      OrientedCut.Away T r e x
  · exact ⟨r, e, f, Or.inl ⟨rfl, rfl⟩, hfe⟩
  · have hef' : ∀ x, OrientedCut.Away T r e x →
        OrientedCut.Away T r f x := hr.resolve_left hfe
    exact ⟨r, f, e, Or.inr ⟨rfl, rfl⟩, hef'⟩

theorem ActualTwoCutAMBOrientation.near_ne_far {n : ℕ}
    {T : PosIntTree n} {e f : T.Edge}
    (O : ActualTwoCutAMBOrientation T e f) (hef : e ≠ f) :
    O.near ≠ O.far := by
  rcases O.near_far with h | h
  · rw [h.1, h.2]
    exact hef
  · rw [h.1, h.2]
    exact hef.symm

/-! ### Exact `A--M--B` component adapter -/

def twoCutA {n : ℕ} (T : PosIntTree n) (r : Fin n) (e : T.Edge) :
    Finset (Fin n) := rootOuterSet T r e

def twoCutM {n : ℕ} (T : PosIntTree n) (r : Fin n)
    (e f : T.Edge) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun x =>
    OrientedCut.Away T r e x ∧ ¬OrientedCut.Away T r f x

def twoCutB {n : ℕ} (T : PosIntTree n) (r : Fin n) (f : T.Edge) :
    Finset (Fin n) := awayOuterSet T r f

/-- Unordered pairs with one endpoint in each of two named disjoint vertex
sets. -/
def betweenPairSet {n : ℕ} (A B : Finset (Fin n)) :
    Finset (VertexPair n) :=
  Finset.univ.filter fun q =>
    (q.left ∈ A ∧ q.right ∈ B) ∨ (q.left ∈ B ∧ q.right ∈ A)

/-- Exact Cartesian indexing of `betweenPairSet`. -/
noncomputable def betweenPairEquiv {n : ℕ} (A B : Finset (Fin n))
    (hAB : Disjoint A B) :
    ({u : Fin n // u ∈ A} × {v : Fin n // v ∈ B}) ≃
      {q : VertexPair n // q ∈ betweenPairSet A B} := by
  classical
  let toFun : ({u : Fin n // u ∈ A} × {v : Fin n // v ∈ B}) →
      {q : VertexPair n // q ∈ betweenPairSet A B} := fun z =>
    ⟨VertexPair.ofDistinct z.1 z.2 (fun h =>
      Finset.disjoint_left.mp hAB z.1.2 (h ▸ z.2.2)), by
      by_cases hlt : z.1.1 < z.2.1
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        left
        simp only [VertexPair.ofDistinct, dif_pos hlt, VertexPair.left,
          VertexPair.right]
        exact ⟨z.1.2, z.2.2⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        right
        simp only [VertexPair.ofDistinct, dif_neg hlt, VertexPair.left,
          VertexPair.right]
        exact ⟨z.2.2, z.1.2⟩⟩
  let invFun : {q : VertexPair n // q ∈ betweenPairSet A B} →
      ({u : Fin n // u ∈ A} × {v : Fin n // v ∈ B}) := fun q =>
    if h : q.1.left ∈ A then
      (⟨q.1.left, h⟩, ⟨q.1.right, by
        have hmem := (Finset.mem_filter.mp q.2).2
        rcases hmem with hd | hs
        · exact hd.2
        · exact (Finset.disjoint_left.mp hAB h hs.1).elim⟩)
    else
      (⟨q.1.right, by
        have hmem := (Finset.mem_filter.mp q.2).2
        rcases hmem with hd | hs
        · exact (h hd.1).elim
        · exact hs.2⟩,
       ⟨q.1.left, by
        have hmem := (Finset.mem_filter.mp q.2).2
        rcases hmem with hd | hs
        · exact (h hd.1).elim
        · exact hs.1⟩)
  exact {
    toFun := toFun
    invFun := invFun
    left_inv := by
      rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
      by_cases huv : u < v
      · simp [toFun, invFun, VertexPair.ofDistinct, huv, hu,
          VertexPair.left, VertexPair.right]
      · have hne : u ≠ v := by
          intro h
          subst v
          exact Finset.disjoint_left.mp hAB hu hv
        have hvu : v < u := lt_of_le_of_ne (le_of_not_gt huv) hne.symm
        have hvA : v ∉ A := fun hvA => Finset.disjoint_left.mp hAB hvA hv
        simp [toFun, invFun, VertexPair.ofDistinct, huv, hvA,
          VertexPair.left, VertexPair.right]
    right_inv := by
      rintro ⟨q, hq⟩
      by_cases hA : q.left ∈ A
      · have hB : q.right ∈ B := by
          rcases (Finset.mem_filter.mp hq).2 with h | h
          · exact h.2
          · exact (Finset.disjoint_left.mp hAB hA h.1).elim
        dsimp only [invFun]
        rw [dif_pos hA]
        dsimp only [toFun]
        apply Subtype.ext
        have hne : q.left ≠ q.right := ne_of_lt q.left_lt_right
        change VertexPair.ofDistinct q.left q.right hne = q
        unfold VertexPair.ofDistinct
        rw [dif_pos q.left_lt_right]
        apply VertexPair.ext <;> rfl
      · have hB : q.left ∈ B := by
          rcases (Finset.mem_filter.mp hq).2 with h | h
          · exact (hA h.1).elim
          · exact h.1
        have hAr : q.right ∈ A := by
          rcases (Finset.mem_filter.mp hq).2 with h | h
          · exact (hA h.1).elim
          · exact h.2
        dsimp only [invFun]
        rw [dif_neg hA]
        dsimp only [toFun]
        apply Subtype.ext
        have hne : q.right ≠ q.left := (ne_of_lt q.left_lt_right).symm
        change VertexPair.ofDistinct q.right q.left hne = q
        unfold VertexPair.ofDistinct
        rw [dif_neg (not_lt_of_ge q.left_lt_right.le)]
        apply VertexPair.ext <;> rfl }

theorem betweenPairSet_card {n : ℕ} (A B : Finset (Fin n))
    (hAB : Disjoint A B) :
    (betweenPairSet A B).card = A.card * B.card := by
  classical
  calc
    (betweenPairSet A B).card =
        Fintype.card {q : VertexPair n // q ∈ betweenPairSet A B} := by simp
    _ = Fintype.card
        ({u : Fin n // u ∈ A} × {v : Fin n // v ∈ B}) :=
      Fintype.card_congr (betweenPairEquiv A B hAB).symm
    _ = A.card * B.card := by simp

def withinPairSet {n : ℕ} (A : Finset (Fin n)) :
    Finset (VertexPair n) :=
  Finset.univ.filter fun q => q.left ∈ A ∧ q.right ∈ A

def positivePart {Vertex : Type*} [DecidableEq Vertex]
    (sign : Vertex → ℤ) (S : Finset Vertex) : Finset Vertex :=
  S.filter fun x => sign x = 1

def negativePart {Vertex : Type*} [DecidableEq Vertex]
    (sign : Vertex → ℤ) (S : Finset Vertex) : Finset Vertex :=
  S.filter fun x => sign x = -1

def oddPairCard {n : ℕ} (T : PosIntTree n)
    (Q : Finset (VertexPair n)) : ℕ :=
  (Q.filter fun q => T.pairDist q % 2 = 1).card

private theorem odd_between_filter_eq {n : ℕ} (T : PosIntTree n)
    (r : Fin n) (A B : Finset (Fin n)) :
    (betweenPairSet A B).filter (fun q => T.pairDist q % 2 = 1) =
      betweenPairSet
          (positivePart (rootParitySign T r) A)
          (negativePart (rootParitySign T r) B) ∪
        betweenPairSet
          (negativePart (rootParitySign T r) A)
          (positivePart (rootParitySign T r) B) := by
  classical
  ext q
  have hs := rootParitySign_pairDist T r q
  have hl := rootParitySign_pm T r q.left
  have hr := rootParitySign_pm T r q.right
  simp only [Finset.mem_filter, Finset.mem_union]
  rw [← paritySign_eq_neg_one_iff_mod_two, ← hs]
  rcases hl with hl | hl
  · rcases hr with hr | hr
    · simp [betweenPairSet, positivePart, negativePart, hl, hr]
    · simp [betweenPairSet, positivePart, negativePart, hl, hr]
  · rcases hr with hr | hr
    · simp [betweenPairSet, positivePart, negativePart, hl, hr]
      tauto
    · simp [betweenPairSet, positivePart, negativePart, hl, hr]

private theorem odd_between_union_disjoint {n : ℕ} (T : PosIntTree n)
    (r : Fin n) (A B : Finset (Fin n)) (hAB : Disjoint A B) :
    Disjoint
      (betweenPairSet
        (positivePart (rootParitySign T r) A)
        (negativePart (rootParitySign T r) B))
      (betweenPairSet
        (negativePart (rootParitySign T r) A)
        (positivePart (rootParitySign T r) B)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro q hq₁ hq₂
  have hdisj := Finset.disjoint_left.mp hAB
  simp only [betweenPairSet, positivePart, negativePart,
    Finset.mem_filter, Finset.mem_univ, true_and] at hq₁ hq₂
  rcases hq₁ with (hq₁ | hq₁) <;> rcases hq₂ with (hq₂ | hq₂)
  · omega
  · exact hdisj hq₁.1.1 hq₂.1.1
  · exact hdisj hq₁.2.1 hq₂.2.1
  · omega

/-- Odd pairs between two disjoint named vertex sets have the exact signed
cross-product count.  This is the generic algebra used in the first three
lines of `(B-odd)`. -/
theorem two_mul_oddPairCard_between {n : ℕ} (T : PosIntTree n)
    (r : Fin n) (A B : Finset (Fin n)) (hAB : Disjoint A B) :
    2 * (oddPairCard T (betweenPairSet A B) : ℤ) =
      ((A.card * B.card : ℕ) : ℤ) -
        signedMass (rootParitySign T r) A *
          signedMass (rootParitySign T r) B := by
  classical
  have hset := odd_between_filter_eq T r A B
  have hpairDisj := odd_between_union_disjoint T r A B hAB
  have hposnegAB : Disjoint
      (positivePart (rootParitySign T r) A)
      (negativePart (rootParitySign T r) B) :=
    Finset.disjoint_filter_filter hAB
  have hnegposAB : Disjoint
      (negativePart (rootParitySign T r) A)
      (positivePart (rootParitySign T r) B) :=
    Finset.disjoint_filter_filter hAB
  have hcard : oddPairCard T (betweenPairSet A B) =
      (positivePart (rootParitySign T r) A).card *
          (negativePart (rootParitySign T r) B).card +
        (negativePart (rootParitySign T r) A).card *
          (positivePart (rootParitySign T r) B).card := by
    unfold oddPairCard
    rw [hset, Finset.card_union_of_disjoint hpairDisj,
      betweenPairSet_card _ _ hposnegAB,
      betweenPairSet_card _ _ hnegposAB]
  have hsumA := positiveCount_add_negativeCount
    (rootParitySign T r) A (fun x hx => rootParitySign_pm T r x)
  have hsumB := positiveCount_add_negativeCount
    (rootParitySign T r) B (fun x hx => rootParitySign_pm T r x)
  have hmassA := signedMass_eq_count_sub
    (rootParitySign T r) A (fun x hx => rootParitySign_pm T r x)
  have hmassB := signedMass_eq_count_sub
    (rootParitySign T r) B (fun x hx => rootParitySign_pm T r x)
  have hsumA' :
      (positivePart (rootParitySign T r) A).card +
          (negativePart (rootParitySign T r) A).card = A.card := by
    simpa only [positiveCount, negativeCount, positivePart, negativePart]
      using hsumA
  have hsumB' :
      (positivePart (rootParitySign T r) B).card +
          (negativePart (rootParitySign T r) B).card = B.card := by
    simpa only [positiveCount, negativeCount, positivePart, negativePart]
      using hsumB
  have hmassA' : signedMass (rootParitySign T r) A =
      ((positivePart (rootParitySign T r) A).card : ℤ) -
        ((negativePart (rootParitySign T r) A).card : ℤ) := by
    simpa only [positiveCount, negativeCount, positivePart, negativePart]
      using hmassA
  have hmassB' : signedMass (rootParitySign T r) B =
      ((positivePart (rootParitySign T r) B).card : ℤ) -
        ((negativePart (rootParitySign T r) B).card : ℤ) := by
    simpa only [positiveCount, negativeCount, positivePart, negativePart]
      using hmassB
  have hcard' : (oddPairCard T (betweenPairSet A B) : ℤ) =
      ((positivePart (rootParitySign T r) A).card : ℤ) *
          ((negativePart (rootParitySign T r) B).card : ℤ) +
        ((negativePart (rootParitySign T r) A).card : ℤ) *
          ((positivePart (rootParitySign T r) B).card : ℤ) := by
    exact_mod_cast hcard
  have hsumA'' : (A.card : ℤ) =
      ((positivePart (rootParitySign T r) A).card : ℤ) +
        ((negativePart (rootParitySign T r) A).card : ℤ) := by
    exact_mod_cast hsumA'.symm
  have hsumB'' : (B.card : ℤ) =
      ((positivePart (rootParitySign T r) B).card : ℤ) +
        ((negativePart (rootParitySign T r) B).card : ℤ) := by
    exact_mod_cast hsumB'.symm
  rw [hcard', Nat.cast_mul, hsumA'', hsumB'', hmassA', hmassB']
  ring

private theorem odd_within_filter_eq {n : ℕ} (T : PosIntTree n)
    (r : Fin n) (A : Finset (Fin n)) :
    (withinPairSet A).filter (fun q => T.pairDist q % 2 = 1) =
      betweenPairSet
        (positivePart (rootParitySign T r) A)
        (negativePart (rootParitySign T r) A) := by
  classical
  ext q
  have hs := rootParitySign_pairDist T r q
  have hl := rootParitySign_pm T r q.left
  have hr := rootParitySign_pm T r q.right
  simp only [Finset.mem_filter]
  rw [← paritySign_eq_neg_one_iff_mod_two, ← hs]
  rcases hl with hl | hl <;> rcases hr with hr | hr <;>
    simp [withinPairSet, betweenPairSet, positivePart, negativePart, hl, hr]

/-- Odd unordered pairs internal to one named set satisfy the exact fourth
moment-free square identity used in the `00` line of `(B-odd)`. -/
theorem four_mul_oddPairCard_within {n : ℕ} (T : PosIntTree n)
    (r : Fin n) (A : Finset (Fin n)) :
    4 * (oddPairCard T (withinPairSet A) : ℤ) =
      (A.card : ℤ) ^ 2 - signedMass (rootParitySign T r) A ^ 2 := by
  classical
  have hdisj : Disjoint
      (positivePart (rootParitySign T r) A)
      (negativePart (rootParitySign T r) A) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    omega
  have hcard : oddPairCard T (withinPairSet A) =
      (positivePart (rootParitySign T r) A).card *
        (negativePart (rootParitySign T r) A).card := by
    unfold oddPairCard
    rw [odd_within_filter_eq T r A,
      betweenPairSet_card _ _ hdisj]
  have hsum := positiveCount_add_negativeCount
    (rootParitySign T r) A (fun x hx => rootParitySign_pm T r x)
  have hmass := signedMass_eq_count_sub
    (rootParitySign T r) A (fun x hx => rootParitySign_pm T r x)
  have hsum' :
      (positivePart (rootParitySign T r) A).card +
          (negativePart (rootParitySign T r) A).card = A.card := by
    simpa only [positiveCount, negativeCount, positivePart, negativePart]
      using hsum
  have hmass' : signedMass (rootParitySign T r) A =
      ((positivePart (rootParitySign T r) A).card : ℤ) -
        ((negativePart (rootParitySign T r) A).card : ℤ) := by
    simpa only [positiveCount, negativeCount, positivePart, negativePart]
      using hmass
  push_cast at hsum' hcard
  nlinarith [hmass']

theorem twoCut_components_pairwise_disjoint {n : ℕ}
    (T : PosIntTree n) (r : Fin n) (e f : T.Edge)
    (far_sub_near : ∀ x, OrientedCut.Away T r f x →
      OrientedCut.Away T r e x) :
    Disjoint (twoCutA T r e) (twoCutM T r e f) ∧
      Disjoint (twoCutA T r e) (twoCutB T r f) ∧
      Disjoint (twoCutM T r e f) (twoCutB T r f) := by
  classical
  constructor
  · exact Finset.disjoint_left.mpr <| by
      intro x hxA hxM
      simp only [twoCutA, rootOuterSet, Finset.mem_filter, Finset.mem_univ,
        true_and] at hxA
      simp only [twoCutM, Finset.mem_filter, Finset.mem_univ, true_and] at hxM
      exact hxA hxM.1
  constructor
  · exact Finset.disjoint_left.mpr <| by
      intro x hxA hxB
      simp only [twoCutA, rootOuterSet, Finset.mem_filter, Finset.mem_univ,
        true_and] at hxA
      simp only [twoCutB, awayOuterSet, Finset.mem_filter, Finset.mem_univ,
        true_and] at hxB
      exact hxA (far_sub_near x hxB)
  · exact Finset.disjoint_left.mpr <| by
      intro x hxM hxB
      simp only [twoCutM, Finset.mem_filter, Finset.mem_univ, true_and] at hxM
      simp only [twoCutB, awayOuterSet, Finset.mem_filter, Finset.mem_univ,
        true_and] at hxB
      exact hxM.2 hxB

/-- Exact identification of all three nonzero membership bins with the
actual deletion components `A--M--B`. -/
theorem twoCutPairBins_eq_between {n : ℕ} (T : PosIntTree n)
    (r : Fin n) (e f : T.Edge)
    (far_sub_near : ∀ x, OrientedCut.Away T r f x →
      OrientedCut.Away T r e x) :
    twoCutPairBin11 T e f = betweenPairSet (twoCutA T r e) (twoCutB T r f) ∧
    twoCutPairBin10 T e f = betweenPairSet (twoCutA T r e) (twoCutM T r e f) ∧
    twoCutPairBin01 T e f = betweenPairSet (twoCutM T r e f) (twoCutB T r f) := by
  classical
  have pointwise (q : VertexPair n) := And.intro
    (far_sub_near q.left) (far_sub_near q.right)
  constructor
  · ext q
    simp only [twoCutPairBin11, betweenPairSet, twoCutA, twoCutB,
      rootOuterSet, awayOuterSet, Finset.mem_filter, Finset.mem_univ,
      true_and]
    rw [OrientedCut.mem_pathEdges_iff_opposite_away,
      OrientedCut.mem_pathEdges_iff_opposite_away]
    have h := pointwise q
    tauto
  constructor
  · ext q
    simp only [twoCutPairBin10, betweenPairSet, twoCutA, twoCutM,
      rootOuterSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [OrientedCut.mem_pathEdges_iff_opposite_away,
      OrientedCut.mem_pathEdges_iff_opposite_away]
    have h := pointwise q
    tauto
  · ext q
    simp only [twoCutPairBin01, betweenPairSet, twoCutM, twoCutB,
      awayOuterSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [OrientedCut.mem_pathEdges_iff_opposite_away,
      OrientedCut.mem_pathEdges_iff_opposite_away]
    have h := pointwise q
    tauto

/-- The fourth membership bin is exactly the disjoint union of the three
within-component pair sets in the actual `A--M--B` decomposition. -/
theorem twoCutPairBin00_eq_within {n : ℕ} (T : PosIntTree n)
    (r : Fin n) (e f : T.Edge)
    (far_sub_near : ∀ x, OrientedCut.Away T r f x →
      OrientedCut.Away T r e x) :
    twoCutPairBin00 T e f =
      (withinPairSet (twoCutA T r e) ∪
        withinPairSet (twoCutM T r e f)) ∪
      withinPairSet (twoCutB T r f) := by
  classical
  ext q
  simp only [twoCutPairBin00, withinPairSet, twoCutA, twoCutM, twoCutB,
    rootOuterSet, awayOuterSet, Finset.mem_filter, Finset.mem_univ,
    Finset.mem_union, true_and]
  rw [OrientedCut.mem_pathEdges_iff_opposite_away,
    OrientedCut.mem_pathEdges_iff_opposite_away]
  have hl := far_sub_near q.left
  have hr := far_sub_near q.right
  tauto

private theorem withinPairSet_disjoint_of_disjoint {n : ℕ}
    {A B : Finset (Fin n)} (hAB : Disjoint A B) :
    Disjoint (withinPairSet A) (withinPairSet B) := by
  apply Finset.disjoint_left.mpr
  intro q hqA hqB
  exact Finset.disjoint_left.mp hAB
    (Finset.mem_filter.mp hqA).2.1 (Finset.mem_filter.mp hqB).2.1

theorem oddPairCard_union {n : ℕ} (T : PosIntTree n)
    {Q R : Finset (VertexPair n)} (hQR : Disjoint Q R) :
    oddPairCard T (Q ∪ R) = oddPairCard T Q + oddPairCard T R := by
  unfold oddPairCard
  rw [Finset.filter_union, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter hQR

/-- Literal division-free `(B-odd)` formulas for all four actual bins.  The
same common root character supplies `alpha,mu,beta`; no marginal signs are
chosen independently. -/
theorem actual_twoCut_AMB_odd_pair_formulas {n : ℕ}
    (T : PosIntTree n) (r : Fin n) (e f : T.Edge)
    (far_sub_near : ∀ x, OrientedCut.Away T r f x →
      OrientedCut.Away T r e x) :
    let A := twoCutA T r e
    let M := twoCutM T r e f
    let B := twoCutB T r f
    let alpha := signedMass (rootParitySign T r) A
    let mu := signedMass (rootParitySign T r) M
    let beta := signedMass (rootParitySign T r) B
    2 * (oddPairCard T (twoCutPairBin11 T e f) : ℤ) =
        ((A.card * B.card : ℕ) : ℤ) - alpha * beta ∧
    2 * (oddPairCard T (twoCutPairBin10 T e f) : ℤ) =
        ((A.card * M.card : ℕ) : ℤ) - alpha * mu ∧
    2 * (oddPairCard T (twoCutPairBin01 T e f) : ℤ) =
        ((B.card * M.card : ℕ) : ℤ) - beta * mu ∧
    4 * (oddPairCard T (twoCutPairBin00 T e f) : ℤ) =
        ((A.card : ℤ) ^ 2 - alpha ^ 2) +
        ((M.card : ℤ) ^ 2 - mu ^ 2) +
        ((B.card : ℤ) ^ 2 - beta ^ 2) := by
  dsimp only
  obtain ⟨hAM, hAB, hMB⟩ :=
    twoCut_components_pairwise_disjoint T r e f far_sub_near
  obtain ⟨h11, h10, h01⟩ :=
    twoCutPairBins_eq_between T r e f far_sub_near
  have h00 := twoCutPairBin00_eq_within T r e f far_sub_near
  have hWA_WM : Disjoint
      (withinPairSet (twoCutA T r e))
      (withinPairSet (twoCutM T r e f)) :=
    withinPairSet_disjoint_of_disjoint hAM
  have hWA_WB : Disjoint
      (withinPairSet (twoCutA T r e))
      (withinPairSet (twoCutB T r f)) :=
    withinPairSet_disjoint_of_disjoint hAB
  have hWM_WB : Disjoint
      (withinPairSet (twoCutM T r e f))
      (withinPairSet (twoCutB T r f)) :=
    withinPairSet_disjoint_of_disjoint hMB
  have hUnion : Disjoint
      (withinPairSet (twoCutA T r e) ∪
        withinPairSet (twoCutM T r e f))
      (withinPairSet (twoCutB T r f)) :=
    Finset.disjoint_union_left.mpr ⟨hWA_WB, hWM_WB⟩
  constructor
  · rw [h11]
    exact two_mul_oddPairCard_between T r _ _ hAB
  constructor
  · rw [h10]
    exact two_mul_oddPairCard_between T r _ _ hAM
  constructor
  · rw [h01]
    simpa only [Nat.mul_comm, mul_comm] using
      two_mul_oddPairCard_between T r _ _ hMB
  · rw [h00, oddPairCard_union T hUnion,
      oddPairCard_union T hWA_WM]
    have hA := four_mul_oddPairCard_within T r (twoCutA T r e)
    have hM := four_mul_oddPairCard_within T r (twoCutM T r e f)
    have hB := four_mul_oddPairCard_within T r (twoCutB T r f)
    push_cast
    linarith

/-- The displayed quotient form of `(B-odd)`, obtained from the exact
division-free identities above. -/
theorem actual_twoCut_AMB_odd_pair_formulas_div {n : ℕ}
    (T : PosIntTree n) (r : Fin n) (e f : T.Edge)
    (far_sub_near : ∀ x, OrientedCut.Away T r f x →
      OrientedCut.Away T r e x) :
    let A := twoCutA T r e
    let M := twoCutM T r e f
    let B := twoCutB T r f
    let alpha := signedMass (rootParitySign T r) A
    let mu := signedMass (rootParitySign T r) M
    let beta := signedMass (rootParitySign T r) B
    (oddPairCard T (twoCutPairBin11 T e f) : ℤ) =
        (((A.card * B.card : ℕ) : ℤ) - alpha * beta) / 2 ∧
    (oddPairCard T (twoCutPairBin10 T e f) : ℤ) =
        (((A.card * M.card : ℕ) : ℤ) - alpha * mu) / 2 ∧
    (oddPairCard T (twoCutPairBin01 T e f) : ℤ) =
        (((B.card * M.card : ℕ) : ℤ) - beta * mu) / 2 ∧
    (oddPairCard T (twoCutPairBin00 T e f) : ℤ) =
        (((A.card : ℤ) ^ 2 - alpha ^ 2) +
          ((M.card : ℤ) ^ 2 - mu ^ 2) +
          ((B.card : ℤ) ^ 2 - beta ^ 2)) / 4 := by
  dsimp only
  obtain ⟨h11, h10, h01, h00⟩ :=
    actual_twoCut_AMB_odd_pair_formulas T r e f far_sub_near
  constructor
  · rw [← h11]
    omega
  constructor
  · rw [← h10]
    omega
  constructor
  · rw [← h01]
    omega
  · rw [← h00]
    omega

def oddRankCard (S : Finset ℕ) : ℕ :=
  (S.filter Odd).card

/-- Injectivity of the Leech spectrum transfers the indexed odd-pair count
to the actual odd-rank count of every pair block. -/
theorem oddRankCard_image_pairDist {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) (Q : Finset (VertexPair n)) :
    oddRankCard (Q.image T.pairDist) = oddPairCard T Q := by
  classical
  have hset : (Q.image T.pairDist).filter Odd =
      (Q.filter fun q => T.pairDist q % 2 = 1).image T.pairDist := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨q, hq, rfl⟩, hodd⟩
      exact ⟨q, ⟨hq, Nat.odd_iff.mp hodd⟩, rfl⟩
    · rintro ⟨q, ⟨hq, hmod⟩, rfl⟩
      exact ⟨⟨q, hq, rfl⟩, Nat.odd_iff.mpr hmod⟩
  unfold oddRankCard oddPairCard
  rw [hset, Finset.card_image_of_injective _ hL.pairDist_injective]

/-- Literal odd-*rank* version of `(B-odd)` for the four occupied target
bins of an actual Leech tree. -/
theorem actual_twoCut_AMB_odd_rank_formulas_div {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) (r : Fin n) (e f : T.Edge)
    (far_sub_near : ∀ x, OrientedCut.Away T r f x →
      OrientedCut.Away T r e x) :
    let A := twoCutA T r e
    let M := twoCutM T r e f
    let B := twoCutB T r f
    let alpha := signedMass (rootParitySign T r) A
    let mu := signedMass (rootParitySign T r) M
    let beta := signedMass (rootParitySign T r) B
    (oddRankCard (twoCutRankBin11 T e f) : ℤ) =
        (((A.card * B.card : ℕ) : ℤ) - alpha * beta) / 2 ∧
    (oddRankCard (twoCutRankBin10 T e f) : ℤ) =
        (((A.card * M.card : ℕ) : ℤ) - alpha * mu) / 2 ∧
    (oddRankCard (twoCutRankBin01 T e f) : ℤ) =
        (((B.card * M.card : ℕ) : ℤ) - beta * mu) / 2 ∧
    (oddRankCard (twoCutRankBin00 T e f) : ℤ) =
        (((A.card : ℤ) ^ 2 - alpha ^ 2) +
          ((M.card : ℤ) ^ 2 - mu ^ 2) +
          ((B.card : ℤ) ^ 2 - beta ^ 2)) / 4 := by
  have hp := actual_twoCut_AMB_odd_pair_formulas_div T r e f far_sub_near
  dsimp only
  unfold twoCutRankBin11 twoCutRankBin10 twoCutRankBin01 twoCutRankBin00
  rw [oddRankCard_image_pairDist hL,
    oddRankCard_image_pairDist hL,
    oddRankCard_image_pairDist hL,
    oddRankCard_image_pairDist hL]
  simpa only using hp

/-- Literal `ab,am,bm` cardinal formulas for the actual A--M--B deletion
components. -/
theorem actual_twoCut_AMB_pair_cards {n : ℕ} (T : PosIntTree n)
    (r : Fin n) (e f : T.Edge)
    (far_sub_near : ∀ x, OrientedCut.Away T r f x →
      OrientedCut.Away T r e x) :
    (twoCutPairBin11 T e f).card =
        (twoCutA T r e).card * (twoCutB T r f).card ∧
    (twoCutPairBin10 T e f).card =
        (twoCutA T r e).card * (twoCutM T r e f).card ∧
    (twoCutPairBin01 T e f).card =
        (twoCutB T r f).card * (twoCutM T r e f).card := by
  obtain ⟨h11, h10, h01⟩ := twoCutPairBins_eq_between T r e f far_sub_near
  obtain ⟨hAM, hAB, hMB⟩ :=
    twoCut_components_pairwise_disjoint T r e f far_sub_near
  rw [h11, h10, h01, betweenPairSet_card _ _ hAB,
    betweenPairSet_card _ _ hAM, betweenPairSet_card _ _ hMB]
  simp [Nat.mul_comm]

/-- Under `IsLeech`, the same exact formulas hold for occupied target-rank
bins because the distance map is injective. -/
theorem actual_twoCut_AMB_rank_cards {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) (r : Fin n) (e f : T.Edge)
    (far_sub_near : ∀ x, OrientedCut.Away T r f x →
      OrientedCut.Away T r e x) :
    (twoCutRankBin11 T e f).card =
        (twoCutA T r e).card * (twoCutB T r f).card ∧
    (twoCutRankBin10 T e f).card =
        (twoCutA T r e).card * (twoCutM T r e f).card ∧
    (twoCutRankBin01 T e f).card =
        (twoCutB T r f).card * (twoCutM T r e f).card := by
  have hp := actual_twoCut_AMB_pair_cards T r e f far_sub_near
  have h11 : (twoCutRankBin11 T e f).card =
      (twoCutPairBin11 T e f).card :=
    Finset.card_image_of_injective _ hL.pairDist_injective
  have h10 : (twoCutRankBin10 T e f).card =
      (twoCutPairBin10 T e f).card :=
    Finset.card_image_of_injective _ hL.pairDist_injective
  have h01 : (twoCutRankBin01 T e f).card =
      (twoCutPairBin01 T e f).card :=
    Finset.card_image_of_injective _ hL.pairDist_injective
  rw [h11, h10, h01]
  exact hp

theorem twoCutRankBins_subset_target {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) (e f : T.Edge) :
    twoCutRankBin11 T e f ⊆ Finset.Icc 1 (targetN n) ∧
      twoCutRankBin10 T e f ⊆ Finset.Icc 1 (targetN n) ∧
      twoCutRankBin01 T e f ⊆ Finset.Icc 1 (targetN n) ∧
      twoCutRankBin00 T e f ⊆ Finset.Icc 1 (targetN n) := by
  constructor
  · intro d hd
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hd
    exact hL.pairDist_mem q
  constructor
  · intro d hd
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hd
    exact hL.pairDist_mem q
  constructor
  · intro d hd
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hd
    exact hL.pairDist_mem q
  · intro d hd
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hd
    exact hL.pairDist_mem q

theorem twoCutRankBins_pairwise_disjoint {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) (e f : T.Edge) :
    Disjoint (twoCutRankBin11 T e f) (twoCutRankBin10 T e f) ∧
      Disjoint (twoCutRankBin11 T e f) (twoCutRankBin01 T e f) ∧
      Disjoint (twoCutRankBin10 T e f) (twoCutRankBin01 T e f) := by
  classical
  have disjoint_of_incompatible
      (A B : Finset (VertexPair n))
      (hincompat : ∀ q, q ∈ A → q ∈ B → False) :
      Disjoint (A.image T.pairDist) (B.image T.pairDist) := by
    apply Finset.disjoint_left.mpr
    intro d hdA hdB
    obtain ⟨q, hqA, hqd⟩ := Finset.mem_image.mp hdA
    obtain ⟨q', hqB, hq'd⟩ := Finset.mem_image.mp hdB
    have hqq' := hL.pairDist_injective (hqd.trans hq'd.symm)
    subst q'
    exact hincompat q hqA hqB
  constructor
  · apply disjoint_of_incompatible
    intro q h11 h10
    exact (Finset.mem_filter.mp h10).2.2 (Finset.mem_filter.mp h11).2.2
  constructor
  · apply disjoint_of_incompatible
    intro q h11 h01
    exact (Finset.mem_filter.mp h01).2.1 (Finset.mem_filter.mp h11).2.1
  · apply disjoint_of_incompatible
    intro q h10 h01
    exact (Finset.mem_filter.mp h01).2.1 (Finset.mem_filter.mp h10).2.1

/-- Actual graph/model endpoint for the two-cut moment inequalities. -/
theorem actual_twoCut_powerMoment_bounds {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) (e f : T.Edge) (p : ℕ) :
    lowerPowerEnvelope (Finset.Icc 1 (targetN n)) p
        (twoCutRankBin10 T e f).card -
        upperPowerEnvelope (Finset.Icc 1 (targetN n)) p
          (twoCutRankBin01 T e f).card ≤
      powerMoment p (twoCutRankBin11 T e f ∪ twoCutRankBin10 T e f) -
        powerMoment p (twoCutRankBin11 T e f ∪ twoCutRankBin01 T e f) ∧
    powerMoment p (twoCutRankBin11 T e f ∪ twoCutRankBin10 T e f) -
        powerMoment p (twoCutRankBin11 T e f ∪ twoCutRankBin01 T e f) ≤
      upperPowerEnvelope (Finset.Icc 1 (targetN n)) p
        (twoCutRankBin10 T e f).card -
        lowerPowerEnvelope (Finset.Icc 1 (targetN n)) p
          (twoCutRankBin01 T e f).card ∧
    lowerPowerEnvelope (Finset.Icc 1 (targetN n)) p
        (twoCutRankBin11 T e f).card +
        lowerPowerEnvelope (Finset.Icc 1 (targetN n)) p
          ((twoCutRankBin11 T e f ∪ twoCutRankBin10 T e f) ∪
            twoCutRankBin01 T e f).card ≤
      powerMoment p (twoCutRankBin11 T e f ∪ twoCutRankBin10 T e f) +
        powerMoment p (twoCutRankBin11 T e f ∪ twoCutRankBin01 T e f) ∧
    powerMoment p (twoCutRankBin11 T e f ∪ twoCutRankBin10 T e f) +
        powerMoment p (twoCutRankBin11 T e f ∪ twoCutRankBin01 T e f) ≤
      upperPowerEnvelope (Finset.Icc 1 (targetN n)) p
        (twoCutRankBin11 T e f).card +
        upperPowerEnvelope (Finset.Icc 1 (targetN n)) p
          ((twoCutRankBin11 T e f ∪ twoCutRankBin10 T e f) ∪
            twoCutRankBin01 T e f).card := by
  obtain ⟨h11U, h10U, h01U, h00U⟩ :=
    twoCutRankBins_subset_target hL e f
  obtain ⟨h11_10, h11_01, h10_01⟩ :=
    twoCutRankBins_pairwise_disjoint hL e f
  exact coupled_twoCut_powerMoment_bounds _ _ _ _ p
    h11U h10U h01U h11_10 h11_01 h10_01

def actualTwoCutRankBin {n : ℕ} (T : PosIntTree n) (e f : T.Edge) :
    Fin 4 → Finset ℕ
  | 0 => twoCutRankBin11 T e f
  | 1 => twoCutRankBin10 T e f
  | 2 => twoCutRankBin01 T e f
  | 3 => twoCutRankBin00 T e f

theorem actualTwoCutRankBins_pairwise_disjoint {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) (e f : T.Edge) :
    ∀ {i j : Fin 4}, i ≠ j →
      Disjoint (actualTwoCutRankBin T e f i)
        (actualTwoCutRankBin T e f j) := by
  classical
  have disjoint_of_incompatible
      (A B : Finset (VertexPair n))
      (hincompat : ∀ q, q ∈ A → q ∈ B → False) :
      Disjoint (A.image T.pairDist) (B.image T.pairDist) := by
    apply Finset.disjoint_left.mpr
    intro d hdA hdB
    obtain ⟨q, hqA, hqd⟩ := Finset.mem_image.mp hdA
    obtain ⟨q', hqB, hq'd⟩ := Finset.mem_image.mp hdB
    have hqq' := hL.pairDist_injective (hqd.trans hq'd.symm)
    subst q'
    exact hincompat q hqA hqB
  intro i j hij
  fin_cases i <;> fin_cases j <;> try { exact (hij rfl).elim }
  all_goals
    apply disjoint_of_incompatible
    intro q hq hq'
    simp only [twoCutPairBin11, twoCutPairBin10, twoCutPairBin01,
      twoCutPairBin00, Finset.mem_filter, Finset.mem_univ, true_and] at hq hq'
    tauto

theorem actualTwoCutRankBins_cover {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) (e f : T.Edge) :
    Finset.univ.biUnion (actualTwoCutRankBin T e f) =
      Finset.Icc 1 (targetN n) := by
  classical
  apply Finset.ext
  intro d
  constructor
  · intro hd
    obtain ⟨i, hi, hdi⟩ := Finset.mem_biUnion.mp hd
    fin_cases i
    · exact (twoCutRankBins_subset_target hL e f).1 hdi
    · exact (twoCutRankBins_subset_target hL e f).2.1 hdi
    · exact (twoCutRankBins_subset_target hL e f).2.2.1 hdi
    · exact (twoCutRankBins_subset_target hL e f).2.2.2 hdi
  · intro hd
    let q : VertexPair n := (hL.spectrumEquiv).symm ⟨d, hd⟩
    have hqd : T.pairDist q = d := by
      exact congrArg Subtype.val ((hL.spectrumEquiv).apply_symm_apply ⟨d, hd⟩)
    by_cases he : e.1 ∈ T.pathEdges q.left q.right
    · by_cases hf : f.1 ∈ T.pathEdges q.left q.right
      · apply Finset.mem_biUnion.mpr
        refine ⟨0, Finset.mem_univ _, ?_⟩
        exact Finset.mem_image.mpr ⟨q, by
          simp [twoCutPairBin11, he, hf], hqd⟩
      · apply Finset.mem_biUnion.mpr
        refine ⟨1, Finset.mem_univ _, ?_⟩
        exact Finset.mem_image.mpr ⟨q, by
          simp [twoCutPairBin10, he, hf], hqd⟩
    · by_cases hf : f.1 ∈ T.pathEdges q.left q.right
      · apply Finset.mem_biUnion.mpr
        refine ⟨2, Finset.mem_univ _, ?_⟩
        exact Finset.mem_image.mpr ⟨q, by
          simp [twoCutPairBin01, he, hf], hqd⟩
      · apply Finset.mem_biUnion.mpr
        refine ⟨3, Finset.mem_univ _, ?_⟩
        exact Finset.mem_image.mpr ⟨q, by
          simp [twoCutPairBin00, he, hf], hqd⟩

/-- Exact moment readout of the actual DP state: the two cut moments share
the `11` bin and differ only by `10` versus `01`. -/
theorem actualTwoCutAllocation_moment_equations {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) (e f : T.Edge) (p : ℕ) :
    powerMoment p (twoCutRankBin11 T e f ∪ twoCutRankBin10 T e f) -
        powerMoment p (twoCutRankBin11 T e f ∪ twoCutRankBin01 T e f) =
      powerMoment p (twoCutRankBin10 T e f) -
        powerMoment p (twoCutRankBin01 T e f) ∧
    powerMoment p (twoCutRankBin11 T e f ∪ twoCutRankBin10 T e f) +
        powerMoment p (twoCutRankBin11 T e f ∪ twoCutRankBin01 T e f) =
      2 * powerMoment p (twoCutRankBin11 T e f) +
        powerMoment p (twoCutRankBin10 T e f) +
        powerMoment p (twoCutRankBin01 T e f) := by
  obtain ⟨h11_10, h11_01, h10_01⟩ :=
    twoCutRankBins_pairwise_disjoint hL e f
  rw [powerMoment_union p h11_10, powerMoment_union p h11_01]
  constructor <;> ring

/-- Exact physical-weight placement in the three nonzero two-cut bins. -/
theorem twoCut_physical_bins {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) {e f : T.Edge} (hef : e ≠ f) :
    twoCutRankBin11 T e f ∩ physicalWeightSet T = ∅ ∧
      twoCutRankBin10 T e f ∩ physicalWeightSet T = {T.weight e} ∧
      twoCutRankBin01 T e f ∩ physicalWeightSet T = {T.weight f} := by
  classical
  have h11 :
      twoCutRankBin11 T e f = selectedPathDistanceSet T {e, f} := by
    unfold twoCutRankBin11 selectedPathDistanceSet
    apply congrArg (Finset.image T.pairDist)
    ext q
    simp [twoCutPairBin11, pathSupport]
  have hcard : ({e, f} : Finset T.Edge).card = 2 := by simp [hef]
  constructor
  · rw [h11]
    exact selectedPathDistance_inter_physical_eq_empty_of_two_le hL
      (by omega)
  constructor
  · apply Finset.ext
    intro d
    constructor
    · intro hd
      obtain ⟨hbin, hphys⟩ := Finset.mem_inter.mp hd
      obtain ⟨q, hq, hqd⟩ := Finset.mem_image.mp hbin
      obtain ⟨g, hg, hgd⟩ := Finset.mem_image.mp hphys
      have hqg : q = T.edgePair g := hL.pairDist_injective <| by
        simpa using hqd.trans hgd.symm
      have hdata := (Finset.mem_filter.mp hq).2
      have heg : e = g := by
        have := hdata.1
        rw [hqg] at this
        change e.1 ∈ T.pathEdges (T.edgeLeft g) (T.edgeRight g) at this
        rw [T.pathEdges_edge g] at this
        exact Subtype.ext (Finset.mem_singleton.mp this)
      subst g
      exact Finset.mem_singleton.mpr hgd.symm
    · intro hd
      have hdw := Finset.mem_singleton.mp hd
      subst d
      apply Finset.mem_inter.mpr
      constructor
      · apply Finset.mem_image.mpr
        refine ⟨T.edgePair e, ?_, T.edgePair_dist e⟩
        apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_univ _
        constructor
        · simp [T.pathEdges_edge e]
        · change f.1 ∉ T.pathEdges (T.edgeLeft e) (T.edgeRight e)
          rw [T.pathEdges_edge e]
          simp only [Finset.mem_singleton]
          intro hval
          exact hef (Subtype.ext hval.symm)
      · exact weight_mem_physicalWeightSet T e
  · apply Finset.ext
    intro d
    constructor
    · intro hd
      obtain ⟨hbin, hphys⟩ := Finset.mem_inter.mp hd
      obtain ⟨q, hq, hqd⟩ := Finset.mem_image.mp hbin
      obtain ⟨g, hg, hgd⟩ := Finset.mem_image.mp hphys
      have hqg : q = T.edgePair g := hL.pairDist_injective <| by
        simpa using hqd.trans hgd.symm
      have hdata := (Finset.mem_filter.mp hq).2
      have hfg : f = g := by
        have := hdata.2
        rw [hqg] at this
        change f.1 ∈ T.pathEdges (T.edgeLeft g) (T.edgeRight g) at this
        rw [T.pathEdges_edge g] at this
        exact Subtype.ext (Finset.mem_singleton.mp this)
      subst g
      exact Finset.mem_singleton.mpr hgd.symm
    · intro hd
      have hdw := Finset.mem_singleton.mp hd
      subst d
      apply Finset.mem_inter.mpr
      constructor
      · apply Finset.mem_image.mpr
        refine ⟨T.edgePair f, ?_, T.edgePair_dist f⟩
        apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_univ _
        constructor
        · change e.1 ∉ T.pathEdges (T.edgeLeft f) (T.edgeRight f)
          rw [T.pathEdges_edge f]
          simp only [Finset.mem_singleton]
          intro hval
          exact hef (Subtype.ext hval)
        · simp [T.pathEdges_edge f]
      · exact weight_mem_physicalWeightSet T f

/-- Exact physical placement in the fourth bin. -/
theorem twoCut_physical_bin00 {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) (e f : T.Edge) :
    twoCutRankBin00 T e f ∩ physicalWeightSet T =
      physicalWeightSet T \ {T.weight e, T.weight f} := by
  classical
  apply Finset.ext
  intro d
  constructor
  · intro hd
    obtain ⟨hbin, hphys⟩ := Finset.mem_inter.mp hd
    obtain ⟨q, hq, hqd⟩ := Finset.mem_image.mp hbin
    obtain ⟨g, hg, hgd⟩ := Finset.mem_image.mp hphys
    have hqg : q = T.edgePair g := hL.pairDist_injective <| by
      simpa using hqd.trans hgd.symm
    have hdata := (Finset.mem_filter.mp hq).2
    have heg : e ≠ g := by
      intro heq
      subst g
      exact hdata.1 (by simp [hqg, T.pathEdges_edge e])
    have hfg : f ≠ g := by
      intro heq
      subst g
      exact hdata.2 (by simp [hqg, T.pathEdges_edge f])
    apply Finset.mem_sdiff.mpr
    refine ⟨hphys, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro hde
      apply heg
      apply t1_edge_weight_injective hL
      exact (hgd.trans hde).symm
    · intro hdf
      apply hfg
      apply t1_edge_weight_injective hL
      exact (hgd.trans hdf).symm
  · intro hd
    obtain ⟨hphys, hnot⟩ := Finset.mem_sdiff.mp hd
    obtain ⟨g, hg, hgd⟩ := Finset.mem_image.mp hphys
    have hne : g ≠ e ∧ g ≠ f := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
      constructor
      · intro hge
        apply hnot.1
        simpa [hge] using hgd.symm
      · intro hgf
        apply hnot.2
        simpa [hgf] using hgd.symm
    apply Finset.mem_inter.mpr
    constructor
    · apply Finset.mem_image.mpr
      refine ⟨T.edgePair g, ?_, (T.edgePair_dist g).trans hgd⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · change e.1 ∉ T.pathEdges (T.edgeLeft g) (T.edgeRight g)
        rw [T.pathEdges_edge g]
        simp only [Finset.mem_singleton]
        intro hval
        exact hne.1 (Subtype.ext hval.symm)
      · change f.1 ∉ T.pathEdges (T.edgeLeft g) (T.edgeRight g)
        rw [T.pathEdges_edge g]
        simp only [Finset.mem_singleton]
        intro hval
        exact hne.2 (Subtype.ext hval.symm)
    · exact hphys
/-! ## Exact four-bin allocation form -/

/-- An exact disjoint four-bin allocation of one finite target pool. -/
structure FourBinAllocation (U : Finset ℕ) where
  bin : Fin 4 → Finset ℕ
  subset_target : ∀ i, bin i ⊆ U
  pairwise_disjoint : ∀ {i j : Fin 4}, i ≠ j → Disjoint (bin i) (bin j)
  covers : Finset.univ.biUnion bin = U

/-- The actual four target-rank bins form a certified exact DP allocation. -/
noncomputable def actualTwoCutAllocation {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) (e f : T.Edge) :
    FourBinAllocation (Finset.Icc 1 (targetN n)) where
  bin := actualTwoCutRankBin T e f
  subset_target := by
    intro i
    fin_cases i
    · exact (twoCutRankBins_subset_target hL e f).1
    · exact (twoCutRankBins_subset_target hL e f).2.1
    · exact (twoCutRankBins_subset_target hL e f).2.2.1
    · exact (twoCutRankBins_subset_target hL e f).2.2.2
  pairwise_disjoint := actualTwoCutRankBins_pairwise_disjoint hL e f
  covers := actualTwoCutRankBins_cover hL e f

/-- Complete exact cardinal readout of the actual A--M--B DP state, including
the complement bin `N-ab-am-bm`. -/
theorem actualTwoCutAllocation_AMB_cards {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) (r : Fin n) (e f : T.Edge)
    (far_sub_near : ∀ x, OrientedCut.Away T r f x →
      OrientedCut.Away T r e x) :
    let a := (twoCutA T r e).card
    let m := (twoCutM T r e f).card
    let b := (twoCutB T r f).card
    ((actualTwoCutAllocation hL e f).bin 0).card = a * b ∧
    ((actualTwoCutAllocation hL e f).bin 1).card = a * m ∧
    ((actualTwoCutAllocation hL e f).bin 2).card = b * m ∧
    ((actualTwoCutAllocation hL e f).bin 3).card =
      targetN n - a * b - a * m - b * m := by
  dsimp only
  obtain ⟨h11, h10, h01⟩ :=
    actual_twoCut_AMB_rank_cards hL r e f far_sub_near
  have h11_10 : Disjoint (twoCutRankBin11 T e f)
      (twoCutRankBin10 T e f) :=
    actualTwoCutRankBins_pairwise_disjoint hL e f
      (i := 0) (j := 1) (by decide)
  have h11_01 : Disjoint (twoCutRankBin11 T e f)
      (twoCutRankBin01 T e f) :=
    actualTwoCutRankBins_pairwise_disjoint hL e f
      (i := 0) (j := 2) (by decide)
  have h10_01 : Disjoint (twoCutRankBin10 T e f)
      (twoCutRankBin01 T e f) :=
    actualTwoCutRankBins_pairwise_disjoint hL e f
      (i := 1) (j := 2) (by decide)
  have h11_00 : Disjoint (twoCutRankBin11 T e f)
      (twoCutRankBin00 T e f) :=
    actualTwoCutRankBins_pairwise_disjoint hL e f
      (i := 0) (j := 3) (by decide)
  have h10_00 : Disjoint (twoCutRankBin10 T e f)
      (twoCutRankBin00 T e f) :=
    actualTwoCutRankBins_pairwise_disjoint hL e f
      (i := 1) (j := 3) (by decide)
  have h01_00 : Disjoint (twoCutRankBin01 T e f)
      (twoCutRankBin00 T e f) :=
    actualTwoCutRankBins_pairwise_disjoint hL e f
      (i := 2) (j := 3) (by decide)
  have hcover :
      ((twoCutRankBin11 T e f ∪ twoCutRankBin10 T e f) ∪
          twoCutRankBin01 T e f) ∪ twoCutRankBin00 T e f =
        Finset.Icc 1 (targetN n) := by
    rw [← actualTwoCutRankBins_cover hL e f]
    apply Finset.ext
    intro d
    constructor
    · intro hd
      simp only [Finset.mem_union] at hd
      rcases hd with ((h11d | h10d) | h01d) | h00d
      · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ _, h11d⟩
      · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ _, h10d⟩
      · exact Finset.mem_biUnion.mpr ⟨2, Finset.mem_univ _, h01d⟩
      · exact Finset.mem_biUnion.mpr ⟨3, Finset.mem_univ _, h00d⟩
    · intro hd
      obtain ⟨i, hi, hid⟩ := Finset.mem_biUnion.mp hd
      fin_cases i
      · apply Finset.mem_union.mpr
        left
        apply Finset.mem_union.mpr
        left
        apply Finset.mem_union.mpr
        left
        simpa only [actualTwoCutRankBin] using hid
      · apply Finset.mem_union.mpr
        left
        apply Finset.mem_union.mpr
        left
        apply Finset.mem_union.mpr
        right
        simpa only [actualTwoCutRankBin] using hid
      · apply Finset.mem_union.mpr
        left
        apply Finset.mem_union.mpr
        right
        simpa only [actualTwoCutRankBin] using hid
      · apply Finset.mem_union.mpr
        right
        simpa only [actualTwoCutRankBin] using hid
  have hcard := congrArg Finset.card hcover
  rw [Finset.card_union_of_disjoint
        (Finset.disjoint_union_left.mpr ⟨
          Finset.disjoint_union_left.mpr ⟨h11_00, h10_00⟩, h01_00⟩),
      Finset.card_union_of_disjoint
        (Finset.disjoint_union_left.mpr ⟨h11_01, h10_01⟩),
      Finset.card_union_of_disjoint h11_10] at hcard
  simp at hcard
  change (twoCutRankBin11 T e f).card = _ ∧
    (twoCutRankBin10 T e f).card = _ ∧
    (twoCutRankBin01 T e f).card = _ ∧
    (twoCutRankBin00 T e f).card = _
  refine ⟨h11, h10, h01, ?_⟩
  omega

/-- Complete physical-rank readout `(∅,{w_e},{w_f},W\{w_e,w_f})` of the
same actual DP state. -/
theorem actualTwoCutAllocation_physical_parts {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) {e f : T.Edge} (hef : e ≠ f) :
    (actualTwoCutAllocation hL e f).bin 0 ∩ physicalWeightSet T = ∅ ∧
    (actualTwoCutAllocation hL e f).bin 1 ∩ physicalWeightSet T =
      {T.weight e} ∧
    (actualTwoCutAllocation hL e f).bin 2 ∩ physicalWeightSet T =
      {T.weight f} ∧
    (actualTwoCutAllocation hL e f).bin 3 ∩ physicalWeightSet T =
      physicalWeightSet T \ {T.weight e, T.weight f} := by
  obtain ⟨h11, h10, h01⟩ := twoCut_physical_bins hL hef
  exact ⟨h11, h10, h01, twoCut_physical_bin00 hL e f⟩

/-- The bin cut out by one total four-way label of the target ranks.  The
existential proof in the predicate is proof-irrelevant, so this definition
does not choose a second copy of a target rank. -/
def fourBinOfLabel (U : Finset ℕ) (label : {d // d ∈ U} → Fin 4)
    (i : Fin 4) : Finset ℕ :=
  U.filter fun d => ∃ hd : d ∈ U, label ⟨d, hd⟩ = i

@[simp] theorem mem_fourBinOfLabel (U : Finset ℕ)
    (label : {d // d ∈ U} → Fin 4) (i : Fin 4) (d : ℕ) :
    d ∈ fourBinOfLabel U label i ↔
      ∃ hd : d ∈ U, label ⟨d, hd⟩ = i := by
  classical
  simp [fourBinOfLabel]

/-- Every total label gives an exact disjoint four-bin cover. -/
noncomputable def fourBinAllocationOfLabel (U : Finset ℕ)
    (label : {d // d ∈ U} → Fin 4) : FourBinAllocation U where
  bin := fourBinOfLabel U label
  subset_target := by
    intro i d hd
    exact (Finset.mem_filter.mp hd).1
  pairwise_disjoint := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro d hdi hdj
    obtain ⟨hU, ei⟩ := (mem_fourBinOfLabel U label i d).mp hdi
    obtain ⟨_hU, ej⟩ := (mem_fourBinOfLabel U label j d).mp hdj
    exact hij (ei.symm.trans ej)
  covers := by
    apply Finset.ext
    intro d
    constructor
    · intro hd
      obtain ⟨i, hi, hdi⟩ := Finset.mem_biUnion.mp hd
      exact (Finset.mem_filter.mp hdi).1
    · intro hd
      apply Finset.mem_biUnion.mpr
      refine ⟨label ⟨d, hd⟩, Finset.mem_univ _, ?_⟩
      exact (mem_fourBinOfLabel U label _ d).mpr ⟨hd, rfl⟩

/-- Exact data checked by the gap-free four-bin DP: prescribed cardinality,
power moments, parity counts, and the complete physical-rank intersection of
each bin. -/
structure FourBinSpecification (U physical : Finset ℕ) where
  card : Fin 4 → ℕ
  /-- The finite set of power moments actually checked by the DP. -/
  powers : Finset ℕ
  moment : ℕ → Fin 4 → ℤ
  oddCard : Fin 4 → ℕ
  physicalPart : Fin 4 → Finset ℕ
  physicalPart_subset : ∀ i, physicalPart i ⊆ physical

/-- A concrete allocation realizes every DP constraint, not merely a label. -/
def FourBinAllocation.Realizes {U physical : Finset ℕ}
    (A : FourBinAllocation U) (S : FourBinSpecification U physical) : Prop :=
  (∀ i, (A.bin i).card = S.card i) ∧
  (∀ p ∈ S.powers, ∀ i, powerMoment p (A.bin i) = S.moment p i) ∧
  (∀ i, ((A.bin i).filter Odd).card = S.oddCard i) ∧
  (∀ i, A.bin i ∩ physical = S.physicalPart i)

/-- The decidable constraint predicate used by the recursive enumerator. -/
def FourBinLabelRealizes (U physical : Finset ℕ)
    (label : {d // d ∈ U} → Fin 4)
    (S : FourBinSpecification U physical) : Prop :=
  (∀ i, (fourBinOfLabel U label i).card = S.card i) ∧
  (∀ p ∈ S.powers, ∀ i,
    powerMoment p (fourBinOfLabel U label i) = S.moment p i) ∧
  (∀ i, ((fourBinOfLabel U label i).filter Odd).card = S.oddCard i) ∧
  (∀ i, fourBinOfLabel U label i ∩ physical = S.physicalPart i)

theorem fourBinLabelRealizes_iff (U physical : Finset ℕ)
    (label : {d // d ∈ U} → Fin 4)
    (S : FourBinSpecification U physical) :
    FourBinLabelRealizes U physical label S ↔
      (fourBinAllocationOfLabel U label).Realizes S := by
  rfl

/-- A successful exact DP state is literally a total target-rank label whose
induced disjoint bins realize all requested constraints.  This replaces the
vacuous existence-of-a-label statement. -/
theorem exactFourBinDP_iff_label
    (U physical : Finset ℕ) (S : FourBinSpecification U physical) :
    (∃ A : FourBinAllocation U, A.Realizes S) ↔
      ∃ label : {d // d ∈ U} → Fin 4,
        (fourBinAllocationOfLabel U label).Realizes S := by
  constructor
  · rintro ⟨A, hA⟩
    classical
    have hdCover (d : {d // d ∈ U}) :
        d.1 ∈ Finset.univ.biUnion A.bin := by
      rw [A.covers]
      exact d.2
    let label : {d // d ∈ U} → Fin 4 := fun d =>
      Classical.choose (Finset.mem_biUnion.mp (hdCover d))
    have hbin : ∀ i, (fourBinAllocationOfLabel U label).bin i = A.bin i := by
      intro i
      apply Finset.ext
      intro d
      constructor
      · intro hd
        obtain ⟨hU, hi⟩ := (mem_fourBinOfLabel U label i d).mp hd
        have hchosen : d ∈ A.bin (label ⟨d, hU⟩) :=
          (Classical.choose_spec
            (Finset.mem_biUnion.mp (hdCover ⟨d, hU⟩))).2
        simpa [hi] using hchosen
      · intro hd
        have hU := A.subset_target i hd
        have hchosen : d ∈ A.bin (label ⟨d, hU⟩) :=
          (Classical.choose_spec
            (Finset.mem_biUnion.mp (hdCover ⟨d, hU⟩))).2
        have heq : label ⟨d, hU⟩ = i := by
          by_contra hne
          exact Finset.disjoint_left.mp (A.pairwise_disjoint hne) hchosen hd
        exact (mem_fourBinOfLabel U label i d).mpr ⟨hU, heq⟩
    refine ⟨label, ?_⟩
    simpa only [FourBinAllocation.Realizes, hbin] using hA
  · rintro ⟨label, hlabel⟩
    exact ⟨fourBinAllocationOfLabel U label, hlabel⟩

/-- The exact finite specification read directly from the actual graph bins.
Its fields remain independently queryable through the cardinal, odd-rank,
moment, and physical-placement theorems proved above. -/
noncomputable def actualTwoCutFourBinSpecification {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) (e f : T.Edge)
    (powers : Finset ℕ) :
    FourBinSpecification (Finset.Icc 1 (targetN n)) (physicalWeightSet T) where
  card i := ((actualTwoCutAllocation hL e f).bin i).card
  powers := powers
  moment p i := powerMoment p ((actualTwoCutAllocation hL e f).bin i)
  oddCard i := (((actualTwoCutAllocation hL e f).bin i).filter Odd).card
  physicalPart i :=
    (actualTwoCutAllocation hL e f).bin i ∩ physicalWeightSet T
  physicalPart_subset := by
    intro i d hd
    exact (Finset.mem_inter.mp hd).2

theorem actualTwoCutAllocation_realizes_specification {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) (e f : T.Edge)
    (powers : Finset ℕ) :
    (actualTwoCutAllocation hL e f).Realizes
      (actualTwoCutFourBinSpecification hL e f powers) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    rfl
  · intro p hp i
    rfl
  · intro i
    rfl
  · intro i
    rfl

/-! ### A genuine finite recursive four-bin DP

The preceding equivalence is semantic.  The following state generator is the
gap-free executable search promised in G006: it processes the ordered target
ranks one at a time and branches over the four possible labels. -/

/-- All partial four-label functions obtained by recursively assigning the
elements of `xs`.  Values outside `xs` remain at the base label zero. -/
def recursiveFourBinLabels {α : Type*} [Fintype α] [DecidableEq α] :
    List α → Finset (α → Fin 4)
  | [] => {fun _ => 0}
  | x :: xs =>
      (recursiveFourBinLabels xs).biUnion fun label =>
        Finset.univ.image fun i : Fin 4 => Function.update label x i

/-- Completeness of the recursive branching process, with an explicit
off-list invariant. -/
theorem mem_recursiveFourBinLabels_of_eq_zero_off
    {α : Type*} [Fintype α] [DecidableEq α]
    (xs : List α) (label : α → Fin 4)
    (hoff : ∀ a, a ∉ xs → label a = 0) :
    label ∈ recursiveFourBinLabels xs := by
  induction xs generalizing label with
  | nil =>
      have hzero : label = fun _ => 0 := by
        funext a
        exact hoff a (by simp)
      simp [recursiveFourBinLabels, hzero]
  | cons x xs ih =>
      let prior : α → Fin 4 := Function.update label x 0
      have hprior : ∀ a, a ∉ xs → prior a = 0 := by
        intro a ha
        by_cases hax : a = x
        · subst a
          simp [prior]
        · have hacons : a ∉ x :: xs := by simp [hax, ha]
          simp [prior, hax, hoff a hacons]
      have hmem : prior ∈ recursiveFourBinLabels xs := ih prior hprior
      apply Finset.mem_biUnion.mpr
      refine ⟨prior, hmem, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨label x, Finset.mem_univ _, ?_⟩
      funext a
      by_cases hax : a = x
      · subst a
        simp [prior]
      · simp [prior, hax]

/-- Canonical increasing list of all target-rank slots. -/
def fourBinTargetList (U : Finset ℕ) : List {d // d ∈ U} :=
  (Finset.univ : Finset {d // d ∈ U}).sort (· ≤ ·)

/-- The complete recursively generated label state space for `U`. -/
def exactFourBinLabelStates (U : Finset ℕ) :
    Finset ({d // d ∈ U} → Fin 4) :=
  recursiveFourBinLabels (fourBinTargetList U)

theorem label_mem_exactFourBinLabelStates (U : Finset ℕ)
    (label : {d // d ∈ U} → Fin 4) :
    label ∈ exactFourBinLabelStates U := by
  apply mem_recursiveFourBinLabels_of_eq_zero_off
  intro d hd
  exfalso
  apply hd
  simp [fourBinTargetList]

/-- The concrete DP result: the finite set of recursively generated labels
which pass every requested cardinal, selected power-moment, parity, and
physical-intersection check. -/
noncomputable def exactFourBinRecursiveDP (U physical : Finset ℕ)
    (S : FourBinSpecification U physical) :
    Finset ({d // d ∈ U} → Fin 4) := by
  classical
  exact (exactFourBinLabelStates U).filter fun label =>
    FourBinLabelRealizes U physical label S

/-- Gap-free soundness and completeness of the actual recursive finite DP. -/
theorem exactFourBinRecursiveDP_nonempty_iff
    (U physical : Finset ℕ) (S : FourBinSpecification U physical) :
    (exactFourBinRecursiveDP U physical S).Nonempty ↔
      ∃ A : FourBinAllocation U, A.Realizes S := by
  classical
  rw [exactFourBinDP_iff_label]
  constructor
  · rintro ⟨label, hlabel⟩
    change label ∈ (exactFourBinLabelStates U).filter
      (fun label => FourBinLabelRealizes U physical label S) at hlabel
    have hreal := (Finset.mem_filter.mp hlabel).2
    exact ⟨label, (fourBinLabelRealizes_iff U physical label S).mp hreal⟩
  · rintro ⟨label, hreal⟩
    refine ⟨label, ?_⟩
    change label ∈ (exactFourBinLabelStates U).filter
      (fun label => FourBinLabelRealizes U physical label S)
    exact Finset.mem_filter.mpr ⟨label_mem_exactFourBinLabelStates U label,
      (fourBinLabelRealizes_iff U physical label S).mpr hreal⟩

/-- Actual graph specialization of the recursive DP: for every finite family
of requested moments, the state generated by the real two-cut partition is
present in the gap-free recursive search. -/
theorem actualTwoCut_recursiveDP_nonempty {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) (e f : T.Edge)
    (powers : Finset ℕ) :
    (exactFourBinRecursiveDP
      (Finset.Icc 1 (targetN n)) (physicalWeightSet T)
      (actualTwoCutFourBinSpecification hL e f powers)).Nonempty := by
  apply (exactFourBinRecursiveDP_nonempty_iff _ _ _).2
  exact ⟨actualTwoCutAllocation hL e f,
    actualTwoCutAllocation_realizes_specification hL e f powers⟩

/-- One no-premise graph endpoint for G006.  It chooses the genuine
`A--M--B` orientation internally and exposes exact bin sizes, all four
signed odd-rank formulas, the two moment identities, physical placement, and
the successful recursive DP state. -/
structure ActualTwoCutGraphConclusion {n : ℕ}
    (T : PosIntTree n) (hL : IsLeech T)
    (e f : T.Edge) (hef : e ≠ f) where
  orientation : ActualTwoCutAMBOrientation T e f
  rankCards :
    (twoCutRankBin11 T orientation.near orientation.far).card =
        (twoCutA T orientation.root orientation.near).card *
          (twoCutB T orientation.root orientation.far).card ∧
    (twoCutRankBin10 T orientation.near orientation.far).card =
        (twoCutA T orientation.root orientation.near).card *
          (twoCutM T orientation.root orientation.near orientation.far).card ∧
    (twoCutRankBin01 T orientation.near orientation.far).card =
        (twoCutB T orientation.root orientation.far).card *
          (twoCutM T orientation.root orientation.near orientation.far).card ∧
    (twoCutRankBin00 T orientation.near orientation.far).card =
      targetN n -
        (twoCutA T orientation.root orientation.near).card *
          (twoCutB T orientation.root orientation.far).card -
        (twoCutA T orientation.root orientation.near).card *
          (twoCutM T orientation.root orientation.near orientation.far).card -
        (twoCutB T orientation.root orientation.far).card *
          (twoCutM T orientation.root orientation.near orientation.far).card
  oddRankFormulas :
    let A := twoCutA T orientation.root orientation.near
    let M := twoCutM T orientation.root orientation.near orientation.far
    let B := twoCutB T orientation.root orientation.far
    let alpha := signedMass (rootParitySign T orientation.root) A
    let mu := signedMass (rootParitySign T orientation.root) M
    let beta := signedMass (rootParitySign T orientation.root) B
    (oddRankCard (twoCutRankBin11 T orientation.near orientation.far) : ℤ) =
        (((A.card * B.card : ℕ) : ℤ) - alpha * beta) / 2 ∧
    (oddRankCard (twoCutRankBin10 T orientation.near orientation.far) : ℤ) =
        (((A.card * M.card : ℕ) : ℤ) - alpha * mu) / 2 ∧
    (oddRankCard (twoCutRankBin01 T orientation.near orientation.far) : ℤ) =
        (((B.card * M.card : ℕ) : ℤ) - beta * mu) / 2 ∧
    (oddRankCard (twoCutRankBin00 T orientation.near orientation.far) : ℤ) =
        (((A.card : ℤ) ^ 2 - alpha ^ 2) +
          ((M.card : ℤ) ^ 2 - mu ^ 2) +
          ((B.card : ℤ) ^ 2 - beta ^ 2)) / 4
  momentEquations : ∀ p,
    powerMoment p
        (twoCutRankBin11 T orientation.near orientation.far ∪
          twoCutRankBin10 T orientation.near orientation.far) -
        powerMoment p
          (twoCutRankBin11 T orientation.near orientation.far ∪
            twoCutRankBin01 T orientation.near orientation.far) =
      powerMoment p (twoCutRankBin10 T orientation.near orientation.far) -
        powerMoment p (twoCutRankBin01 T orientation.near orientation.far) ∧
    powerMoment p
        (twoCutRankBin11 T orientation.near orientation.far ∪
          twoCutRankBin10 T orientation.near orientation.far) +
        powerMoment p
          (twoCutRankBin11 T orientation.near orientation.far ∪
            twoCutRankBin01 T orientation.near orientation.far) =
      2 * powerMoment p
          (twoCutRankBin11 T orientation.near orientation.far) +
        powerMoment p (twoCutRankBin10 T orientation.near orientation.far) +
        powerMoment p (twoCutRankBin01 T orientation.near orientation.far)
  physicalParts :
    (actualTwoCutAllocation hL orientation.near orientation.far).bin 0 ∩
        physicalWeightSet T = ∅ ∧
    (actualTwoCutAllocation hL orientation.near orientation.far).bin 1 ∩
        physicalWeightSet T = {T.weight orientation.near} ∧
    (actualTwoCutAllocation hL orientation.near orientation.far).bin 2 ∩
        physicalWeightSet T = {T.weight orientation.far} ∧
    (actualTwoCutAllocation hL orientation.near orientation.far).bin 3 ∩
        physicalWeightSet T =
      physicalWeightSet T \ {T.weight orientation.near,
        T.weight orientation.far}
  recursiveDP : ∀ powers : Finset ℕ,
    (exactFourBinRecursiveDP
      (Finset.Icc 1 (targetN n)) (physicalWeightSet T)
      (actualTwoCutFourBinSpecification hL orientation.near
        orientation.far powers)).Nonempty

noncomputable def actual_twoCut_graph_conclusion {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T)
    (e f : T.Edge) (hef : e ≠ f) :
    ActualTwoCutGraphConclusion T hL e f hef := by
  let O := actualTwoCutAMBOrientation T e f hef
  refine {
    orientation := O
    rankCards := by
      simpa [actualTwoCutAllocation, actualTwoCutRankBin] using
        actualTwoCutAllocation_AMB_cards hL O.root O.near O.far
          O.far_sub_near
    oddRankFormulas := actual_twoCut_AMB_odd_rank_formulas_div hL O.root
      O.near O.far O.far_sub_near
    momentEquations := ?_
    physicalParts := actualTwoCutAllocation_physical_parts hL
      (O.near_ne_far hef)
    recursiveDP := ?_ }
  · intro p
    exact actualTwoCutAllocation_moment_equations hL O.near O.far p
  · intro powers
    exact actualTwoCut_recursiveDP_nonempty hL O.near O.far powers

/-! ## Capacitated Hall, with component-pair demands cloned exactly -/

abbrev DemandSlot {I : Type*} (demand : I → ℕ) := Σ i, Fin (demand i)

def cloneAllowed {I Rank : Type*} {demand : I → ℕ}
    (allowed : I → Finset Rank)
    (s : DemandSlot demand) : Finset Rank := allowed s.1

/-- Base-family capacity inequalities are equivalent to Hall's inequalities
on all cloned demand slots. -/
theorem capacitatedHall_base_iff_clone
    {I Rank : Type*} [DecidableEq I] [DecidableEq Rank]
    (demand : I → ℕ) (allowed : I → Finset Rank) :
    (∀ F : Finset I,
        (∑ i ∈ F, demand i) ≤ (F.biUnion allowed).card) ↔
      ∀ S : Finset (DemandSlot demand),
        S.card ≤ (S.biUnion (cloneAllowed allowed)).card := by
  classical
  constructor
  · intro hbase S
    let F : Finset I := S.image Sigma.fst
    have hsubset :
        S ⊆ F.sigma (fun i => (Finset.univ : Finset (Fin (demand i)))) := by
      intro s hs
      apply Finset.mem_sigma.mpr
      refine ⟨?_, Finset.mem_univ _⟩
      exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
    have hcard : S.card ≤ ∑ i ∈ F, demand i := by
      calc
        S.card ≤ (F.sigma
            (fun i => (Finset.univ : Finset (Fin (demand i))))).card :=
          Finset.card_le_card hsubset
        _ = ∑ i ∈ F, demand i := by simp [Finset.card_sigma]
    have hunion :
        S.biUnion (cloneAllowed allowed) = F.biUnion allowed := by
      apply Finset.ext
      intro r
      constructor
      · intro hr
        obtain ⟨s, hs, hrs⟩ := Finset.mem_biUnion.mp hr
        exact Finset.mem_biUnion.mpr ⟨s.1,
          Finset.mem_image.mpr ⟨s, hs, rfl⟩, hrs⟩
      · intro hr
        obtain ⟨i, hi, hri⟩ := Finset.mem_biUnion.mp hr
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hi
        exact Finset.mem_biUnion.mpr ⟨s, hs, hri⟩
    rw [hunion]
    exact hcard.trans (hbase F)
  · intro hclone F
    let S : Finset (DemandSlot demand) :=
      F.sigma (fun i => (Finset.univ : Finset (Fin (demand i))))
    have h := hclone S
    have hcard : S.card = ∑ i ∈ F, demand i := by
      simp [S, Finset.card_sigma]
    have hunionSub : S.biUnion (cloneAllowed allowed) ⊆
        F.biUnion allowed := by
      intro r hr
      obtain ⟨s, hs, hrs⟩ := Finset.mem_biUnion.mp hr
      have his : s.1 ∈ F := (Finset.mem_sigma.mp hs).1
      exact Finset.mem_biUnion.mpr ⟨s.1, his, hrs⟩
    calc
      ∑ i ∈ F, demand i = S.card := hcard.symm
      _ ≤ (S.biUnion (cloneAllowed allowed)).card := h
      _ ≤ (F.biUnion allowed).card := Finset.card_le_card hunionSub

/-- Exact capacitated Hall iff: all component-pair family inequalities hold
iff every requested abstract slot can be injected into its allowed rank set. -/
theorem capacitatedHall_iff_injective
    {I Rank : Type*} [DecidableEq I] [DecidableEq Rank]
    (demand : I → ℕ) (allowed : I → Finset Rank) :
    (∀ F : Finset I,
        (∑ i ∈ F, demand i) ≤ (F.biUnion allowed).card) ↔
      ∃ assign : DemandSlot demand → Rank,
        Function.Injective assign ∧
          ∀ s, assign s ∈ allowed s.1 := by
  rw [capacitatedHall_base_iff_clone demand allowed]
  simpa only [cloneAllowed] using
    (Finset.all_card_le_biUnion_card_iff_exists_injective
      (cloneAllowed (demand := demand) allowed))

/-- Shared-tail consequence: any chosen family whose allowed sets all lie in
one parity/rank tail competes for that single tail, not for separate copies. -/
theorem shared_tail_capacity
    {I Rank : Type*} [DecidableEq I] [DecidableEq Rank]
    (demand : I → ℕ) (allowed : I → Finset Rank)
    (hHall : ∀ F : Finset I,
      (∑ i ∈ F, demand i) ≤ (F.biUnion allowed).card)
    (F : Finset I) (tail : Finset Rank)
    (htail : ∀ i ∈ F, allowed i ⊆ tail) :
    (∑ i ∈ F, demand i) ≤ tail.card := by
  exact (hHall F).trans (Finset.card_le_card <| by
    intro r hr
    obtain ⟨i, hi, hir⟩ := Finset.mem_biUnion.mp hr
    exact htail i hi hir)

/-- The port-aware suffix family used in (24): if every chosen block is
contained in the same punctured parity tail, the sum of all block demands is
bounded by the number of ranks in that tail. -/
theorem punctured_parity_shared_tail
    {I : Type*} [DecidableEq I]
    (demand : I → ℕ) (allowed : I → Finset ℕ)
    (hHall : ∀ F : Finset I,
      (∑ i ∈ F, demand i) ≤ (F.biUnion allowed).card)
    (F : Finset I) (N threshold parity : ℕ) (physical : Finset ℕ)
    (htail : ∀ i ∈ F, allowed i ⊆
      (Finset.Icc threshold N).filter
        (fun d => d % 2 = parity ∧ d ∉ physical)) :
    (∑ i ∈ F, demand i) ≤
      ((Finset.Icc threshold N).filter
        (fun d => d % 2 = parity ∧ d ∉ physical)).card := by
  exact shared_tail_capacity demand allowed hHall F _ htail

end

end LeechTrees.PathMulticut
