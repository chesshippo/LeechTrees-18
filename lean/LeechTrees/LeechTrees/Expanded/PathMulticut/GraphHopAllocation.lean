import LeechTrees.Foundations
import LeechTrees.Expanded.PathMulticut.RankAllocation
import LeechTrees.Expanded.PathMulticut.PathSegmentStatistics

/-!
# Actual-tree hop-rank allocation

The first theorem is the exact graph-level double count (9).  The subsequent
definitions partition the actual indexed pair spectrum by parity and hop
count and prove the cardinality and sum identities behind (12).
-/

open scoped BigOperators

namespace LeechTrees.PathMulticut

open LeechTrees.Foundation

noncomputable section

/-- Unweighted hop count of the canonical path of an indexed pair. -/
def hopCount {n : ℕ} (T : PosIntTree n) (p : VertexPair n) : ℕ :=
  (T.pathEdges p.left p.right).card

/-- Path incidence multiplied by the hop count of that row. -/
def hopIncidence {n : ℕ} (T : PosIntTree n)
    (p : VertexPair n) (e : T.Edge) : ℕ :=
  hopCount T p * T.pathIncidence p e

/-- `H_e = Σ_{p:e∈P_p} h_p`. -/
def hopCoefficient {n : ℕ} (T : PosIntTree n) (e : T.Edge) : ℕ :=
  LeechTrees.columnCount (hopIncidence T) e

/-! ### Exact cut-side expansion (11) -/

/-- The same named topology with every physical edge given unit weight. -/
def unitWeightTopology {n : ℕ} (T : PosIntTree n) : PosIntTree n where
  graph := T.graph
  isTree := T.isTree
  weight := fun _ => 1
  weight_pos := by intro e; omega

@[simp] theorem unitWeightTopology_graph {n : ℕ} (T : PosIntTree n) :
    (unitWeightTopology T).graph = T.graph := rfl

@[simp] theorem unitWeightTopology_dist {n : ℕ} (T : PosIntTree n)
    (u v : Fin n) :
    (unitWeightTopology T).dist u v = (T.pathEdges u v).card := by
  classical
  have hpath : (unitWeightTopology T).path u v = T.path u v := by
    exact T.path_unique ((unitWeightTopology T).path u v)
  have hEdges : (unitWeightTopology T).pathEdges u v = T.pathEdges u v := by
    simp only [PosIntTree.pathEdges, hpath]
  unfold PosIntTree.dist
  rw [hEdges]
  calc
    (∑ e ∈ T.pathEdges u v, (unitWeightTopology T).weightOfPair e) =
        ∑ _e ∈ T.pathEdges u v, 1 := by
      apply Finset.sum_congr rfl
      intro e he
      unfold PosIntTree.weightOfPair
      simp [unitWeightTopology, T.pathEdges_subset_edgeSet u v he]
    _ = (T.pathEdges u v).card := by simp

/-- Unweighted depth within the endpoint-oriented left deletion side. -/
def leftHopDepth {n : ℕ} (T : PosIntTree n) (e : T.Edge)
    (u : T.LeftVertex e) : ℕ :=
  (T.pathEdges u.1 (T.edgeLeft e)).card

/-- Unweighted depth within the endpoint-oriented right deletion side. -/
def rightHopDepth {n : ℕ} (T : PosIntTree n) (e : T.Edge)
    (v : T.RightVertex e) : ℕ :=
  (T.pathEdges (T.edgeRight e) v.1).card

/-- Every path crossing `e` consists of its left-side path, the edge `e`, and
its right-side path, now counted in hops. -/
theorem hopCount_crossVertexPair_decomposition {n : ℕ}
    (T : PosIntTree n) (e : T.Edge)
    (x : T.LeftVertex e × T.RightVertex e) :
    hopCount T (T.crossVertexPair e x) =
      leftHopDepth T e x.1 + 1 + rightHopDepth T e x.2 := by
  let U := unitWeightTopology T
  have hleft : U.LeftCut e x.1.1 := by
    simpa [U, unitWeightTopology, PosIntTree.LeftCut,
      PosIntTree.cutGraph] using x.1.2
  have hright : U.RightCut e x.2.1 := by
    simpa [U, unitWeightTopology, PosIntTree.RightCut,
      PosIntTree.cutGraph] using x.2.2
  have h := U.cross_distance_decomposition e hleft hright
  rw [unitWeightTopology_dist, unitWeightTopology_dist,
    unitWeightTopology_dist] at h
  change
    (T.pathEdges x.1.1 x.2.1).card =
      (T.pathEdges x.1.1 (T.edgeLeft e)).card + 1 +
        (T.pathEdges (T.edgeRight e) x.2.1).card at h
  have hcross :
      T.pathEdges (T.crossVertexPair e x).left
          (T.crossVertexPair e x).right =
        T.pathEdges x.1.1 x.2.1 := by
    unfold PosIntTree.crossVertexPair
    by_cases hlt : x.1.1 < x.2.1
    · simp [VertexPair.ofDistinct, hlt, VertexPair.left, VertexPair.right]
    · simp [VertexPair.ofDistinct, hlt, VertexPair.left, VertexPair.right,
        T.pathEdges_comm]
  unfold hopCount leftHopDepth rightHopDepth
  rw [hcross]
  exact h

/-- `H_e` is the sum of hop counts over the actual Cartesian cut rectangle. -/
theorem hopCoefficient_eq_crossRectangle_sum {n : ℕ}
    (T : PosIntTree n) (e : T.Edge) :
    hopCoefficient T e =
      ∑ x : T.LeftVertex e × T.RightVertex e,
        hopCount T (T.crossVertexPair e x) := by
  classical
  calc
    hopCoefficient T e =
        ∑ p : VertexPair n,
          if e.1 ∈ T.pathEdges p.left p.right then hopCount T p else 0 := by
      unfold hopCoefficient LeechTrees.columnCount hopIncidence
      apply Finset.sum_congr rfl
      intro p hp
      simp [PosIntTree.pathIncidence]
    _ = ∑ p : T.CrossingPair e, hopCount T p.1 := by
      let s := (Finset.univ : Finset (VertexPair n)).filter fun p =>
        e.1 ∈ T.pathEdges p.left p.right
      rw [← Finset.sum_filter]
      change (∑ p ∈ s, hopCount T p) = _
      exact Finset.sum_subtype s (by intro p; simp [s]) (hopCount T)
    _ = ∑ x : T.LeftVertex e × T.RightVertex e,
          hopCount T (T.crossVertexPair e x) := by
      symm
      apply Fintype.sum_equiv (T.crossingPairEquiv e)
      intro x
      rw [T.crossingPairEquiv_apply_val e]

/-- Exact cut-side coefficient expansion (11), with `A` and `B` the actual
endpoint-oriented deletion sides and `alpha`,`beta` their actual edge ports. -/
theorem hopCoefficient_cut_side_expansion {n : ℕ}
    (T : PosIntTree n) (e : T.Edge) :
    hopCoefficient T e =
      T.cutSize e * (n - T.cutSize e) +
      (n - T.cutSize e) *
        (∑ u : T.LeftVertex e, leftHopDepth T e u) +
      T.cutSize e *
        (∑ v : T.RightVertex e, rightHopDepth T e v) := by
  rw [hopCoefficient_eq_crossRectangle_sum]
  simp_rw [hopCount_crossVertexPair_decomposition]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.cast_id]
  rw [T.rightVertex_card e]
  unfold PosIntTree.cutSize
  simp only [← Finset.mul_sum]
  ac_rfl

theorem hopIncidence_weightedRow {n : ℕ} (T : PosIntTree n)
    (p : VertexPair n) :
    LeechTrees.weightedRow (hopIncidence T) T.weight p =
      hopCount T p * T.pairDist p := by
  classical
  unfold LeechTrees.weightedRow hopIncidence
  simp_rw [Nat.mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  exact T.pathIncidence_row p

/-- Exact graph-level hop-rank double count (9). -/
theorem hop_rank_double_count {n : ℕ} (T : PosIntTree n) :
    (∑ p : VertexPair n, hopCount T p * T.pairDist p) =
      ∑ e : T.Edge, T.weight e * hopCoefficient T e := by
  classical
  calc
    (∑ p : VertexPair n, hopCount T p * T.pairDist p) =
        ∑ p : VertexPair n,
          LeechTrees.weightedRow (hopIncidence T) T.weight p := by
      apply Finset.sum_congr rfl
      intro p hp
      exact (hopIncidence_weightedRow T p).symm
    _ = ∑ e : T.Edge,
          LeechTrees.columnCount (hopIncidence T) e * T.weight e :=
      LeechTrees.sum_weightedRows_eq_sum_columnCounts
        (hopIncidence T) T.weight
    _ = ∑ e : T.Edge, T.weight e * hopCoefficient T e := by
      apply Finset.sum_congr rfl
      intro e he
      simp [hopCoefficient, Nat.mul_comm]

@[simp] theorem hopCount_edgePair {n : ℕ} (T : PosIntTree n) (e : T.Edge) :
    hopCount T (T.edgePair e) = 1 := by
  simp [hopCount, T.pathEdges_edge e]

/-- Actual nonedge indexed pairs. -/
abbrev ActualNonedgePair {n : ℕ} (T : PosIntTree n) :=
  {p : VertexPair n // ∀ e : T.Edge, p ≠ T.edgePair e}

/-- Actual target ranks after deleting every physical weight. -/
abbrev ActualNonphysicalRank {n : ℕ} (T : PosIntTree n) :=
  {d : {d : ℕ // d ∈ Finset.Icc 1 (targetN n)} //
    ∀ e : T.Edge, d.1 ≠ T.weight e}

/-- Restricting the spectrum bijection gives an actual bijection from
nonedge pairs to target ranks with all physical weights punctured. -/
noncomputable def actualNonedgeSpectrumEquiv {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) : ActualNonedgePair T ≃ ActualNonphysicalRank T where
  toFun p :=
    ⟨hL.spectrumEquiv p.1, by
      intro e he
      apply p.2 e
      apply hL.pairDist_injective
      simpa using he⟩
  invFun d :=
    ⟨(hL.spectrumEquiv).symm d.1, by
      intro e he
      apply d.2 e
      have hs := congrArg Subtype.val
        ((hL.spectrumEquiv).apply_symm_apply d.1)
      change T.pairDist ((hL.spectrumEquiv).symm d.1) = d.1.1 at hs
      rw [he, T.edgePair_dist] at hs
      exact hs.symm⟩
  left_inv p := by
    apply Subtype.ext
    exact (hL.spectrumEquiv).symm_apply_apply p.1
  right_inv d := by
    apply Subtype.ext
    exact (hL.spectrumEquiv).apply_symm_apply d.1

@[simp] theorem actualNonedgeSpectrumEquiv_value {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) (p : ActualNonedgePair T) :
    (actualNonedgeSpectrumEquiv hL p).1.1 = T.pairDist p.1 := rfl

/-- Actual indexed `(parity,hop)` pair bin. -/
def parityHopPairBin {n : ℕ} (T : PosIntTree n) (parity h : ℕ) :
    Finset (VertexPair n) :=
  Finset.univ.filter fun p =>
    T.pairDist p % 2 = parity ∧ hopCount T p = h

/-- Actual target ranks occupied by one parity/hop bin. -/
def parityHopRankBin {n : ℕ} (T : PosIntTree n) (parity h : ℕ) :
    Finset ℕ :=
  (parityHopPairBin T parity h).image T.pairDist

/-- Number of paths in one parity/hop bin that contain edge `e`. -/
def parityHopEdgeCount {n : ℕ} (T : PosIntTree n)
    (parity h : ℕ) (e : T.Edge) : ℕ :=
  ((parityHopPairBin T parity h).filter fun p =>
    e.1 ∈ T.pathEdges p.left p.right).card

theorem parityHopRankBin_card {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) (parity h : ℕ) :
    (parityHopRankBin T parity h).card =
      (parityHopPairBin T parity h).card := by
  classical
  exact Finset.card_image_of_injective _ hL.pairDist_injective

/-- A one-hop indexed pair is exactly the endpoint pair of a physical edge. -/
theorem exists_edgePair_of_hopCount_eq_one {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) (p : VertexPair n) (hh : hopCount T p = 1) :
    ∃ e : T.Edge, p = T.edgePair e := by
  classical
  have hnonempty : (T.pathEdges p.left p.right).Nonempty := by
    rw [← Finset.card_pos]
    change 0 < hopCount T p
    omega
  obtain ⟨edgeValue, hedgeValue⟩ := hnonempty
  let e : T.Edge := T.edgeOfPathMem edgeValue hedgeValue
  have hsingleton : T.pathEdges p.left p.right = {edgeValue} := by
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hh
    have hex : edgeValue = x := by simpa [hx] using hedgeValue
    simpa [hex] using hx
  refine ⟨e, ?_⟩
  apply hL.pairDist_injective
  rw [T.edgePair_dist]
  unfold PosIntTree.pairDist PosIntTree.dist
  rw [hsingleton]
  simp [e]

/-- The hop-one parity bin is exactly the physical-weight set in that parity
channel, retaining the paper's `R_{p,1}=W_p` assertion. -/
theorem parityHopRankBin_one_eq_physical {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) (parity : ℕ) :
    parityHopRankBin T parity 1 =
      (Finset.univ.image T.weight).filter fun w => w % 2 = parity := by
  classical
  apply Finset.ext
  intro d
  constructor
  · intro hd
    obtain ⟨p, hp, hpd⟩ := Finset.mem_image.mp hd
    have hdata := (Finset.mem_filter.mp hp).2
    obtain ⟨e, rfl⟩ := exists_edgePair_of_hopCount_eq_one hL p hdata.2
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, by simpa using hpd⟩
    · rw [← hpd]
      exact hdata.1
  · intro hd
    obtain ⟨hphysical, hparity⟩ := Finset.mem_filter.mp hd
    obtain ⟨e, he, hed⟩ := Finset.mem_image.mp hphysical
    apply Finset.mem_image.mpr
    refine ⟨T.edgePair e, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, hopCount_edgePair T e⟩
      simpa [T.edgePair_dist e, hed] using hparity
    · simpa [T.edgePair_dist e] using hed

/-- Exact bin sum `S_{p,h}=Σ_e k_{e,p,h}w_e`. -/
theorem parityHopRankBin_sum {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) (parity h : ℕ) :
    (∑ d ∈ parityHopRankBin T parity h, d) =
      ∑ e : T.Edge, parityHopEdgeCount T parity h e * T.weight e := by
  classical
  have hsumImage :
      (∑ d ∈ parityHopRankBin T parity h, d) =
        ∑ p ∈ parityHopPairBin T parity h, T.pairDist p := by
    unfold parityHopRankBin
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact hL.pairDist_injective hab
  rw [hsumImage]
  calc
    (∑ p ∈ parityHopPairBin T parity h, T.pairDist p) =
        ∑ p ∈ parityHopPairBin T parity h,
          ∑ e : T.Edge, T.pathIncidence p e * T.weight e := by
      apply Finset.sum_congr rfl
      intro p hp
      exact (T.pathIncidence_row p).symm
    _ = ∑ e : T.Edge,
          (∑ p ∈ parityHopPairBin T parity h,
            T.pathIncidence p e) * T.weight e := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = ∑ e : T.Edge,
          parityHopEdgeCount T parity h e * T.weight e := by
      apply Finset.sum_congr rfl
      intro e he
      congr 1
      unfold parityHopEdgeCount PosIntTree.pathIncidence
      rw [← Finset.card_filter]

theorem parityHopRankBins_disjoint {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) {p h p' h' : ℕ}
    (hne : p ≠ p' ∨ h ≠ h') :
    Disjoint (parityHopRankBin T p h) (parityHopRankBin T p' h') := by
  classical
  apply Finset.disjoint_left.mpr
  intro d hd hd'
  obtain ⟨q, hq, hqd⟩ := Finset.mem_image.mp hd
  obtain ⟨q', hq', hq'd⟩ := Finset.mem_image.mp hd'
  have hqq' : q = q' := hL.pairDist_injective (hqd.trans hq'd.symm)
  subst q'
  have hdata := (Finset.mem_filter.mp hq).2
  have hdata' := (Finset.mem_filter.mp hq').2
  rcases hne with hp | hh
  · exact hp (hdata.1.symm.trans hdata'.1)
  · exact hh (hdata.2.symm.trans hdata'.2)

/-- Every target rank belongs to the bin determined by its actual pair's
parity and hop count. -/
theorem parityHopRankBins_cover {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) :
    ∀ (d : ℕ) (hd : d ∈ Finset.Icc 1 (targetN n)),
      d ∈ parityHopRankBin T (d % 2)
        (hopCount T ((hL.spectrumEquiv).symm ⟨d, hd⟩)) := by
  intro d hd
  classical
  let q : VertexPair n := (hL.spectrumEquiv).symm ⟨d, hd⟩
  have hq : T.pairDist q = d :=
    congrArg Subtype.val ((hL.spectrumEquiv).apply_symm_apply ⟨d, hd⟩)
  apply Finset.mem_image.mpr
  refine ⟨q, ?_, ?_⟩
  · simp only [parityHopPairBin, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by rw [hq], rfl⟩
  · exact hq

/-- A sorted actual nonedge rank allocation.  The only fields supplied by a
caller are genuine enumerations of actual pair and rank types plus the fact
that those enumerations are sorted; the rank permutation itself is derived
from `IsLeech` below. -/
structure HopRankOrdering {n : ℕ} (T : PosIntTree n) (hL : IsLeech T)
    (L : ℕ) where
  NonedgePair : Type*
  NonphysicalRank : Type*
  nonedgePairFintype : Fintype NonedgePair
  nonphysicalRankFintype : Fintype NonphysicalRank
  pairValue : NonedgePair → VertexPair n
  rankValue : NonphysicalRank → ℕ
  pair_is_nonedge : ∀ x e, pairValue x ≠ T.edgePair e
  rank_is_target : ∀ x, rankValue x ∈ Finset.Icc 1 (targetN n)
  rank_is_nonphysical : ∀ x e, rankValue x ≠ T.weight e
  pairOrder : Fin L ≃ NonedgePair
  rankOrder : Fin L ≃ NonphysicalRank
  spectrumEquiv : NonedgePair ≃ NonphysicalRank
  spectrum_value : ∀ x,
    rankValue (spectrumEquiv x) = T.pairDist (pairValue x)
  score_mono : Monotone (fun i => (hopCount T (pairValue (pairOrder i)) : ℝ))
  rank_mono : Monotone (fun i => (rankValue (rankOrder i) : ℝ))

attribute [instance]
  HopRankOrdering.nonedgePairFintype
  HopRankOrdering.nonphysicalRankFintype

/-- The sorted ordering required by (10) always exists for the actual
nonedge/nonphysical spectrum.  Both orders are constructed by `Tuple.sort`;
the caller supplies no ordering certificate. -/
noncomputable def actualHopRankOrdering {n : ℕ} (T : PosIntTree n)
    (hL : IsLeech T) :
    HopRankOrdering T hL (Fintype.card (ActualNonphysicalRank T)) := by
  let L := Fintype.card (ActualNonphysicalRank T)
  have hcard : Fintype.card (ActualNonedgePair T) = L :=
    Fintype.card_congr (actualNonedgeSpectrumEquiv hL)
  let pairBase : Fin L ≃ ActualNonedgePair T :=
    (finCongr hcard.symm).trans
      (Fintype.equivFin (ActualNonedgePair T)).symm
  let rankBase : Fin L ≃ ActualNonphysicalRank T :=
    (Fintype.equivFin (ActualNonphysicalRank T)).symm
  let pairKey : Fin L → ℝ := fun i => (hopCount T (pairBase i).1 : ℝ)
  let rankKey : Fin L → ℝ := fun i => ((rankBase i).1.1 : ℝ)
  exact {
    NonedgePair := ActualNonedgePair T
    NonphysicalRank := ActualNonphysicalRank T
    nonedgePairFintype := inferInstance
    nonphysicalRankFintype := inferInstance
    pairValue := Subtype.val
    rankValue := fun d => d.1.1
    pair_is_nonedge := fun x e => x.2 e
    rank_is_target := fun x => x.1.2
    rank_is_nonphysical := fun x e => x.2 e
    pairOrder := (Tuple.sort pairKey).trans pairBase
    rankOrder := (Tuple.sort rankKey).trans rankBase
    spectrumEquiv := actualNonedgeSpectrumEquiv hL
    spectrum_value := fun x => rfl
    score_mono := by
      simpa [pairKey, Function.comp_def] using Tuple.monotone_sort pairKey
    rank_mono := by
      simpa [rankKey, Function.comp_def] using Tuple.monotone_sort rankKey }

theorem exists_actualHopRankOrdering {n : ℕ} (T : PosIntTree n)
    (hL : IsLeech T) :
    Nonempty (HopRankOrdering.{0, 0} T hL
      (Fintype.card (ActualNonphysicalRank T))) :=
  ⟨actualHopRankOrdering T hL⟩

namespace HopRankOrdering

variable {n L : ℕ} {T : PosIntTree n} {hL : IsLeech T}

/-- The actual permutation induced by the Leech spectrum bijection. -/
def actualPermutation (O : HopRankOrdering T hL L) : Equiv.Perm (Fin L) :=
  O.pairOrder.trans (O.spectrumEquiv.trans O.rankOrder.symm)

theorem actualPermutation_rank (O : HopRankOrdering T hL L) (i : Fin L) :
    O.rankValue (O.rankOrder (O.actualPermutation i)) =
      T.pairDist (O.pairValue (O.pairOrder i)) := by
  simp [actualPermutation, O.spectrum_value]

def sortedHop (O : HopRankOrdering T hL L) : Fin L → ℝ :=
  fun i => (hopCount T (O.pairValue (O.pairOrder i)) : ℝ)

def sortedRank (O : HopRankOrdering T hL L) : Fin L → ℝ :=
  fun i => (O.rankValue (O.rankOrder i) : ℝ)

def actualNonedgeMoment (O : HopRankOrdering T hL L) : ℝ :=
  rankDot O.sortedHop (O.sortedRank ∘ O.actualPermutation)

theorem actualNonedgeMoment_eq_sum (O : HopRankOrdering T hL L) :
    O.actualNonedgeMoment =
      ∑ i : Fin L,
        (hopCount T (O.pairValue (O.pairOrder i)) : ℝ) *
          T.pairDist (O.pairValue (O.pairOrder i)) := by
  unfold actualNonedgeMoment rankDot sortedHop sortedRank
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Function.comp_apply]
  rw [O.actualPermutation_rank]

/-- Exact hop-rank rearrangement (10) for the actual nonedge assignment.
The equality cases are retained as exact iff statements. -/
theorem actual_hop_rank_rearrangement
    (O : HopRankOrdering T hL L) :
    lowerRankDot
        (fun i => (hopCount T (O.pairValue (O.pairOrder i)) : ℝ))
        (fun i => (O.rankValue (O.rankOrder i) : ℝ)) ≤
      rankDot
        (fun i => (hopCount T (O.pairValue (O.pairOrder i)) : ℝ))
        ((fun i => (O.rankValue (O.rankOrder i) : ℝ)) ∘
          O.actualPermutation) ∧
    rankDot
        (fun i => (hopCount T (O.pairValue (O.pairOrder i)) : ℝ))
        ((fun i => (O.rankValue (O.rankOrder i) : ℝ)) ∘
          O.actualPermutation) ≤
      upperRankDot
        (fun i => (hopCount T (O.pairValue (O.pairOrder i)) : ℝ))
        (fun i => (O.rankValue (O.rankOrder i) : ℝ)) ∧
    (rankDot
        (fun i => (hopCount T (O.pairValue (O.pairOrder i)) : ℝ))
        ((fun i => (O.rankValue (O.rankOrder i) : ℝ)) ∘
          O.actualPermutation) =
        upperRankDot
          (fun i => (hopCount T (O.pairValue (O.pairOrder i)) : ℝ))
          (fun i => (O.rankValue (O.rankOrder i) : ℝ)) ↔
      Monovary
        (fun i => (hopCount T (O.pairValue (O.pairOrder i)) : ℝ))
        ((fun i => (O.rankValue (O.rankOrder i) : ℝ)) ∘
          O.actualPermutation)) ∧
    (rankDot
        (fun i => (hopCount T (O.pairValue (O.pairOrder i)) : ℝ))
        ((fun i => (O.rankValue (O.rankOrder i) : ℝ)) ∘
          O.actualPermutation) =
        lowerRankDot
          (fun i => (hopCount T (O.pairValue (O.pairOrder i)) : ℝ))
          (fun i => (O.rankValue (O.rankOrder i) : ℝ)) ↔
      Antivary
        (fun i => (hopCount T (O.pairValue (O.pairOrder i)) : ℝ))
        ((fun i => (O.rankValue (O.rankOrder i) : ℝ)) ∘
          O.actualPermutation)) :=
  sharp_rank_rearrangement _ _ O.actualPermutation O.score_mono O.rank_mono

end HopRankOrdering

def hopPhysicalPairSet {n : ℕ} (T : PosIntTree n) :
    Finset (VertexPair n) := Finset.univ.image T.edgePair

/-- Exact split of the hop moment into the hop-one physical endpoint rows and
all actual nonedge rows. -/
theorem hopMoment_eq_physical_add_nonedge {n : ℕ}
    {T : PosIntTree n} (_hL : IsLeech T) :
    (∑ p : VertexPair n, (hopCount T p : ℝ) * T.pairDist p) =
      (∑ e : T.Edge, (T.weight e : ℝ)) +
        ∑ p : ActualNonedgePair T,
          (hopCount T p.1 : ℝ) * T.pairDist p.1 := by
  classical
  let term : VertexPair n → ℝ := fun p =>
    (hopCount T p : ℝ) * T.pairDist p
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (VertexPair n))
      (fun p => p ∈ hopPhysicalPairSet T) term
  have hphysical :
      (∑ p ∈ (Finset.univ : Finset (VertexPair n)).filter
          (fun p => p ∈ hopPhysicalPairSet T), term p) =
        ∑ e : T.Edge, (T.weight e : ℝ) := by
    have hset :
        (Finset.univ : Finset (VertexPair n)).filter
            (fun p => p ∈ hopPhysicalPairSet T) =
          Finset.univ.image T.edgePair := by
      ext p
      simp [hopPhysicalPairSet]
    rw [hset, Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro e he
      simp [term, T.edgePair_dist]
    · intro e he f hf hef
      exact edgePair_injective T hef
  have hnonedge :
      (∑ p ∈ (Finset.univ : Finset (VertexPair n)).filter
          (fun p => p ∉ hopPhysicalPairSet T), term p) =
        ∑ p : ActualNonedgePair T,
          (hopCount T p.1 : ℝ) * T.pairDist p.1 := by
    apply Finset.sum_subtype
    intro p
    constructor
    · intro hp e hpe
      apply (Finset.mem_filter.mp hp).2
      apply Finset.mem_image.mpr
      exact ⟨e, Finset.mem_univ _, hpe.symm⟩
    · intro hp
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hmem
      obtain ⟨e, he, hep⟩ := Finset.mem_image.mp hmem
      exact hp e hep.symm
  change (∑ p ∈ (Finset.univ : Finset (VertexPair n)), term p) = _
  rw [← hsplit, hphysical, hnonedge]

/-- Formula (10) with no ordering hypothesis: the orders and the actual rank
permutation are all constructed from `T` and `IsLeech`. -/
theorem actual_hop_rank_bounds {n : ℕ} (T : PosIntTree n)
    (hL : IsLeech T) :
    let O := actualHopRankOrdering T hL
    (∑ e : T.Edge, (T.weight e : ℝ)) +
        lowerRankDot O.sortedHop O.sortedRank ≤
      (∑ e : T.Edge, (T.weight e : ℝ) * hopCoefficient T e) ∧
    (∑ e : T.Edge, (T.weight e : ℝ) * hopCoefficient T e) ≤
      (∑ e : T.Edge, (T.weight e : ℝ)) +
        upperRankDot O.sortedHop O.sortedRank := by
  let O := actualHopRankOrdering T hL
  have hr := O.actual_hop_rank_rearrangement
  have hnonedge : O.actualNonedgeMoment =
      ∑ p : ActualNonedgePair T,
        (hopCount T p.1 : ℝ) * T.pairDist p.1 := by
    rw [O.actualNonedgeMoment_eq_sum]
    apply Fintype.sum_equiv O.pairOrder
    intro i
    rfl
  have htotal :
      (∑ e : T.Edge, (T.weight e : ℝ) * hopCoefficient T e) =
        (∑ e : T.Edge, (T.weight e : ℝ)) + O.actualNonedgeMoment := by
    rw [hnonedge, ← hopMoment_eq_physical_add_nonedge hL]
    exact_mod_cast (hop_rank_double_count T).symm
  dsimp only
  rw [htotal]
  exact ⟨add_le_add_left hr.1 _, add_le_add_left hr.2.1 _⟩

end

end LeechTrees.PathMulticut
