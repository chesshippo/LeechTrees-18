import LeechTrees.Foundations
import LeechTrees.ParityTail

/-!
# Graph adapter for the parity-tail kernel, version 1

This module instantiates the frozen abstract parity-tail algebra with the
indexed paths, cuts, and exact spectrum in `Foundation.PosIntTree` and
`Foundation.IsLeech`.  It is kept separate so neither frozen dependency is
mutated.
-/

open scoped BigOperators

namespace LeechTrees.ParityTail.GraphAdapterV1

open LeechTrees.Foundation

/-! ## Actual physical-edge rows and parity blocks -/

variable {n : ℕ} (T : PosIntTree n)

/-! ## Actual root-parity signs -/

/-- The actual root-distance parity character. -/
noncomputable def rootParitySign (r u : Fin n) : ℤ :=
  paritySign (T.dist r u)

theorem paritySign_eq_one_iff_mod_two (d : ℕ) :
    paritySign d = 1 ↔ d % 2 = 0 := by
  unfold paritySign
  rw [neg_one_pow_eq_pow_mod_two]
  have hlt : d % 2 < 2 := Nat.mod_lt _ (by omega)
  interval_cases h : d % 2 <;> norm_num [h]

theorem paritySign_eq_neg_one_iff_mod_two (d : ℕ) :
    paritySign d = -1 ↔ d % 2 = 1 := by
  unfold paritySign
  rw [neg_one_pow_eq_pow_mod_two]
  have hlt : d % 2 < 2 := Nat.mod_lt _ (by omega)
  interval_cases h : d % 2 <;> norm_num [h]

theorem rootParitySign_pm (r u : Fin n) :
    rootParitySign T r u = 1 ∨ rootParitySign T r u = -1 := by
  unfold rootParitySign paritySign
  rw [neg_one_pow_eq_pow_mod_two]
  have hlt : T.dist r u % 2 < 2 := Nat.mod_lt _ (by omega)
  interval_cases h : T.dist r u % 2 <;> norm_num [h]

theorem rootParitySign_eq_one_iff (r u : Fin n) :
    rootParitySign T r u = 1 ↔ T.dist r u % 2 = 0 := by
  unfold rootParitySign paritySign
  rw [neg_one_pow_eq_pow_mod_two]
  have hlt : T.dist r u % 2 < 2 := Nat.mod_lt _ (by omega)
  interval_cases h : T.dist r u % 2 <;> norm_num [h]

theorem rootParitySign_eq_neg_one_iff (r u : Fin n) :
    rootParitySign T r u = -1 ↔ T.dist r u % 2 = 1 := by
  unfold rootParitySign paritySign
  rw [neg_one_pow_eq_pow_mod_two]
  have hlt : T.dist r u % 2 < 2 := Nat.mod_lt _ (by omega)
  interval_cases h : T.dist r u % 2 <;> norm_num [h]

/-- The actual graph parity lemma: a pair of root signs is the sign of the
actual indexed distance. -/
theorem rootParitySign_pair (r u v : Fin n) :
    rootParitySign T r u * rootParitySign T r v =
      paritySign (T.dist u v) := by
  have heven := T.root_path_even r u v
  rw [Nat.even_iff] at heven
  have hmod : (T.dist r u + T.dist r v) % 2 = T.dist u v % 2 := by
    omega
  calc
    rootParitySign T r u * rootParitySign T r v =
        paritySign (T.dist r u + T.dist r v) := by
      exact paritySign_add _ _
    _ = paritySign (T.dist u v) := paritySign_eq_of_mod_two hmod

theorem rootParitySign_pairDist (r : Fin n) (q : VertexPair n) :
    rootParitySign T r q.left * rootParitySign T r q.right =
      paritySign (T.pairDist q) := by
  exact rootParitySign_pair T r q.left q.right

/-- Pair products are independent of the actual root, now derived from tree
parity rather than assumed as a common multiplier. -/
theorem rootParitySign_pair_root_invariant (r r' u v : Fin n) :
    rootParitySign T r u * rootParitySign T r v =
      rootParitySign T r' u * rootParitySign T r' v := by
  rw [rootParitySign_pair, rootParitySign_pair]

theorem positiveCount_add_negativeCount
    {Vertex : Type*} [DecidableEq Vertex]
    (sign : Vertex → ℤ) (s : Finset Vertex)
    (pm : ∀ v ∈ s, sign v = 1 ∨ sign v = -1) :
    positiveCount sign s + negativeCount sign s = s.card := by
  classical
  let pos := s.filter fun v => sign v = 1
  let neg := s.filter fun v => sign v = -1
  have hdisj : Disjoint pos neg := by
    rw [Finset.disjoint_left]
    intro v hp hn
    have hp' := (Finset.mem_filter.mp hp).2
    have hn' := (Finset.mem_filter.mp hn).2
    omega
  have hunion : pos ∪ neg = s := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with hp | hn
      · exact (Finset.mem_filter.mp hp).1
      · exact (Finset.mem_filter.mp hn).1
    · intro hv
      rcases pm v hv with hp | hn
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv, hp⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv, hn⟩)
  unfold positiveCount negativeCount
  change pos.card + neg.card = s.card
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

theorem positiveCount_union
    {Vertex : Type*} [DecidableEq Vertex]
    (sign : Vertex → ℤ) {s t : Finset Vertex} (hdisj : Disjoint s t) :
    positiveCount sign s + positiveCount sign t =
      positiveCount sign (s ∪ t) := by
  classical
  unfold positiveCount
  rw [Finset.filter_union]
  symm
  apply Finset.card_union_of_disjoint
  exact Finset.disjoint_filter_filter hdisj

theorem negativeCount_union
    {Vertex : Type*} [DecidableEq Vertex]
    (sign : Vertex → ℤ) {s t : Finset Vertex} (hdisj : Disjoint s t) :
    negativeCount sign s + negativeCount sign t =
      negativeCount sign (s ∪ t) := by
  classical
  unfold negativeCount
  rw [Finset.filter_union]
  symm
  apply Finset.card_union_of_disjoint
  exact Finset.disjoint_filter_filter hdisj

/-- The global positive root-sign count is the foundation's even parity-class
size. -/
theorem rootPositiveCount_univ (r : Fin n) :
    positiveCount (rootParitySign T r) Finset.univ =
      T.parityClassSize r := by
  classical
  unfold positiveCount PosIntTree.parityClassSize
  rw [Fintype.card_subtype]
  congr 1
  ext u
  simp [rootParitySign_eq_one_iff]

theorem rootNegativeCount_univ (r : Fin n) :
    negativeCount (rootParitySign T r) Finset.univ =
      n - T.parityClassSize r := by
  have hsum := positiveCount_add_negativeCount
    (rootParitySign T r) (Finset.univ : Finset (Fin n))
    (fun u _ => rootParitySign_pm T r u)
  rw [rootPositiveCount_univ] at hsum
  have hle := T.parityClassSize_le_order r
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  omega

/-- The order-18 normalization multiplier chooses the global sign for which
the positive class has order eleven. -/
noncomputable def normalizationMultiplier18
    (T : PosIntTree 18) (r : Fin 18) : ℤ :=
  if T.parityClassSize r = 11 then 1 else -1

theorem normalizationMultiplier18_pm
    (T : PosIntTree 18) (r : Fin 18) :
    normalizationMultiplier18 T r = 1 ∨
      normalizationMultiplier18 T r = -1 := by
  unfold normalizationMultiplier18
  split_ifs <;> simp

/-- Root parity with the harmless common sign normalized to total mass four. -/
noncomputable def normalizedParitySign18
    (T : PosIntTree 18) (r u : Fin 18) : ℤ :=
  normalizationMultiplier18 T r * rootParitySign T r u

theorem normalizedParitySign18_pm
    (T : PosIntTree 18) (r u : Fin 18) :
    normalizedParitySign18 T r u = 1 ∨
      normalizedParitySign18 T r u = -1 := by
  rcases normalizationMultiplier18_pm T r with hm | hm <;>
    rcases rootParitySign_pm T r u with hu | hu <;>
    simp [normalizedParitySign18, hm, hu]

theorem normalizedParitySign18_pair
    (T : PosIntTree 18) (r u v : Fin 18) :
    normalizedParitySign18 T r u * normalizedParitySign18 T r v =
      paritySign (T.dist u v) := by
  rcases normalizationMultiplier18_pm T r with hm | hm <;>
    simp [normalizedParitySign18, hm, rootParitySign_pair]

theorem normalizedPositiveCount_univ
    {T : PosIntTree 18} (hL : IsLeech T) (r : Fin 18) :
    positiveCount (normalizedParitySign18 T r) Finset.univ = 11 := by
  classical
  rcases t3_order18_class_sizes hL r with h7 | h11
  · have hnot : ¬T.parityClassSize r = 11 := by omega
    have heq :
        positiveCount (normalizedParitySign18 T r) Finset.univ =
          negativeCount (rootParitySign T r) Finset.univ := by
      unfold positiveCount negativeCount normalizedParitySign18
      simp only [normalizationMultiplier18, if_neg hnot]
      congr 1
      ext u
      rcases rootParitySign_pm T r u with hu | hu <;> simp [hu]
    rw [heq, rootNegativeCount_univ, h7]
  · have heq : normalizedParitySign18 T r = rootParitySign T r := by
      funext u
      simp [normalizedParitySign18, normalizationMultiplier18, h11]
    rw [heq, rootPositiveCount_univ, h11]

theorem normalizedNegativeCount_univ
    {T : PosIntTree 18} (hL : IsLeech T) (r : Fin 18) :
    negativeCount (normalizedParitySign18 T r) Finset.univ = 7 := by
  have hsum := positiveCount_add_negativeCount
    (normalizedParitySign18 T r) (Finset.univ : Finset (Fin 18))
    (fun u _ => normalizedParitySign18_pm T r u)
  rw [normalizedPositiveCount_univ hL r] at hsum
  norm_num at hsum ⊢
  omega

/-! ## Actual deletion-side sign counts -/

noncomputable def leftVertexSet (e : T.Edge) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun u => T.LeftCut e u

noncomputable def rightVertexSet (e : T.Edge) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun u => T.RightCut e u

theorem leftVertexSet_disjoint_rightVertexSet (e : T.Edge) :
    Disjoint (leftVertexSet T e) (rightVertexSet T e) := by
  classical
  rw [Finset.disjoint_left]
  intro u hu hv
  exact T.LeftCut_disjoint_RightCut e u
    ⟨(Finset.mem_filter.mp hu).2, (Finset.mem_filter.mp hv).2⟩

theorem leftVertexSet_union_rightVertexSet (e : T.Edge) :
    leftVertexSet T e ∪ rightVertexSet T e = Finset.univ := by
  classical
  ext u
  simp only [leftVertexSet, rightVertexSet, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    trivial
  · intro h
    exact T.cut_cover e u

theorem leftVertexSet_card (e : T.Edge) :
    (leftVertexSet T e).card = T.cutSize e := by
  classical
  unfold leftVertexSet PosIntTree.cutSize
  rw [Fintype.card_subtype]

theorem rightVertexSet_card (e : T.Edge) :
    (rightVertexSet T e).card = n - T.cutSize e := by
  classical
  calc
    (rightVertexSet T e).card = Fintype.card (T.RightVertex e) := by
      unfold rightVertexSet
      rw [Fintype.card_subtype]
    _ = n - T.cutSize e := T.rightVertex_card e

noncomputable def leftPositive18
    (T : PosIntTree 18) (r : Fin 18) (e : T.Edge) : ℕ :=
  positiveCount (normalizedParitySign18 T r) (leftVertexSet T e)

noncomputable def leftNegative18
    (T : PosIntTree 18) (r : Fin 18) (e : T.Edge) : ℕ :=
  negativeCount (normalizedParitySign18 T r) (leftVertexSet T e)

noncomputable def rightPositive18
    (T : PosIntTree 18) (r : Fin 18) (e : T.Edge) : ℕ :=
  positiveCount (normalizedParitySign18 T r) (rightVertexSet T e)

noncomputable def rightNegative18
    (T : PosIntTree 18) (r : Fin 18) (e : T.Edge) : ℕ :=
  negativeCount (normalizedParitySign18 T r) (rightVertexSet T e)

noncomputable def leftImbalance18
    (T : PosIntTree 18) (r : Fin 18) (e : T.Edge) : ℤ :=
  (leftPositive18 T r e : ℤ) - leftNegative18 T r e

theorem leftCounts_total18
    (T : PosIntTree 18) (r : Fin 18) (e : T.Edge) :
    leftPositive18 T r e + leftNegative18 T r e = T.cutSize e := by
  unfold leftPositive18 leftNegative18
  rw [positiveCount_add_negativeCount
    (normalizedParitySign18 T r) (leftVertexSet T e)
    (fun u _ => normalizedParitySign18_pm T r u)]
  exact leftVertexSet_card T e

theorem rightCounts_total18
    (T : PosIntTree 18) (r : Fin 18) (e : T.Edge) :
    rightPositive18 T r e + rightNegative18 T r e =
      18 - T.cutSize e := by
  unfold rightPositive18 rightNegative18
  rw [positiveCount_add_negativeCount
    (normalizedParitySign18 T r) (rightVertexSet T e)
    (fun u _ => normalizedParitySign18_pm T r u)]
  exact rightVertexSet_card T e

theorem cutPositiveCounts_total18
    {T : PosIntTree 18} (hL : IsLeech T) (r : Fin 18) (e : T.Edge) :
    leftPositive18 T r e + rightPositive18 T r e = 11 := by
  unfold leftPositive18 rightPositive18
  rw [positiveCount_union (normalizedParitySign18 T r)
    (leftVertexSet_disjoint_rightVertexSet T e)]
  rw [leftVertexSet_union_rightVertexSet]
  exact normalizedPositiveCount_univ hL r

theorem cutNegativeCounts_total18
    {T : PosIntTree 18} (hL : IsLeech T) (r : Fin 18) (e : T.Edge) :
    leftNegative18 T r e + rightNegative18 T r e = 7 := by
  unfold leftNegative18 rightNegative18
  rw [negativeCount_union (normalizedParitySign18 T r)
    (leftVertexSet_disjoint_rightVertexSet T e)]
  rw [leftVertexSet_union_rightVertexSet]
  exact normalizedNegativeCount_univ hL r

theorem cutGlobalSignEquation18
    {T : PosIntTree 18} (hL : IsLeech T) (r : Fin 18) (e : T.Edge) :
    ((leftPositive18 T r e : ℤ) + rightPositive18 T r e) -
      ((leftNegative18 T r e : ℤ) + rightNegative18 T r e) = 4 := by
  have hp := cutPositiveCounts_total18 hL r e
  have hn := cutNegativeCounts_total18 hL r e
  have hpZ : (leftPositive18 T r e : ℤ) + rightPositive18 T r e = 11 := by
    exact_mod_cast hp
  have hnZ : (leftNegative18 T r e : ℤ) + rightNegative18 T r e = 7 := by
    exact_mod_cast hn
  omega

/-- The exact order-18 side-feasibility constraints from the actual cut.
The first conjunct is the parity constraint on the left signed mass; the
remaining conjuncts are the two absolute-value bounds. -/
theorem T8_actual_order18_side_feasibility
    {T : PosIntTree 18} (hL : IsLeech T) (r : Fin 18) (e : T.Edge) :
    leftImbalance18 T r e % 2 = (T.cutSize e : ℤ) % 2 ∧
      -(T.cutSize e : ℤ) ≤ leftImbalance18 T r e ∧
      leftImbalance18 T r e ≤ (T.cutSize e : ℤ) ∧
      -((18 - T.cutSize e : ℕ) : ℤ) ≤ 4 - leftImbalance18 T r e ∧
      4 - leftImbalance18 T r e ≤ ((18 - T.cutSize e : ℕ) : ℤ) := by
  have ha := leftCounts_total18 T r e
  have hb := rightCounts_total18 T r e
  have hg := cutGlobalSignEquation18 hL r e
  have haZ :
      (leftPositive18 T r e : ℤ) + leftNegative18 T r e =
        (T.cutSize e : ℤ) := by
    exact_mod_cast ha
  have hbZ :
      (rightPositive18 T r e : ℤ) + rightNegative18 T r e =
        ((18 - T.cutSize e : ℕ) : ℤ) := by
    exact_mod_cast hb
  unfold leftImbalance18
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

noncomputable def leftPositiveDomain18
    (T : PosIntTree 18) (r : Fin 18) (e : T.Edge) :
    Finset (T.LeftVertex e) := by
  classical
  exact Finset.univ.filter fun u => normalizedParitySign18 T r u.1 = 1

noncomputable def leftNegativeDomain18
    (T : PosIntTree 18) (r : Fin 18) (e : T.Edge) :
    Finset (T.LeftVertex e) := by
  classical
  exact Finset.univ.filter fun u => normalizedParitySign18 T r u.1 = -1

noncomputable def rightPositiveDomain18
    (T : PosIntTree 18) (r : Fin 18) (e : T.Edge) :
    Finset (T.RightVertex e) := by
  classical
  exact Finset.univ.filter fun v => normalizedParitySign18 T r v.1 = 1

noncomputable def rightNegativeDomain18
    (T : PosIntTree 18) (r : Fin 18) (e : T.Edge) :
    Finset (T.RightVertex e) := by
  classical
  exact Finset.univ.filter fun v => normalizedParitySign18 T r v.1 = -1

private theorem subtypeFilter_card_eq_baseFilter
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (P : Vertex → Prop) [DecidablePred P] [Fintype {u : Vertex // P u}]
    (sign : Vertex → ℤ) (value : ℤ) :
    ((Finset.univ : Finset {u : Vertex // P u}).filter
        (fun u => sign u.1 = value)).card =
      ((Finset.univ.filter P).filter fun u => sign u = value).card := by
  classical
  calc
    ((Finset.univ : Finset {u : Vertex // P u}).filter
        (fun u => sign u.1 = value)).card =
        Fintype.card {u : {u : Vertex // P u} // sign u.1 = value} := by
      exact (Fintype.card_subtype _).symm
    _ = Fintype.card {u : Vertex // P u ∧ sign u = value} :=
      Fintype.card_congr
        (Equiv.subtypeSubtypeEquivSubtypeInter P (fun u => sign u = value))
    _ = ((Finset.univ.filter P).filter fun u => sign u = value).card := by
      rw [Fintype.card_subtype]
      congr 1
      ext u
      simp

theorem leftPositiveDomain18_card
    (T : PosIntTree 18) (r : Fin 18) (e : T.Edge) :
    (leftPositiveDomain18 T r e).card = leftPositive18 T r e := by
  classical
  exact subtypeFilter_card_eq_baseFilter
    (T.LeftCut e) (normalizedParitySign18 T r) 1

theorem leftNegativeDomain18_card
    (T : PosIntTree 18) (r : Fin 18) (e : T.Edge) :
    (leftNegativeDomain18 T r e).card = leftNegative18 T r e := by
  classical
  exact subtypeFilter_card_eq_baseFilter
    (T.LeftCut e) (normalizedParitySign18 T r) (-1)

theorem rightPositiveDomain18_card
    (T : PosIntTree 18) (r : Fin 18) (e : T.Edge) :
    (rightPositiveDomain18 T r e).card = rightPositive18 T r e := by
  classical
  exact subtypeFilter_card_eq_baseFilter
    (T.RightCut e) (normalizedParitySign18 T r) 1

theorem rightNegativeDomain18_card
    (T : PosIntTree 18) (r : Fin 18) (e : T.Edge) :
    (rightNegativeDomain18 T r e).card = rightNegative18 T r e := by
  classical
  exact subtypeFilter_card_eq_baseFilter
    (T.RightCut e) (normalizedParitySign18 T r) (-1)

/-- A duplicate-free exhaustive enumeration of the actual physical edges. -/
noncomputable def physicalEdgeList : List T.Edge :=
  (Finset.univ : Finset T.Edge).toList

theorem physicalEdgeList_nodup : (physicalEdgeList T).Nodup :=
  Finset.nodup_toList _

/-- Actual physical weights, cast only after their natural value is fixed. -/
def physicalWeightInt (e : T.Edge) : ℤ := T.weight e

/-- Actual unique-path incidence, cast from its natural `0/1` definition. -/
noncomputable def pathIncidenceInt (p : VertexPair n) (e : T.Edge) : ℤ :=
  T.pathIncidence p e

/-- Indexed unordered pairs whose actual distance has parity `p`. -/
noncomputable def pairParityBlock (p : ℕ) : Finset (VertexPair n) :=
  Finset.univ.filter fun q => T.pairDist q % 2 = p

/-- The exact target parity block at order `n`. -/
def targetParityBlock (n p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (targetN n)).filter fun k => k % 2 = p

theorem pathIncidenceInt_zero_one (p : VertexPair n) (e : T.Edge) :
    pathIncidenceInt T p e = 0 ∨ pathIncidenceInt T p e = 1 := by
  classical
  by_cases h : e.1 ∈ T.pathEdges p.left p.right
  · right
    simp [pathIncidenceInt, PosIntTree.pathIncidence, h]
  · left
    simp [pathIncidenceInt, PosIntTree.pathIncidence, h]

/-- The abstract list `pathValue` is exactly the actual indexed tree
distance. -/
theorem actual_pathValue (p : VertexPair n) :
    pathValue (physicalEdgeList T) (physicalWeightInt T)
      (pathIncidenceInt T) p = (T.pairDist p : ℤ) := by
  have hrow := congrArg (fun z : ℕ => (z : ℤ)) (T.pathIncidence_row p)
  simpa [pathValue, physicalEdgeList, physicalWeightInt, pathIncidenceInt,
    LeechTrees.weightedRow, mul_comm] using hrow

/-- `IsLeech` identifies the image of each actual indexed parity block with
the corresponding full target block. -/
theorem pairParityBlock_image (hL : IsLeech T) (p : ℕ) :
    (pairParityBlock T p).image T.pairDist = targetParityBlock n p := by
  classical
  ext k
  constructor
  · intro hk
    rcases Finset.mem_image.mp hk with ⟨q, hq, rfl⟩
    have hpar : T.pairDist q % 2 = p :=
      (Finset.mem_filter.mp hq).2
    exact Finset.mem_filter.mpr ⟨hL.pairDist_mem q, hpar⟩
  · intro hk
    have hk' := Finset.mem_filter.mp hk
    obtain ⟨q, hq, -⟩ := hL.target_existsUnique k hk'.1
    apply Finset.mem_image.mpr
    refine ⟨q, ?_, hq⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ q, by simpa [hq] using hk'.2⟩

/-- Every power sum on an actual indexed parity block is the corresponding
target power sum.  Injectivity is used before passing from indices to values. -/
theorem pairParityMoment_eq_target (hL : IsLeech T) (p k : ℕ) :
    (∑ q ∈ pairParityBlock T p, (T.pairDist q : ℤ) ^ k) =
      ∑ t ∈ targetParityBlock n p, (t : ℤ) ^ k := by
  classical
  rw [← pairParityBlock_image T hL p, Finset.sum_image]
  intro q hq q' hq' heq
  exact hL.pairDist_injective heq

/-! ## T8: actual path supports and global parity-resolved moments -/

/-- Actual indexed unordered pairs whose canonical physical path contains
every edge in `F`. -/
noncomputable def pathSupport (F : Finset T.Edge) : Finset (VertexPair n) :=
  Finset.univ.filter fun q =>
    ∀ e ∈ F, e.1 ∈ T.pathEdges q.left q.right

/-- The actual ordinary path coefficient of an edge set. -/
noncomputable def actualPathCoefficient (F : Finset T.Edge) : ℕ :=
  (pathSupport T F).card

/-- The actual signed path coefficient of an edge set. -/
noncomputable def actualSignedPathCoefficient
    (sign : Fin n → ℤ) (F : Finset T.Edge) : ℤ :=
  ∑ q : {q : VertexPair n // q ∈ pathSupport T F},
    sign q.1.left * sign q.1.right

/-- The complete actual noncollinear branch of T8.  The displayed hypothesis
is exactly that no indexed vertex-pair path contains all of `F`; no outer
component construction is assumed. -/
theorem T8_actual_noncollinear_zero
    (sign : Fin n → ℤ) (F : Finset T.Edge) (F_nonempty : F.Nonempty)
    (not_contained : ¬∃ q : VertexPair n,
      ∀ e ∈ F, e.1 ∈ T.pathEdges q.left q.right) :
    actualPathCoefficient T F = 0 ∧
      actualSignedPathCoefficient T sign F = 0 := by
  have _ := F_nonempty
  have hs : pathSupport T F = ∅ := by
    classical
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    apply not_contained
    exact ⟨q, (Finset.mem_filter.mp hq).2⟩
  constructor
  · simp [actualPathCoefficient, hs]
  · unfold actualSignedPathCoefficient
    change (∑ q ∈ (pathSupport T F).attach,
      sign q.1.left * sign q.1.right) = 0
    rw [hs]
    simp

/-- Exact remaining interface for the collinear outer-component geometry.
An adapter certificate is an equivalence between the actual indexed support
and the two outer vertex components, together with preservation of the
endpoint sign product.  Constructing this certificate from the extreme edges
of an arbitrary collinear nonempty `F` is the one T8 graph-geometric lemma
not supplied by `Foundations`. -/
structure OuterCertificate (sign : Fin n → ℤ) (F : Finset T.Edge) where
  left : Finset (Fin n)
  right : Finset (Fin n)
  equiv : {q : VertexPair n // q ∈ pathSupport T F} ≃
    ({u : Fin n // u ∈ left} × {v : Fin n // v ∈ right})
  sign_product : ∀ q,
    sign q.1.left * sign q.1.right =
      sign (equiv q).1.1 * sign (equiv q).2.1

/-- Exact named T8 blocker.  This proposition records, but deliberately does
not assert, the missing construction of an outer certificate for every
nonempty edge set lying on one canonical path.  Proving it from tree data
requires an order on the selected path edges, extreme-edge selection, and the
outer-component endpoint equivalence; those APIs are absent from the frozen
`Foundations` module. -/
def T8CollinearOuterCertificateRequired (T : PosIntTree n) : Prop :=
  ∀ (sign : Fin n → ℤ) (F : Finset T.Edge),
    F.Nonempty → (pathSupport T F).Nonempty →
      Nonempty (OuterCertificate T sign F)

/-- T8 outer-component factorization from the exact outstanding geometric
certificate.  The theorem itself now uses the actual path support. -/
theorem T8_actual_collinear_outer_factorization
    (sign : Fin n → ℤ) (F : Finset T.Edge)
    (cert : OuterCertificate T sign F) :
    actualPathCoefficient T F = cert.left.card * cert.right.card ∧
    actualSignedPathCoefficient T sign F =
      signedMass sign cert.left * signedMass sign cert.right := by
  classical
  constructor
  · unfold actualPathCoefficient
    calc
      (pathSupport T F).card =
          Fintype.card {q : VertexPair n // q ∈ pathSupport T F} := by
        simp
      _ = Fintype.card
          ({u : Fin n // u ∈ cert.left} ×
            {v : Fin n // v ∈ cert.right}) :=
        Fintype.card_congr cert.equiv
      _ = cert.left.card * cert.right.card := by simp
  · unfold actualSignedPathCoefficient
    calc
      (∑ q : {q : VertexPair n // q ∈ pathSupport T F},
          sign q.1.left * sign q.1.right) =
        ∑ x : ({u : Fin n // u ∈ cert.left} ×
            {v : Fin n // v ∈ cert.right}),
            sign x.1.1 * sign x.2.1 := by
        apply Fintype.sum_equiv cert.equiv
          (fun q => sign q.1.left * sign q.1.right)
          (fun x => sign x.1.1 * sign x.2.1)
        intro q
        exact cert.sign_product q
      _ = signedMass sign cert.left * signedMass sign cert.right := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.univ_eq_attach]
        unfold signedMass
        rw [← Finset.sum_attach cert.left sign,
          ← Finset.sum_attach cert.right sign]
        rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum]

/-- Claim-level T8 moment identities instantiated with the actual exhaustive
physical-edge list, actual unique-path incidence, and the exact `IsLeech`
target parity block. -/
theorem T8_actual_parity_resolved_path_moments
    (hL : IsLeech T) (p : ℕ) :
    ((∑ t ∈ targetParityBlock n p, (t : ℤ)) =
      ((physicalEdgeList T).map fun e =>
        singletonCoefficient (pairParityBlock T p) (pathIncidenceInt T) e *
          physicalWeightInt T e).sum) ∧
    ((∑ t ∈ targetParityBlock n p, (t : ℤ) ^ 2) =
      ((physicalEdgeList T).map fun e =>
        singletonCoefficient (pairParityBlock T p) (pathIncidenceInt T) e *
          physicalWeightInt T e ^ 2).sum +
        2 * pairSum (physicalEdgeList T) (fun e f =>
          pairCoefficient (pairParityBlock T p) (pathIncidenceInt T) e f *
            physicalWeightInt T e * physicalWeightInt T f)) ∧
    ((∑ t ∈ targetParityBlock n p, (t : ℤ) ^ 3) =
      ((physicalEdgeList T).map fun e =>
        singletonCoefficient (pairParityBlock T p) (pathIncidenceInt T) e *
          physicalWeightInt T e ^ 3).sum +
        3 * pairSum (physicalEdgeList T) (fun e f =>
          pairCoefficient (pairParityBlock T p) (pathIncidenceInt T) e f *
            (physicalWeightInt T e ^ 2 * physicalWeightInt T f +
              physicalWeightInt T e * physicalWeightInt T f ^ 2)) +
        6 * tripleSum (physicalEdgeList T) (fun e f g =>
          tripleCoefficient (pairParityBlock T p) (pathIncidenceInt T) e f g *
            physicalWeightInt T e * physicalWeightInt T f *
              physicalWeightInt T g)) := by
  have hm := T8_parity_resolved_path_moments
    (physicalEdgeList T) (physicalWeightInt T) (pathIncidenceInt T)
    (pairParityBlock T p)
    (fun q _ e => pathIncidenceInt_zero_one T q e)
  rcases hm with ⟨hm1, hm2, hm3⟩
  constructor
  · calc
      (∑ t ∈ targetParityBlock n p, (t : ℤ)) =
          ∑ q ∈ pairParityBlock T p, (T.pairDist q : ℤ) :=
        by simpa using (pairParityMoment_eq_target T hL p 1).symm
      _ = ∑ q ∈ pairParityBlock T p,
          pathValue (physicalEdgeList T) (physicalWeightInt T)
            (pathIncidenceInt T) q := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [actual_pathValue]
      _ = _ := hm1
  constructor
  · calc
      (∑ t ∈ targetParityBlock n p, (t : ℤ) ^ 2) =
          ∑ q ∈ pairParityBlock T p, (T.pairDist q : ℤ) ^ 2 :=
        (pairParityMoment_eq_target T hL p 2).symm
      _ = ∑ q ∈ pairParityBlock T p,
          pathValue (physicalEdgeList T) (physicalWeightInt T)
            (pathIncidenceInt T) q ^ 2 := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [actual_pathValue]
      _ = _ := hm2
  · calc
      (∑ t ∈ targetParityBlock n p, (t : ℤ) ^ 3) =
          ∑ q ∈ pairParityBlock T p, (T.pairDist q : ℤ) ^ 3 :=
        (pairParityMoment_eq_target T hL p 3).symm
      _ = ∑ q ∈ pairParityBlock T p,
          pathValue (physicalEdgeList T) (physicalWeightInt T)
            (pathIncidenceInt T) q ^ 3 := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [actual_pathValue]
      _ = _ := hm3

/-- The three actual edge-coefficient expansions, named for concise
order-18 claim statements. -/
noncomputable def actualMomentExpansion1
    (T : PosIntTree n) (p : ℕ) : ℤ :=
  ((physicalEdgeList T).map fun e =>
    singletonCoefficient (pairParityBlock T p) (pathIncidenceInt T) e *
      physicalWeightInt T e).sum

noncomputable def actualMomentExpansion2
    (T : PosIntTree n) (p : ℕ) : ℤ :=
  ((physicalEdgeList T).map fun e =>
    singletonCoefficient (pairParityBlock T p) (pathIncidenceInt T) e *
      physicalWeightInt T e ^ 2).sum +
    2 * pairSum (physicalEdgeList T) (fun e f =>
      pairCoefficient (pairParityBlock T p) (pathIncidenceInt T) e f *
        physicalWeightInt T e * physicalWeightInt T f)

noncomputable def actualMomentExpansion3
    (T : PosIntTree n) (p : ℕ) : ℤ :=
  ((physicalEdgeList T).map fun e =>
    singletonCoefficient (pairParityBlock T p) (pathIncidenceInt T) e *
      physicalWeightInt T e ^ 3).sum +
    3 * pairSum (physicalEdgeList T) (fun e f =>
      pairCoefficient (pairParityBlock T p) (pathIncidenceInt T) e f *
        (physicalWeightInt T e ^ 2 * physicalWeightInt T f +
          physicalWeightInt T e * physicalWeightInt T f ^ 2)) +
    6 * tripleSum (physicalEdgeList T) (fun e f g =>
      tripleCoefficient (pairParityBlock T p) (pathIncidenceInt T) e f g *
        physicalWeightInt T e * physicalWeightInt T f * physicalWeightInt T g)

theorem order18TargetParityMomentsInt :
    (∑ t ∈ targetParityBlock 18 0, (t : ℤ)) = 5852 ∧
    (∑ t ∈ targetParityBlock 18 1, (t : ℤ)) = 5929 ∧
    (∑ t ∈ targetParityBlock 18 0, (t : ℤ) ^ 2) = 596904 ∧
    (∑ t ∈ targetParityBlock 18 1, (t : ℤ) ^ 2) = 608685 ∧
    (∑ t ∈ targetParityBlock 18 0, (t : ℤ) ^ 3) = 68491808 ∧
    (∑ t ∈ targetParityBlock 18 1, (t : ℤ) ^ 3) = 70300153 := by
  decide

/-- The exact numerical order-18 T8 moment system for the actual physical
edge coefficients and actual unique-path incidence. -/
theorem T8_actual_order18_parity_moment_system
    {T : PosIntTree 18} (hL : IsLeech T) :
    actualMomentExpansion1 T 0 = 5852 ∧
    actualMomentExpansion1 T 1 = 5929 ∧
    actualMomentExpansion2 T 0 = 596904 ∧
    actualMomentExpansion2 T 1 = 608685 ∧
    actualMomentExpansion3 T 0 = 68491808 ∧
    actualMomentExpansion3 T 1 = 70300153 := by
  rcases T8_actual_parity_resolved_path_moments T hL 0 with
    ⟨he1, he2, he3⟩
  rcases T8_actual_parity_resolved_path_moments T hL 1 with
    ⟨ho1, ho2, ho3⟩
  rcases order18TargetParityMomentsInt with
    ⟨hc1e, hc1o, hc2e, hc2o, hc3e, hc3o⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      actualMomentExpansion1 T 0 =
          ∑ t ∈ targetParityBlock 18 0, (t : ℤ) := by
        simpa [actualMomentExpansion1] using he1.symm
      _ = 5852 := hc1e
  · calc
      actualMomentExpansion1 T 1 =
          ∑ t ∈ targetParityBlock 18 1, (t : ℤ) := by
        simpa [actualMomentExpansion1] using ho1.symm
      _ = 5929 := hc1o
  · calc
      actualMomentExpansion2 T 0 =
          ∑ t ∈ targetParityBlock 18 0, (t : ℤ) ^ 2 := by
        simpa [actualMomentExpansion2] using he2.symm
      _ = 596904 := hc2e
  · calc
      actualMomentExpansion2 T 1 =
          ∑ t ∈ targetParityBlock 18 1, (t : ℤ) ^ 2 := by
        simpa [actualMomentExpansion2] using ho2.symm
      _ = 608685 := hc2o
  · calc
      actualMomentExpansion3 T 0 =
          ∑ t ∈ targetParityBlock 18 0, (t : ℤ) ^ 3 := by
        simpa [actualMomentExpansion3] using he3.symm
      _ = 68491808 := hc3e
  · calc
      actualMomentExpansion3 T 1 =
          ∑ t ∈ targetParityBlock 18 1, (t : ℤ) ^ 3 := by
        simpa [actualMomentExpansion3] using ho3.symm
      _ = 70300153 := hc3o

/-! ## T9: the actual cross-distance parity image of one physical edge -/

/-- Actual indexed cross pairs in one parity class. -/
noncomputable def crossParityDomain (e : T.Edge) (p : ℕ) :
    Finset (T.LeftVertex e × T.RightVertex e) :=
  Finset.univ.filter fun x => T.rootedCrossSum e x % 2 = p

/-- Actual value image of that indexed cross block. -/
noncomputable def crossParityBlock (e : T.Edge) (p : ℕ) : Finset ℕ :=
  (crossParityDomain T e p).image (T.rootedCrossSum e)

theorem crossParityBlock_card (hL : IsLeech T) (e : T.Edge) (p : ℕ) :
    (crossParityBlock T e p).card = (crossParityDomain T e p).card := by
  classical
  exact Finset.card_image_of_injective _ (T.rootedCrossSum_injective hL e)

theorem normalizedCrossSign18
    (T : PosIntTree 18) (r : Fin 18) (e : T.Edge)
    (x : T.LeftVertex e × T.RightVertex e) :
    normalizedParitySign18 T r x.1.1 * normalizedParitySign18 T r x.2.1 =
      paritySign (T.rootedCrossSum e x) := by
  calc
    normalizedParitySign18 T r x.1.1 * normalizedParitySign18 T r x.2.1 =
        paritySign (T.dist x.1.1 x.2.1) :=
      normalizedParitySign18_pair T r x.1.1 x.2.1
    _ = paritySign (T.rootedCrossSum e x) := by
      congr 1
      simpa [PosIntTree.rootedCrossSum, PosIntTree.leftDepth,
        PosIntTree.rightDepth] using
        T.cross_distance_decomposition e x.1.2 x.2.2

theorem rootedCrossSum_even_iff_same_sign18
    (T : PosIntTree 18) (r : Fin 18) (e : T.Edge)
    (x : T.LeftVertex e × T.RightVertex e) :
    T.rootedCrossSum e x % 2 = 0 ↔
      (normalizedParitySign18 T r x.1.1 = 1 ∧
        normalizedParitySign18 T r x.2.1 = 1) ∨
      (normalizedParitySign18 T r x.1.1 = -1 ∧
        normalizedParitySign18 T r x.2.1 = -1) := by
  rw [← paritySign_eq_one_iff_mod_two]
  rw [← normalizedCrossSign18 T r e x]
  rcases normalizedParitySign18_pm T r x.1.1 with hl | hl <;>
    rcases normalizedParitySign18_pm T r x.2.1 with hr | hr <;>
    simp [hl, hr]

theorem rootedCrossSum_odd_iff_opposite_sign18
    (T : PosIntTree 18) (r : Fin 18) (e : T.Edge)
    (x : T.LeftVertex e × T.RightVertex e) :
    T.rootedCrossSum e x % 2 = 1 ↔
      (normalizedParitySign18 T r x.1.1 = 1 ∧
        normalizedParitySign18 T r x.2.1 = -1) ∨
      (normalizedParitySign18 T r x.1.1 = -1 ∧
        normalizedParitySign18 T r x.2.1 = 1) := by
  rw [← paritySign_eq_neg_one_iff_mod_two]
  rw [← normalizedCrossSign18 T r e x]
  rcases normalizedParitySign18_pm T r x.1.1 with hl | hl <;>
    rcases normalizedParitySign18_pm T r x.2.1 with hr | hr <;>
    simp [hl, hr]

private noncomputable def sameSignDomain18
    (T : PosIntTree 18) (r : Fin 18) (e : T.Edge) :
    Finset (T.LeftVertex e × T.RightVertex e) :=
  (leftPositiveDomain18 T r e ×ˢ rightPositiveDomain18 T r e) ∪
    (leftNegativeDomain18 T r e ×ˢ rightNegativeDomain18 T r e)

private noncomputable def oppositeSignDomain18
    (T : PosIntTree 18) (r : Fin 18) (e : T.Edge) :
    Finset (T.LeftVertex e × T.RightVertex e) :=
  (leftPositiveDomain18 T r e ×ˢ rightNegativeDomain18 T r e) ∪
    (leftNegativeDomain18 T r e ×ˢ rightPositiveDomain18 T r e)

theorem crossParityDomain_zero_eq_sameSign18
    (T : PosIntTree 18) (r : Fin 18) (e : T.Edge) :
    crossParityDomain T e 0 = sameSignDomain18 T r e := by
  classical
  ext x
  simpa [crossParityDomain, sameSignDomain18,
    leftPositiveDomain18, leftNegativeDomain18,
    rightPositiveDomain18, rightNegativeDomain18] using
    rootedCrossSum_even_iff_same_sign18 T r e x

theorem crossParityDomain_one_eq_oppositeSign18
    (T : PosIntTree 18) (r : Fin 18) (e : T.Edge) :
    crossParityDomain T e 1 = oppositeSignDomain18 T r e := by
  classical
  ext x
  simpa [crossParityDomain, oppositeSignDomain18,
    leftPositiveDomain18, leftNegativeDomain18,
    rightPositiveDomain18, rightNegativeDomain18] using
    rootedCrossSum_odd_iff_opposite_sign18 T r e x

private theorem sameSignDomain18_card
    (T : PosIntTree 18) (r : Fin 18) (e : T.Edge) :
    (sameSignDomain18 T r e).card =
      leftPositive18 T r e * rightPositive18 T r e +
        leftNegative18 T r e * rightNegative18 T r e := by
  classical
  have hdisj : Disjoint
      (leftPositiveDomain18 T r e ×ˢ rightPositiveDomain18 T r e)
      (leftNegativeDomain18 T r e ×ˢ rightNegativeDomain18 T r e) := by
    rw [Finset.disjoint_left]
    intro x hp hn
    have hpL := (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
    have hnL := (Finset.mem_filter.mp (Finset.mem_product.mp hn).1).2
    omega
  unfold sameSignDomain18
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_product,
    Finset.card_product, leftPositiveDomain18_card,
    rightPositiveDomain18_card, leftNegativeDomain18_card,
    rightNegativeDomain18_card]

private theorem oppositeSignDomain18_card
    (T : PosIntTree 18) (r : Fin 18) (e : T.Edge) :
    (oppositeSignDomain18 T r e).card =
      leftPositive18 T r e * rightNegative18 T r e +
        leftNegative18 T r e * rightPositive18 T r e := by
  classical
  have hdisj : Disjoint
      (leftPositiveDomain18 T r e ×ˢ rightNegativeDomain18 T r e)
      (leftNegativeDomain18 T r e ×ˢ rightPositiveDomain18 T r e) := by
    rw [Finset.disjoint_left]
    intro x hp hn
    have hpL := (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
    have hnL := (Finset.mem_filter.mp (Finset.mem_product.mp hn).1).2
    omega
  unfold oppositeSignDomain18
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_product,
    Finset.card_product, leftPositiveDomain18_card,
    rightNegativeDomain18_card, leftNegativeDomain18_card,
    rightPositiveDomain18_card]

theorem crossParityBlock_zero_card18
    {T : PosIntTree 18} (hL : IsLeech T) (r : Fin 18) (e : T.Edge) :
    (crossParityBlock T e 0).card =
      leftPositive18 T r e * rightPositive18 T r e +
        leftNegative18 T r e * rightNegative18 T r e := by
  rw [crossParityBlock_card T hL e 0,
    crossParityDomain_zero_eq_sameSign18,
    sameSignDomain18_card]

theorem crossParityBlock_one_card18
    {T : PosIntTree 18} (hL : IsLeech T) (r : Fin 18) (e : T.Edge) :
    (crossParityBlock T e 1).card =
      leftPositive18 T r e * rightNegative18 T r e +
        leftNegative18 T r e * rightPositive18 T r e := by
  rw [crossParityBlock_card T hL e 1,
    crossParityDomain_one_eq_oppositeSign18,
    oppositeSignDomain18_card]

/-- The actual cross-distance value block lies in the exact target parity
tail beginning at the physical edge weight. -/
theorem crossParityBlock_subset_tail (hL : IsLeech T) (e : T.Edge) (p : ℕ) :
    crossParityBlock T e p ⊆
      parityTail (targetN n) (T.weight e) p := by
  classical
  intro t ht
  rcases Finset.mem_image.mp ht with ⟨x, hx, rfl⟩
  have hpar : T.rootedCrossSum e x % 2 = p :=
    (Finset.mem_filter.mp hx).2
  apply Finset.mem_filter.mpr
  exact ⟨T.rootedCrossSum_mem_target_tail hL e x, hpar⟩

/-- Claim-level T9 for the actual injective cross-distance image of every
physical edge.  Positivity is required only for the largest-element capacity
conclusion, exactly as in the paper audit. -/
theorem T9_actual_edge_parity_tail
    (hL : IsLeech T) (e : T.Edge) (p : ℕ) (hp : p < 2)
    (hpos : 0 < (crossParityBlock T e p).card) :
    ((∑ j ∈ Finset.range (crossParityBlock T e p).card,
        (parityStart (T.weight e) p + 2 * j)) ≤
      ∑ t ∈ crossParityBlock T e p, t) ∧
    ((∑ j ∈ Finset.range (crossParityBlock T e p).card,
        (parityStart (T.weight e) p + 2 * j) ^ 2) ≤
      ∑ t ∈ crossParityBlock T e p, t ^ 2) ∧
    ((∑ j ∈ Finset.range (crossParityBlock T e p).card,
        (parityStart (T.weight e) p + 2 * j) ^ 3) ≤
      ∑ t ∈ crossParityBlock T e p, t ^ 3) ∧
    ((∑ t ∈ crossParityBlock T e p, t) ≤
      ∑ t ∈ parityTail (targetN n) (T.weight e) p, t) ∧
    ((∑ t ∈ crossParityBlock T e p, t ^ 2) ≤
      ∑ t ∈ parityTail (targetN n) (T.weight e) p, t ^ 2) ∧
    ((∑ t ∈ crossParityBlock T e p, t ^ 3) ≤
      ∑ t ∈ parityTail (targetN n) (T.weight e) p, t ^ 3) ∧
    parityStart (T.weight e) p +
      2 * ((crossParityBlock T e p).card - 1) ≤ targetN n := by
  exact T9_parity_tail_spacing
    (crossParityBlock T e p) (targetN n) (T.weight e) p
    (crossParityBlock T e p).card hp hpos rfl
    (crossParityBlock_subset_tail T hL e p)

/-- Actual T9 saturation identifies the complete cross-distance value image,
not the ownership of individual target values. -/
theorem T9_actual_edge_saturation
    (hL : IsLeech T) (e : T.Edge) (p : ℕ)
    (same_card : (crossParityBlock T e p).card =
      (parityTail (targetN n) (T.weight e) p).card) :
    crossParityBlock T e p =
      parityTail (targetN n) (T.weight e) p := by
  exact T9_saturated_parity_tail _ _ _
    (crossParityBlock_subset_tail T hL e p) same_card

/-! ## T10/T10b: actual order-18 physical-edge implications -/

/-- Full graph-level T10 implication for an actual order-18 `IsLeech` tree
and an actual physical edge of weight 67 with a `9|9` deletion cut.  The root
sign is normalized canonically to global mass four; no largest-edge,
existence, or exclusion premise is used. -/
theorem T10_actual_weight67_nine_nine
    {T : PosIntTree 18} (hL : IsLeech T) (r : Fin 18) (e : T.Edge)
    (weight_eq : T.weight e = 67) (split_eq : T.cutSize e = 9) :
    leftImbalance18 T r e = -1 ∨
    leftImbalance18 T r e = 1 ∨
    leftImbalance18 T r e = 3 ∨
    leftImbalance18 T r e = 5 := by
  apply T10_weight67_nine_nine
    (leftPositive18 T r e) (leftNegative18 T r e)
    (rightPositive18 T r e) (rightNegative18 T r e)
    (leftImbalance18 T r e)
    (crossParityBlock T e 0) (crossParityBlock T e 1)
  · simpa [split_eq] using leftCounts_total18 T r e
  · have hr := rightCounts_total18 T r e
    omega
  · rfl
  · exact cutGlobalSignEquation18 hL r e
  · exact crossParityBlock_zero_card18 hL r e
  · exact crossParityBlock_one_card18 hL r e
  · simpa [targetN, weight_eq] using
      crossParityBlock_subset_tail T hL e 0
  · simpa [targetN, weight_eq] using
      crossParityBlock_subset_tail T hL e 1

/-- Full graph-level T10b implication for an actual order-18 `IsLeech` tree
and an actual physical edge of weight 68 with a `9|9` cut.  Only the paper's
local side-imbalance alternative remains as a hypothesis. -/
theorem T10b_actual_weight68_nine_nine
    {T : PosIntTree 18} (hL : IsLeech T) (r : Fin 18) (e : T.Edge)
    (weight_eq : T.weight e = 68) (split_eq : T.cutSize e = 9)
    (extreme_mass : leftImbalance18 T r e = -1 ∨
      leftImbalance18 T r e = 5) :
    crossParityBlock T e 1 = parityTail 153 68 1 ∧
    (crossParityBlock T e 1).image (fun t => t - 68) = oddResidual43 ∧
    (∑ t ∈ (crossParityBlock T e 1).image (fun t => t - 68), t) = 1849 ∧
    (∑ t ∈ (crossParityBlock T e 1).image (fun t => t - 68), t ^ 2) =
      105995 ∧
    (∑ t ∈ (crossParityBlock T e 1).image (fun t => t - 68), t ^ 3) =
      6835753 ∧
    (∑ t ∈ crossParityBlock T e 1, t) = 4773 ∧
    (∑ t ∈ crossParityBlock T e 1, t ^ 2) = 556291 ∧
    (∑ t ∈ crossParityBlock T e 1, t ^ 3) = 67628637 := by
  apply T10b_weight68_nine_nine
    (leftPositive18 T r e) (leftNegative18 T r e)
    (rightPositive18 T r e) (rightNegative18 T r e)
    (leftImbalance18 T r e) (crossParityBlock T e 1)
  · simpa [split_eq] using leftCounts_total18 T r e
  · have hr := rightCounts_total18 T r e
    omega
  · rfl
  · exact cutGlobalSignEquation18 hL r e
  · exact extreme_mass
  · exact crossParityBlock_one_card18 hL r e
  · simpa [targetN, weight_eq] using
      crossParityBlock_subset_tail T hL e 1

end LeechTrees.ParityTail.GraphAdapterV1
