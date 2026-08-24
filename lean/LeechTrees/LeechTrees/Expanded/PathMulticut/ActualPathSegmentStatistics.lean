import LeechTrees.Expanded.PathMulticut.SelectedBlockHall

/-!
# Actual punctured path-segment order statistics and variance

This is the graph endpoint for G004.  The two depth rows, the shifted
Cartesian block, its eligible punctured rank set, its sorted enumerations, and
the placement embedding are all constructed from an actual `PosIntTree`, an
actual selected-edge deletion, and one actual pair of deletion components.
No `OrderedPuncturedBlock` is assumed by a caller.
-/

open scoped BigOperators

namespace LeechTrees.PathMulticut

open LeechTrees.Foundation
open LeechTrees.OddQuotient
open LeechTrees.ParityTail.GraphAdapterV1
open LeechTrees.ParityTail.T8Collinear

noncomputable section

/-! ## A reusable canonical sorted enumeration -/

noncomputable def sortedFiniteEquiv {alpha : Type*} [Fintype alpha]
    (key : alpha → ℕ) : Fin (Fintype.card alpha) ≃ alpha :=
  let base : Fin (Fintype.card alpha) ≃ alpha :=
    (Fintype.equivFin alpha).symm
  let tupleKey : Fin (Fintype.card alpha) → ℕ := fun i => key (base i)
  (Tuple.sort tupleKey).trans base

theorem sortedFiniteEquiv_monotone {alpha : Type*} [Fintype alpha]
    (key : alpha → ℕ) :
    Monotone (fun i => key (sortedFiniteEquiv key i)) := by
  let base : Fin (Fintype.card alpha) ≃ alpha :=
    (Fintype.equivFin alpha).symm
  let tupleKey : Fin (Fintype.card alpha) → ℕ := fun i => key (base i)
  simpa [sortedFiniteEquiv, base, tupleKey, Function.comp_def] using
    Tuple.monotone_sort tupleKey

theorem sortedFiniteEquiv_strictMono {alpha : Type*} [Fintype alpha]
    (key : alpha → ℕ) (hinj : Function.Injective key) :
    StrictMono (fun i => key (sortedFiniteEquiv key i)) :=
  (sortedFiniteEquiv_monotone key).strictMono_of_injective
    (hinj.comp (sortedFiniteEquiv key).injective)

/-! ## Actual component depths and eligible punctured ranks -/

theorem selectedLeftDepth_injective {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) :
    Function.Injective (selectedLeftDepth T F q) := by
  let y0 := selectedTargetPort T F q
  intro x x' hxx
  have hsum : selectedCrossRank T F q (x, y0) =
      selectedCrossRank T F q (x', y0) := by
    simp only [selectedCrossRank]
    rw [hxx]
  exact congrArg Prod.fst (selectedCrossRank_injective hL F q hsum)

theorem selectedRightDepth_injective {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) :
    Function.Injective (selectedRightDepth T F q) := by
  let x0 := selectedSourcePort T F q
  intro y y' hyy
  have hsum : selectedCrossRank T F q (x0, y) =
      selectedCrossRank T F q (x0, y') := by
    simp only [selectedCrossRank]
    rw [hyy]
  exact congrArg Prod.snd (selectedCrossRank_injective hL F q hsum)

abbrev SelectedEligibleRank {n : ℕ} (T : PosIntTree n)
    (F : Finset T.Edge) (q : SelectedComponentPair T F) :=
  {d : ℕ // d ∈ selectedAllowedSet T F q}

def selectedEligibleOffset {n : ℕ} (T : PosIntTree n)
    (F : Finset T.Edge) (q : SelectedComponentPair T F)
    (d : SelectedEligibleRank T F q) : ℕ :=
  d.1 - selectedRouteLength T F q

theorem selectedEligibleOffset_injective {n : ℕ} (T : PosIntTree n)
    (F : Finset T.Edge) (q : SelectedComponentPair T F) :
    Function.Injective (selectedEligibleOffset T F q) := by
  intro d e hde
  apply Subtype.ext
  have hd := (Finset.mem_filter.mp d.2).1
  have he := (Finset.mem_filter.mp e.2).1
  obtain ⟨hdl, -⟩ := Finset.mem_Icc.mp hd
  obtain ⟨hel, -⟩ := Finset.mem_Icc.mp he
  simp only [selectedEligibleOffset] at hde
  omega

abbrev SelectedLeftSize {n : ℕ} (T : PosIntTree n)
    (F : Finset T.Edge) (q : SelectedComponentPair T F) :=
  Fintype.card (SelectedComponentVertex T F q.left)

abbrev SelectedRightSize {n : ℕ} (T : PosIntTree n)
    (F : Finset T.Edge) (q : SelectedComponentPair T F) :=
  Fintype.card (SelectedComponentVertex T F q.right)

abbrev SelectedEligibleSize {n : ℕ} (T : PosIntTree n)
    (F : Finset T.Edge) (q : SelectedComponentPair T F) :=
  Fintype.card (SelectedEligibleRank T F q)

noncomputable def selectedLeftOrder {n : ℕ} (T : PosIntTree n)
    (F : Finset T.Edge) (q : SelectedComponentPair T F) :
    Fin (SelectedLeftSize T F q) ≃ SelectedComponentVertex T F q.left :=
  sortedFiniteEquiv (selectedLeftDepth T F q)

noncomputable def selectedRightOrder {n : ℕ} (T : PosIntTree n)
    (F : Finset T.Edge) (q : SelectedComponentPair T F) :
    Fin (SelectedRightSize T F q) ≃ SelectedComponentVertex T F q.right :=
  sortedFiniteEquiv (selectedRightDepth T F q)

noncomputable def selectedEligibleOrder {n : ℕ} (T : PosIntTree n)
    (F : Finset T.Edge) (q : SelectedComponentPair T F) :
    Fin (SelectedEligibleSize T F q) ≃ SelectedEligibleRank T F q :=
  sortedFiniteEquiv (selectedEligibleOffset T F q)

/-- The actual placement of every Cartesian component pair into its unique
eligible punctured rank. -/
noncomputable def selectedBlockPlace {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) :
    Fin (SelectedLeftSize T F q) × Fin (SelectedRightSize T F q) ↪
      Fin (SelectedEligibleSize T F q) where
  toFun z := (selectedEligibleOrder T F q).symm ⟨
    selectedCrossRank T F q
      (selectedLeftOrder T F q z.1, selectedRightOrder T F q z.2),
    selectedBlock_subset_allowed hL F q <| Finset.mem_image.mpr
      ⟨(selectedLeftOrder T F q z.1, selectedRightOrder T F q z.2),
        Finset.mem_univ _, rfl⟩⟩
  inj' := by
    intro z z' hzz
    have hrank :
        selectedCrossRank T F q
            (selectedLeftOrder T F q z.1, selectedRightOrder T F q z.2) =
          selectedCrossRank T F q
            (selectedLeftOrder T F q z'.1, selectedRightOrder T F q z'.2) := by
      exact congrArg Subtype.val <|
        (selectedEligibleOrder T F q).symm.injective hzz
    have hp := selectedCrossRank_injective hL F q hrank
    apply Prod.ext
    · exact (selectedLeftOrder T F q).injective (congrArg Prod.fst hp)
    · exact (selectedRightOrder T F q).injective (congrArg Prod.snd hp)

/-- Constructed graph-to-`OrderedPuncturedBlock` adapter. -/
noncomputable def actualOrderedPuncturedBlock {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) :
    OrderedPuncturedBlock
      (SelectedLeftSize T F q) (SelectedRightSize T F q)
      (SelectedEligibleSize T F q) where
  leftDepth := fun i => selectedLeftDepth T F q (selectedLeftOrder T F q i)
  rightDepth := fun j => selectedRightDepth T F q (selectedRightOrder T F q j)
  eligibleOffset := fun k =>
    selectedEligibleOffset T F q (selectedEligibleOrder T F q k)
  place := selectedBlockPlace hL F q
  left_strict := sortedFiniteEquiv_strictMono _
    (selectedLeftDepth_injective hL F q)
  right_strict := sortedFiniteEquiv_strictMono _
    (selectedRightDepth_injective hL F q)
  eligible_strict := sortedFiniteEquiv_strictMono _
    (selectedEligibleOffset_injective T F q)
  place_value := by
    intro z
    simp [selectedBlockPlace, selectedEligibleOffset, selectedCrossRank]
    omega

theorem actualOrderedPuncturedBlock_fit {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) :
    SelectedLeftSize T F q * SelectedRightSize T F q ≤
      SelectedEligibleSize T F q := by
  have hsub := Finset.card_le_card (selectedBlock_subset_allowed hL F q)
  rw [selectedBlock_card hL F q] at hsub
  simpa [selectedBlockDemand] using hsub

/-- Formula (8) for the actual graph-derived path-segment block. -/
theorem actual_selectedSegment_rectangle_order_statistics {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) (F : Finset T.Edge)
    (q : SelectedComponentPair T F)
    (i : Fin (SelectedLeftSize T F q))
    (j : Fin (SelectedRightSize T F q)) :
    let B := actualOrderedPuncturedBlock hL F q
    B.eligibleOffset
        ⟨(i.1 + 1) * (j.1 + 1) - 1, by
          have hi : i.1 + 1 ≤ SelectedLeftSize T F q :=
            Nat.succ_le_iff.mpr i.2
          have hj : j.1 + 1 ≤ SelectedRightSize T F q :=
            Nat.succ_le_iff.mpr j.2
          have hf := actualOrderedPuncturedBlock_fit hL F q
          have hprod := (Nat.mul_le_mul hi hj).trans hf
          have hpos := Nat.mul_pos (Nat.succ_pos i.1) (Nat.succ_pos j.1)
          exact (Nat.sub_lt hpos (by decide)).trans_le hprod⟩ ≤
      B.leftDepth i + B.rightDepth j ∧
    B.leftDepth i + B.rightDepth j ≤
      B.eligibleOffset
        ⟨SelectedEligibleSize T F q -
            ((SelectedLeftSize T F q - i.1) *
              (SelectedRightSize T F q - j.1)), by
          have hi : 0 < SelectedLeftSize T F q - i.1 :=
            Nat.sub_pos_of_lt i.2
          have hj : 0 < SelectedRightSize T F q - j.1 :=
            Nat.sub_pos_of_lt j.2
          have hle := actualOrderedPuncturedBlock_fit hL F q
          have hprod :
              (SelectedLeftSize T F q - i.1) *
                  (SelectedRightSize T F q - j.1) ≤
                SelectedLeftSize T F q * SelectedRightSize T F q :=
            Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
          have hpos := Nat.mul_pos hi hj
          omega⟩ := by
  exact (actualOrderedPuncturedBlock hL F q).rectangle_order_statistics
    (actualOrderedPuncturedBlock_fit hL F q) i j

/-- G004 graph bundle: exact block size/shifted direct-sum construction,
puncture alternatives, and both order-statistic inequalities. -/
theorem actual_selectedSegment_block_and_puncture {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) :
    (selectedBlock T F q).card = selectedBlockDemand T F q ∧
    selectedBlock T F q ⊆
      Finset.Icc (selectedRouteLength T F q) (targetN n) ∧
    (selectedRouteHops T F q = 1 →
      selectedBlock T F q ∩ physicalWeightSet T =
        {selectedRouteLength T F q}) ∧
    (2 ≤ selectedRouteHops T F q →
      selectedBlock T F q ∩ physicalWeightSet T = ∅) := by
  exact ⟨selectedBlock_card hL F q,
    selectedBlock_subset_interval hL F q,
    selectedBlock_inter_physical_eq_singleton_of_one_hop hL F q,
    selectedBlock_inter_physical_eq_empty_of_two_le hL F q⟩

/-! ## Actual direct-sum variance and its equality case -/

def selectedLeftDelta {n : ℕ} (T : PosIntTree n) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) : ℤ :=
  indexedDelta fun x : SelectedComponentVertex T F q.left =>
    (selectedLeftDepth T F q x : ℤ)

def selectedRightDelta {n : ℕ} (T : PosIntTree n) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) : ℤ :=
  indexedDelta fun y : SelectedComponentVertex T F q.right =>
    (selectedRightDepth T F q y : ℤ)

def selectedOffsetRank {n : ℕ} (T : PosIntTree n) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) (z : SelectedBlockIndex T F q) : ℕ :=
  selectedLeftDepth T F q z.1 + selectedRightDepth T F q z.2

theorem selectedOffsetRank_injective {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) :
    Function.Injective (selectedOffsetRank T F q) := by
  intro x y hxy
  apply selectedCrossRank_injective hL F q
  simpa only [selectedCrossRank, selectedOffsetRank, Nat.add_assoc] using
    congrArg (fun k => selectedRouteLength T F q + k) hxy

theorem actual_selectedSegment_variance_identity {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) :
    indexedDelta (fun z : SelectedBlockIndex T F q =>
      (selectedOffsetRank T F q z : ℤ)) =
      (SelectedRightSize T F q : ℤ) ^ 2 * selectedLeftDelta T F q +
        (SelectedLeftSize T F q : ℤ) ^ 2 * selectedRightDelta T F q := by
  exact indexedDelta_add_product
    (fun x : SelectedComponentVertex T F q.left =>
      (selectedLeftDepth T F q x : ℤ))
    (fun y : SelectedComponentVertex T F q.right =>
      (selectedRightDepth T F q y : ℤ))

/-- Division-free variance lower bound for the actual block. -/
theorem actual_selectedSegment_variance_lower {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) :
    let m := SelectedLeftSize T F q * SelectedRightSize T F q
    (m : ℤ) ^ 2 * ((m : ℤ) ^ 2 - 1) ≤
      12 * ((SelectedRightSize T F q : ℤ) ^ 2 *
          selectedLeftDelta T F q +
        (SelectedLeftSize T F q : ℤ) ^ 2 *
          selectedRightDelta T F q) := by
  let m := SelectedLeftSize T F q * SelectedRightSize T F q
  have h := indexedDelta_injective_ge_consecutive
    (selectedOffsetRank T F q) (selectedOffsetRank_injective hL F q)
  rw [actual_selectedSegment_variance_identity] at h
  simpa [m] using h

noncomputable def selectedOffsetOrder {n : ℕ} (T : PosIntTree n)
    (F : Finset T.Edge) (q : SelectedComponentPair T F) :
    Fin (SelectedLeftSize T F q * SelectedRightSize T F q) ≃
      SelectedBlockIndex T F q := by
  have hcard : Fintype.card (SelectedBlockIndex T F q) =
      SelectedLeftSize T F q * SelectedRightSize T F q := by
    simp [SelectedBlockIndex]
  exact (finCongr hcard.symm).trans
    (sortedFiniteEquiv (selectedOffsetRank T F q))

/-- Exact equality condition: equality in the actual variance lower bound
forces the sorted shifted block to have every adjacent gap equal to one, i.e.
the full multiplicity-preserving sumset is a consecutive interval. -/
theorem actual_selectedSegment_variance_equality_forces_consecutive {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) (F : Finset T.Edge)
    (q : SelectedComponentPair T F)
    (heq :
      12 * ((SelectedRightSize T F q : ℤ) ^ 2 *
          selectedLeftDelta T F q +
        (SelectedLeftSize T F q : ℤ) ^ 2 *
          selectedRightDelta T F q) =
      let m := SelectedLeftSize T F q * SelectedRightSize T F q
      (m : ℤ) ^ 2 * ((m : ℤ) ^ 2 - 1)) :
    ∀ k : Fin
        (SelectedLeftSize T F q * SelectedRightSize T F q - 1),
      selectedOffsetRank T F q
          (selectedOffsetOrder T F q ⟨k.1 + 1, by omega⟩) =
        selectedOffsetRank T F q
          (selectedOffsetOrder T F q ⟨k.1, by omega⟩) + 1 := by
  let m := SelectedLeftSize T F q * SelectedRightSize T F q
  let sorted : Fin m → ℕ := fun i =>
    selectedOffsetRank T F q (selectedOffsetOrder T F q i)
  have hstrict : StrictMono sorted := by
    intro i j hij
    apply sortedFiniteEquiv_strictMono
      (selectedOffsetRank T F q) (selectedOffsetRank_injective hL F q)
    simpa [selectedOffsetOrder, finCongr, m] using hij
  have hdelta : indexedDelta (fun i : Fin m => (sorted i : ℤ)) =
      indexedDelta (fun z : SelectedBlockIndex T F q =>
        (selectedOffsetRank T F q z : ℤ)) := by
    have hsum : (∑ i : Fin m, (sorted i : ℤ)) =
        ∑ z : SelectedBlockIndex T F q,
          (selectedOffsetRank T F q z : ℤ) := by
      apply Fintype.sum_equiv (selectedOffsetOrder T F q)
      intro i
      rfl
    have hsq : (∑ i : Fin m, (sorted i : ℤ) ^ 2) =
        ∑ z : SelectedBlockIndex T F q,
          (selectedOffsetRank T F q z : ℤ) ^ 2 := by
      apply Fintype.sum_equiv (selectedOffsetOrder T F q)
      intro i
      rfl
    unfold indexedDelta
    rw [hsum, hsq]
    simp [m]
  have heq' : 12 * indexedDelta (fun i : Fin m => (sorted i : ℤ)) =
      (m : ℤ) ^ 2 * ((m : ℤ) ^ 2 - 1) := by
    rw [hdelta, actual_selectedSegment_variance_identity]
    simpa [m] using heq
  simpa [m, sorted] using
    indexedDelta_equality_forces_consecutive sorted hstrict heq'

/-! ## Constructing the actual extreme block of a contiguous segment -/

/-- The physical edges of the canonical path of an actual named pair. -/
def actualPathSegmentEdges {n : ℕ} (T : PosIntTree n)
    (p : VertexPair n) : Finset T.Edge :=
  Finset.univ.filter fun e => e.1 ∈ T.pathEdges p.left p.right

@[simp] theorem mem_actualPathSegmentEdges {n : ℕ}
    (T : PosIntTree n) (p : VertexPair n) (e : T.Edge) :
    e ∈ actualPathSegmentEdges T p ↔
      e.1 ∈ T.pathEdges p.left p.right := by
  simp [actualPathSegmentEdges]

theorem actualPathSegmentEdges_nonempty {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) (p : VertexPair n) :
    (actualPathSegmentEdges T p).Nonempty := by
  have hdist : 0 < T.dist p.left p.right := by
    simpa [PosIntTree.pairDist] using hL.pairDist_pos p
  obtain ⟨edgeValue, hedgeValue⟩ :=
    T.pathEdges_nonempty_of_dist_pos hdist
  let e : T.Edge := T.edgeOfPathMem edgeValue hedgeValue
  exact ⟨e, by simp [actualPathSegmentEdges, e, hedgeValue]⟩

theorem actualPathSegmentEdges_supports_pair {n : ℕ}
    (T : PosIntTree n) (p : VertexPair n) :
    p ∈ pathSupport T (actualPathSegmentEdges T p) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro e he
  exact (mem_actualPathSegmentEdges T p e).mp he

def actualPathSegmentWeight {n : ℕ} (T : PosIntTree n)
    (p : VertexPair n) : ℕ :=
  ∑ e ∈ actualPathSegmentEdges T p, T.weight e

/-- The displayed segment weight is the original metric length of its actual
canonical endpoint path. -/
theorem actualPathSegmentWeight_eq_pairDist {n : ℕ}
    (T : PosIntTree n) (p : VertexPair n) :
    actualPathSegmentWeight T p = T.pairDist p := by
  classical
  have himage :
      (actualPathSegmentEdges T p).image Subtype.val =
        T.pathEdges p.left p.right := by
    apply Finset.ext
    intro edgeValue
    constructor
    · intro hmem
      obtain ⟨e, he, heval⟩ := Finset.mem_image.mp hmem
      rw [← heval]
      exact (mem_actualPathSegmentEdges T p e).mp he
    · intro hedge
      let e : T.Edge := T.edgeOfPathMem edgeValue hedge
      exact Finset.mem_image.mpr
        ⟨e, (mem_actualPathSegmentEdges T p e).mpr (by simpa [e]), rfl⟩
  calc
    actualPathSegmentWeight T p =
        ∑ edgeValue ∈ (actualPathSegmentEdges T p).image Subtype.val,
          T.weightOfPair edgeValue := by
      unfold actualPathSegmentWeight
      rw [Finset.sum_image]
      · simp [T.weightOfPair_edge]
      · intro e he f hf hef
        exact Subtype.ext hef
    _ = ∑ edgeValue ∈ T.pathEdges p.left p.right,
          T.weightOfPair edgeValue := by rw [himage]
    _ = T.pairDist p := rfl

/-- For the selected family consisting of every physical edge of one actual
contiguous path, the component-route shift is exactly the total weight of
that path.  The proof characterizes both quantities as the least distance in
the common graph-derived block; no port or rectangle equation is assumed. -/
theorem selectedRouteLength_actualPathSegment_eq_weight {n : ℕ}
    (T : PosIntTree n) (p : VertexPair n)
    (q : SelectedComponentPair T (actualPathSegmentEdges T p))
    (hblock :
      selectedPathDistanceSet T (actualPathSegmentEdges T p) =
        selectedBlock T (actualPathSegmentEdges T p) q) :
    selectedRouteLength T (actualPathSegmentEdges T p) q =
      actualPathSegmentWeight T p := by
  classical
  have hrouteBlock :
      selectedRouteLength T (actualPathSegmentEdges T p) q ∈
        selectedBlock T (actualPathSegmentEdges T p) q := by
    unfold selectedBlock
    apply Finset.mem_image.mpr
    refine ⟨(selectedSourcePort T (actualPathSegmentEdges T p) q,
      selectedTargetPort T (actualPathSegmentEdges T p) q),
      Finset.mem_univ _, ?_⟩
    simp [selectedCrossRank, selectedLeftDepth, selectedRightDepth]
  have hrouteDistance :
      selectedRouteLength T (actualPathSegmentEdges T p) q ∈
        selectedPathDistanceSet T (actualPathSegmentEdges T p) := by
    rw [hblock]
    exact hrouteBlock
  unfold selectedPathDistanceSet at hrouteDistance
  obtain ⟨r, hrSupport, hrDistance⟩ :=
    Finset.mem_image.mp hrouteDistance
  have hrAll : ∀ e ∈ actualPathSegmentEdges T p,
      e.1 ∈ T.pathEdges r.left r.right := by
    simpa [pathSupport] using hrSupport
  have hpathSubset :
      T.pathEdges p.left p.right ⊆ T.pathEdges r.left r.right := by
    intro edgeValue hedgeValue
    let e : T.Edge := T.edgeOfPathMem edgeValue hedgeValue
    have heSegment : e ∈ actualPathSegmentEdges T p :=
      (mem_actualPathSegmentEdges T p e).mpr (by simpa [e])
    simpa [e] using hrAll e heSegment
  have hp_le_route : T.pairDist p ≤
      selectedRouteLength T (actualPathSegmentEdges T p) q := by
    calc
      T.pairDist p ≤ T.pairDist r := by
        unfold PosIntTree.pairDist PosIntTree.dist
        exact Finset.sum_le_sum_of_subset_of_nonneg hpathSubset
          (fun _ _ _ => Nat.zero_le _)
      _ = selectedRouteLength T (actualPathSegmentEdges T p) q :=
        hrDistance
  have hpBlock : T.pairDist p ∈
      selectedBlock T (actualPathSegmentEdges T p) q := by
    rw [← hblock]
    unfold selectedPathDistanceSet
    exact Finset.mem_image.mpr
      ⟨p, actualPathSegmentEdges_supports_pair T p, rfl⟩
  unfold selectedBlock at hpBlock
  obtain ⟨z, -, hz⟩ := Finset.mem_image.mp hpBlock
  have hroute_le_p :
      selectedRouteLength T (actualPathSegmentEdges T p) q ≤
        T.pairDist p := by
    calc
      selectedRouteLength T (actualPathSegmentEdges T p) q ≤
          selectedCrossRank T (actualPathSegmentEdges T p) q z := by
        simp only [selectedCrossRank]
        omega
      _ = T.pairDist p := hz
  rw [actualPathSegmentWeight_eq_pairDist]
  exact Nat.le_antisymm hroute_le_p hp_le_route

private theorem selected_root_component_iff_extreme {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge) (r : Fin n)
    (near : T.Edge) (hnear : near ∈ F)
    (toNear : ∀ f ∈ F, ∀ x,
      OrientedCut.Away T r f x → OrientedCut.Away T r near x)
    (u : Fin n) :
    componentOf (selectedMarker T F) u =
        componentOf (selectedMarker T F) r ↔
      u ∈ rootOuterSet T r near := by
  classical
  constructor
  · intro hcomp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro huAway
    have hnone :=
      (selected_componentOf_eq_iff_no_selected_path T F u r).mp hcomp
    apply hnone near hnear
    rw [T.pathEdges_comm]
    exact (OrientedCut.away_iff_mem_pathEdges T r near u).mp huAway
  · intro hu
    have huNear := (Finset.mem_filter.mp hu).2
    apply (selected_componentOf_eq_iff_no_selected_path T F u r).mpr
    intro f hf hpath
    have hfAway : OrientedCut.Away T r f u :=
      (OrientedCut.away_iff_mem_pathEdges T r f u).mpr <| by
        simpa [T.pathEdges_comm] using hpath
    exact huNear (toNear f hf u hfAway)

private theorem selected_away_component_iff_extreme {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    (q₀ : VertexPair n) (hq₀ : q₀ ∈ pathSupport T F)
    (far : T.Edge) (hfar : far ∈ F)
    (fromFar : ∀ f ∈ F, ∀ x,
      OrientedCut.Away T q₀.left far x →
        OrientedCut.Away T q₀.left f x)
    (v : Fin n) :
    componentOf (selectedMarker T F) v =
        componentOf (selectedMarker T F) q₀.right ↔
      v ∈ awayOuterSet T q₀.left far := by
  classical
  have hqAway : OrientedCut.Away T q₀.left far q₀.right :=
    (OrientedCut.away_iff_mem_pathEdges T q₀.left far q₀.right).mpr
      ((Finset.mem_filter.mp hq₀).2 far hfar)
  constructor
  · intro hcomp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra hvAway
    have hnone :=
      (selected_componentOf_eq_iff_no_selected_path T F v q₀.right).mp
        hcomp
    apply hnone far hfar
    exact (OrientedCut.mem_pathEdges_iff_opposite_away
      T q₀.left far v q₀.right).mpr (Or.inr ⟨hvAway, hqAway⟩)
  · intro hv
    have hvAway := (Finset.mem_filter.mp hv).2
    apply (selected_componentOf_eq_iff_no_selected_path
      T F v q₀.right).mpr
    intro f hf hpath
    have hvf : OrientedCut.Away T q₀.left f v :=
      fromFar f hf v hvAway
    have hqf : OrientedCut.Away T q₀.left f q₀.right :=
      (OrientedCut.away_iff_mem_pathEdges T q₀.left f q₀.right).mpr
        ((Finset.mem_filter.mp hq₀).2 f hf)
    have hop := (OrientedCut.mem_pathEdges_iff_opposite_away
      T q₀.left f v q₀.right).mp hpath
    rcases hop with h | h <;> tauto

private theorem selected_extreme_components_ne {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    (q₀ : VertexPair n) (hq₀ : q₀ ∈ pathSupport T F)
    (near : T.Edge) (hnear : near ∈ F) :
    componentOf (selectedMarker T F) q₀.left ≠
      componentOf (selectedMarker T F) q₀.right := by
  intro heq
  have hnone := (selected_componentOf_eq_iff_no_selected_path
    T F q₀.left q₀.right).mp heq
  exact hnone near hnear ((Finset.mem_filter.mp hq₀).2 near hnear)

/-- The two actual extreme deletion components, oriented only by their
canonical representatives as required by `SelectedComponentPair`. -/
noncomputable def extremeSelectedComponentPair {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge) (u v : Fin n)
    (hne : componentOf (selectedMarker T F) u ≠
      componentOf (selectedMarker T F) v) :
    SelectedComponentPair T F := by
  let M := selectedMarker T F
  let C := componentOf M u
  let D := componentOf M v
  by_cases hCD : componentRep M C < componentRep M D
  · exact ⟨(C, D), hCD⟩
  · have hrepNe : componentRep M D ≠ componentRep M C := by
      intro hrep
      apply hne
      exact componentRep_injective M hrep.symm
    exact ⟨(D, C), lt_of_le_of_ne (le_of_not_gt hCD) hrepNe⟩

private theorem extremeSelectedComponentPair_vertex_components {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge) (u v : Fin n)
    (hne : componentOf (selectedMarker T F) u ≠
      componentOf (selectedMarker T F) v)
    (z : SelectedBlockIndex T F
      (extremeSelectedComponentPair T F u v hne)) :
    (componentOf (selectedMarker T F) z.1.1 =
        componentOf (selectedMarker T F) u ∧
      componentOf (selectedMarker T F) z.2.1 =
        componentOf (selectedMarker T F) v) ∨
    (componentOf (selectedMarker T F) z.1.1 =
        componentOf (selectedMarker T F) v ∧
      componentOf (selectedMarker T F) z.2.1 =
        componentOf (selectedMarker T F) u) := by
  by_cases hCD : componentRep (selectedMarker T F)
      (componentOf (selectedMarker T F) u) <
        componentRep (selectedMarker T F)
          (componentOf (selectedMarker T F) v)
  · left
    simpa [extremeSelectedComponentPair, hCD] using
      (And.intro z.1.2 z.2.2)
  · right
    simpa [extremeSelectedComponentPair, hCD] using
      (And.intro z.1.2 z.2.2)

private theorem exists_support_pair_of_extreme_components {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    (q₀ : VertexPair n) (hq₀ : q₀ ∈ pathSupport T F)
    (near far : T.Edge) (hnear : near ∈ F) (hfar : far ∈ F)
    (toNear : ∀ f ∈ F, ∀ x,
      OrientedCut.Away T q₀.left f x →
        OrientedCut.Away T q₀.left near x)
    (fromFar : ∀ f ∈ F, ∀ x,
      OrientedCut.Away T q₀.left far x →
        OrientedCut.Away T q₀.left f x)
    (u v : Fin n)
    (hcomponents :
      (componentOf (selectedMarker T F) u =
          componentOf (selectedMarker T F) q₀.left ∧
        componentOf (selectedMarker T F) v =
          componentOf (selectedMarker T F) q₀.right) ∨
      (componentOf (selectedMarker T F) u =
          componentOf (selectedMarker T F) q₀.right ∧
        componentOf (selectedMarker T F) v =
          componentOf (selectedMarker T F) q₀.left)) :
    ∃ p : VertexPair n,
      p ∈ pathSupport T F ∧ T.pairDist p = T.dist u v := by
  classical
  have hCne := selected_extreme_components_ne T F q₀ hq₀ near hnear
  have huv : u ≠ v := by
    intro huv
    subst v
    rcases hcomponents with h | h
    · exact hCne (h.1.symm.trans h.2)
    · exact hCne (h.2.symm.trans h.1)
  let p := VertexPair.ofDistinct u v huv
  refine ⟨p, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro f hf
    rw [pathEdges_ofDistinct]
    rcases hcomponents with h | h
    · have huRoot := (selected_root_component_iff_extreme
        T F q₀.left near hnear toNear u).mp h.1
      have hvAway := (selected_away_component_iff_extreme
        T F q₀ hq₀ far hfar fromFar v).mp h.2
      have huf : ¬OrientedCut.Away T q₀.left f u := by
        intro hu
        exact (Finset.mem_filter.mp huRoot).2 (toNear f hf u hu)
      have hvf : OrientedCut.Away T q₀.left f v :=
        fromFar f hf v (Finset.mem_filter.mp hvAway).2
      exact (OrientedCut.mem_pathEdges_iff_opposite_away
        T q₀.left f u v).mpr (Or.inr ⟨huf, hvf⟩)
    · have huAway := (selected_away_component_iff_extreme
        T F q₀ hq₀ far hfar fromFar u).mp h.1
      have hvRoot := (selected_root_component_iff_extreme
        T F q₀.left near hnear toNear v).mp h.2
      have huf : OrientedCut.Away T q₀.left f u :=
        fromFar f hf u (Finset.mem_filter.mp huAway).2
      have hvf : ¬OrientedCut.Away T q₀.left f v := by
        intro hv
        exact (Finset.mem_filter.mp hvRoot).2 (toNear f hf v hv)
      exact (OrientedCut.mem_pathEdges_iff_opposite_away
        T q₀.left f u v).mpr (Or.inl ⟨huf, hvf⟩)
  · exact T.pairDist_pairOfDistinct u v huv

private theorem extreme_selectedBlock_subset_pathDistance {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    (q₀ : VertexPair n) (hq₀ : q₀ ∈ pathSupport T F)
    (near far : T.Edge) (hnear : near ∈ F) (hfar : far ∈ F)
    (toNear : ∀ f ∈ F, ∀ x,
      OrientedCut.Away T q₀.left f x →
        OrientedCut.Away T q₀.left near x)
    (fromFar : ∀ f ∈ F, ∀ x,
      OrientedCut.Away T q₀.left far x →
        OrientedCut.Away T q₀.left f x) :
    let hne := selected_extreme_components_ne T F q₀ hq₀ near hnear
    selectedBlock T F
        (extremeSelectedComponentPair T F q₀.left q₀.right hne) ⊆
      selectedPathDistanceSet T F := by
  dsimp only
  intro d hd
  obtain ⟨z, -, hzd⟩ := Finset.mem_image.mp hd
  have hcomponents := extremeSelectedComponentPair_vertex_components
    T F q₀.left q₀.right
      (selected_extreme_components_ne T F q₀ hq₀ near hnear) z
  obtain ⟨p, hp, hpdist⟩ := exists_support_pair_of_extreme_components
    T F q₀ hq₀ near far hnear hfar toNear fromFar
      z.1.1 z.2.1 hcomponents
  apply Finset.mem_image.mpr
  refine ⟨p, hp, ?_⟩
  calc
    T.pairDist p = T.dist z.1.1 z.2.1 := hpdist
    _ = selectedCrossRank T F
        (extremeSelectedComponentPair T F q₀.left q₀.right
          (selected_extreme_components_ne T F q₀ hq₀ near hnear)) z := by
      simpa [selectedCrossRank, selectedLeftDepth, selectedRightDepth] using
        selected_cross_distance_decomposition T F
          (extremeSelectedComponentPair T F q₀.left q₀.right
            (selected_extreme_components_ne T F q₀ hq₀ near hnear))
          z.1 z.2
    _ = d := hzd

private theorem extreme_selectedBlockDemand {n : ℕ}
    (T : PosIntTree n) (F : Finset T.Edge)
    (q₀ : VertexPair n) (hq₀ : q₀ ∈ pathSupport T F)
    (near far : T.Edge) (hnear : near ∈ F) (hfar : far ∈ F)
    (toNear : ∀ f ∈ F, ∀ x,
      OrientedCut.Away T q₀.left f x →
        OrientedCut.Away T q₀.left near x)
    (fromFar : ∀ f ∈ F, ∀ x,
      OrientedCut.Away T q₀.left far x →
        OrientedCut.Away T q₀.left f x) :
    let hne := selected_extreme_components_ne T F q₀ hq₀ near hnear
    selectedBlockDemand T F
        (extremeSelectedComponentPair T F q₀.left q₀.right hne) =
      (rootOuterSet T q₀.left near).card *
        (awayOuterSet T q₀.left far).card := by
  dsimp only
  let M := selectedMarker T F
  let C := componentOf M q₀.left
  let D := componentOf M q₀.right
  let ER : SelectedComponentVertex T F C ≃
      {u : Fin n // u ∈ rootOuterSet T q₀.left near} :=
    Equiv.subtypeEquivProp <| funext fun u => propext <| by
      exact selected_root_component_iff_extreme
        T F q₀.left near hnear toNear u
  let EA : SelectedComponentVertex T F D ≃
      {v : Fin n // v ∈ awayOuterSet T q₀.left far} :=
    Equiv.subtypeEquivProp <| funext fun v => propext <| by
      exact selected_away_component_iff_extreme
        T F q₀ hq₀ far hfar fromFar v
  have hroot : Fintype.card (SelectedComponentVertex T F C) =
      (rootOuterSet T q₀.left near).card := by
    simpa using Fintype.card_congr ER
  have haway : Fintype.card (SelectedComponentVertex T F D) =
      (awayOuterSet T q₀.left far).card := by
    simpa using Fintype.card_congr EA
  unfold selectedBlockDemand extremeSelectedComponentPair
  dsimp only
  split
  · change Fintype.card (SelectedComponentVertex T F C) *
        Fintype.card (SelectedComponentVertex T F D) = _
    rw [hroot, haway]
  · change Fintype.card (SelectedComponentVertex T F D) *
        Fintype.card (SelectedComponentVertex T F C) = _
    rw [haway, hroot, Nat.mul_comm]

/-- A collinear selected family is exactly the one graph-derived extreme
component block, not merely a block with an assumed rectangle equation. -/
theorem exists_extreme_selectedBlock_eq_pathDistance {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T)
    (F : Finset T.Edge) (hF : F.Nonempty)
    (hcol : (pathSupport T F).Nonempty) :
    ∃ (q₀ : VertexPair n) (near far : T.Edge)
      (q : SelectedComponentPair T F),
      q₀ ∈ pathSupport T F ∧ near ∈ F ∧ far ∈ F ∧
      (∀ f ∈ F, ∀ x,
        OrientedCut.Away T q₀.left f x →
          OrientedCut.Away T q₀.left near x) ∧
      (∀ f ∈ F, ∀ x,
        OrientedCut.Away T q₀.left far x →
          OrientedCut.Away T q₀.left f x) ∧
      selectedPathDistanceSet T F = selectedBlock T F q := by
  obtain ⟨q₀, hq₀⟩ := hcol
  obtain ⟨near, far, hnear, hfar, toNear, fromFar⟩ :=
    exists_extreme_edges T F hF q₀ hq₀
  let hne := selected_extreme_components_ne T F q₀ hq₀ near hnear
  let q := extremeSelectedComponentPair T F q₀.left q₀.right hne
  have hsub : selectedBlock T F q ⊆ selectedPathDistanceSet T F :=
    extreme_selectedBlock_subset_pathDistance T F q₀ hq₀ near far
      hnear hfar toNear fromFar
  let E := supportOuterFinsetEquiv T q₀.left F near far
    hnear hfar toNear fromFar
  have hsupportCard : (pathSupport T F).card =
      (rootOuterSet T q₀.left near).card *
        (awayOuterSet T q₀.left far).card := by
    simpa [Fintype.card_prod] using Fintype.card_congr E
  have hdistanceCard : (selectedPathDistanceSet T F).card =
      (pathSupport T F).card := by
    unfold selectedPathDistanceSet
    exact Finset.card_image_of_injective _ hL.pairDist_injective
  have hblockCard : (selectedBlock T F q).card =
      (rootOuterSet T q₀.left near).card *
        (awayOuterSet T q₀.left far).card := by
    rw [selectedBlock_card hL F q]
    exact extreme_selectedBlockDemand T F q₀ hq₀ near far
      hnear hfar toNear fromFar
  have heq : selectedBlock T F q = selectedPathDistanceSet T F := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hdistanceCard, hsupportCard, hblockCard]
  exact ⟨q₀, near, far, q, hq₀, hnear, hfar,
    toNear, fromFar, heq.symm⟩

/-- The multiplicity-free actual offset sumset. -/
def selectedOffsetSet {n : ℕ} (T : PosIntTree n)
    (F : Finset T.Edge) (q : SelectedComponentPair T F) : Finset ℤ :=
  Finset.univ.image fun z : SelectedBlockIndex T F q =>
    (selectedOffsetRank T F q z : ℤ)

/-- The report's set-level `Delta(X+Y)`. -/
def selectedOffsetSetDelta {n : ℕ} (T : PosIntTree n)
    (F : Finset T.Edge) (q : SelectedComponentPair T F) : ℤ :=
  ((selectedOffsetSet T F q).card : ℤ) *
      (∑ s ∈ selectedOffsetSet T F q, s ^ 2) -
    (∑ s ∈ selectedOffsetSet T F q, s) ^ 2

/-- Exact set-level direct-sum variance identity for the actual extreme
block.  Injectivity supplied by `IsLeech` is what permits passage from the
indexed Cartesian family to the finite sumset. -/
theorem actual_selectedSegment_finset_variance_identity {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) :
    selectedOffsetSetDelta T F q =
      (SelectedRightSize T F q : ℤ) ^ 2 * selectedLeftDelta T F q +
        (SelectedLeftSize T F q : ℤ) ^ 2 * selectedRightDelta T F q := by
  classical
  let x := fun u : SelectedComponentVertex T F q.left =>
    (selectedLeftDepth T F q u : ℤ)
  let y := fun v : SelectedComponentVertex T F q.right =>
    (selectedRightDepth T F q v : ℤ)
  have hinj : Function.Injective
      (fun z : SelectedBlockIndex T F q => x z.1 + y z.2) := by
    intro z z' hzz
    apply selectedOffsetRank_injective hL F q
    dsimp only [x, y] at hzz
    have hnat :
        selectedLeftDepth T F q z.1 + selectedRightDepth T F q z.2 =
          selectedLeftDepth T F q z'.1 +
            selectedRightDepth T F q z'.2 := by
      exact_mod_cast hzz
    simpa [selectedOffsetRank] using hnat
  have hset : selectedOffsetSet T F q =
      (Finset.univ : Finset (SelectedBlockIndex T F q)).image
        (fun z => x z.1 + y z.2) := by
    unfold selectedOffsetSet selectedOffsetRank
    apply Finset.image_congr
    intro z hz
    simp only [x, y, Nat.cast_add]
  have h := finsetDelta_image_add_product x y hinj
  unfold selectedOffsetSetDelta
  rw [hset]
  simpa only [selectedLeftDelta, selectedRightDelta, x, y] using h

/-- Division-free lower bound stated directly for the actual finite offset
sumset, rather than only for its Cartesian indexing. -/
theorem actual_selectedSegment_finset_variance_lower {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) (F : Finset T.Edge)
    (q : SelectedComponentPair T F) :
    let m := SelectedLeftSize T F q * SelectedRightSize T F q
    (m : ℤ) ^ 2 * ((m : ℤ) ^ 2 - 1) ≤
      12 * selectedOffsetSetDelta T F q := by
  rw [actual_selectedSegment_finset_variance_identity hL F q]
  exact actual_selectedSegment_variance_lower hL F q

/-- Fully graph-level G004 endpoint.  The extreme component pair is
constructed from the segment, its block is identified with the actual
`pathSupport` distance image, and every downstream order-statistic and
variance conclusion is exported without an assumed rectangle. -/
structure ActualPathSegmentConclusion {n : ℕ}
    (T : PosIntTree n) (hL : IsLeech T) (F : Finset T.Edge) where
  witness : VertexPair n
  near : T.Edge
  far : T.Edge
  componentPair : SelectedComponentPair T F
  witness_mem : witness ∈ pathSupport T F
  near_mem : near ∈ F
  far_mem : far ∈ F
  block_eq : selectedPathDistanceSet T F =
    selectedBlock T F componentPair
  shiftedSumset_eq : selectedPathDistanceSet T F =
    Finset.univ.image fun z : SelectedBlockIndex T F componentPair =>
      selectedRouteLength T F componentPair +
        selectedLeftDepth T F componentPair z.1 +
        selectedRightDepth T F componentPair z.2
  actualSegmentRouteWeight : ∀ (p : VertexPair n)
      (_ : F = actualPathSegmentEdges T p),
    selectedRouteLength T F componentPair = actualPathSegmentWeight T p
  actualSegmentShiftedSumset : ∀ (p : VertexPair n)
      (_ : F = actualPathSegmentEdges T p),
    selectedPathDistanceSet T F =
      Finset.univ.image fun z : SelectedBlockIndex T F componentPair =>
        actualPathSegmentWeight T p +
          selectedLeftDepth T F componentPair z.1 +
          selectedRightDepth T F componentPair z.2
  shiftedRectangle : ∀
      (x : SelectedComponentVertex T F componentPair.left)
      (y : SelectedComponentVertex T F componentPair.right),
    T.dist x.1 y.1 = selectedRouteLength T F componentPair +
      selectedLeftDepth T F componentPair x +
      selectedRightDepth T F componentPair y
  singletonPuncture : ∀ e : T.Edge, F = {e} →
    selectedPathDistanceSet T F ∩ physicalWeightSet T = {T.weight e}
  multiEdgePuncture : 2 ≤ F.card →
    selectedPathDistanceSet T F ∩ physicalWeightSet T = ∅
  orderStatistics : ∀
      (i : Fin (SelectedLeftSize T F componentPair))
      (j : Fin (SelectedRightSize T F componentPair)),
    let B := actualOrderedPuncturedBlock hL F componentPair
    B.eligibleOffset
        ⟨(i.1 + 1) * (j.1 + 1) - 1, by
          have hi : i.1 + 1 ≤ SelectedLeftSize T F componentPair :=
            Nat.succ_le_iff.mpr i.2
          have hj : j.1 + 1 ≤ SelectedRightSize T F componentPair :=
            Nat.succ_le_iff.mpr j.2
          have hf := actualOrderedPuncturedBlock_fit hL F componentPair
          have hprod := (Nat.mul_le_mul hi hj).trans hf
          have hpos := Nat.mul_pos (Nat.succ_pos i.1) (Nat.succ_pos j.1)
          exact (Nat.sub_lt hpos (by decide)).trans_le hprod⟩ ≤
      B.leftDepth i + B.rightDepth j ∧
    B.leftDepth i + B.rightDepth j ≤
      B.eligibleOffset
        ⟨SelectedEligibleSize T F componentPair -
            ((SelectedLeftSize T F componentPair - i.1) *
              (SelectedRightSize T F componentPair - j.1)), by
          have hi : 0 < SelectedLeftSize T F componentPair - i.1 :=
            Nat.sub_pos_of_lt i.2
          have hj : 0 < SelectedRightSize T F componentPair - j.1 :=
            Nat.sub_pos_of_lt j.2
          have hle := actualOrderedPuncturedBlock_fit hL F componentPair
          have hprod :
              (SelectedLeftSize T F componentPair - i.1) *
                  (SelectedRightSize T F componentPair - j.1) ≤
                SelectedLeftSize T F componentPair *
                  SelectedRightSize T F componentPair :=
            Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
          have hpos := Nat.mul_pos hi hj
          omega⟩
  varianceLower :
    let m := SelectedLeftSize T F componentPair *
      SelectedRightSize T F componentPair
    (m : ℤ) ^ 2 * ((m : ℤ) ^ 2 - 1) ≤
      12 * ((SelectedRightSize T F componentPair : ℤ) ^ 2 *
          selectedLeftDelta T F componentPair +
        (SelectedLeftSize T F componentPair : ℤ) ^ 2 *
          selectedRightDelta T F componentPair)
  finsetVarianceIdentity :
    selectedOffsetSetDelta T F componentPair =
      (SelectedRightSize T F componentPair : ℤ) ^ 2 *
          selectedLeftDelta T F componentPair +
        (SelectedLeftSize T F componentPair : ℤ) ^ 2 *
          selectedRightDelta T F componentPair
  finsetVarianceLower :
    let m := SelectedLeftSize T F componentPair *
      SelectedRightSize T F componentPair
    (m : ℤ) ^ 2 * ((m : ℤ) ^ 2 - 1) ≤
      12 * selectedOffsetSetDelta T F componentPair
  equalityForcesConsecutive :
    ∀ _heq :
      12 * ((SelectedRightSize T F componentPair : ℤ) ^ 2 *
          selectedLeftDelta T F componentPair +
        (SelectedLeftSize T F componentPair : ℤ) ^ 2 *
          selectedRightDelta T F componentPair) =
      let m := SelectedLeftSize T F componentPair *
        SelectedRightSize T F componentPair
      (m : ℤ) ^ 2 * ((m : ℤ) ^ 2 - 1),
    ∀ k : Fin
        (SelectedLeftSize T F componentPair *
          SelectedRightSize T F componentPair - 1),
      selectedOffsetRank T F componentPair
          (selectedOffsetOrder T F componentPair ⟨k.1 + 1, by omega⟩) =
        selectedOffsetRank T F componentPair
          (selectedOffsetOrder T F componentPair ⟨k.1, by omega⟩) + 1

noncomputable def actualCollinearPathSegmentConclusion {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T)
    (F : Finset T.Edge) (hF : F.Nonempty)
    (hcol : (pathSupport T F).Nonempty) :
    ActualPathSegmentConclusion T hL F := Classical.choice <| by
  obtain ⟨q₀, near, far, q, hq₀, hnear, hfar,
      toNear, fromFar, hblock⟩ :=
    exists_extreme_selectedBlock_eq_pathDistance hL F hF hcol
  refine ⟨{
    witness := q₀
    near := near
    far := far
    componentPair := q
    witness_mem := hq₀
    near_mem := hnear
    far_mem := hfar
    block_eq := hblock
    shiftedSumset_eq := by
      rw [hblock]
      rfl
    actualSegmentRouteWeight := by
      intro p hp
      subst F
      exact selectedRouteLength_actualPathSegment_eq_weight T p q hblock
    actualSegmentShiftedSumset := by
      intro p hp
      subst F
      have hroute :=
        selectedRouteLength_actualPathSegment_eq_weight T p q hblock
      rw [hblock]
      unfold selectedBlock
      apply Finset.image_congr
      intro z hz
      simp only [selectedCrossRank]
      rw [hroute]
    shiftedRectangle := selected_cross_distance_decomposition T F q
    singletonPuncture := by
      intro e he
      rw [he]
      exact singleton_selectedPathDistance_inter_physical hL e
    multiEdgePuncture :=
      selectedPathDistance_inter_physical_eq_empty_of_two_le hL
    orderStatistics := actual_selectedSegment_rectangle_order_statistics
      hL F q
    varianceLower := actual_selectedSegment_variance_lower hL F q
    finsetVarianceIdentity :=
      actual_selectedSegment_finset_variance_identity hL F q
    finsetVarianceLower :=
      actual_selectedSegment_finset_variance_lower hL F q
    equalityForcesConsecutive :=
      actual_selectedSegment_variance_equality_forces_consecutive hL F q }⟩

/-- Every actual nonempty contiguous path segment obtains the full G004
conclusion with no selected family, extreme components, or ordering supplied
by the caller. -/
noncomputable def actualContiguousPathSegmentConclusion {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) (p : VertexPair n) :
    ActualPathSegmentConclusion T hL (actualPathSegmentEdges T p) :=
  actualCollinearPathSegmentConclusion hL (actualPathSegmentEdges T p)
    (actualPathSegmentEdges_nonempty hL p)
    ⟨p, actualPathSegmentEdges_supports_pair T p⟩

/-- The literal graph-level path-segment shift: `L` is the sum of the actual
physical edge weights on the named contiguous segment. -/
theorem actualContiguousPathSegment_routeLength_eq_weight {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) (p : VertexPair n) :
    selectedRouteLength T (actualPathSegmentEdges T p)
        (actualContiguousPathSegmentConclusion hL p).componentPair =
      actualPathSegmentWeight T p :=
  (actualContiguousPathSegmentConclusion hL p).actualSegmentRouteWeight p rfl

/-- The preprint's exact `L + (X+Y)` identity for an actual contiguous
physical path, with `L = ∑ e ∈ actualPathSegmentEdges T p, T.weight e`. -/
theorem actualContiguousPathSegment_shiftedSumset {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) (p : VertexPair n) :
    selectedPathDistanceSet T (actualPathSegmentEdges T p) =
      Finset.univ.image fun z : SelectedBlockIndex T
          (actualPathSegmentEdges T p)
          (actualContiguousPathSegmentConclusion hL p).componentPair =>
        actualPathSegmentWeight T p +
          selectedLeftDepth T (actualPathSegmentEdges T p)
            (actualContiguousPathSegmentConclusion hL p).componentPair z.1 +
          selectedRightDepth T (actualPathSegmentEdges T p)
            (actualContiguousPathSegmentConclusion hL p).componentPair z.2 :=
  (actualContiguousPathSegmentConclusion hL p).actualSegmentShiftedSumset p rfl

end

end LeechTrees.PathMulticut
