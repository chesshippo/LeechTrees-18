import LeechTrees.OddQuotient.F9Endpoints

/-!
# Second-odd-edge tail and capacity bounds

This module isolates the human proofs in
`runs/260810b/structural/ODD_QUOTIENT_Q2_BOUND.md`.

The graph layer below is not a solver certificate.  Starting from an actual
`IsLeech` tree and an actual least/second-odd-edge datum, it constructs the
missing injection from every even-length cross-component block into the
high even half-rank tail.  The remainder of the file records the sharp
order-18 `G` and `H` optimizations and their arithmetic consequences.

The separately inherited order-18 assertion `Q <= 68` is deliberately not a
hypothesis of any unconditional theorem.  Results that combine it with odd
packing are named `..._of_largestOdd_le_67`.
-/

open scoped BigOperators

namespace LeechTrees.OddQuotient.Q2Bounds

open LeechTrees.Foundation

variable {n : ℕ}

/-! ## Actual second-odd-edge data -/

/-- Data saying that `unit` is the unique possible odd bridge below
`q₂ = 2t+1`, and that it has physical weight one.  In an actual tree this
is obtained by choosing the physical edge of weight one and the second
smallest odd physical edge. -/
structure SecondOddBridgeData (T : PosIntTree n) where
  unit : OddBridge T
  q₂ : ℕ
  t : ℕ
  q₂_eq : q₂ = 2 * t + 1
  t_pos : 0 < t
  unit_weight : T.weight unit.1 = 1
  other_weight_lower : ∀ e : OddBridge T, e ≠ unit → q₂ ≤ T.weight e.1
  q₂_le_target : q₂ ≤ targetN n

namespace SecondOddBridgeData

theorem q₂_pos {T : PosIntTree n} (D : SecondOddBridgeData T) : 0 < D.q₂ := by
  rw [D.q₂_eq]
  omega

theorem other_halfWeight_lower {T : PosIntTree n}
    (D : SecondOddBridgeData T) (e : OddBridge T) (hne : e ≠ D.unit) :
    D.t ≤ bridgeHalfWeight T e := by
  have hweight := D.other_weight_lower e hne
  have hodd := bridge_weight_eq_two_mul_half_add_one T e
  rw [D.q₂_eq] at hweight
  omega

end SecondOddBridgeData

/-! ## Canonical construction from an actual Leech tree -/

/-- An actual second odd physical edge exists.  The formulation by weight,
rather than by inequality with a preselected edge, makes the hypothesis
independent of every classical choice below. -/
def HasNonunitOddBridge (T : PosIntTree n) : Prop :=
  ∃ e : OddBridge T, T.weight e.1 ≠ 1

/-- The unique actual physical edge of weight one, selected only after the
order boundary needed by `t1_existsUnique_weight_one` has been supplied. -/
noncomputable def unitEdgeOfIsLeech
    {T : PosIntTree n} (hL : IsLeech T) (hn : 2 ≤ n) : T.Edge :=
  Classical.choose (t1_existsUnique_weight_one hL hn)

@[simp] theorem unitEdgeOfIsLeech_weight
    {T : PosIntTree n} (hL : IsLeech T) (hn : 2 ≤ n) :
    T.weight (unitEdgeOfIsLeech hL hn) = 1 :=
  (Classical.choose_spec (t1_existsUnique_weight_one hL hn)).1

/-- The selected weight-one edge, now retained as an indexed odd bridge. -/
noncomputable def unitBridgeOfIsLeech
    {T : PosIntTree n} (hL : IsLeech T) (hn : 2 ≤ n) : OddBridge T :=
  ⟨unitEdgeOfIsLeech hL hn, by
    rw [unitEdgeOfIsLeech_weight]
    norm_num⟩

@[simp] theorem unitBridgeOfIsLeech_weight
    {T : PosIntTree n} (hL : IsLeech T) (hn : 2 ≤ n) :
    T.weight (unitBridgeOfIsLeech hL hn).1 = 1 :=
  unitEdgeOfIsLeech_weight hL hn

private theorem nonunitOddWeight_exists
    {T : PosIntTree n} (h₂ : HasNonunitOddBridge T) :
    ∃ q : ℕ, ∃ e : OddBridge T, T.weight e.1 = q ∧ q ≠ 1 := by
  rcases h₂ with ⟨e, he⟩
  exact ⟨T.weight e.1, e, rfl, he⟩

/-- The actual second odd physical weight: the least odd-bridge weight other
than one. -/
noncomputable def secondOddWeight
    {T : PosIntTree n} (h₂ : HasNonunitOddBridge T) : ℕ :=
  Nat.find (nonunitOddWeight_exists h₂)

theorem secondOddWeight_spec
    {T : PosIntTree n} (h₂ : HasNonunitOddBridge T) :
    ∃ e : OddBridge T,
      T.weight e.1 = secondOddWeight h₂ ∧ secondOddWeight h₂ ≠ 1 :=
  Nat.find_spec (nonunitOddWeight_exists h₂)

/-- A physical bridge attaining the canonical second odd weight. -/
noncomputable def secondOddBridge
    {T : PosIntTree n} (h₂ : HasNonunitOddBridge T) : OddBridge T :=
  Classical.choose (secondOddWeight_spec h₂)

@[simp] theorem secondOddBridge_weight
    {T : PosIntTree n} (h₂ : HasNonunitOddBridge T) :
    T.weight (secondOddBridge h₂).1 = secondOddWeight h₂ :=
  (Classical.choose_spec (secondOddWeight_spec h₂)).1

theorem secondOddWeight_ne_one
    {T : PosIntTree n} (h₂ : HasNonunitOddBridge T) :
    secondOddWeight h₂ ≠ 1 :=
  (Classical.choose_spec (secondOddWeight_spec h₂)).2

theorem secondOddWeight_le
    {T : PosIntTree n} (h₂ : HasNonunitOddBridge T)
    (e : OddBridge T) (he : T.weight e.1 ≠ 1) :
    secondOddWeight h₂ ≤ T.weight e.1 := by
  exact Nat.find_min' (nonunitOddWeight_exists h₂) ⟨e, rfl, he⟩

theorem secondOddWeight_odd
    {T : PosIntTree n} (h₂ : HasNonunitOddBridge T) :
    Odd (secondOddWeight h₂) := by
  rw [← secondOddBridge_weight h₂]
  exact (secondOddBridge h₂).2

theorem three_le_secondOddWeight
    {T : PosIntTree n} (h₂ : HasNonunitOddBridge T) :
    3 ≤ secondOddWeight h₂ := by
  have hodd := secondOddWeight_odd h₂
  have hne := secondOddWeight_ne_one h₂
  rcases hodd with ⟨k, hk⟩
  omega

/-- Canonical graph-derived data used by all q₂ injections below.  No
arithmetic lower-bound assumption is imported: minimality is proved by
`Nat.find`, the upper bound comes from the actual physical edge, and the
unit edge comes from the exact Leech spectrum. -/
noncomputable def canonicalSecondOddBridgeData
    {T : PosIntTree n} (hL : IsLeech T) (hn : 2 ≤ n)
    (h₂ : HasNonunitOddBridge T) : SecondOddBridgeData T where
  unit := unitBridgeOfIsLeech hL hn
  q₂ := secondOddWeight h₂
  t := secondOddWeight h₂ / 2
  q₂_eq := by
    have hodd := secondOddWeight_odd h₂
    exact (Nat.two_mul_div_two_add_one_of_odd hodd).symm
  t_pos := by
    have hthree := three_le_secondOddWeight h₂
    omega
  unit_weight := unitBridgeOfIsLeech_weight hL hn
  other_weight_lower := by
    intro e hne
    apply secondOddWeight_le h₂ e
    intro heone
    apply hne
    apply Subtype.ext
    exact t1_edge_weight_injective hL
      (heone.trans (unitBridgeOfIsLeech_weight hL hn).symm)
  q₂_le_target := by
    have hmem := t1_edge_weight_mem_target hL (secondOddBridge h₂).1
    rw [secondOddBridge_weight h₂] at hmem
    exact (Finset.mem_Icc.mp hmem).2

theorem canonicalSecondOddBridgeData_q₂
    {T : PosIntTree n} (hL : IsLeech T) (hn : 2 ≤ n)
    (h₂ : HasNonunitOddBridge T) :
    (canonicalSecondOddBridgeData hL hn h₂).q₂ = secondOddWeight h₂ := rfl

/-! ## The high-tail graph injection -/

/-- Two consecutive edges of a quotient path already contribute at least
`t` in bridge half-weight and one more from `floor(length/2)`.  Distinctness
of the two quotient edges is obtained from the path/trail property; no
quotient shape is assumed. -/
private theorem routeShift_cons_cons_ge
    {T : PosIntTree n} (D : SecondOddBridgeData T)
    {C₀ C₁ C₂ E : EvenComponent T}
    (h₁ : (quotientGraph T).Adj C₀ C₁)
    (h₂ : (quotientGraph T).Adj C₁ C₂)
    (p : (quotientGraph T).Walk C₂ E)
    (hp : (.cons h₁ (.cons h₂ p) :
      (quotientGraph T).Walk C₀ E).IsPath) :
    D.t + 1 ≤ routeShift T h₁ (.cons h₂ p) := by
  let b₁ := orientedBridgeOfAdj T h₁
  let b₂ := orientedBridgeOfAdj T h₂
  have havoid : s(C₀, C₁) ∉
      (.cons h₂ p : (quotientGraph T).Walk C₁ E).edges :=
    ((SimpleGraph.Walk.cons_isTrail_iff h₁ (.cons h₂ p)).mp
      hp.isTrail).2
  have hpairs : s(C₀, C₁) ≠ s(C₁, C₂) := by
    intro heq
    apply havoid
    simp [heq]
  have hbne : b₁.bridge ≠ b₂.bridge := by
    intro heq
    apply hpairs
    calc
      s(C₀, C₁) = quotientEdgePair T b₁.bridge :=
        b₁.component_pair.symm
      _ = quotientEdgePair T b₂.bridge :=
        congrArg (quotientEdgePair T) heq
      _ = s(C₁, C₂) := b₂.component_pair
  have hbridge :
      D.t ≤ bridgeHalfWeight T b₁.bridge ∨
        D.t ≤ bridgeHalfWeight T b₂.bridge := by
    by_cases hunit : b₁.bridge = D.unit
    · right
      apply D.other_halfWeight_lower
      intro hsecond
      exact hbne (hunit.trans hsecond.symm)
    · exact Or.inl (D.other_halfWeight_lower b₁.bridge hunit)
  have hlength : 1 ≤
      (.cons h₁ (.cons h₂ p) :
        (quotientGraph T).Walk C₀ E).length / 2 := by
    simp only [SimpleGraph.Walk.length]
    omega
  rw [routeShift_cons]
  simp only [b₁, b₂] at hbridge
  rcases hbridge with hbridge | hbridge <;> omega

/-- Every even-length route between distinct even components has half-rank
at least `t+1`, hence raw distance at least `q₂+1`. -/
theorem evenQuotientPair_shift_ge
    {T : PosIntTree n} (D : SecondOddBridgeData T)
    (q : EvenQuotientComponentPair T) :
    D.t + 1 ≤ canonicalRouteShift T q.1 := by
  let R := canonicalRouteData T q.1
  have hp : (.cons R.head R.tail :
      (quotientGraph T).Walk q.1.left q.1.right).IsPath := R.isPath
  have hpar : (.cons R.head R.tail :
      (quotientGraph T).Walk q.1.left q.1.right).length % 2 = 0 := by
    simpa [R, quotientPairParity, canonicalRouteWalk] using q.2
  have htail_pos : 0 < R.tail.length := by
    by_contra hzero
    have hzero' : R.tail.length = 0 := Nat.eq_zero_of_not_pos hzero
    simp only [SimpleGraph.Walk.length, hzero'] at hpar
    omega
  have htail_not_nil : ¬ R.tail.Nil :=
    SimpleGraph.Walk.not_nil_iff_lt_length.mpr htail_pos
  rcases SimpleGraph.Walk.not_nil_iff.mp htail_not_nil with
    ⟨C₂, h₂, p, htail⟩
  have hp' : (.cons R.head (.cons h₂ p) :
      (quotientGraph T).Walk q.1.left q.1.right).IsPath := by
    simpa [htail] using hp
  change D.t + 1 ≤ routeShift T R.head R.tail
  rw [htail]
  exact routeShift_cons_cons_ge D R.head h₂ p hp'

/-- Forget the parity proof on the quotient-pair base. -/
def EvenCrossIndex.toCross {T : PosIntTree n}
    (z : EvenCrossIndex T) : CrossIndex T :=
  ⟨z.1.1, z.2⟩

theorem EvenCrossIndex.toCross_injective {T : PosIntTree n} :
    Function.Injective (EvenCrossIndex.toCross (T := T)) := by
  rintro ⟨⟨q, hq⟩, x⟩ ⟨⟨r, hr⟩, y⟩ h
  simp only [EvenCrossIndex.toCross] at h
  cases h
  rfl

/-- Exact high-tail lower bound for every actual same-color,
distinct-component endpoint pair. -/
theorem evenCross_pairDist_ge_q₂_add_one
    {T : PosIntTree n} (D : SecondOddBridgeData T)
    (z : EvenCrossIndex T) :
    D.q₂ + 1 ≤
      T.pairDist (indexToPair T (.inr (EvenCrossIndex.toCross z))) := by
  have hshift := evenQuotientPair_shift_ge D z.1
  have hrank : D.t + 1 ≤ crossRank T z.1.1 z.2 := by
    unfold crossRank
    omega
  have hdist := pairDist_indexToPair_cross T (EvenCrossIndex.toCross z)
  simp only [EvenCrossIndex.toCross] at hdist
  have hpar : quotientPairParity T z.1.1 = 0 := z.1.2
  rw [hpar] at hdist
  calc
    D.q₂ + 1 = 2 * (D.t + 1) := by rw [D.q₂_eq]; omega
    _ ≤ 2 * crossRank T z.1.1 z.2 := Nat.mul_le_mul_left 2 hrank
    _ = T.pairDist
        (indexToPair T (.inr (EvenCrossIndex.toCross z))) := hdist.symm

/-- The exact finite set of even half-ranks at or above `t+1`. -/
def evenTailHalfRanks (N t : ℕ) : Finset ℕ :=
  Finset.Icc (t + 1) (N / 2)

theorem card_evenTailHalfRanks (N t : ℕ) (_ht : t ≤ N / 2) :
    (evenTailHalfRanks N t).card = N / 2 - t := by
  simp [evenTailHalfRanks]

/-- The promised graph-level injection: every even cross-component pair is
sent to its actual high even half-rank. -/
noncomputable def evenCrossTailEmbedding
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T) :
    EvenCrossIndex T ↪ {k : ℕ // k ∈ evenTailHalfRanks (targetN n) D.t} where
  toFun z := ⟨crossRank T z.1.1 z.2, by
    rw [evenTailHalfRanks, Finset.mem_Icc]
    constructor
    · exact evenQuotientPair_shift_ge D z.1 |>.trans <| by
        unfold crossRank
        omega
    · have hdist := pairDist_indexToPair_cross T (EvenCrossIndex.toCross z)
      simp only [EvenCrossIndex.toCross] at hdist
      have hpar : quotientPairParity T z.1.1 = 0 := z.1.2
      rw [hpar] at hdist
      have htarget := hL.pairDist_le_target
        (indexToPair T (.inr (EvenCrossIndex.toCross z)))
      apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2
      calc
        crossRank T z.1.1 z.2 * 2 = 2 * crossRank T z.1.1 z.2 :=
          Nat.mul_comm _ _
        _ = T.pairDist
            (indexToPair T (.inr (EvenCrossIndex.toCross z))) := hdist.symm
        _ ≤ targetN n := htarget⟩
  inj' := by
    intro x y hxy
    have hrank : crossRank T x.1.1 x.2 = crossRank T y.1.1 y.2 :=
      congrArg Subtype.val hxy
    have hx := pairDist_indexToPair_cross T (EvenCrossIndex.toCross x)
    have hy := pairDist_indexToPair_cross T (EvenCrossIndex.toCross y)
    simp only [EvenCrossIndex.toCross] at hx hy
    rw [x.1.2] at hx
    rw [y.1.2] at hy
    have hp : indexToPair T (.inr (EvenCrossIndex.toCross x)) =
        indexToPair T (.inr (EvenCrossIndex.toCross y)) :=
      hL.pairDist_injective (by
        calc
          T.pairDist (indexToPair T (.inr (EvenCrossIndex.toCross x))) =
              2 * crossRank T x.1.1 x.2 := hx
          _ = 2 * crossRank T y.1.1 y.2 := by rw [hrank]
          _ = T.pairDist
              (indexToPair T (.inr (EvenCrossIndex.toCross y))) := hy.symm)
    have hz : EvenCrossIndex.toCross x = EvenCrossIndex.toCross y := by
      have hs : (Sum.inr (EvenCrossIndex.toCross x) :
          WithinIndex T ⊕ CrossIndex T) =
          Sum.inr (EvenCrossIndex.toCross y) := by
        exact (vertexPairIndexEquiv T).symm.injective hp
      exact Sum.inr.inj hs
    exact EvenCrossIndex.toCross_injective hz

/-- Cardinal high-tail consequence of the graph injection. -/
theorem evenCross_card_le_highTail
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T) :
    Fintype.card (EvenCrossIndex T) ≤ targetN n / 2 - D.t := by
  have ht : D.t ≤ targetN n / 2 := by
    have hq := D.q₂_le_target
    rw [D.q₂_eq] at hq
    omega
  calc
    Fintype.card (EvenCrossIndex T) ≤
        Fintype.card {k : ℕ //
          k ∈ evenTailHalfRanks (targetN n) D.t} :=
      Fintype.card_le_of_injective (evenCrossTailEmbedding hL D)
        (evenCrossTailEmbedding hL D).injective
    _ = (evenTailHalfRanks (targetN n) D.t).card := Fintype.card_coe _
    _ = targetN n / 2 - D.t := card_evenTailHalfRanks _ _ ht

/-- The cardinal of `EvenCrossIndex` is the sum of the actual Cartesian
block cardinalities.  Thus the preceding theorem counts original vertex
pairs, not merely quotient vertices. -/
theorem evenCross_card_eq_sum_products (T : PosIntTree n) :
    Fintype.card (EvenCrossIndex T) =
      ∑ q : EvenQuotientComponentPair T,
        Fintype.card (ComponentVertex T q.1.left) *
          Fintype.card (ComponentVertex T q.1.right) := by
  simp only [EvenCrossIndex, Fintype.card_sigma, Fintype.card_prod]

/-! ## Physical-rank puncturing in the same high tail -/

/-- The global pair underlying an even cross-component index really has
endpoints in different even components.  This small lemma is what prevents a
cross pair from silently colliding with an even physical edge. -/
theorem EvenCrossIndex.indexToPair_components_ne
    {T : PosIntTree n} (z : EvenCrossIndex T) :
    componentOf T (indexToPair T (.inr (EvenCrossIndex.toCross z))).left ≠
      componentOf T (indexToPair T (.inr (EvenCrossIndex.toCross z))).right := by
  intro hsame
  have hs := indexToPair_cross_sym2 T (EvenCrossIndex.toCross z)
  rcases Sym2.eq_iff.mp hs with h | h
  · rcases h with ⟨hl, hr⟩
    apply z.1.1.ne
    calc
      z.1.1.left = componentOf T z.2.1.1 := z.2.1.2.symm
      _ = componentOf T
          (indexToPair T (.inr (EvenCrossIndex.toCross z))).left :=
        congrArg (componentOf T) hl.symm
      _ = componentOf T
          (indexToPair T (.inr (EvenCrossIndex.toCross z))).right := hsame
      _ = componentOf T z.2.2.1 := congrArg (componentOf T) hr
      _ = z.1.1.right := z.2.2.2
  · rcases h with ⟨hl, hr⟩
    apply z.1.1.ne
    calc
      z.1.1.left = componentOf T z.2.1.1 := z.2.1.2.symm
      _ = componentOf T
          (indexToPair T (.inr (EvenCrossIndex.toCross z))).right :=
        congrArg (componentOf T) hr.symm
      _ = componentOf T
          (indexToPair T (.inr (EvenCrossIndex.toCross z))).left := hsame.symm
      _ = componentOf T z.2.2.1 := congrArg (componentOf T) hl
      _ = z.1.1.right := z.2.2.2

/-- Actual even physical edges whose half-ranks lie in the q₂ high tail. -/
abbrev HighEvenPhysicalEdge {T : PosIntTree n}
    (D : SecondOddBridgeData T) :=
  {e : T.Edge // Even (T.weight e) ∧ D.t + 1 ≤ T.weight e / 2}

/-- Even high physical edges inject into the very same rank interval used by
the even cross-component blocks. -/
noncomputable def highEvenPhysicalTailEmbedding
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T) :
    HighEvenPhysicalEdge D ↪
      {k : ℕ // k ∈ evenTailHalfRanks (targetN n) D.t} where
  toFun e := ⟨T.weight e.1 / 2, by
    rw [evenTailHalfRanks, Finset.mem_Icc]
    refine ⟨e.2.2, ?_⟩
    have htarget := (Finset.mem_Icc.mp
      (t1_edge_weight_mem_target hL e.1)).2
    have hexact := Nat.two_mul_div_two_of_even e.2.1
    omega⟩
  inj' := by
    intro e f hef
    have hhalf : T.weight e.1 / 2 = T.weight f.1 / 2 :=
      congrArg Subtype.val hef
    have he := Nat.two_mul_div_two_of_even e.2.1
    have hf := Nat.two_mul_div_two_of_even f.2.1
    apply Subtype.ext
    exact t1_edge_weight_injective hL (by omega)

/-- The cross blocks and the high even physical weights form a disjoint sum
inside one high-rank interval.  Cross/physical disjointness is derived from
global distance injectivity and the even-component partition. -/
noncomputable def evenCrossPhysicalTailEmbedding
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T) :
    EvenCrossIndex T ⊕ HighEvenPhysicalEdge D ↪
      {k : ℕ // k ∈ evenTailHalfRanks (targetN n) D.t} where
  toFun
    | .inl z => evenCrossTailEmbedding hL D z
    | .inr e => highEvenPhysicalTailEmbedding hL D e
  inj' := by
    intro x y hxy
    cases x with
    | inl x =>
        cases y with
        | inl y =>
            exact congrArg Sum.inl
              ((evenCrossTailEmbedding hL D).injective hxy)
        | inr y =>
            exfalso
            have hrank : crossRank T x.1.1 x.2 = T.weight y.1 / 2 :=
              congrArg Subtype.val hxy
            have hcross := pairDist_indexToPair_cross T
              (EvenCrossIndex.toCross x)
            simp only [EvenCrossIndex.toCross] at hcross
            rw [x.1.2] at hcross
            have hyexact := Nat.two_mul_div_two_of_even y.2.1
            have hp : indexToPair T (.inr (EvenCrossIndex.toCross x)) =
                T.edgePair y.1 :=
              hL.pairDist_injective (by
                rw [T.edgePair_dist]
                calc
                  T.pairDist
                      (indexToPair T (.inr (EvenCrossIndex.toCross x))) =
                      2 * crossRank T x.1.1 x.2 := hcross
                  _ = 2 * (T.weight y.1 / 2) := by rw [hrank]
                  _ = T.weight y.1 := hyexact)
            apply EvenCrossIndex.indexToPair_components_ne x
            rw [hp, T.edgePair_left, T.edgePair_right]
            exact evenEdge_components_eq T y.1 y.2.1
    | inr x =>
        cases y with
        | inl y =>
            exfalso
            have hrank : T.weight x.1 / 2 = crossRank T y.1.1 y.2 :=
              congrArg Subtype.val hxy
            have hcross := pairDist_indexToPair_cross T
              (EvenCrossIndex.toCross y)
            simp only [EvenCrossIndex.toCross] at hcross
            rw [y.1.2] at hcross
            have hxexact := Nat.two_mul_div_two_of_even x.2.1
            have hp : indexToPair T (.inr (EvenCrossIndex.toCross y)) =
                T.edgePair x.1 :=
              hL.pairDist_injective (by
                rw [T.edgePair_dist]
                calc
                  T.pairDist
                      (indexToPair T (.inr (EvenCrossIndex.toCross y))) =
                      2 * crossRank T y.1.1 y.2 := hcross
                  _ = 2 * (T.weight x.1 / 2) := by rw [← hrank]
                  _ = T.weight x.1 := hxexact)
            apply EvenCrossIndex.indexToPair_components_ne y
            rw [hp, T.edgePair_left, T.edgePair_right]
            exact evenEdge_components_eq T x.1 x.2.1
        | inr y =>
            exact congrArg Sum.inr
              ((highEvenPhysicalTailEmbedding hL D).injective hxy)

/-- Exact subtraction-free graph-level punctured-tail capacity. -/
theorem evenCross_add_highEvenPhysical_card_le_tail
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T) :
    Fintype.card (EvenCrossIndex T) +
        Fintype.card (HighEvenPhysicalEdge D) ≤
      targetN n / 2 - D.t := by
  have ht : D.t ≤ targetN n / 2 := by
    have hq := D.q₂_le_target
    rw [D.q₂_eq] at hq
    omega
  calc
    Fintype.card (EvenCrossIndex T) +
        Fintype.card (HighEvenPhysicalEdge D) =
        Fintype.card (EvenCrossIndex T ⊕ HighEvenPhysicalEdge D) := by
      rw [Fintype.card_sum]
    _ ≤ Fintype.card
        {k : ℕ // k ∈ evenTailHalfRanks (targetN n) D.t} :=
      Fintype.card_le_of_injective (evenCrossPhysicalTailEmbedding hL D)
        (evenCrossPhysicalTailEmbedding hL D).injective
    _ = (evenTailHalfRanks (targetN n) D.t).card := Fintype.card_coe _
    _ = targetN n / 2 - D.t := card_evenTailHalfRanks _ _ ht

/-- Queryable graph-level q₂ cap retaining both the exact cross demand and
the exact number of puncturing even physical ranks. -/
theorem q₂_le_graph_punctured_highTail
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T) :
    D.q₂ ≤ 2 * (targetN n / 2 -
      Fintype.card (EvenCrossIndex T) -
      Fintype.card (HighEvenPhysicalEdge D)) + 1 := by
  have htail := evenCross_add_highEvenPhysical_card_le_tail hL D
  have ht : D.t ≤ targetN n / 2 := by
    have hq := D.q₂_le_target
    rw [D.q₂_eq] at hq
    omega
  have hrestore : targetN n / 2 - D.t + D.t = targetN n / 2 :=
    Nat.sub_add_cancel ht
  have hcap : Fintype.card (EvenCrossIndex T) +
      Fintype.card (HighEvenPhysicalEdge D) + D.t ≤ targetN n / 2 := by
    omega
  rw [D.q₂_eq]
  omega

/-- Placement-free graph endpoint: any proved floor for the actual indexed
cross blocks immediately gives the corrected q₂ cap. -/
theorem q₂_le_graph_crossFloor
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T)
    (G : ℕ) (hG : G ≤ Fintype.card (EvenCrossIndex T)) :
    D.q₂ ≤ 2 * (targetN n / 2 - G) + 1 := by
  have htail := evenCross_card_le_highTail hL D
  have ht : D.t ≤ targetN n / 2 := by
    have hq := D.q₂_le_target
    rw [D.q₂_eq] at hq
    omega
  have hrestore : targetN n / 2 - D.t + D.t = targetN n / 2 :=
    Nat.sub_add_cancel ht
  have hcap : G + D.t ≤ targetN n / 2 := by
    omega
  rw [D.q₂_eq]
  omega

/-- Fully canonical version, whose only extra input is existence of an
actual second odd physical edge. -/
theorem canonical_q₂_le_graph_crossFloor
    {T : PosIntTree n} (hL : IsLeech T) (hn : 2 ≤ n)
    (h₂ : HasNonunitOddBridge T) (G : ℕ)
    (hG : G ≤ Fintype.card (EvenCrossIndex T)) :
    secondOddWeight h₂ ≤ 2 * (targetN n / 2 - G) + 1 := by
  simpa only [canonicalSecondOddBridgeData_q₂] using
    q₂_le_graph_crossFloor hL (canonicalSecondOddBridgeData hL hn h₂) G hG

/-! ## Low-rank companion: actual graph embeddings -/

theorem SecondOddBridgeData.t_le_evenTargetHalf
    {T : PosIntTree n} (D : SecondOddBridgeData T) :
    D.t ≤ targetN n / 2 := by
  have hq := D.q₂_le_target
  rw [D.q₂_eq] at hq
  omega

theorem SecondOddBridgeData.t_lt_oddTargetHalfCount
    {T : PosIntTree n} (D : SecondOddBridgeData T) :
    D.t < (targetN n + 1) / 2 := by
  have hq := D.q₂_le_target
  rw [D.q₂_eq] at hq
  omega

/-- The target even half-rank `i+1`, for `i<t`. -/
def lowEvenTargetHalfRank {T : PosIntTree n} (D : SecondOddBridgeData T)
    (i : Fin D.t) :
    {k : ℕ // k ∈ Finset.Icc 1 (targetN n / 2)} :=
  ⟨i.1 + 1, by
    rw [Finset.mem_Icc]
    exact ⟨by omega, by
      have ht := D.t_le_evenTargetHalf
      omega⟩⟩

/-- The unique actual pair at the even target distance `2(i+1)`. -/
noncomputable def lowEvenPair
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T)
    (i : Fin D.t) : EvenVertexPair T :=
  (LeechTrees.OddQuotient.IsLeech.evenHalfRankEquiv hL).symm
    (lowEvenTargetHalfRank D i)

theorem lowEvenPair_halfRank
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T)
    (i : Fin D.t) :
    T.pairDist (lowEvenPair hL D i).1 / 2 = i.1 + 1 := by
  have h := congrArg Subtype.val
    ((LeechTrees.OddQuotient.IsLeech.evenHalfRankEquiv hL).apply_symm_apply
      (lowEvenTargetHalfRank D i))
  simpa only [lowEvenPair,
    LeechTrees.OddQuotient.IsLeech.evenHalfRankEquiv_val,
    lowEvenTargetHalfRank] using h

theorem lowEvenPair_dist
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T)
    (i : Fin D.t) :
    T.pairDist (lowEvenPair hL D i).1 = 2 * (i.1 + 1) := by
  have hhalf := lowEvenPair_halfRank hL D i
  have heven := (lowEvenPair hL D i).2
  omega

theorem lowEvenPair_injective
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T) :
    Function.Injective (lowEvenPair hL D) := by
  intro i j hij
  have htargets :=
    (LeechTrees.OddQuotient.IsLeech.evenHalfRankEquiv hL).symm.injective hij
  have hvals := congrArg Subtype.val htargets
  apply Fin.ext
  simpa only [lowEvenTargetHalfRank] using Nat.add_right_cancel hvals

/-- A low even target pair cannot occupy an even cross-component block,
because every such block starts at half-rank `t+1`. -/
theorem lowEvenPair_exists_withinIndex
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T)
    (i : Fin D.t) :
    ∃ z : WithinIndex T,
      evenPairBlockEquiv T (lowEvenPair hL D i) = .inl z := by
  generalize hb : evenPairBlockEquiv T (lowEvenPair hL D i) = b
  cases b with
  | inl z => exact ⟨z, rfl⟩
  | inr z =>
      exfalso
      have hrank := evenPairBlockEquiv_rank T (lowEvenPair hL D i)
      rw [hb] at hrank
      simp only [evenBlockRank] at hrank
      have hshift := evenQuotientPair_shift_ge D z.1
      have hcross : D.t + 1 ≤ crossRank T z.1.1 z.2 := by
        unfold crossRank
        omega
      have hhalf := lowEvenPair_halfRank hL D i
      omega

/-- The actual within-component index carrying low even half-rank `i+1`. -/
noncomputable def lowEvenWithinIndex
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T)
    (i : Fin D.t) : WithinIndex T :=
  Classical.choose (lowEvenPair_exists_withinIndex hL D i)

theorem lowEvenWithinIndex_spec
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T)
    (i : Fin D.t) :
    evenPairBlockEquiv T (lowEvenPair hL D i) =
      .inl (lowEvenWithinIndex hL D i) :=
  Classical.choose_spec (lowEvenPair_exists_withinIndex hL D i)

/-- Graph-level injection of all low even target ranks into actual internal
component pairs. -/
noncomputable def lowEvenWithinEmbedding
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T) :
    Fin D.t ↪ WithinIndex T where
  toFun := lowEvenWithinIndex hL D
  inj' := by
    intro i j hij
    apply lowEvenPair_injective hL D
    apply (evenPairBlockEquiv T).injective
    rw [lowEvenWithinIndex_spec hL D i,
      lowEvenWithinIndex_spec hL D j, hij]

theorem lowEven_internal_capacity
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T) :
    D.t ≤ Fintype.card (WithinIndex T) := by
  simpa using Fintype.card_le_of_injective (lowEvenWithinEmbedding hL D)
    (lowEvenWithinEmbedding hL D).injective

/-- The target odd half-rank `i`, for `i<t`. -/
def lowOddTargetHalfRank {T : PosIntTree n} (D : SecondOddBridgeData T)
    (i : Fin D.t) : Fin ((targetN n + 1) / 2) :=
  ⟨i.1, i.2.trans D.t_lt_oddTargetHalfCount⟩

/-- The unique actual pair at the odd target distance `2i+1`. -/
noncomputable def lowOddPair
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T)
    (i : Fin D.t) : OddVertexPair T :=
  (LeechTrees.OddQuotient.IsLeech.oddHalfRankEquiv hL).symm
    (lowOddTargetHalfRank D i)

theorem lowOddPair_halfRank
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T)
    (i : Fin D.t) :
    T.pairDist (lowOddPair hL D i).1 / 2 = i.1 := by
  have h := congrArg Fin.val
    ((LeechTrees.OddQuotient.IsLeech.oddHalfRankEquiv hL).apply_symm_apply
      (lowOddTargetHalfRank D i))
  simpa only [lowOddPair,
    LeechTrees.OddQuotient.IsLeech.oddHalfRankEquiv_val,
    lowOddTargetHalfRank] using h

theorem lowOddPair_dist
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T)
    (i : Fin D.t) :
    T.pairDist (lowOddPair hL D i).1 = 2 * i.1 + 1 := by
  have hhalf := lowOddPair_halfRank hL D i
  have hodd := (lowOddPair hL D i).2
  omega

theorem lowOddPair_dist_lt_q₂
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T)
    (i : Fin D.t) :
    T.pairDist (lowOddPair hL D i).1 < D.q₂ := by
  rw [lowOddPair_dist hL D i, D.q₂_eq]
  omega

theorem lowOddPair_injective
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T) :
    Function.Injective (lowOddPair hL D) := by
  intro i j hij
  have htargets :=
    (LeechTrees.OddQuotient.IsLeech.oddHalfRankEquiv hL).symm.injective hij
  apply Fin.ext
  simpa only [lowOddTargetHalfRank] using congrArg Fin.val htargets

/-- If a path shorter than q₂ avoids the unit bridge, every edge on it is
even: an odd edge would be either the avoided unit or a non-unit bridge of
weight at least q₂. -/
theorem path_all_even_of_avoids_unit_of_dist_lt_q₂
    {T : PosIntTree n} (D : SecondOddBridgeData T)
    {u v : Fin n} (havoid : D.unit.1.1 ∉ T.pathEdges u v)
    (hdist : T.dist u v < D.q₂) :
    ∀ e ∈ T.pathEdges u v, Even (T.weightOfPair e) := by
  intro e he
  rw [← Nat.not_odd_iff_even]
  intro hodd
  let b : OddBridge T := ⟨T.edgeOfPathMem e he, by
    simpa using hodd⟩
  by_cases hunit : b = D.unit
  · apply havoid
    have hedge : e = D.unit.1.1 := by
      exact congrArg Subtype.val (congrArg Subtype.val hunit)
    simpa [hedge] using he
  · have hlower := D.other_weight_lower b hunit
    have hle := T.weightOfPair_le_dist_of_mem he
    have hweight : T.weight b.1 = T.weightOfPair e := by
      simp [b]
    rw [hweight] at hlower
    omega

/-- Every low odd target pair crosses the actual weight-one bridge. -/
theorem unit_mem_lowOddPair_path
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T)
    (i : Fin D.t) :
    D.unit.1.1 ∈ T.pathEdges
      (lowOddPair hL D i).1.left (lowOddPair hL D i).1.right := by
  by_contra havoid
  have hall := path_all_even_of_avoids_unit_of_dist_lt_q₂ D havoid (by
    simpa [PosIntTree.pairDist] using lowOddPair_dist_lt_q₂ hL D i)
  have hcomp := componentOf_eq_of_path_all_even T hall
  have heven := dist_even_of_component_eq T hcomp
  rcases heven with ⟨k, hk⟩
  have hodd := (lowOddPair hL D i).2
  change T.dist (lowOddPair hL D i).1.left
      (lowOddPair hL D i).1.right % 2 = 1 at hodd
  omega

/-- Actual named vertices in the two even components incident with the unit
bridge. -/
abbrev UnitLeftComponentVertex {T : PosIntTree n}
    (D : SecondOddBridgeData T) :=
  ComponentVertex T (componentOf T (T.edgeLeft D.unit.1))

abbrev UnitRightComponentVertex {T : PosIntTree n}
    (D : SecondOddBridgeData T) :=
  ComponentVertex T (componentOf T (T.edgeRight D.unit.1))

theorem unitRectangle_endpoints_ne
    {T : PosIntTree n} (D : SecondOddBridgeData T)
    (z : UnitLeftComponentVertex D × UnitRightComponentVertex D) :
    z.1.1 ≠ z.2.1 := by
  intro h
  apply oddBridge_components_ne T D.unit
  calc
    componentOf T (T.edgeLeft D.unit.1) = componentOf T z.1.1 := z.1.2.symm
    _ = componentOf T z.2.1 := congrArg (componentOf T) h
    _ = componentOf T (T.edgeRight D.unit.1) := z.2.2

/-- Forget an oriented unit-component rectangle point to its unordered
global pair. -/
noncomputable def unitRectanglePair
    {T : PosIntTree n} (D : SecondOddBridgeData T)
    (z : UnitLeftComponentVertex D × UnitRightComponentVertex D) :
    VertexPair n :=
  VertexPair.ofDistinct z.1.1 z.2.1 (unitRectangle_endpoints_ne D z)

/-- Every low odd target pair is represented by the actual Cartesian product
of the two even components incident with the unit bridge. -/
theorem lowOddPair_exists_unitRectangle
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T)
    (i : Fin D.t) :
    ∃ z : UnitLeftComponentVertex D × UnitRightComponentVertex D,
      unitRectanglePair D z = (lowOddPair hL D i).1 := by
  let p := (lowOddPair hL D i).1
  have hmem := unit_mem_lowOddPair_path hL D i
  rcases (T.mem_pathEdges_iff_opposite_cuts D.unit.1 p.left p.right).mp hmem with
    hdirect | hreverse
  · rcases hdirect with ⟨hleft, hright⟩
    have hroute := T.cross_distance_decomposition D.unit.1 hleft hright
    have hpdist : T.dist p.left p.right < D.q₂ := by
      simpa [p, PosIntTree.pairDist] using lowOddPair_dist_lt_q₂ hL D i
    have hleftDist : T.dist p.left (T.edgeLeft D.unit.1) < D.q₂ := by
      rw [D.unit_weight] at hroute
      omega
    have hrightDist : T.dist p.right (T.edgeRight D.unit.1) < D.q₂ := by
      rw [D.unit_weight, T.dist_comm (T.edgeRight D.unit.1) p.right] at hroute
      omega
    have hleftAvoid : D.unit.1.1 ∉
        T.pathEdges p.left (T.edgeLeft D.unit.1) :=
      (T.cut_reachable_iff_not_mem_pathEdges D.unit.1 _ _).mp hleft
    have hrightAvoid : D.unit.1.1 ∉
        T.pathEdges p.right (T.edgeRight D.unit.1) :=
      (T.cut_reachable_iff_not_mem_pathEdges D.unit.1 _ _).mp hright
    have hleftComp := componentOf_eq_of_path_all_even T
      (path_all_even_of_avoids_unit_of_dist_lt_q₂ D hleftAvoid hleftDist)
    have hrightComp := componentOf_eq_of_path_all_even T
      (path_all_even_of_avoids_unit_of_dist_lt_q₂ D hrightAvoid hrightDist)
    let z : UnitLeftComponentVertex D × UnitRightComponentVertex D :=
      (⟨p.left, hleftComp⟩, ⟨p.right, hrightComp⟩)
    refine ⟨z, ?_⟩
    change VertexPair.ofDistinct p.left p.right _ = p
    rw [VertexPair.ofDistinct_eq_of_lt _ p.left_lt_right]
    apply Subtype.ext
    rfl
  · rcases hreverse with ⟨hright, hleft⟩
    have hroute := T.cross_distance_decomposition D.unit.1 hleft hright
    have hpdist : T.dist p.right p.left < D.q₂ := by
      rw [T.dist_comm]
      simpa [p, PosIntTree.pairDist] using lowOddPair_dist_lt_q₂ hL D i
    have hleftDist : T.dist p.right (T.edgeLeft D.unit.1) < D.q₂ := by
      rw [D.unit_weight] at hroute
      omega
    have hrightDist : T.dist p.left (T.edgeRight D.unit.1) < D.q₂ := by
      rw [D.unit_weight, T.dist_comm (T.edgeRight D.unit.1) p.left] at hroute
      omega
    have hleftAvoid : D.unit.1.1 ∉
        T.pathEdges p.right (T.edgeLeft D.unit.1) :=
      (T.cut_reachable_iff_not_mem_pathEdges D.unit.1 _ _).mp hleft
    have hrightAvoid : D.unit.1.1 ∉
        T.pathEdges p.left (T.edgeRight D.unit.1) :=
      (T.cut_reachable_iff_not_mem_pathEdges D.unit.1 _ _).mp hright
    have hleftComp := componentOf_eq_of_path_all_even T
      (path_all_even_of_avoids_unit_of_dist_lt_q₂ D hleftAvoid hleftDist)
    have hrightComp := componentOf_eq_of_path_all_even T
      (path_all_even_of_avoids_unit_of_dist_lt_q₂ D hrightAvoid hrightDist)
    let z : UnitLeftComponentVertex D × UnitRightComponentVertex D :=
      (⟨p.right, hleftComp⟩, ⟨p.left, hrightComp⟩)
    refine ⟨z, ?_⟩
    change VertexPair.ofDistinct p.right p.left _ = p
    rw [VertexPair.ofDistinct]
    split
    · rename_i hlt
      exact (not_lt_of_ge p.left_lt_right.le hlt).elim
    · rfl

noncomputable def lowOddUnitRectanglePoint
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T)
    (i : Fin D.t) :
    UnitLeftComponentVertex D × UnitRightComponentVertex D :=
  Classical.choose (lowOddPair_exists_unitRectangle hL D i)

theorem lowOddUnitRectanglePoint_spec
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T)
    (i : Fin D.t) :
    unitRectanglePair D (lowOddUnitRectanglePoint hL D i) =
      (lowOddPair hL D i).1 :=
  Classical.choose_spec (lowOddPair_exists_unitRectangle hL D i)

/-- Graph-level injection of the complete low odd prefix into the actual
unit-bridge component rectangle. -/
noncomputable def lowOddUnitRectangleEmbedding
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T) :
    Fin D.t ↪ UnitLeftComponentVertex D × UnitRightComponentVertex D where
  toFun := lowOddUnitRectanglePoint hL D
  inj' := by
    intro i j hij
    apply lowOddPair_injective hL D
    apply Subtype.ext
    rw [← lowOddUnitRectanglePoint_spec hL D i,
      ← lowOddUnitRectanglePoint_spec hL D j, hij]

theorem lowOdd_unitRectangle_capacity
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T) :
    D.t ≤ Fintype.card (UnitLeftComponentVertex D) *
      Fintype.card (UnitRightComponentVertex D) := by
  have hcard := Fintype.card_le_of_injective
    (lowOddUnitRectangleEmbedding hL D)
    (lowOddUnitRectangleEmbedding hL D).injective
  simpa [Fintype.card_prod] using hcard

/-- Fixed-profile companion derived entirely from the two actual low-rank
embeddings. -/
theorem q₂_le_graph_internal_and_unitBridge
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T) :
    D.q₂ ≤ 2 * min (Fintype.card (WithinIndex T))
      (Fintype.card (UnitLeftComponentVertex D) *
        Fintype.card (UnitRightComponentVertex D)) + 1 := by
  exact LeechTrees.secondOddWeight_from_two_capacities
    D.q₂ D.t (Fintype.card (WithinIndex T))
      (Fintype.card (UnitLeftComponentVertex D) *
        Fintype.card (UnitRightComponentVertex D))
      D.q₂_eq (lowEven_internal_capacity hL D)
      (lowOdd_unitRectangle_capacity hL D)

theorem canonical_q₂_le_graph_internal_and_unitBridge
    {T : PosIntTree n} (hL : IsLeech T) (hn : 2 ≤ n)
    (h₂ : HasNonunitOddBridge T) :
    secondOddWeight h₂ ≤
      2 * min (Fintype.card (WithinIndex T))
        (Fintype.card
            (UnitLeftComponentVertex (canonicalSecondOddBridgeData hL hn h₂)) *
          Fintype.card
            (UnitRightComponentVertex (canonicalSecondOddBridgeData hL hn h₂))) + 1 := by
  simpa only [canonicalSecondOddBridgeData_q₂] using
    q₂_le_graph_internal_and_unitBridge hL
      (canonicalSecondOddBridgeData hL hn h₂)

/-! ## Abstract punctured-tail and fixed-profile consequences -/

/-- The exact rank-pool inequality, after the graph injection and the
physical-rank disjointness argument have supplied `S+h <= E-t`. -/
theorem q₂_le_of_punctured_highTail
    (q₂ t E S h : ℕ)
    (q₂_def : q₂ = 2 * t + 1)
    (tail_capacity : S + h + t ≤ E) :
    q₂ ≤ 2 * (E - S - h) + 1 := by
  have ht : t ≤ E - S - h := by
    omega
  omega

/-- Placement-free `G` consequence. -/
theorem q₂_le_of_crossFloor
    (q₂ t E S G : ℕ)
    (q₂_def : q₂ = 2 * t + 1)
    (structural_floor : G ≤ S)
    (tail_capacity : S + t ≤ E) :
    q₂ ≤ 2 * (E - G) + 1 := by
  have ht : t ≤ E - G := by
    omega
  omega

/-- Fixed-profile low-rank companion `q₂ <= 2 min(I,xy)+1`. -/
theorem q₂_le_of_internal_and_unitBridge
    (q₂ t I x y : ℕ)
    (q₂_def : q₂ = 2 * t + 1)
    (low_even : t ≤ I)
    (low_odd : t ≤ x * y) :
    q₂ ≤ 2 * min I (x * y) + 1 := by
  exact LeechTrees.secondOddWeight_from_two_capacities
    q₂ t I (x * y) q₂_def low_even low_odd

/-! ## Sharp order-18 `G` optimization -/

/-- `F(M,k)=(k-1)(2M-k)/2`, evaluated only under the usual feasibility
conditions `1 <= k <= M`. -/
def colorCrossFloor (M k : ℕ) : ℕ :=
  (k - 1) * (2 * M - k) / 2

def FeasibleColorSplit (a b r k : ℕ) : Prop :=
  1 ≤ k ∧ k ≤ a ∧ 1 ≤ r + 1 - k ∧ r + 1 - k ≤ b

/-- Exact sharp `G_{7,11}` values, including the formal endpoints. -/
def order18G : ℕ → ℕ
  | 1 => 0
  | 2 => 6
  | 3 => 11
  | 4 => 15
  | 5 => 18
  | 6 => 20
  | 7 => 21
  | 8 => 31
  | 9 => 40
  | 10 => 48
  | 11 => 55
  | 12 => 61
  | 13 => 66
  | 14 => 70
  | 15 => 73
  | 16 => 75
  | 17 => 76
  | _ => 0

theorem order18G_lower_bound
    {r k : ℕ} (hr₃ : 3 ≤ r) (hr₁₅ : r ≤ 15)
    (hk : FeasibleColorSplit 7 11 r k) :
    order18G r ≤
      colorCrossFloor 7 k + colorCrossFloor 11 (r + 1 - k) := by
  rcases hk with ⟨hk₁, hk₇, hl₁, hl₁₁⟩
  interval_cases r <;> interval_cases k <;>
    norm_num [order18G, colorCrossFloor] at *

theorem order18G_attained
    {r : ℕ} (hr₃ : 3 ≤ r) (hr₁₅ : r ≤ 15) :
    ∃ k, FeasibleColorSplit 7 11 r k ∧
      colorCrossFloor 7 k + colorCrossFloor 11 (r + 1 - k) =
        order18G r := by
  interval_cases r
  · exact ⟨3, by norm_num [FeasibleColorSplit, colorCrossFloor, order18G]⟩
  · exact ⟨4, by norm_num [FeasibleColorSplit, colorCrossFloor, order18G]⟩
  · exact ⟨5, by norm_num [FeasibleColorSplit, colorCrossFloor, order18G]⟩
  · exact ⟨6, by norm_num [FeasibleColorSplit, colorCrossFloor, order18G]⟩
  · exact ⟨7, by norm_num [FeasibleColorSplit, colorCrossFloor, order18G]⟩
  · exact ⟨7, by norm_num [FeasibleColorSplit, colorCrossFloor, order18G]⟩
  · exact ⟨7, by norm_num [FeasibleColorSplit, colorCrossFloor, order18G]⟩
  · exact ⟨7, by norm_num [FeasibleColorSplit, colorCrossFloor, order18G]⟩
  · exact ⟨7, by norm_num [FeasibleColorSplit, colorCrossFloor, order18G]⟩
  · exact ⟨7, by norm_num [FeasibleColorSplit, colorCrossFloor, order18G]⟩
  · exact ⟨7, by norm_num [FeasibleColorSplit, colorCrossFloor, order18G]⟩
  · exact ⟨7, by norm_num [FeasibleColorSplit, colorCrossFloor, order18G]⟩
  · exact ⟨7, by norm_num [FeasibleColorSplit, colorCrossFloor, order18G]⟩

/-- Optimization correctness on the full feasible formal boundary.  The
`r = 1` row is deliberately excluded: with only two quotient components
there is no nonunit (second) odd bridge to which the later `q₂` cap applies. -/
theorem order18G_formalBoundary_lower_bound
    {r k : ℕ} (hr₂ : 2 ≤ r) (hr₁₇ : r ≤ 17)
    (hk : FeasibleColorSplit 7 11 r k) :
    order18G r ≤
      colorCrossFloor 7 k + colorCrossFloor 11 (r + 1 - k) := by
  rcases hk with ⟨hk₁, hk₇, hl₁, hl₁₁⟩
  interval_cases r <;> interval_cases k <;>
    norm_num [order18G, colorCrossFloor] at *

/-- Every row of the feasible formal boundary `2 ≤ r ≤ 17` is attained by
an explicit color split. -/
theorem order18G_formalBoundary_attained
    {r : ℕ} (hr₂ : 2 ≤ r) (hr₁₇ : r ≤ 17) :
    ∃ k, FeasibleColorSplit 7 11 r k ∧
      colorCrossFloor 7 k + colorCrossFloor 11 (r + 1 - k) =
        order18G r := by
  interval_cases r
  · exact ⟨2, by norm_num [FeasibleColorSplit, colorCrossFloor, order18G]⟩
  · exact ⟨3, by norm_num [FeasibleColorSplit, colorCrossFloor, order18G]⟩
  · exact ⟨4, by norm_num [FeasibleColorSplit, colorCrossFloor, order18G]⟩
  · exact ⟨5, by norm_num [FeasibleColorSplit, colorCrossFloor, order18G]⟩
  · exact ⟨6, by norm_num [FeasibleColorSplit, colorCrossFloor, order18G]⟩
  · exact ⟨7, by norm_num [FeasibleColorSplit, colorCrossFloor, order18G]⟩
  · exact ⟨7, by norm_num [FeasibleColorSplit, colorCrossFloor, order18G]⟩
  · exact ⟨7, by norm_num [FeasibleColorSplit, colorCrossFloor, order18G]⟩
  · exact ⟨7, by norm_num [FeasibleColorSplit, colorCrossFloor, order18G]⟩
  · exact ⟨7, by norm_num [FeasibleColorSplit, colorCrossFloor, order18G]⟩
  · exact ⟨7, by norm_num [FeasibleColorSplit, colorCrossFloor, order18G]⟩
  · exact ⟨7, by norm_num [FeasibleColorSplit, colorCrossFloor, order18G]⟩
  · exact ⟨7, by norm_num [FeasibleColorSplit, colorCrossFloor, order18G]⟩
  · exact ⟨7, by norm_num [FeasibleColorSplit, colorCrossFloor, order18G]⟩
  · exact ⟨7, by norm_num [FeasibleColorSplit, colorCrossFloor, order18G]⟩
  · exact ⟨7, by norm_num [FeasibleColorSplit, colorCrossFloor, order18G]⟩

def order18PrimaryCap (r : ℕ) : ℕ :=
  2 * (76 - order18G r) + 1

theorem order18_primary_cap
    (q₂ t S r : ℕ)
    (q₂_def : q₂ = 2 * t + 1)
    (structural_floor : order18G r ≤ S)
    (tail_capacity : S + t ≤ 76) :
    q₂ ≤ order18PrimaryCap r := by
  exact q₂_le_of_crossFloor q₂ t 76 S (order18G r)
    q₂_def structural_floor tail_capacity

/-- Order-18 G cap with the tail inequality discharged by the actual graph
injection.  The remaining hypothesis is exactly the independently checkable
component-size floor for the actual indexed quotient blocks. -/
theorem order18_graph_primary_cap
    {T : PosIntTree 18} (hL : IsLeech T) (D : SecondOddBridgeData T)
    (r : ℕ) (hG : order18G r ≤ Fintype.card (EvenCrossIndex T)) :
    D.q₂ ≤ order18PrimaryCap r := by
  have h := q₂_le_graph_crossFloor hL D (order18G r) hG
  norm_num [targetN, order18PrimaryCap] at h ⊢
  exact h

/-- Exact graph-level punctured refinement of the order-18 G endpoint. -/
theorem order18_graph_punctured_cap
    {T : PosIntTree 18} (hL : IsLeech T) (D : SecondOddBridgeData T) :
    D.q₂ ≤ 2 * (76 - Fintype.card (EvenCrossIndex T) -
      Fintype.card (HighEvenPhysicalEdge D)) + 1 := by
  simpa [targetN] using q₂_le_graph_punctured_highTail hL D

theorem order18_canonical_graph_primary_cap
    {T : PosIntTree 18} (hL : IsLeech T)
    (h₂ : HasNonunitOddBridge T) (r : ℕ)
    (hG : order18G r ≤ Fintype.card (EvenCrossIndex T)) :
    secondOddWeight h₂ ≤ order18PrimaryCap r := by
  simpa only [canonicalSecondOddBridgeData_q₂] using
    order18_graph_primary_cap hL
      (canonicalSecondOddBridgeData hL (by decide) h₂) r hG

theorem order18G_table :
    [order18G 3, order18G 4, order18G 5, order18G 6,
      order18G 7, order18G 8, order18G 9, order18G 10,
      order18G 11, order18G 12, order18G 13, order18G 14,
      order18G 15] =
    [11, 15, 18, 20, 21, 31, 40, 48, 55, 61, 66, 70, 73] := by
  decide

/-- Literal table for every formally displayed `G_{7,11}` boundary row.
Only rows `2 ≤ r ≤ 17` have an accompanying feasible-split optimization
theorem; row `r = 1` is retained as the documented formal endpoint. -/
theorem order18G_formalBoundary_table :
    [order18G 1, order18G 2, order18G 3, order18G 4,
      order18G 5, order18G 6, order18G 7, order18G 8,
      order18G 9, order18G 10, order18G 11, order18G 12,
      order18G 13, order18G 14, order18G 15, order18G 16,
      order18G 17] =
    [0, 6, 11, 15, 18, 20, 21, 31, 40, 48, 55, 61, 66, 70,
      73, 75, 76] := by
  decide

theorem order18PrimaryCap_table :
    [order18PrimaryCap 3, order18PrimaryCap 4, order18PrimaryCap 5,
      order18PrimaryCap 6, order18PrimaryCap 7, order18PrimaryCap 8,
      order18PrimaryCap 9, order18PrimaryCap 10, order18PrimaryCap 11,
      order18PrimaryCap 12, order18PrimaryCap 13, order18PrimaryCap 14,
      order18PrimaryCap 15] =
    [131, 123, 117, 113, 111, 91, 73, 57, 43, 31, 21, 13, 7] := by
  decide

/-- Literal primary-cap table on the feasible formal boundary. -/
theorem order18PrimaryCap_formalBoundary_table :
    [order18PrimaryCap 2, order18PrimaryCap 3,
      order18PrimaryCap 4, order18PrimaryCap 5,
      order18PrimaryCap 6, order18PrimaryCap 7,
      order18PrimaryCap 8, order18PrimaryCap 9,
      order18PrimaryCap 10, order18PrimaryCap 11,
      order18PrimaryCap 12, order18PrimaryCap 13,
      order18PrimaryCap 14, order18PrimaryCap 15,
      order18PrimaryCap 16, order18PrimaryCap 17] =
    [141, 131, 123, 117, 113, 111, 91, 73, 57, 43, 31, 21, 13,
      7, 3, 1] := by
  decide

/-! ## Sharp order-18 `H` optimization -/

def order18FixedCompanionCapacity (r k : ℕ) : ℕ :=
  min (Nat.choose (8 - k) 2 + Nat.choose (11 + k - r) 2)
    ((8 - k) * (11 + k - r))

def order18H : ℕ → ℕ
  | 2 => 66
  | 3 => 60
  | 4 => 51
  | 5 => 45
  | 6 => 38
  | 7 => 32
  | 8 => 27
  | 9 => 21
  | 10 => 18
  | 11 => 13
  | 12 => 10
  | 13 => 7
  | 14 => 4
  | 15 => 3
  | 16 => 1
  | 17 => 0
  | _ => 0

theorem order18H_upper_bound
    {r k : ℕ} (hr₃ : 3 ≤ r) (hr₁₅ : r ≤ 15)
    (hk : FeasibleColorSplit 7 11 r k) :
    order18FixedCompanionCapacity r k ≤ order18H r := by
  rcases hk with ⟨hk₁, hk₇, hl₁, hl₁₁⟩
  interval_cases r <;> interval_cases k <;>
    norm_num [Nat.choose, order18H, order18FixedCompanionCapacity] at *

theorem order18H_attained
    {r : ℕ} (hr₃ : 3 ≤ r) (hr₁₅ : r ≤ 15) :
    ∃ k, FeasibleColorSplit 7 11 r k ∧
      order18FixedCompanionCapacity r k = order18H r := by
  interval_cases r
  · exact ⟨2, by norm_num [Nat.choose, FeasibleColorSplit,
      order18FixedCompanionCapacity, order18H]⟩
  · exact ⟨2, by norm_num [Nat.choose, FeasibleColorSplit,
      order18FixedCompanionCapacity, order18H]⟩
  · exact ⟨3, by norm_num [Nat.choose, FeasibleColorSplit,
      order18FixedCompanionCapacity, order18H]⟩
  · exact ⟨3, by norm_num [Nat.choose, FeasibleColorSplit,
      order18FixedCompanionCapacity, order18H]⟩
  · exact ⟨4, by norm_num [Nat.choose, FeasibleColorSplit,
      order18FixedCompanionCapacity, order18H]⟩
  · exact ⟨4, by norm_num [Nat.choose, FeasibleColorSplit,
      order18FixedCompanionCapacity, order18H]⟩
  · exact ⟨5, by norm_num [Nat.choose, FeasibleColorSplit,
      order18FixedCompanionCapacity, order18H]⟩
  · exact ⟨5, by norm_num [Nat.choose, FeasibleColorSplit,
      order18FixedCompanionCapacity, order18H]⟩
  · exact ⟨5, by norm_num [Nat.choose, FeasibleColorSplit,
      order18FixedCompanionCapacity, order18H]⟩
  · exact ⟨6, by norm_num [Nat.choose, FeasibleColorSplit,
      order18FixedCompanionCapacity, order18H]⟩
  · exact ⟨6, by norm_num [Nat.choose, FeasibleColorSplit,
      order18FixedCompanionCapacity, order18H]⟩
  · exact ⟨7, by norm_num [Nat.choose, FeasibleColorSplit,
      order18FixedCompanionCapacity, order18H]⟩
  · exact ⟨7, by norm_num [Nat.choose, FeasibleColorSplit,
      order18FixedCompanionCapacity, order18H]⟩

def order18CompanionCap (r : ℕ) : ℕ := 2 * order18H r + 1

theorem order18_companion_cap
    (q₂ t I x y r k : ℕ)
    (hr₃ : 3 ≤ r) (hr₁₅ : r ≤ 15)
    (hk : FeasibleColorSplit 7 11 r k)
    (q₂_def : q₂ = 2 * t + 1)
    (low_even : t ≤ I) (low_odd : t ≤ x * y)
    (internal_capacity :
      I ≤ Nat.choose (8 - k) 2 + Nat.choose (11 + k - r) 2)
    (bridge_capacity : x * y ≤ (8 - k) * (11 + k - r)) :
    q₂ ≤ order18CompanionCap r := by
  have ht : t ≤ order18FixedCompanionCapacity r k := by
    unfold order18FixedCompanionCapacity
    rw [Nat.le_min]
    exact ⟨low_even.trans internal_capacity, low_odd.trans bridge_capacity⟩
  have hH := order18H_upper_bound hr₃ hr₁₅ hk
  unfold order18CompanionCap
  omega

/-- Order-18 H cap whose two low-prefix demands are discharged by the actual
within-component and unit-bridge rectangle embeddings.  The last two inputs
are the fixed-profile component-size upper bounds, not tail assumptions. -/
theorem order18_graph_companion_cap
    {T : PosIntTree 18} (hL : IsLeech T) (D : SecondOddBridgeData T)
    (r k : ℕ) (hr₃ : 3 ≤ r) (hr₁₅ : r ≤ 15)
    (hk : FeasibleColorSplit 7 11 r k)
    (internal_profile_bound :
      Fintype.card (WithinIndex T) ≤
        Nat.choose (8 - k) 2 + Nat.choose (11 + k - r) 2)
    (unit_profile_bound :
      Fintype.card (UnitLeftComponentVertex D) *
          Fintype.card (UnitRightComponentVertex D) ≤
        (8 - k) * (11 + k - r)) :
    D.q₂ ≤ order18CompanionCap r := by
  exact order18_companion_cap
    D.q₂ D.t (Fintype.card (WithinIndex T))
      (Fintype.card (UnitLeftComponentVertex D))
      (Fintype.card (UnitRightComponentVertex D)) r k
      hr₃ hr₁₅ hk D.q₂_eq
      (lowEven_internal_capacity hL D)
      (lowOdd_unitRectangle_capacity hL D)
      internal_profile_bound unit_profile_bound

theorem order18_canonical_graph_companion_cap
    {T : PosIntTree 18} (hL : IsLeech T)
    (h₂ : HasNonunitOddBridge T) (r k : ℕ)
    (hr₃ : 3 ≤ r) (hr₁₅ : r ≤ 15)
    (hk : FeasibleColorSplit 7 11 r k)
    (internal_profile_bound :
      Fintype.card (WithinIndex T) ≤
        Nat.choose (8 - k) 2 + Nat.choose (11 + k - r) 2)
    (unit_profile_bound :
      Fintype.card
          (UnitLeftComponentVertex (canonicalSecondOddBridgeData hL (by decide) h₂)) *
        Fintype.card
          (UnitRightComponentVertex (canonicalSecondOddBridgeData hL (by decide) h₂)) ≤
        (8 - k) * (11 + k - r)) :
    secondOddWeight h₂ ≤ order18CompanionCap r := by
  simpa only [canonicalSecondOddBridgeData_q₂] using
    order18_graph_companion_cap hL
      (canonicalSecondOddBridgeData hL (by decide) h₂)
      r k hr₃ hr₁₅ hk internal_profile_bound unit_profile_bound

theorem order18H_table :
    [order18H 3, order18H 4, order18H 5, order18H 6,
      order18H 7, order18H 8, order18H 9, order18H 10,
      order18H 11, order18H 12, order18H 13, order18H 14,
      order18H 15] =
    [60, 51, 45, 38, 32, 27, 21, 18, 13, 10, 7, 4, 3] := by
  decide

theorem order18CompanionCap_table :
    [order18CompanionCap 3, order18CompanionCap 4,
      order18CompanionCap 5, order18CompanionCap 6,
      order18CompanionCap 7, order18CompanionCap 8,
      order18CompanionCap 9, order18CompanionCap 10,
      order18CompanionCap 11, order18CompanionCap 12,
      order18CompanionCap 13, order18CompanionCap 14,
      order18CompanionCap 15] =
    [121, 103, 91, 77, 65, 55, 43, 37, 27, 21, 15, 9, 7] := by
  decide

/-! ## Conditional combination with the external `Q <= 68` input -/

def order18OddPackingCap (r : ℕ) : ℕ := 71 - 2 * r

def order18EffectiveCap (r : ℕ) : ℕ :=
  min (order18CompanionCap r) (order18OddPackingCap r)

/-- This theorem is conditional on the separately established largest-odd
packing inequality.  It is not an unconditional Lean proof of `Q <= 68`. -/
theorem order18_effective_cap_of_largestOdd_le_67
    (q₂ r : ℕ)
    (companion : q₂ ≤ order18CompanionCap r)
    (odd_packing_from_largestOdd_le_67 : q₂ ≤ 71 - 2 * r) :
    q₂ ≤ order18EffectiveCap r := by
  exact (Nat.le_min).2 ⟨companion, odd_packing_from_largestOdd_le_67⟩

theorem order18EffectiveCap_table :
    [order18EffectiveCap 3, order18EffectiveCap 4,
      order18EffectiveCap 5, order18EffectiveCap 6,
      order18EffectiveCap 7, order18EffectiveCap 8,
      order18EffectiveCap 9, order18EffectiveCap 10,
      order18EffectiveCap 11, order18EffectiveCap 12,
      order18EffectiveCap 13, order18EffectiveCap 14,
      order18EffectiveCap 15] =
    [65, 63, 61, 59, 57, 55, 43, 37, 27, 21, 15, 9, 7] := by
  decide

/-! ## Equality prefix and truncated-factorization boundary -/

/-- Rooted depth in a three-vertex path with successive edge weights
`u,v`, where `port=0,1,2`. -/
def pathThreeDepth (u v : ℕ) (port vertex : Fin 3) : ℕ :=
  if port = vertex then 0
  else if (port = 0 ∧ vertex = 1) ∨ (port = 1 ∧ vertex = 0) then u
  else if (port = 1 ∧ vertex = 2) ∨ (port = 2 ∧ vertex = 1) then v
  else u + v

/-- Exact local equality audit at `r=15,q₂=7`: if the three internal
distances are precisely `2,4,6` and the three distances across a unit bridge
are precisely `1,3,5`, the bridge attaches at the middle vertex and the two
even path weights are `2,4` in some order. -/
theorem equality_prefix_forces_star
    (u v : ℕ) (port : Fin 3)
    (hu : 0 < u) (hv : 0 < v)
    (hinternal : ({u, v, u + v} : Finset ℕ) = {2, 4, 6})
    (hbridge :
      (Finset.univ.image fun z : Fin 3 => pathThreeDepth u v port z + 1) =
        {1, 3, 5}) :
    ((u = 2 ∧ v = 4) ∨ (u = 4 ∧ v = 2)) ∧ port = 1 := by
  have hu_mem : u ∈ ({2, 4, 6} : Finset ℕ) := by
    rw [← hinternal]
    simp
  have hv_mem : v ∈ ({2, 4, 6} : Finset ℕ) := by
    rw [← hinternal]
    simp
  have huv_mem : u + v ∈ ({2, 4, 6} : Finset ℕ) := by
    rw [← hinternal]
    simp
  have hsix_mem : 6 ∈ ({u, v, u + v} : Finset ℕ) := by
    rw [hinternal]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu_mem hv_mem huv_mem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsix_mem
  have huv : (u = 2 ∧ v = 4) ∨ (u = 4 ∧ v = 2) := by
    rcases hu_mem with hu | hu | hu <;>
      rcases hv_mem with hv | hv | hv <;>
      simp_all
  have hbridge_mem (z : Fin 3) :
      pathThreeDepth u v port z + 1 ∈ ({1, 3, 5} : Finset ℕ) := by
    rw [← hbridge]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ z)
  have hport : port = 1 := by
    fin_cases port
    · have hz := hbridge_mem (2 : Fin 3)
      rcases huv with h | h <;> rcases h with ⟨rfl, rfl⟩ <;>
        simp [pathThreeDepth, Fin.ext_iff] at hz
    · rfl
    · have hz := hbridge_mem (0 : Fin 3)
      rcases huv with h | h <;> rcases h with ⟨rfl, rfl⟩ <;>
        simp [pathThreeDepth, Fin.ext_iff] at hz
  exact ⟨huv, hport⟩

/-- Mixed-radix indexed sums used in the hostile truncation control. -/
def mixedRadixSum (x : ℕ) {y : ℕ} : Fin x × Fin y → ℕ :=
  fun z => z.1.1 + x * z.2.1

theorem mixedRadixSum_injective {x y : ℕ} (hx : 0 < x) :
    Function.Injective (mixedRadixSum x (y := y)) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  have hi : (mixedRadixSum x (i, j)) % x = i := by
    simp [mixedRadixSum, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]
  have hi' : (mixedRadixSum x (i', j')) % x = i' := by
    simp [mixedRadixSum, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i'.isLt]
  have hieq : (i : ℕ) = (i' : ℕ) := by
    rw [← hi, ← hi', h]
  apply Prod.ext
  · exact Fin.ext hieq
  · apply Fin.ext
    have hmul : x * (j : ℕ) = x * (j' : ℕ) := by
      simpa [mixedRadixSum, hieq] using h
    exact Nat.eq_of_mul_eq_mul_left hx hmul

/-- For every `t <= x*y`, the direct mixed-radix rectangle covers the whole
prefix `0,...,t-1` with unique indexed sums.  Hence the truncated polynomial
identity alone has no cardinal consequence stronger than `x*y >= t`. -/
theorem mixedRadix_covers_truncated_prefix
    {x y t : ℕ} (hx : 0 < x) (hxy : t ≤ x * y) :
    Function.Injective (mixedRadixSum x (y := y)) ∧
      ∀ k < t, ∃! z : Fin x × Fin y, mixedRadixSum x z = k := by
  refine ⟨mixedRadixSum_injective hx, ?_⟩
  intro k hk
  have hkxy : k < x * y := hk.trans_le hxy
  let i : Fin x := ⟨k % x, Nat.mod_lt _ hx⟩
  let j : Fin y := ⟨k / x, by
    have : k / x < y := (Nat.div_lt_iff_lt_mul hx).2 (by
      simpa [Nat.mul_comm] using hkxy)
    exact this⟩
  refine ⟨(i, j), ?_, ?_⟩
  · simp [mixedRadixSum, i, j, Nat.mod_add_div]
  · intro z hz
    exact mixedRadixSum_injective hx (hz.trans (by
      simp [mixedRadixSum, i, j, Nat.mod_add_div]))

end LeechTrees.OddQuotient.Q2Bounds
