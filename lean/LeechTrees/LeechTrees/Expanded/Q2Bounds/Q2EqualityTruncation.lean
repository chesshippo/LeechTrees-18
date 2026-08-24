import LeechTrees.Expanded.Q2Bounds.Q2GraphProfiles
import LeechTrees.OddEdgesT11Adapter

/-!
# The r=15 equality spectra and the actual truncated unit factor
-/

open scoped BigOperators Polynomial

namespace LeechTrees.OddQuotient.Q2Bounds.EqualityTruncation

open LeechTrees.Foundation
open LeechTrees.OddQuotient.Q2Bounds.GraphProfiles

variable {n : ℕ}

theorem lowEvenWithinIndex_dist
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T)
    (i : Fin D.t) :
    T.pairDist (indexToPair T (.inl (lowEvenWithinIndex hL D i))) =
      2 * (i.1 + 1) := by
  have hrank := evenPairBlockEquiv_rank T (lowEvenPair hL D i)
  rw [lowEvenWithinIndex_spec hL D i] at hrank
  simp only [evenBlockRank] at hrank
  have hpair := pairDist_indexToPair_internal T
    (lowEvenWithinIndex hL D i)
  have hhalf := lowEvenPair_halfRank hL D i
  omega

theorem lowOddUnitRectanglePoint_dist
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T)
    (i : Fin D.t) :
    T.pairDist (unitRectanglePair D (lowOddUnitRectanglePoint hL D i)) =
      2 * i.1 + 1 := by
  rw [lowOddUnitRectanglePoint_spec hL D i]
  exact lowOddPair_dist hL D i

/-- At the `r=15,q₂=7` endpoint both low-rank injections saturate their
actual graph capacities.  In particular the forbidden middle split is
removed by the low-even injection rather than by an assumed profile row. -/
theorem order18_r15_q₂_seven_capacity_equalities
    {T : PosIntTree 18} (hL : IsLeech T) (root : Fin 18)
    (D : SecondOddBridgeData T)
    (hr : Fintype.card (OddBridge T) = 15)
    (hq : D.q₂ = 7) :
    D.t = 3 ∧ Fintype.card (WithinIndex T) = 3 ∧
      Fintype.card (UnitLeftComponentVertex D) *
        Fintype.card (UnitRightComponentVertex D) = 3 := by
  have ht : D.t = 3 := by rw [D.q₂_eq] at hq; omega
  let k := order18SmallComponentCount T root
  have hfeas := order18_component_profile_feasible hL root
  have hI := order18_withinIndex_profile_bound hL root
  have hxy := order18_unitRectangle_profile_bound hL root D
  have hIlow := lowEven_internal_capacity hL D
  have hxylow := lowOdd_unitRectangle_capacity hL D
  rw [hr] at hfeas hI hxy
  change FeasibleColorSplit 7 11 15 k at hfeas
  change Fintype.card (WithinIndex T) ≤
      Nat.choose (8 - k) 2 + Nat.choose (11 + k - 15) 2 at hI
  change Fintype.card (UnitLeftComponentVertex D) *
      Fintype.card (UnitRightComponentVertex D) ≤
        (8 - k) * (11 + k - 15) at hxy
  rcases hfeas with ⟨hk1, hk7, hl1, hl11⟩
  have hk_cases : k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases hk_cases with hk | hk | hk
  · rw [hk] at hI hxy
    norm_num at hI hxy
    have hI' : Fintype.card (WithinIndex T) ≤ 3 := by
      simpa only [Fintype.card_sigma] using hI
    exact ⟨ht, by omega, by omega⟩
  · rw [hk] at hI
    norm_num at hI
    have hI' : Fintype.card (WithinIndex T) ≤ 2 := by
      simpa only [Fintype.card_sigma] using hI
    omega
  · rw [hk] at hI hxy
    norm_num at hI hxy
    have hI' : Fintype.card (WithinIndex T) ≤ 3 := by
      simpa only [Fintype.card_sigma] using hI
    exact ⟨ht, by omega, by omega⟩

noncomputable def withinDistanceSet (T : PosIntTree n) : Finset ℕ :=
  Finset.univ.image fun z : WithinIndex T =>
    T.pairDist (indexToPair T (.inl z))

noncomputable def unitRectangleDistanceSet
    {T : PosIntTree n} (D : SecondOddBridgeData T) : Finset ℕ :=
  Finset.univ.image fun z :
      UnitLeftComponentVertex D × UnitRightComponentVertex D =>
    T.pairDist (unitRectanglePair D z)

private theorem embedding_surjective_of_card_eq
    {α β : Type*} [Fintype α] [Fintype β]
    (f : α ↪ β) (hcard : Fintype.card α = Fintype.card β) :
    Function.Surjective f := by
  by_contra hnot
  have hlt := Fintype.card_lt_of_injective_not_surjective f f.injective hnot
  omega

/-- The exact internal spectrum is now a consequence of graph saturation,
not a hypothesis of the local three-vertex calculation. -/
theorem order18_r15_q₂_seven_internal_spectrum
    {T : PosIntTree 18} (hL : IsLeech T) (root : Fin 18)
    (D : SecondOddBridgeData T)
    (hr : Fintype.card (OddBridge T) = 15)
    (hq : D.q₂ = 7) :
    withinDistanceSet T = {2, 4, 6} := by
  have hcap := order18_r15_q₂_seven_capacity_equalities hL root D hr hq
  have ht := hcap.1
  have hsurj : Function.Surjective (lowEvenWithinEmbedding hL D) := by
    apply embedding_surjective_of_card_eq
    simp [ht, hcap.2.1]
  ext d
  constructor
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨z, -, rfl⟩
    rcases hsurj z with ⟨i, rfl⟩
    change T.pairDist
      (indexToPair T (.inl (lowEvenWithinIndex hL D i))) ∈ {2, 4, 6}
    rw [lowEvenWithinIndex_dist hL D i]
    have hi : i.1 < 3 := by simpa [ht] using i.2
    interval_cases i.1 <;> simp
  · intro hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · let i : Fin D.t := ⟨0, by omega⟩
      rw [withinDistanceSet, Finset.mem_image]
      exact ⟨lowEvenWithinIndex hL D i, Finset.mem_univ _, by
        simpa [i] using lowEvenWithinIndex_dist hL D i⟩
    · let i : Fin D.t := ⟨1, by omega⟩
      rw [withinDistanceSet, Finset.mem_image]
      exact ⟨lowEvenWithinIndex hL D i, Finset.mem_univ _, by
        simpa [i] using lowEvenWithinIndex_dist hL D i⟩
    · let i : Fin D.t := ⟨2, by omega⟩
      rw [withinDistanceSet, Finset.mem_image]
      exact ⟨lowEvenWithinIndex hL D i, Finset.mem_univ _, by
        simpa [i] using lowEvenWithinIndex_dist hL D i⟩

/-- The exact weight-one-bridge spectrum is likewise graph-derived. -/
theorem order18_r15_q₂_seven_unit_spectrum
    {T : PosIntTree 18} (hL : IsLeech T) (root : Fin 18)
    (D : SecondOddBridgeData T)
    (hr : Fintype.card (OddBridge T) = 15)
    (hq : D.q₂ = 7) :
    unitRectangleDistanceSet D = {1, 3, 5} := by
  have hcap := order18_r15_q₂_seven_capacity_equalities hL root D hr hq
  have ht := hcap.1
  have hcard : Fintype.card
      (UnitLeftComponentVertex D × UnitRightComponentVertex D) = 3 := by
    simpa [Fintype.card_prod] using hcap.2.2
  have hsurj : Function.Surjective (lowOddUnitRectangleEmbedding hL D) := by
    apply embedding_surjective_of_card_eq
    simp [ht, hcard]
  ext d
  constructor
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨z, -, rfl⟩
    rcases hsurj z with ⟨i, rfl⟩
    change T.pairDist
      (unitRectanglePair D (lowOddUnitRectanglePoint hL D i)) ∈ {1, 3, 5}
    rw [lowOddUnitRectanglePoint_dist hL D i]
    have hi : i.1 < 3 := by simpa [ht] using i.2
    interval_cases i.1 <;> simp
  · intro hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · let i : Fin D.t := ⟨0, by omega⟩
      rw [unitRectangleDistanceSet, Finset.mem_image]
      exact ⟨lowOddUnitRectanglePoint hL D i, Finset.mem_univ _, by
        simpa [i] using lowOddUnitRectanglePoint_dist hL D i⟩
    · let i : Fin D.t := ⟨1, by omega⟩
      rw [unitRectangleDistanceSet, Finset.mem_image]
      exact ⟨lowOddUnitRectanglePoint hL D i, Finset.mem_univ _, by
        simpa [i] using lowOddUnitRectanglePoint_dist hL D i⟩
    · let i : Fin D.t := ⟨2, by omega⟩
      rw [unitRectangleDistanceSet, Finset.mem_image]
      exact ⟨lowOddUnitRectanglePoint hL D i, Finset.mem_univ _, by
        simpa [i] using lowOddUnitRectanglePoint_dist hL D i⟩

/-! ## The actual saturated three-vertex component -/

/-- The unordered pair underlying `VertexPair.ofDistinct` is the pair with
which it was constructed.  Keeping this small lemma public makes later
distance-injectivity arguments independent of the ambient name order. -/
theorem pairOfDistinct_sym2 {u v : Fin n} (huv : u ≠ v) :
    s((VertexPair.ofDistinct u v huv).left,
      (VertexPair.ofDistinct u v huv).right) = s(u, v) := by
  by_cases h : u < v
  · simp [VertexPair.ofDistinct, h, VertexPair.left, VertexPair.right]
  · simp [VertexPair.ofDistinct, h, VertexPair.left, VertexPair.right,
      Sym2.eq_swap]

/-- Global Leech injectivity separates the distances carried by two
different unordered named-vertex pairs. -/
theorem dist_ne_of_sym2_ne
    {T : PosIntTree n} (hL : IsLeech T)
    {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (hpairs : s(a, b) ≠ s(c, d)) :
    T.dist a b ≠ T.dist c d := by
  intro hdist
  let p := VertexPair.ofDistinct a b hab
  let q := VertexPair.ofDistinct c d hcd
  have hpq : p = q := hL.pairDist_injective <| by
    simpa [p, q, T.pairDist_pairOfDistinct] using hdist
  apply hpairs
  calc
    s(a, b) = s(p.left, p.right) := (pairOfDistinct_sym2 hab).symm
    _ = s(q.left, q.right) := congrArg (fun z : VertexPair n => s(z.left, z.right)) hpq
    _ = s(c, d) := pairOfDistinct_sym2 hcd

/-- An internal pair made from two component vertices, independently of the
ambient order on their names. -/
noncomputable def componentInternalPair
    {T : PosIntTree n} {C : EvenComponent T}
    (x y : ComponentVertex T C) (hxy : x ≠ y) : InternalPair T C := by
  by_cases h : x.1 < y.1
  · exact ⟨(x, y), h⟩
  · exact ⟨(y, x), lt_of_le_of_ne (le_of_not_gt h)
      (fun hyx => hxy (Subtype.ext hyx.symm))⟩

theorem componentInternalPair_dist
    {T : PosIntTree n} {C : EvenComponent T}
    (x y : ComponentVertex T C) (hxy : x ≠ y) :
    T.pairDist
        (indexToPair T (.inl
          (⟨C, componentInternalPair x y hxy⟩ : WithinIndex T))) =
      T.dist x.1 y.1 := by
  unfold componentInternalPair
  split_ifs with h
  · change T.dist x.1 y.1 = T.dist x.1 y.1
    rfl
  · change T.dist y.1 x.1 = T.dist x.1 y.1
    exact T.dist_comm y.1 x.1

theorem component_distance_mem_withinDistanceSet
    {T : PosIntTree n} {C : EvenComponent T}
    (x y : ComponentVertex T C) (hxy : x ≠ y) :
    T.dist x.1 y.1 ∈ withinDistanceSet T := by
  rw [withinDistanceSet, Finset.mem_image]
  refine ⟨⟨C, componentInternalPair x y hxy⟩, Finset.mem_univ _, ?_⟩
  exact componentInternalPair_dist x y hxy

/-- Exact cross-distance formula for the actual unit-component rectangle. -/
theorem unitRectanglePair_dist_eq
    {T : PosIntTree n} (D : SecondOddBridgeData T)
    (z : UnitLeftComponentVertex D × UnitRightComponentVertex D) :
    T.pairDist (unitRectanglePair D z) =
      T.dist z.1.1 (T.edgeLeft D.unit.1) + 1 +
        T.dist (T.edgeRight D.unit.1) z.2.1 := by
  have hleftAvoid : D.unit.1.1 ∉
      T.pathEdges z.1.1 (T.edgeLeft D.unit.1) := by
    intro hmem
    have heven := path_edge_even_of_component_eq T z.1.2 hmem
    have : Even (T.weight D.unit.1) := by simpa using heven
    exact (Nat.not_odd_iff_even.mpr this) D.unit.2
  have hrightAvoid : D.unit.1.1 ∉
      T.pathEdges z.2.1 (T.edgeRight D.unit.1) := by
    intro hmem
    have heven := path_edge_even_of_component_eq T z.2.2 hmem
    have : Even (T.weight D.unit.1) := by simpa using heven
    exact (Nat.not_odd_iff_even.mpr this) D.unit.2
  have hleft := (T.cut_reachable_iff_not_mem_pathEdges D.unit.1 _ _).2
    hleftAvoid
  have hright := (T.cut_reachable_iff_not_mem_pathEdges D.unit.1 _ _).2
    hrightAvoid
  have hroute := T.cross_distance_decomposition D.unit.1 hleft hright
  rw [unitRectanglePair, T.pairDist_pairOfDistinct]
  rw [D.unit_weight] at hroute
  exact hroute

/-- Concrete graph witness for the equality row.  The component has exactly
three actual named vertices.  The unit bridge port is the metric middle:
the two incident even arms have raw weights `2` and `4` (in either order),
and the two outer vertices are at distance `6`.  In a positive weighted tree
on exactly these three component vertices this is precisely the weighted
three-vertex path, so the statement does not hide a topology assumption. -/
structure Order18EqualityStarWitness
    (T : PosIntTree 18) (D : SecondOddBridgeData T) where
  component : EvenComponent T
  port : Fin 18
  endpointA : Fin 18
  endpointB : Fin 18
  component_card : Fintype.card (ComponentVertex T component) = 3
  other_components_singleton : ∀ C' : EvenComponent T, C' ≠ component →
    Fintype.card (ComponentVertex T C') = 1
  port_mem : componentOf T port = component
  endpointA_mem : componentOf T endpointA = component
  endpointB_mem : componentOf T endpointB = component
  pairwise_ne : port ≠ endpointA ∧ port ≠ endpointB ∧ endpointA ≠ endpointB
  /-- These are actual adjacencies in the original tree, not merely metric
  distances in the deleted-odd-edge component. -/
  arm_adjacent : T.graph.Adj port endpointA ∧ T.graph.Adj port endpointB
  port_is_unit_endpoint :
    port = T.edgeLeft D.unit.1 ∨ port = T.edgeRight D.unit.1
  opposite_component_singleton :
    (port = T.edgeLeft D.unit.1 ∧
        Fintype.card (UnitRightComponentVertex D) = 1) ∨
      (port = T.edgeRight D.unit.1 ∧
        Fintype.card (UnitLeftComponentVertex D) = 1)
  arm_weights :
    (T.dist port endpointA = 2 ∧ T.dist port endpointB = 4) ∨
      (T.dist port endpointA = 4 ∧ T.dist port endpointB = 2)
  /-- Because `arm_adjacent` holds, these are the two actual physical even
  edge weights. -/
  physical_arm_weights :
    (T.weightOfPair s(port, endpointA) = 2 ∧
        T.weightOfPair s(port, endpointB) = 4) ∨
      (T.weightOfPair s(port, endpointA) = 4 ∧
        T.weightOfPair s(port, endpointB) = 2)
  outer_distance : T.dist endpointA endpointB = 6

private theorem componentVertex_eq_three
    {T : PosIntTree n} {C : EvenComponent T}
    (hcard : Fintype.card (ComponentVertex T C) = 3)
    (p a b x : ComponentVertex T C)
    (hpa : p ≠ a) (hpb : p ≠ b) (hab : a ≠ b) :
    x = p ∨ x = a ∨ x = b := by
  classical
  have htriple :
      ({p, a, b} : Finset (ComponentVertex T C)).card = 3 := by
    simp [hpa, hpb, hab]
  have hall : ({p, a, b} : Finset (ComponentVertex T C)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [htriple]
    simpa using hcard.symm
  have hx : x ∈ ({p, a, b} : Finset (ComponentVertex T C)) := by
    rw [hall]
    exact Finset.mem_univ x
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hx

private theorem other_components_singleton_of_within_card_three
    {T : PosIntTree n}
    (hwithin : Fintype.card (WithinIndex T) = 3)
    {C : EvenComponent T}
    (hC : Fintype.card (ComponentVertex T C) = 3) :
    ∀ C' : EvenComponent T, C' ≠ C →
      Fintype.card (ComponentVertex T C') = 1 := by
  classical
  intro C' hne
  have hsum :
      (∑ K : EvenComponent T,
        Nat.choose (Fintype.card (ComponentVertex T K)) 2) = 3 := by
    rw [← card_withinIndex T]
    exact hwithin
  have hsplit :
      (∑ K : EvenComponent T,
          Nat.choose (Fintype.card (ComponentVertex T K)) 2) =
        Nat.choose (Fintype.card (ComponentVertex T C)) 2 +
          ∑ K ∈ Finset.univ.erase C,
            Nat.choose (Fintype.card (ComponentVertex T K)) 2 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ C), Nat.add_comm]
  have hrest :
      (∑ K ∈ Finset.univ.erase C,
        Nat.choose (Fintype.card (ComponentVertex T K)) 2) = 0 := by
    rw [hC] at hsplit
    norm_num at hsplit
    omega
  have hmem : C' ∈ Finset.univ.erase C := by simp [hne]
  have hle :
      Nat.choose (Fintype.card (ComponentVertex T C')) 2 ≤
        ∑ K ∈ Finset.univ.erase C,
          Nat.choose (Fintype.card (ComponentVertex T K)) 2 :=
    Finset.single_le_sum
      (s := Finset.univ.erase C)
      (f := fun K : EvenComponent T =>
        Nat.choose (Fintype.card (ComponentVertex T K)) 2)
      (fun _ _ => Nat.zero_le _) hmem
  have hchoose :
      Nat.choose (Fintype.card (ComponentVertex T C')) 2 = 0 := by
    rw [hrest] at hle
    omega
  let m := Fintype.card (ComponentVertex T C')
  have hmpos : 0 < m := by
    simpa [m] using componentVertex_card_pos T C'
  have hquot : m * (m - 1) / 2 = 0 := by
    simpa [m, Nat.choose_two_right] using hchoose
  have hprodlt : m * (m - 1) < 2 := by omega
  have hmle : m ≤ 1 := by
    by_contra hnot
    have hm2 : 2 ≤ m := by omega
    have hpred : 1 ≤ m - 1 := by omega
    have hprod2 : 2 ≤ m * (m - 1) := by
      simpa using Nat.mul_le_mul hm2 hpred
    omega
  omega

private theorem dist_eq_weightOfPair_of_adj
    {T : PosIntTree n} {u v : Fin n} (huv : T.graph.Adj u v) :
    T.dist u v = T.weightOfPair s(u, v) := by
  let p : T.graph.Path u v := SimpleGraph.Path.singleton huv
  calc
    T.dist u v = T.walkWeight p.1 :=
      (T.path_walkWeight_eq_dist p).symm
    _ = T.weightOfPair s(u, v) := by
      simp [p, SimpleGraph.Path.singleton, PosIntTree.walkWeight]

/-- In a three-vertex even component, the strict metric triangle at `b`
forces the `p`--`a` route to be one physical edge.  If it were not, its
first intermediate vertex would have to be the only third component vertex
`b`, contradicting strictness after splitting the actual path there. -/
private theorem adjacent_of_three_component_strict
    {T : PosIntTree n} {C : EvenComponent T}
    (hL : IsLeech T)
    (hcard : Fintype.card (ComponentVertex T C) = 3)
    (p a b : ComponentVertex T C)
    (hpa : p ≠ a) (hpb : p ≠ b) (hab : a ≠ b)
    (hstrict : T.dist p.1 a.1 < T.dist p.1 b.1 + T.dist b.1 a.1) :
    T.graph.Adj p.1 a.1 := by
  classical
  by_contra hnotAdj
  let P := T.path p.1 a.1
  have hpaval : p.1 ≠ a.1 := fun h => hpa (Subtype.ext h)
  have hdistPos : 0 < T.dist p.1 a.1 := by
    rw [← T.pairDist_pairOfDistinct p.1 a.1 hpaval]
    exact hL.pairDist_pos _
  have hpathNonempty : (T.pathEdges p.1 a.1).Nonempty :=
    T.pathEdges_nonempty_of_dist_pos hdistPos
  have hedgesNonempty : P.1.edges ≠ [] := by
    intro hempty
    have : T.pathEdges p.1 a.1 = ∅ := by
      unfold PosIntTree.pathEdges
      change P.1.edges.toFinset = ∅
      rw [hempty]
      rfl
    exact Finset.not_nonempty_iff_eq_empty.mpr this hpathNonempty
  have hlen : 0 < P.1.length := by
    rw [← P.1.length_edges]
    exact List.length_pos_iff.mpr hedgesNonempty
  have hpnon : ¬P.1.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    exact hlen
  let w := P.1.snd
  have hpw : T.graph.Adj p.1 w := P.1.adj_snd hpnon
  have hcons := P.1.cons_tail_eq hpnon
  have hfirstList : s(p.1, w) ∈ P.1.edges := by
    rw [← hcons]
    simp [w]
  have hfirst : s(p.1, w) ∈ T.pathEdges p.1 a.1 := by
    simpa [P, PosIntTree.pathEdges] using hfirstList
  have hcompPA : componentOf T p.1 = componentOf T a.1 :=
    p.2.trans a.2.symm
  have heven : Even (T.weightOfPair s(p.1, w)) :=
    path_edge_even_of_component_eq T hcompPA hfirst
  have hpwEven : (evenForest T).Adj p.1 w :=
    (evenForest_adj_iff T).2 ⟨hpw, heven⟩
  have hcompPW : componentOf T p.1 = componentOf T w :=
    (componentOf_eq_iff T p.1 w).2
      (SimpleGraph.Adj.reachable hpwEven)
  let wc : ComponentVertex T C := ⟨w, hcompPW.symm.trans p.2⟩
  have hw_ne_p : wc ≠ p := by
    intro h
    exact hpw.ne (congrArg Subtype.val h).symm
  have hw_ne_a : wc ≠ a := by
    intro h
    apply hnotAdj
    have hwa : w = a.1 := congrArg Subtype.val h
    simpa [hwa] using hpw
  have hw_eq_b : wc = b := by
    rcases componentVertex_eq_three hcard p a b wc hpa hpb hab with
      h | h | h
    · exact (hw_ne_p h).elim
    · exact (hw_ne_a h).elim
    · exact h
  have hwSupport : w ∈ P.1.support := by
    rw [← hcons]
    simp [w]
  have hsplit :=
    LeechTrees.OddEdges.T11Adapter.PosIntTree.dist_split_at_path_vertex
      T hwSupport
  have hwb : w = b.1 := congrArg Subtype.val hw_eq_b
  rw [hwb] at hsplit
  omega

private noncomputable def finThreeEquivOfCard
    (α : Type*) [Fintype α] (hcard : Fintype.card α = 3) :
    Fin 3 ≃ α :=
  (finCongr hcard.symm).trans (Fintype.equivFin α).symm

private theorem three_vertices_around
    {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α = 3) (p : α) :
    ∃ a b : α, p ≠ a ∧ p ≠ b ∧ a ≠ b := by
  let e : Fin 3 ≃ α := finThreeEquivOfCard α hcard
  by_cases h0 : p = e 0
  · refine ⟨e 1, e 2, ?_, ?_, ?_⟩
    · intro h
      have : (0 : Fin 3) = 1 := e.injective (h0.symm.trans h)
      exact (by decide : (0 : Fin 3) ≠ 1) this
    · intro h
      have : (0 : Fin 3) = 2 := e.injective (h0.symm.trans h)
      exact (by decide : (0 : Fin 3) ≠ 2) this
    · intro h
      have : (1 : Fin 3) = 2 := e.injective h
      exact (by decide : (1 : Fin 3) ≠ 2) this
  · by_cases h1 : p = e 1
    · refine ⟨e 0, e 2, ?_, ?_, ?_⟩
      · exact h0
      · intro h
        have : (1 : Fin 3) = 2 := e.injective (h1.symm.trans h)
        exact (by decide : (1 : Fin 3) ≠ 2) this
      · intro h
        have : (0 : Fin 3) = 2 := e.injective h
        exact (by decide : (0 : Fin 3) ≠ 2) this
    · have h2 : p = e 2 := by
        obtain ⟨i, rfl⟩ := e.surjective p
        fin_cases i
        · exact (h0 rfl).elim
        · exact (h1 rfl).elim
        · rfl
      refine ⟨e 0, e 1, ?_, ?_, ?_⟩
      · exact h0
      · exact h1
      · intro h
        have : (0 : Fin 3) = 1 := e.injective h
        exact (by decide : (0 : Fin 3) ≠ 1) this

private theorem positive_dist_of_ne
    {T : PosIntTree n} (hL : IsLeech T) {u v : Fin n} (huv : u ≠ v) :
    0 < T.dist u v := by
  rw [← T.pairDist_pairOfDistinct u v huv]
  exact hL.pairDist_pos _

private theorem unit_left_depth_is_two_or_four
    {T : PosIntTree 18} (hL : IsLeech T) (D : SecondOddBridgeData T)
    (hspectrum : unitRectangleDistanceSet D = {1, 3, 5})
    (x : UnitLeftComponentVertex D)
    (hx : x.1 ≠ T.edgeLeft D.unit.1) :
    T.dist (T.edgeLeft D.unit.1) x.1 = 2 ∨
      T.dist (T.edgeLeft D.unit.1) x.1 = 4 := by
  let y₀ : UnitRightComponentVertex D :=
    ⟨T.edgeRight D.unit.1, rfl⟩
  let z : UnitLeftComponentVertex D × UnitRightComponentVertex D := (x, y₀)
  have hmem : T.pairDist (unitRectanglePair D z) ∈
      ({1, 3, 5} : Finset ℕ) := by
    rw [← hspectrum, unitRectangleDistanceSet, Finset.mem_image]
    exact ⟨z, Finset.mem_univ _, rfl⟩
  have hformula := unitRectanglePair_dist_eq D z
  dsimp only [z, y₀, Prod.fst, Prod.snd] at hformula
  have hzero : T.dist (T.edgeRight D.unit.1) y₀.1 = 0 :=
    T.dist_self _
  rw [T.dist_comm x.1 (T.edgeLeft D.unit.1), hzero] at hformula
  rw [hformula] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hpos : 0 < T.dist (T.edgeLeft D.unit.1) x.1 :=
    positive_dist_of_ne hL hx.symm
  omega

private theorem unit_right_depth_is_two_or_four
    {T : PosIntTree 18} (hL : IsLeech T) (D : SecondOddBridgeData T)
    (hspectrum : unitRectangleDistanceSet D = {1, 3, 5})
    (x : UnitRightComponentVertex D)
    (hx : x.1 ≠ T.edgeRight D.unit.1) :
    T.dist (T.edgeRight D.unit.1) x.1 = 2 ∨
      T.dist (T.edgeRight D.unit.1) x.1 = 4 := by
  let x₀ : UnitLeftComponentVertex D :=
    ⟨T.edgeLeft D.unit.1, rfl⟩
  let z : UnitLeftComponentVertex D × UnitRightComponentVertex D := (x₀, x)
  have hmem : T.pairDist (unitRectanglePair D z) ∈
      ({1, 3, 5} : Finset ℕ) := by
    rw [← hspectrum, unitRectangleDistanceSet, Finset.mem_image]
    exact ⟨z, Finset.mem_univ _, rfl⟩
  have hformula := unitRectanglePair_dist_eq D z
  dsimp only [z, x₀, Prod.fst, Prod.snd] at hformula
  have hzero : T.dist x₀.1 (T.edgeLeft D.unit.1) = 0 :=
    T.dist_self _
  rw [hzero] at hformula
  rw [hformula] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hpos : 0 < T.dist (T.edgeRight D.unit.1) x.1 :=
    positive_dist_of_ne hL hx.symm
  omega

/-- Public graph-level equality endpoint.  It consumes only `IsLeech`, the
actual odd quotient count, and the actual canonical second odd bridge. -/
theorem order18_r15_q₂_seven_actual_star
    {T : PosIntTree 18} (hL : IsLeech T) (root : Fin 18)
    (D : SecondOddBridgeData T)
    (hr : Fintype.card (OddBridge T) = 15)
    (hq : D.q₂ = 7) :
    Nonempty (Order18EqualityStarWitness T D) := by
  classical
  have hcap := order18_r15_q₂_seven_capacity_equalities hL root D hr hq
  have hinter := order18_r15_q₂_seven_internal_spectrum hL root D hr hq
  have hunit := order18_r15_q₂_seven_unit_spectrum hL root D hr hq
  have hleftPos := componentVertex_card_pos T
    (componentOf T (T.edgeLeft D.unit.1))
  have hrightPos := componentVertex_card_pos T
    (componentOf T (T.edgeRight D.unit.1))
  have hsizes :
      (Fintype.card (UnitLeftComponentVertex D) = 3 ∧
        Fintype.card (UnitRightComponentVertex D) = 1) ∨
      (Fintype.card (UnitLeftComponentVertex D) = 1 ∧
        Fintype.card (UnitRightComponentVertex D) = 3) := by
    have hprod := hcap.2.2
    let x := Fintype.card (UnitLeftComponentVertex D)
    let y := Fintype.card (UnitRightComponentVertex D)
    have hxpos : 0 < x := by
      simpa [x, UnitLeftComponentVertex] using hleftPos
    have hypos : 0 < y := by
      simpa [y, UnitRightComponentVertex] using hrightPos
    have hxy : x * y = 3 := by simpa [x, y] using hprod
    have hxle : x ≤ 3 := by
      exact Nat.le_of_dvd (by norm_num) ⟨y, hxy.symm⟩
    have hyle : y ≤ 3 := by
      exact Nat.le_of_dvd (by norm_num) ⟨x, by simpa [Nat.mul_comm] using hxy.symm⟩
    have hcases : (x = 3 ∧ y = 1) ∨ (x = 1 ∧ y = 3) := by
      interval_cases x <;> interval_cases y <;> norm_num at hxy
      all_goals simp_all
    simpa [x, y] using hcases
  rcases hsizes with hleft | hright
  · let C := componentOf T (T.edgeLeft D.unit.1)
    let p : ComponentVertex T C := ⟨T.edgeLeft D.unit.1, rfl⟩
    obtain ⟨a, b, hpa, hpb, hab⟩ := three_vertices_around hleft.1 p
    have hda := unit_left_depth_is_two_or_four hL D hunit a
      (fun h => hpa (Subtype.ext h.symm))
    have hdb := unit_left_depth_is_two_or_four hL D hunit b
      (fun h => hpb (Subtype.ext h.symm))
    have hdab_mem : T.dist a.1 b.1 ∈ ({2, 4, 6} : Finset ℕ) := by
      rw [← hinter]
      exact component_distance_mem_withinDistanceSet a b hab
    have hdpa_ne_hdpp : T.dist p.1 a.1 ≠ T.dist p.1 b.1 := by
      apply dist_ne_of_sym2_ne hL
        (fun h => hpa (Subtype.ext h))
        (fun h => hpb (Subtype.ext h))
      intro hsym
      rcases Sym2.eq_iff.mp hsym with ⟨_, h⟩ | ⟨_, h⟩
      · exact hab (Subtype.ext h)
      · exact hpa (Subtype.ext h.symm)
    have hdab_ne_a : T.dist a.1 b.1 ≠ T.dist p.1 a.1 := by
      apply dist_ne_of_sym2_ne hL
        (fun h => hab (Subtype.ext h))
        (fun h => hpa (Subtype.ext h))
      intro hsym
      rcases Sym2.eq_iff.mp hsym with ⟨h, _⟩ | ⟨_, h⟩
      · exact hpa (Subtype.ext h.symm)
      · exact hpb (Subtype.ext h.symm)
    have hdab_ne_b : T.dist a.1 b.1 ≠ T.dist p.1 b.1 := by
      apply dist_ne_of_sym2_ne hL
        (fun h => hab (Subtype.ext h))
        (fun h => hpb (Subtype.ext h))
      intro hsym
      rcases Sym2.eq_iff.mp hsym with ⟨h, _⟩ | ⟨_, h⟩
      · exact hpa (Subtype.ext h.symm)
      · exact hpb (Subtype.ext h.symm)
    have harms :
        (T.dist p.1 a.1 = 2 ∧ T.dist p.1 b.1 = 4) ∨
        (T.dist p.1 a.1 = 4 ∧ T.dist p.1 b.1 = 2) := by
      rcases hda with hda | hda
      · rcases hdb with hdb | hdb
        · exact (hdpa_ne_hdpp (hda.trans hdb.symm)).elim
        · exact Or.inl ⟨hda, hdb⟩
      · rcases hdb with hdb | hdb
        · exact Or.inr ⟨hda, hdb⟩
        · exact (hdpa_ne_hdpp (hda.trans hdb.symm)).elim
    have hdab : T.dist a.1 b.1 = 6 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hdab_mem
      rcases harms with h | h <;> omega
    have hadjA : T.graph.Adj p.1 a.1 := by
      apply adjacent_of_three_component_strict hL hleft.1 p a b hpa hpb hab
      rw [T.dist_comm b.1 a.1]
      rcases harms with h | h <;> omega
    have hadjB : T.graph.Adj p.1 b.1 := by
      apply adjacent_of_three_component_strict hL hleft.1 p b a hpb hpa hab.symm
      rcases harms with h | h <;> omega
    have hphysical :
        (T.weightOfPair s(p.1, a.1) = 2 ∧
            T.weightOfPair s(p.1, b.1) = 4) ∨
          (T.weightOfPair s(p.1, a.1) = 4 ∧
            T.weightOfPair s(p.1, b.1) = 2) := by
      have hwa := dist_eq_weightOfPair_of_adj hadjA
      have hwb := dist_eq_weightOfPair_of_adj hadjB
      rcases harms with h | h
      · exact Or.inl ⟨hwa.symm.trans h.1, hwb.symm.trans h.2⟩
      · exact Or.inr ⟨hwa.symm.trans h.1, hwb.symm.trans h.2⟩
    exact ⟨{
      component := C
      port := p.1
      endpointA := a.1
      endpointB := b.1
      component_card := hleft.1
      other_components_singleton :=
        other_components_singleton_of_within_card_three hcap.2.1 hleft.1
      port_mem := p.2
      endpointA_mem := a.2
      endpointB_mem := b.2
      pairwise_ne := ⟨fun h => hpa (Subtype.ext h),
        fun h => hpb (Subtype.ext h), fun h => hab (Subtype.ext h)⟩
      arm_adjacent := ⟨hadjA, hadjB⟩
      port_is_unit_endpoint := Or.inl rfl
      opposite_component_singleton := Or.inl ⟨rfl, hleft.2⟩
      arm_weights := harms
      physical_arm_weights := hphysical
      outer_distance := hdab }⟩
  · let C := componentOf T (T.edgeRight D.unit.1)
    let p : ComponentVertex T C := ⟨T.edgeRight D.unit.1, rfl⟩
    obtain ⟨a, b, hpa, hpb, hab⟩ := three_vertices_around hright.2 p
    have hda := unit_right_depth_is_two_or_four hL D hunit a
      (fun h => hpa (Subtype.ext h.symm))
    have hdb := unit_right_depth_is_two_or_four hL D hunit b
      (fun h => hpb (Subtype.ext h.symm))
    have hdab_mem : T.dist a.1 b.1 ∈ ({2, 4, 6} : Finset ℕ) := by
      rw [← hinter]
      exact component_distance_mem_withinDistanceSet a b hab
    have hdpa_ne_hdpp : T.dist p.1 a.1 ≠ T.dist p.1 b.1 := by
      apply dist_ne_of_sym2_ne hL
        (fun h => hpa (Subtype.ext h))
        (fun h => hpb (Subtype.ext h))
      intro hsym
      rcases Sym2.eq_iff.mp hsym with ⟨_, h⟩ | ⟨_, h⟩
      · exact hab (Subtype.ext h)
      · exact hpa (Subtype.ext h.symm)
    have hdab_ne_a : T.dist a.1 b.1 ≠ T.dist p.1 a.1 := by
      apply dist_ne_of_sym2_ne hL
        (fun h => hab (Subtype.ext h))
        (fun h => hpa (Subtype.ext h))
      intro hsym
      rcases Sym2.eq_iff.mp hsym with ⟨h, _⟩ | ⟨_, h⟩
      · exact hpa (Subtype.ext h.symm)
      · exact hpb (Subtype.ext h.symm)
    have hdab_ne_b : T.dist a.1 b.1 ≠ T.dist p.1 b.1 := by
      apply dist_ne_of_sym2_ne hL
        (fun h => hab (Subtype.ext h))
        (fun h => hpb (Subtype.ext h))
      intro hsym
      rcases Sym2.eq_iff.mp hsym with ⟨h, _⟩ | ⟨_, h⟩
      · exact hpa (Subtype.ext h.symm)
      · exact hpb (Subtype.ext h.symm)
    have harms :
        (T.dist p.1 a.1 = 2 ∧ T.dist p.1 b.1 = 4) ∨
        (T.dist p.1 a.1 = 4 ∧ T.dist p.1 b.1 = 2) := by
      rcases hda with hda | hda
      · rcases hdb with hdb | hdb
        · exact (hdpa_ne_hdpp (hda.trans hdb.symm)).elim
        · exact Or.inl ⟨hda, hdb⟩
      · rcases hdb with hdb | hdb
        · exact Or.inr ⟨hda, hdb⟩
        · exact (hdpa_ne_hdpp (hda.trans hdb.symm)).elim
    have hdab : T.dist a.1 b.1 = 6 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hdab_mem
      rcases harms with h | h <;> omega
    have hadjA : T.graph.Adj p.1 a.1 := by
      apply adjacent_of_three_component_strict hL hright.2 p a b hpa hpb hab
      rw [T.dist_comm b.1 a.1]
      rcases harms with h | h <;> omega
    have hadjB : T.graph.Adj p.1 b.1 := by
      apply adjacent_of_three_component_strict hL hright.2 p b a hpb hpa hab.symm
      rcases harms with h | h <;> omega
    have hphysical :
        (T.weightOfPair s(p.1, a.1) = 2 ∧
            T.weightOfPair s(p.1, b.1) = 4) ∨
          (T.weightOfPair s(p.1, a.1) = 4 ∧
            T.weightOfPair s(p.1, b.1) = 2) := by
      have hwa := dist_eq_weightOfPair_of_adj hadjA
      have hwb := dist_eq_weightOfPair_of_adj hadjB
      rcases harms with h | h
      · exact Or.inl ⟨hwa.symm.trans h.1, hwb.symm.trans h.2⟩
      · exact Or.inr ⟨hwa.symm.trans h.1, hwb.symm.trans h.2⟩
    exact ⟨{
      component := C
      port := p.1
      endpointA := a.1
      endpointB := b.1
      component_card := hright.2
      other_components_singleton :=
        other_components_singleton_of_within_card_three hcap.2.1 hright.2
      port_mem := p.2
      endpointA_mem := a.2
      endpointB_mem := b.2
      pairwise_ne := ⟨fun h => hpa (Subtype.ext h),
        fun h => hpb (Subtype.ext h), fun h => hab (Subtype.ext h)⟩
      arm_adjacent := ⟨hadjA, hadjB⟩
      port_is_unit_endpoint := Or.inr rfl
      opposite_component_singleton := Or.inr ⟨rfl, hright.1⟩
      arm_weights := harms
      physical_arm_weights := hphysical
      outer_distance := hdab }⟩

/-- Canonical equality-row endpoint: the threshold is the attained actual
second odd physical weight selected from the graph, rather than an arbitrary
lower-bound datum. -/
theorem order18_r15_actual_secondOddWeight_seven_star
    {T : PosIntTree 18} (hL : IsLeech T) (root : Fin 18)
    (h₂ : HasNonunitOddBridge T)
    (hr : Fintype.card (OddBridge T) = 15)
    (hq : secondOddWeight h₂ = 7) :
    Nonempty
      (Order18EqualityStarWitness T
        (canonicalSecondOddBridgeData hL (by decide) h₂)) := by
  apply order18_r15_q₂_seven_actual_star hL root
    (canonicalSecondOddBridgeData hL (by decide) h₂) hr
  simpa only [canonicalSecondOddBridgeData_q₂] using hq

/-! ## Literal polynomial congruence modulo X^t -/

theorem unitRectanglePair_injective
    {T : PosIntTree n} (D : SecondOddBridgeData T) :
    Function.Injective (unitRectanglePair D) := by
  intro x y hxy
  have hs := congrArg
    (fun p : VertexPair n => s(p.left, p.right)) hxy
  have hs' : s(x.1.1, x.2.1) = s(y.1.1, y.2.1) := by
    simpa only [unitRectanglePair, pairOfDistinct_sym2] using hs
  rcases Sym2.eq_iff.mp hs' with h | h
  · rcases h with ⟨hl, hr⟩
    apply Prod.ext <;> apply Subtype.ext
    · exact hl
    · exact hr
  · rcases h with ⟨hl, hr⟩
    exfalso
    apply oddBridge_components_ne T D.unit
    calc
      componentOf T (T.edgeLeft D.unit.1) = componentOf T x.1.1 := x.1.2.symm
      _ = componentOf T y.2.1 := congrArg (componentOf T) hl
      _ = componentOf T (T.edgeRight D.unit.1) := y.2.2

theorem unitRectanglePair_dist_odd
    {T : PosIntTree n} (D : SecondOddBridgeData T)
    (z : UnitLeftComponentVertex D × UnitRightComponentVertex D) :
    Odd (T.pairDist (unitRectanglePair D z)) := by
  have hleftEven : Even (T.dist z.1.1 (T.edgeLeft D.unit.1)) :=
    dist_even_of_component_eq T z.1.2
  have hrightEven : Even (T.dist z.2.1 (T.edgeRight D.unit.1)) :=
    dist_even_of_component_eq T z.2.2
  have hleftAvoid : D.unit.1.1 ∉
      T.pathEdges z.1.1 (T.edgeLeft D.unit.1) := by
    intro hmem
    have heven := path_edge_even_of_component_eq T z.1.2 hmem
    have : Even (T.weight D.unit.1) := by simpa using heven
    exact (Nat.not_odd_iff_even.mpr this) D.unit.2
  have hrightAvoid : D.unit.1.1 ∉
      T.pathEdges z.2.1 (T.edgeRight D.unit.1) := by
    intro hmem
    have heven := path_edge_even_of_component_eq T z.2.2 hmem
    have : Even (T.weight D.unit.1) := by simpa using heven
    exact (Nat.not_odd_iff_even.mpr this) D.unit.2
  have hleft := (T.cut_reachable_iff_not_mem_pathEdges D.unit.1 _ _).2
    hleftAvoid
  have hright := (T.cut_reachable_iff_not_mem_pathEdges D.unit.1 _ _).2
    hrightAvoid
  have hroute := T.cross_distance_decomposition D.unit.1 hleft hright
  have hpair : T.pairDist (unitRectanglePair D z) = T.dist z.1.1 z.2.1 := by
    rw [unitRectanglePair, T.pairDist_pairOfDistinct]
  rw [hpair]
  rw [D.unit_weight] at hroute
  rcases hleftEven with ⟨a, ha⟩
  rcases hrightEven with ⟨b, hb⟩
  rw [T.dist_comm z.2.1 (T.edgeRight D.unit.1)] at hb
  exact ⟨a + b, by omega⟩

theorem unitRectangleHalfRank_injective
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T) :
    Function.Injective
      (fun z : UnitLeftComponentVertex D × UnitRightComponentVertex D =>
        T.pairDist (unitRectanglePair D z) / 2) := by
  intro x y hhalf
  have hx := unitRectanglePair_dist_odd D x
  have hy := unitRectanglePair_dist_odd D y
  have hdist : T.pairDist (unitRectanglePair D x) =
      T.pairDist (unitRectanglePair D y) := by
    rcases hx with ⟨a, ha⟩
    rcases hy with ⟨b, hb⟩
    have hxa : T.pairDist (unitRectanglePair D x) / 2 = a := by
      omega
    have hyb : T.pairDist (unitRectanglePair D y) / 2 = b := by
      omega
    change T.pairDist (unitRectanglePair D x) / 2 =
      T.pairDist (unitRectanglePair D y) / 2 at hhalf
    rw [hxa, hyb] at hhalf
    omega
  exact unitRectanglePair_injective D (hL.pairDist_injective hdist)

noncomputable def unitRectangleHalfRankPoly
    {T : PosIntTree n} (D : SecondOddBridgeData T) : ℕ[X] :=
  rankPoly fun z : UnitLeftComponentVertex D × UnitRightComponentVertex D =>
    T.pairDist (unitRectanglePair D z) / 2

noncomputable def truncatedIntervalPoly (t : ℕ) : ℕ[X] :=
  rankPoly fun i : Fin t => (i : ℕ)

theorem unitRectangleHalfRankPoly_coeff_lt
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T)
    {k : ℕ} (hk : k < D.t) :
    (unitRectangleHalfRankPoly D).coeff k = 1 := by
  let i : Fin D.t := ⟨k, hk⟩
  let z₀ := lowOddUnitRectanglePoint hL D i
  have hz₀ : T.pairDist (unitRectanglePair D z₀) / 2 = k := by
    rw [lowOddUnitRectanglePoint_spec hL D i,
      lowOddPair_halfRank hL D i]
  rw [unitRectangleHalfRankPoly, rankPoly_coeff]
  calc
    Fintype.card
        {z : UnitLeftComponentVertex D × UnitRightComponentVertex D //
          T.pairDist (unitRectanglePair D z) / 2 = k} =
        Fintype.card
          {z : UnitLeftComponentVertex D × UnitRightComponentVertex D //
            z = z₀} := by
      apply Fintype.card_congr
      exact Equiv.subtypeEquivRight fun z => by
        constructor
        · intro hz
          exact unitRectangleHalfRank_injective hL D (hz.trans hz₀.symm)
        · rintro rfl
          exact hz₀
    _ = 1 := Fintype.card_subtype_eq z₀

theorem truncatedIntervalPoly_coeff_lt (t : ℕ) {k : ℕ} (hk : k < t) :
    (truncatedIntervalPoly t).coeff k = 1 := by
  let i : Fin t := ⟨k, hk⟩
  rw [truncatedIntervalPoly, rankPoly_coeff]
  calc
    Fintype.card {j : Fin t // (j : ℕ) = k} =
        Fintype.card {j : Fin t // j = i} := by
      apply Fintype.card_congr
      exact Equiv.subtypeEquivRight fun j => by
        constructor
        · intro h
          apply Fin.ext
          exact h
        · rintro rfl
          rfl
    _ = 1 := Fintype.card_subtype_eq i

/-- The actual unit-bridge polynomial is congruent to the interval factor
modulo `X^t`.  This is the literal polynomial boundary behind the audited
truncation warning; it makes no full-factorization claim. -/
theorem unitRectangle_polynomial_congruent_mod_X_pow_t
    {T : PosIntTree n} (hL : IsLeech T) (D : SecondOddBridgeData T) :
    (Polynomial.X : ℤ[X]) ^ D.t ∣
      (unitRectangleHalfRankPoly D).map (Nat.castRingHom ℤ) -
        (truncatedIntervalPoly D.t).map (Nat.castRingHom ℤ) := by
  apply (Polynomial.X_pow_dvd_iff).2
  intro k hk
  rw [Polynomial.coeff_sub, Polynomial.coeff_map,
    Polynomial.coeff_map, unitRectangleHalfRankPoly_coeff_lt hL D hk,
    truncatedIntervalPoly_coeff_lt D.t hk]
  norm_num

end LeechTrees.OddQuotient.Q2Bounds.EqualityTruncation
