import LeechTrees.FirstEdge

/-!
# The exhaustive first-edge placement dossier

This module formalizes the eight local rows in
`legacy_core/root_search/forced_small_edge_placement_lemma.md`.

The statements are deliberately local.  They neither assert the existence of
a Leech tree nor exclude any order.  The three cut conclusions are conditional
on the order being exactly eighteen.
-/

namespace LeechTrees.Foundation

namespace PosIntTree

variable {n : ℕ} (T : PosIntTree n)

/-- Endpoint-disjointness is symmetric. -/
theorem edgeEndpointDisjoint_comm (e f : T.Edge) :
    T.EdgeEndpointDisjoint e f ↔ T.EdgeEndpointDisjoint f e := by
  constructor
  · intro h v hvf hve
    exact h v hve hvf
  · intro h v hve hvf
    exact h v hvf hve

/-- Two distinct simple edges either meet in one endpoint or are endpoint-disjoint. -/
theorem edgeAdjacent_or_endpointDisjoint {e f : T.Edge} (hef : e ≠ f) :
    T.EdgeAdjacent e f ∨ T.EdgeEndpointDisjoint e f := by
  by_cases hmeet : ∃ v : Fin n, v ∈ e.1 ∧ v ∈ f.1
  · exact Or.inl ⟨hef, hmeet⟩
  · right
    intro v hve hvf
    exact hmeet ⟨v, hve, hvf⟩

/-- For distinct edges, endpoint-disjointness is exactly failure of adjacency. -/
theorem edgeEndpointDisjoint_iff_not_adjacent {e f : T.Edge} (hef : e ≠ f) :
    T.EdgeEndpointDisjoint e f ↔ ¬T.EdgeAdjacent e f := by
  constructor
  · intro hdis hadj
    obtain ⟨v, hve, hvf⟩ := hadj.2
    exact hdis v hve hvf
  · intro hnot
    rcases T.edgeAdjacent_or_endpointDisjoint hef with hadj | hdis
    · exact (hnot hadj).elim
    · exact hdis

/-- Three actual edges occur consecutively on a simple path in the displayed
order.  The endpoint-disjointness of the outer edges is part of the exact
path condition. -/
def EdgeChain (e f g : T.Edge) : Prop :=
  T.EdgeAdjacent e f ∧ T.EdgeAdjacent f g ∧ T.EdgeEndpointDisjoint e g

theorem edgeChain_reverse (e f g : T.Edge) :
    T.EdgeChain e f g ↔ T.EdgeChain g f e := by
  constructor
  · rintro ⟨hef, hfg, heg⟩
    exact ⟨(T.edgeAdjacent_comm f g).1 hfg,
      (T.edgeAdjacent_comm e f).1 hef,
      (T.edgeEndpointDisjoint_comm e g).1 heg⟩
  · rintro ⟨hgf, hfe, hge⟩
    exact ⟨(T.edgeAdjacent_comm f e).1 hfe,
      (T.edgeAdjacent_comm g f).1 hgf,
      (T.edgeEndpointDisjoint_comm g e).1 hge⟩

/-- The three named edges form a simple three-edge path, with one of them as
the middle edge. -/
def ThreeEdgePathArrangement (e f g : T.Edge) : Prop :=
  T.EdgeChain e f g ∨ T.EdgeChain e g f ∨ T.EdgeChain f e g

end PosIntTree

namespace FirstEdgeDossier

variable {n : ℕ} {T : PosIntTree n}

/-- The ordered list of physical weights on a named simple path. -/
noncomputable def pathWeightList {u v : Fin n} (p : T.graph.Path u v) : List ℕ :=
  p.1.edges.map T.weightOfPair

/-- A simple path whose physical weights, in one orientation, are exactly the
displayed list. -/
def HasPathWeightSequence (T : PosIntTree n) (weights : List ℕ) : Prop :=
  ∃ u v : Fin n, ∃ p : T.graph.Path u v,
    pathWeightList (T := T) p = weights

/-- A physical edge of weight `k`, unique among physical edges, together with
the exact internal-distance set immediately before it and the forced-MEX
equation. -/
def ForcedPrefixEdge (T : PosIntTree n) (k : ℕ) (spectrum : Finset ℕ) : Prop :=
  ∃ e : T.Edge,
    T.weight e = k ∧
    (∀ f : T.Edge, T.weight f = k → f = e) ∧
    T.prefixInternalDistances e = spectrum ∧
    PosIntTree.mexPos (T.prefixInternalDistances e) = k

/-! ## Literal row propositions -/

structure AdjacentNoneRow (T : PosIntTree n) (e1 e2 : T.Edge) : Prop where
  adjacent12 : T.EdgeAdjacent e1 e2
  noWeight3 : ¬∃ e : T.Edge, T.weight e = 3
  witness4 : ∃ e4 : T.Edge,
    T.weight e4 = 4 ∧
    (∀ f : T.Edge, T.weight f = 4 → f = e4) ∧
    T.EdgeEndpointDisjoint e4 e1 ∧
    T.EdgeEndpointDisjoint e4 e2
  path12 : HasPathWeightSequence T [1, 2]
  forced5 : ForcedPrefixEdge T 5 {1, 2, 3, 4}

structure AdjacentMeetsOneRow (T : PosIntTree n) (e1 e2 : T.Edge) : Prop where
  adjacent12 : T.EdgeAdjacent e1 e2
  noWeight3 : ¬∃ e : T.Edge, T.weight e = 3
  witness4 : ∃ e4 : T.Edge,
    T.weight e4 = 4 ∧
    (∀ f : T.Edge, T.weight f = 4 → f = e4) ∧
    T.EdgeAdjacent e4 e1 ∧
    T.EdgeEndpointDisjoint e4 e2
  path12 : HasPathWeightSequence T [1, 2]
  path14 : HasPathWeightSequence T [1, 4]
  path214 : HasPathWeightSequence T [2, 1, 4]
  noWeight5 : ¬∃ e : T.Edge, T.weight e = 5
  noWeight7 : ¬∃ e : T.Edge, T.weight e = 7
  forced6 : ForcedPrefixEdge T 6 {1, 2, 3, 4, 5, 7}
  weight6_disjoint_e1 :
    ∀ e6 : T.Edge, T.weight e6 = 6 → T.EdgeEndpointDisjoint e6 e1
  order18_cut : n = 18 →
    32 ≤ T.cutSize e1 * (n - T.cutSize e1)

structure AdjacentMeetsTwoRow (T : PosIntTree n) (e1 e2 : T.Edge) : Prop where
  adjacent12 : T.EdgeAdjacent e1 e2
  noWeight3 : ¬∃ e : T.Edge, T.weight e = 3
  witness4 : ∃ e4 : T.Edge,
    T.weight e4 = 4 ∧
    (∀ f : T.Edge, T.weight f = 4 → f = e4) ∧
    T.EdgeEndpointDisjoint e4 e1 ∧
    T.EdgeAdjacent e4 e2
  path12 : HasPathWeightSequence T [1, 2]
  path24 : HasPathWeightSequence T [2, 4]
  path124 : HasPathWeightSequence T [1, 2, 4]
  noWeight6 : ¬∃ e : T.Edge, T.weight e = 6
  noWeight7 : ¬∃ e : T.Edge, T.weight e = 7
  forced5 : ForcedPrefixEdge T 5 {1, 2, 3, 4, 6, 7}
  weight5_disjoint_e1 :
    ∀ e5 : T.Edge, T.weight e5 = 5 → T.EdgeEndpointDisjoint e5 e1
  weight5_disjoint_e2 :
    ∀ e5 : T.Edge, T.weight e5 = 5 → T.EdgeEndpointDisjoint e5 e2
  order18_cut : n = 18 →
    32 ≤ T.cutSize e2 * (n - T.cutSize e2)

structure AdjacentMeetsBothRow (T : PosIntTree n) (e1 e2 : T.Edge) : Prop where
  adjacent12 : T.EdgeAdjacent e1 e2
  noWeight3 : ¬∃ e : T.Edge, T.weight e = 3
  witness4 : ∃ e4 : T.Edge,
    T.weight e4 = 4 ∧
    (∀ f : T.Edge, T.weight f = 4 → f = e4) ∧
    T.EdgeAdjacent e4 e1 ∧
    T.EdgeAdjacent e4 e2
  path12 : HasPathWeightSequence T [1, 2]
  path14 : HasPathWeightSequence T [1, 4]
  path24 : HasPathWeightSequence T [2, 4]
  noWeight5 : ¬∃ e : T.Edge, T.weight e = 5
  noWeight6 : ¬∃ e : T.Edge, T.weight e = 6
  forced7 : ForcedPrefixEdge T 7 {1, 2, 3, 4, 5, 6}

structure DisjointNoneRow (T : PosIntTree n) (e1 e2 : T.Edge) : Prop where
  disjoint12 : T.EdgeEndpointDisjoint e1 e2
  witness3 : ∃ e3 : T.Edge,
    T.weight e3 = 3 ∧
    (∀ f : T.Edge, T.weight f = 3 → f = e3) ∧
    T.EdgeEndpointDisjoint e3 e1 ∧
    T.EdgeEndpointDisjoint e3 e2
  forced4 : ForcedPrefixEdge T 4 {1, 2, 3}

structure DisjointMeetsOneRow (T : PosIntTree n) (e1 e2 : T.Edge) : Prop where
  disjoint12 : T.EdgeEndpointDisjoint e1 e2
  witness3 : ∃ e3 : T.Edge,
    T.weight e3 = 3 ∧
    (∀ f : T.Edge, T.weight f = 3 → f = e3) ∧
    T.EdgeAdjacent e3 e1 ∧
    T.EdgeEndpointDisjoint e3 e2
  path13 : HasPathWeightSequence T [1, 3]
  noWeight4 : ¬∃ e : T.Edge, T.weight e = 4
  forced5 : ForcedPrefixEdge T 5 {1, 2, 3, 4}

structure DisjointMeetsTwoRow (T : PosIntTree n) (e1 e2 : T.Edge) : Prop where
  disjoint12 : T.EdgeEndpointDisjoint e1 e2
  witness3 : ∃ e3 : T.Edge,
    T.weight e3 = 3 ∧
    (∀ f : T.Edge, T.weight f = 3 → f = e3) ∧
    T.EdgeEndpointDisjoint e3 e1 ∧
    T.EdgeAdjacent e3 e2
  path23 : HasPathWeightSequence T [2, 3]
  noWeight5 : ¬∃ e : T.Edge, T.weight e = 5
  forced4 : ForcedPrefixEdge T 4 {1, 2, 3, 5}
  weight4_disjoint_e1 :
    ∀ e4 : T.Edge, T.weight e4 = 4 → T.EdgeEndpointDisjoint e4 e1

structure DisjointMeetsBothRow (T : PosIntTree n) (e1 e2 : T.Edge) : Prop where
  disjoint12 : T.EdgeEndpointDisjoint e1 e2
  witness3 : ∃ e3 : T.Edge,
    T.weight e3 = 3 ∧
    (∀ f : T.Edge, T.weight f = 3 → f = e3) ∧
    T.EdgeAdjacent e3 e1 ∧
    T.EdgeAdjacent e3 e2 ∧
    (n = 18 → 32 ≤ T.cutSize e3 * (n - T.cutSize e3))
  path13 : HasPathWeightSequence T [1, 3]
  path32 : HasPathWeightSequence T [3, 2]
  path132 : HasPathWeightSequence T [1, 3, 2]
  noWeight4 : ¬∃ e : T.Edge, T.weight e = 4
  noWeight5 : ¬∃ e : T.Edge, T.weight e = 5
  noWeight6 : ¬∃ e : T.Edge, T.weight e = 6
  forced7 : ForcedPrefixEdge T 7 {1, 2, 3, 4, 5, 6}

/-- The exact eight-way local partition. -/
def EightRowDossier (T : PosIntTree n) (e1 e2 : T.Edge) : Prop :=
  AdjacentNoneRow T e1 e2 ∨
  AdjacentMeetsOneRow T e1 e2 ∨
  AdjacentMeetsTwoRow T e1 e2 ∨
  AdjacentMeetsBothRow T e1 e2 ∨
  DisjointNoneRow T e1 e2 ∨
  DisjointMeetsOneRow T e1 e2 ∨
  DisjointMeetsTwoRow T e1 e2 ∨
  DisjointMeetsBothRow T e1 e2

/-! ## Weighted-path infrastructure -/

private def edgeOfAdj {u v : Fin n} (h : T.graph.Adj u v) : T.Edge :=
  ⟨s(u, v), by simpa [SimpleGraph.mem_edgeSet] using h⟩

@[simp] private theorem edgeOfAdj_val {u v : Fin n} (h : T.graph.Adj u v) :
    (edgeOfAdj (T := T) h).1 = s(u, v) := rfl

private theorem weight_edgeOfAdj {u v : Fin n} (h : T.graph.Adj u v) :
    T.weight (edgeOfAdj (T := T) h) = T.weightOfPair s(u, v) := by
  change T.weight (edgeOfAdj (T := T) h) =
    T.weightOfPair (edgeOfAdj (T := T) h).1
  exact (T.weightOfPair_edge (edgeOfAdj (T := T) h)).symm

private theorem pathWeightList_sum {u v : Fin n} (p : T.graph.Path u v) :
    (pathWeightList (T := T) p).sum = T.walkWeight p.1 := rfl

private theorem pathWeightList_positive {u v : Fin n}
    (p : T.graph.Path u v) :
    ∀ w ∈ pathWeightList (T := T) p, 0 < w := by
  intro w hw
  rw [pathWeightList, List.mem_map] at hw
  obtain ⟨e, he, rfl⟩ := hw
  let actual : T.Edge := ⟨e, p.1.edges_subset_edgeSet he⟩
  have hpos := T.weight_pos actual
  rw [← T.weightOfPair_edge actual] at hpos
  exact hpos

private theorem pathWeightList_nodup (hL : IsLeech T) {u v : Fin n}
    (p : T.graph.Path u v) :
    (pathWeightList (T := T) p).Nodup := by
  unfold pathWeightList
  apply (List.nodup_map_iff_inj_on p.2.isTrail.edges_nodup).2
  intro e he f hf hw
  let actualE : T.Edge := ⟨e, p.1.edges_subset_edgeSet he⟩
  let actualF : T.Edge := ⟨f, p.1.edges_subset_edgeSet hf⟩
  have hweights : T.weight actualE = T.weight actualF := by
    rw [← T.weightOfPair_edge actualE, ← T.weightOfPair_edge actualF]
    exact hw
  exact congrArg Subtype.val (t1_edge_weight_injective hL hweights)

private theorem pathWeightList_length {u v : Fin n} (p : T.graph.Path u v) :
    (pathWeightList (T := T) p).length = p.1.length := by
  simpa only [pathWeightList, List.length_map] using p.1.length_edges

private theorem path_endpoints_ne_of_weightList_nonempty {u v : Fin n}
    (p : T.graph.Path u v)
    (h : pathWeightList (T := T) p ≠ []) : u ≠ v := by
  intro huv
  subst v
  let p0 : T.graph.Path u u := ⟨SimpleGraph.Walk.nil, by simp⟩
  have hp : p = p0 := (T.path_unique p).trans (T.path_unique p0).symm
  apply h
  rw [hp]
  simp [p0, pathWeightList]

private theorem sym2_pairOfDistinct (u v : Fin n) (huv : u ≠ v) :
    s((VertexPair.ofDistinct u v huv).left,
      (VertexPair.ofDistinct u v huv).right) = s(u, v) := by
  by_cases h : u < v
  · simp [VertexPair.ofDistinct, h, VertexPair.left, VertexPair.right]
  · simp [VertexPair.ofDistinct, h, VertexPair.left, VertexPair.right,
      Sym2.eq_swap]

/-- In an exact Leech spectrum, equal-weight simple paths have the same number
of edges, even when their endpoint orientations differ. -/
private theorem path_length_eq_of_walkWeight_eq (hL : IsLeech T)
    {u v x y : Fin n} (p : T.graph.Path u v) (q : T.graph.Path x y)
    (huv : u ≠ v) (hxy : x ≠ y)
    (hweight : T.walkWeight p.1 = T.walkWeight q.1) :
    p.1.length = q.1.length := by
  have hpdist :
      T.pairDist (VertexPair.ofDistinct u v huv) = T.walkWeight p.1 := by
    rw [T.pairDist_pairOfDistinct]
    exact (T.path_walkWeight_eq_dist p).symm
  have hqdist :
      T.pairDist (VertexPair.ofDistinct x y hxy) = T.walkWeight q.1 := by
    rw [T.pairDist_pairOfDistinct]
    exact (T.path_walkWeight_eq_dist q).symm
  have hpairs : VertexPair.ofDistinct u v huv =
      VertexPair.ofDistinct x y hxy :=
    hL.pairDist_injective (hpdist.trans (hweight.trans hqdist.symm))
  have hs : s(u, v) = s(x, y) := by
    calc
      s(u, v) = s((VertexPair.ofDistinct u v huv).left,
          (VertexPair.ofDistinct u v huv).right) :=
        (sym2_pairOfDistinct u v huv).symm
      _ = s((VertexPair.ofDistinct x y hxy).left,
          (VertexPair.ofDistinct x y hxy).right) := by rw [hpairs]
      _ = s(x, y) := sym2_pairOfDistinct x y hxy
  rcases Sym2.eq_iff.mp hs with hdirect | hreverse
  · rcases hdirect with ⟨rfl, rfl⟩
    have hpq : p = q := (T.path_unique p).trans (T.path_unique q).symm
    exact congrArg (fun r => r.1.length) hpq
  · rcases hreverse with ⟨rfl, rfl⟩
    let qr : T.graph.Path u v := ⟨q.1.reverse, q.2.reverse⟩
    have hpq : p = qr := (T.path_unique p).trans (T.path_unique qr).symm
    have hlen := congrArg (fun r => r.1.length) hpq
    simpa [qr] using hlen

private theorem sequence_length_eq_of_sum_eq (hL : IsLeech T)
    {a b : List ℕ}
    (ha : HasPathWeightSequence T a) (hb : HasPathWeightSequence T b)
    (hane : a ≠ []) (hbne : b ≠ []) (hsum : a.sum = b.sum) :
    a.length = b.length := by
  obtain ⟨u, v, p, hp⟩ := ha
  obtain ⟨x, y, q, hq⟩ := hb
  have huv : u ≠ v := path_endpoints_ne_of_weightList_nonempty p (hp ▸ hane)
  have hxy : x ≠ y := path_endpoints_ne_of_weightList_nonempty q (hq ▸ hbne)
  have hw : T.walkWeight p.1 = T.walkWeight q.1 := by
    rw [← pathWeightList_sum p, ← pathWeightList_sum q, hp, hq, hsum]
  have hlen := path_length_eq_of_walkWeight_eq hL p q huv hxy hw
  rw [← pathWeightList_length p, ← pathWeightList_length q, hp, hq] at hlen
  exact hlen

private theorem sequence_eq_or_reverse_of_sum_eq (hL : IsLeech T)
    {a b : List ℕ}
    (ha : HasPathWeightSequence T a) (hb : HasPathWeightSequence T b)
    (hane : a ≠ []) (hbne : b ≠ []) (hsum : a.sum = b.sum) :
    a = b ∨ a = b.reverse := by
  obtain ⟨u, v, p, hp⟩ := ha
  obtain ⟨x, y, q, hq⟩ := hb
  have huv : u ≠ v := path_endpoints_ne_of_weightList_nonempty p (hp ▸ hane)
  have hxy : x ≠ y := path_endpoints_ne_of_weightList_nonempty q (hq ▸ hbne)
  have hpdist :
      T.pairDist (VertexPair.ofDistinct u v huv) = T.walkWeight p.1 := by
    rw [T.pairDist_pairOfDistinct]
    exact (T.path_walkWeight_eq_dist p).symm
  have hqdist :
      T.pairDist (VertexPair.ofDistinct x y hxy) = T.walkWeight q.1 := by
    rw [T.pairDist_pairOfDistinct]
    exact (T.path_walkWeight_eq_dist q).symm
  have hwalk : T.walkWeight p.1 = T.walkWeight q.1 := by
    rw [← pathWeightList_sum p, ← pathWeightList_sum q, hp, hq, hsum]
  have hpairs : VertexPair.ofDistinct u v huv =
      VertexPair.ofDistinct x y hxy :=
    hL.pairDist_injective (hpdist.trans (hwalk.trans hqdist.symm))
  have hs : s(u, v) = s(x, y) := by
    calc
      s(u, v) = s((VertexPair.ofDistinct u v huv).left,
          (VertexPair.ofDistinct u v huv).right) :=
        (sym2_pairOfDistinct u v huv).symm
      _ = s((VertexPair.ofDistinct x y hxy).left,
          (VertexPair.ofDistinct x y hxy).right) := by rw [hpairs]
      _ = s(x, y) := sym2_pairOfDistinct x y hxy
  rcases Sym2.eq_iff.mp hs with hdirect | hreverse
  · rcases hdirect with ⟨rfl, rfl⟩
    have hpq : p = q := (T.path_unique p).trans (T.path_unique q).symm
    left
    rw [← hp, ← hq, hpq]
  · rcases hreverse with ⟨rfl, rfl⟩
    let qr : T.graph.Path u v := ⟨q.1.reverse, q.2.reverse⟩
    have hpq : p = qr := (T.path_unique p).trans (T.path_unique qr).symm
    right
    rw [← hp, ← hq, hpq]
    simp [qr, pathWeightList]

private theorem edge_hasPathWeightSequence (e : T.Edge) :
    HasPathWeightSequence T [T.weight e] := by
  let p : T.graph.Path (T.edgeLeft e) (T.edgeRight e) :=
    SimpleGraph.Path.singleton (T.edge_adj e)
  refine ⟨T.edgeLeft e, T.edgeRight e, p, ?_⟩
  have hweight :
      T.weightOfPair s(T.edgeLeft e, T.edgeRight e) = T.weight e := by
    rw [← T.edge_eq_mk_endpoints e, T.weightOfPair_edge]
  simp [p, pathWeightList, SimpleGraph.Path.singleton, hweight]

private theorem no_physicalWeight_of_nontrivial_sequence
    (hL : IsLeech T) {weights : List ℕ}
    (hseq : HasPathWeightSequence T weights)
    (hne : weights ≠ []) (hlen : weights.length ≠ 1) :
    ¬∃ e : T.Edge, T.weight e = weights.sum := by
  rintro ⟨e, he⟩
  have hedge : HasPathWeightSequence T [weights.sum] := by
    simpa [he] using edge_hasPathWeightSequence (T := T) e
  have hlength := sequence_length_eq_of_sum_eq hL hseq hedge hne (by simp) (by simp)
  simp at hlength
  exact hlen hlength

private theorem edgeAdjacent_hasPathWeightSequence (e f : T.Edge)
    (hadj : T.EdgeAdjacent e f) :
    HasPathWeightSequence T [T.weight e, T.weight f] := by
  obtain ⟨v, hve, hvf⟩ := hadj.2
  let x : Fin n := Sym2.Mem.other hve
  let y : Fin n := Sym2.Mem.other hvf
  have he : s(v, x) = e.1 := Sym2.other_spec hve
  have hf : s(v, y) = f.1 := Sym2.other_spec hvf
  have hvx : T.graph.Adj v x := by
    rw [← SimpleGraph.mem_edgeSet, he]
    exact e.2
  have hvy : T.graph.Adj v y := by
    rw [← SimpleGraph.mem_edgeSet, hf]
    exact f.2
  have hxy : x ≠ y := by
    intro h
    apply hadj.1
    apply Subtype.ext
    rw [← he, ← hf, h]
  let w : T.graph.Walk x y :=
    SimpleGraph.Walk.cons hvx.symm
      (SimpleGraph.Walk.cons hvy SimpleGraph.Walk.nil)
  have hw : w.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simp [w, hvx.ne.symm, hvy.ne, hxy]
  let p : T.graph.Path x y := ⟨w, hw⟩
  have hwe : T.weightOfPair s(x, v) = T.weight e := by
    calc
      T.weightOfPair s(x, v) = T.weightOfPair s(v, x) := by rw [Sym2.eq_swap]
      _ = T.weightOfPair e.1 := by rw [he]
      _ = T.weight e := T.weightOfPair_edge e
  have hwf : T.weightOfPair s(v, y) = T.weight f := by
    calc
      T.weightOfPair s(v, y) = T.weightOfPair f.1 := by rw [hf]
      _ = T.weight f := T.weightOfPair_edge f
  exact ⟨x, y, p, by simp [p, w, pathWeightList, hwe, hwf]⟩

private theorem edgeChain_hasPathWeightSequence (e f g : T.Edge)
    (hchain : T.EdgeChain e f g) :
    HasPathWeightSequence T [T.weight e, T.weight f, T.weight g] := by
  obtain ⟨hef, hfg, heg⟩ := hchain
  obtain ⟨a, hae, haf⟩ := hef.2
  obtain ⟨b, hbf, hbg⟩ := hfg.2
  have hab : a ≠ b := by
    intro h
    subst b
    exact heg a hae hbg
  let x : Fin n := Sym2.Mem.other hae
  let y : Fin n := Sym2.Mem.other hbg
  have he : s(a, x) = e.1 := Sym2.other_spec hae
  have hg : s(b, y) = g.1 := Sym2.other_spec hbg
  have hf : f.1 = s(a, b) :=
    (Sym2.mem_and_mem_iff hab).mp ⟨haf, hbf⟩
  have hax : T.graph.Adj a x := by
    rw [← SimpleGraph.mem_edgeSet, he]
    exact e.2
  have habAdj : T.graph.Adj a b := by
    rw [← SimpleGraph.mem_edgeSet, ← hf]
    exact f.2
  have hby : T.graph.Adj b y := by
    rw [← SimpleGraph.mem_edgeSet, hg]
    exact g.2
  have hxe : x ∈ e.1 := by rw [← he]; simp
  have hyg : y ∈ g.1 := by rw [← hg]; simp
  have hxb : x ≠ b := by
    intro h
    subst b
    exact heg x hxe hbg
  have hay : a ≠ y := by
    intro h
    exact heg a hae (h.symm ▸ hyg)
  have hxy : x ≠ y := by
    intro h
    exact heg x hxe (h.symm ▸ hyg)
  let w : T.graph.Walk x y :=
    SimpleGraph.Walk.cons hax.symm
      (SimpleGraph.Walk.cons habAdj
        (SimpleGraph.Walk.cons hby SimpleGraph.Walk.nil))
  have hw : w.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simp [w, hax.ne.symm, habAdj.ne, hby.ne, hxb, hay, hxy]
  let p : T.graph.Path x y := ⟨w, hw⟩
  have hwe : T.weightOfPair s(x, a) = T.weight e := by
    calc
      T.weightOfPair s(x, a) = T.weightOfPair s(a, x) := by rw [Sym2.eq_swap]
      _ = T.weightOfPair e.1 := by rw [he]
      _ = T.weight e := T.weightOfPair_edge e
  have hwf : T.weightOfPair s(a, b) = T.weight f := by
    calc
      T.weightOfPair s(a, b) = T.weightOfPair f.1 := by rw [hf]
      _ = T.weight f := T.weightOfPair_edge f
  have hwg : T.weightOfPair s(b, y) = T.weight g := by
    calc
      T.weightOfPair s(b, y) = T.weightOfPair g.1 := by rw [hg]
      _ = T.weight g := T.weightOfPair_edge g
  exact ⟨x, y, p, by simp [p, w, pathWeightList, hwe, hwf, hwg]⟩

private theorem physicalEdge_of_pathWeightList_singleton
    {u v : Fin n} (p : T.graph.Path u v) {k : ℕ}
    (hlist : pathWeightList (T := T) p = [k]) :
    ∃ e : T.Edge, T.weight e = k := by
  have hlenEdges : p.1.edges.length = 1 := by
    have h := congrArg List.length hlist
    simpa [pathWeightList] using h
  have hlen : p.1.length = 1 := by
    rw [← p.1.length_edges]
    exact hlenEdges
  have hpnon : ¬p.1.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    omega
  let first := edgeOfAdj (T := T) (p.1.adj_snd hpnon)
  have hcons := p.1.cons_tail_eq hpnon
  have hlist' := hlist
  unfold pathWeightList at hlist'
  rw [← hcons] at hlist'
  simp only [SimpleGraph.Walk.edges_cons, List.map_cons] at hlist'
  have hhead : T.weightOfPair s(u, p.1.snd) = k := by
    simpa using congrArg List.head? hlist'
  exact ⟨first, by rw [weight_edgeOfAdj]; exact hhead⟩

private theorem adjacentEdges_of_pathWeightList_pair
    {u v : Fin n} (p : T.graph.Path u v) {a b : ℕ}
    (hlist : pathWeightList (T := T) p = [a, b]) :
    ∃ eA eB : T.Edge,
      T.weight eA = a ∧ T.weight eB = b ∧ T.EdgeAdjacent eA eB := by
  have hlenEdges : p.1.edges.length = 2 := by
    have h := congrArg List.length hlist
    simpa [pathWeightList] using h
  have hlen : p.1.length = 2 := by
    rw [← p.1.length_edges]
    exact hlenEdges
  have hpnon : ¬p.1.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    omega
  have htailLen : p.1.tail.length = 1 := by
    have h := p.1.length_tail_add_one hpnon
    omega
  have htailnon : ¬p.1.tail.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    omega
  let first := edgeOfAdj (T := T) (p.1.adj_snd hpnon)
  let second := edgeOfAdj (T := T) (p.1.tail.adj_snd htailnon)
  have hcons := p.1.cons_tail_eq hpnon
  have htailCons := p.1.tail.cons_tail_eq htailnon
  have hlist' := hlist
  unfold pathWeightList at hlist'
  rw [← hcons] at hlist'
  simp only [SimpleGraph.Walk.edges_cons, List.map_cons] at hlist'
  have hfirstWeight : T.weightOfPair s(u, p.1.snd) = a := by
    simpa using congrArg List.head? hlist'
  have htailList : p.1.tail.edges.map T.weightOfPair = [b] := by
    simpa using congrArg List.tail hlist'
  have htailList' := htailList
  rw [← htailCons] at htailList'
  simp only [SimpleGraph.Walk.edges_cons, List.map_cons] at htailList'
  have hsecondWeight :
      T.weightOfPair s(p.1.snd, p.1.tail.snd) = b := by
    simpa using congrArg List.head? htailList'
  have hnotFirst : s(u, p.1.snd) ∉ p.1.tail.edges := by
    have hnodup := p.2.isTrail.edges_nodup
    rw [← hcons] at hnodup
    exact (List.nodup_cons.mp hnodup).1
  have hsecondMem : s(p.1.snd, p.1.tail.snd) ∈ p.1.tail.edges := by
    rw [← htailCons]
    simp
  have hne : first ≠ second := by
    intro heq
    have hval : s(u, p.1.snd) = s(p.1.snd, p.1.tail.snd) :=
      congrArg Subtype.val heq
    apply hnotFirst
    rw [hval]
    exact hsecondMem
  refine ⟨first, second, ?_, ?_, hne, p.1.snd, ?_, ?_⟩
  · rw [weight_edgeOfAdj]
    exact hfirstWeight
  · rw [weight_edgeOfAdj]
    exact hsecondWeight
  · simp [first, edgeOfAdj]
  · simp [second, edgeOfAdj]

/-- Three entries in a path weight list produce three actual consecutive
edges; in particular, the outer actual edges are endpoint-disjoint. -/
private theorem chainEdges_of_pathWeightList_triple
    {u v : Fin n} (p : T.graph.Path u v) {a b c : ℕ}
    (hlist : pathWeightList (T := T) p = [a, b, c]) :
    ∃ eA eB eC : T.Edge,
      T.weight eA = a ∧ T.weight eB = b ∧ T.weight eC = c ∧
      T.EdgeChain eA eB eC := by
  have hlenEdges : p.1.edges.length = 3 := by
    have h := congrArg List.length hlist
    simpa [pathWeightList] using h
  have hlen : p.1.length = 3 := by
    rw [← p.1.length_edges]
    exact hlenEdges
  have hpnon : ¬p.1.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    omega
  have htailLen : p.1.tail.length = 2 := by
    have h := p.1.length_tail_add_one hpnon
    omega
  have htailnon : ¬p.1.tail.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    omega
  have htailtailLen : p.1.tail.tail.length = 1 := by
    have h := p.1.tail.length_tail_add_one htailnon
    omega
  have htailtailnon : ¬p.1.tail.tail.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    omega
  let first := edgeOfAdj (T := T) (p.1.adj_snd hpnon)
  let second := edgeOfAdj (T := T) (p.1.tail.adj_snd htailnon)
  let third := edgeOfAdj (T := T) (p.1.tail.tail.adj_snd htailtailnon)
  have hcons := p.1.cons_tail_eq hpnon
  have hcons2 := p.1.tail.cons_tail_eq htailnon
  have hcons3 := p.1.tail.tail.cons_tail_eq htailtailnon
  have hlist' := hlist
  unfold pathWeightList at hlist'
  rw [← hcons] at hlist'
  simp only [SimpleGraph.Walk.edges_cons, List.map_cons] at hlist'
  have hw1 : T.weightOfPair s(u, p.1.snd) = a := by
    simpa using congrArg List.head? hlist'
  have htailList : p.1.tail.edges.map T.weightOfPair = [b, c] := by
    simpa using congrArg List.tail hlist'
  have htailList' := htailList
  rw [← hcons2] at htailList'
  simp only [SimpleGraph.Walk.edges_cons, List.map_cons] at htailList'
  have hw2 : T.weightOfPair s(p.1.snd, p.1.tail.snd) = b := by
    simpa using congrArg List.head? htailList'
  have htailtailList : p.1.tail.tail.edges.map T.weightOfPair = [c] := by
    simpa using congrArg List.tail htailList'
  have htailtailList' := htailtailList
  rw [← hcons3] at htailtailList'
  simp only [SimpleGraph.Walk.edges_cons, List.map_cons] at htailtailList'
  have hw3 :
      T.weightOfPair s(p.1.tail.snd, p.1.tail.tail.snd) = c := by
    simpa using congrArg List.head? htailtailList'
  have hedgesNodup := p.2.isTrail.edges_nodup
  rw [← hcons, SimpleGraph.Walk.edges_cons,
    ← hcons2, SimpleGraph.Walk.edges_cons,
    ← hcons3, SimpleGraph.Walk.edges_cons] at hedgesNodup
  have hne12 : first ≠ second := by
    intro h
    have hv := congrArg Subtype.val h
    change s(u, p.1.snd) = s(p.1.snd, p.1.tail.snd) at hv
    apply (List.nodup_cons.mp hedgesNodup).1
    exact List.mem_cons.mpr (Or.inl hv)
  have hne23 : second ≠ third := by
    intro h
    have hv := congrArg Subtype.val h
    change s(p.1.snd, p.1.tail.snd) =
      s(p.1.tail.snd, p.1.tail.tail.snd) at hv
    have htailNodup := (List.nodup_cons.mp hedgesNodup).2
    apply (List.nodup_cons.mp htailNodup).1
    exact List.mem_cons.mpr (Or.inl hv)
  have hne13 : first ≠ third := by
    intro h
    have hv := congrArg Subtype.val h
    change s(u, p.1.snd) = s(p.1.tail.snd, p.1.tail.tail.snd) at hv
    apply (List.nodup_cons.mp hedgesNodup).1
    exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl hv)))
  have hadj12 : T.EdgeAdjacent first second := by
    refine ⟨hne12, p.1.snd, ?_, ?_⟩ <;>
      simp [first, second, edgeOfAdj]
  have hadj23 : T.EdgeAdjacent second third := by
    refine ⟨hne23, p.1.tail.snd, ?_, ?_⟩ <;>
      simp [second, third, edgeOfAdj]
  have hdis13 : T.EdgeEndpointDisjoint first third := by
    intro z hz1 hz3
    have hz1' : z = u ∨ z = p.1.snd := by
      simpa [first, edgeOfAdj] using hz1
    have hz3' : z = p.1.tail.snd ∨ z = p.1.tail.tail.snd := by
      simpa [third, edgeOfAdj] using hz3
    have hu2 : u ≠ p.1.tail.snd := by
      intro h
      have hi : (0 : ℕ) = 2 := p.2.getVert_injOn
        (show 0 ≤ p.1.length by omega) (show 2 ≤ p.1.length by omega) (by
          simp [h])
      omega
    have hu3 : u ≠ p.1.tail.tail.snd := by
      intro h
      have hi : (0 : ℕ) = 3 := p.2.getVert_injOn
        (show 0 ≤ p.1.length by omega) (show 3 ≤ p.1.length by omega) (by
          simp [h])
      omega
    have hsnd2 : p.1.snd ≠ p.1.tail.snd := by
      intro h
      have hi : (1 : ℕ) = 2 := p.2.getVert_injOn
        (show 1 ≤ p.1.length by omega) (show 2 ≤ p.1.length by omega) (by
          simp [h])
      omega
    have hsnd3 : p.1.snd ≠ p.1.tail.tail.snd := by
      intro h
      have hi : (1 : ℕ) = 3 := p.2.getVert_injOn
        (show 1 ≤ p.1.length by omega) (show 3 ≤ p.1.length by omega) (by
          simp [h])
      omega
    rcases hz1' with hz1u | hz1s <;> rcases hz3' with hz32 | hz33
    · exact hu2 (hz1u.symm.trans hz32)
    · exact hu3 (hz1u.symm.trans hz33)
    · exact hsnd2 (hz1s.symm.trans hz32)
    · exact hsnd3 (hz1s.symm.trans hz33)
  refine ⟨first, second, third, ?_, ?_, ?_, hadj12, hadj23, hdis13⟩
  · rw [weight_edgeOfAdj]
    exact hw1
  · rw [weight_edgeOfAdj]
    exact hw2
  · rw [weight_edgeOfAdj]
    exact hw3

/-! The next three lemmas are the complete distinct-positive compositions
through seven, with path order retained. -/

private theorem positive_nodup_sum_four_shape {weights : List ℕ}
    (positive : ∀ w ∈ weights, 0 < w)
    (nodup : weights.Nodup) (total : weights.sum = 4) :
    weights = [4] ∨ weights = [1, 3] ∨ weights = [3, 1] := by
  cases weights with
  | nil => simp at total
  | cons a as =>
      cases as with
      | nil =>
          left
          simp only [List.sum_cons, List.sum_nil, add_zero] at total
          simp [total]
      | cons b bs =>
          cases bs with
          | nil =>
              have ha : 0 < a := positive a (by simp)
              have hb : 0 < b := positive b (by simp)
              have hab : a ≠ b := by
                intro h
                exact (List.nodup_cons.mp nodup).1 (by simp [h])
              simp only [List.sum_cons, List.sum_nil, add_zero] at total
              have hc : (a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1) := by omega
              rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr rfl)
          | cons c cs =>
              have ha : 0 < a := positive a (by simp)
              have hb : 0 < b := positive b (by simp)
              have hc : 0 < c := positive c (by simp)
              have hna := (List.nodup_cons.mp nodup).1
              have htail := (List.nodup_cons.mp nodup).2
              have hnb := (List.nodup_cons.mp htail).1
              have hab : a ≠ b := by intro h; exact hna (by simp [h])
              have hac : a ≠ c := by intro h; exact hna (by simp [h])
              have hbc : b ≠ c := by intro h; exact hnb (by simp [h])
              simp only [List.sum_cons] at total
              omega

private theorem positive_nodup_sum_five_shape {weights : List ℕ}
    (positive : ∀ w ∈ weights, 0 < w)
    (nodup : weights.Nodup) (total : weights.sum = 5) :
    weights = [5] ∨
    weights = [1, 4] ∨ weights = [4, 1] ∨
    weights = [2, 3] ∨ weights = [3, 2] := by
  cases weights with
  | nil => simp at total
  | cons a as =>
      cases as with
      | nil =>
          left
          simp only [List.sum_cons, List.sum_nil, add_zero] at total
          simp [total]
      | cons b bs =>
          cases bs with
          | nil =>
              have ha : 0 < a := positive a (by simp)
              have hb : 0 < b := positive b (by simp)
              have hab : a ≠ b := by
                intro h
                exact (List.nodup_cons.mp nodup).1 (by simp [h])
              simp only [List.sum_cons, List.sum_nil, add_zero] at total
              have hcases :
                  (a = 1 ∧ b = 4) ∨ (a = 4 ∧ b = 1) ∨
                  (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) := by omega
              rcases hcases with h | h | h | h <;> rcases h with ⟨rfl, rfl⟩
              · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr (Or.inl rfl))
              · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
              · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
          | cons c cs =>
              have ha : 0 < a := positive a (by simp)
              have hb : 0 < b := positive b (by simp)
              have hc : 0 < c := positive c (by simp)
              have hna := (List.nodup_cons.mp nodup).1
              have htail := (List.nodup_cons.mp nodup).2
              have hnb := (List.nodup_cons.mp htail).1
              have hab : a ≠ b := by intro h; exact hna (by simp [h])
              have hac : a ≠ c := by intro h; exact hna (by simp [h])
              have hbc : b ≠ c := by intro h; exact hnb (by simp [h])
              simp only [List.sum_cons] at total
              omega

private theorem positive_nodup_sum_six_shape {weights : List ℕ}
    (positive : ∀ w ∈ weights, 0 < w)
    (nodup : weights.Nodup) (total : weights.sum = 6) :
    weights = [6] ∨
    (weights = [1, 5] ∨ weights = [5, 1] ∨
      weights = [2, 4] ∨ weights = [4, 2]) ∨
    (weights = [1, 2, 3] ∨ weights = [3, 2, 1] ∨
      weights = [1, 3, 2] ∨ weights = [2, 3, 1] ∨
      weights = [2, 1, 3] ∨ weights = [3, 1, 2]) := by
  cases weights with
  | nil => simp at total
  | cons a as =>
      cases as with
      | nil =>
          left
          simp only [List.sum_cons, List.sum_nil, add_zero] at total
          simp [total]
      | cons b bs =>
          cases bs with
          | nil =>
              have ha : 0 < a := positive a (by simp)
              have hb : 0 < b := positive b (by simp)
              have hab : a ≠ b := by
                intro h
                exact (List.nodup_cons.mp nodup).1 (by simp [h])
              simp only [List.sum_cons, List.sum_nil, add_zero] at total
              have hcases :
                  (a = 1 ∧ b = 5) ∨ (a = 5 ∧ b = 1) ∨
                  (a = 2 ∧ b = 4) ∨ (a = 4 ∧ b = 2) := by omega
              right; left
              rcases hcases with h | h | h | h <;> rcases h with ⟨rfl, rfl⟩
              · exact Or.inl rfl
              · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr (Or.inl rfl))
              · exact Or.inr (Or.inr (Or.inr rfl))
          | cons c cs =>
              cases cs with
              | nil =>
                  have ha : 0 < a := positive a (by simp)
                  have hb : 0 < b := positive b (by simp)
                  have hc : 0 < c := positive c (by simp)
                  have hna := (List.nodup_cons.mp nodup).1
                  have htail := (List.nodup_cons.mp nodup).2
                  have hnb := (List.nodup_cons.mp htail).1
                  have hab : a ≠ b := by intro h; exact hna (by simp [h])
                  have hac : a ≠ c := by intro h; exact hna (by simp [h])
                  have hbc : b ≠ c := by intro h; exact hnb (by simp [h])
                  simp only [List.sum_cons, List.sum_nil, add_zero] at total
                  have hcases :
                      (a = 1 ∧ b = 2 ∧ c = 3) ∨
                      (a = 3 ∧ b = 2 ∧ c = 1) ∨
                      (a = 1 ∧ b = 3 ∧ c = 2) ∨
                      (a = 2 ∧ b = 3 ∧ c = 1) ∨
                      (a = 2 ∧ b = 1 ∧ c = 3) ∨
                      (a = 3 ∧ b = 1 ∧ c = 2) := by
                    have ha_le : a ≤ 3 := by omega
                    have hb_le : b ≤ 3 := by omega
                    interval_cases a <;> interval_cases b <;> omega
                  right; right
                  rcases hcases with h | h | h | h | h | h <;>
                    rcases h with ⟨rfl, rfl, rfl⟩
                  · exact Or.inl rfl
                  · exact Or.inr (Or.inl rfl)
                  · exact Or.inr (Or.inr (Or.inl rfl))
                  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
              | cons d ds =>
                  have ha : 0 < a := positive a (by simp)
                  have hb : 0 < b := positive b (by simp)
                  have hc : 0 < c := positive c (by simp)
                  have hd : 0 < d := positive d (by simp)
                  have hna := (List.nodup_cons.mp nodup).1
                  have hn1 := (List.nodup_cons.mp nodup).2
                  have hnb := (List.nodup_cons.mp hn1).1
                  have hn2 := (List.nodup_cons.mp hn1).2
                  have hnc := (List.nodup_cons.mp hn2).1
                  have hab : a ≠ b := by intro h; exact hna (by simp [h])
                  have hac : a ≠ c := by intro h; exact hna (by simp [h])
                  have had : a ≠ d := by intro h; exact hna (by simp [h])
                  have hbc : b ≠ c := by intro h; exact hnb (by simp [h])
                  have hbd : b ≠ d := by intro h; exact hnb (by simp [h])
                  have hcd : c ≠ d := by intro h; exact hnc (by simp [h])
                  simp only [List.sum_cons] at total
                  omega

private theorem positive_nodup_sum_seven_shape {weights : List ℕ}
    (positive : ∀ w ∈ weights, 0 < w)
    (nodup : weights.Nodup) (total : weights.sum = 7) :
    weights = [7] ∨
    (weights = [1, 6] ∨ weights = [6, 1] ∨
      weights = [2, 5] ∨ weights = [5, 2] ∨
      weights = [3, 4] ∨ weights = [4, 3]) ∨
    (weights = [1, 2, 4] ∨ weights = [4, 2, 1] ∨
      weights = [1, 4, 2] ∨ weights = [2, 4, 1] ∨
      weights = [2, 1, 4] ∨ weights = [4, 1, 2]) := by
  cases weights with
  | nil => simp at total
  | cons a as =>
      cases as with
      | nil =>
          left
          simp only [List.sum_cons, List.sum_nil, add_zero] at total
          simp [total]
      | cons b bs =>
          cases bs with
          | nil =>
              have ha : 0 < a := positive a (by simp)
              have hb : 0 < b := positive b (by simp)
              have hab : a ≠ b := by
                intro h
                exact (List.nodup_cons.mp nodup).1 (by simp [h])
              simp only [List.sum_cons, List.sum_nil, add_zero] at total
              have hcases :
                  (a = 1 ∧ b = 6) ∨ (a = 6 ∧ b = 1) ∨
                  (a = 2 ∧ b = 5) ∨ (a = 5 ∧ b = 2) ∨
                  (a = 3 ∧ b = 4) ∨ (a = 4 ∧ b = 3) := by omega
              right; left
              rcases hcases with h | h | h | h | h | h <;>
                rcases h with ⟨rfl, rfl⟩
              · exact Or.inl rfl
              · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr (Or.inl rfl))
              · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
          | cons c cs =>
              cases cs with
              | nil =>
                  have ha : 0 < a := positive a (by simp)
                  have hb : 0 < b := positive b (by simp)
                  have hc : 0 < c := positive c (by simp)
                  have hna := (List.nodup_cons.mp nodup).1
                  have htail := (List.nodup_cons.mp nodup).2
                  have hnb := (List.nodup_cons.mp htail).1
                  have hab : a ≠ b := by intro h; exact hna (by simp [h])
                  have hac : a ≠ c := by intro h; exact hna (by simp [h])
                  have hbc : b ≠ c := by intro h; exact hnb (by simp [h])
                  simp only [List.sum_cons, List.sum_nil, add_zero] at total
                  have hcases :
                      (a = 1 ∧ b = 2 ∧ c = 4) ∨
                      (a = 4 ∧ b = 2 ∧ c = 1) ∨
                      (a = 1 ∧ b = 4 ∧ c = 2) ∨
                      (a = 2 ∧ b = 4 ∧ c = 1) ∨
                      (a = 2 ∧ b = 1 ∧ c = 4) ∨
                      (a = 4 ∧ b = 1 ∧ c = 2) := by
                    have ha_le : a ≤ 4 := by omega
                    have hb_le : b ≤ 4 := by omega
                    interval_cases a <;> interval_cases b <;> omega
                  right; right
                  rcases hcases with h | h | h | h | h | h <;>
                    rcases h with ⟨rfl, rfl, rfl⟩
                  · exact Or.inl rfl
                  · exact Or.inr (Or.inl rfl)
                  · exact Or.inr (Or.inr (Or.inl rfl))
                  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
              | cons d ds =>
                  have ha : 0 < a := positive a (by simp)
                  have hb : 0 < b := positive b (by simp)
                  have hc : 0 < c := positive c (by simp)
                  have hd : 0 < d := positive d (by simp)
                  have hna := (List.nodup_cons.mp nodup).1
                  have hn1 := (List.nodup_cons.mp nodup).2
                  have hnb := (List.nodup_cons.mp hn1).1
                  have hn2 := (List.nodup_cons.mp hn1).2
                  have hnc := (List.nodup_cons.mp hn2).1
                  have hab : a ≠ b := by intro h; exact hna (by simp [h])
                  have hac : a ≠ c := by intro h; exact hna (by simp [h])
                  have had : a ≠ d := by intro h; exact hna (by simp [h])
                  have hbc : b ≠ c := by intro h; exact hnb (by simp [h])
                  have hbd : b ≠ d := by intro h; exact hnb (by simp [h])
                  have hcd : c ≠ d := by intro h; exact hnc (by simp [h])
                  simp only [List.sum_cons] at total
                  omega

private theorem weightFourPath_shape (hL : IsLeech T)
    {u v : Fin n} (p : T.graph.Path u v)
    (htotal : T.walkWeight p.1 = 4) :
    (∃ e4 : T.Edge, T.weight e4 = 4) ∨
    (∃ e1 e3 : T.Edge,
      T.weight e1 = 1 ∧ T.weight e3 = 3 ∧ T.EdgeAdjacent e1 e3) := by
  have hsum : (pathWeightList (T := T) p).sum = 4 := by
    rw [pathWeightList_sum]
    exact htotal
  rcases positive_nodup_sum_four_shape
      (pathWeightList_positive (T := T) p)
      (pathWeightList_nodup hL p) hsum with h4 | h13 | h31
  · exact Or.inl (physicalEdge_of_pathWeightList_singleton p h4)
  · exact Or.inr (adjacentEdges_of_pathWeightList_pair p h13)
  · obtain ⟨e3, e1, h3, h1, hadj⟩ :=
      adjacentEdges_of_pathWeightList_pair p h31
    exact Or.inr ⟨e1, e3, h1, h3,
      (T.edgeAdjacent_comm e3 e1).1 hadj⟩

private theorem weightFivePath_shape (hL : IsLeech T)
    {u v : Fin n} (p : T.graph.Path u v)
    (htotal : T.walkWeight p.1 = 5) :
    (∃ e5 : T.Edge, T.weight e5 = 5) ∨
    (∃ e1 e4 : T.Edge,
      T.weight e1 = 1 ∧ T.weight e4 = 4 ∧ T.EdgeAdjacent e1 e4) ∨
    (∃ e2 e3 : T.Edge,
      T.weight e2 = 2 ∧ T.weight e3 = 3 ∧ T.EdgeAdjacent e2 e3) := by
  have hsum : (pathWeightList (T := T) p).sum = 5 := by
    rw [pathWeightList_sum]
    exact htotal
  rcases positive_nodup_sum_five_shape
      (pathWeightList_positive (T := T) p)
      (pathWeightList_nodup hL p) hsum with
    h5 | h14 | h41 | h23 | h32
  · exact Or.inl (physicalEdge_of_pathWeightList_singleton p h5)
  · exact Or.inr (Or.inl (adjacentEdges_of_pathWeightList_pair p h14))
  · obtain ⟨e4, e1, h4, h1, hadj⟩ :=
      adjacentEdges_of_pathWeightList_pair p h41
    exact Or.inr (Or.inl ⟨e1, e4, h1, h4,
      (T.edgeAdjacent_comm e4 e1).1 hadj⟩)
  · exact Or.inr (Or.inr (adjacentEdges_of_pathWeightList_pair p h23))
  · obtain ⟨e3, e2, h3, h2, hadj⟩ :=
      adjacentEdges_of_pathWeightList_pair p h32
    exact Or.inr (Or.inr ⟨e2, e3, h2, h3,
      (T.edgeAdjacent_comm e3 e2).1 hadj⟩)

private theorem weightSixPath_shape (hL : IsLeech T)
    {u v : Fin n} (p : T.graph.Path u v)
    (htotal : T.walkWeight p.1 = 6) :
    (∃ e6 : T.Edge, T.weight e6 = 6) ∨
    (∃ e1 e5 : T.Edge,
      T.weight e1 = 1 ∧ T.weight e5 = 5 ∧ T.EdgeAdjacent e1 e5) ∨
    (∃ e2 e4 : T.Edge,
      T.weight e2 = 2 ∧ T.weight e4 = 4 ∧ T.EdgeAdjacent e2 e4) ∨
    (∃ e1 e2 e3 : T.Edge,
      T.weight e1 = 1 ∧ T.weight e2 = 2 ∧ T.weight e3 = 3 ∧
      T.ThreeEdgePathArrangement e1 e2 e3) := by
  have hsum : (pathWeightList (T := T) p).sum = 6 := by
    rw [pathWeightList_sum]
    exact htotal
  rcases positive_nodup_sum_six_shape
      (pathWeightList_positive (T := T) p)
      (pathWeightList_nodup hL p) hsum with h6 | hpairs | htriples
  · exact Or.inl (physicalEdge_of_pathWeightList_singleton p h6)
  · rcases hpairs with h15 | h51 | h24 | h42
    · exact Or.inr (Or.inl (adjacentEdges_of_pathWeightList_pair p h15))
    · obtain ⟨e5, e1, h5, h1, hadj⟩ :=
        adjacentEdges_of_pathWeightList_pair p h51
      exact Or.inr (Or.inl ⟨e1, e5, h1, h5,
        (T.edgeAdjacent_comm e5 e1).1 hadj⟩)
    · exact Or.inr (Or.inr (Or.inl
        (adjacentEdges_of_pathWeightList_pair p h24)))
    · obtain ⟨e4, e2, h4, h2, hadj⟩ :=
        adjacentEdges_of_pathWeightList_pair p h42
      exact Or.inr (Or.inr (Or.inl ⟨e2, e4, h2, h4,
        (T.edgeAdjacent_comm e4 e2).1 hadj⟩))
  · rcases htriples with h123 | h321 | h132 | h231 | h213 | h312
    · obtain ⟨e1, e2, e3, h1, h2, h3, hc⟩ :=
        chainEdges_of_pathWeightList_triple p h123
      exact Or.inr (Or.inr (Or.inr ⟨e1, e2, e3, h1, h2, h3, Or.inl hc⟩))
    · obtain ⟨e3, e2, e1, h3, h2, h1, hc⟩ :=
        chainEdges_of_pathWeightList_triple p h321
      exact Or.inr (Or.inr (Or.inr ⟨e1, e2, e3, h1, h2, h3,
        Or.inl ((T.edgeChain_reverse e1 e2 e3).2 hc)⟩))
    · obtain ⟨e1, e3, e2, h1, h3, h2, hc⟩ :=
        chainEdges_of_pathWeightList_triple p h132
      exact Or.inr (Or.inr (Or.inr ⟨e1, e2, e3, h1, h2, h3,
        Or.inr (Or.inl hc)⟩))
    · obtain ⟨e2, e3, e1, h2, h3, h1, hc⟩ :=
        chainEdges_of_pathWeightList_triple p h231
      exact Or.inr (Or.inr (Or.inr ⟨e1, e2, e3, h1, h2, h3,
        Or.inr (Or.inl ((T.edgeChain_reverse e1 e3 e2).2 hc))⟩))
    · obtain ⟨e2, e1, e3, h2, h1, h3, hc⟩ :=
        chainEdges_of_pathWeightList_triple p h213
      exact Or.inr (Or.inr (Or.inr ⟨e1, e2, e3, h1, h2, h3,
        Or.inr (Or.inr hc)⟩))
    · obtain ⟨e3, e1, e2, h3, h1, h2, hc⟩ :=
        chainEdges_of_pathWeightList_triple p h312
      exact Or.inr (Or.inr (Or.inr ⟨e1, e2, e3, h1, h2, h3,
        Or.inr (Or.inr ((T.edgeChain_reverse e2 e1 e3).2 hc))⟩))

private theorem weightSevenPath_shape (hL : IsLeech T)
    {u v : Fin n} (p : T.graph.Path u v)
    (htotal : T.walkWeight p.1 = 7) :
    (∃ e7 : T.Edge, T.weight e7 = 7) ∨
    (∃ e1 e6 : T.Edge,
      T.weight e1 = 1 ∧ T.weight e6 = 6 ∧ T.EdgeAdjacent e1 e6) ∨
    (∃ e2 e5 : T.Edge,
      T.weight e2 = 2 ∧ T.weight e5 = 5 ∧ T.EdgeAdjacent e2 e5) ∨
    (∃ e3 e4 : T.Edge,
      T.weight e3 = 3 ∧ T.weight e4 = 4 ∧ T.EdgeAdjacent e3 e4) ∨
    (∃ e1 e2 e4 : T.Edge,
      T.weight e1 = 1 ∧ T.weight e2 = 2 ∧ T.weight e4 = 4 ∧
      T.ThreeEdgePathArrangement e1 e2 e4) := by
  have hsum : (pathWeightList (T := T) p).sum = 7 := by
    rw [pathWeightList_sum]
    exact htotal
  rcases positive_nodup_sum_seven_shape
      (pathWeightList_positive (T := T) p)
      (pathWeightList_nodup hL p) hsum with h7 | hpairs | htriples
  · exact Or.inl (physicalEdge_of_pathWeightList_singleton p h7)
  · rcases hpairs with h16 | h61 | h25 | h52 | h34 | h43
    · exact Or.inr (Or.inl (adjacentEdges_of_pathWeightList_pair p h16))
    · obtain ⟨e6, e1, h6, h1, hadj⟩ :=
        adjacentEdges_of_pathWeightList_pair p h61
      exact Or.inr (Or.inl ⟨e1, e6, h1, h6,
        (T.edgeAdjacent_comm e6 e1).1 hadj⟩)
    · exact Or.inr (Or.inr (Or.inl
        (adjacentEdges_of_pathWeightList_pair p h25)))
    · obtain ⟨e5, e2, h5, h2, hadj⟩ :=
        adjacentEdges_of_pathWeightList_pair p h52
      exact Or.inr (Or.inr (Or.inl ⟨e2, e5, h2, h5,
        (T.edgeAdjacent_comm e5 e2).1 hadj⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        (adjacentEdges_of_pathWeightList_pair p h34))))
    · obtain ⟨e4, e3, h4, h3, hadj⟩ :=
        adjacentEdges_of_pathWeightList_pair p h43
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e3, e4, h3, h4,
        (T.edgeAdjacent_comm e4 e3).1 hadj⟩)))
  · rcases htriples with h124 | h421 | h142 | h241 | h214 | h412
    · obtain ⟨e1, e2, e4, h1, h2, h4, hc⟩ :=
        chainEdges_of_pathWeightList_triple p h124
      exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨e1, e2, e4, h1, h2, h4, Or.inl hc⟩)))
    · obtain ⟨e4, e2, e1, h4, h2, h1, hc⟩ :=
        chainEdges_of_pathWeightList_triple p h421
      exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨e1, e2, e4, h1, h2, h4,
          Or.inl ((T.edgeChain_reverse e1 e2 e4).2 hc)⟩)))
    · obtain ⟨e1, e4, e2, h1, h4, h2, hc⟩ :=
        chainEdges_of_pathWeightList_triple p h142
      exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨e1, e2, e4, h1, h2, h4, Or.inr (Or.inl hc)⟩)))
    · obtain ⟨e2, e4, e1, h2, h4, h1, hc⟩ :=
        chainEdges_of_pathWeightList_triple p h241
      exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨e1, e2, e4, h1, h2, h4,
          Or.inr (Or.inl ((T.edgeChain_reverse e1 e4 e2).2 hc))⟩)))
    · obtain ⟨e2, e1, e4, h2, h1, h4, hc⟩ :=
        chainEdges_of_pathWeightList_triple p h214
      exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨e1, e2, e4, h1, h2, h4, Or.inr (Or.inr hc)⟩)))
    · obtain ⟨e4, e1, e2, h4, h1, h2, hc⟩ :=
        chainEdges_of_pathWeightList_triple p h412
      exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨e1, e2, e4, h1, h2, h4,
          Or.inr (Or.inr ((T.edgeChain_reverse e2 e1 e4).2 hc))⟩)))

private theorem arrangement123_of_triple_shape
    {u v : Fin n} (p : T.graph.Path u v)
    (h : pathWeightList (T := T) p = [1, 2, 3] ∨
      pathWeightList (T := T) p = [3, 2, 1] ∨
      pathWeightList (T := T) p = [1, 3, 2] ∨
      pathWeightList (T := T) p = [2, 3, 1] ∨
      pathWeightList (T := T) p = [2, 1, 3] ∨
      pathWeightList (T := T) p = [3, 1, 2]) :
    ∃ e1 e2 e3 : T.Edge,
      T.weight e1 = 1 ∧ T.weight e2 = 2 ∧ T.weight e3 = 3 ∧
      T.ThreeEdgePathArrangement e1 e2 e3 := by
  rcases h with h123 | h321 | h132 | h231 | h213 | h312
  · obtain ⟨e1, e2, e3, h1, h2, h3, hc⟩ :=
      chainEdges_of_pathWeightList_triple p h123
    exact ⟨e1, e2, e3, h1, h2, h3, Or.inl hc⟩
  · obtain ⟨e3, e2, e1, h3, h2, h1, hc⟩ :=
      chainEdges_of_pathWeightList_triple p h321
    exact ⟨e1, e2, e3, h1, h2, h3,
      Or.inl ((T.edgeChain_reverse e1 e2 e3).2 hc)⟩
  · obtain ⟨e1, e3, e2, h1, h3, h2, hc⟩ :=
      chainEdges_of_pathWeightList_triple p h132
    exact ⟨e1, e2, e3, h1, h2, h3, Or.inr (Or.inl hc)⟩
  · obtain ⟨e2, e3, e1, h2, h3, h1, hc⟩ :=
      chainEdges_of_pathWeightList_triple p h231
    exact ⟨e1, e2, e3, h1, h2, h3,
      Or.inr (Or.inl ((T.edgeChain_reverse e1 e3 e2).2 hc))⟩
  · obtain ⟨e2, e1, e3, h2, h1, h3, hc⟩ :=
      chainEdges_of_pathWeightList_triple p h213
    exact ⟨e1, e2, e3, h1, h2, h3, Or.inr (Or.inr hc)⟩
  · obtain ⟨e3, e1, e2, h3, h1, h2, hc⟩ :=
      chainEdges_of_pathWeightList_triple p h312
    exact ⟨e1, e2, e3, h1, h2, h3,
      Or.inr (Or.inr ((T.edgeChain_reverse e2 e1 e3).2 hc))⟩

private theorem arrangement124_of_triple_shape
    {u v : Fin n} (p : T.graph.Path u v)
    (h : pathWeightList (T := T) p = [1, 2, 4] ∨
      pathWeightList (T := T) p = [4, 2, 1] ∨
      pathWeightList (T := T) p = [1, 4, 2] ∨
      pathWeightList (T := T) p = [2, 4, 1] ∨
      pathWeightList (T := T) p = [2, 1, 4] ∨
      pathWeightList (T := T) p = [4, 1, 2]) :
    ∃ e1 e2 e4 : T.Edge,
      T.weight e1 = 1 ∧ T.weight e2 = 2 ∧ T.weight e4 = 4 ∧
      T.ThreeEdgePathArrangement e1 e2 e4 := by
  rcases h with h124 | h421 | h142 | h241 | h214 | h412
  · obtain ⟨e1, e2, e4, h1, h2, h4, hc⟩ :=
      chainEdges_of_pathWeightList_triple p h124
    exact ⟨e1, e2, e4, h1, h2, h4, Or.inl hc⟩
  · obtain ⟨e4, e2, e1, h4, h2, h1, hc⟩ :=
      chainEdges_of_pathWeightList_triple p h421
    exact ⟨e1, e2, e4, h1, h2, h4,
      Or.inl ((T.edgeChain_reverse e1 e2 e4).2 hc)⟩
  · obtain ⟨e1, e4, e2, h1, h4, h2, hc⟩ :=
      chainEdges_of_pathWeightList_triple p h142
    exact ⟨e1, e2, e4, h1, h2, h4, Or.inr (Or.inl hc)⟩
  · obtain ⟨e2, e4, e1, h2, h4, h1, hc⟩ :=
      chainEdges_of_pathWeightList_triple p h241
    exact ⟨e1, e2, e4, h1, h2, h4,
      Or.inr (Or.inl ((T.edgeChain_reverse e1 e4 e2).2 hc))⟩
  · obtain ⟨e2, e1, e4, h2, h1, h4, hc⟩ :=
      chainEdges_of_pathWeightList_triple p h214
    exact ⟨e1, e2, e4, h1, h2, h4, Or.inr (Or.inr hc)⟩
  · obtain ⟨e4, e1, e2, h4, h1, h2, hc⟩ :=
      chainEdges_of_pathWeightList_triple p h412
    exact ⟨e1, e2, e4, h1, h2, h4,
      Or.inr (Or.inr ((T.edgeChain_reverse e2 e1 e4).2 hc))⟩

/-! ## Target paths, prefix membership, and bounded three-edge prefixes -/

private theorem rank_mem_target_of_five_le (hn : 5 ≤ n) {k : ℕ}
    (hkpos : 1 ≤ k) (hkle : k ≤ 10) :
    k ∈ Finset.Icc 1 (targetN n) := by
  rw [Finset.mem_Icc]
  refine ⟨hkpos, ?_⟩
  have hc : Nat.choose 5 2 ≤ Nat.choose n 2 := Nat.choose_le_choose 2 hn
  norm_num [targetN, Nat.choose] at hc ⊢
  omega

private theorem target_path_of_rank (hL : IsLeech T) (k : ℕ)
    (hk : k ∈ Finset.Icc 1 (targetN n)) :
    ∃ u v : Fin n, ∃ p : T.graph.Path u v,
      T.walkWeight p.1 = k := by
  obtain ⟨q, hq, _⟩ := hL.target_existsUnique k hk
  refine ⟨q.left, q.right, T.path q.left q.right, ?_⟩
  calc
    T.walkWeight (T.path q.left q.right).1 = T.dist q.left q.right :=
      T.path_walkWeight_eq_dist (T.path q.left q.right)
    _ = T.pairDist q := rfl
    _ = k := hq

private theorem unique_physicalWeight (hL : IsLeech T)
    {k : ℕ} {e : T.Edge} (he : T.weight e = k) :
    ∀ f : T.Edge, T.weight f = k → f = e := by
  intro f hf
  exact t1_edge_weight_injective hL (hf.trans he.symm)

private theorem sequence_sum_mem_prefixInternalDistances
    {next : T.Edge} {weights : List ℕ}
    (hseq : HasPathWeightSequence T weights)
    (hne : weights ≠ [])
    (hbelow : ∀ w ∈ weights, w < T.weight next) :
    weights.sum ∈ T.prefixInternalDistances next := by
  classical
  obtain ⟨u, v, p, hp⟩ := hseq
  have huv : u ≠ v := path_endpoints_ne_of_weightList_nonempty p (hp ▸ hne)
  let q : VertexPair n := VertexPair.ofDistinct u v huv
  have hcanonical : p = T.path u v := T.path_unique p
  have hpairPath :
      T.pathEdges q.left q.right = T.pathEdges u v := by
    apply Finset.ext
    intro z
    by_cases horder : u < v
    · simp [q, VertexPair.ofDistinct, horder, VertexPair.left, VertexPair.right]
    · simp [q, VertexPair.ofDistinct, horder, VertexPair.left, VertexPair.right,
        T.pathEdges_comm]
  have hinternal : T.PrefixInternal next q :=
    (T.prefixInternal_iff_path_lighter next q).2 <| by
      intro f hf
      have hfuv : f ∈ T.pathEdges u v := by
        rw [← hpairPath]
        exact hf
      have hfp : f ∈ p.1.edges := by
        rw [hcanonical]
        simpa [PosIntTree.pathEdges] using hfuv
      have hmem : T.weightOfPair f ∈ pathWeightList (T := T) p := by
        rw [pathWeightList, List.mem_map]
        exact ⟨f, hfp, rfl⟩
      rw [hp] at hmem
      exact hbelow _ hmem
  rw [PosIntTree.prefixInternalDistances, Finset.mem_image]
  refine ⟨q, by simp [hinternal], ?_⟩
  calc
    T.pairDist q = T.dist u v := T.pairDist_pairOfDistinct u v huv
    _ = T.walkWeight p.1 := (T.path_walkWeight_eq_dist p).symm
    _ = (pathWeightList (T := T) p).sum := (pathWeightList_sum p).symm
    _ = weights.sum := by rw [hp]

private theorem prefix_pairDist_le_three_edges
    (next a b c : T.Edge)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hall : ∀ f : T.Edge, T.weight f < T.weight next →
      f = a ∨ f = b ∨ f = c)
    (p : VertexPair n) (hp : T.PrefixInternal next p) :
    T.pairDist p ≤ T.weight a + T.weight b + T.weight c := by
  classical
  have hsubset : T.pathEdges p.left p.right ⊆ {a.1, b.1, c.1} := by
    intro x hx
    let f : T.Edge := T.edgeOfPathMem x hx
    have hlt := (T.prefixInternal_iff_path_lighter next p).1 hp x hx
    have hfw : T.weight f < T.weight next := by
      simpa [f] using hlt
    rcases hall f hfw with rfl | rfl | rfl <;> simp [f]
  have hsum :
      (∑ x ∈ T.pathEdges p.left p.right, T.weightOfPair x) ≤
        ∑ x ∈ ({a.1, b.1, c.1} : Finset (Sym2 (Fin n))),
          T.weightOfPair x := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun _ _ _ => Nat.zero_le _)
  have habv : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
  have hacv : a.1 ≠ c.1 := fun h => hac (Subtype.ext h)
  have hbcv : b.1 ≠ c.1 := fun h => hbc (Subtype.ext h)
  change (∑ x ∈ T.pathEdges p.left p.right, T.weightOfPair x) ≤ _
  simpa [habv, hacv, hbcv, T.weightOfPair_edge, add_assoc] using hsum

private theorem edgeList_below_next {next : T.Edge} {u v : Fin n}
    (huv : u ≠ v) (p : T.graph.Path u v)
    (hp : T.PrefixInternal next (VertexPair.ofDistinct u v huv)) :
    ∀ w ∈ pathWeightList (T := T) p, w < T.weight next := by
  intro w hw
  rw [pathWeightList, List.mem_map] at hw
  obtain ⟨x, hx, rfl⟩ := hw
  have hcanon : p = T.path u v := T.path_unique p
  have hfin : x ∈ T.pathEdges u v := by
    unfold PosIntTree.pathEdges
    rw [← hcanon]
    simpa using hx
  have hpairPath :
      T.pathEdges (VertexPair.ofDistinct u v huv).left
          (VertexPair.ofDistinct u v huv).right =
        T.pathEdges u v := by
    apply Finset.ext
    intro z
    by_cases huv : u < v
    · simp [VertexPair.ofDistinct, huv, VertexPair.left, VertexPair.right]
    · simp [VertexPair.ofDistinct, huv, VertexPair.left, VertexPair.right,
        T.pathEdges_comm]
  have hxpair : x ∈ T.pathEdges
      (VertexPair.ofDistinct u v huv).left
      (VertexPair.ofDistinct u v huv).right := by
    rw [hpairPath]
    exact hfin
  exact (T.prefixInternal_iff_path_lighter _ _).1 hp x hxpair

private theorem pairPathWeightList_below_next {next : T.Edge}
    (p : VertexPair n) (hp : T.PrefixInternal next p) :
    ∀ w ∈ pathWeightList (T := T) (T.path p.left p.right),
      w < T.weight next := by
  intro w hw
  rw [pathWeightList, List.mem_map] at hw
  obtain ⟨x, hx, rfl⟩ := hw
  have hfin : x ∈ T.pathEdges p.left p.right := by
    simpa [PosIntTree.pathEdges] using hx
  exact (T.prefixInternal_iff_path_lighter next p).1 hp x hfin

private theorem physicalEdge_of_mem_pathWeightList
    {u v : Fin n} (p : T.graph.Path u v) {k : ℕ}
    (hk : k ∈ pathWeightList (T := T) p) :
    ∃ e : T.Edge, T.weight e = k := by
  rw [pathWeightList, List.mem_map] at hk
  obtain ⟨x, hx, hxw⟩ := hk
  let e : T.Edge := ⟨x, p.1.edges_subset_edgeSet hx⟩
  refine ⟨e, ?_⟩
  rw [← T.weightOfPair_edge e]
  exact hxw

private theorem chosen_weight_not_prefix (hL : IsLeech T) (e : T.Edge) :
    T.weight e ∉ T.prefixInternalDistances e := by
  rw [← T.t2_forced_mex hL e]
  exact PosIntTree.mexPos_not_mem _

private theorem physical_sequence_mem_prefix {e next : T.Edge}
    (hlt : T.weight e < T.weight next) :
    T.weight e ∈ T.prefixInternalDistances next := by
  have hseq := edge_hasPathWeightSequence (T := T) e
  simpa using sequence_sum_mem_prefixInternalDistances
    (next := next) hseq (by simp) (by simpa using hlt)

private theorem pair_sequence_mem_prefix {e f next : T.Edge}
    (hadj : T.EdgeAdjacent e f)
    (helt : T.weight e < T.weight next)
    (hflt : T.weight f < T.weight next) :
    T.weight e + T.weight f ∈ T.prefixInternalDistances next := by
  have hseq := edgeAdjacent_hasPathWeightSequence (T := T) e f hadj
  simpa using sequence_sum_mem_prefixInternalDistances
    (next := next) hseq (by simp) (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact helt
      · exact hflt)

private theorem chain_sequence_mem_prefix {e f g next : T.Edge}
    (hchain : T.EdgeChain e f g)
    (helt : T.weight e < T.weight next)
    (hflt : T.weight f < T.weight next)
    (hglt : T.weight g < T.weight next) :
    T.weight e + T.weight f + T.weight g ∈
      T.prefixInternalDistances next := by
  have hseq := edgeChain_hasPathWeightSequence (T := T) e f g hchain
  simpa [add_assoc] using sequence_sum_mem_prefixInternalDistances
    (next := next) hseq (by simp) (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact helt
      · exact hflt
      · exact hglt)

private theorem arrangement_impossible_of_third_disjoint
    {a b c : T.Edge}
    (hca : T.EdgeEndpointDisjoint c a)
    (hcb : T.EdgeEndpointDisjoint c b) :
    ¬T.ThreeEdgePathArrangement a b c := by
  rintro (h | h | h)
  · obtain ⟨_, hbc, _⟩ := h
    obtain ⟨v, hvb, hvc⟩ := hbc.2
    exact hcb v hvc hvb
  · obtain ⟨hac, _, _⟩ := h
    obtain ⟨v, hva, hvc⟩ := hac.2
    exact hca v hvc hva
  · obtain ⟨_, hac, _⟩ := h
    obtain ⟨v, hva, hvc⟩ := hac.2
    exact hca v hvc hva

private theorem arrangement_impossible_of_first_disjoint
    {a b c : T.Edge}
    (hab : T.EdgeEndpointDisjoint a b)
    (hac : T.EdgeEndpointDisjoint a c) :
    ¬T.ThreeEdgePathArrangement a b c := by
  rintro (h | h | h)
  · obtain ⟨hab', _, _⟩ := h
    obtain ⟨v, hva, hvb⟩ := hab'.2
    exact hab v hva hvb
  · obtain ⟨hac', _, _⟩ := h
    obtain ⟨v, hva, hvc⟩ := hac'.2
    exact hac v hva hvc
  · obtain ⟨hba, _, _⟩ := h
    obtain ⟨v, hvb, hva⟩ := hba.2
    exact hab v hva hvb

private theorem arrangement_impossible_of_second_disjoint
    {a b c : T.Edge}
    (hba : T.EdgeEndpointDisjoint b a)
    (hbc : T.EdgeEndpointDisjoint b c) :
    ¬T.ThreeEdgePathArrangement a b c := by
  rintro (h | h | h)
  · obtain ⟨hab, _, _⟩ := h
    obtain ⟨v, hva, hvb⟩ := hab.2
    exact hba v hvb hva
  · obtain ⟨_, hcb, _⟩ := h
    obtain ⟨v, hvc, hvb⟩ := hcb.2
    exact hbc v hvb hvc
  · obtain ⟨hba', _, _⟩ := h
    obtain ⟨v, hvb, hva⟩ := hba'.2
    exact hba v hvb hva

private theorem arrangement_impossible_of_pairwise_adjacent
    {a b c : T.Edge}
    (hab : T.EdgeAdjacent a b) (hac : T.EdgeAdjacent a c)
    (hbc : T.EdgeAdjacent b c) :
    ¬T.ThreeEdgePathArrangement a b c := by
  rintro (h | h | h)
  · obtain ⟨_, _, hacDis⟩ := h
    obtain ⟨v, hva, hvc⟩ := hac.2
    exact hacDis v hva hvc
  · obtain ⟨_, _, habDis⟩ := h
    obtain ⟨v, hva, hvb⟩ := hab.2
    exact habDis v hva hvb
  · obtain ⟨_, _, hbcDis⟩ := h
    obtain ⟨v, hvb, hvc⟩ := hbc.2
    exact hbcDis v hvb hvc

private theorem prefix_member_witness {next : T.Edge} {k : ℕ}
    (hk : k ∈ T.prefixInternalDistances next) :
    ∃ p : VertexPair n, T.PrefixInternal next p ∧ T.pairDist p = k := by
  classical
  rw [PosIntTree.prefixInternalDistances, Finset.mem_image] at hk
  obtain ⟨p, hp, hpk⟩ := hk
  exact ⟨p, (Finset.mem_filter.mp hp).2, hpk⟩

private theorem prefix_member_pos (hL : IsLeech T) {next : T.Edge} {k : ℕ}
    (hk : k ∈ T.prefixInternalDistances next) : 0 < k := by
  obtain ⟨p, _, hp⟩ := prefix_member_witness hk
  rw [← hp]
  exact hL.pairDist_pos p

private theorem prefix_member_path_data {next : T.Edge} {k : ℕ}
    (hk : k ∈ T.prefixInternalDistances next) :
    ∃ p : VertexPair n,
      T.PrefixInternal next p ∧
      (pathWeightList (T := T) (T.path p.left p.right)).sum = k ∧
      (∀ w ∈ pathWeightList (T := T) (T.path p.left p.right),
        w < T.weight next) := by
  obtain ⟨p, hp, hpk⟩ := prefix_member_witness hk
  refine ⟨p, hp, ?_, pairPathWeightList_below_next p hp⟩
  calc
    (pathWeightList (T := T) (T.path p.left p.right)).sum =
        T.walkWeight (T.path p.left p.right).1 := pathWeightList_sum _
    _ = T.dist p.left p.right :=
      T.path_walkWeight_eq_dist (T.path p.left p.right)
    _ = T.pairDist p := rfl
    _ = k := hpk

private theorem adjacent_known_lighter
    (hL : IsLeech T) {e1 e2 e4 next : T.Edge}
    (h1 : T.weight e1 = 1) (h2 : T.weight e2 = 2)
    (h4 : T.weight e4 = 4)
    (hnext : T.weight next ≤ 7)
    (hno3 : ¬∃ e : T.Edge, T.weight e = 3)
    (hno5 : T.weight next ≤ 5 ∨ ¬∃ e : T.Edge, T.weight e = 5)
    (hno6 : T.weight next ≤ 6 ∨ ¬∃ e : T.Edge, T.weight e = 6) :
    ∀ f : T.Edge, T.weight f < T.weight next →
      f = e1 ∨ f = e2 ∨ f = e4 := by
  intro f hf
  have hfpos := T.weight_pos f
  have hw : T.weight f = 1 ∨ T.weight f = 2 ∨ T.weight f = 3 ∨
      T.weight f = 4 ∨ T.weight f = 5 ∨ T.weight f = 6 := by omega
  rcases hw with hw | hw | hw | hw | hw | hw
  · exact Or.inl (t1_edge_weight_injective hL (hw.trans h1.symm))
  · exact Or.inr (Or.inl (t1_edge_weight_injective hL (hw.trans h2.symm)))
  · exact (hno3 ⟨f, hw⟩).elim
  · exact Or.inr (Or.inr (t1_edge_weight_injective hL (hw.trans h4.symm)))
  · rcases hno5 with hle | hno
    · omega
    · exact (hno ⟨f, hw⟩).elim
  · rcases hno6 with hle | hno
    · omega
    · exact (hno ⟨f, hw⟩).elim

private theorem disjoint_known_lighter
    (hL : IsLeech T) {e1 e2 e3 next : T.Edge}
    (h1 : T.weight e1 = 1) (h2 : T.weight e2 = 2)
    (h3 : T.weight e3 = 3)
    (hnext : T.weight next ≤ 7)
    (hno4 : T.weight next ≤ 4 ∨ ¬∃ e : T.Edge, T.weight e = 4)
    (hno5 : T.weight next ≤ 5 ∨ ¬∃ e : T.Edge, T.weight e = 5)
    (hno6 : T.weight next ≤ 6 ∨ ¬∃ e : T.Edge, T.weight e = 6) :
    ∀ f : T.Edge, T.weight f < T.weight next →
      f = e1 ∨ f = e2 ∨ f = e3 := by
  intro f hf
  have hfpos := T.weight_pos f
  have hw : T.weight f = 1 ∨ T.weight f = 2 ∨ T.weight f = 3 ∨
      T.weight f = 4 ∨ T.weight f = 5 ∨ T.weight f = 6 := by omega
  rcases hw with hw | hw | hw | hw | hw | hw
  · exact Or.inl (t1_edge_weight_injective hL (hw.trans h1.symm))
  · exact Or.inr (Or.inl (t1_edge_weight_injective hL (hw.trans h2.symm)))
  · exact Or.inr (Or.inr (t1_edge_weight_injective hL (hw.trans h3.symm)))
  · rcases hno4 with hle | hno
    · omega
    · exact (hno ⟨f, hw⟩).elim
  · rcases hno5 with hle | hno
    · omega
    · exact (hno ⟨f, hw⟩).elim
  · rcases hno6 with hle | hno
    · omega
    · exact (hno ⟨f, hw⟩).elim

private theorem adjacent_meets_one_prefix_spectrum
    (hL : IsLeech T) (e1 e2 e4 e6 : T.Edge)
    (h1 : T.weight e1 = 1) (h2 : T.weight e2 = 2)
    (h4 : T.weight e4 = 4) (h6 : T.weight e6 = 6)
    (h12 : T.EdgeAdjacent e1 e2)
    (h41 : T.EdgeAdjacent e4 e1)
    (h42 : T.EdgeEndpointDisjoint e4 e2)
    (hno3 : ¬∃ e : T.Edge, T.weight e = 3)
    (hno5 : ¬∃ e : T.Edge, T.weight e = 5) :
    T.prefixInternalDistances e6 = {1, 2, 3, 4, 5, 7} := by
  classical
  have hne12 : e1 ≠ e2 := by intro h; have := congrArg T.weight h; omega
  have hne14 : e1 ≠ e4 := by intro h; have := congrArg T.weight h; omega
  have hne24 : e2 ≠ e4 := by intro h; have := congrArg T.weight h; omega
  have hall := adjacent_known_lighter hL h1 h2 h4 (by omega : T.weight e6 ≤ 7)
    hno3 (Or.inr hno5) (Or.inl (by omega : T.weight e6 ≤ 6))
  have hm1 : 1 ∈ T.prefixInternalDistances e6 := by
    simpa [h1, h6] using physical_sequence_mem_prefix (T := T)
      (e := e1) (next := e6) (by omega)
  have hm2 : 2 ∈ T.prefixInternalDistances e6 := by
    simpa [h2, h6] using physical_sequence_mem_prefix (T := T)
      (e := e2) (next := e6) (by omega)
  have hm4 : 4 ∈ T.prefixInternalDistances e6 := by
    simpa [h4, h6] using physical_sequence_mem_prefix (T := T)
      (e := e4) (next := e6) (by omega)
  have hm3 : 3 ∈ T.prefixInternalDistances e6 := by
    simpa [h1, h2, h6] using pair_sequence_mem_prefix (T := T)
      (next := e6) h12 (by omega) (by omega)
  have h14 : T.EdgeAdjacent e1 e4 := (T.edgeAdjacent_comm e4 e1).1 h41
  have hm5 : 5 ∈ T.prefixInternalDistances e6 := by
    simpa [h1, h4, h6] using pair_sequence_mem_prefix (T := T)
      (next := e6) h14 (by omega) (by omega)
  have hchain : T.EdgeChain e2 e1 e4 := by
    exact ⟨(T.edgeAdjacent_comm e1 e2).1 h12, h14,
      (T.edgeEndpointDisjoint_comm e4 e2).1 h42⟩
  have hm7 : 7 ∈ T.prefixInternalDistances e6 := by
    simpa [h1, h2, h4, h6, add_assoc] using
      chain_sequence_mem_prefix (T := T) (next := e6) hchain
        (by omega) (by omega) (by omega)
  have hnot6 : 6 ∉ T.prefixInternalDistances e6 := by
    simpa [h6] using chosen_weight_not_prefix hL e6
  ext k
  constructor
  · intro hk
    obtain ⟨p, hp, hpk⟩ := prefix_member_witness hk
    have hle := prefix_pairDist_le_three_edges e6 e1 e2 e4
      hne12 hne14 hne24 hall p hp
    rw [hpk, h1, h2, h4] at hle
    have hpos := prefix_member_pos hL hk
    have hne : k ≠ 6 := fun h => hnot6 (h ▸ hk)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · intro hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hm1
    · exact hm2
    · exact hm3
    · exact hm4
    · exact hm5
    · exact hm7

private theorem adjacent_meets_two_prefix_spectrum
    (hL : IsLeech T) (e1 e2 e4 e5 : T.Edge)
    (h1 : T.weight e1 = 1) (h2 : T.weight e2 = 2)
    (h4 : T.weight e4 = 4) (h5 : T.weight e5 = 5)
    (h12 : T.EdgeAdjacent e1 e2)
    (h41 : T.EdgeEndpointDisjoint e4 e1)
    (h42 : T.EdgeAdjacent e4 e2)
    (hno3 : ¬∃ e : T.Edge, T.weight e = 3) :
    T.prefixInternalDistances e5 = {1, 2, 3, 4, 6, 7} := by
  classical
  have hne12 : e1 ≠ e2 := by intro h; have := congrArg T.weight h; omega
  have hne14 : e1 ≠ e4 := by intro h; have := congrArg T.weight h; omega
  have hne24 : e2 ≠ e4 := by intro h; have := congrArg T.weight h; omega
  have hall := adjacent_known_lighter hL h1 h2 h4 (by omega : T.weight e5 ≤ 7)
    hno3 (Or.inl (by omega : T.weight e5 ≤ 5))
    (Or.inl (by omega : T.weight e5 ≤ 6))
  have hm1 : 1 ∈ T.prefixInternalDistances e5 := by
    simpa [h1, h5] using physical_sequence_mem_prefix (T := T)
      (e := e1) (next := e5) (by omega)
  have hm2 : 2 ∈ T.prefixInternalDistances e5 := by
    simpa [h2, h5] using physical_sequence_mem_prefix (T := T)
      (e := e2) (next := e5) (by omega)
  have hm4 : 4 ∈ T.prefixInternalDistances e5 := by
    simpa [h4, h5] using physical_sequence_mem_prefix (T := T)
      (e := e4) (next := e5) (by omega)
  have hm3 : 3 ∈ T.prefixInternalDistances e5 := by
    simpa [h1, h2, h5] using pair_sequence_mem_prefix (T := T)
      (next := e5) h12 (by omega) (by omega)
  have h24 : T.EdgeAdjacent e2 e4 := (T.edgeAdjacent_comm e4 e2).1 h42
  have hm6 : 6 ∈ T.prefixInternalDistances e5 := by
    simpa [h2, h4, h5] using pair_sequence_mem_prefix (T := T)
      (next := e5) h24 (by omega) (by omega)
  have hchain : T.EdgeChain e1 e2 e4 := by
    exact ⟨h12, h24, (T.edgeEndpointDisjoint_comm e4 e1).1 h41⟩
  have hm7 : 7 ∈ T.prefixInternalDistances e5 := by
    simpa [h1, h2, h4, h5, add_assoc] using
      chain_sequence_mem_prefix (T := T) (next := e5) hchain
        (by omega) (by omega) (by omega)
  have hnot5 : 5 ∉ T.prefixInternalDistances e5 := by
    simpa [h5] using chosen_weight_not_prefix hL e5
  ext k
  constructor
  · intro hk
    obtain ⟨p, hp, hpk⟩ := prefix_member_witness hk
    have hle := prefix_pairDist_le_three_edges e5 e1 e2 e4
      hne12 hne14 hne24 hall p hp
    rw [hpk, h1, h2, h4] at hle
    have hpos := prefix_member_pos hL hk
    have hne : k ≠ 5 := fun h => hnot5 (h ▸ hk)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · intro hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hm1
    · exact hm2
    · exact hm3
    · exact hm4
    · exact hm6
    · exact hm7

private theorem adjacent_meets_both_prefix_spectrum
    (hL : IsLeech T) (e1 e2 e4 e7 : T.Edge)
    (h1 : T.weight e1 = 1) (h2 : T.weight e2 = 2)
    (h4 : T.weight e4 = 4) (h7 : T.weight e7 = 7)
    (h12 : T.EdgeAdjacent e1 e2)
    (h41 : T.EdgeAdjacent e4 e1)
    (h42 : T.EdgeAdjacent e4 e2)
    (hno3 : ¬∃ e : T.Edge, T.weight e = 3)
    (hno5 : ¬∃ e : T.Edge, T.weight e = 5)
    (hno6 : ¬∃ e : T.Edge, T.weight e = 6) :
    T.prefixInternalDistances e7 = {1, 2, 3, 4, 5, 6} := by
  classical
  have hne12 : e1 ≠ e2 := by intro h; have := congrArg T.weight h; omega
  have hne14 : e1 ≠ e4 := by intro h; have := congrArg T.weight h; omega
  have hne24 : e2 ≠ e4 := by intro h; have := congrArg T.weight h; omega
  have hall := adjacent_known_lighter hL h1 h2 h4 (by omega : T.weight e7 ≤ 7)
    hno3 (Or.inr hno5) (Or.inr hno6)
  have hm1 : 1 ∈ T.prefixInternalDistances e7 := by
    simpa [h1, h7] using physical_sequence_mem_prefix (T := T)
      (e := e1) (next := e7) (by omega)
  have hm2 : 2 ∈ T.prefixInternalDistances e7 := by
    simpa [h2, h7] using physical_sequence_mem_prefix (T := T)
      (e := e2) (next := e7) (by omega)
  have hm4 : 4 ∈ T.prefixInternalDistances e7 := by
    simpa [h4, h7] using physical_sequence_mem_prefix (T := T)
      (e := e4) (next := e7) (by omega)
  have hm3 : 3 ∈ T.prefixInternalDistances e7 := by
    simpa [h1, h2, h7] using pair_sequence_mem_prefix (T := T)
      (next := e7) h12 (by omega) (by omega)
  have h14 : T.EdgeAdjacent e1 e4 := (T.edgeAdjacent_comm e4 e1).1 h41
  have h24 : T.EdgeAdjacent e2 e4 := (T.edgeAdjacent_comm e4 e2).1 h42
  have hm5 : 5 ∈ T.prefixInternalDistances e7 := by
    simpa [h1, h4, h7] using pair_sequence_mem_prefix (T := T)
      (next := e7) h14 (by omega) (by omega)
  have hm6 : 6 ∈ T.prefixInternalDistances e7 := by
    simpa [h2, h4, h7] using pair_sequence_mem_prefix (T := T)
      (next := e7) h24 (by omega) (by omega)
  have hnot7 : 7 ∉ T.prefixInternalDistances e7 := by
    simpa [h7] using chosen_weight_not_prefix hL e7
  ext k
  constructor
  · intro hk
    obtain ⟨p, hp, hpk⟩ := prefix_member_witness hk
    have hle := prefix_pairDist_le_three_edges e7 e1 e2 e4
      hne12 hne14 hne24 hall p hp
    rw [hpk, h1, h2, h4] at hle
    have hpos := prefix_member_pos hL hk
    have hn7 : k ≠ 7 := fun h => hnot7 (h ▸ hk)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · intro hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hm1
    · exact hm2
    · exact hm3
    · exact hm4
    · exact hm5
    · exact hm6

private theorem disjoint_meets_both_prefix_spectrum
    (hL : IsLeech T) (e1 e2 e3 e7 : T.Edge)
    (h1 : T.weight e1 = 1) (h2 : T.weight e2 = 2)
    (h3 : T.weight e3 = 3) (h7 : T.weight e7 = 7)
    (h12 : T.EdgeEndpointDisjoint e1 e2)
    (h31 : T.EdgeAdjacent e3 e1)
    (h32 : T.EdgeAdjacent e3 e2)
    (hno4 : ¬∃ e : T.Edge, T.weight e = 4)
    (hno5 : ¬∃ e : T.Edge, T.weight e = 5)
    (hno6 : ¬∃ e : T.Edge, T.weight e = 6) :
    T.prefixInternalDistances e7 = {1, 2, 3, 4, 5, 6} := by
  classical
  have hne12 : e1 ≠ e2 := by intro h; have := congrArg T.weight h; omega
  have hne13 : e1 ≠ e3 := by intro h; have := congrArg T.weight h; omega
  have hne23 : e2 ≠ e3 := by intro h; have := congrArg T.weight h; omega
  have hall := disjoint_known_lighter hL h1 h2 h3 (by omega : T.weight e7 ≤ 7)
    (Or.inr hno4) (Or.inr hno5) (Or.inr hno6)
  have hm1 : 1 ∈ T.prefixInternalDistances e7 := by
    simpa [h1, h7] using physical_sequence_mem_prefix (T := T)
      (e := e1) (next := e7) (by omega)
  have hm2 : 2 ∈ T.prefixInternalDistances e7 := by
    simpa [h2, h7] using physical_sequence_mem_prefix (T := T)
      (e := e2) (next := e7) (by omega)
  have hm3 : 3 ∈ T.prefixInternalDistances e7 := by
    simpa [h3, h7] using physical_sequence_mem_prefix (T := T)
      (e := e3) (next := e7) (by omega)
  have h13 : T.EdgeAdjacent e1 e3 := (T.edgeAdjacent_comm e3 e1).1 h31
  have hm4 : 4 ∈ T.prefixInternalDistances e7 := by
    simpa [h1, h3, h7] using pair_sequence_mem_prefix (T := T)
      (next := e7) h13 (by omega) (by omega)
  have hm5 : 5 ∈ T.prefixInternalDistances e7 := by
    simpa [h2, h3, h7] using pair_sequence_mem_prefix (T := T)
      (next := e7) h32 (by omega) (by omega)
  have hchain : T.EdgeChain e1 e3 e2 := by
    exact ⟨h13, h32, h12⟩
  have hm6 : 6 ∈ T.prefixInternalDistances e7 := by
    simpa [h1, h2, h3, h7, add_assoc] using
      chain_sequence_mem_prefix (T := T) (next := e7) hchain
        (by omega) (by omega) (by omega)
  ext k
  constructor
  · intro hk
    obtain ⟨p, hp, hpk⟩ := prefix_member_witness hk
    have hle := prefix_pairDist_le_three_edges e7 e1 e2 e3
      hne12 hne13 hne23 hall p hp
    rw [hpk, h1, h2, h3] at hle
    have hpos := prefix_member_pos hL hk
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · intro hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hm1
    · exact hm2
    · exact hm3
    · exact hm4
    · exact hm5
    · exact hm6

private theorem adjacent_none_prefix_spectrum
    (hL : IsLeech T) (e1 e2 e4 e5 : T.Edge)
    (h1 : T.weight e1 = 1) (h2 : T.weight e2 = 2)
    (h4 : T.weight e4 = 4) (h5 : T.weight e5 = 5)
    (h12 : T.EdgeAdjacent e1 e2)
    (h41 : T.EdgeEndpointDisjoint e4 e1)
    (h42 : T.EdgeEndpointDisjoint e4 e2)
    (hno3 : ¬∃ e : T.Edge, T.weight e = 3) :
    T.prefixInternalDistances e5 = {1, 2, 3, 4} := by
  classical
  have hne12 : e1 ≠ e2 := by intro h; have := congrArg T.weight h; omega
  have hne14 : e1 ≠ e4 := by intro h; have := congrArg T.weight h; omega
  have hne24 : e2 ≠ e4 := by intro h; have := congrArg T.weight h; omega
  have hall := adjacent_known_lighter hL h1 h2 h4 (by omega : T.weight e5 ≤ 7)
    hno3 (Or.inl (by omega : T.weight e5 ≤ 5))
    (Or.inl (by omega : T.weight e5 ≤ 6))
  have hm1 : 1 ∈ T.prefixInternalDistances e5 := by
    simpa [h1, h5] using physical_sequence_mem_prefix (T := T)
      (e := e1) (next := e5) (by omega)
  have hm2 : 2 ∈ T.prefixInternalDistances e5 := by
    simpa [h2, h5] using physical_sequence_mem_prefix (T := T)
      (e := e2) (next := e5) (by omega)
  have hm4 : 4 ∈ T.prefixInternalDistances e5 := by
    simpa [h4, h5] using physical_sequence_mem_prefix (T := T)
      (e := e4) (next := e5) (by omega)
  have hm3 : 3 ∈ T.prefixInternalDistances e5 := by
    simpa [h1, h2, h5] using pair_sequence_mem_prefix (T := T)
      (next := e5) h12 (by omega) (by omega)
  have hnot5 : 5 ∉ T.prefixInternalDistances e5 := by
    simpa [h5] using chosen_weight_not_prefix hL e5
  have hnot6 : 6 ∉ T.prefixInternalDistances e5 := by
    intro hk
    obtain ⟨p, _, hsum, hbelow⟩ := prefix_member_path_data hk
    let q := T.path p.left p.right
    have hshape := positive_nodup_sum_six_shape
      (pathWeightList_positive (T := T) q) (pathWeightList_nodup hL q) hsum
    rcases hshape with h6 | hpairs | htriples
    · have hlt := hbelow 6 (by rw [h6]; simp)
      omega
    · rcases hpairs with h15 | h51 | h24 | h42'
      · have hlt := hbelow 5 (by rw [h15]; simp)
        omega
      · have hlt := hbelow 5 (by rw [h51]; simp)
        omega
      · obtain ⟨f2, f4, hf2, hf4, hadj⟩ :=
          adjacentEdges_of_pathWeightList_pair q h24
        have hf2e : f2 = e2 := t1_edge_weight_injective hL (hf2.trans h2.symm)
        have hf4e : f4 = e4 := t1_edge_weight_injective hL (hf4.trans h4.symm)
        subst f2; subst f4
        obtain ⟨v, hv2, hv4⟩ := hadj.2
        exact h42 v hv4 hv2
      · obtain ⟨f4, f2, hf4, hf2, hadj⟩ :=
          adjacentEdges_of_pathWeightList_pair q h42'
        have hf2e : f2 = e2 := t1_edge_weight_injective hL (hf2.trans h2.symm)
        have hf4e : f4 = e4 := t1_edge_weight_injective hL (hf4.trans h4.symm)
        subst f2; subst f4
        obtain ⟨v, hv4, hv2⟩ := hadj.2
        exact h42 v hv4 hv2
    · have hm3path : 3 ∈ pathWeightList (T := T) q := by
        rcases htriples with h | h | h | h | h | h <;> rw [h] <;> simp
      exact hno3 (physicalEdge_of_mem_pathWeightList q hm3path)
  have hnot7 : 7 ∉ T.prefixInternalDistances e5 := by
    intro hk
    obtain ⟨p, _, hsum, hbelow⟩ := prefix_member_path_data hk
    let q := T.path p.left p.right
    have hshape := positive_nodup_sum_seven_shape
      (pathWeightList_positive (T := T) q) (pathWeightList_nodup hL q) hsum
    rcases hshape with h7 | hpairs | htriples
    · have hlt := hbelow 7 (by rw [h7]; simp)
      omega
    · rcases hpairs with h16 | h61 | h25 | h52 | h34 | h43
      · have hlt := hbelow 6 (by rw [h16]; simp); omega
      · have hlt := hbelow 6 (by rw [h61]; simp); omega
      · have hlt := hbelow 5 (by rw [h25]; simp); omega
      · have hlt := hbelow 5 (by rw [h52]; simp); omega
      · exact hno3 (physicalEdge_of_mem_pathWeightList q (by rw [h34]; simp))
      · exact hno3 (physicalEdge_of_mem_pathWeightList q (by rw [h43]; simp))
    · obtain ⟨f1, f2, f4, hf1, hf2, hf4, harr⟩ :=
        arrangement124_of_triple_shape q htriples
      have hf1e : f1 = e1 := t1_edge_weight_injective hL (hf1.trans h1.symm)
      have hf2e : f2 = e2 := t1_edge_weight_injective hL (hf2.trans h2.symm)
      have hf4e : f4 = e4 := t1_edge_weight_injective hL (hf4.trans h4.symm)
      subst f1; subst f2; subst f4
      exact arrangement_impossible_of_third_disjoint h41 h42 harr
  ext k
  constructor
  · intro hk
    obtain ⟨p, hp, hpk⟩ := prefix_member_witness hk
    have hle := prefix_pairDist_le_three_edges e5 e1 e2 e4
      hne12 hne14 hne24 hall p hp
    rw [hpk, h1, h2, h4] at hle
    have hpos := prefix_member_pos hL hk
    have hn5 : k ≠ 5 := fun h => hnot5 (h ▸ hk)
    have hn6 : k ≠ 6 := fun h => hnot6 (h ▸ hk)
    have hn7 : k ≠ 7 := fun h => hnot7 (h ▸ hk)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · intro hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact hm1
    · exact hm2
    · exact hm3
    · exact hm4

private theorem disjoint_none_prefix_spectrum
    (hL : IsLeech T) (e1 e2 e3 e4 : T.Edge)
    (h1 : T.weight e1 = 1) (h2 : T.weight e2 = 2)
    (h3 : T.weight e3 = 3) (h4 : T.weight e4 = 4)
    (h12 : T.EdgeEndpointDisjoint e1 e2)
    (h31 : T.EdgeEndpointDisjoint e3 e1)
    (h32 : T.EdgeEndpointDisjoint e3 e2) :
    T.prefixInternalDistances e4 = {1, 2, 3} := by
  classical
  have hne12 : e1 ≠ e2 := by intro h; have := congrArg T.weight h; omega
  have hne13 : e1 ≠ e3 := by intro h; have := congrArg T.weight h; omega
  have hne23 : e2 ≠ e3 := by intro h; have := congrArg T.weight h; omega
  have hall := disjoint_known_lighter hL h1 h2 h3 (by omega : T.weight e4 ≤ 7)
    (Or.inl (by omega : T.weight e4 ≤ 4))
    (Or.inl (by omega : T.weight e4 ≤ 5))
    (Or.inl (by omega : T.weight e4 ≤ 6))
  have hm1 : 1 ∈ T.prefixInternalDistances e4 := by
    simpa [h1, h4] using physical_sequence_mem_prefix (T := T)
      (e := e1) (next := e4) (by omega)
  have hm2 : 2 ∈ T.prefixInternalDistances e4 := by
    simpa [h2, h4] using physical_sequence_mem_prefix (T := T)
      (e := e2) (next := e4) (by omega)
  have hm3 : 3 ∈ T.prefixInternalDistances e4 := by
    simpa [h3, h4] using physical_sequence_mem_prefix (T := T)
      (e := e3) (next := e4) (by omega)
  have hnot4 : 4 ∉ T.prefixInternalDistances e4 := by
    simpa [h4] using chosen_weight_not_prefix hL e4
  have hnot5 : 5 ∉ T.prefixInternalDistances e4 := by
    intro hk
    obtain ⟨p, _, hsum, hbelow⟩ := prefix_member_path_data hk
    let q := T.path p.left p.right
    have hshape := positive_nodup_sum_five_shape
      (pathWeightList_positive (T := T) q) (pathWeightList_nodup hL q) hsum
    rcases hshape with h5 | h14 | h41 | h23 | h32'
    · have hlt := hbelow 5 (by rw [h5]; simp); omega
    · have hlt := hbelow 4 (by rw [h14]; simp); omega
    · have hlt := hbelow 4 (by rw [h41]; simp); omega
    · obtain ⟨f2, f3, hf2, hf3, hadj⟩ :=
        adjacentEdges_of_pathWeightList_pair q h23
      have hf2e : f2 = e2 := t1_edge_weight_injective hL (hf2.trans h2.symm)
      have hf3e : f3 = e3 := t1_edge_weight_injective hL (hf3.trans h3.symm)
      subst f2; subst f3
      obtain ⟨v, hv2, hv3⟩ := hadj.2
      exact h32 v hv3 hv2
    · obtain ⟨f3, f2, hf3, hf2, hadj⟩ :=
        adjacentEdges_of_pathWeightList_pair q h32'
      have hf2e : f2 = e2 := t1_edge_weight_injective hL (hf2.trans h2.symm)
      have hf3e : f3 = e3 := t1_edge_weight_injective hL (hf3.trans h3.symm)
      subst f2; subst f3
      obtain ⟨v, hv3, hv2⟩ := hadj.2
      exact h32 v hv3 hv2
  have hnot6 : 6 ∉ T.prefixInternalDistances e4 := by
    intro hk
    obtain ⟨p, _, hsum, hbelow⟩ := prefix_member_path_data hk
    let q := T.path p.left p.right
    have hshape := positive_nodup_sum_six_shape
      (pathWeightList_positive (T := T) q) (pathWeightList_nodup hL q) hsum
    rcases hshape with h6 | hpairs | htriples
    · have hlt := hbelow 6 (by rw [h6]; simp); omega
    · rcases hpairs with h15 | h51 | h24 | h42
      · have hlt := hbelow 5 (by rw [h15]; simp); omega
      · have hlt := hbelow 5 (by rw [h51]; simp); omega
      · have hlt := hbelow 4 (by rw [h24]; simp); omega
      · have hlt := hbelow 4 (by rw [h42]; simp); omega
    · obtain ⟨f1, f2, f3, hf1, hf2, hf3, harr⟩ :=
        arrangement123_of_triple_shape q htriples
      have hf1e : f1 = e1 := t1_edge_weight_injective hL (hf1.trans h1.symm)
      have hf2e : f2 = e2 := t1_edge_weight_injective hL (hf2.trans h2.symm)
      have hf3e : f3 = e3 := t1_edge_weight_injective hL (hf3.trans h3.symm)
      subst f1; subst f2; subst f3
      exact arrangement_impossible_of_first_disjoint h12
        ((T.edgeEndpointDisjoint_comm e3 e1).1 h31) harr
  ext k
  constructor
  · intro hk
    obtain ⟨p, hp, hpk⟩ := prefix_member_witness hk
    have hle := prefix_pairDist_le_three_edges e4 e1 e2 e3
      hne12 hne13 hne23 hall p hp
    rw [hpk, h1, h2, h3] at hle
    have hpos := prefix_member_pos hL hk
    have hn4 : k ≠ 4 := fun h => hnot4 (h ▸ hk)
    have hn5 : k ≠ 5 := fun h => hnot5 (h ▸ hk)
    have hn6 : k ≠ 6 := fun h => hnot6 (h ▸ hk)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · intro hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact hm1
    · exact hm2
    · exact hm3

private theorem disjoint_meets_one_prefix_spectrum
    (hL : IsLeech T) (e1 e2 e3 e5 : T.Edge)
    (h1 : T.weight e1 = 1) (h2 : T.weight e2 = 2)
    (h3 : T.weight e3 = 3) (h5 : T.weight e5 = 5)
    (h12 : T.EdgeEndpointDisjoint e1 e2)
    (h31 : T.EdgeAdjacent e3 e1)
    (h32 : T.EdgeEndpointDisjoint e3 e2)
    (hno4 : ¬∃ e : T.Edge, T.weight e = 4) :
    T.prefixInternalDistances e5 = {1, 2, 3, 4} := by
  classical
  have hne12 : e1 ≠ e2 := by intro h; have := congrArg T.weight h; omega
  have hne13 : e1 ≠ e3 := by intro h; have := congrArg T.weight h; omega
  have hne23 : e2 ≠ e3 := by intro h; have := congrArg T.weight h; omega
  have hall := disjoint_known_lighter hL h1 h2 h3 (by omega : T.weight e5 ≤ 7)
    (Or.inr hno4) (Or.inl (by omega : T.weight e5 ≤ 5))
    (Or.inl (by omega : T.weight e5 ≤ 6))
  have hm1 : 1 ∈ T.prefixInternalDistances e5 := by
    simpa [h1, h5] using physical_sequence_mem_prefix (T := T)
      (e := e1) (next := e5) (by omega)
  have hm2 : 2 ∈ T.prefixInternalDistances e5 := by
    simpa [h2, h5] using physical_sequence_mem_prefix (T := T)
      (e := e2) (next := e5) (by omega)
  have hm3 : 3 ∈ T.prefixInternalDistances e5 := by
    simpa [h3, h5] using physical_sequence_mem_prefix (T := T)
      (e := e3) (next := e5) (by omega)
  have h13 : T.EdgeAdjacent e1 e3 := (T.edgeAdjacent_comm e3 e1).1 h31
  have hm4 : 4 ∈ T.prefixInternalDistances e5 := by
    simpa [h1, h3, h5] using pair_sequence_mem_prefix (T := T)
      (next := e5) h13 (by omega) (by omega)
  have hnot5 : 5 ∉ T.prefixInternalDistances e5 := by
    simpa [h5] using chosen_weight_not_prefix hL e5
  have hnot6 : 6 ∉ T.prefixInternalDistances e5 := by
    intro hk
    obtain ⟨p, _, hsum, hbelow⟩ := prefix_member_path_data hk
    let q := T.path p.left p.right
    have hshape := positive_nodup_sum_six_shape
      (pathWeightList_positive (T := T) q) (pathWeightList_nodup hL q) hsum
    rcases hshape with h6 | hpairs | htriples
    · have hlt := hbelow 6 (by rw [h6]; simp); omega
    · rcases hpairs with h15 | h51 | h24 | h42
      · have hlt := hbelow 5 (by rw [h15]; simp); omega
      · have hlt := hbelow 5 (by rw [h51]; simp); omega
      · exact hno4 (physicalEdge_of_mem_pathWeightList q (by rw [h24]; simp))
      · exact hno4 (physicalEdge_of_mem_pathWeightList q (by rw [h42]; simp))
    · obtain ⟨f1, f2, f3, hf1, hf2, hf3, harr⟩ :=
        arrangement123_of_triple_shape q htriples
      have hf1e : f1 = e1 := t1_edge_weight_injective hL (hf1.trans h1.symm)
      have hf2e : f2 = e2 := t1_edge_weight_injective hL (hf2.trans h2.symm)
      have hf3e : f3 = e3 := t1_edge_weight_injective hL (hf3.trans h3.symm)
      subst f1; subst f2; subst f3
      exact arrangement_impossible_of_second_disjoint
        ((T.edgeEndpointDisjoint_comm e1 e2).1 h12)
        ((T.edgeEndpointDisjoint_comm e3 e2).1 h32) harr
  ext k
  constructor
  · intro hk
    obtain ⟨p, hp, hpk⟩ := prefix_member_witness hk
    have hle := prefix_pairDist_le_three_edges e5 e1 e2 e3
      hne12 hne13 hne23 hall p hp
    rw [hpk, h1, h2, h3] at hle
    have hpos := prefix_member_pos hL hk
    have hn5 : k ≠ 5 := fun h => hnot5 (h ▸ hk)
    have hn6 : k ≠ 6 := fun h => hnot6 (h ▸ hk)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · intro hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact hm1
    · exact hm2
    · exact hm3
    · exact hm4

private theorem disjoint_meets_two_prefix_spectrum
    (hL : IsLeech T) (e1 e2 e3 e4 : T.Edge)
    (h1 : T.weight e1 = 1) (h2 : T.weight e2 = 2)
    (h3 : T.weight e3 = 3) (h4 : T.weight e4 = 4)
    (h12 : T.EdgeEndpointDisjoint e1 e2)
    (h31 : T.EdgeEndpointDisjoint e3 e1)
    (h32 : T.EdgeAdjacent e3 e2) :
    T.prefixInternalDistances e4 = {1, 2, 3, 5} := by
  classical
  have hne12 : e1 ≠ e2 := by intro h; have := congrArg T.weight h; omega
  have hne13 : e1 ≠ e3 := by intro h; have := congrArg T.weight h; omega
  have hne23 : e2 ≠ e3 := by intro h; have := congrArg T.weight h; omega
  have hall := disjoint_known_lighter hL h1 h2 h3 (by omega : T.weight e4 ≤ 7)
    (Or.inl (by omega : T.weight e4 ≤ 4))
    (Or.inl (by omega : T.weight e4 ≤ 5))
    (Or.inl (by omega : T.weight e4 ≤ 6))
  have hm1 : 1 ∈ T.prefixInternalDistances e4 := by
    simpa [h1, h4] using physical_sequence_mem_prefix (T := T)
      (e := e1) (next := e4) (by omega)
  have hm2 : 2 ∈ T.prefixInternalDistances e4 := by
    simpa [h2, h4] using physical_sequence_mem_prefix (T := T)
      (e := e2) (next := e4) (by omega)
  have hm3 : 3 ∈ T.prefixInternalDistances e4 := by
    simpa [h3, h4] using physical_sequence_mem_prefix (T := T)
      (e := e3) (next := e4) (by omega)
  have hm5 : 5 ∈ T.prefixInternalDistances e4 := by
    simpa [h2, h3, h4] using pair_sequence_mem_prefix (T := T)
      (next := e4) h32 (by omega) (by omega)
  have hnot4 : 4 ∉ T.prefixInternalDistances e4 := by
    simpa [h4] using chosen_weight_not_prefix hL e4
  have hnot6 : 6 ∉ T.prefixInternalDistances e4 := by
    intro hk
    obtain ⟨p, _, hsum, hbelow⟩ := prefix_member_path_data hk
    let q := T.path p.left p.right
    have hshape := positive_nodup_sum_six_shape
      (pathWeightList_positive (T := T) q) (pathWeightList_nodup hL q) hsum
    rcases hshape with h6 | hpairs | htriples
    · have hlt := hbelow 6 (by rw [h6]; simp); omega
    · rcases hpairs with h15 | h51 | h24 | h42
      · have hlt := hbelow 5 (by rw [h15]; simp); omega
      · have hlt := hbelow 5 (by rw [h51]; simp); omega
      · have hlt := hbelow 4 (by rw [h24]; simp); omega
      · have hlt := hbelow 4 (by rw [h42]; simp); omega
    · obtain ⟨f1, f2, f3, hf1, hf2, hf3, harr⟩ :=
        arrangement123_of_triple_shape q htriples
      have hf1e : f1 = e1 := t1_edge_weight_injective hL (hf1.trans h1.symm)
      have hf2e : f2 = e2 := t1_edge_weight_injective hL (hf2.trans h2.symm)
      have hf3e : f3 = e3 := t1_edge_weight_injective hL (hf3.trans h3.symm)
      subst f1; subst f2; subst f3
      exact arrangement_impossible_of_first_disjoint h12
        ((T.edgeEndpointDisjoint_comm e3 e1).1 h31) harr
  ext k
  constructor
  · intro hk
    obtain ⟨p, hp, hpk⟩ := prefix_member_witness hk
    have hle := prefix_pairDist_le_three_edges e4 e1 e2 e3
      hne12 hne13 hne23 hall p hp
    rw [hpk, h1, h2, h3] at hle
    have hpos := prefix_member_pos hL hk
    have hn4 : k ≠ 4 := fun h => hnot4 (h ▸ hk)
    have hn6 : k ≠ 6 := fun h => hnot6 (h ▸ hk)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · intro hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact hm1
    · exact hm2
    · exact hm3
    · exact hm5

/-! ## Forced next physical edges -/

private theorem adjacent_none_exists_weight_five
    (hL : IsLeech T) (hn : 5 ≤ n) (e1 e2 e4 : T.Edge)
    (h1 : T.weight e1 = 1) (_h2 : T.weight e2 = 2)
    (h4 : T.weight e4 = 4)
    (h41 : T.EdgeEndpointDisjoint e4 e1)
    (hno3 : ¬∃ e : T.Edge, T.weight e = 3) :
    ∃ e5 : T.Edge, T.weight e5 = 5 := by
  obtain ⟨u, v, p, hp⟩ := target_path_of_rank hL 5
    (rank_mem_target_of_five_le hn (by omega) (by omega))
  rcases weightFivePath_shape hL p hp with h5 | h14 | h23
  · exact h5
  · obtain ⟨f1, f4, hf1, hf4, hadj⟩ := h14
    have hf1e : f1 = e1 := t1_edge_weight_injective hL (hf1.trans h1.symm)
    have hf4e : f4 = e4 := t1_edge_weight_injective hL (hf4.trans h4.symm)
    subst f1; subst f4
    obtain ⟨x, hx1, hx4⟩ := hadj.2
    exact (h41 x hx4 hx1).elim
  · obtain ⟨f2, f3, hf2, hf3, _⟩ := h23
    exact (hno3 ⟨f3, hf3⟩).elim

private theorem adjacent_meets_one_exists_weight_six
    (hL : IsLeech T) (hn : 5 ≤ n) (e1 e2 e4 : T.Edge)
    (_h1 : T.weight e1 = 1) (h2 : T.weight e2 = 2)
    (h4 : T.weight e4 = 4)
    (h42 : T.EdgeEndpointDisjoint e4 e2)
    (hno3 : ¬∃ e : T.Edge, T.weight e = 3)
    (hno5 : ¬∃ e : T.Edge, T.weight e = 5) :
    ∃ e6 : T.Edge, T.weight e6 = 6 := by
  obtain ⟨u, v, p, hp⟩ := target_path_of_rank hL 6
    (rank_mem_target_of_five_le hn (by omega) (by omega))
  rcases weightSixPath_shape hL p hp with h6 | h15 | h24 | h123
  · exact h6
  · obtain ⟨_, f5, _, hf5, _⟩ := h15
    exact (hno5 ⟨f5, hf5⟩).elim
  · obtain ⟨f2, f4, hf2, hf4, hadj⟩ := h24
    have hf2e : f2 = e2 := t1_edge_weight_injective hL (hf2.trans h2.symm)
    have hf4e : f4 = e4 := t1_edge_weight_injective hL (hf4.trans h4.symm)
    subst f2; subst f4
    obtain ⟨x, hx2, hx4⟩ := hadj.2
    exact (h42 x hx4 hx2).elim
  · obtain ⟨_, _, f3, _, _, hf3, _⟩ := h123
    exact (hno3 ⟨f3, hf3⟩).elim

private theorem adjacent_meets_two_exists_weight_five
    (hL : IsLeech T) (hn : 5 ≤ n) (e1 e2 e4 : T.Edge)
    (h1 : T.weight e1 = 1) (h2 : T.weight e2 = 2)
    (h4 : T.weight e4 = 4)
    (h41 : T.EdgeEndpointDisjoint e4 e1)
    (hno3 : ¬∃ e : T.Edge, T.weight e = 3) :
    ∃ e5 : T.Edge, T.weight e5 = 5 :=
  adjacent_none_exists_weight_five hL hn e1 e2 e4 h1 h2 h4 h41 hno3

private theorem adjacent_meets_both_exists_weight_seven
    (hL : IsLeech T) (hn : 5 ≤ n) (e1 e2 e4 : T.Edge)
    (h1 : T.weight e1 = 1) (h2 : T.weight e2 = 2)
    (h4 : T.weight e4 = 4)
    (h12 : T.EdgeAdjacent e1 e2)
    (h41 : T.EdgeAdjacent e4 e1)
    (h42 : T.EdgeAdjacent e4 e2)
    (hno3 : ¬∃ e : T.Edge, T.weight e = 3)
    (hno5 : ¬∃ e : T.Edge, T.weight e = 5)
    (hno6 : ¬∃ e : T.Edge, T.weight e = 6) :
    ∃ e7 : T.Edge, T.weight e7 = 7 := by
  obtain ⟨u, v, p, hp⟩ := target_path_of_rank hL 7
    (rank_mem_target_of_five_le hn (by omega) (by omega))
  rcases weightSevenPath_shape hL p hp with h7 | h16 | h25 | h34 | h124
  · exact h7
  · obtain ⟨_, f6, _, hf6, _⟩ := h16
    exact (hno6 ⟨f6, hf6⟩).elim
  · obtain ⟨_, f5, _, hf5, _⟩ := h25
    exact (hno5 ⟨f5, hf5⟩).elim
  · obtain ⟨f3, _, hf3, _, _⟩ := h34
    exact (hno3 ⟨f3, hf3⟩).elim
  · obtain ⟨f1, f2, f4, hf1, hf2, hf4, harr⟩ := h124
    have hf1e : f1 = e1 := t1_edge_weight_injective hL (hf1.trans h1.symm)
    have hf2e : f2 = e2 := t1_edge_weight_injective hL (hf2.trans h2.symm)
    have hf4e : f4 = e4 := t1_edge_weight_injective hL (hf4.trans h4.symm)
    subst f1; subst f2; subst f4
    exact (arrangement_impossible_of_pairwise_adjacent h12
      ((T.edgeAdjacent_comm e4 e1).1 h41)
      ((T.edgeAdjacent_comm e4 e2).1 h42) harr).elim

private theorem disjoint_none_exists_weight_four
    (hL : IsLeech T) (hn : 5 ≤ n) (e1 e3 : T.Edge)
    (h1 : T.weight e1 = 1) (h3 : T.weight e3 = 3)
    (h31 : T.EdgeEndpointDisjoint e3 e1) :
    ∃ e4 : T.Edge, T.weight e4 = 4 := by
  obtain ⟨u, v, p, hp⟩ := target_path_of_rank hL 4
    (rank_mem_target_of_five_le hn (by omega) (by omega))
  rcases weightFourPath_shape hL p hp with h4 | h13
  · exact h4
  · obtain ⟨f1, f3, hf1, hf3, hadj⟩ := h13
    have hf1e : f1 = e1 := t1_edge_weight_injective hL (hf1.trans h1.symm)
    have hf3e : f3 = e3 := t1_edge_weight_injective hL (hf3.trans h3.symm)
    subst f1; subst f3
    obtain ⟨x, hx1, hx3⟩ := hadj.2
    exact (h31 x hx3 hx1).elim

private theorem disjoint_meets_one_exists_weight_five
    (hL : IsLeech T) (hn : 5 ≤ n) (e1 e2 e3 : T.Edge)
    (_h1 : T.weight e1 = 1) (h2 : T.weight e2 = 2)
    (h3 : T.weight e3 = 3)
    (h32 : T.EdgeEndpointDisjoint e3 e2)
    (hno4 : ¬∃ e : T.Edge, T.weight e = 4) :
    ∃ e5 : T.Edge, T.weight e5 = 5 := by
  obtain ⟨u, v, p, hp⟩ := target_path_of_rank hL 5
    (rank_mem_target_of_five_le hn (by omega) (by omega))
  rcases weightFivePath_shape hL p hp with h5 | h14 | h23
  · exact h5
  · obtain ⟨_, f4, _, hf4, _⟩ := h14
    exact (hno4 ⟨f4, hf4⟩).elim
  · obtain ⟨f2, f3, hf2, hf3, hadj⟩ := h23
    have hf2e : f2 = e2 := t1_edge_weight_injective hL (hf2.trans h2.symm)
    have hf3e : f3 = e3 := t1_edge_weight_injective hL (hf3.trans h3.symm)
    subst f2; subst f3
    obtain ⟨x, hx2, hx3⟩ := hadj.2
    exact (h32 x hx3 hx2).elim

private theorem disjoint_meets_both_exists_weight_seven
    (hL : IsLeech T) (hn : 5 ≤ n)
    (hno4 : ¬∃ e : T.Edge, T.weight e = 4)
    (hno5 : ¬∃ e : T.Edge, T.weight e = 5)
    (hno6 : ¬∃ e : T.Edge, T.weight e = 6) :
    ∃ e7 : T.Edge, T.weight e7 = 7 := by
  obtain ⟨u, v, p, hp⟩ := target_path_of_rank hL 7
    (rank_mem_target_of_five_le hn (by omega) (by omega))
  rcases weightSevenPath_shape hL p hp with h7 | h16 | h25 | h34 | h124
  · exact h7
  · obtain ⟨_, f6, _, hf6, _⟩ := h16
    exact (hno6 ⟨f6, hf6⟩).elim
  · obtain ⟨_, f5, _, hf5, _⟩ := h25
    exact (hno5 ⟨f5, hf5⟩).elim
  · obtain ⟨_, f4, _, hf4, _⟩ := h34
    exact (hno4 ⟨f4, hf4⟩).elim
  · obtain ⟨_, _, f4, _, _, hf4, _⟩ := h124
    exact (hno4 ⟨f4, hf4⟩).elim

/-! ## The three order-eighteen cut consequences -/

private theorem two_le_card_subtype_of_two
    {P : Fin n → Prop} {a b : Fin n}
    (ha : P a) (hb : P b) (hab : a ≠ b) :
    2 ≤ Nat.card {x : Fin n // P x} := by
  classical
  let encode : Bool → {x : Fin n // P x} := fun z =>
    if z then ⟨a, ha⟩ else ⟨b, hb⟩
  have hinj : Function.Injective encode := by
    intro x y hxy
    cases x <;> cases y <;> simp [encode] at hxy ⊢
    · exact (hab hxy.symm).elim
    · exact (hab hxy).elim
  have hcard := Nat.card_le_card_of_injective encode hinj
  simpa using hcard

private theorem cut_sides_two_of_opposite_adjacent_edges
    (e f g : T.Edge)
    (hef : T.EdgeAdjacent e f) (heg : T.EdgeAdjacent e g)
    (hfg : T.EdgeEndpointDisjoint f g) :
    2 ≤ T.cutSize e ∧ 2 ≤ n - T.cutSize e := by
  classical
  obtain ⟨a, hae, haf⟩ := hef.2
  obtain ⟨b, hbe, hbg⟩ := heg.2
  have hab : a ≠ b := by
    intro h
    subst b
    exact hfg a haf hbg
  let x : Fin n := Sym2.Mem.other haf
  let y : Fin n := Sym2.Mem.other hbg
  have hf : s(a, x) = f.1 := Sym2.other_spec haf
  have hg : s(b, y) = g.1 := Sym2.other_spec hbg
  have hax : T.graph.Adj a x := by
    rw [← SimpleGraph.mem_edgeSet, hf]
    exact f.2
  have hby : T.graph.Adj b y := by
    rw [← SimpleGraph.mem_edgeSet, hg]
    exact g.2
  have hcutax : (T.cutGraph e).Adj a x := by
    rw [PosIntTree.cutGraph, SimpleGraph.deleteEdges_adj]
    refine ⟨hax, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hraw
    apply hef.1
    apply Subtype.ext
    exact (hf.symm.trans hraw).symm
  have hcutby : (T.cutGraph e).Adj b y := by
    rw [PosIntTree.cutGraph, SimpleGraph.deleteEdges_adj]
    refine ⟨hby, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hraw
    apply heg.1
    apply Subtype.ext
    exact (hg.symm.trans hraw).symm
  have hreachax : (T.cutGraph e).Reachable a x :=
    ⟨SimpleGraph.Walk.cons hcutax SimpleGraph.Walk.nil⟩
  have hreachby : (T.cutGraph e).Reachable b y :=
    ⟨SimpleGraph.Walk.cons hcutby SimpleGraph.Walk.nil⟩
  have heab : e.1 = s(a, b) :=
    (Sym2.mem_and_mem_iff hab).mp ⟨hae, hbe⟩
  have habAdj : T.graph.Adj a b := by
    rw [← SimpleGraph.mem_edgeSet, ← heab]
    exact e.2
  let direct : T.graph.Path a b := SimpleGraph.Path.singleton habAdj
  have hdirect : direct = T.path a b := T.path_unique direct
  have hepath : e.1 ∈ T.pathEdges a b := by
    unfold PosIntTree.pathEdges
    rw [← hdirect]
    simp [direct, SimpleGraph.Path.singleton, heab]
  have hopp := (T.mem_pathEdges_iff_opposite_cuts e a b).1 hepath
  have hxa : x ≠ a := hax.ne.symm
  have hyb : y ≠ b := hby.ne.symm
  rcases hopp with ⟨haL, hbR⟩ | ⟨haR, hbL⟩
  · have hxL : T.LeftCut e x := hreachax.symm.trans haL
    have hyR : T.RightCut e y := hreachby.symm.trans hbR
    have hleft : 2 ≤ T.cutSize e := by
      unfold PosIntTree.cutSize
      rw [← Nat.card_eq_fintype_card]
      exact two_le_card_subtype_of_two haL hxL hxa.symm
    have hrightCard : 2 ≤ Fintype.card (T.RightVertex e) := by
      rw [← Nat.card_eq_fintype_card]
      exact two_le_card_subtype_of_two hbR hyR hyb.symm
    rw [T.rightVertex_card e] at hrightCard
    exact ⟨hleft, hrightCard⟩
  · have hxR : T.RightCut e x := hreachax.symm.trans haR
    have hyL : T.LeftCut e y := hreachby.symm.trans hbL
    have hleft : 2 ≤ T.cutSize e := by
      unfold PosIntTree.cutSize
      rw [← Nat.card_eq_fintype_card]
      exact two_le_card_subtype_of_two hbL hyL hyb.symm
    have hrightCard : 2 ≤ Fintype.card (T.RightVertex e) := by
      rw [← Nat.card_eq_fintype_card]
      exact two_le_card_subtype_of_two haR hxR hxa.symm
    rw [T.rightVertex_card e] at hrightCard
    exact ⟨hleft, hrightCard⟩

private theorem cut_product_ge_thirty_two
    (e f g : T.Edge)
    (hef : T.EdgeAdjacent e f) (heg : T.EdgeAdjacent e g)
    (hfg : T.EdgeEndpointDisjoint f g)
    (hn18 : n = 18) :
    32 ≤ T.cutSize e * (n - T.cutSize e) := by
  obtain ⟨hl, hr⟩ := cut_sides_two_of_opposite_adjacent_edges e f g hef heg hfg
  subst n
  have hupper : T.cutSize e ≤ 16 := by omega
  interval_cases hcut : T.cutSize e <;> norm_num [hcut] at hl hupper ⊢

/-! ## Graph-level row constructors -/

/-- Adjacent row 1: the weight-four edge meets neither earlier edge. -/
theorem adjacentNoneRow_of_placement
    (hL : IsLeech T) (hn : 5 ≤ n)
    (e1 e2 e4 : T.Edge)
    (h1 : T.weight e1 = 1) (h2 : T.weight e2 = 2)
    (h4 : T.weight e4 = 4)
    (h12 : T.EdgeAdjacent e1 e2)
    (h41 : T.EdgeEndpointDisjoint e4 e1)
    (h42 : T.EdgeEndpointDisjoint e4 e2) :
    AdjacentNoneRow T e1 e2 := by
  have hno3 := firstEdge_adjacent_no_weight_three hL e1 e2 h1 h2 h12
  have hpath12 : HasPathWeightSequence T [1, 2] := by
    simpa [h1, h2] using edgeAdjacent_hasPathWeightSequence (T := T) e1 e2 h12
  obtain ⟨e5, h5⟩ :=
    adjacent_none_exists_weight_five hL hn e1 e2 e4 h1 h2 h4 h41 hno3
  have hspectrum := adjacent_none_prefix_spectrum hL e1 e2 e4 e5
    h1 h2 h4 h5 h12 h41 h42 hno3
  have hforced : ForcedPrefixEdge T 5 {1, 2, 3, 4} := by
    exact ⟨e5, h5, unique_physicalWeight hL h5, hspectrum,
      by simpa [h5] using T.t2_forced_mex hL e5⟩
  exact
    { adjacent12 := h12
      noWeight3 := hno3
      witness4 := ⟨e4, h4, unique_physicalWeight hL h4, h41, h42⟩
      path12 := hpath12
      forced5 := hforced }

/-- Adjacent row 2: the weight-four edge meets only the weight-one edge. -/
theorem adjacentMeetsOneRow_of_placement
    (hL : IsLeech T) (hn : 5 ≤ n)
    (e1 e2 e4 : T.Edge)
    (h1 : T.weight e1 = 1) (h2 : T.weight e2 = 2)
    (h4 : T.weight e4 = 4)
    (h12 : T.EdgeAdjacent e1 e2)
    (h41 : T.EdgeAdjacent e4 e1)
    (h42 : T.EdgeEndpointDisjoint e4 e2) :
    AdjacentMeetsOneRow T e1 e2 := by
  have hno3 := firstEdge_adjacent_no_weight_three hL e1 e2 h1 h2 h12
  have h14 : T.EdgeAdjacent e1 e4 := (T.edgeAdjacent_comm e4 e1).1 h41
  have hpath12 : HasPathWeightSequence T [1, 2] := by
    simpa [h1, h2] using edgeAdjacent_hasPathWeightSequence (T := T) e1 e2 h12
  have hpath14 : HasPathWeightSequence T [1, 4] := by
    simpa [h1, h4] using edgeAdjacent_hasPathWeightSequence (T := T) e1 e4 h14
  have hchain : T.EdgeChain e2 e1 e4 :=
    ⟨(T.edgeAdjacent_comm e1 e2).1 h12, h14,
      (T.edgeEndpointDisjoint_comm e4 e2).1 h42⟩
  have hpath214 : HasPathWeightSequence T [2, 1, 4] := by
    simpa [h1, h2, h4] using edgeChain_hasPathWeightSequence
      (T := T) e2 e1 e4 hchain
  have hno5 : ¬∃ e : T.Edge, T.weight e = 5 := by
    simpa using no_physicalWeight_of_nontrivial_sequence hL hpath14
      (by simp) (by norm_num)
  have hno7 : ¬∃ e : T.Edge, T.weight e = 7 := by
    simpa using no_physicalWeight_of_nontrivial_sequence hL hpath214
      (by simp) (by norm_num)
  obtain ⟨e6, h6⟩ := adjacent_meets_one_exists_weight_six hL hn
    e1 e2 e4 h1 h2 h4 h42 hno3 hno5
  have hspectrum := adjacent_meets_one_prefix_spectrum hL e1 e2 e4 e6
    h1 h2 h4 h6 h12 h41 h42 hno3 hno5
  have hforced : ForcedPrefixEdge T 6 {1, 2, 3, 4, 5, 7} := by
    exact ⟨e6, h6, unique_physicalWeight hL h6, hspectrum,
      by simpa [h6] using T.t2_forced_mex hL e6⟩
  have h6dis : ∀ f6 : T.Edge, T.weight f6 = 6 →
      T.EdgeEndpointDisjoint f6 e1 := by
    intro f6 hf6
    have hne : f6 ≠ e1 := by intro h; have := congrArg T.weight h; omega
    apply (T.edgeEndpointDisjoint_iff_not_adjacent hne).2
    intro hadj
    have hseq61 : HasPathWeightSequence T [6, 1] := by
      simpa [hf6, h1] using edgeAdjacent_hasPathWeightSequence
        (T := T) f6 e1 hadj
    have hlen := sequence_length_eq_of_sum_eq hL hseq61 hpath214
      (by simp) (by simp) (by norm_num)
    norm_num at hlen
  have hcut : n = 18 → 32 ≤ T.cutSize e1 * (n - T.cutSize e1) := by
    intro hn18
    exact cut_product_ge_thirty_two e1 e2 e4 h12 h14
      ((T.edgeEndpointDisjoint_comm e4 e2).1 h42) hn18
  exact
    { adjacent12 := h12
      noWeight3 := hno3
      witness4 := ⟨e4, h4, unique_physicalWeight hL h4, h41, h42⟩
      path12 := hpath12
      path14 := hpath14
      path214 := hpath214
      noWeight5 := hno5
      noWeight7 := hno7
      forced6 := hforced
      weight6_disjoint_e1 := h6dis
      order18_cut := hcut }

/-- Adjacent row 3: the weight-four edge meets only the weight-two edge. -/
theorem adjacentMeetsTwoRow_of_placement
    (hL : IsLeech T) (hn : 5 ≤ n)
    (e1 e2 e4 : T.Edge)
    (h1 : T.weight e1 = 1) (h2 : T.weight e2 = 2)
    (h4 : T.weight e4 = 4)
    (h12 : T.EdgeAdjacent e1 e2)
    (h41 : T.EdgeEndpointDisjoint e4 e1)
    (h42 : T.EdgeAdjacent e4 e2) :
    AdjacentMeetsTwoRow T e1 e2 := by
  have hno3 := firstEdge_adjacent_no_weight_three hL e1 e2 h1 h2 h12
  have h24 : T.EdgeAdjacent e2 e4 := (T.edgeAdjacent_comm e4 e2).1 h42
  have hpath12 : HasPathWeightSequence T [1, 2] := by
    simpa [h1, h2] using edgeAdjacent_hasPathWeightSequence (T := T) e1 e2 h12
  have hpath24 : HasPathWeightSequence T [2, 4] := by
    simpa [h2, h4] using edgeAdjacent_hasPathWeightSequence (T := T) e2 e4 h24
  have hchain : T.EdgeChain e1 e2 e4 :=
    ⟨h12, h24, (T.edgeEndpointDisjoint_comm e4 e1).1 h41⟩
  have hpath124 : HasPathWeightSequence T [1, 2, 4] := by
    simpa [h1, h2, h4] using edgeChain_hasPathWeightSequence
      (T := T) e1 e2 e4 hchain
  have hno6 : ¬∃ e : T.Edge, T.weight e = 6 := by
    simpa using no_physicalWeight_of_nontrivial_sequence hL hpath24
      (by simp) (by norm_num)
  have hno7 : ¬∃ e : T.Edge, T.weight e = 7 := by
    simpa using no_physicalWeight_of_nontrivial_sequence hL hpath124
      (by simp) (by norm_num)
  obtain ⟨e5, h5⟩ := adjacent_meets_two_exists_weight_five hL hn
    e1 e2 e4 h1 h2 h4 h41 hno3
  have hspectrum := adjacent_meets_two_prefix_spectrum hL e1 e2 e4 e5
    h1 h2 h4 h5 h12 h41 h42 hno3
  have hforced : ForcedPrefixEdge T 5 {1, 2, 3, 4, 6, 7} := by
    exact ⟨e5, h5, unique_physicalWeight hL h5, hspectrum,
      by simpa [h5] using T.t2_forced_mex hL e5⟩
  have h5dis1 : ∀ f5 : T.Edge, T.weight f5 = 5 →
      T.EdgeEndpointDisjoint f5 e1 := by
    intro f5 hf5
    have hne : f5 ≠ e1 := by intro h; have := congrArg T.weight h; omega
    apply (T.edgeEndpointDisjoint_iff_not_adjacent hne).2
    intro hadj
    have hseq51 : HasPathWeightSequence T [5, 1] := by
      simpa [hf5, h1] using edgeAdjacent_hasPathWeightSequence
        (T := T) f5 e1 hadj
    have heq := sequence_eq_or_reverse_of_sum_eq hL hseq51 hpath24
      (by simp) (by simp) (by norm_num)
    norm_num at heq
  have h5dis2 : ∀ f5 : T.Edge, T.weight f5 = 5 →
      T.EdgeEndpointDisjoint f5 e2 := by
    intro f5 hf5
    have hne : f5 ≠ e2 := by intro h; have := congrArg T.weight h; omega
    apply (T.edgeEndpointDisjoint_iff_not_adjacent hne).2
    intro hadj
    have hseq52 : HasPathWeightSequence T [5, 2] := by
      simpa [hf5, h2] using edgeAdjacent_hasPathWeightSequence
        (T := T) f5 e2 hadj
    have hlen := sequence_length_eq_of_sum_eq hL hseq52 hpath124
      (by simp) (by simp) (by norm_num)
    norm_num at hlen
  have hcut : n = 18 → 32 ≤ T.cutSize e2 * (n - T.cutSize e2) := by
    intro hn18
    exact cut_product_ge_thirty_two e2 e1 e4
      ((T.edgeAdjacent_comm e1 e2).1 h12) h24
      ((T.edgeEndpointDisjoint_comm e4 e1).1 h41) hn18
  exact
    { adjacent12 := h12
      noWeight3 := hno3
      witness4 := ⟨e4, h4, unique_physicalWeight hL h4, h41, h42⟩
      path12 := hpath12
      path24 := hpath24
      path124 := hpath124
      noWeight6 := hno6
      noWeight7 := hno7
      forced5 := hforced
      weight5_disjoint_e1 := h5dis1
      weight5_disjoint_e2 := h5dis2
      order18_cut := hcut }

/-- Adjacent row 4: the weight-four edge meets both earlier edges. -/
theorem adjacentMeetsBothRow_of_placement
    (hL : IsLeech T) (hn : 5 ≤ n)
    (e1 e2 e4 : T.Edge)
    (h1 : T.weight e1 = 1) (h2 : T.weight e2 = 2)
    (h4 : T.weight e4 = 4)
    (h12 : T.EdgeAdjacent e1 e2)
    (h41 : T.EdgeAdjacent e4 e1)
    (h42 : T.EdgeAdjacent e4 e2) :
    AdjacentMeetsBothRow T e1 e2 := by
  have hno3 := firstEdge_adjacent_no_weight_three hL e1 e2 h1 h2 h12
  have h14 : T.EdgeAdjacent e1 e4 := (T.edgeAdjacent_comm e4 e1).1 h41
  have h24 : T.EdgeAdjacent e2 e4 := (T.edgeAdjacent_comm e4 e2).1 h42
  have hpath12 : HasPathWeightSequence T [1, 2] := by
    simpa [h1, h2] using edgeAdjacent_hasPathWeightSequence (T := T) e1 e2 h12
  have hpath14 : HasPathWeightSequence T [1, 4] := by
    simpa [h1, h4] using edgeAdjacent_hasPathWeightSequence (T := T) e1 e4 h14
  have hpath24 : HasPathWeightSequence T [2, 4] := by
    simpa [h2, h4] using edgeAdjacent_hasPathWeightSequence (T := T) e2 e4 h24
  have hno5 : ¬∃ e : T.Edge, T.weight e = 5 := by
    simpa using no_physicalWeight_of_nontrivial_sequence hL hpath14
      (by simp) (by norm_num)
  have hno6 : ¬∃ e : T.Edge, T.weight e = 6 := by
    simpa using no_physicalWeight_of_nontrivial_sequence hL hpath24
      (by simp) (by norm_num)
  obtain ⟨e7, h7⟩ := adjacent_meets_both_exists_weight_seven hL hn
    e1 e2 e4 h1 h2 h4 h12 h41 h42 hno3 hno5 hno6
  have hspectrum := adjacent_meets_both_prefix_spectrum hL e1 e2 e4 e7
    h1 h2 h4 h7 h12 h41 h42 hno3 hno5 hno6
  have hforced : ForcedPrefixEdge T 7 {1, 2, 3, 4, 5, 6} := by
    exact ⟨e7, h7, unique_physicalWeight hL h7, hspectrum,
      by simpa [h7] using T.t2_forced_mex hL e7⟩
  exact
    { adjacent12 := h12
      noWeight3 := hno3
      witness4 := ⟨e4, h4, unique_physicalWeight hL h4, h41, h42⟩
      path12 := hpath12
      path14 := hpath14
      path24 := hpath24
      noWeight5 := hno5
      noWeight6 := hno6
      forced7 := hforced }

/-- Disjoint row 1: the weight-three edge meets neither earlier edge. -/
theorem disjointNoneRow_of_placement
    (hL : IsLeech T) (hn : 5 ≤ n)
    (e1 e2 e3 : T.Edge)
    (h1 : T.weight e1 = 1) (h2 : T.weight e2 = 2)
    (h3 : T.weight e3 = 3)
    (h12 : T.EdgeEndpointDisjoint e1 e2)
    (h31 : T.EdgeEndpointDisjoint e3 e1)
    (h32 : T.EdgeEndpointDisjoint e3 e2) :
    DisjointNoneRow T e1 e2 := by
  obtain ⟨e4, h4⟩ := disjoint_none_exists_weight_four hL hn e1 e3 h1 h3 h31
  have hspectrum := disjoint_none_prefix_spectrum hL e1 e2 e3 e4
    h1 h2 h3 h4 h12 h31 h32
  have hforced : ForcedPrefixEdge T 4 {1, 2, 3} := by
    exact ⟨e4, h4, unique_physicalWeight hL h4, hspectrum,
      by simpa [h4] using T.t2_forced_mex hL e4⟩
  exact
    { disjoint12 := h12
      witness3 := ⟨e3, h3, unique_physicalWeight hL h3, h31, h32⟩
      forced4 := hforced }

/-- Disjoint row 2: the weight-three edge meets only the weight-one edge. -/
theorem disjointMeetsOneRow_of_placement
    (hL : IsLeech T) (hn : 5 ≤ n)
    (e1 e2 e3 : T.Edge)
    (h1 : T.weight e1 = 1) (h2 : T.weight e2 = 2)
    (h3 : T.weight e3 = 3)
    (h12 : T.EdgeEndpointDisjoint e1 e2)
    (h31 : T.EdgeAdjacent e3 e1)
    (h32 : T.EdgeEndpointDisjoint e3 e2) :
    DisjointMeetsOneRow T e1 e2 := by
  have h13 : T.EdgeAdjacent e1 e3 := (T.edgeAdjacent_comm e3 e1).1 h31
  have hpath13 : HasPathWeightSequence T [1, 3] := by
    simpa [h1, h3] using edgeAdjacent_hasPathWeightSequence
      (T := T) e1 e3 h13
  have hno4 : ¬∃ e : T.Edge, T.weight e = 4 := by
    simpa using no_physicalWeight_of_nontrivial_sequence hL hpath13
      (by simp) (by norm_num)
  obtain ⟨e5, h5⟩ := disjoint_meets_one_exists_weight_five hL hn
    e1 e2 e3 h1 h2 h3 h32 hno4
  have hspectrum := disjoint_meets_one_prefix_spectrum hL e1 e2 e3 e5
    h1 h2 h3 h5 h12 h31 h32 hno4
  have hforced : ForcedPrefixEdge T 5 {1, 2, 3, 4} := by
    exact ⟨e5, h5, unique_physicalWeight hL h5, hspectrum,
      by simpa [h5] using T.t2_forced_mex hL e5⟩
  exact
    { disjoint12 := h12
      witness3 := ⟨e3, h3, unique_physicalWeight hL h3, h31, h32⟩
      path13 := hpath13
      noWeight4 := hno4
      forced5 := hforced }

/-- Disjoint row 3: the weight-three edge meets only the weight-two edge. -/
theorem disjointMeetsTwoRow_of_placement
    (hL : IsLeech T) (hn : 5 ≤ n)
    (e1 e2 e3 : T.Edge)
    (h1 : T.weight e1 = 1) (h2 : T.weight e2 = 2)
    (h3 : T.weight e3 = 3)
    (h12 : T.EdgeEndpointDisjoint e1 e2)
    (h31 : T.EdgeEndpointDisjoint e3 e1)
    (h32 : T.EdgeAdjacent e3 e2) :
    DisjointMeetsTwoRow T e1 e2 := by
  have h23 : T.EdgeAdjacent e2 e3 := (T.edgeAdjacent_comm e3 e2).1 h32
  have hpath23 : HasPathWeightSequence T [2, 3] := by
    simpa [h2, h3] using edgeAdjacent_hasPathWeightSequence
      (T := T) e2 e3 h23
  have hno5 : ¬∃ e : T.Edge, T.weight e = 5 := by
    simpa using no_physicalWeight_of_nontrivial_sequence hL hpath23
      (by simp) (by norm_num)
  obtain ⟨e4, h4⟩ := disjoint_none_exists_weight_four hL hn e1 e3 h1 h3 h31
  have hspectrum := disjoint_meets_two_prefix_spectrum hL e1 e2 e3 e4
    h1 h2 h3 h4 h12 h31 h32
  have hforced : ForcedPrefixEdge T 4 {1, 2, 3, 5} := by
    exact ⟨e4, h4, unique_physicalWeight hL h4, hspectrum,
      by simpa [h4] using T.t2_forced_mex hL e4⟩
  have h4dis1 : ∀ f4 : T.Edge, T.weight f4 = 4 →
      T.EdgeEndpointDisjoint f4 e1 := by
    intro f4 hf4
    have hne : f4 ≠ e1 := by intro h; have := congrArg T.weight h; omega
    apply (T.edgeEndpointDisjoint_iff_not_adjacent hne).2
    intro hadj
    have hseq41 : HasPathWeightSequence T [4, 1] := by
      simpa [hf4, h1] using edgeAdjacent_hasPathWeightSequence
        (T := T) f4 e1 hadj
    have heq := sequence_eq_or_reverse_of_sum_eq hL hseq41 hpath23
      (by simp) (by simp) (by norm_num)
    norm_num at heq
  exact
    { disjoint12 := h12
      witness3 := ⟨e3, h3, unique_physicalWeight hL h3, h31, h32⟩
      path23 := hpath23
      noWeight5 := hno5
      forced4 := hforced
      weight4_disjoint_e1 := h4dis1 }

/-- Disjoint row 4: the weight-three edge bridges the two earlier edges. -/
theorem disjointMeetsBothRow_of_placement
    (hL : IsLeech T) (hn : 5 ≤ n)
    (e1 e2 e3 : T.Edge)
    (h1 : T.weight e1 = 1) (h2 : T.weight e2 = 2)
    (h3 : T.weight e3 = 3)
    (h12 : T.EdgeEndpointDisjoint e1 e2)
    (h31 : T.EdgeAdjacent e3 e1)
    (h32 : T.EdgeAdjacent e3 e2) :
    DisjointMeetsBothRow T e1 e2 := by
  have h13 : T.EdgeAdjacent e1 e3 := (T.edgeAdjacent_comm e3 e1).1 h31
  have hpath13 : HasPathWeightSequence T [1, 3] := by
    simpa [h1, h3] using edgeAdjacent_hasPathWeightSequence
      (T := T) e1 e3 h13
  have hpath32 : HasPathWeightSequence T [3, 2] := by
    simpa [h3, h2] using edgeAdjacent_hasPathWeightSequence
      (T := T) e3 e2 h32
  have hchain : T.EdgeChain e1 e3 e2 := ⟨h13, h32, h12⟩
  have hpath132 : HasPathWeightSequence T [1, 3, 2] := by
    simpa [h1, h2, h3] using edgeChain_hasPathWeightSequence
      (T := T) e1 e3 e2 hchain
  have hno4 : ¬∃ e : T.Edge, T.weight e = 4 := by
    simpa using no_physicalWeight_of_nontrivial_sequence hL hpath13
      (by simp) (by norm_num)
  have hno5 : ¬∃ e : T.Edge, T.weight e = 5 := by
    simpa using no_physicalWeight_of_nontrivial_sequence hL hpath32
      (by simp) (by norm_num)
  have hno6 : ¬∃ e : T.Edge, T.weight e = 6 := by
    simpa using no_physicalWeight_of_nontrivial_sequence hL hpath132
      (by simp) (by norm_num)
  obtain ⟨e7, h7⟩ := disjoint_meets_both_exists_weight_seven hL hn hno4 hno5 hno6
  have hspectrum := disjoint_meets_both_prefix_spectrum hL e1 e2 e3 e7
    h1 h2 h3 h7 h12 h31 h32 hno4 hno5 hno6
  have hforced : ForcedPrefixEdge T 7 {1, 2, 3, 4, 5, 6} := by
    exact ⟨e7, h7, unique_physicalWeight hL h7, hspectrum,
      by simpa [h7] using T.t2_forced_mex hL e7⟩
  have hcut : n = 18 → 32 ≤ T.cutSize e3 * (n - T.cutSize e3) := by
    intro hn18
    exact cut_product_ge_thirty_two e3 e1 e2 h31 h32 h12 hn18
  exact
    { disjoint12 := h12
      witness3 := ⟨e3, h3, unique_physicalWeight hL h3, h31, h32, hcut⟩
      path13 := hpath13
      path32 := hpath32
      path132 := hpath132
      noWeight4 := hno4
      noWeight5 := hno5
      noWeight6 := hno6
      forced7 := hforced }

/-! ## Exhaustive graph-level endpoint -/

/-- Every naming of the physical weight-one and weight-two edges lies in
exactly one of the eight dossier rows (presented here as an exhaustive
disjunction).  The order-five bound is the precise uniform condition ensuring
that every displayed rank through seven belongs to the target spectrum. -/
theorem eightRowDossier_of_weights
    (hL : IsLeech T) (hn : 5 ≤ n)
    (e1 e2 : T.Edge)
    (h1 : T.weight e1 = 1) (h2 : T.weight e2 = 2) :
    EightRowDossier T e1 e2 := by
  rcases firstEdge_split_of_weights hL (by omega : 4 ≤ n) e1 e2 h1 h2 with
    ⟨h12, hno3, hex4⟩ | ⟨h12, hex3⟩
  · obtain ⟨e4, h4, _⟩ := hex4
    have hne41 : e4 ≠ e1 := by intro h; have := congrArg T.weight h; omega
    have hne42 : e4 ≠ e2 := by intro h; have := congrArg T.weight h; omega
    rcases T.edgeAdjacent_or_endpointDisjoint hne41 with h41 | h41 <;>
      rcases T.edgeAdjacent_or_endpointDisjoint hne42 with h42 | h42
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        (adjacentMeetsBothRow_of_placement hL hn e1 e2 e4
          h1 h2 h4 h12 h41 h42))))
    · exact Or.inr (Or.inl
        (adjacentMeetsOneRow_of_placement hL hn e1 e2 e4
          h1 h2 h4 h12 h41 h42))
    · exact Or.inr (Or.inr (Or.inl
        (adjacentMeetsTwoRow_of_placement hL hn e1 e2 e4
          h1 h2 h4 h12 h41 h42)))
    · exact Or.inl
        (adjacentNoneRow_of_placement hL hn e1 e2 e4
          h1 h2 h4 h12 h41 h42)
  · obtain ⟨e3, h3, _⟩ := hex3
    have hne31 : e3 ≠ e1 := by intro h; have := congrArg T.weight h; omega
    have hne32 : e3 ≠ e2 := by intro h; have := congrArg T.weight h; omega
    rcases T.edgeAdjacent_or_endpointDisjoint hne31 with h31 | h31 <;>
      rcases T.edgeAdjacent_or_endpointDisjoint hne32 with h32 | h32
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (disjointMeetsBothRow_of_placement hL hn e1 e2 e3
          h1 h2 h3 h12 h31 h32)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (disjointMeetsOneRow_of_placement hL hn e1 e2 e3
          h1 h2 h3 h12 h31 h32))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (disjointMeetsTwoRow_of_placement hL hn e1 e2 e3
          h1 h2 h3 h12 h31 h32)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (disjointNoneRow_of_placement hL hn e1 e2 e3
          h1 h2 h3 h12 h31 h32)))))

/-- Paper-facing bundle: the first two physical edges exist uniquely, and
every choice of their names satisfies the complete eight-row dossier. -/
theorem firstEdge_eightRowDossier
    (hL : IsLeech T) (hn : 5 ≤ n) :
    (∃! e1 : T.Edge, T.weight e1 = 1) ∧
    (∃! e2 : T.Edge, T.weight e2 = 2) ∧
    ∀ e1 e2 : T.Edge,
      T.weight e1 = 1 → T.weight e2 = 2 →
      EightRowDossier T e1 e2 := by
  exact ⟨t1_existsUnique_weight_one hL (by omega),
    t1_existsUnique_weight_two hL (by omega),
    fun e1 e2 h1 h2 => eightRowDossier_of_weights hL hn e1 e2 h1 h2⟩

end FirstEdgeDossier

end LeechTrees.Foundation
