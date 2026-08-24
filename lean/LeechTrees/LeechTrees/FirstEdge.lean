import LeechTrees.Foundations

/-!
# The first two physical edges

This module proves only the safe first-edge split.  It does not encode the
later eight-row placement dossier.
-/

namespace LeechTrees.Foundation

namespace PosIntTree

variable {n : ℕ} (T : PosIntTree n)

/-- Two distinct actual edges are adjacent when their endpoint pairs share a
vertex.  The explicit inequality follows the usual graph-theoretic convention
that an edge is not adjacent to itself. -/
def EdgeAdjacent (e f : T.Edge) : Prop :=
  e ≠ f ∧ ∃ v : Fin n, v ∈ e.1 ∧ v ∈ f.1

/-- Two actual edges are endpoint-disjoint. -/
def EdgeEndpointDisjoint (e f : T.Edge) : Prop :=
  ∀ v : Fin n, v ∈ e.1 → v ∈ f.1 → False

theorem edgeAdjacent_comm (e f : T.Edge) :
    T.EdgeAdjacent e f ↔ T.EdgeAdjacent f e := by
  constructor
  · rintro ⟨hef, v, hve, hvf⟩
    exact ⟨hef.symm, v, hvf, hve⟩
  · rintro ⟨hfe, v, hvf, hve⟩
    exact ⟨hfe.symm, v, hve, hvf⟩

/-- Distinct simple edges have at most one common endpoint. -/
theorem edgeAdjacent_existsUnique_commonEndpoint {e f : T.Edge}
    (h : T.EdgeAdjacent e f) :
    ∃! v : Fin n, v ∈ e.1 ∧ v ∈ f.1 := by
  rcases h with ⟨hef, v, hve, hvf⟩
  refine ⟨v, ⟨hve, hvf⟩, ?_⟩
  intro w hw
  by_contra hvw
  have hvw' : v ≠ w := fun h => hvw h.symm
  have he : e.1 = s(v, w) :=
    (Sym2.mem_and_mem_iff hvw').mp ⟨hve, hw.1⟩
  have hf : f.1 = s(v, w) :=
    (Sym2.mem_and_mem_iff hvw').mp ⟨hvf, hw.2⟩
  apply hef
  apply Subtype.ext
  exact he.trans hf.symm

end PosIntTree

section FirstEdge

variable {n : ℕ} {T : PosIntTree n}

private def edgeOfAdj {u v : Fin n} (h : T.graph.Adj u v) : T.Edge :=
  ⟨s(u, v), by
    rw [SimpleGraph.mem_edgeSet]
    exact h⟩

@[simp] private theorem edgeOfAdj_val {u v : Fin n} (h : T.graph.Adj u v) :
    (edgeOfAdj (T := T) h).1 = s(u, v) := rfl

private theorem weight_edgeOfAdj {u v : Fin n} (h : T.graph.Adj u v) :
    T.weight (edgeOfAdj (T := T) h) = T.weightOfPair s(u, v) := by
  change T.weight (edgeOfAdj (T := T) h) =
    T.weightOfPair (edgeOfAdj (T := T) h).1
  exact (T.weightOfPair_edge (edgeOfAdj (T := T) h)).symm

private noncomputable def pathWeightList {u v : Fin n}
    (p : T.graph.Path u v) : List ℕ :=
  p.1.edges.map T.weightOfPair

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

private theorem positive_nodup_sum_three_shape
    {weights : List ℕ}
    (positive : ∀ w ∈ weights, 0 < w)
    (nodup : weights.Nodup)
    (total : weights.sum = 3) :
    weights = [3] ∨ weights = [1, 2] ∨ weights = [2, 1] := by
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
              simp only [List.sum_cons, List.sum_nil, add_zero] at total
              have hab : (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) := by omega
              rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr rfl)
          | cons c cs =>
              have ha : 0 < a := positive a (by simp)
              have hb : 0 < b := positive b (by simp)
              have hc : 0 < c := positive c (by simp)
              have hnot : a ∉ b :: c :: cs := (List.nodup_cons.mp nodup).1
              have hab : a ≠ b := by
                intro h
                apply hnot
                simp [h]
              simp only [List.sum_cons] at total
              omega

private theorem positive_nodup_sum_four_shape
    {weights : List ℕ}
    (positive : ∀ w ∈ weights, 0 < w)
    (nodup : weights.Nodup)
    (total : weights.sum = 4) :
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
              have hnot : a ∉ [b] := (List.nodup_cons.mp nodup).1
              have habne : a ≠ b := by
                intro h
                apply hnot
                simp [h]
              simp only [List.sum_cons, List.sum_nil, add_zero] at total
              have hab : (a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1) := by omega
              rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr rfl)
          | cons c cs =>
              have ha : 0 < a := positive a (by simp)
              have hb : 0 < b := positive b (by simp)
              have hc : 0 < c := positive c (by simp)
              have hnotA : a ∉ b :: c :: cs :=
                (List.nodup_cons.mp nodup).1
              have htail : (b :: c :: cs).Nodup :=
                (List.nodup_cons.mp nodup).2
              have hnotB : b ∉ c :: cs :=
                (List.nodup_cons.mp htail).1
              have hab : a ≠ b := by
                intro h
                apply hnotA
                simp [h]
              have hac : a ≠ c := by
                intro h
                apply hnotA
                simp [h]
              have hbc : b ≠ c := by
                intro h
                apply hnotB
                simp [h]
              simp only [List.sum_cons] at total
              omega

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
  refine ⟨first, ?_⟩
  rw [weight_edgeOfAdj]
  exact hhead

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
  have htailList :
      p.1.tail.edges.map T.weightOfPair = [b] := by
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

private theorem weightThreePath_shape (hL : IsLeech T)
    {u v : Fin n} (p : T.graph.Path u v)
    (htotal : T.walkWeight p.1 = 3) :
    (∃ e3 : T.Edge, T.weight e3 = 3) ∨
      ∃ e1 e2 : T.Edge,
        T.weight e1 = 1 ∧ T.weight e2 = 2 ∧ T.EdgeAdjacent e1 e2 := by
  have hsum : (pathWeightList (T := T) p).sum = 3 := by
    exact htotal
  rcases positive_nodup_sum_three_shape
      (pathWeightList_positive (T := T) p)
      (pathWeightList_nodup hL p) hsum with hsingle | hpair | hpair
  · exact Or.inl (physicalEdge_of_pathWeightList_singleton p hsingle)
  · exact Or.inr (adjacentEdges_of_pathWeightList_pair p hpair)
  · obtain ⟨e2, e1, h2, h1, hadj⟩ :=
      adjacentEdges_of_pathWeightList_pair p hpair
    exact Or.inr ⟨e1, e2, h1, h2,
      (T.edgeAdjacent_comm e1 e2).2 hadj⟩

private theorem weightFourPath_shape (hL : IsLeech T)
    {u v : Fin n} (p : T.graph.Path u v)
    (htotal : T.walkWeight p.1 = 4) :
    (∃ e4 : T.Edge, T.weight e4 = 4) ∨
      ∃ e3 : T.Edge, T.weight e3 = 3 := by
  have hsum : (pathWeightList (T := T) p).sum = 4 := by
    exact htotal
  rcases positive_nodup_sum_four_shape
      (pathWeightList_positive (T := T) p)
      (pathWeightList_nodup hL p) hsum with hsingle | hpair | hpair
  · exact Or.inl (physicalEdge_of_pathWeightList_singleton p hsingle)
  · obtain ⟨_, e3, _, h3, _⟩ :=
      adjacentEdges_of_pathWeightList_pair p hpair
    exact Or.inr ⟨e3, h3⟩
  · obtain ⟨e3, _, h3, _, _⟩ :=
      adjacentEdges_of_pathWeightList_pair p hpair
    exact Or.inr ⟨e3, h3⟩

private theorem sym2_pairOfDistinct (u v : Fin n) (huv : u ≠ v) :
    s((VertexPair.ofDistinct u v huv).left,
      (VertexPair.ofDistinct u v huv).right) = s(u, v) := by
  by_cases h : u < v
  · simp [VertexPair.ofDistinct, h, VertexPair.left, VertexPair.right]
  · simp [VertexPair.ofDistinct, h, VertexPair.left, VertexPair.right,
      Sym2.eq_swap]

/-- Adjacent physical edges of weights one and two realize distance three by
their two-edge path, so a physical weight-three edge would duplicate that
indexed pair distance. -/
theorem firstEdge_adjacent_no_weight_three
    (hL : IsLeech T) (e1 e2 : T.Edge)
    (h1 : T.weight e1 = 1) (h2 : T.weight e2 = 2)
    (hadj : T.EdgeAdjacent e1 e2) :
    ¬ ∃ e3 : T.Edge, T.weight e3 = 3 := by
  rintro ⟨e3, h3⟩
  obtain ⟨v, hv1, hv2⟩ := hadj.2
  let x : Fin n := Sym2.Mem.other hv1
  let y : Fin n := Sym2.Mem.other hv2
  have he1 : s(v, x) = e1.1 := by
    exact Sym2.other_spec hv1
  have he2 : s(v, y) = e2.1 := by
    exact Sym2.other_spec hv2
  have hvx : T.graph.Adj v x := by
    rw [← SimpleGraph.mem_edgeSet, he1]
    exact e1.2
  have hvy : T.graph.Adj v y := by
    rw [← SimpleGraph.mem_edgeSet, he2]
    exact e2.2
  have hxy : x ≠ y := by
    intro h
    apply hadj.1
    apply Subtype.ext
    rw [← he1, ← he2, h]
  let walkXY : T.graph.Walk x y :=
    SimpleGraph.Walk.cons hvx.symm
      (SimpleGraph.Walk.cons hvy SimpleGraph.Walk.nil)
  have hwalkPath : walkXY.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simp [walkXY, hvx.ne.symm, hvy.ne, hxy]
  let pathXY : T.graph.Path x y := ⟨walkXY, hwalkPath⟩
  have hwx : T.weightOfPair s(x, v) = 1 := by
    calc
      T.weightOfPair s(x, v) = T.weightOfPair s(v, x) := by
        rw [Sym2.eq_swap]
      _ = T.weightOfPair e1.1 := by rw [he1]
      _ = T.weight e1 := T.weightOfPair_edge e1
      _ = 1 := h1
  have hwy : T.weightOfPair s(v, y) = 2 := by
    calc
      T.weightOfPair s(v, y) = T.weightOfPair e2.1 := by rw [he2]
      _ = T.weight e2 := T.weightOfPair_edge e2
      _ = 2 := h2
  have hwalkWeight : T.walkWeight pathXY.1 = 3 := by
    simp [pathXY, walkXY, PosIntTree.walkWeight, hwx, hwy]
  have hdist : T.dist x y = 3 := by
    calc
      T.dist x y = T.walkWeight pathXY.1 :=
        (T.path_walkWeight_eq_dist pathXY).symm
      _ = 3 := hwalkWeight
  let pairXY : VertexPair n := VertexPair.ofDistinct x y hxy
  have hpairDist : T.pairDist pairXY = 3 := by
    rw [T.pairDist_pairOfDistinct]
    exact hdist
  have hedgeDist : T.pairDist (T.edgePair e3) = 3 := by
    rw [T.edgePair_dist, h3]
  have hpairs : pairXY = T.edgePair e3 :=
    hL.pairDist_injective (hpairDist.trans hedgeDist.symm)
  have he3 : e3.1 = s(x, y) := by
    calc
      e3.1 = s(T.edgeLeft e3, T.edgeRight e3) := T.edge_eq_mk_endpoints e3
      _ = s((T.edgePair e3).left, (T.edgePair e3).right) := rfl
      _ = s(pairXY.left, pairXY.right) := by rw [hpairs]
      _ = s(x, y) := sym2_pairOfDistinct x y hxy
  have hxyAdj : T.graph.Adj x y := by
    rw [← SimpleGraph.mem_edgeSet, ← he3]
    exact e3.2
  let direct : T.graph.Path x y := SimpleGraph.Path.singleton hxyAdj
  have hpaths : pathXY = direct :=
    (T.path_unique pathXY).trans (T.path_unique direct).symm
  have hlength := congrArg (fun p : T.graph.Path x y => p.1.length) hpaths
  simp [pathXY, walkXY, direct, SimpleGraph.Path.singleton] at hlength

private theorem rank_three_mem_target (hn : 3 ≤ n) :
    3 ∈ Finset.Icc 1 (targetN n) := by
  rw [Finset.mem_Icc]
  constructor
  · omega
  · have hc : Nat.choose 3 2 ≤ Nat.choose n 2 :=
      Nat.choose_le_choose 2 hn
    norm_num [targetN] at hc ⊢
    omega

private theorem rank_four_mem_target (hn : 4 ≤ n) :
    4 ∈ Finset.Icc 1 (targetN n) := by
  rw [Finset.mem_Icc]
  constructor
  · omega
  · have hc : Nat.choose 4 2 ≤ Nat.choose n 2 :=
      Nat.choose_le_choose 2 hn
    have hchoose : Nat.choose 4 2 = 6 := by
      norm_num [Nat.choose]
    rw [hchoose] at hc
    change 4 ≤ Nat.choose n 2
    omega

private theorem existsUnique_physicalWeight (hL : IsLeech T)
    {k : ℕ} (h : ∃ e : T.Edge, T.weight e = k) :
    ∃! e : T.Edge, T.weight e = k := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, he, ?_⟩
  intro f hf
  exact t1_edge_weight_injective hL (hf.trans he.symm)

/-- Safe adjacent/disjoint split for named actual physical edges of weights
one and two.  The lower bound is sharp for the combined statement: order
three has the adjacent `1,2` path but has no target rank four. -/
theorem firstEdge_split_of_weights
    (hL : IsLeech T) (hn : 4 ≤ n)
    (e1 e2 : T.Edge)
    (h1 : T.weight e1 = 1) (h2 : T.weight e2 = 2) :
    ((T.EdgeAdjacent e1 e2 ∧
        (¬ ∃ e3 : T.Edge, T.weight e3 = 3) ∧
        ∃! e4 : T.Edge, T.weight e4 = 4) ∨
      (T.EdgeEndpointDisjoint e1 e2 ∧
        ∃! e3 : T.Edge, T.weight e3 = 3)) := by
  have hne : e1 ≠ e2 := by
    intro heq
    have hw := congrArg T.weight heq
    omega
  by_cases hmeet : ∃ v : Fin n, v ∈ e1.1 ∧ v ∈ e2.1
  · have hadj : T.EdgeAdjacent e1 e2 := ⟨hne, hmeet⟩
    have hno3 := firstEdge_adjacent_no_weight_three hL e1 e2 h1 h2 hadj
    obtain ⟨p4, hp4, _⟩ :=
      hL.target_existsUnique 4 (rank_four_mem_target hn)
    have hwalk4 :
        T.walkWeight (T.path p4.left p4.right).1 = 4 := by
      calc
        T.walkWeight (T.path p4.left p4.right).1 =
            T.dist p4.left p4.right :=
          T.path_walkWeight_eq_dist (T.path p4.left p4.right)
        _ = T.pairDist p4 := rfl
        _ = 4 := hp4
    have hex4 : ∃ e4 : T.Edge, T.weight e4 = 4 := by
      rcases weightFourPath_shape hL (T.path p4.left p4.right) hwalk4 with h4 | h3
      · exact h4
      · exact (hno3 h3).elim
    exact Or.inl ⟨hadj, hno3, existsUnique_physicalWeight hL hex4⟩
  · have hdisjoint : T.EdgeEndpointDisjoint e1 e2 := by
      intro v hv1 hv2
      exact hmeet ⟨v, hv1, hv2⟩
    obtain ⟨p3, hp3, _⟩ :=
      hL.target_existsUnique 3 (rank_three_mem_target (by omega))
    have hwalk3 :
        T.walkWeight (T.path p3.left p3.right).1 = 3 := by
      calc
        T.walkWeight (T.path p3.left p3.right).1 =
            T.dist p3.left p3.right :=
          T.path_walkWeight_eq_dist (T.path p3.left p3.right)
        _ = T.pairDist p3 := rfl
        _ = 3 := hp3
    have hex3 : ∃ e3 : T.Edge, T.weight e3 = 3 := by
      rcases weightThreePath_shape hL (T.path p3.left p3.right) hwalk3 with
        h3 | ⟨f1, f2, hf1, hf2, hfadj⟩
      · exact h3
      · have hfe1 : f1 = e1 :=
          t1_edge_weight_injective hL (hf1.trans h1.symm)
        have hfe2 : f2 = e2 :=
          t1_edge_weight_injective hL (hf2.trans h2.symm)
        subst f1
        subst f2
        obtain ⟨v, hv1, hv2⟩ := hfadj.2
        exact (hdisjoint v hv1 hv2).elim
    exact Or.inr ⟨hdisjoint, existsUnique_physicalWeight hL hex3⟩

/-- Paper-facing first-edge theorem.  T1 supplies the unique physical edges of
weights one and two, and every naming of those edges satisfies the safe split. -/
theorem firstEdge_physical_split
    (hL : IsLeech T) (hn : 4 ≤ n) :
    (∃! e1 : T.Edge, T.weight e1 = 1) ∧
    (∃! e2 : T.Edge, T.weight e2 = 2) ∧
    ∀ e1 e2 : T.Edge,
      T.weight e1 = 1 → T.weight e2 = 2 →
      ((T.EdgeAdjacent e1 e2 ∧
          (¬ ∃ e3 : T.Edge, T.weight e3 = 3) ∧
          ∃! e4 : T.Edge, T.weight e4 = 4) ∨
        (T.EdgeEndpointDisjoint e1 e2 ∧
          ∃! e3 : T.Edge, T.weight e3 = 3)) := by
  exact ⟨t1_existsUnique_weight_one hL (by omega),
    t1_existsUnique_weight_two hL (by omega),
    fun e1 e2 h1 h2 => firstEdge_split_of_weights hL hn e1 e2 h1 h2⟩

end FirstEdge

end LeechTrees.Foundation
