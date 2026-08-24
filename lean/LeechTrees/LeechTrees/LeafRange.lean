import LeechTrees.Extensions

/-!
# Rooted-depth and unchanged-subtree range obstructions

This module supplies the graph adapters left deliberately outside the generic
extension kernels.  `UnchangedSubtreeData` names an induced copy of the old
tree and preserves its indexed metric.  New edges, their cardinality, their
freshness, and the path containing two of them are all derived facts.
-/

open scoped BigOperators

namespace LeechTrees.LeafRange

open LeechTrees.Foundation
open LeechTrees.Extension

/-! ## The rooted-depth obstruction -/

theorem rootedDepth_lt_order_of_eq_range
    {m : ℕ} {T : PosIntTree m} {v : Fin m}
    (hdepth : rootedDepthSet T v = Finset.range m) (u : Fin m) :
    T.dist v u < m := by
  have hu : T.dist v u ∈ rootedDepthSet T v := by
    unfold rootedDepthSet
    exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
  rw [hdepth] at hu
  simpa only [Finset.mem_range] using hu

/-- If all rooted depths are `0,...,m-1`, then every physical edge has weight
strictly below `m`.  This is a consequence of the actual deletion-side
decomposition, not an abstract triangle inequality. -/
theorem edge_weight_lt_order_of_rootedDepthSet_eq_range
    {m : ℕ} {T : PosIntTree m} {v : Fin m}
    (hdepth : rootedDepthSet T v = Finset.range m) (e : T.Edge) :
    T.weight e < m := by
  rcases T.cut_cover e v with hv | hv
  · have hroute := T.cross_distance_decomposition e hv
        (T.edgeRight_mem_RightCut e)
    rw [T.dist_self] at hroute
    have hd := rootedDepth_lt_order_of_eq_range hdepth (T.edgeRight e)
    omega
  · have hroute := T.cross_distance_decomposition e
        (T.edgeLeft_mem_LeftCut e) hv
    rw [T.dist_self] at hroute
    have hd := rootedDepth_lt_order_of_eq_range hdepth (T.edgeLeft e)
    rw [T.dist_comm v (T.edgeLeft e)] at hd
    omega

/-- Under the full rooted-depth range hypothesis, every actual edge is
incident with the root.  The proof realizes the physical weight as a rooted
depth and invokes indexed pair-distance injectivity on the frozen bytes. -/
theorem every_edge_incident_root_of_rootedDepthSet_eq_range
    {m : ℕ} {T : PosIntTree m} (hL : IsLeech T) {v : Fin m}
    (hdepth : rootedDepthSet T v = Finset.range m) (e : T.Edge) :
    v = T.edgeLeft e ∨ v = T.edgeRight e := by
  have hwlt := edge_weight_lt_order_of_rootedDepthSet_eq_range hdepth e
  have hwmem : T.weight e ∈ rootedDepthSet T v := by
    rw [hdepth]
    simpa only [Finset.mem_range] using hwlt
  unfold rootedDepthSet at hwmem
  rcases Finset.mem_image.mp hwmem with ⟨z, -, hz⟩
  have hvz : v ≠ z := by
    intro h
    subst z
    rw [T.dist_self] at hz
    have hwpos := T.weight_pos e
    omega
  let q : VertexPair m := VertexPair.ofDistinct v z hvz
  have hqdist : T.pairDist q = T.weight e := by
    change T.pairDist (VertexPair.ofDistinct v z hvz) = T.weight e
    rw [T.pairDist_pairOfDistinct v z hvz, hz]
  have hqedge : q = T.edgePair e :=
    hL.pairDist_injective (hqdist.trans (T.edgePair_dist e).symm)
  have hedgePair : T.edgePair e =
      VertexPair.ofDistinct (T.edgeLeft e) (T.edgeRight e)
        (ne_of_lt (T.edgeLeft_lt_edgeRight e)) := by
    unfold PosIntTree.edgePair
    symm
    exact VertexPair.ofDistinct_eq_of_lt _ (T.edgeLeft_lt_edgeRight e)
  have hpairs :=
    (LeechTrees.QHop.VertexPair.ofDistinct_eq_iff hvz
      (ne_of_lt (T.edgeLeft_lt_edgeRight e))).mp
      (hqedge.trans hedgePair)
  rcases hpairs with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

private theorem exists_otherEndpoint_of_incident
    {m : ℕ} (T : PosIntTree m) (e : T.Edge) (v : Fin m)
    (hinc : v = T.edgeLeft e ∨ v = T.edgeRight e) :
    ∃ x : Fin m, x ≠ v ∧ e.1 = s(v, x) := by
  rcases hinc with h | h
  · refine ⟨T.edgeRight e, ?_, ?_⟩
    · intro hx
      have hlt := T.edgeLeft_lt_edgeRight e
      omega
    · rw [T.edge_eq_mk_endpoints e, h]
  · refine ⟨T.edgeLeft e, ?_, ?_⟩
    · intro hx
      have hlt := T.edgeLeft_lt_edgeRight e
      omega
    · rw [T.edge_eq_mk_endpoints e, h]
      exact Sym2.eq_swap

/-- The other endpoints of two distinct actual edges meeting at `v` are at
distance equal to the sum of the two physical weights. -/
private theorem dist_otherEndpoints_eq_add
    {m : ℕ} (T : PosIntTree m) (e f : T.Edge) (hef : e ≠ f)
    {v x y : Fin m} (he : e.1 = s(v, x)) (hf : f.1 = s(v, y)) :
    T.dist x y = T.weight e + T.weight f := by
  have hvx : T.graph.Adj v x := by
    rw [← SimpleGraph.mem_edgeSet, ← he]
    exact e.2
  have hvy : T.graph.Adj v y := by
    rw [← SimpleGraph.mem_edgeSet, ← hf]
    exact f.2
  have hxy : x ≠ y := by
    intro h
    apply hef
    apply Subtype.ext
    rw [he, hf, h]
  have hyx : y ≠ x := hxy.symm
  have hyv : y ≠ v := hvy.ne.symm
  let pxv : T.graph.Path x v := SimpleGraph.Path.singleton hvx.symm
  let route : T.graph.Walk x y := pxv.1.concat hvy
  have hynot : y ∉ pxv.1.support := by
    simp [pxv, SimpleGraph.Path.singleton, hyx, hyv]
  have hroute : route.IsPath := pxv.2.concat hynot hvy
  have hwx : T.weightOfPair s(x, v) = T.weight e := by
    rw [Sym2.eq_swap, ← he]
    exact T.weightOfPair_edge e
  have hwy : T.weightOfPair s(v, y) = T.weight f := by
    rw [← hf]
    exact T.weightOfPair_edge f
  calc
    T.dist x y = T.walkWeight route :=
      (T.path_walkWeight_eq_dist ⟨route, hroute⟩).symm
    _ = T.weight e + T.weight f := by
      simp [route, pxv, SimpleGraph.Path.singleton, PosIntTree.walkWeight,
        hwx, hwy]

/-- No Leech tree of order at least four has rooted depths exactly
`0,...,m-1`.  The collision is between the pair joining the non-root
endpoints of the weight-one and weight-two edges and the rooted depth-three
pair. -/
theorem rootedDepthSet_ne_range_of_four_le
    {m : ℕ} {T : PosIntTree m} (hL : IsLeech T) (hm : 4 ≤ m)
    (v : Fin m) : rootedDepthSet T v ≠ Finset.range m := by
  intro hdepth
  obtain ⟨e1, he1, -⟩ := t1_existsUnique_weight_one hL (by omega)
  obtain ⟨e2, he2, -⟩ := t1_existsUnique_weight_two hL (by omega)
  have he12 : e1 ≠ e2 := by
    intro h
    subst e2
    omega
  have hi1 := every_edge_incident_root_of_rootedDepthSet_eq_range hL hdepth e1
  have hi2 := every_edge_incident_root_of_rootedDepthSet_eq_range hL hdepth e2
  obtain ⟨x, hxv, hxedge⟩ := exists_otherEndpoint_of_incident T e1 v hi1
  obtain ⟨y, hyv, hyedge⟩ := exists_otherEndpoint_of_incident T e2 v hi2
  have hxy : x ≠ y := by
    intro h
    apply he12
    apply Subtype.ext
    rw [hxedge, hyedge, h]
  have hdxy := dist_otherEndpoints_eq_add T e1 e2 he12 hxedge hyedge
  rw [he1, he2] at hdxy
  have h3mem : 3 ∈ rootedDepthSet T v := by
    rw [hdepth]
    simp only [Finset.mem_range]
    omega
  unfold rootedDepthSet at h3mem
  rcases Finset.mem_image.mp h3mem with ⟨z, -, hz⟩
  have hvz : v ≠ z := by
    intro h
    subst z
    rw [T.dist_self] at hz
    omega
  have hpXY : T.pairDist (VertexPair.ofDistinct x y hxy) = 3 := by
    rw [T.pairDist_pairOfDistinct x y hxy, hdxy]
  have hpVZ : T.pairDist (VertexPair.ofDistinct v z hvz) = 3 := by
    rw [T.pairDist_pairOfDistinct v z hvz, hz]
  have hpairs : VertexPair.ofDistinct x y hxy =
      VertexPair.ofDistinct v z hvz :=
    hL.pairDist_injective (hpXY.trans hpVZ.symm)
  rcases (LeechTrees.QHop.VertexPair.ofDistinct_eq_iff hxy hvz).mp hpairs with h | h
  · exact hxv h.1
  · exact hyv h.2

/-- Tail-set obstruction obtained by combining the exact tail
characterization with the rooted-depth theorem.  This statement concerns
`CompletesOneLeafTail`; an operation-level leaf-attachment adapter is a
separate interface. -/
theorem no_completesOneLeafTail_of_four_le
    {m : ℕ} {T : PosIntTree m} (hL : IsLeech T) (hm : 4 ≤ m)
    (v : Fin m) (q : ℕ) : ¬ CompletesOneLeafTail T v q := by
  intro htail
  have hchar := (completesOneLeafTail_iff T v q (by omega)).1 htail
  exact rootedDepthSet_ne_range_of_four_le hL hm v hchar.2

/-! ## Two actual edges lie on one actual pair path -/

private theorem pathEdges_ofDistinct
    {n : ℕ} (U : PosIntTree n) {a b : Fin n} (hab : a ≠ b) :
    U.pathEdges (VertexPair.ofDistinct a b hab).left
      (VertexPair.ofDistinct a b hab).right = U.pathEdges a b := by
  by_cases hlt : a < b
  · simp [VertexPair.ofDistinct, hlt, VertexPair.left, VertexPair.right]
  · simp only [VertexPair.ofDistinct, dif_neg hlt,
      VertexPair.left, VertexPair.right]
    exact U.pathEdges_comm b a

private theorem exists_pair_of_raw_path_memberships
    {n : ℕ} (U : PosIntTree n) (e f : U.Edge) {a b : Fin n}
    (he : e.1 ∈ U.pathEdges a b) (hf : f.1 ∈ U.pathEdges a b) :
    ∃ p : VertexPair n,
      e.1 ∈ U.pathEdges p.left p.right ∧
      f.1 ∈ U.pathEdges p.left p.right := by
  have hab : a ≠ b := by
    intro h
    subst b
    rw [U.pathEdges_self] at he
    simp at he
  refine ⟨VertexPair.ofDistinct a b hab, ?_, ?_⟩
  · rw [pathEdges_ofDistinct U hab]
    exact he
  · rw [pathEdges_ofDistinct U hab]
    exact hf

private theorem distinct_edge_endpoints_same_cut
    {n : ℕ} (U : PosIntTree n) (e f : U.Edge) (hef : e ≠ f) :
    (U.LeftCut e (U.edgeLeft f) ∧ U.LeftCut e (U.edgeRight f)) ∨
    (U.RightCut e (U.edgeLeft f) ∧ U.RightCut e (U.edgeRight f)) := by
  have hefval : e.1 ≠ f.1 := fun h => hef (Subtype.ext h)
  have havoid : e.1 ∉ U.pathEdges (U.edgeLeft f) (U.edgeRight f) := by
    rw [U.pathEdges_edge f]
    simpa using hefval
  have hreach : (U.cutGraph e).Reachable (U.edgeLeft f) (U.edgeRight f) :=
    (U.cut_reachable_iff_not_mem_pathEdges e _ _).2 havoid
  rcases U.cut_cover e (U.edgeLeft f) with hl | hr
  · left
    exact ⟨hl, hreach.symm.trans hl⟩
  · right
    exact ⟨hr, hreach.symm.trans hr⟩

/-- In a tree, any two distinct physical edges occur together on the
canonical path of an actual unordered vertex pair. -/
theorem exists_pair_containing_two_edges
    {n : ℕ} (U : PosIntTree n) (e f : U.Edge) (hef : e ≠ f) :
    ∃ p : VertexPair n,
      e.1 ∈ U.pathEdges p.left p.right ∧
      f.1 ∈ U.pathEdges p.left p.right := by
  rcases distinct_edge_endpoints_same_cut U e f hef with hleft | hright
  · rcases U.cut_cover f (U.edgeRight e) with hefL | hefR
    · apply exists_pair_of_raw_path_memberships U e f
      · exact (U.mem_pathEdges_iff_opposite_cuts e _ _).2
          (Or.inr ⟨U.edgeRight_mem_RightCut e, hleft.2⟩)
      · exact (U.mem_pathEdges_iff_opposite_cuts f _ _).2
          (Or.inl ⟨hefL, U.edgeRight_mem_RightCut f⟩)
    · apply exists_pair_of_raw_path_memberships U e f
      · exact (U.mem_pathEdges_iff_opposite_cuts e _ _).2
          (Or.inr ⟨U.edgeRight_mem_RightCut e, hleft.1⟩)
      · exact (U.mem_pathEdges_iff_opposite_cuts f _ _).2
          (Or.inr ⟨hefR, U.edgeLeft_mem_LeftCut f⟩)
  · rcases U.cut_cover f (U.edgeLeft e) with hefL | hefR
    · apply exists_pair_of_raw_path_memberships U e f
      · exact (U.mem_pathEdges_iff_opposite_cuts e _ _).2
          (Or.inl ⟨U.edgeLeft_mem_LeftCut e, hright.2⟩)
      · exact (U.mem_pathEdges_iff_opposite_cuts f _ _).2
          (Or.inl ⟨hefL, U.edgeRight_mem_RightCut f⟩)
    · apply exists_pair_of_raw_path_memberships U e f
      · exact (U.mem_pathEdges_iff_opposite_cuts e _ _).2
          (Or.inl ⟨U.edgeLeft_mem_LeftCut e, hright.1⟩)
      · exact (U.mem_pathEdges_iff_opposite_cuts f _ _).2
          (Or.inr ⟨hefR, U.edgeLeft_mem_LeftCut f⟩)

/-- The two positive physical weights of distinct edges on one pair path are
bounded by that pair distance. -/
theorem two_edge_weights_le_pairDist
    {n : ℕ} (U : PosIntTree n) (e f : U.Edge) (hef : e ≠ f)
    (p : VertexPair n)
    (he : e.1 ∈ U.pathEdges p.left p.right)
    (hf : f.1 ∈ U.pathEdges p.left p.right) :
    U.weight e + U.weight f ≤ U.pairDist p := by
  classical
  have hefval : e.1 ≠ f.1 := fun h => hef (Subtype.ext h)
  have hsubset : ({e.1, f.1} : Finset (Sym2 (Fin n))) ⊆
      U.pathEdges p.left p.right := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact he
    · exact hf
  have hsum :
      (∑ x ∈ ({e.1, f.1} : Finset (Sym2 (Fin n))), U.weightOfPair x) ≤
        U.dist p.left p.right := by
    unfold PosIntTree.dist
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_pair hefval, U.weightOfPair_edge e,
    U.weightOfPair_edge f] at hsum
  simpa [PosIntTree.pairDist] using hsum

/-! ## An exact unchanged connected-subtree interface -/

/-- An induced named copy of the old tree inside the larger tree, together
with preservation of every indexed old distance.  Since both graphs are
trees and the old copy is connected, inducedness is the exact no-new-chord
form of being an unchanged connected subtree. -/
structure UnchangedSubtreeData {m k : ℕ}
    (T : PosIntTree m) (U : PosIntTree (m + k)) where
  embedding : T.graph ↪g U.graph
  pairDist_eq : ∀ p,
    U.pairDist (mapVertexPair embedding.toEmbedding p) = T.pairDist p

namespace UnchangedSubtreeData

variable {m k : ℕ} {T : PosIntTree m} {U : PosIntTree (m + k)}

def retain (E : UnchangedSubtreeData T U) : RetainsOldMetric T U where
  vertex := E.embedding.toEmbedding
  pairDist_eq := E.pairDist_eq

noncomputable def oldEdgeSet (E : UnchangedSubtreeData T U) : Finset U.Edge :=
  Finset.univ.map E.embedding.mapEdgeSet

noncomputable def newEdgeSet (E : UnchangedSubtreeData T U) : Finset U.Edge :=
  Finset.univ \ E.oldEdgeSet

theorem oldEdgeSet_card (E : UnchangedSubtreeData T U) :
    E.oldEdgeSet.card = Fintype.card T.Edge := by
  classical
  simp [oldEdgeSet]

theorem newEdgeSet_card (E : UnchangedSubtreeData T U) (_hm : 1 ≤ m) :
    E.newEdgeSet.card = k := by
  classical
  have hTcard :=
    LeechTrees.OddEdges.GraphAdapter.physicalEdge_card_add_one T
  have hUcard :=
    LeechTrees.OddEdges.GraphAdapter.physicalEdge_card_add_one U
  have hsub : E.oldEdgeSet ⊆ (Finset.univ : Finset U.Edge) := by simp
  rw [newEdgeSet, Finset.card_sdiff_of_subset hsub, E.oldEdgeSet_card]
  simp only [Finset.card_univ]
  omega

private theorem edge_mem_oldEdgeSet_of_pair_eq
    (E : UnchangedSubtreeData T U) (f : U.Edge) (p : VertexPair m)
    (hpair : U.edgePair f =
      mapVertexPair E.embedding.toEmbedding p) :
    f ∈ E.oldEdgeSet := by
  classical
  by_cases hlt : E.embedding p.left < E.embedding p.right
  · have hpair' := hpair
    unfold mapVertexPair VertexPair.ofDistinct at hpair'
    simp only [RelEmbedding.coe_toEmbedding] at hpair'
    rw [dif_pos hlt] at hpair'
    have hl : U.edgeLeft f = E.embedding p.left := by
      simpa [PosIntTree.edgePair, VertexPair.left, VertexPair.right] using
        congrArg VertexPair.left hpair'
    have hr : U.edgeRight f = E.embedding p.right := by
      simpa [PosIntTree.edgePair, VertexPair.left, VertexPair.right] using
        congrArg VertexPair.right hpair'
    have hadjU : U.graph.Adj (E.embedding p.left) (E.embedding p.right) := by
      simpa [hl, hr] using U.edge_adj f
    have hadjT : T.graph.Adj p.left p.right :=
      E.embedding.map_adj_iff.mp hadjU
    let e : T.Edge := ⟨s(p.left, p.right), hadjT⟩
    have heq : E.embedding.mapEdgeSet e = f := by
      apply Subtype.ext
      change Sym2.map (fun x => E.embedding x) s(p.left, p.right) = f.1
      rw [Sym2.map_pair_eq, U.edge_eq_mk_endpoints f, hl, hr]
    exact Finset.mem_map.mpr ⟨e, Finset.mem_univ _, heq⟩
  · have hpair' := hpair
    unfold mapVertexPair VertexPair.ofDistinct at hpair'
    simp only [RelEmbedding.coe_toEmbedding] at hpair'
    rw [dif_neg hlt] at hpair'
    have hl : U.edgeLeft f = E.embedding p.right := by
      simpa [PosIntTree.edgePair, VertexPair.left, VertexPair.right] using
        congrArg VertexPair.left hpair'
    have hr : U.edgeRight f = E.embedding p.left := by
      simpa [PosIntTree.edgePair, VertexPair.left, VertexPair.right] using
        congrArg VertexPair.right hpair'
    have hadjU : U.graph.Adj (E.embedding p.left) (E.embedding p.right) := by
      simpa [hl, hr] using (U.edge_adj f).symm
    have hadjT : T.graph.Adj p.left p.right :=
      E.embedding.map_adj_iff.mp hadjU
    let e : T.Edge := ⟨s(p.left, p.right), hadjT⟩
    have heq : E.embedding.mapEdgeSet e = f := by
      apply Subtype.ext
      change Sym2.map (fun x => E.embedding x) s(p.left, p.right) = f.1
      rw [Sym2.map_pair_eq, U.edge_eq_mk_endpoints f, hl, hr]
      exact Sym2.eq_swap
    exact Finset.mem_map.mpr ⟨e, Finset.mem_univ _, heq⟩

theorem newEdge_pair_fresh (E : UnchangedSubtreeData T U) (f : U.Edge)
    (hf : f ∈ E.newEdgeSet) :
    ∀ p : VertexPair m,
      U.edgePair f ≠ mapVertexPair E.embedding.toEmbedding p := by
  intro p hp
  have hold := edge_mem_oldEdgeSet_of_pair_eq E f p hp
  exact (Finset.mem_sdiff.mp hf).2 hold

theorem newEdge_weight_gt_target
    (E : UnchangedSubtreeData T U) (hT : IsLeech T) (hU : IsLeech U)
    (f : U.Edge) (hf : f ∈ E.newEdgeSet) :
    targetN m < U.weight f := by
  have hfresh := E.newEdge_pair_fresh f hf
  have hgt := E.retain.fresh_pair_gt_target hT hU (U.edgePair f) hfresh
  simpa using hgt

/-- The exact binomial decomposition needed to rewrite the larger target. -/
theorem targetN_add (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) :
    targetN (m + k) = targetN m + m * k + targetN k := by
  have hmN := two_mul_targetN m
  have hkN := two_mul_targetN k
  have hmkN := two_mul_targetN (m + k)
  have hmPred : m = (m - 1) + 1 := by omega
  have hkPred : k = (k - 1) + 1 := by omega
  have hsumPred : m + k - 1 = (m - 1) + k := by omega
  nlinarith

/-- Any unchanged connected-subtree extension by at least two vertices must
satisfy the D5 range inequality.  The witnessing pair and both new-edge
weights are derived from the actual larger tree. -/
theorem unchangedSubtree_range_necessary
    (E : UnchangedSubtreeData T U) (hT : IsLeech T) (hU : IsLeech U)
    (hm : 1 ≤ m) (hk : 2 ≤ k) :
    targetN m + 3 ≤ m * k + targetN k := by
  classical
  have hcard := E.newEdgeSet_card hm
  have hcardTwo : 1 < E.newEdgeSet.card := by omega
  obtain ⟨e, he, f, hf, hef⟩ := Finset.one_lt_card.mp hcardTwo
  have hegt := E.newEdge_weight_gt_target hT hU e he
  have hfgt := E.newEdge_weight_gt_target hT hU f hf
  have hwne : U.weight e ≠ U.weight f := by
    intro hw
    exact hef (t1_edge_weight_injective hU hw)
  have hweights : 2 * targetN m + 3 ≤ U.weight e + U.weight f := by
    omega
  obtain ⟨p, hep, hfp⟩ := exists_pair_containing_two_edges U e f hef
  have hsum := two_edge_weights_le_pairDist U e f hef p hep hfp
  have hmax := hU.pairDist_le_target p
  have htotal : 2 * targetN m + 3 ≤ targetN (m + k) := by omega
  rw [targetN_add m k hm (by omega)] at htotal
  omega

theorem no_unchangedSubtreeExtension_of_range
    (E : UnchangedSubtreeData T U) (hT : IsLeech T) (hU : IsLeech U)
    (hm : 1 ≤ m) (hk : 2 ≤ k)
    (hrange : m * k + targetN k < targetN m + 3) : False := by
  have hnecessary := E.unchangedSubtree_range_necessary hT hU hm hk
  omega

theorem two_new_vertices_range_inequality
    {m : ℕ} (hm : 5 ≤ m) :
    m * 2 + targetN 2 < targetN m + 3 := by
  have hN := two_mul_targetN m
  have hmPred : m = (m - 1) + 1 := by omega
  have htwo : targetN 2 = 1 := by norm_num [targetN]
  rw [htwo]
  nlinarith

/-- D5 with `k=2`: no unchanged connected-subtree extension exists from any
base order at least five. -/
theorem no_unchangedSubtreeExtension_two_new_of_five_le
    {m : ℕ} {T : PosIntTree m} {U : PosIntTree (m + 2)}
    (E : UnchangedSubtreeData T U) (hT : IsLeech T) (hU : IsLeech U)
    (hm : 5 ≤ m) : False := by
  exact E.no_unchangedSubtreeExtension_of_range hT hU (by omega) (by omega)
    (two_new_vertices_range_inequality hm)

theorem order18_range_inequality
    {k : ℕ} (hk2 : 2 ≤ k) (hk7 : k ≤ 7) :
    18 * k + targetN k < targetN 18 + 3 := by
  interval_cases k <;> norm_num [targetN, Nat.choose_two_right]

/-- For an order-18 base, D5 excludes every unchanged connected-subtree
extension by `2,...,7` vertices. -/
theorem no_order18_unchangedSubtreeExtension_two_to_seven
    {k : ℕ} {T : PosIntTree 18} {U : PosIntTree (18 + k)}
    (E : UnchangedSubtreeData T U) (hT : IsLeech T) (hU : IsLeech U)
    (hk2 : 2 ≤ k) (hk7 : k ≤ 7) : False := by
  exact E.no_unchangedSubtreeExtension_of_range hT hU (by omega) hk2
    (order18_range_inequality hk2 hk7)

end UnchangedSubtreeData

end LeechTrees.LeafRange
