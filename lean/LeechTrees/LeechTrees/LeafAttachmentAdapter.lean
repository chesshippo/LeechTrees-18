import LeechTrees.OperationAdapters
import LeechTrees.LeafRange

/-!
# Exact literal one-leaf attachment adapter

This downstream module closes the singleton boundary deliberately left open
by `OperationAdapters`.  `LiteralOneLeafAttachment` names an exhaustive old
copy, one fresh vertex, exactly one new edge at a named old port, and verbatim
old physical weights.  The leaf weight is the weight of that actual new edge,
so its positivity is derived from the positive-integral-tree structure.

The adapter derives old metric retention, classifies every genuinely new
indexed vertex pair, identifies its actual distance set with
`newLeafDistanceSet`, and only then invokes the frozen `LeafRange` theorem.
No reweighting or more general gluing operation is represented here.
-/

namespace LeechTrees.OperationAdapters

open LeechTrees.Foundation
open LeechTrees.Extension
open LeechTrees.LeafRange

/-- Exact relation saying that `U` is obtained from `T` by attaching one
fresh leaf at `port`, without changing any old physical edge or weight.

The global `edgeSet_eq` clause excludes every hidden chord or additional
leaf edge.  Its singleton term is the actual edge whose positive integral
weight is used below. -/
structure LiteralOneLeafAttachment {m : ℕ}
    (T : PosIntTree m) (U : PosIntTree (m + 1)) where
  oldEmbedding : T.graph ↪g U.graph
  leaf : Fin (m + 1)
  leaf_not_old : ∀ x, leaf ≠ oldEmbedding x
  vertex_cover : ∀ z, z = leaf ∨ ∃ x, oldEmbedding x = z
  port : Fin m
  edgeSet_eq :
    U.graph.edgeSet =
      (Sym2.map (fun x => oldEmbedding x) '' T.graph.edgeSet) ∪
      ({s(leaf, oldEmbedding port)} : Set (Sym2 (Fin (m + 1))))
  old_weight_eq : ∀ e : T.Edge,
    U.weightOfPair (Sym2.map (fun x => oldEmbedding x) e.1) = T.weight e

namespace LiteralOneLeafAttachment

variable {m : ℕ} {T : PosIntTree m} {U : PosIntTree (m + 1)}

def leafPair (L : LiteralOneLeafAttachment T U) :
    Sym2 (Fin (m + 1)) :=
  s(L.leaf, L.oldEmbedding L.port)

theorem leafPair_mem (L : LiteralOneLeafAttachment T U) :
    L.leafPair ∈ U.graph.edgeSet := by
  rw [L.edgeSet_eq]
  simp [leafPair]

def leafEdge (L : LiteralOneLeafAttachment T U) : U.Edge :=
  ⟨L.leafPair, L.leafPair_mem⟩

theorem leafEdge_val (L : LiteralOneLeafAttachment T U) :
    L.leafEdge.1 = L.leafPair := rfl

def leafWeight (L : LiteralOneLeafAttachment T U) : ℕ :=
  U.weight L.leafEdge

theorem leafWeight_pos (L : LiteralOneLeafAttachment T U) :
    0 < L.leafWeight :=
  U.weight_pos L.leafEdge

theorem leaf_adj (L : LiteralOneLeafAttachment T U) :
    U.graph.Adj L.leaf (L.oldEmbedding L.port) := by
  rw [← SimpleGraph.mem_edgeSet]
  exact L.leafPair_mem

def oldWeightedEmbedding (L : LiteralOneLeafAttachment T U) :
    WeightedGraphEmbedding T U where
  embedding := L.oldEmbedding
  weight_eq := L.old_weight_eq

/-- Every old indexed distance is derived to be unchanged. -/
theorem dist_old_eq (L : LiteralOneLeafAttachment T U) (x y : Fin m) :
    U.dist (L.oldEmbedding x) (L.oldEmbedding y) = T.dist x y :=
  L.oldWeightedEmbedding.dist_map x y

noncomputable def toRetainsOldMetric
    (L : LiteralOneLeafAttachment T U) : RetainsOldMetric T U :=
  L.oldWeightedEmbedding.retain

/-- The literal leaf-to-old route is the new physical leaf edge followed by
the mapped canonical old path.  Its distance formula is derived rather than
stored in the operation record. -/
theorem dist_leaf_old_eq (L : LiteralOneLeafAttachment T U) (x : Fin m) :
    U.dist L.leaf (L.oldEmbedding x) =
      L.leafWeight + T.dist L.port x := by
  let oldPath : U.graph.Path
      (L.oldEmbedding L.port) (L.oldEmbedding x) :=
    (T.path L.port x).mapEmbedding L.oldEmbedding
  have hleaf : L.leaf ∉ oldPath.1.support := by
    change L.leaf ∉
      ((T.path L.port x).1.map L.oldEmbedding.toHom).support
    simp only [SimpleGraph.Walk.support_map, List.mem_map,
      SimpleGraph.Embedding.coe_toHom, not_exists, not_and]
    intro y _ hy
    exact L.leaf_not_old y hy.symm
  let routeWalk : U.graph.Walk L.leaf (L.oldEmbedding x) :=
    .cons L.leaf_adj oldPath.1
  have hroute : routeWalk.IsPath := oldPath.2.cons hleaf
  let route : U.graph.Path L.leaf (L.oldEmbedding x) :=
    ⟨routeWalk, hroute⟩
  have holdPathWeight :
      U.walkWeight oldPath.1 = T.walkWeight (T.path L.port x).1 := by
    change U.walkWeight
        ((T.path L.port x).1.map L.oldEmbedding.toHom) =
      T.walkWeight (T.path L.port x).1
    exact L.oldWeightedEmbedding.walkWeight_map (T.path L.port x).1
  have hconsWeight :
      U.walkWeight route.1 =
        U.weightOfPair L.leafPair + U.walkWeight oldPath.1 := by
    simp [route, routeWalk, PosIntTree.walkWeight, leafPair]
  calc
    U.dist L.leaf (L.oldEmbedding x) = U.walkWeight route.1 :=
      (U.path_walkWeight_eq_dist route).symm
    _ = U.weightOfPair L.leafPair + U.walkWeight oldPath.1 := hconsWeight
    _ = L.leafWeight + T.walkWeight (T.path L.port x).1 := by
      rw [← L.leafEdge_val, U.weightOfPair_edge L.leafEdge,
        holdPathWeight]
      rfl
    _ = L.leafWeight + T.dist L.port x := by
      rw [T.path_walkWeight_eq_dist (T.path L.port x)]

noncomputable def leafVertexPair (L : LiteralOneLeafAttachment T U)
    (x : Fin m) : VertexPair (m + 1) :=
  VertexPair.ofDistinct L.leaf (L.oldEmbedding x) (L.leaf_not_old x)

theorem pairDist_leafVertexPair (L : LiteralOneLeafAttachment T U)
    (x : Fin m) :
    U.pairDist (L.leafVertexPair x) =
      L.leafWeight + T.dist L.port x := by
  rw [leafVertexPair, U.pairDist_pairOfDistinct]
  exact L.dist_leaf_old_eq x

theorem leafVertexPair_injective (L : LiteralOneLeafAttachment T U) :
    Function.Injective L.leafVertexPair := by
  intro x y hxy
  have hcases :=
    (LeechTrees.QHop.VertexPair.ofDistinct_eq_iff
      (L.leaf_not_old x) (L.leaf_not_old y)).mp hxy
  rcases hcases with h | h
  · exact L.oldEmbedding.injective h.2
  · exact (L.leaf_not_old y h.1).elim

noncomputable def oldPairSet (L : LiteralOneLeafAttachment T U) :
    Finset (VertexPair (m + 1)) :=
  Finset.univ.image (mapVertexPair L.oldEmbedding.toEmbedding)

/-- The actual new indexed pairs are all larger-tree pairs outside the
embedded old indexed-pair image. -/
noncomputable def actualNewPairSet (L : LiteralOneLeafAttachment T U) :
    Finset (VertexPair (m + 1)) :=
  Finset.univ \ L.oldPairSet

theorem leafVertexPair_fresh (L : LiteralOneLeafAttachment T U)
    (x : Fin m) :
    ∀ p : VertexPair m,
      L.leafVertexPair x ≠ mapVertexPair L.oldEmbedding.toEmbedding p := by
  intro p hp
  unfold leafVertexPair mapVertexPair at hp
  have hcases :=
    (LeechTrees.QHop.VertexPair.ofDistinct_eq_iff
      (L.leaf_not_old x)
      (L.oldEmbedding.injective.ne (ne_of_lt p.left_lt_right))).mp hp
  rcases hcases with h | h
  · exact L.leaf_not_old p.left h.1
  · exact L.leaf_not_old p.right h.1

theorem leafVertexPair_mem_actualNewPairSet
    (L : LiteralOneLeafAttachment T U) (x : Fin m) :
    L.leafVertexPair x ∈ L.actualNewPairSet := by
  rw [actualNewPairSet, Finset.mem_sdiff]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hold
  rw [oldPairSet, Finset.mem_image] at hold
  rcases hold with ⟨p, -, hp⟩
  exact L.leafVertexPair_fresh x p hp.symm

private theorem ofDistinct_left_right_eq {n : ℕ} (p : VertexPair n) :
    VertexPair.ofDistinct p.left p.right (ne_of_lt p.left_lt_right) = p := by
  rw [VertexPair.ofDistinct_eq_of_lt
    (ne_of_lt p.left_lt_right) p.left_lt_right]
  apply VertexPair.ext <;> rfl

private theorem oldPair_of_both_old
    (L : LiteralOneLeafAttachment T U) (q : VertexPair (m + 1))
    (x y : Fin m) (hx : L.oldEmbedding x = q.left)
    (hy : L.oldEmbedding y = q.right) :
    q ∈ L.oldPairSet := by
  have hxy : x ≠ y := by
    intro h
    subst y
    exact (ne_of_lt q.left_lt_right) (hx.symm.trans hy)
  let p : VertexPair m := VertexPair.ofDistinct x y hxy
  have hpends :
      (p.left = x ∧ p.right = y) ∨
      (p.left = y ∧ p.right = x) := by
    unfold p VertexPair.ofDistinct
    split_ifs with hlt
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  have hmap : mapVertexPair L.oldEmbedding.toEmbedding p = q := by
    rw [mapVertexPair, ← ofDistinct_left_right_eq q,
      LeechTrees.QHop.VertexPair.ofDistinct_eq_iff]
    rcases hpends with hp | hp
    · exact Or.inl ⟨by simpa [hp.1] using hx,
        by simpa [hp.2] using hy⟩
    · exact Or.inr ⟨by simpa [hp.1] using hy,
        by simpa [hp.2] using hx⟩
  rw [oldPairSet, Finset.mem_image]
  exact ⟨p, Finset.mem_univ _, hmap⟩

/-- Exhaustiveness of the vertex partition promotes the displayed leaf pairs
to an exhaustive classification of every genuinely new indexed pair. -/
theorem exists_leafVertexPair_of_mem_actualNewPairSet
    (L : LiteralOneLeafAttachment T U) (q : VertexPair (m + 1))
    (hq : q ∈ L.actualNewPairSet) :
    ∃ x : Fin m, q = L.leafVertexPair x := by
  rw [actualNewPairSet] at hq
  have hnotOld : q ∉ L.oldPairSet := (Finset.mem_sdiff.mp hq).2
  rcases L.vertex_cover q.left with hleft | ⟨x, hx⟩
  · rcases L.vertex_cover q.right with hright | ⟨y, hy⟩
    · exact ((ne_of_lt q.left_lt_right) (hleft.trans hright.symm)).elim
    · refine ⟨y, ?_⟩
      calc
        q = VertexPair.ofDistinct q.left q.right
            (ne_of_lt q.left_lt_right) := (ofDistinct_left_right_eq q).symm
        _ = L.leafVertexPair y := by
          unfold leafVertexPair
          apply (LeechTrees.QHop.VertexPair.ofDistinct_eq_iff
            (ne_of_lt q.left_lt_right) (L.leaf_not_old y)).mpr
          exact Or.inl ⟨hleft, hy.symm⟩
  · rcases L.vertex_cover q.right with hright | ⟨y, hy⟩
    · refine ⟨x, ?_⟩
      calc
        q = VertexPair.ofDistinct q.left q.right
            (ne_of_lt q.left_lt_right) := (ofDistinct_left_right_eq q).symm
        _ = L.leafVertexPair x := by
          unfold leafVertexPair
          apply (LeechTrees.QHop.VertexPair.ofDistinct_eq_iff
            (ne_of_lt q.left_lt_right) (L.leaf_not_old x)).mpr
          exact Or.inr ⟨hx.symm, hright⟩
    · exact (hnotOld (L.oldPair_of_both_old q x y hx hy)).elim

theorem actualNewPairSet_eq (L : LiteralOneLeafAttachment T U) :
    L.actualNewPairSet = Finset.univ.image L.leafVertexPair := by
  ext q
  constructor
  · intro hq
    obtain ⟨x, rfl⟩ := L.exists_leafVertexPair_of_mem_actualNewPairSet q hq
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  · intro hq
    rcases Finset.mem_image.mp hq with ⟨x, -, rfl⟩
    exact L.leafVertexPair_mem_actualNewPairSet x

theorem actualNewPairSet_card (L : LiteralOneLeafAttachment T U) :
    L.actualNewPairSet.card = m := by
  rw [L.actualNewPairSet_eq,
    Finset.card_image_of_injective _ L.leafVertexPair_injective]
  simp

/-- The support of all actual new-pair distances in `U`, defined from the
complement of the old indexed-pair image rather than from a preselected list
of leaf pairs. -/
noncomputable def actualNewPairDistanceSet
    (L : LiteralOneLeafAttachment T U) : Finset ℕ :=
  L.actualNewPairSet.image U.pairDist

/-- The actual new-pair distance support is exactly the frozen
`newLeafDistanceSet` expression.  This is unconditional: Leech hypotheses
enter only when proving that this set is the next target tail. -/
theorem actualNewPairDistanceSet_eq_newLeafDistanceSet
    (L : LiteralOneLeafAttachment T U) :
    L.actualNewPairDistanceSet =
      newLeafDistanceSet T L.port L.leafWeight := by
  ext d
  constructor
  · intro hd
    rw [actualNewPairDistanceSet, Finset.mem_image] at hd
    rcases hd with ⟨q, hq, rfl⟩
    rw [L.actualNewPairSet_eq] at hq
    rcases Finset.mem_image.mp hq with ⟨x, -, rfl⟩
    rw [newLeafDistanceSet, Finset.mem_image]
    exact ⟨x, Finset.mem_univ _, (L.pairDist_leafVertexPair x).symm⟩
  · intro hd
    rw [newLeafDistanceSet, Finset.mem_image] at hd
    rcases hd with ⟨x, -, hx⟩
    rw [actualNewPairDistanceSet, Finset.mem_image]
    refine ⟨L.leafVertexPair x,
      L.leafVertexPair_mem_actualNewPairSet x, ?_⟩
    rw [L.pairDist_leafVertexPair x]
    exact hx

theorem actualNewPair_gt_target
    (L : LiteralOneLeafAttachment T U) (hT : IsLeech T) (hU : IsLeech U)
    (q : VertexPair (m + 1)) (hq : q ∈ L.actualNewPairSet) :
    targetN m < U.pairDist q := by
  apply L.toRetainsOldMetric.fresh_pair_gt_target hT hU q
  intro p hp
  have hold : q ∈ L.oldPairSet := by
    rw [oldPairSet, Finset.mem_image]
    exact ⟨p, Finset.mem_univ _, hp.symm⟩
  rw [actualNewPairSet] at hq
  exact (Finset.mem_sdiff.mp hq).2 hold

theorem targetN_succ (m : ℕ) :
    targetN (m + 1) = targetN m + m := by
  unfold targetN
  rw [Nat.choose_succ_succ']
  simp [Nat.add_comm]

/-- In a Leech output the actual new pairs occupy exactly the ranks beyond
the retained old target interval. -/
theorem actualNewPairDistanceSet_eq_tail
    (L : LiteralOneLeafAttachment T U) (hT : IsLeech T) (hU : IsLeech U) :
    L.actualNewPairDistanceSet =
      Finset.Icc (targetN m + 1) (targetN m + m) := by
  ext d
  constructor
  · intro hd
    rw [actualNewPairDistanceSet, Finset.mem_image] at hd
    rcases hd with ⟨q, hq, rfl⟩
    rw [Finset.mem_Icc]
    have hlower := L.actualNewPair_gt_target hT hU q hq
    have hupper := hU.pairDist_le_target q
    rw [targetN_succ] at hupper
    omega
  · intro hd
    rw [Finset.mem_Icc] at hd
    have hdTarget : d ∈ Finset.Icc 1 (targetN (m + 1)) := by
      rw [Finset.mem_Icc, targetN_succ]
      omega
    obtain ⟨q, hqd, -⟩ := hU.target_existsUnique d hdTarget
    have hqnew : q ∈ L.actualNewPairSet := by
      rw [actualNewPairSet, Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hqold
      rw [oldPairSet, Finset.mem_image] at hqold
      rcases hqold with ⟨p, -, hp⟩
      have holdUpper := hT.pairDist_le_target p
      have hretained :
          U.pairDist (mapVertexPair L.oldEmbedding.toEmbedding p) =
            T.pairDist p := by
        rw [mapVertexPair, U.pairDist_pairOfDistinct]
        simpa [PosIntTree.pairDist] using L.dist_old_eq p.left p.right
      have hqUpper : U.pairDist q ≤ targetN m := by
        rw [← hp, hretained]
        exact holdUpper
      omega
    rw [actualNewPairDistanceSet, Finset.mem_image]
    exact ⟨q, hqnew, hqd⟩

/-- Literal unchanged one-leaf attachment between Leech trees forces the
frozen one-leaf tail certificate. -/
theorem completesOneLeafTail
    (L : LiteralOneLeafAttachment T U) (hT : IsLeech T) (hU : IsLeech U) :
    CompletesOneLeafTail T L.port L.leafWeight := by
  unfold CompletesOneLeafTail
  rw [← L.actualNewPairDistanceSet_eq_newLeafDistanceSet]
  exact L.actualNewPairDistanceSet_eq_tail hT hU

/-- No literal unchanged one-leaf extension of a Leech tree of order at
least four can itself be a Leech tree. -/
theorem no_literalOneLeafAttachment_of_four_le
    (hT : IsLeech T) (hU : IsLeech U) (hm : 4 ≤ m)
    (L : LiteralOneLeafAttachment T U) : False :=
  LeafRange.no_completesOneLeafTail_of_four_le
    hT hm L.port L.leafWeight (L.completesOneLeafTail hT hU)

end LiteralOneLeafAttachment

end LeechTrees.OperationAdapters
