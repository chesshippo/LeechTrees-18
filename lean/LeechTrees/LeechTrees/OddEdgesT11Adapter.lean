import LeechTrees.Foundations
import LeechTrees.OddEdges
import LeechTrees.OddEdgesGraphAdapter

/-!
# Concrete T11 graph-to-decomposition adapter

This module constructs the one-odd decomposition from the frozen concrete
weighted-tree model.  It does not alter the three frozen input modules and
does not address T12.
-/

open scoped BigOperators

namespace LeechTrees.OddEdges.T11Adapter

open LeechTrees.Foundation
open LeechTrees.OddEdges.GraphAdapter

namespace PosIntTree

variable {n : ℕ} (T : PosIntTree n)

private theorem exists_first_common
    {u v r : Fin n} (p : T.graph.Walk u r) (q : T.graph.Walk v r) :
    ∃ z, ∃ hp : z ∈ p.support, ∃ _hq : z ∈ q.support,
      ∀ x, x ∈ (p.takeUntil z hp).support → x ∈ q.support → x = z := by
  induction p with
  | @nil r0 =>
      refine ⟨r0, by simp, q.end_mem_support, ?_⟩
      intro x hx _
      simpa using hx
  | @cons u w r h p ih =>
      by_cases hu : u ∈ q.support
      · refine ⟨u, by simp, hu, ?_⟩
        intro x hx _
        simpa using hx
      · obtain ⟨z, hzp, hzq, hfirst⟩ := ih q
        have hzu : u ≠ z := by
          intro huz
          apply hu
          simpa [huz] using hzq
        have hzcons : z ∈ (p.cons h).support := by simp [hzp]
        refine ⟨z, hzcons, hzq, ?_⟩
        intro x hx hxq
        rw [p.takeUntil_cons hzp hzu h] at hx
        rcases (by simpa using hx : x = u ∨ x ∈ (p.takeUntil z hzp).support) with
          rfl | hxtail
        · exact (hu hxq).elim
        · exact hfirst x hxtail hxq

theorem walkWeight_reverse {u v : Fin n} (p : T.graph.Walk u v) :
    T.walkWeight p.reverse = T.walkWeight p := by
  unfold LeechTrees.Foundation.PosIntTree.walkWeight
  simp

theorem walkWeight_append {u v w : Fin n}
    (p : T.graph.Walk u v) (q : T.graph.Walk v w) :
    T.walkWeight (p.append q) = T.walkWeight p + T.walkWeight q := by
  unfold LeechTrees.Foundation.PosIntTree.walkWeight
  simp [List.sum_append]

theorem dist_split_at_path_vertex {u v z : Fin n}
    (hz : z ∈ (T.path u v).1.support) :
    T.dist u v = T.dist u z + T.dist z v := by
  let a := (T.path u v).1.takeUntil z hz
  let b := (T.path u v).1.dropUntil z hz
  have ha : a.IsPath := (T.path u v).2.takeUntil hz
  have hb : b.IsPath := (T.path u v).2.dropUntil hz
  have hsplit : a.append b = (T.path u v).1 :=
    (T.path u v).1.take_spec hz
  calc
    T.dist u v = T.walkWeight (T.path u v).1 :=
      T.dist_eq_walkWeight_path u v
    _ = T.walkWeight (a.append b) := by rw [hsplit]
    _ = T.walkWeight a + T.walkWeight b := walkWeight_append T a b
    _ = T.dist u z + T.dist z v := by
      rw [T.path_walkWeight_eq_dist ⟨a, ha⟩,
        T.path_walkWeight_eq_dist ⟨b, hb⟩]

/-- Rooted-tree gate/LCA realization.  The witness is a genuine named vertex
lying on both root paths, and the identity uses the actual weighted metric. -/
theorem exists_root_gate (r u v : Fin n) :
    ∃ z : Fin n,
      z ∈ (T.path u r).1.support ∧
      z ∈ (T.path v r).1.support ∧
      T.dist u v + 2 * T.dist z r = T.dist u r + T.dist v r ∧
      T.dist z r ≤ T.dist u r ∧ T.dist z r ≤ T.dist v r := by
  classical
  let pu := T.path u r
  let pv := T.path v r
  obtain ⟨z, hzu, hzv, hfirst⟩ :=
    exists_first_common T pu.1 pv.1
  let a := pu.1.takeUntil z hzu
  let b := pv.1.takeUntil z hzv
  have ha : a.IsPath := pu.2.takeUntil hzu
  have hb : b.IsPath := pv.2.takeUntil hzv
  have hdisjoint : a.support.Disjoint b.reverse.support.tail := by
    rw [List.disjoint_left]
    intro x hxa hxb
    have hxbq : x ∈ pv.1.support := by
      apply pv.1.support_takeUntil_subset hzv
      have : x ∈ b.reverse.support := List.mem_of_mem_tail hxb
      simpa [b] using this
    have hxz : x = z := hfirst x (by simpa [a] using hxa) hxbq
    subst x
    have hnodup : b.reverse.support.Nodup := hb.reverse.support_nodup
    rw [b.reverse.support_eq_cons] at hnodup hxb
    exact (List.nodup_cons.mp hnodup).1 hxb
  let route := a.append b.reverse
  have hroute : route.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append,
      List.nodup_append]
    refine ⟨ha.support_nodup, hb.reverse.support_nodup.tail, ?_⟩
    intro x hx y hy hxy
    subst y
    exact (List.disjoint_left.mp hdisjoint hx) hy
  have huv : T.dist u v = T.dist u z + T.dist v z := by
    have hw : T.walkWeight route = T.dist u v :=
      T.path_walkWeight_eq_dist ⟨route, hroute⟩
    rw [walkWeight_append T, walkWeight_reverse T,
      T.path_walkWeight_eq_dist ⟨a, ha⟩,
      T.path_walkWeight_eq_dist ⟨b, hb⟩] at hw
    exact hw.symm
  have hur : T.dist u r = T.dist u z + T.dist z r :=
    dist_split_at_path_vertex T hzu
  have hvr : T.dist v r = T.dist v z + T.dist z r :=
    dist_split_at_path_vertex T hzv
  refine ⟨z, hzu, hzv, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega

end PosIntTree

/-! ## Half-depth coordinates on the unique odd cut -/

variable {n : ℕ} (T : PosIntTree n)

noncomputable def leftHalfDepth
    (hOne : ExactlyOneOddPhysicalEdge T)
    (u : T.LeftVertex (uniqueOddEdge T hOne)) : ℕ :=
  T.leftDepth (uniqueOddEdge T hOne) u / 2

noncomputable def rightHalfDepth
    (hOne : ExactlyOneOddPhysicalEdge T)
    (v : T.RightVertex (uniqueOddEdge T hOne)) : ℕ :=
  T.rightDepth (uniqueOddEdge T hOne) v / 2

theorem leftDepth_even (hOne : ExactlyOneOddPhysicalEdge T)
    (u : T.LeftVertex (uniqueOddEdge T hOne)) :
    Even (T.leftDepth (uniqueOddEdge T hOne) u) := by
  rw [← Nat.not_odd_iff_even]
  intro hodd
  have hmem := (dist_odd_iff_unique_mem T hOne u.1
    (T.edgeLeft (uniqueOddEdge T hOne))).1 hodd
  exact ((T.cut_reachable_iff_not_mem_pathEdges
    (uniqueOddEdge T hOne) u.1 (T.edgeLeft (uniqueOddEdge T hOne))).1 u.2) hmem

theorem rightDepth_even (hOne : ExactlyOneOddPhysicalEdge T)
    (v : T.RightVertex (uniqueOddEdge T hOne)) :
    Even (T.rightDepth (uniqueOddEdge T hOne) v) := by
  rw [← Nat.not_odd_iff_even]
  intro hodd
  have hmem := (dist_odd_iff_unique_mem T hOne
    (T.edgeRight (uniqueOddEdge T hOne)) v.1).1 hodd
  rw [T.pathEdges_comm] at hmem
  exact ((T.cut_reachable_iff_not_mem_pathEdges
    (uniqueOddEdge T hOne) v.1 (T.edgeRight (uniqueOddEdge T hOne))).1 v.2) hmem

theorem two_mul_leftHalfDepth (hOne : ExactlyOneOddPhysicalEdge T)
    (u : T.LeftVertex (uniqueOddEdge T hOne)) :
    2 * leftHalfDepth T hOne u = T.leftDepth (uniqueOddEdge T hOne) u :=
  Nat.two_mul_div_two_of_even (leftDepth_even T hOne u)

theorem two_mul_rightHalfDepth (hOne : ExactlyOneOddPhysicalEdge T)
    (v : T.RightVertex (uniqueOddEdge T hOne)) :
    2 * rightHalfDepth T hOne v = T.rightDepth (uniqueOddEdge T hOne) v :=
  Nat.two_mul_div_two_of_even (rightDepth_even T hOne v)

theorem leftHalfDepth_injective (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T) :
    Function.Injective (leftHalfDepth T hOne) := by
  intro u v h
  apply T.leftDepth_injective hL (uniqueOddEdge T hOne)
  have hu := two_mul_leftHalfDepth T hOne u
  have hv := two_mul_leftHalfDepth T hOne v
  omega

theorem rightHalfDepth_injective (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T) :
    Function.Injective (rightHalfDepth T hOne) := by
  intro u v h
  apply T.rightDepth_injective hL (uniqueOddEdge T hOne)
  have hu := two_mul_rightHalfDepth T hOne u
  have hv := two_mul_rightHalfDepth T hOne v
  omega

noncomputable def leftDepthSet (hOne : ExactlyOneOddPhysicalEdge T) : Finset ℕ :=
  Finset.univ.image (leftHalfDepth T hOne)

noncomputable def rightDepthSet (hOne : ExactlyOneOddPhysicalEdge T) : Finset ℕ :=
  Finset.univ.image (rightHalfDepth T hOne)

noncomputable def leftDepthEquiv (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T) :
    T.LeftVertex (uniqueOddEdge T hOne) ≃ ↥(leftDepthSet T hOne) := by
  classical
  let f : T.LeftVertex (uniqueOddEdge T hOne) → ↥(leftDepthSet T hOne) :=
    fun u => ⟨leftHalfDepth T hOne u, by simp [leftDepthSet]⟩
  apply Equiv.ofBijective f
  constructor
  · intro u v h
    apply leftHalfDepth_injective T hL hOne
    exact congrArg Subtype.val h
  · intro x
    rcases Finset.mem_image.mp x.2 with ⟨u, _, hu⟩
    refine ⟨u, Subtype.ext ?_⟩
    exact hu

noncomputable def rightDepthEquiv (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T) :
    T.RightVertex (uniqueOddEdge T hOne) ≃ ↥(rightDepthSet T hOne) := by
  classical
  let f : T.RightVertex (uniqueOddEdge T hOne) → ↥(rightDepthSet T hOne) :=
    fun v => ⟨rightHalfDepth T hOne v, by simp [rightDepthSet]⟩
  apply Equiv.ofBijective f
  constructor
  · intro u v h
    apply rightHalfDepth_injective T hL hOne
    exact congrArg Subtype.val h
  · intro x
    rcases Finset.mem_image.mp x.2 with ⟨v, _, hv⟩
    refine ⟨v, Subtype.ext ?_⟩
    exact hv

theorem leftDepthSet_card (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T) :
    (leftDepthSet T hOne).card = T.cutSize (uniqueOddEdge T hOne) := by
  rw [← Fintype.card_coe, ← Fintype.card_congr (leftDepthEquiv T hL hOne)]
  rfl

theorem rightDepthSet_card (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T) :
    (rightDepthSet T hOne).card = n - T.cutSize (uniqueOddEdge T hOne) := by
  rw [← Fintype.card_coe, ← Fintype.card_congr (rightDepthEquiv T hL hOne)]
  exact T.rightVertex_card (uniqueOddEdge T hOne)

theorem zero_mem_leftDepthSet (hOne : ExactlyOneOddPhysicalEdge T) :
    0 ∈ leftDepthSet T hOne := by
  classical
  let u : T.LeftVertex (uniqueOddEdge T hOne) :=
    ⟨T.edgeLeft (uniqueOddEdge T hOne),
      T.edgeLeft_mem_LeftCut (uniqueOddEdge T hOne)⟩
  rw [leftDepthSet, Finset.mem_image]
  refine ⟨u, Finset.mem_univ _, ?_⟩
  simp [leftHalfDepth, u, LeechTrees.Foundation.PosIntTree.leftDepth]

theorem zero_mem_rightDepthSet (hOne : ExactlyOneOddPhysicalEdge T) :
    0 ∈ rightDepthSet T hOne := by
  classical
  let v : T.RightVertex (uniqueOddEdge T hOne) :=
    ⟨T.edgeRight (uniqueOddEdge T hOne),
      T.edgeRight_mem_RightCut (uniqueOddEdge T hOne)⟩
  rw [rightDepthSet, Finset.mem_image]
  refine ⟨v, Finset.mem_univ _, ?_⟩
  simp [rightHalfDepth, v, LeechTrees.Foundation.PosIntTree.rightDepth]

noncomputable def crossHalfIndex
    (hOne : ExactlyOneOddPhysicalEdge T)
    (x : T.LeftVertex (uniqueOddEdge T hOne) ×
      T.RightVertex (uniqueOddEdge T hOne)) : ℕ :=
  leftHalfDepth T hOne x.1 + rightHalfDepth T hOne x.2

theorem crossHalfIndex_lt (hL : IsLeech T) (hn : 2 ≤ n)
    (hOne : ExactlyOneOddPhysicalEdge T)
    (x : T.LeftVertex (uniqueOddEdge T hOne) ×
      T.RightVertex (uniqueOddEdge T hOne)) :
    crossHalfIndex T hOne x < oddTargetCount n := by
  have hmem := T.rootedCrossSum_mem_target_tail hL
    (uniqueOddEdge T hOne) x
  rw [Finset.mem_Icc] at hmem
  have hw := uniqueOddEdge_weight_one T hL hn hOne
  have hl := two_mul_leftHalfDepth T hOne x.1
  have hr := two_mul_rightHalfDepth T hOne x.2
  have hc := oddTargetCount_eq (n := n)
  unfold crossHalfIndex
  unfold LeechTrees.Foundation.PosIntTree.rootedCrossSum at hmem
  omega

theorem crossHalfIndex_injective (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T) :
    Function.Injective (crossHalfIndex T hOne) := by
  intro x y h
  apply T.rootedCrossSum_injective hL (uniqueOddEdge T hOne)
  have hxl := two_mul_leftHalfDepth T hOne x.1
  have hxr := two_mul_rightHalfDepth T hOne x.2
  have hyl := two_mul_leftHalfDepth T hOne y.1
  have hyr := two_mul_rightHalfDepth T hOne y.2
  unfold crossHalfIndex at h
  unfold LeechTrees.Foundation.PosIntTree.rootedCrossSum
  omega

noncomputable def crossHalfEquiv (hL : IsLeech T) (hn : 2 ≤ n)
    (hOne : ExactlyOneOddPhysicalEdge T) :
    (T.LeftVertex (uniqueOddEdge T hOne) ×
      T.RightVertex (uniqueOddEdge T hOne)) ≃ Fin (oddTargetCount n) := by
  let f : T.LeftVertex (uniqueOddEdge T hOne) ×
      T.RightVertex (uniqueOddEdge T hOne) → Fin (oddTargetCount n) :=
    fun x => ⟨crossHalfIndex T hOne x, crossHalfIndex_lt T hL hn hOne x⟩
  apply Equiv.ofBijective f
  apply (Fintype.bijective_iff_injective_and_card f).2
  constructor
  · intro x y h
    apply crossHalfIndex_injective T hL hOne
    exact congrArg Fin.val h
  · calc
      Fintype.card
          (T.LeftVertex (uniqueOddEdge T hOne) ×
            T.RightVertex (uniqueOddEdge T hOne)) =
          Fintype.card (T.CrossingPair (uniqueOddEdge T hOne)) :=
        Fintype.card_congr (T.crossingPairEquiv (uniqueOddEdge T hOne))
      _ = oddTargetCount n := uniqueOdd_crossingPair_card T hL hOne
      _ = Fintype.card (Fin (oddTargetCount n)) := by simp

noncomputable def crossRanks (hL : IsLeech T) (hn : 2 ≤ n)
    (hOne : ExactlyOneOddPhysicalEdge T) :
    IntervalDirectSum (leftDepthSet T hOne) (rightDepthSet T hOne)
      (oddTargetCount n) where
  equiv := (Equiv.prodCongr (leftDepthEquiv T hL hOne).symm
    (rightDepthEquiv T hL hOne).symm).trans (crossHalfEquiv T hL hn hOne)
  sum_eq := by
    intro p
    let u := (leftDepthEquiv T hL hOne).symm p.1
    let v := (rightDepthEquiv T hL hOne).symm p.2
    have hu : leftHalfDepth T hOne u = p.1.1 := by
      have h := (leftDepthEquiv T hL hOne).apply_symm_apply p.1
      exact congrArg Subtype.val h
    have hv : rightHalfDepth T hOne v = p.2.1 := by
      have h := (rightDepthEquiv T hL hOne).apply_symm_apply p.2
      exact congrArg Subtype.val h
    change crossHalfIndex T hOne (u, v) = p.1.1 + p.2.1
    simp only [crossHalfIndex, hu, hv]

/-! ## Same-side indexed pairs and genuine gate realization -/

private theorem depthEdge_inf_ne_sup {X : Finset ℕ} (d : DepthEdge X) :
    d.1.inf ≠ d.1.sup := by
  intro h
  apply (⊤ : SimpleGraph ↥X).not_isDiag_of_mem_edgeSet d.2
  rw [(Sym2.sortEquiv.symm_apply_apply d.1).symm]
  exact Sym2.mk_isDiag_iff.mpr h

private theorem ofDistinct_sym2 {u v : Fin n} (huv : u ≠ v) :
    s((VertexPair.ofDistinct u v huv).left,
      (VertexPair.ofDistinct u v huv).right) = s(u, v) := by
  by_cases h : u < v
  · simp [VertexPair.ofDistinct, h, VertexPair.left, VertexPair.right]
  · simp [VertexPair.ofDistinct, h, VertexPair.left, VertexPair.right,
      Sym2.eq_swap]

noncomputable def internalPairOfDepthEdge {X : Finset ℕ}
    (vertex : ↥X ↪ Fin n) (d : DepthEdge X) : VertexPair n :=
  VertexPair.ofDistinct (vertex d.1.inf) (vertex d.1.sup)
    (vertex.injective.ne (depthEdge_inf_ne_sup d))

theorem internalPairOfDepthEdge_sym2 {X : Finset ℕ}
    (vertex : ↥X ↪ Fin n) (d : DepthEdge X) :
    s((internalPairOfDepthEdge vertex d).left,
      (internalPairOfDepthEdge vertex d).right) = Sym2.map vertex d.1 := by
  unfold internalPairOfDepthEdge
  calc
    s((VertexPair.ofDistinct (vertex d.1.inf) (vertex d.1.sup) _).left,
        (VertexPair.ofDistinct (vertex d.1.inf) (vertex d.1.sup) _).right) =
        s(vertex d.1.inf, vertex d.1.sup) := ofDistinct_sym2 _
    _ = Sym2.map vertex (s(d.1.inf, d.1.sup)) := rfl
    _ = Sym2.map vertex d.1 := by
      have hsort : s(d.1.inf, d.1.sup) = d.1 := by
        exact Sym2.sortEquiv.symm_apply_apply d.1
      rw [hsort]

theorem internalPairOfDepthEdge_injective {X : Finset ℕ}
    (vertex : ↥X ↪ Fin n) :
    Function.Injective (internalPairOfDepthEdge vertex) := by
  intro d f h
  have hsym := congrArg
    (fun p : VertexPair n => s(p.left, p.right)) h
  change
    s((internalPairOfDepthEdge vertex d).left,
        (internalPairOfDepthEdge vertex d).right) =
      s((internalPairOfDepthEdge vertex f).left,
        (internalPairOfDepthEdge vertex f).right) at hsym
  rw [internalPairOfDepthEdge_sym2, internalPairOfDepthEdge_sym2] at hsym
  have hval : d.1 = f.1 := (Sym2.map.injective vertex.injective) hsym
  exact Subtype.ext hval

theorem pairDist_internalPairOfDepthEdge {X : Finset ℕ}
    (vertex : ↥X ↪ Fin n) (d : DepthEdge X) :
    T.pairDist (internalPairOfDepthEdge vertex d) =
      T.dist (vertex d.1.inf) (vertex d.1.sup) := by
  unfold internalPairOfDepthEdge
  exact T.pairDist_pairOfDistinct _ _ _

noncomputable def leftVertexEmbedding (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T) :
    ↥(leftDepthSet T hOne) ↪ Fin n where
  toFun x := ((leftDepthEquiv T hL hOne).symm x).1
  inj' := by
    intro x y h
    apply (leftDepthEquiv T hL hOne).symm.injective
    exact Subtype.ext h

noncomputable def rightVertexEmbedding (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T) :
    ↥(rightDepthSet T hOne) ↪ Fin n where
  toFun x := ((rightDepthEquiv T hL hOne).symm x).1
  inj' := by
    intro x y h
    apply (rightDepthEquiv T hL hOne).symm.injective
    exact Subtype.ext h

noncomputable def leftInternalPair (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T) :
    DepthEdge (leftDepthSet T hOne) → VertexPair n :=
  internalPairOfDepthEdge (leftVertexEmbedding T hL hOne)

noncomputable def rightInternalPair (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T) :
    DepthEdge (rightDepthSet T hOne) → VertexPair n :=
  internalPairOfDepthEdge (rightVertexEmbedding T hL hOne)

theorem leftInternalPair_injective (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T) :
    Function.Injective (leftInternalPair T hL hOne) :=
  internalPairOfDepthEdge_injective _

theorem rightInternalPair_injective (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T) :
    Function.Injective (rightInternalPair T hL hOne) :=
  internalPairOfDepthEdge_injective _

theorem pathEdges_suffix_subset {u r z : Fin n}
    (hz : z ∈ (T.path u r).1.support) :
    T.pathEdges z r ⊆ T.pathEdges u r := by
  classical
  let b := (T.path u r).1.dropUntil z hz
  have hb : b.IsPath := (T.path u r).2.dropUntil hz
  have hbeq : (⟨b, hb⟩ : T.graph.Path z r) = T.path z r := T.path_unique _
  intro f hf
  have hflist : f ∈ (T.path z r).1.edges := by
    simpa [LeechTrees.Foundation.PosIntTree.pathEdges] using hf
  rw [← hbeq] at hflist
  have hfull : f ∈ (T.path u r).1.edges :=
    (T.path u r).1.edges_dropUntil_subset hz hflist
  simpa [LeechTrees.Foundation.PosIntTree.pathEdges] using hfull

theorem leftCut_of_mem_path_to_left
    (hOne : ExactlyOneOddPhysicalEdge T)
    (u : T.LeftVertex (uniqueOddEdge T hOne)) {z : Fin n}
    (hz : z ∈ (T.path u.1 (T.edgeLeft (uniqueOddEdge T hOne))).1.support) :
    T.LeftCut (uniqueOddEdge T hOne) z := by
  unfold PosIntTree.LeftCut
  rw [T.cut_reachable_iff_not_mem_pathEdges]
  intro hmem
  have hsub := pathEdges_suffix_subset T hz hmem
  exact ((T.cut_reachable_iff_not_mem_pathEdges
    (uniqueOddEdge T hOne) u.1 (T.edgeLeft (uniqueOddEdge T hOne))).1 u.2) hsub

theorem rightCut_of_mem_path_to_right
    (hOne : ExactlyOneOddPhysicalEdge T)
    (v : T.RightVertex (uniqueOddEdge T hOne)) {z : Fin n}
    (hz : z ∈ (T.path v.1 (T.edgeRight (uniqueOddEdge T hOne))).1.support) :
    T.RightCut (uniqueOddEdge T hOne) z := by
  unfold PosIntTree.RightCut
  rw [T.cut_reachable_iff_not_mem_pathEdges]
  intro hmem
  have hsub := pathEdges_suffix_subset T hz hmem
  exact ((T.cut_reachable_iff_not_mem_pathEdges
    (uniqueOddEdge T hOne) v.1 (T.edgeRight (uniqueOddEdge T hOne))).1 v.2) hsub

theorem left_sameSide_dist_even (hOne : ExactlyOneOddPhysicalEdge T)
    (u v : T.LeftVertex (uniqueOddEdge T hOne)) : Even (T.dist u.1 v.1) := by
  rw [← Nat.not_odd_iff_even]
  intro hodd
  have hmem := (dist_odd_iff_unique_mem T hOne u.1 v.1).1 hodd
  rcases (T.mem_pathEdges_iff_opposite_cuts
    (uniqueOddEdge T hOne) u.1 v.1).1 hmem with h | h
  · exact T.LeftCut_disjoint_RightCut (uniqueOddEdge T hOne) v.1 ⟨v.2, h.2⟩
  · exact T.LeftCut_disjoint_RightCut (uniqueOddEdge T hOne) u.1 ⟨u.2, h.1⟩

theorem right_sameSide_dist_even (hOne : ExactlyOneOddPhysicalEdge T)
    (u v : T.RightVertex (uniqueOddEdge T hOne)) : Even (T.dist u.1 v.1) := by
  rw [← Nat.not_odd_iff_even]
  intro hodd
  have hmem := (dist_odd_iff_unique_mem T hOne u.1 v.1).1 hodd
  rcases (T.mem_pathEdges_iff_opposite_cuts
    (uniqueOddEdge T hOne) u.1 v.1).1 hmem with h | h
  · exact T.LeftCut_disjoint_RightCut (uniqueOddEdge T hOne) u.1 ⟨h.1, u.2⟩
  · exact T.LeftCut_disjoint_RightCut (uniqueOddEdge T hOne) v.1 ⟨h.2, v.2⟩

theorem exists_left_half_gate (hOne : ExactlyOneOddPhysicalEdge T)
    (u v : T.LeftVertex (uniqueOddEdge T hOne)) :
    ∃ z : T.LeftVertex (uniqueOddEdge T hOne),
      leftHalfDepth T hOne z ≤ leftHalfDepth T hOne u ∧
      leftHalfDepth T hOne z ≤ leftHalfDepth T hOne v ∧
      T.dist u.1 v.1 / 2 + 2 * leftHalfDepth T hOne z =
        leftHalfDepth T hOne u + leftHalfDepth T hOne v := by
  obtain ⟨z, hzu, hzv, hid, hleu, hlev⟩ :=
    PosIntTree.exists_root_gate T (T.edgeLeft (uniqueOddEdge T hOne)) u.1 v.1
  let zs : T.LeftVertex (uniqueOddEdge T hOne) :=
    ⟨z, leftCut_of_mem_path_to_left T hOne u hzu⟩
  have heven := left_sameSide_dist_even T hOne u v
  have hd : 2 * (T.dist u.1 v.1 / 2) = T.dist u.1 v.1 :=
    Nat.two_mul_div_two_of_even heven
  have hu := two_mul_leftHalfDepth T hOne u
  have hv := two_mul_leftHalfDepth T hOne v
  have hz := two_mul_leftHalfDepth T hOne zs
  refine ⟨zs, ?_, ?_, ?_⟩
  · exact Nat.div_le_div_right hleu
  · exact Nat.div_le_div_right hlev
  · change T.dist u.1 v.1 / 2 +
        2 * (T.dist z (T.edgeLeft (uniqueOddEdge T hOne)) / 2) =
      T.dist u.1 (T.edgeLeft (uniqueOddEdge T hOne)) / 2 +
        T.dist v.1 (T.edgeLeft (uniqueOddEdge T hOne)) / 2
    unfold leftHalfDepth PosIntTree.leftDepth at hu hv
    have hz' : 2 * (T.dist z (T.edgeLeft (uniqueOddEdge T hOne)) / 2) =
        T.dist z (T.edgeLeft (uniqueOddEdge T hOne)) := by
      simpa only [leftHalfDepth, PosIntTree.leftDepth] using hz
    omega

theorem exists_right_half_gate (hOne : ExactlyOneOddPhysicalEdge T)
    (u v : T.RightVertex (uniqueOddEdge T hOne)) :
    ∃ z : T.RightVertex (uniqueOddEdge T hOne),
      rightHalfDepth T hOne z ≤ rightHalfDepth T hOne u ∧
      rightHalfDepth T hOne z ≤ rightHalfDepth T hOne v ∧
      T.dist u.1 v.1 / 2 + 2 * rightHalfDepth T hOne z =
        rightHalfDepth T hOne u + rightHalfDepth T hOne v := by
  obtain ⟨z, hzu, hzv, hid, hleu, hlev⟩ :=
    PosIntTree.exists_root_gate T (T.edgeRight (uniqueOddEdge T hOne)) u.1 v.1
  let zs : T.RightVertex (uniqueOddEdge T hOne) :=
    ⟨z, rightCut_of_mem_path_to_right T hOne u hzu⟩
  have heven := right_sameSide_dist_even T hOne u v
  have hd : 2 * (T.dist u.1 v.1 / 2) = T.dist u.1 v.1 :=
    Nat.two_mul_div_two_of_even heven
  have hu := two_mul_rightHalfDepth T hOne u
  have hv := two_mul_rightHalfDepth T hOne v
  have hz := two_mul_rightHalfDepth T hOne zs
  have hid' := hid
  rw [T.dist_comm u.1 (T.edgeRight (uniqueOddEdge T hOne)),
    T.dist_comm v.1 (T.edgeRight (uniqueOddEdge T hOne)),
    T.dist_comm z (T.edgeRight (uniqueOddEdge T hOne))] at hid'
  have hleu' := hleu
  rw [T.dist_comm z (T.edgeRight (uniqueOddEdge T hOne)),
    T.dist_comm u.1 (T.edgeRight (uniqueOddEdge T hOne))] at hleu'
  have hlev' := hlev
  rw [T.dist_comm z (T.edgeRight (uniqueOddEdge T hOne)),
    T.dist_comm v.1 (T.edgeRight (uniqueOddEdge T hOne))] at hlev'
  refine ⟨zs, ?_, ?_, ?_⟩
  · exact Nat.div_le_div_right hleu'
  · exact Nat.div_le_div_right hlev'
  · change T.dist u.1 v.1 / 2 +
        2 * (T.dist (T.edgeRight (uniqueOddEdge T hOne)) z / 2) =
      T.dist (T.edgeRight (uniqueOddEdge T hOne)) u.1 / 2 +
        T.dist (T.edgeRight (uniqueOddEdge T hOne)) v.1 / 2
    unfold rightHalfDepth PosIntTree.rightDepth at hu hv
    have hz' : 2 * (T.dist (T.edgeRight (uniqueOddEdge T hOne)) z / 2) =
        T.dist (T.edgeRight (uniqueOddEdge T hOne)) z := by
      simpa only [rightHalfDepth, PosIntTree.rightDepth] using hz
    omega

/-! ## Exact indexing of the internal even ranks -/

theorem evenTargetCount_eq_half :
    evenTargetCount n = targetN n / 2 := by
  unfold evenTargetCount
  rw [oddTargetCount_eq]
  omega

noncomputable def leftInternalHalfRank (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T)
    (d : DepthEdge (leftDepthSet T hOne)) : ℕ :=
  T.pairDist (leftInternalPair T hL hOne d) / 2

noncomputable def rightInternalHalfRank (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T)
    (d : DepthEdge (rightDepthSet T hOne)) : ℕ :=
  T.pairDist (rightInternalPair T hL hOne d) / 2

theorem leftInternalPair_even (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T)
    (d : DepthEdge (leftDepthSet T hOne)) :
    Even (T.pairDist (leftInternalPair T hL hOne d)) := by
  unfold leftInternalPair
  rw [pairDist_internalPairOfDepthEdge]
  simpa only [leftVertexEmbedding] using left_sameSide_dist_even T hOne
    ((leftDepthEquiv T hL hOne).symm d.1.inf)
    ((leftDepthEquiv T hL hOne).symm d.1.sup)

theorem rightInternalPair_even (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T)
    (d : DepthEdge (rightDepthSet T hOne)) :
    Even (T.pairDist (rightInternalPair T hL hOne d)) := by
  unfold rightInternalPair
  rw [pairDist_internalPairOfDepthEdge]
  simpa only [rightVertexEmbedding] using right_sameSide_dist_even T hOne
    ((rightDepthEquiv T hL hOne).symm d.1.inf)
    ((rightDepthEquiv T hL hOne).symm d.1.sup)

theorem two_mul_leftInternalHalfRank (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T)
    (d : DepthEdge (leftDepthSet T hOne)) :
    2 * leftInternalHalfRank T hL hOne d =
      T.pairDist (leftInternalPair T hL hOne d) :=
  Nat.two_mul_div_two_of_even (leftInternalPair_even T hL hOne d)

theorem two_mul_rightInternalHalfRank (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T)
    (d : DepthEdge (rightDepthSet T hOne)) :
    2 * rightInternalHalfRank T hL hOne d =
      T.pairDist (rightInternalPair T hL hOne d) :=
  Nat.two_mul_div_two_of_even (rightInternalPair_even T hL hOne d)

theorem leftInternalHalfRank_pos (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T)
    (d : DepthEdge (leftDepthSet T hOne)) :
    0 < leftInternalHalfRank T hL hOne d := by
  have hp := hL.pairDist_pos (leftInternalPair T hL hOne d)
  have hd := two_mul_leftInternalHalfRank T hL hOne d
  omega

theorem rightInternalHalfRank_pos (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T)
    (d : DepthEdge (rightDepthSet T hOne)) :
    0 < rightInternalHalfRank T hL hOne d := by
  have hp := hL.pairDist_pos (rightInternalPair T hL hOne d)
  have hd := two_mul_rightInternalHalfRank T hL hOne d
  omega

theorem leftInternalHalfRank_le (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T)
    (d : DepthEdge (leftDepthSet T hOne)) :
    leftInternalHalfRank T hL hOne d ≤ evenTargetCount n := by
  rw [evenTargetCount_eq_half]
  rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
  calc
    leftInternalHalfRank T hL hOne d * 2 =
        T.pairDist (leftInternalPair T hL hOne d) := by
      rw [Nat.mul_comm, two_mul_leftInternalHalfRank]
    _ ≤ targetN n := hL.pairDist_le_target _

theorem rightInternalHalfRank_le (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T)
    (d : DepthEdge (rightDepthSet T hOne)) :
    rightInternalHalfRank T hL hOne d ≤ evenTargetCount n := by
  rw [evenTargetCount_eq_half]
  rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
  calc
    rightInternalHalfRank T hL hOne d * 2 =
        T.pairDist (rightInternalPair T hL hOne d) := by
      rw [Nat.mul_comm, two_mul_rightInternalHalfRank]
    _ ≤ targetN n := hL.pairDist_le_target _

noncomputable def leftInternalIndex (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T)
    (d : DepthEdge (leftDepthSet T hOne)) : Fin (evenTargetCount n) :=
  ⟨leftInternalHalfRank T hL hOne d - 1, by
    have hp := leftInternalHalfRank_pos T hL hOne d
    have hle := leftInternalHalfRank_le T hL hOne d
    omega⟩

noncomputable def rightInternalIndex (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T)
    (d : DepthEdge (rightDepthSet T hOne)) : Fin (evenTargetCount n) :=
  ⟨rightInternalHalfRank T hL hOne d - 1, by
    have hp := rightInternalHalfRank_pos T hL hOne d
    have hle := rightInternalHalfRank_le T hL hOne d
    omega⟩

@[simp] theorem leftInternalIndex_val_add_one (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T)
    (d : DepthEdge (leftDepthSet T hOne)) :
    (leftInternalIndex T hL hOne d : ℕ) + 1 =
      leftInternalHalfRank T hL hOne d := by
  unfold leftInternalIndex
  have hp := leftInternalHalfRank_pos T hL hOne d
  change leftInternalHalfRank T hL hOne d - 1 + 1 =
    leftInternalHalfRank T hL hOne d
  omega

@[simp] theorem rightInternalIndex_val_add_one (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T)
    (d : DepthEdge (rightDepthSet T hOne)) :
    (rightInternalIndex T hL hOne d : ℕ) + 1 =
      rightInternalHalfRank T hL hOne d := by
  unfold rightInternalIndex
  have hp := rightInternalHalfRank_pos T hL hOne d
  change rightInternalHalfRank T hL hOne d - 1 + 1 =
    rightInternalHalfRank T hL hOne d
  omega

theorem leftInternalIndex_injective (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T) :
    Function.Injective (leftInternalIndex T hL hOne) := by
  intro d f h
  have hv := congrArg (fun q : Fin (evenTargetCount n) => (q : ℕ) + 1) h
  change (leftInternalIndex T hL hOne d : ℕ) + 1 =
    (leftInternalIndex T hL hOne f : ℕ) + 1 at hv
  rw [leftInternalIndex_val_add_one, leftInternalIndex_val_add_one] at hv
  apply leftInternalPair_injective T hL hOne
  apply hL.pairDist_injective
  have hd := two_mul_leftInternalHalfRank T hL hOne d
  have hf := two_mul_leftInternalHalfRank T hL hOne f
  omega

theorem rightInternalIndex_injective (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T) :
    Function.Injective (rightInternalIndex T hL hOne) := by
  intro d f h
  have hv := congrArg (fun q : Fin (evenTargetCount n) => (q : ℕ) + 1) h
  change (rightInternalIndex T hL hOne d : ℕ) + 1 =
    (rightInternalIndex T hL hOne f : ℕ) + 1 at hv
  rw [rightInternalIndex_val_add_one, rightInternalIndex_val_add_one] at hv
  apply rightInternalPair_injective T hL hOne
  apply hL.pairDist_injective
  have hd := two_mul_rightInternalHalfRank T hL hOne d
  have hf := two_mul_rightInternalHalfRank T hL hOne f
  omega

private theorem internalPairOfDepthEdge_endpoints
    {X : Finset ℕ} (vertex : ↑X ↪ Fin n) (d : DepthEdge X)
    (P : Fin n → Prop)
    (hinf : P (vertex d.1.inf)) (hsup : P (vertex d.1.sup)) :
    P (internalPairOfDepthEdge vertex d).left ∧
      P (internalPairOfDepthEdge vertex d).right := by
  unfold internalPairOfDepthEdge
  by_cases h : vertex d.1.inf < vertex d.1.sup
  · simpa [VertexPair.ofDistinct, h, VertexPair.left, VertexPair.right]
      using And.intro hinf hsup
  · simpa [VertexPair.ofDistinct, h, VertexPair.left, VertexPair.right]
      using And.intro hsup hinf

theorem leftInternalPair_endpoints (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T)
    (d : DepthEdge (leftDepthSet T hOne)) :
    T.LeftCut (uniqueOddEdge T hOne) (leftInternalPair T hL hOne d).left ∧
      T.LeftCut (uniqueOddEdge T hOne) (leftInternalPair T hL hOne d).right := by
  apply internalPairOfDepthEdge_endpoints
  · exact ((leftDepthEquiv T hL hOne).symm d.1.inf).2
  · exact ((leftDepthEquiv T hL hOne).symm d.1.sup).2

theorem rightInternalPair_endpoints (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T)
    (d : DepthEdge (rightDepthSet T hOne)) :
    T.RightCut (uniqueOddEdge T hOne) (rightInternalPair T hL hOne d).left ∧
      T.RightCut (uniqueOddEdge T hOne) (rightInternalPair T hL hOne d).right := by
  apply internalPairOfDepthEdge_endpoints
  · exact ((rightDepthEquiv T hL hOne).symm d.1.inf).2
  · exact ((rightDepthEquiv T hL hOne).symm d.1.sup).2

noncomputable def internalIndex (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T) :
    DepthEdge (leftDepthSet T hOne) ⊕ DepthEdge (rightDepthSet T hOne) →
      Fin (evenTargetCount n)
  | Sum.inl d => leftInternalIndex T hL hOne d
  | Sum.inr d => rightInternalIndex T hL hOne d

theorem internalIndex_injective (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T) :
    Function.Injective (internalIndex T hL hOne) := by
  intro a b hab
  cases a with
  | inl d =>
      cases b with
      | inl f =>
          exact congrArg Sum.inl (leftInternalIndex_injective T hL hOne hab)
      | inr f =>
          exfalso
          have hv := congrArg
            (fun q : Fin (evenTargetCount n) => (q : ℕ) + 1) hab
          change (leftInternalIndex T hL hOne d : ℕ) + 1 =
            (rightInternalIndex T hL hOne f : ℕ) + 1 at hv
          rw [leftInternalIndex_val_add_one,
            rightInternalIndex_val_add_one] at hv
          have hp : leftInternalPair T hL hOne d =
              rightInternalPair T hL hOne f := by
            apply hL.pairDist_injective
            have hd := two_mul_leftInternalHalfRank T hL hOne d
            have hf := two_mul_rightInternalHalfRank T hL hOne f
            omega
          have hl := (leftInternalPair_endpoints T hL hOne d).1
          have hr := (rightInternalPair_endpoints T hL hOne f).1
          rw [hp] at hl
          exact T.LeftCut_disjoint_RightCut (uniqueOddEdge T hOne) _ ⟨hl, hr⟩
  | inr d =>
      cases b with
      | inl f =>
          exfalso
          have hv := congrArg
            (fun q : Fin (evenTargetCount n) => (q : ℕ) + 1) hab
          change (rightInternalIndex T hL hOne d : ℕ) + 1 =
            (leftInternalIndex T hL hOne f : ℕ) + 1 at hv
          rw [rightInternalIndex_val_add_one,
            leftInternalIndex_val_add_one] at hv
          have hp : rightInternalPair T hL hOne d =
              leftInternalPair T hL hOne f := by
            apply hL.pairDist_injective
            have hd := two_mul_rightInternalHalfRank T hL hOne d
            have hf := two_mul_leftInternalHalfRank T hL hOne f
            omega
          have hr := (rightInternalPair_endpoints T hL hOne d).1
          have hl := (leftInternalPair_endpoints T hL hOne f).1
          rw [hp] at hr
          exact T.LeftCut_disjoint_RightCut (uniqueOddEdge T hOne) _ ⟨hl, hr⟩
      | inr f =>
          exact congrArg Sum.inr (rightInternalIndex_injective T hL hOne hab)

theorem internalIndex_domain_card (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T) :
    Fintype.card
        (DepthEdge (leftDepthSet T hOne) ⊕ DepthEdge (rightDepthSet T hOne)) =
      evenTargetCount n := by
  let e := uniqueOddEdge T hOne
  let l := T.cutSize e
  let r := Fintype.card (T.RightVertex e)
  have hlpos : 0 < l := T.cutSize_pos e
  have hrpos : 0 < r := T.rightVertex_card_pos e
  have hr : r = n - l := T.rightVertex_card e
  have hsum : l + r = n := by omega
  have hC : l * r = oddTargetCount n := by
    rw [hr]
    rw [← T.crossingPair_card e]
    exact uniqueOdd_crossingPair_card T hL hOne
  have hsplit := oddTargetCount_add_evenTargetCount (n := n)
  have hN := two_mul_targetN n
  have hlsub : l - 1 + 1 = l := by omega
  have hrsub : r - 1 + 1 = r := by omega
  have htarget : targetN n = l * r + evenTargetCount n := by omega
  have hlrsub : l + r - 1 = (l - 1) + r := by omega
  have hNclean : 2 * (l * r + evenTargetCount n) =
      (l + r) * ((l - 1) + r) := by
    calc
      2 * (l * r + evenTargetCount n) = 2 * targetN n := by rw [htarget]
      _ = n * (n - 1) := hN
      _ = (l + r) * (l + r - 1) := by rw [hsum]
      _ = (l + r) * ((l - 1) + r) := by rw [hlrsub]
  have two_mul_choose_two (m : ℕ) :
      2 * m.choose 2 = m * (m - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self m)
  have hchoose : l.choose 2 + r.choose 2 = evenTargetCount n := by
    have hlc := two_mul_choose_two l
    have hrc := two_mul_choose_two r
    have htwice : 2 * (l.choose 2 + r.choose 2) =
        2 * evenTargetCount n := by
      nlinarith [hNclean]
    omega
  rw [hr] at hchoose
  rw [Fintype.card_sum, card_depthEdge, card_depthEdge,
    leftDepthSet_card T hL hOne, rightDepthSet_card T hL hOne]
  simpa [e, l] using hchoose

noncomputable def internalRankEquiv (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T) :
    (DepthEdge (leftDepthSet T hOne) ⊕ DepthEdge (rightDepthSet T hOne)) ≃
      Fin (evenTargetCount n) :=
  Equiv.ofBijective (internalIndex T hL hOne)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨internalIndex_injective T hL hOne,
        by simpa using internalIndex_domain_card T hL hOne⟩)

@[simp] theorem internalRankEquiv_apply (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T)
    (d : DepthEdge (leftDepthSet T hOne) ⊕ DepthEdge (rightDepthSet T hOne)) :
    internalRankEquiv T hL hOne d = internalIndex T hL hOne d := rfl

theorem leftInternalHalfRank_eq_dist (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T)
    (d : DepthEdge (leftDepthSet T hOne)) :
    leftInternalHalfRank T hL hOne d =
      T.dist (((leftDepthEquiv T hL hOne).symm d.1.inf).1)
        (((leftDepthEquiv T hL hOne).symm d.1.sup).1) / 2 := by
  unfold leftInternalHalfRank leftInternalPair
  rw [pairDist_internalPairOfDepthEdge]
  rfl

theorem rightInternalHalfRank_eq_dist (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T)
    (d : DepthEdge (rightDepthSet T hOne)) :
    rightInternalHalfRank T hL hOne d =
      T.dist (((rightDepthEquiv T hL hOne).symm d.1.inf).1)
        (((rightDepthEquiv T hL hOne).symm d.1.sup).1) / 2 := by
  unfold rightInternalHalfRank rightInternalPair
  rw [pairDist_internalPairOfDepthEdge]
  rfl

theorem leftInternalRank_realizes (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T)
    (d : DepthEdge (leftDepthSet T hOne)) :
    RealizesInternalRank (leftDepthSet T hOne)
      (((internalRankEquiv T hL hOne (Sum.inl d) :
        Fin (evenTargetCount n)) : ℕ) + 1) := by
  let u := (leftDepthEquiv T hL hOne).symm d.1.inf
  let v := (leftDepthEquiv T hL hOne).symm d.1.sup
  have hu : leftHalfDepth T hOne u = d.1.inf.1 := by
    have h := (leftDepthEquiv T hL hOne).apply_symm_apply d.1.inf
    exact congrArg Subtype.val h
  have hv : leftHalfDepth T hOne v = d.1.sup.1 := by
    have h := (leftDepthEquiv T hL hOne).apply_symm_apply d.1.sup
    exact congrArg Subtype.val h
  obtain ⟨z, hzu, hzv, hgate⟩ := exists_left_half_gate T hOne u v
  have hne : d.1.inf.1 ≠ d.1.sup.1 := by
    intro h
    apply depthEdge_inf_ne_sup d
    exact Subtype.ext h
  have hrank :
      ((internalRankEquiv T hL hOne (Sum.inl d) :
        Fin (evenTargetCount n)) : ℕ) + 1 =
        leftInternalHalfRank T hL hOne d := by
    rw [internalRankEquiv_apply]
    exact leftInternalIndex_val_add_one T hL hOne d
  refine ⟨d.1.inf.1, d.1.inf.2, d.1.sup.1, d.1.sup.2, hne,
    leftHalfDepth T hOne z, ?_, ?_, ?_, ?_⟩
  · simp [leftDepthSet]
  · simpa [hu] using hzu
  · simpa [hv] using hzv
  · rw [hrank, leftInternalHalfRank_eq_dist, ← hu, ← hv]
    exact hgate

theorem rightInternalRank_realizes (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T)
    (d : DepthEdge (rightDepthSet T hOne)) :
    RealizesInternalRank (rightDepthSet T hOne)
      (((internalRankEquiv T hL hOne (Sum.inr d) :
        Fin (evenTargetCount n)) : ℕ) + 1) := by
  let u := (rightDepthEquiv T hL hOne).symm d.1.inf
  let v := (rightDepthEquiv T hL hOne).symm d.1.sup
  have hu : rightHalfDepth T hOne u = d.1.inf.1 := by
    have h := (rightDepthEquiv T hL hOne).apply_symm_apply d.1.inf
    exact congrArg Subtype.val h
  have hv : rightHalfDepth T hOne v = d.1.sup.1 := by
    have h := (rightDepthEquiv T hL hOne).apply_symm_apply d.1.sup
    exact congrArg Subtype.val h
  obtain ⟨z, hzu, hzv, hgate⟩ := exists_right_half_gate T hOne u v
  have hne : d.1.inf.1 ≠ d.1.sup.1 := by
    intro h
    apply depthEdge_inf_ne_sup d
    exact Subtype.ext h
  have hrank :
      ((internalRankEquiv T hL hOne (Sum.inr d) :
        Fin (evenTargetCount n)) : ℕ) + 1 =
        rightInternalHalfRank T hL hOne d := by
    rw [internalRankEquiv_apply]
    exact rightInternalIndex_val_add_one T hL hOne d
  refine ⟨d.1.inf.1, d.1.inf.2, d.1.sup.1, d.1.sup.2, hne,
    rightHalfDepth T hOne z, ?_, ?_, ?_, ?_⟩
  · simp [rightDepthSet]
  · simpa [hu] using hzu
  · simpa [hv] using hzv
  · rw [hrank, rightInternalHalfRank_eq_dist, ← hu, ← hv]
    exact hgate

noncomputable def internalRanks (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T) :
    InternalRankPartition (leftDepthSet T hOne) (rightDepthSet T hOne)
      (evenTargetCount n) where
  rankEquiv := internalRankEquiv T hL hOne
  realizes_left := leftInternalRank_realizes T hL hOne
  realizes_right := rightInternalRank_realizes T hL hOne

/-! ## Indexed parity count on the two complete depth graphs -/

def evenPart (X : Finset ℕ) : Finset ℕ := X.filter Even

def oddPart (X : Finset ℕ) : Finset ℕ := X.filter (fun x => ¬Even x)

noncomputable def evenVertexEquiv (X : Finset ℕ) :
    {x : ↑X // Even x.1} ≃ ↑(evenPart X) where
  toFun x := ⟨x.1.1, by simp [evenPart, x.1.2, x.2]⟩
  invFun x := ⟨⟨x.1, (Finset.mem_filter.mp x.2).1⟩,
    (Finset.mem_filter.mp x.2).2⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl

noncomputable def oddVertexEquiv (X : Finset ℕ) :
    {x : ↑X // ¬Even x.1} ≃ ↑(oddPart X) where
  toFun x := ⟨x.1.1, by
    apply Finset.mem_filter.mpr
    exact ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨⟨x.1, (Finset.mem_filter.mp x.2).1⟩,
    (Finset.mem_filter.mp x.2).2⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl

abbrev OddDepthEdge (X : Finset ℕ) :=
  {d : DepthEdge X // Odd (d.1.inf.1 + d.1.sup.1)}

noncomputable def oddDepthEdgeMap (X : Finset ℕ) :
    ({x : ↑X // Even x.1} × {x : ↑X // ¬Even x.1}) → OddDepthEdge X :=
  fun p => by
    have hne : p.1.1 ≠ p.2.1 := by
      intro h
      exact p.2.2 (h ▸ p.1.2)
    let d : DepthEdge X := ⟨s(p.1.1, p.2.1), by simpa using hne⟩
    have hsum : d.1.inf.1 + d.1.sup.1 = p.1.1.1 + p.2.1.1 := by
      by_cases hle : p.1.1 ≤ p.2.1
      · simp [d, hle]
      · have hrev : p.2.1 ≤ p.1.1 := le_of_not_ge hle
        simp [d, hrev, Nat.add_comm]
    refine ⟨d, ?_⟩
    rw [hsum]
    exact p.1.2.add_odd (Nat.not_even_iff_odd.mp p.2.2)

theorem oddDepthEdgeMap_injective (X : Finset ℕ) :
    Function.Injective (oddDepthEdgeMap X) := by
  intro p q h
  have he := congrArg (fun z : OddDepthEdge X => z.1.1) h
  change s(p.1.1, p.2.1) = s(q.1.1, q.2.1) at he
  rcases Sym2.eq_iff.mp he with hdirect | hswap
  · rcases hdirect with ⟨h1, h2⟩
    apply Prod.ext
    · exact Subtype.ext h1
    · exact Subtype.ext h2
  · rcases hswap with ⟨h1, h2⟩
    exfalso
    exact q.2.2 (h1 ▸ p.1.2)

theorem oddDepthEdgeMap_surjective (X : Finset ℕ) :
    Function.Surjective (oddDepthEdgeMap X) := by
  intro d
  have hop :
      (Even d.1.1.inf.1 ∧ ¬Even d.1.1.sup.1) ∨
        (¬Even d.1.1.inf.1 ∧ Even d.1.1.sup.1) := by
    have hodd := d.2
    rw [Nat.odd_iff] at hodd
    simp only [Nat.even_iff]
    omega
  have hsort : s(d.1.1.inf, d.1.1.sup) = d.1.1 := by
    exact Sym2.sortEquiv.symm_apply_apply d.1.1
  rcases hop with h | h
  · refine ⟨(⟨⟨d.1.1.inf, h.1⟩, ⟨d.1.1.sup, h.2⟩⟩), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hsort
  · refine ⟨(⟨⟨d.1.1.sup, h.2⟩, ⟨d.1.1.inf, h.1⟩⟩), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact Sym2.eq_swap.trans hsort

noncomputable def oddDepthEdgeEquiv (X : Finset ℕ) :
    ({x : ↑X // Even x.1} × {x : ↑X // ¬Even x.1}) ≃ OddDepthEdge X :=
  Equiv.ofBijective (oddDepthEdgeMap X)
    ⟨oddDepthEdgeMap_injective X, oddDepthEdgeMap_surjective X⟩

theorem oddDepthEdge_card (X : Finset ℕ) :
    Fintype.card (OddDepthEdge X) = (evenPart X).card * (oddPart X).card := by
  calc
    Fintype.card (OddDepthEdge X) =
        Fintype.card ({x : ↑X // Even x.1} × {x : ↑X // ¬Even x.1}) :=
      (Fintype.card_congr (oddDepthEdgeEquiv X)).symm
    _ = Fintype.card {x : ↑X // Even x.1} *
        Fintype.card {x : ↑X // ¬Even x.1} := Fintype.card_prod _ _
    _ = (evenPart X).card * (oddPart X).card := by
      rw [Fintype.card_congr (evenVertexEquiv X),
        Fintype.card_congr (oddVertexEquiv X)]
      simp

theorem leftInternalRank_mod_two (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T)
    (d : DepthEdge (leftDepthSet T hOne)) :
    ((((internalRankEquiv T hL hOne (Sum.inl d) :
        Fin (evenTargetCount n)) : ℕ) + 1) % 2) =
      (d.1.inf.1 + d.1.sup.1) % 2 := by
  let u := (leftDepthEquiv T hL hOne).symm d.1.inf
  let v := (leftDepthEquiv T hL hOne).symm d.1.sup
  have hu : leftHalfDepth T hOne u = d.1.inf.1 := by
    have h := (leftDepthEquiv T hL hOne).apply_symm_apply d.1.inf
    exact congrArg Subtype.val h
  have hv : leftHalfDepth T hOne v = d.1.sup.1 := by
    have h := (leftDepthEquiv T hL hOne).apply_symm_apply d.1.sup
    exact congrArg Subtype.val h
  obtain ⟨z, _, _, hgate⟩ := exists_left_half_gate T hOne u v
  have hrank :
      ((internalRankEquiv T hL hOne (Sum.inl d) :
        Fin (evenTargetCount n)) : ℕ) + 1 =
        leftInternalHalfRank T hL hOne d := by
    rw [internalRankEquiv_apply]
    exact leftInternalIndex_val_add_one T hL hOne d
  have heq := hgate
  rw [← leftInternalHalfRank_eq_dist T hL hOne d,
    ← hrank, hu, hv] at heq
  omega

theorem rightInternalRank_mod_two (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T)
    (d : DepthEdge (rightDepthSet T hOne)) :
    ((((internalRankEquiv T hL hOne (Sum.inr d) :
        Fin (evenTargetCount n)) : ℕ) + 1) % 2) =
      (d.1.inf.1 + d.1.sup.1) % 2 := by
  let u := (rightDepthEquiv T hL hOne).symm d.1.inf
  let v := (rightDepthEquiv T hL hOne).symm d.1.sup
  have hu : rightHalfDepth T hOne u = d.1.inf.1 := by
    have h := (rightDepthEquiv T hL hOne).apply_symm_apply d.1.inf
    exact congrArg Subtype.val h
  have hv : rightHalfDepth T hOne v = d.1.sup.1 := by
    have h := (rightDepthEquiv T hL hOne).apply_symm_apply d.1.sup
    exact congrArg Subtype.val h
  obtain ⟨z, _, _, hgate⟩ := exists_right_half_gate T hOne u v
  have hrank :
      ((internalRankEquiv T hL hOne (Sum.inr d) :
        Fin (evenTargetCount n)) : ℕ) + 1 =
        rightInternalHalfRank T hL hOne d := by
    rw [internalRankEquiv_apply]
    exact rightInternalIndex_val_add_one T hL hOne d
  have heq := hgate
  rw [← rightInternalHalfRank_eq_dist T hL hOne d,
    ← hrank, hu, hv] at heq
  omega

def combinedDepthOdd (X Y : Finset ℕ) :
    DepthEdge X ⊕ DepthEdge Y → Prop
  | Sum.inl d => Odd (d.1.inf.1 + d.1.sup.1)
  | Sum.inr d => Odd (d.1.inf.1 + d.1.sup.1)

noncomputable instance combinedDepthOddFintype (X Y : Finset ℕ) :
    Fintype {d : DepthEdge X ⊕ DepthEdge Y // combinedDepthOdd X Y d} :=
  Fintype.ofFinite _

def combinedOddDepthEquiv (X Y : Finset ℕ) :
    {d : DepthEdge X ⊕ DepthEdge Y // combinedDepthOdd X Y d} ≃
      OddDepthEdge X ⊕ OddDepthEdge Y where
  toFun d := by
    rcases d with ⟨d, hd⟩
    cases d with
    | inl e => exact Sum.inl ⟨e, hd⟩
    | inr e => exact Sum.inr ⟨e, hd⟩
  invFun d := by
    cases d with
    | inl e => exact ⟨Sum.inl e.1, e.2⟩
    | inr e => exact ⟨Sum.inr e.1, e.2⟩
  left_inv d := by cases d with | mk d hd => cases d <;> rfl
  right_inv d := by cases d <;> rfl

noncomputable def combinedOddRankEquiv (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T) :
    {d : DepthEdge (leftDepthSet T hOne) ⊕
          DepthEdge (rightDepthSet T hOne) //
        combinedDepthOdd (leftDepthSet T hOne) (rightDepthSet T hOne) d} ≃
      {k : Fin (evenTargetCount n) // Odd ((k : ℕ) + 1)} :=
  Equiv.subtypeEquiv (internalRankEquiv T hL hOne) <| by
    intro d
    cases d with
    | inl e =>
        change Odd (e.1.inf.1 + e.1.sup.1) ↔
          Odd (((internalRankEquiv T hL hOne (Sum.inl e) :
            Fin (evenTargetCount n)) : ℕ) + 1)
        rw [Nat.odd_iff, Nat.odd_iff]
        rw [leftInternalRank_mod_two T hL hOne e]
    | inr e =>
        change Odd (e.1.inf.1 + e.1.sup.1) ↔
          Odd (((internalRankEquiv T hL hOne (Sum.inr e) :
            Fin (evenTargetCount n)) : ℕ) + 1)
        rw [Nat.odd_iff, Nat.odd_iff]
        rw [rightInternalRank_mod_two T hL hOne e]

noncomputable def oddFinEquivTarget (M : ℕ) :
    {k : Fin M // Odd ((k : ℕ) + 1)} ≃ ↑(oddTargetRanks M) where
  toFun k := ⟨(k.1 : ℕ) + 1, by
    rw [oddTargetRanks, Finset.mem_filter]
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    exact Nat.odd_iff.mp k.2⟩
  invFun k := by
    have hk := Finset.mem_filter.mp k.2
    refine ⟨⟨k.1 - 1, by
      have hb := Finset.mem_Icc.mp hk.1
      omega⟩, ?_⟩
    rw [Nat.odd_iff]
    have hb := Finset.mem_Icc.mp hk.1
    simpa [Nat.sub_add_cancel hb.1] using hk.2
  left_inv k := by
    apply Subtype.ext
    apply Fin.ext
    change (((k.1 : ℕ) + 1) - 1) = (k.1 : ℕ)
    omega
  right_inv k := by
    apply Subtype.ext
    have hk := Finset.mem_Icc.mp (Finset.mem_filter.mp k.2).1
    change k.1 - 1 + 1 = k.1
    omega

theorem oddInternalDepthEdge_card (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T) :
    Fintype.card (OddDepthEdge (leftDepthSet T hOne)) +
        Fintype.card (OddDepthEdge (rightDepthSet T hOne)) =
      (evenTargetCount n + 1) / 2 := by
  calc
    Fintype.card (OddDepthEdge (leftDepthSet T hOne)) +
        Fintype.card (OddDepthEdge (rightDepthSet T hOne)) =
        Fintype.card (OddDepthEdge (leftDepthSet T hOne) ⊕
          OddDepthEdge (rightDepthSet T hOne)) := Fintype.card_sum.symm
    _ = Fintype.card
        {d : DepthEdge (leftDepthSet T hOne) ⊕
            DepthEdge (rightDepthSet T hOne) //
          combinedDepthOdd (leftDepthSet T hOne) (rightDepthSet T hOne) d} :=
      (Fintype.card_congr
        (combinedOddDepthEquiv (leftDepthSet T hOne)
          (rightDepthSet T hOne))).symm
    _ = Fintype.card
        {k : Fin (evenTargetCount n) // Odd ((k : ℕ) + 1)} :=
      Fintype.card_congr (combinedOddRankEquiv T hL hOne)
    _ = Fintype.card ↑(oddTargetRanks (evenTargetCount n)) :=
      Fintype.card_congr (oddFinEquivTarget (evenTargetCount n))
    _ = (evenTargetCount n + 1) / 2 := by
      rw [Fintype.card_coe, oddTargetRanks_card]

theorem oddInternalProductCount (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T) :
    (evenPart (leftDepthSet T hOne)).card *
          (oddPart (leftDepthSet T hOne)).card +
        (evenPart (rightDepthSet T hOne)).card *
          (oddPart (rightDepthSet T hOne)).card =
      (evenTargetCount n + 1) / 2 := by
  rw [← oddDepthEdge_card, ← oddDepthEdge_card]
  exact oddInternalDepthEdge_card T hL hOne

theorem evenPart_card_add_oddPart_card (X : Finset ℕ) :
    (evenPart X).card + (oddPart X).card = X.card := by
  simpa [evenPart, oddPart] using
    (Finset.filter_card_add_filter_neg_card_eq_card
      (s := X) (p := fun x : ℕ => Even x))

theorem signedImbalance_eq_even_sub_odd (X : Finset ℕ) :
    signedImbalance X =
      ((evenPart X).card : ℤ) - ((oddPart X).card : ℤ) := by
  classical
  unfold signedImbalance
  have hsplit := Finset.sum_filter_add_sum_filter_not X
    (fun x : ℕ => Even x) (fun x => (-1 : ℤ) ^ x)
  have hsplit' :
      (∑ x ∈ evenPart X, (-1 : ℤ) ^ x) +
        (∑ x ∈ oddPart X, (-1 : ℤ) ^ x) =
          ∑ x ∈ X, (-1 : ℤ) ^ x := by
    simpa [evenPart, oddPart] using hsplit
  have he : (∑ x ∈ evenPart X, (-1 : ℤ) ^ x) =
      ((evenPart X).card : ℤ) := by
    calc
      (∑ x ∈ evenPart X, (-1 : ℤ) ^ x) =
          ∑ _x ∈ evenPart X, (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxEven := (Finset.mem_filter.mp hx).2
        rw [hxEven.neg_one_pow]
      _ = ((evenPart X).card : ℤ) := by simp
  have ho : (∑ x ∈ oddPart X, (-1 : ℤ) ^ x) =
      -((oddPart X).card : ℤ) := by
    calc
      (∑ x ∈ oddPart X, (-1 : ℤ) ^ x) =
          ∑ _x ∈ oddPart X, (-1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxOdd : Odd x := Nat.not_even_iff_odd.mp
          (Finset.mem_filter.mp hx).2
        rw [hxOdd.neg_one_pow]
      _ = -((oddPart X).card : ℤ) := by simp
  rw [← hsplit']
  rw [he, ho]
  ring

theorem card_sq_sub_signedImbalance_sq (X : Finset ℕ) :
    (X.card : ℤ) ^ 2 - signedImbalance X ^ 2 =
      4 * ((evenPart X).card : ℤ) * ((oddPart X).card : ℤ) := by
  have hc := evenPart_card_add_oddPart_card X
  have hcZ : (X.card : ℤ) =
      ((evenPart X).card : ℤ) + ((oddPart X).card : ℤ) := by
    exact_mod_cast hc.symm
  rw [signedImbalance_eq_even_sub_odd, hcZ]
  ring

theorem depthSets_parity_even (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T) :
    Even (evenTargetCount n) →
      ((leftDepthSet T hOne).card : ℤ) ^ 2 +
        ((rightDepthSet T hOne).card : ℤ) ^ 2 -
        signedImbalance (leftDepthSet T hOne) ^ 2 -
        signedImbalance (rightDepthSet T hOne) ^ 2 =
          2 * (evenTargetCount n : ℤ) := by
  intro hEven
  have hx := card_sq_sub_signedImbalance_sq (leftDepthSet T hOne)
  have hy := card_sq_sub_signedImbalance_sq (rightDepthSet T hOne)
  have hc := oddInternalProductCount T hL hOne
  have hcZ :
      ((evenPart (leftDepthSet T hOne)).card : ℤ) *
          ((oddPart (leftDepthSet T hOne)).card : ℤ) +
        ((evenPart (rightDepthSet T hOne)).card : ℤ) *
          ((oddPart (rightDepthSet T hOne)).card : ℤ) =
        (((evenTargetCount n + 1) / 2 : ℕ) : ℤ) := by
    exact_mod_cast hc
  have hNat : 4 * ((evenTargetCount n + 1) / 2) =
      2 * evenTargetCount n := by
    rcases hEven with ⟨k, hk⟩
    omega
  have hZ : (4 : ℤ) * (((evenTargetCount n + 1) / 2 : ℕ) : ℤ) =
      2 * (evenTargetCount n : ℤ) := by
    exact_mod_cast hNat
  nlinarith

theorem depthSets_parity_odd (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T) :
    Odd (evenTargetCount n) →
      ((leftDepthSet T hOne).card : ℤ) ^ 2 +
        ((rightDepthSet T hOne).card : ℤ) ^ 2 -
        signedImbalance (leftDepthSet T hOne) ^ 2 -
        signedImbalance (rightDepthSet T hOne) ^ 2 =
          2 * ((evenTargetCount n : ℤ) + 1) := by
  intro hOdd
  have hx := card_sq_sub_signedImbalance_sq (leftDepthSet T hOne)
  have hy := card_sq_sub_signedImbalance_sq (rightDepthSet T hOne)
  have hc := oddInternalProductCount T hL hOne
  have hcZ :
      ((evenPart (leftDepthSet T hOne)).card : ℤ) *
          ((oddPart (leftDepthSet T hOne)).card : ℤ) +
        ((evenPart (rightDepthSet T hOne)).card : ℤ) *
          ((oddPart (rightDepthSet T hOne)).card : ℤ) =
        (((evenTargetCount n + 1) / 2 : ℕ) : ℤ) := by
    exact_mod_cast hc
  have hNat : 4 * ((evenTargetCount n + 1) / 2) =
      2 * (evenTargetCount n + 1) := by
    rcases hOdd with ⟨k, hk⟩
    omega
  have hZ : (4 : ℤ) * (((evenTargetCount n + 1) / 2 : ℕ) : ℤ) =
      2 * ((evenTargetCount n : ℤ) + 1) := by
    exact_mod_cast hNat
  nlinarith

/-! ## Orientation and the concrete `OneOddDecomposition` -/

def internalRankPartitionComm {X Y : Finset ℕ} {M : ℕ}
    (p : InternalRankPartition X Y M) : InternalRankPartition Y X M where
  rankEquiv := (Equiv.sumComm (DepthEdge Y) (DepthEdge X)).trans p.rankEquiv
  realizes_left e := p.realizes_right e
  realizes_right e := p.realizes_left e

theorem depthSet_card_add (hL : IsLeech T)
    (hOne : ExactlyOneOddPhysicalEdge T) :
    (leftDepthSet T hOne).card + (rightDepthSet T hOne).card = n := by
  rw [leftDepthSet_card T hL hOne, rightDepthSet_card T hL hOne]
  have hlt := T.cutSize_lt_order (uniqueOddEdge T hOne)
  omega

theorem one_mem_either_depthSet (hL : IsLeech T) (hn : 18 ≤ n)
    (hOne : ExactlyOneOddPhysicalEdge T) :
    1 ∈ leftDepthSet T hOne ∨ 1 ∈ rightDepthSet T hOne := by
  have hn2 : 2 ≤ n := by omega
  have hNle : targetN 18 ≤ targetN n := by
    simpa [targetN] using Nat.choose_le_choose 2 hn
  have h18 : Nat.choose 18 2 = 153 := by norm_num [Nat.choose]
  have hC : 1 < oddTargetCount n := by
    rw [oddTargetCount_eq]
    change 1 < (n.choose 2 + 1) / 2
    change Nat.choose 18 2 ≤ Nat.choose n 2 at hNle
    rw [h18] at hNle
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    (crossRanks T hL hn2 hOne).exists_repr hC
  have hcases : (x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) := by omega
  rcases hcases with h | h
  · exact Or.inl (h.1 ▸ hx)
  · exact Or.inr (h.2 ▸ hy)

noncomputable def oneOddDecompositionOfGraph (hL : IsLeech T)
    (hn : 18 ≤ n) (hOne : ExactlyOneOddPhysicalEdge T) :
    OneOddDecomposition n := by
  classical
  have hn2 : 2 ≤ n := by omega
  have hEither := one_mem_either_depthSet T hL hn hOne
  by_cases hOneLeft : 1 ∈ leftDepthSet T hOne
  · exact
      { N := targetN n
        C := oddTargetCount n
        M := evenTargetCount n
        leftOrder := (leftDepthSet T hOne).card
        rightOrder := (rightDepthSet T hOne).card
        X := leftDepthSet T hOne
        Y := rightDepthSet T hOne
        pair_twice := two_mul_targetN n
        target_split := (oddTargetCount_add_evenTargetCount (n := n)).symm
        target_case := oddTargetCount_evenTargetCount_case (n := n)
        component_orders := depthSet_card_add T hL hOne
        cross_count := (crossRanks T hL hn2 hOne).card_mul
        card_X := rfl
        card_Y := rfl
        zero_X := zero_mem_leftDepthSet T hOne
        zero_Y := zero_mem_rightDepthSet T hOne
        one_X := hOneLeft
        crossRanks := crossRanks T hL hn2 hOne
        internalRanks := internalRanks T hL hOne
        parity_even := depthSets_parity_even T hL hOne
        parity_odd := depthSets_parity_odd T hL hOne }
  · have hOneRight : 1 ∈ rightDepthSet T hOne :=
      hEither.resolve_left hOneLeft
    exact
      { N := targetN n
        C := oddTargetCount n
        M := evenTargetCount n
        leftOrder := (rightDepthSet T hOne).card
        rightOrder := (leftDepthSet T hOne).card
        X := rightDepthSet T hOne
        Y := leftDepthSet T hOne
        pair_twice := two_mul_targetN n
        target_split := (oddTargetCount_add_evenTargetCount (n := n)).symm
        target_case := oddTargetCount_evenTargetCount_case (n := n)
        component_orders := by
          rw [Nat.add_comm]
          exact depthSet_card_add T hL hOne
        cross_count := ((crossRanks T hL hn2 hOne).comm).card_mul
        card_X := rfl
        card_Y := rfl
        zero_X := zero_mem_rightDepthSet T hOne
        zero_Y := zero_mem_leftDepthSet T hOne
        one_X := hOneRight
        crossRanks := (crossRanks T hL hn2 hOne).comm
        internalRanks := internalRankPartitionComm (internalRanks T hL hOne)
        parity_even := by
          intro h
          have hp := depthSets_parity_even T hL hOne h
          nlinarith
        parity_odd := by
          intro h
          have hp := depthSets_parity_odd T hL hOne h
          nlinarith }

/-- Concrete, unconditional graph-level T11: no positive-integral Leech tree
of order at least 18 has exactly one odd physical edge. -/
theorem T11_no_exactly_one_odd {n : ℕ} (T : PosIntTree n)
    (hL : IsLeech T) (hn : 18 ≤ n) :
    ¬ExactlyOneOddPhysicalEdge T := by
  intro hOne
  exact oneOddDecomposition_impossible hn
    (oneOddDecompositionOfGraph T hL hn hOne)

end LeechTrees.OddEdges.T11Adapter
