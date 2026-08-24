import LeechTrees.LeafAttachmentAdapter

/-!
# Correct small-order boundary for literal one-leaf extensions

This module records the exact existential notion of a successful
literal unchanged one-leaf step, constructs the positive base-order two and
three witnesses, and combines them with the existing order-at-least-four
obstruction.  It deliberately does not turn a `CompletesOneLeafTail` support
identity into an output-tree existence claim.

The optional vacuous-base endpoint at order one is kept separate.  The
adjacent `DESIGN.md` is the historical pre-integration design record; current
kernel and release-validation status is recorded in the package README and
release evidence.
-/

namespace LeechTrees.SmallLeafBoundary

open LeechTrees.Foundation
open LeechTrees.OperationAdapters

/-- There is an actual Leech-to-Leech literal one-leaf attachment at base
order `m`.  This quantifies over both weighted trees and the graph-level
operation record; it is intentionally stronger than the tail-set predicate
`CompletesOneLeafTail`. -/
def HasSuccessfulLiteralOneLeafStep (m : ℕ) : Prop :=
  ∃ (T : PosIntTree m) (U : PosIntTree (m + 1))
      (_L : LiteralOneLeafAttachment T U),
    IsLeech T ∧ IsLeech U

/-! ## Closed small positive witnesses -/

private def graphOne : SimpleGraph (Fin 1) := ⊥

private def graphTwo : SimpleGraph (Fin 2) :=
  SimpleGraph.edge 0 1

private def graphThree : SimpleGraph (Fin 3) :=
  SimpleGraph.edge 0 1 ⊔ SimpleGraph.edge 1 2

private def graphFour : SimpleGraph (Fin 4) :=
  (SimpleGraph.edge 0 1 ⊔ SimpleGraph.edge 1 2) ⊔
    SimpleGraph.edge 1 3

@[simp] private theorem graphOne_edgeSet :
    graphOne.edgeSet = (∅ : Set (Sym2 (Fin 1))) := by
  simp [graphOne]

@[simp] private theorem graphTwo_edgeSet :
    graphTwo.edgeSet =
      ({s((0 : Fin 2), (1 : Fin 2))} : Set (Sym2 (Fin 2))) := by
  exact SimpleGraph.edge_edgeSet_of_ne (by decide)

@[simp] private theorem graphThree_edgeSet :
    graphThree.edgeSet =
      ({s((0 : Fin 3), (1 : Fin 3)),
        s((1 : Fin 3), (2 : Fin 3))} : Set (Sym2 (Fin 3))) := by
  rw [graphThree, SimpleGraph.edgeSet_sup,
    SimpleGraph.edge_edgeSet_of_ne (by decide : (0 : Fin 3) ≠ 1),
    SimpleGraph.edge_edgeSet_of_ne (by decide : (1 : Fin 3) ≠ 2)]
  ext e
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]

@[simp] private theorem graphFour_edgeSet :
    graphFour.edgeSet =
      ({s((0 : Fin 4), (1 : Fin 4)),
        s((1 : Fin 4), (2 : Fin 4)),
        s((1 : Fin 4), (3 : Fin 4))} : Set (Sym2 (Fin 4))) := by
  rw [graphFour, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_sup,
    SimpleGraph.edge_edgeSet_of_ne (by decide : (0 : Fin 4) ≠ 1),
    SimpleGraph.edge_edgeSet_of_ne (by decide : (1 : Fin 4) ≠ 2),
    SimpleGraph.edge_edgeSet_of_ne (by decide : (1 : Fin 4) ≠ 3)]
  ext e
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff,
    or_assoc]

private theorem graphTwo_connected : graphTwo.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨(0 : Fin 2), ?_⟩
  intro v
  fin_cases v
  · exact SimpleGraph.Reachable.rfl
  · exact SimpleGraph.Adj.reachable (by
      simp [graphTwo, SimpleGraph.edge_adj])

private theorem graphOne_isTree : graphOne.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  constructor
  · simpa [graphOne] using
      (SimpleGraph.connected_bot_iff.mpr
        (show Subsingleton (Fin 1) ∧ Nonempty (Fin 1) from
          ⟨inferInstance, inferInstance⟩))
  · rw [graphOne_edgeSet]
    simp

private theorem graphThree_connected : graphThree.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨(1 : Fin 3), ?_⟩
  intro v
  fin_cases v
  · exact SimpleGraph.Adj.reachable (by
      simp [graphThree, SimpleGraph.edge_adj])
  · exact SimpleGraph.Reachable.rfl
  · exact SimpleGraph.Adj.reachable (by
      simp [graphThree, SimpleGraph.edge_adj])

private theorem graphFour_connected : graphFour.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨(1 : Fin 4), ?_⟩
  intro v
  fin_cases v
  · exact SimpleGraph.Adj.reachable (by
      simp [graphFour, SimpleGraph.edge_adj])
  · exact SimpleGraph.Reachable.rfl
  · exact SimpleGraph.Adj.reachable (by
      simp [graphFour, SimpleGraph.edge_adj])
  · exact SimpleGraph.Adj.reachable (by
      simp [graphFour, SimpleGraph.edge_adj])

private theorem graphTwo_isTree : graphTwo.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨graphTwo_connected, ?_⟩
  rw [graphTwo_edgeSet]
  simp

private theorem graphThree_isTree : graphThree.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨graphThree_connected, ?_⟩
  rw [graphThree_edgeSet]
  simp [
    show s((0 : Fin 3), (1 : Fin 3)) ≠ s((1 : Fin 3), (2 : Fin 3)) by
      decide]

private theorem graphFour_isTree : graphFour.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨graphFour_connected, ?_⟩
  rw [graphFour_edgeSet]
  simp [
    show s((0 : Fin 4), (1 : Fin 4)) ≠ s((1 : Fin 4), (2 : Fin 4)) by
      decide,
    show s((0 : Fin 4), (1 : Fin 4)) ≠ s((1 : Fin 4), (3 : Fin 4)) by
      decide,
    show s((1 : Fin 4), (2 : Fin 4)) ≠ s((1 : Fin 4), (3 : Fin 4)) by
      decide]

/-- The one-vertex tree used only for the explicit vacuous-base convention.
Its physical edge type is empty. -/
def leechOne : PosIntTree 1 where
  graph := graphOne
  isTree := graphOne_isTree
  weight := fun e => False.elim (by
    have hemem := e.2
    change e.1 ∈ graphOne.edgeSet at hemem
    simp at hemem)
  weight_pos := by
    intro e
    have hemem := e.2
    change e.1 ∈ graphOne.edgeSet at hemem
    simp at hemem

/-- The unique order-two positive example, with its physical edge of
weight one. -/
def leechTwo : PosIntTree 2 where
  graph := graphTwo
  isTree := graphTwo_isTree
  weight := fun _ => 1
  weight_pos := by
    intro e
    omega

/-- The order-three path `0 - 1 - 2`, with physical weights one and two. -/
def leechThree : PosIntTree 3 where
  graph := graphThree
  isTree := graphThree_isTree
  weight := fun e =>
    if e.1 = s((0 : Fin 3), (1 : Fin 3)) then 1 else 2
  weight_pos := by
    intro e
    split_ifs <;> omega

/-- The order-four star centered at vertex one, with physical weights one,
two, and four on leaves zero, two, and three respectively. -/
def leechFour : PosIntTree 4 where
  graph := graphFour
  isTree := graphFour_isTree
  weight := fun e =>
    if e.1 = s((0 : Fin 4), (1 : Fin 4)) then 1
    else if e.1 = s((1 : Fin 4), (2 : Fin 4)) then 2
    else 4
  weight_pos := by
    intro e
    split_ifs <;> omega

private theorem dist_of_adjacent
    {n : ℕ} (T : PosIntTree n) {u v : Fin n}
    (huv : T.graph.Adj u v) :
    T.dist u v = T.weightOfPair s(u, v) := by
  let p : T.graph.Path u v := SimpleGraph.Path.singleton huv
  calc
    T.dist u v = T.walkWeight p.1 :=
      (T.path_walkWeight_eq_dist p).symm
    _ = T.weightOfPair s(u, v) := by
      simp [p, SimpleGraph.Path.singleton, PosIntTree.walkWeight]

private theorem dist_of_two_edges
    {n : ℕ} (T : PosIntTree n) {x v y : Fin n}
    (hxv : T.graph.Adj x v) (hvy : T.graph.Adj v y)
    (hxy : x ≠ y) :
    T.dist x y =
      T.weightOfPair s(x, v) + T.weightOfPair s(v, y) := by
  have hyx : y ≠ x := hxy.symm
  have hyv : y ≠ v := hvy.ne.symm
  let pxv : T.graph.Path x v := SimpleGraph.Path.singleton hxv
  let route : T.graph.Walk x y := pxv.1.concat hvy
  have hynot : y ∉ pxv.1.support := by
    simp [pxv, SimpleGraph.Path.singleton, hyx, hyv]
  have hroute : route.IsPath := pxv.2.concat hynot hvy
  calc
    T.dist x y = T.walkWeight route :=
      (T.path_walkWeight_eq_dist ⟨route, hroute⟩).symm
    _ = T.weightOfPair s(x, v) + T.weightOfPair s(v, y) := by
      simp [route, pxv, SimpleGraph.Path.singleton, PosIntTree.walkWeight]

private theorem leechTwo_adj_01 :
    leechTwo.graph.Adj (0 : Fin 2) 1 := by
  simp [leechTwo, graphTwo, SimpleGraph.edge_adj]

private theorem leechThree_adj_01 :
    leechThree.graph.Adj (0 : Fin 3) 1 := by
  simp [leechThree, graphThree, SimpleGraph.edge_adj]

private theorem leechThree_adj_12 :
    leechThree.graph.Adj (1 : Fin 3) 2 := by
  simp [leechThree, graphThree, SimpleGraph.edge_adj]

private theorem leechFour_adj_01 :
    leechFour.graph.Adj (0 : Fin 4) 1 := by
  simp [leechFour, graphFour, SimpleGraph.edge_adj]

private theorem leechFour_adj_12 :
    leechFour.graph.Adj (1 : Fin 4) 2 := by
  simp [leechFour, graphFour, SimpleGraph.edge_adj]

private theorem leechFour_adj_13 :
    leechFour.graph.Adj (1 : Fin 4) 3 := by
  simp [leechFour, graphFour, SimpleGraph.edge_adj]

@[simp] private theorem leechTwo_weightOfPair_01 :
    leechTwo.weightOfPair s((0 : Fin 2), (1 : Fin 2)) = 1 := by
  let e : leechTwo.Edge :=
    ⟨s((0 : Fin 2), (1 : Fin 2)), leechTwo_adj_01⟩
  rw [leechTwo.weightOfPair_edge e]
  rfl

@[simp] private theorem leechThree_weightOfPair_01 :
    leechThree.weightOfPair s((0 : Fin 3), (1 : Fin 3)) = 1 := by
  let e : leechThree.Edge :=
    ⟨s((0 : Fin 3), (1 : Fin 3)), leechThree_adj_01⟩
  rw [leechThree.weightOfPair_edge e]
  simp [leechThree, e]

@[simp] private theorem leechThree_weightOfPair_12 :
    leechThree.weightOfPair s((1 : Fin 3), (2 : Fin 3)) = 2 := by
  let e : leechThree.Edge :=
    ⟨s((1 : Fin 3), (2 : Fin 3)), leechThree_adj_12⟩
  rw [leechThree.weightOfPair_edge e]
  simp [leechThree, e]

@[simp] private theorem leechFour_weightOfPair_01 :
    leechFour.weightOfPair s((0 : Fin 4), (1 : Fin 4)) = 1 := by
  let e : leechFour.Edge :=
    ⟨s((0 : Fin 4), (1 : Fin 4)), leechFour_adj_01⟩
  rw [leechFour.weightOfPair_edge e]
  simp [leechFour, e]

@[simp] private theorem leechFour_weightOfPair_12 :
    leechFour.weightOfPair s((1 : Fin 4), (2 : Fin 4)) = 2 := by
  let e : leechFour.Edge :=
    ⟨s((1 : Fin 4), (2 : Fin 4)), leechFour_adj_12⟩
  rw [leechFour.weightOfPair_edge e]
  simp [leechFour, e]

@[simp] private theorem leechFour_weightOfPair_13 :
    leechFour.weightOfPair s((1 : Fin 4), (3 : Fin 4)) = 4 := by
  let e : leechFour.Edge :=
    ⟨s((1 : Fin 4), (3 : Fin 4)), leechFour_adj_13⟩
  rw [leechFour.weightOfPair_edge e]
  simp [leechFour, e]

private abbrev pairTwo01 : VertexPair 2 :=
  ⟨((0 : Fin 2), (1 : Fin 2)), by decide⟩

private abbrev pairThree01 : VertexPair 3 :=
  ⟨((0 : Fin 3), (1 : Fin 3)), by decide⟩

private abbrev pairThree02 : VertexPair 3 :=
  ⟨((0 : Fin 3), (2 : Fin 3)), by decide⟩

private abbrev pairThree12 : VertexPair 3 :=
  ⟨((1 : Fin 3), (2 : Fin 3)), by decide⟩

private abbrev pairFour01 : VertexPair 4 :=
  ⟨((0 : Fin 4), (1 : Fin 4)), by decide⟩

private abbrev pairFour02 : VertexPair 4 :=
  ⟨((0 : Fin 4), (2 : Fin 4)), by decide⟩

private abbrev pairFour03 : VertexPair 4 :=
  ⟨((0 : Fin 4), (3 : Fin 4)), by decide⟩

private abbrev pairFour12 : VertexPair 4 :=
  ⟨((1 : Fin 4), (2 : Fin 4)), by decide⟩

private abbrev pairFour13 : VertexPair 4 :=
  ⟨((1 : Fin 4), (3 : Fin 4)), by decide⟩

private abbrev pairFour23 : VertexPair 4 :=
  ⟨((2 : Fin 4), (3 : Fin 4)), by decide⟩

@[simp] private theorem leechTwo_pairDist_01 :
    leechTwo.pairDist pairTwo01 = 1 := by
  change leechTwo.dist (0 : Fin 2) 1 = 1
  rw [dist_of_adjacent leechTwo leechTwo_adj_01]
  exact leechTwo_weightOfPair_01

@[simp] private theorem leechThree_pairDist_01 :
    leechThree.pairDist pairThree01 = 1 := by
  change leechThree.dist (0 : Fin 3) 1 = 1
  rw [dist_of_adjacent leechThree leechThree_adj_01]
  exact leechThree_weightOfPair_01

@[simp] private theorem leechThree_pairDist_02 :
    leechThree.pairDist pairThree02 = 3 := by
  change leechThree.dist (0 : Fin 3) 2 = 3
  rw [dist_of_two_edges leechThree leechThree_adj_01
    leechThree_adj_12 (by decide)]
  simp

@[simp] private theorem leechThree_pairDist_12 :
    leechThree.pairDist pairThree12 = 2 := by
  change leechThree.dist (1 : Fin 3) 2 = 2
  rw [dist_of_adjacent leechThree leechThree_adj_12]
  exact leechThree_weightOfPair_12

@[simp] private theorem leechFour_pairDist_01 :
    leechFour.pairDist pairFour01 = 1 := by
  change leechFour.dist (0 : Fin 4) 1 = 1
  rw [dist_of_adjacent leechFour leechFour_adj_01]
  exact leechFour_weightOfPair_01

@[simp] private theorem leechFour_pairDist_02 :
    leechFour.pairDist pairFour02 = 3 := by
  change leechFour.dist (0 : Fin 4) 2 = 3
  rw [dist_of_two_edges leechFour leechFour_adj_01
    leechFour_adj_12 (by decide)]
  simp

@[simp] private theorem leechFour_pairDist_03 :
    leechFour.pairDist pairFour03 = 5 := by
  change leechFour.dist (0 : Fin 4) 3 = 5
  rw [dist_of_two_edges leechFour leechFour_adj_01
    leechFour_adj_13 (by decide)]
  simp

@[simp] private theorem leechFour_pairDist_12 :
    leechFour.pairDist pairFour12 = 2 := by
  change leechFour.dist (1 : Fin 4) 2 = 2
  rw [dist_of_adjacent leechFour leechFour_adj_12]
  exact leechFour_weightOfPair_12

@[simp] private theorem leechFour_pairDist_13 :
    leechFour.pairDist pairFour13 = 4 := by
  change leechFour.dist (1 : Fin 4) 3 = 4
  rw [dist_of_adjacent leechFour leechFour_adj_13]
  exact leechFour_weightOfPair_13

@[simp] private theorem leechFour_pairDist_23 :
    leechFour.pairDist pairFour23 = 6 := by
  change leechFour.dist (2 : Fin 4) 3 = 6
  rw [dist_of_two_edges leechFour leechFour_adj_12.symm
    leechFour_adj_13 (by decide)]
  rw [show s((2 : Fin 4), (1 : Fin 4)) =
    s((1 : Fin 4), (2 : Fin 4)) by exact Sym2.eq_swap]
  simp

/-- The order-two witness has the exact indexed spectrum `{1}`. -/
theorem leechTwo_isLeech : IsLeech leechTwo := by
  let hmem : ∀ p, leechTwo.pairDist p ∈
      Finset.Icc 1 (targetN 2) := by
    intro p
    fin_cases p
    all_goals norm_num [targetN, pairTwo01]
  refine ⟨hmem, ?_⟩
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨?_, by decide⟩
  intro p q hpq
  have hval := congrArg Subtype.val hpq
  fin_cases p
  all_goals fin_cases q
  all_goals simp_all

/-- The order-three path has indexed distances `1,3,2`, hence the exact
target spectrum `{1,2,3}`. -/
theorem leechThree_isLeech : IsLeech leechThree := by
  let hmem : ∀ p, leechThree.pairDist p ∈
      Finset.Icc 1 (targetN 3) := by
    intro p
    have hlt : p.left.val < p.right.val := p.left_lt_right
    have hl : p.left.val < 3 := p.left.isLt
    have hr : p.right.val < 3 := p.right.isLt
    have hcases :
        (p.left.val = 0 ∧ p.right.val = 1) ∨
        (p.left.val = 0 ∧ p.right.val = 2) ∨
        (p.left.val = 1 ∧ p.right.val = 2) := by
      omega
    rcases hcases with ⟨hlv, hrv⟩ | ⟨hlv, hrv⟩ | ⟨hlv, hrv⟩
    · have hp : p = pairThree01 := by
        apply VertexPair.ext <;> apply Fin.ext
        · exact hlv
        · exact hrv
      rw [hp]
      norm_num [targetN, Nat.choose_two_right]
    · have hp : p = pairThree02 := by
        apply VertexPair.ext <;> apply Fin.ext
        · exact hlv
        · exact hrv
      rw [hp]
      norm_num [targetN, Nat.choose_two_right]
    · have hp : p = pairThree12 := by
        apply VertexPair.ext <;> apply Fin.ext
        · exact hlv
        · exact hrv
      rw [hp]
      norm_num [targetN, Nat.choose_two_right]
  refine ⟨hmem, ?_⟩
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨?_, by decide⟩
  intro p q hpq
  have hval := congrArg Subtype.val hpq
  fin_cases p
  all_goals fin_cases q
  all_goals simp_all

/-- The order-four star has indexed distances `1,3,5,2,4,6`, hence the
exact target spectrum `{1,2,3,4,5,6}`. -/
theorem leechFour_isLeech : IsLeech leechFour := by
  let hmem : ∀ p, leechFour.pairDist p ∈
      Finset.Icc 1 (targetN 4) := by
    intro p
    have hlt : p.left.val < p.right.val := p.left_lt_right
    have hl : p.left.val < 4 := p.left.isLt
    have hr : p.right.val < 4 := p.right.isLt
    have hcases :
        (p.left.val = 0 ∧ p.right.val = 1) ∨
        (p.left.val = 0 ∧ p.right.val = 2) ∨
        (p.left.val = 0 ∧ p.right.val = 3) ∨
        (p.left.val = 1 ∧ p.right.val = 2) ∨
        (p.left.val = 1 ∧ p.right.val = 3) ∨
        (p.left.val = 2 ∧ p.right.val = 3) := by
      omega
    rcases hcases with ⟨hlv, hrv⟩ | ⟨hlv, hrv⟩ | ⟨hlv, hrv⟩ |
        ⟨hlv, hrv⟩ | ⟨hlv, hrv⟩ | ⟨hlv, hrv⟩
    · have hp : p = pairFour01 := by
        apply VertexPair.ext <;> apply Fin.ext
        · exact hlv
        · exact hrv
      rw [hp]
      norm_num [targetN, Nat.choose_two_right]
    · have hp : p = pairFour02 := by
        apply VertexPair.ext <;> apply Fin.ext
        · exact hlv
        · exact hrv
      rw [hp]
      norm_num [targetN, Nat.choose_two_right]
    · have hp : p = pairFour03 := by
        apply VertexPair.ext <;> apply Fin.ext
        · exact hlv
        · exact hrv
      rw [hp]
      norm_num [targetN, Nat.choose_two_right]
    · have hp : p = pairFour12 := by
        apply VertexPair.ext <;> apply Fin.ext
        · exact hlv
        · exact hrv
      rw [hp]
      norm_num [targetN, Nat.choose_two_right]
    · have hp : p = pairFour13 := by
        apply VertexPair.ext <;> apply Fin.ext
        · exact hlv
        · exact hrv
      rw [hp]
      norm_num [targetN, Nat.choose_two_right]
    · have hp : p = pairFour23 := by
        apply VertexPair.ext <;> apply Fin.ext
        · exact hlv
        · exact hrv
      rw [hp]
      norm_num [targetN, Nat.choose_two_right]
  refine ⟨hmem, ?_⟩
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨?_, by decide⟩
  intro p q hpq
  have hval := congrArg Subtype.val hpq
  fin_cases p
  all_goals fin_cases q
  all_goals simp_all

/-- The order-one spectrum is vacuous: both the indexed pair type and the
target interval `Icc 1 (targetN 1)` are empty. -/
theorem leechOne_isLeech : IsLeech leechOne := by
  let hmem : ∀ p, leechOne.pairDist p ∈
      Finset.Icc 1 (targetN 1) := by
    intro p
    have hlt := p.left_lt_right
    have hl := p.left.isLt
    have hr := p.right.isLt
    omega
  refine ⟨hmem, ?_⟩
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨?_, by decide⟩
  intro p q hpq
  have hlt := p.left_lt_right
  have hl := p.left.isLt
  have hr := p.right.isLt
  omega

private def oldEmbedding12 : leechOne.graph ↪g leechTwo.graph where
  toFun := fun x => ⟨x, by omega⟩
  inj' := by
    intro x y hxy
    exact Fin.ext (congrArg (fun z : Fin 2 => z.val) hxy)
  map_rel_iff' := by
    intro x y
    fin_cases x
    all_goals fin_cases y
    all_goals simp [leechOne, leechTwo, graphOne, graphTwo]

private def oldEmbedding23 : leechTwo.graph ↪g leechThree.graph where
  toFun := fun x => ⟨x, by omega⟩
  inj' := by
    intro x y hxy
    exact Fin.ext (congrArg (fun z : Fin 3 => z.val) hxy)
  map_rel_iff' := by
    intro x y
    fin_cases x <;> fin_cases y <;>
      simp [leechTwo, leechThree, graphTwo, graphThree,
        SimpleGraph.edge_adj]

private def oldEmbedding34 : leechThree.graph ↪g leechFour.graph where
  toFun := fun x => ⟨x, by omega⟩
  inj' := by
    intro x y hxy
    exact Fin.ext (congrArg (fun z : Fin 4 => z.val) hxy)
  map_rel_iff' := by
    intro x y
    fin_cases x <;> fin_cases y <;>
      simp [leechThree, leechFour, graphThree, graphFour,
        SimpleGraph.edge_adj]

/-- The convention-dependent vacuous 1→2 leaf operation.  The unique old
vertex is the port and the fresh last vertex is attached at weight one. -/
def literalStep12 : LiteralOneLeafAttachment leechOne leechTwo where
  oldEmbedding := oldEmbedding12
  leaf := 1
  leaf_not_old := by
    intro x h
    have hv := congrArg Fin.val h
    fin_cases x
    all_goals simp [oldEmbedding12] at hv
  vertex_cover := by
    intro z
    fin_cases z
    · exact Or.inr ⟨0, rfl⟩
    · exact Or.inl rfl
  port := 0
  edgeSet_eq := by
    change graphTwo.edgeSet =
      (Sym2.map (fun x => oldEmbedding12 x) '' graphOne.edgeSet) ∪
        ({s((1 : Fin 2), oldEmbedding12 0)} : Set (Sym2 (Fin 2)))
    rw [graphTwo_edgeSet, graphOne_edgeSet, Set.image_empty,
      Set.empty_union]
    change
      ({s((0 : Fin 2), (1 : Fin 2))} : Set (Sym2 (Fin 2))) =
        {s((1 : Fin 2), (0 : Fin 2))}
    rw [show s((1 : Fin 2), (0 : Fin 2)) =
      s((0 : Fin 2), (1 : Fin 2)) by exact Sym2.eq_swap]
  old_weight_eq := by
    intro e
    have hemem := e.2
    change e.1 ∈ graphOne.edgeSet at hemem
    simp at hemem

/-- The actual unchanged 2→3 leaf operation: the old edge has weight one,
the port is vertex one, and the fresh last vertex is attached at weight two.
-/
def literalStep23 : LiteralOneLeafAttachment leechTwo leechThree where
  oldEmbedding := oldEmbedding23
  leaf := 2
  leaf_not_old := by
    intro x h
    have hv := congrArg Fin.val h
    fin_cases x <;> simp [oldEmbedding23] at hv
  vertex_cover := by
    intro z
    fin_cases z
    · exact Or.inr ⟨0, rfl⟩
    · exact Or.inr ⟨1, rfl⟩
    · exact Or.inl rfl
  port := 1
  edgeSet_eq := by
    change graphThree.edgeSet =
      (Sym2.map (fun x => oldEmbedding23 x) '' graphTwo.edgeSet) ∪
        ({s((2 : Fin 3), oldEmbedding23 1)} : Set (Sym2 (Fin 3)))
    rw [graphThree_edgeSet, graphTwo_edgeSet, Set.image_singleton,
      Sym2.map_pair_eq]
    change
      ({s((0 : Fin 3), (1 : Fin 3)), s((1 : Fin 3), (2 : Fin 3))} :
        Set (Sym2 (Fin 3))) =
      {s((0 : Fin 3), (1 : Fin 3))} ∪
        {s((2 : Fin 3), (1 : Fin 3))}
    rw [show s((2 : Fin 3), (1 : Fin 3)) = s((1 : Fin 3), (2 : Fin 3)) by
      exact Sym2.eq_swap]
    apply Set.ext
    intro e
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  old_weight_eq := by
    intro e
    have he : e.1 = s((0 : Fin 2), (1 : Fin 2)) := by
      have hemem := e.2
      change e.1 ∈ graphTwo.edgeSet at hemem
      rw [graphTwo_edgeSet] at hemem
      simpa using hemem
    change leechThree.weightOfPair
      (Sym2.map (fun x => oldEmbedding23 x) e.1) = 1
    rw [he, Sym2.map_pair_eq]
    exact leechThree_weightOfPair_01

/-- The actual unchanged 3→4 leaf operation: the old path has weights one
and two, its central vertex one is the port, and the fresh last vertex is
attached at weight four. -/
def literalStep34 : LiteralOneLeafAttachment leechThree leechFour where
  oldEmbedding := oldEmbedding34
  leaf := 3
  leaf_not_old := by
    intro x h
    have hv := congrArg Fin.val h
    fin_cases x <;> simp [oldEmbedding34] at hv
  vertex_cover := by
    intro z
    fin_cases z
    · exact Or.inr ⟨0, rfl⟩
    · exact Or.inr ⟨1, rfl⟩
    · exact Or.inr ⟨2, rfl⟩
    · exact Or.inl rfl
  port := 1
  edgeSet_eq := by
    change graphFour.edgeSet =
      (Sym2.map (fun x => oldEmbedding34 x) '' graphThree.edgeSet) ∪
        ({s((3 : Fin 4), oldEmbedding34 1)} : Set (Sym2 (Fin 4)))
    rw [graphFour_edgeSet, graphThree_edgeSet, Set.image_insert_eq,
      Set.image_singleton, Sym2.map_pair_eq, Sym2.map_pair_eq]
    change
      ({s((0 : Fin 4), (1 : Fin 4)), s((1 : Fin 4), (2 : Fin 4)),
        s((1 : Fin 4), (3 : Fin 4))} : Set (Sym2 (Fin 4))) =
      {s((0 : Fin 4), (1 : Fin 4)), s((1 : Fin 4), (2 : Fin 4))} ∪
        {s((3 : Fin 4), (1 : Fin 4))}
    rw [show s((3 : Fin 4), (1 : Fin 4)) = s((1 : Fin 4), (3 : Fin 4)) by
      exact Sym2.eq_swap]
    apply Set.ext
    intro e
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union,
      or_assoc]
  old_weight_eq := by
    intro e
    have he : e.1 = s((0 : Fin 3), (1 : Fin 3)) ∨
        e.1 = s((1 : Fin 3), (2 : Fin 3)) := by
      have hemem := e.2
      change e.1 ∈ graphThree.edgeSet at hemem
      rw [graphThree_edgeSet] at hemem
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hemem
    rcases he with he | he
    · change leechFour.weightOfPair
        (Sym2.map (fun x => oldEmbedding34 x) e.1) =
          (if e.1 = s((0 : Fin 3), (1 : Fin 3)) then 1 else 2)
      rw [he, Sym2.map_pair_eq]
      simp [oldEmbedding34]
    · change leechFour.weightOfPair
        (Sym2.map (fun x => oldEmbedding34 x) e.1) =
          (if e.1 = s((0 : Fin 3), (1 : Fin 3)) then 1 else 2)
      rw [he, Sym2.map_pair_eq]
      simp [oldEmbedding34,
        show s((1 : Fin 3), (2 : Fin 3)) ≠
          s((0 : Fin 3), (1 : Fin 3)) by decide]

/-- The retained order-at-least-four obstruction, lifted to the existential
paper-facing notion of a successful literal step. -/
theorem no_successfulLiteralOneLeafStep_of_four_le
    {m : ℕ} (hm : 4 ≤ m) :
    ¬ HasSuccessfulLiteralOneLeafStep m := by
  rintro ⟨T, U, L, hT, hU⟩
  exact OperationAdapters.LiteralOneLeafAttachment.no_literalOneLeafAttachment_of_four_le
    hT hU hm L

/-- Necessity half of the corrected main boundary.  Among admitted base
orders `m ≥ 2`, any actual successful literal unchanged one-leaf extension
has base order two or three. -/
theorem successful_literal_base_eq_two_or_three
    {m : ℕ} (hm : 2 ≤ m)
    {T : PosIntTree m} {U : PosIntTree (m + 1)}
    (L : LiteralOneLeafAttachment T U)
    (hT : IsLeech T) (hU : IsLeech U) :
    m = 2 ∨ m = 3 := by
  have hnot4 : ¬ 4 ≤ m := by
    intro hm4
    exact OperationAdapters.LiteralOneLeafAttachment.no_literalOneLeafAttachment_of_four_le
      hT hU hm4 L
  omega

/-- Necessity half under the convention that the vacuous order-one Leech
tree is admitted.  The order-one case is kept explicit rather than silently
folded into the publication theorem for `m ≥ 2`. -/
theorem successful_literal_base_eq_one_two_or_three
    {m : ℕ} (hm : 1 ≤ m)
    {T : PosIntTree m} {U : PosIntTree (m + 1)}
    (L : LiteralOneLeafAttachment T U)
    (hT : IsLeech T) (hU : IsLeech U) :
    m = 1 ∨ m = 2 ∨ m = 3 := by
  have hnot4 : ¬ 4 ≤ m := by
    intro hm4
    exact OperationAdapters.LiteralOneLeafAttachment.no_literalOneLeafAttachment_of_four_le
      hT hU hm4 L
  omega

/-- Closed paper-facing witness for the literal unchanged 2→3 step. -/
theorem hasSuccessfulLiteralOneLeafStep_two :
    HasSuccessfulLiteralOneLeafStep 2 :=
  ⟨leechTwo, leechThree, literalStep23,
    leechTwo_isLeech, leechThree_isLeech⟩

/-- Closed convention endpoint for the vacuous-spectrum literal 1→2 step.
-/
theorem hasSuccessfulLiteralOneLeafStep_one :
    HasSuccessfulLiteralOneLeafStep 1 :=
  ⟨leechOne, leechTwo, literalStep12,
    leechOne_isLeech, leechTwo_isLeech⟩

/-- Closed paper-facing witness for the literal unchanged 3→4 step. -/
theorem hasSuccessfulLiteralOneLeafStep_three :
    HasSuccessfulLiteralOneLeafStep 3 :=
  ⟨leechThree, leechFour, literalStep34,
    leechThree_isLeech, leechFour_isLeech⟩

/-- Full corrected boundary at the publication convention `m ≥ 2`: literal
unchanged one-leaf Leech-to-Leech extensions exist exactly for 2→3 and 3→4.
-/
theorem hasSuccessfulLiteralOneLeafStep_iff_of_two_le
    {m : ℕ} (hm : 2 ≤ m) :
    HasSuccessfulLiteralOneLeafStep m ↔ m = 2 ∨ m = 3 := by
  constructor
  · rintro ⟨T, U, L, hT, hU⟩
    exact successful_literal_base_eq_two_or_three hm L hT hU
  · rintro (rfl | rfl)
    · exact hasSuccessfulLiteralOneLeafStep_two
    · exact hasSuccessfulLiteralOneLeafStep_three

/-- Full boundary under the convention admitting the vacuous order-one
Leech tree.  This is kept separate from the main `m ≥ 2` publication result.
-/
theorem hasSuccessfulLiteralOneLeafStep_iff_of_one_le
    {m : ℕ} (hm : 1 ≤ m) :
    HasSuccessfulLiteralOneLeafStep m ↔
      m = 1 ∨ m = 2 ∨ m = 3 := by
  constructor
  · rintro ⟨T, U, L, hT, hU⟩
    exact successful_literal_base_eq_one_two_or_three hm L hT hU
  · rintro (rfl | rfl | rfl)
    · exact hasSuccessfulLiteralOneLeafStep_one
    · exact hasSuccessfulLiteralOneLeafStep_two
    · exact hasSuccessfulLiteralOneLeafStep_three

end LeechTrees.SmallLeafBoundary
