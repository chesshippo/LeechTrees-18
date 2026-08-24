import Mathlib
import LeechTrees.CombinatorialCore

/-!
# LeechTrees: weighted-tree foundations and claims T1--T5

This module gives an indexed, graph-level model of a positive integral
weighted tree.  Pair distances are indexed by unordered distinct vertex
pairs (represented by their increasing orientation), and `IsLeech` is a
bijection with the full target interval rather than an equality of supports.
-/

open scoped BigOperators

namespace LeechTrees.Foundation

/-- An unordered pair of distinct vertices, represented by its unique
increasing orientation. -/
abbrev VertexPair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

instance (n : ℕ) : Fintype (VertexPair n) := inferInstance
instance (n : ℕ) : DecidableEq (VertexPair n) := inferInstance

namespace VertexPair

def left {n : ℕ} (p : VertexPair n) : Fin n := p.1.1
def right {n : ℕ} (p : VertexPair n) : Fin n := p.1.2

@[simp] theorem left_lt_right {n : ℕ} (p : VertexPair n) : p.left < p.right := p.2

@[ext] theorem ext {n : ℕ} {p q : VertexPair n}
    (hleft : p.left = q.left) (hright : p.right = q.right) : p = q := by
  apply Subtype.ext
  exact Prod.ext hleft hright

/-- The canonical increasing representative of two distinct named vertices. -/
def ofDistinct {n : ℕ} (u v : Fin n) (huv : u ≠ v) : VertexPair n :=
  if h : u < v then ⟨(u, v), h⟩
  else ⟨(v, u), lt_of_le_of_ne (le_of_not_gt h) huv.symm⟩

theorem ofDistinct_eq_of_lt {n : ℕ} {u v : Fin n} (huv : u ≠ v) (h : u < v) :
    ofDistinct u v huv = ⟨(u, v), h⟩ := by
  simp [ofDistinct, h]

end VertexPair

/-- Unordered pairs whose endpoints lie in opposite classes of a predicate. -/
def OppositePair {n : ℕ} (P : Fin n → Prop) :=
  {p : VertexPair n //
    (P p.left ∧ ¬P p.right) ∨ (¬P p.left ∧ P p.right)}

/-- Opposite unordered pairs are canonically indexed by the Cartesian product
of the two predicate classes. -/
noncomputable def oppositePairEquiv {n : ℕ} (P : Fin n → Prop) :
    ({u : Fin n // P u} × {v : Fin n // ¬P v}) ≃ OppositePair P := by
  classical
  let toFun : ({u : Fin n // P u} × {v : Fin n // ¬P v}) → OppositePair P := fun z =>
    ⟨VertexPair.ofDistinct z.1 z.2 (fun h => z.2.2 (h ▸ z.1.2)), by
      by_cases hlt : z.1.1 < z.2.1
      · left
        simpa [VertexPair.ofDistinct, hlt, VertexPair.left, VertexPair.right]
          using And.intro z.1.2 z.2.2
      · right
        simpa [VertexPair.ofDistinct, hlt, VertexPair.left, VertexPair.right]
          using And.intro z.2.2 z.1.2⟩
  let invFun : OppositePair P → ({u : Fin n // P u} × {v : Fin n // ¬P v}) := fun q =>
    if h : P q.1.left then
      (⟨q.1.left, h⟩, ⟨q.1.right, fun hr => by
        rcases q.2 with hq | hq
        · exact hq.2 hr
        · exact hq.1 h⟩)
    else
      (⟨q.1.right, by
        rcases q.2 with hq | hq
        · exact (h hq.1).elim
        · exact hq.2⟩, ⟨q.1.left, h⟩)
  exact
    { toFun := toFun
      invFun := invFun
      left_inv := by
        intro z
        rcases z with ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
        by_cases hlt : u < v
        · simp [toFun, invFun, VertexPair.ofDistinct, hlt, hu,
            VertexPair.left, VertexPair.right]
        · have hvu : v < u := lt_of_le_of_ne (le_of_not_gt hlt) (fun h => hv (h ▸ hu))
          simp [toFun, invFun, VertexPair.ofDistinct, hlt, hv,
            VertexPair.left, VertexPair.right]
      right_inv := by
        intro q
        rcases q with ⟨p, hp⟩
        by_cases hP : P p.left
        · have hnP : ¬P p.right := by
            rcases hp with hp | hp
            · exact hp.2
            · exact (hp.1 hP).elim
          dsimp only [invFun]
          rw [dif_pos hP]
          dsimp only [toFun]
          apply Subtype.ext
          have hne : p.left ≠ p.right := ne_of_lt p.left_lt_right
          change VertexPair.ofDistinct p.left p.right hne = p
          unfold VertexPair.ofDistinct
          rw [dif_pos p.left_lt_right]
          apply VertexPair.ext <;> rfl
        · have hPr : P p.right := by
            rcases hp with hp | hp
            · exact (hP hp.1).elim
            · exact hp.2
          dsimp only [invFun]
          rw [dif_neg hP]
          dsimp only [toFun]
          apply Subtype.ext
          have hne : p.right ≠ p.left := (ne_of_lt p.left_lt_right).symm
          change VertexPair.ofDistinct p.right p.left hne = p
          have hnot : ¬p.right < p.left := not_lt_of_ge p.left_lt_right.le
          unfold VertexPair.ofDistinct
          rw [dif_neg hnot]
          apply VertexPair.ext <;> rfl }

/-- A finite simple tree on the named vertices `Fin n`, with a positive
natural weight on every actual graph edge. -/
structure PosIntTree (n : ℕ) where
  graph : SimpleGraph (Fin n)
  isTree : graph.IsTree
  weight : graph.edgeSet → ℕ
  weight_pos : ∀ e, 0 < weight e

namespace PosIntTree

variable {n : ℕ} (T : PosIntTree n)

/-- The canonical physical-edge type.  Because the underlying graph is
simple, an edge has no duplicate or parallel representation. -/
abbrev Edge := T.graph.edgeSet

noncomputable instance : Fintype T.Edge := Fintype.ofFinite _
instance : DecidableEq T.Edge := inferInstance

noncomputable def path (u v : Fin n) : T.graph.Path u v := by
  let w := Classical.choose (T.isTree.existsUnique_path u v)
  exact ⟨w, (Classical.choose_spec (T.isTree.existsUnique_path u v)).1⟩

theorem path_unique {u v : Fin n} (p : T.graph.Path u v) : p = T.path u v :=
  T.isTree.IsAcyclic.path_unique p (T.path u v)

noncomputable def weightOfPair (e : Sym2 (Fin n)) : ℕ := by
  classical
  exact if h : e ∈ T.graph.edgeSet then T.weight ⟨e, h⟩ else 0

noncomputable def pathEdges (u v : Fin n) : Finset (Sym2 (Fin n)) :=
  (T.path u v).1.edges.toFinset

theorem pathEdges_subset_edgeSet (u v : Fin n) :
    ↑(T.pathEdges u v) ⊆ T.graph.edgeSet := by
  intro e he
  have he' : e ∈ (T.path u v).1.edges := by
    simpa [pathEdges] using he
  induction e using Sym2.ind with
  | _ x y =>
      exact (T.path u v).1.adj_of_mem_edges he'

theorem pathEdges_nodup (u v : Fin n) : (T.path u v).1.edges.Nodup := by
  exact (SimpleGraph.Walk.isTrail_def (T.path u v).1).mp (T.path u v).2.isTrail

def edgeLeft (e : T.Edge) : Fin n := e.1.inf
def edgeRight (e : T.Edge) : Fin n := e.1.sup

theorem edgeLeft_le_edgeRight (e : T.Edge) : T.edgeLeft e ≤ T.edgeRight e :=
  Sym2.inf_le_sup e.1

theorem edgeLeft_lt_edgeRight (e : T.Edge) : T.edgeLeft e < T.edgeRight e := by
  apply lt_of_le_of_ne (T.edgeLeft_le_edgeRight e)
  intro h
  have hdiag : e.1.IsDiag := by
    rw [(Sym2.sortEquiv.symm_apply_apply e.1).symm]
    exact Sym2.mk_isDiag_iff.mpr h
  exact (T.graph.not_isDiag_of_mem_edgeSet e.2) hdiag

def edgePair (e : T.Edge) : VertexPair n :=
  ⟨(T.edgeLeft e, T.edgeRight e), T.edgeLeft_lt_edgeRight e⟩

@[simp] theorem edgePair_left (e : T.Edge) : (T.edgePair e).left = T.edgeLeft e := rfl
@[simp] theorem edgePair_right (e : T.Edge) : (T.edgePair e).right = T.edgeRight e := rfl

theorem edge_eq_mk_endpoints (e : T.Edge) :
    e.1 = s(T.edgeLeft e, T.edgeRight e) := by
  exact (Sym2.sortEquiv.symm_apply_apply e.1).symm

theorem edge_adj (e : T.Edge) : T.graph.Adj (T.edgeLeft e) (T.edgeRight e) := by
  rw [← SimpleGraph.mem_edgeSet, ← T.edge_eq_mk_endpoints e]
  exact e.2

theorem pathEdges_edge (e : T.Edge) :
    T.pathEdges (T.edgeLeft e) (T.edgeRight e) = {e.1} := by
  have hp : SimpleGraph.Path.singleton (T.edge_adj e) =
      T.path (T.edgeLeft e) (T.edgeRight e) := T.path_unique _
  rw [pathEdges, ← hp]
  simp [SimpleGraph.Path.singleton, T.edge_eq_mk_endpoints e]

@[simp] theorem weightOfPair_edge (e : T.Edge) : T.weightOfPair e.1 = T.weight e := by
  classical
  simp [weightOfPair, e.2]

def edgeOfPathMem {u v : Fin n} (e : Sym2 (Fin n))
    (he : e ∈ T.pathEdges u v) : T.Edge :=
  ⟨e, T.pathEdges_subset_edgeSet u v he⟩

@[simp] theorem edgeOfPathMem_val {u v : Fin n} (e : Sym2 (Fin n))
    (he : e ∈ T.pathEdges u v) : (T.edgeOfPathMem e he).1 = e := rfl

@[simp] theorem weight_edgeOfPathMem {u v : Fin n} (e : Sym2 (Fin n))
    (he : e ∈ T.pathEdges u v) :
    T.weight (T.edgeOfPathMem e he) = T.weightOfPair e := by
  rw [← T.weightOfPair_edge (T.edgeOfPathMem e he)]
  rfl

noncomputable def dist (u v : Fin n) : ℕ :=
  ∑ e ∈ pathEdges T u v, weightOfPair T e

noncomputable def pairDist (p : VertexPair n) : ℕ := dist T p.left p.right

@[simp] theorem edgePair_dist (e : T.Edge) : T.pairDist (T.edgePair e) = T.weight e := by
  classical
  simp [pairDist, dist, T.pathEdges_edge e]

theorem weightOfPair_pos_of_mem_pathEdges {u v : Fin n} {e : Sym2 (Fin n)}
    (he : e ∈ T.pathEdges u v) : 0 < T.weightOfPair e := by
  rw [← T.weight_edgeOfPathMem e he]
  exact T.weight_pos _

theorem weightOfPair_le_dist_of_mem {u v : Fin n} {e : Sym2 (Fin n)}
    (he : e ∈ T.pathEdges u v) : T.weightOfPair e ≤ T.dist u v := by
  classical
  unfold dist
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) he

theorem pathEdges_nonempty_of_dist_pos {u v : Fin n} (h : 0 < T.dist u v) :
    (T.pathEdges u v).Nonempty := by
  by_contra hempty
  have hs : T.pathEdges u v = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
  rw [dist, hs] at h
  simp at h

private theorem finsetSum_toFinset_eq_listSum
    {α : Type*} [DecidableEq α] (f : α → ℕ) (l : List α) (hl : l.Nodup) :
    (∑ x ∈ l.toFinset, f x) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.nodup_cons] at hl
      simp [hl.1, ih hl.2]

noncomputable def walkWeight {u v : Fin n} (p : T.graph.Walk u v) : ℕ :=
  (p.edges.map T.weightOfPair).sum

theorem dist_eq_walkWeight_path (u v : Fin n) :
    T.dist u v = T.walkWeight (T.path u v).1 := by
  classical
  unfold dist pathEdges walkWeight
  exact finsetSum_toFinset_eq_listSum _ _ (T.pathEdges_nodup u v)

theorem path_walkWeight_eq_dist {u v : Fin n} (p : T.graph.Path u v) :
    T.walkWeight p.1 = T.dist u v := by
  rw [T.path_unique p]
  exact (T.dist_eq_walkWeight_path u v).symm

end PosIntTree

/-- The target upper rank for a tree of order `n`. -/
def targetN (n : ℕ) : ℕ := Nat.choose n 2

/-- Exact Leech spectrum: the indexed map from unordered distinct vertex
pairs to positive ranks is a bijection onto `1, ..., choose n 2`. -/
structure IsLeech {n : ℕ} (T : PosIntTree n) : Prop where
  pairDist_mem : ∀ p, T.pairDist p ∈ Finset.Icc 1 (targetN n)
  bijective : Function.Bijective
    (fun p : VertexPair n =>
      (⟨T.pairDist p, pairDist_mem p⟩ : {k // k ∈ Finset.Icc 1 (targetN n)}))

namespace IsLeech

variable {n : ℕ} {T : PosIntTree n} (hL : IsLeech T)

include hL

theorem pairDist_injective : Function.Injective T.pairDist := by
  intro p q hpq
  apply hL.2.1
  exact Subtype.ext hpq

theorem target_existsUnique (k : ℕ) (hk : k ∈ Finset.Icc 1 (targetN n)) :
    ∃! p : VertexPair n, T.pairDist p = k := by
  obtain ⟨p, hp⟩ := hL.2.2 ⟨k, hk⟩
  refine ⟨p, congrArg Subtype.val hp, ?_⟩
  intro q hq
  exact hL.pairDist_injective (hq.trans (congrArg Subtype.val hp).symm)

theorem pairDist_pos (p : VertexPair n) : 0 < T.pairDist p := by
  exact (Finset.mem_Icc.mp (hL.1 p)).1

theorem pairDist_le_target (p : VertexPair n) : T.pairDist p ≤ targetN n := by
  exact (Finset.mem_Icc.mp (hL.1 p)).2

end IsLeech

/-! ## T1: physical weights and the forced weights one and two -/

section T1

variable {n : ℕ} {T : PosIntTree n}

/-- Global pair-distance injectivity forces all physical edge weights to be
distinct. -/
theorem t1_edge_weight_injective (hL : IsLeech T) : Function.Injective T.weight := by
  intro e f hw
  have hp : T.edgePair e = T.edgePair f := hL.pairDist_injective <| by
    simpa using hw
  apply Subtype.ext
  rw [T.edge_eq_mk_endpoints e, T.edge_eq_mk_endpoints f]
  have hl : T.edgeLeft e = T.edgeLeft f := by
    simpa using congrArg VertexPair.left hp
  have hr : T.edgeRight e = T.edgeRight f := by
    simpa using congrArg VertexPair.right hp
  rw [hl, hr]

/-- Every physical edge weight is one of the target ranks. -/
theorem t1_edge_weight_mem_target (hL : IsLeech T) (e : T.Edge) :
    T.weight e ∈ Finset.Icc 1 (targetN n) := by
  simpa using hL.1 (T.edgePair e)

private theorem target_one_mem (hn : 2 ≤ n) :
    1 ∈ Finset.Icc 1 (targetN n) := by
  rw [Finset.mem_Icc]
  constructor
  · omega
  · have hc : Nat.choose 2 2 ≤ Nat.choose n 2 := Nat.choose_le_choose 2 hn
    simpa [targetN] using hc

private theorem target_two_mem (hn : 3 ≤ n) :
    2 ∈ Finset.Icc 1 (targetN n) := by
  rw [Finset.mem_Icc]
  constructor
  · omega
  · have hc : Nat.choose 3 2 ≤ Nat.choose n 2 := Nat.choose_le_choose 2 hn
    norm_num [targetN] at hc ⊢
    omega

private theorem exists_edge_of_pairDist_eq_one (hL : IsLeech T)
    (p : VertexPair n) (hp : T.pairDist p = 1) :
    ∃ e : T.Edge, T.weight e = 1 := by
  have hdpos : 0 < T.dist p.left p.right := by
    simpa [PosIntTree.pairDist] using hL.pairDist_pos p
  obtain ⟨x, hx⟩ := T.pathEdges_nonempty_of_dist_pos hdpos
  let e : T.Edge := T.edgeOfPathMem x hx
  refine ⟨e, ?_⟩
  have hpos := T.weightOfPair_pos_of_mem_pathEdges hx
  have hle := T.weightOfPair_le_dist_of_mem hx
  have hdist : T.dist p.left p.right = 1 := by simpa [PosIntTree.pairDist] using hp
  have hxone : T.weightOfPair x = 1 := by omega
  simpa [e] using hxone

private theorem exists_edge_of_pairDist_eq_two (hL : IsLeech T)
    (p : VertexPair n) (hp : T.pairDist p = 2) :
    ∃ e : T.Edge, T.weight e = 2 := by
  classical
  have hdpos : 0 < T.dist p.left p.right := by
    simpa [PosIntTree.pairDist] using hL.pairDist_pos p
  obtain ⟨x, hx⟩ := T.pathEdges_nonempty_of_dist_pos hdpos
  have hdist : T.dist p.left p.right = 2 := by simpa [PosIntTree.pairDist] using hp
  have hxpos := T.weightOfPair_pos_of_mem_pathEdges hx
  have hxle := T.weightOfPair_le_dist_of_mem hx
  have hx12 : T.weightOfPair x = 1 ∨ T.weightOfPair x = 2 := by omega
  rcases hx12 with hxone | hxtwo
  · exfalso
    by_cases hsingle : T.pathEdges p.left p.right = {x}
    · have : T.dist p.left p.right = T.weightOfPair x := by
        simp [PosIntTree.dist, hsingle]
      omega
    · have hyex : ∃ y ∈ T.pathEdges p.left p.right, y ≠ x := by
        by_contra hno
        push_neg at hno
        apply hsingle
        ext y
        constructor
        · intro hy
          have := hno y hy
          simp [this]
        · intro hy
          have hyx' : y = x := Finset.mem_singleton.mp hy
          simpa [hyx'] using hx
      obtain ⟨y, hy, hyx⟩ := hyex
      have hypos := T.weightOfPair_pos_of_mem_pathEdges hy
      have hyle := T.weightOfPair_le_dist_of_mem hy
      have hweights_ne : T.weightOfPair y ≠ T.weightOfPair x := by
        intro heq
        have hedges : T.edgeOfPathMem y hy = T.edgeOfPathMem x hx :=
          t1_edge_weight_injective hL <| by simpa using heq
        exact hyx (congrArg Subtype.val hedges)
      have hytwo : T.weightOfPair y = 2 := by omega
      have hpair_subset : {x, y} ⊆ T.pathEdges p.left p.right := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hx
        · exact hy
      have hpair_le :
          (∑ z ∈ ({x, y} : Finset (Sym2 (Fin n))), T.weightOfPair z) ≤
            T.dist p.left p.right := by
        unfold PosIntTree.dist
        exact Finset.sum_le_sum_of_subset_of_nonneg hpair_subset (fun _ _ _ => Nat.zero_le _)
      rw [Finset.sum_pair hyx.symm, hxone, hytwo, hdist] at hpair_le
      omega
  · exact ⟨T.edgeOfPathMem x hx, by simpa using hxtwo⟩

/-- The unique physical edge of weight one.  The order hypothesis is necessary:
an order-one exact spectrum has no edge. -/
theorem t1_existsUnique_weight_one (hL : IsLeech T) (hn : 2 ≤ n) :
    ∃! e : T.Edge, T.weight e = 1 := by
  obtain ⟨p, hp⟩ := hL.target_existsUnique 1 (target_one_mem hn)
  obtain ⟨e, he⟩ := exists_edge_of_pairDist_eq_one hL p hp.1
  refine ⟨e, he, ?_⟩
  intro f hf
  exact t1_edge_weight_injective hL (hf.trans he.symm)

/-- The unique physical edge of weight two.  The order-three lower bound is
the sharp small-order repair to the informal proposition. -/
theorem t1_existsUnique_weight_two (hL : IsLeech T) (hn : 3 ≤ n) :
    ∃! e : T.Edge, T.weight e = 2 := by
  obtain ⟨p, hp⟩ := hL.target_existsUnique 2 (target_two_mem hn)
  obtain ⟨e, he⟩ := exists_edge_of_pairDist_eq_two hL p hp.1
  refine ⟨e, he, ?_⟩
  intro f hf
  exact t1_edge_weight_injective hL (hf.trans he.symm)

/-- Claim-level T1 bundle, with its necessary `3 ≤ n` boundary explicit. -/
theorem T1_physical_weights_one_two (hL : IsLeech T) (hn : 3 ≤ n) :
    Function.Injective T.weight ∧
    (∀ e : T.Edge, T.weight e ∈ Finset.Icc 1 (targetN n)) ∧
    (∃! e : T.Edge, T.weight e = 1) ∧
    (∃! e : T.Edge, T.weight e = 2) := by
  exact ⟨t1_edge_weight_injective hL, t1_edge_weight_mem_target hL,
    t1_existsUnique_weight_one hL (by omega), t1_existsUnique_weight_two hL hn⟩

end T1

/-! ## T2: actual increasing-weight prefixes and forced MEX -/

section T2

variable {n : ℕ} (T : PosIntTree n)

namespace PosIntTree

/-- The actual proper prefix immediately before a chosen physical edge `e`:
all and only physical edges of strictly smaller actual weight. -/
noncomputable def exposedEdgesBefore (e : T.Edge) : Finset T.Edge := by
  classical
  exact Finset.univ.filter (fun f => T.weight f < T.weight e)

/-- The spanning forest made from the actual edges strictly lighter than `e`.
Isolated named vertices are retained because the vertex type is unchanged. -/
noncomputable def prefixForest (e : T.Edge) : SimpleGraph (Fin n) where
  Adj u v := T.graph.Adj u v ∧ T.weightOfPair s(u, v) < T.weight e
  symm := by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    simpa only [Sym2.eq_swap] using h.2
  loopless := by
    intro u h
    exact T.graph.loopless u h.1

theorem prefixForest_le (e : T.Edge) : T.prefixForest e ≤ T.graph := by
  intro u v h
  exact h.1

theorem prefixForest_isAcyclic (e : T.Edge) : (T.prefixForest e).IsAcyclic :=
  T.isTree.IsAcyclic.anti (T.prefixForest_le e)

/-- An indexed pair is internal to one component of the actual prefix forest. -/
def PrefixInternal (e : T.Edge) (p : VertexPair n) : Prop :=
  (T.prefixForest e).Reachable p.left p.right

theorem prefixInternal_iff_path_lighter (e : T.Edge) (p : VertexPair n) :
    T.PrefixInternal e p ↔
      ∀ f ∈ T.pathEdges p.left p.right, T.weightOfPair f < T.weight e := by
  classical
  constructor
  · intro hr
    obtain ⟨q, hq⟩ := hr.exists_isPath
    let qT : T.graph.Path p.left p.right :=
      ⟨q.mapLe (T.prefixForest_le e), hq.mapLe (T.prefixForest_le e)⟩
    have hcanon : qT = T.path p.left p.right := T.path_unique qT
    intro f hf
    have hfcanon : f ∈ (T.path p.left p.right).1.edges := by
      simpa [PosIntTree.pathEdges] using hf
    have hfqT : f ∈ qT.1.edges := by
      rw [hcanon]
      exact hfcanon
    have hfq : f ∈ q.edges := by
      simpa [qT] using hfqT
    induction f using Sym2.ind with
    | _ x y =>
        exact (q.adj_of_mem_edges hfq).2
  · intro hall
    let pth := T.path p.left p.right
    have hedge : ∀ f ∈ pth.1.edges, f ∈ (T.prefixForest e).edgeSet := by
      intro f hf
      have hffin : f ∈ T.pathEdges p.left p.right := by
        simpa [PosIntTree.pathEdges, pth] using hf
      induction f using Sym2.ind with
      | _ x y =>
          rw [SimpleGraph.mem_edgeSet]
          exact ⟨pth.1.adj_of_mem_edges hf, hall _ hffin⟩
    exact (pth.1.transfer (T.prefixForest e) hedge).reachable

/-- The finite set of all distances internal to any component of the actual
prefix forest.  Pair indices are filtered before taking the value image. -/
noncomputable def prefixInternalDistances (e : T.Edge) : Finset ℕ := by
  classical
  exact (Finset.univ.filter (T.PrefixInternal e)).image T.pairDist

private theorem mexWitness (D : Finset ℕ) :
    ∃ m : ℕ, 0 < m ∧ m ∉ D := by
  classical
  refine ⟨(∑ k ∈ D, k) + 1, by omega, ?_⟩
  intro hm
  have hle : (∑ k ∈ ({(∑ k ∈ D, k) + 1} : Finset ℕ), k) ≤ ∑ k ∈ D, k := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · simpa using hm
    · exact fun _ _ _ => Nat.zero_le _
  simp at hle

/-- Least strictly positive natural number absent from a finite distance set. -/
noncomputable def mexPos (D : Finset ℕ) : ℕ := Nat.find (mexWitness D)

theorem mexPos_pos (D : Finset ℕ) : 0 < mexPos D := (Nat.find_spec (mexWitness D)).1

theorem mexPos_not_mem (D : Finset ℕ) : mexPos D ∉ D :=
  (Nat.find_spec (mexWitness D)).2

theorem pos_lt_mexPos_mem (D : Finset ℕ) {k : ℕ} (hkpos : 0 < k)
    (hk : k < mexPos D) : k ∈ D := by
  by_contra hnot
  exact (Nat.find_min (mexWitness D) hk) ⟨hkpos, hnot⟩

theorem mem_exposedEdgesBefore_iff (e f : T.Edge) :
    f ∈ T.exposedEdgesBefore e ↔ T.weight f < T.weight e := by
  classical
  simp [exposedEdgesBefore]

theorem chosenEdge_not_exposedBefore (e : T.Edge) :
    e ∉ T.exposedEdgesBefore e := by
  simp [T.mem_exposedEdgesBefore_iff]

theorem least_unexposed_weight (e f : T.Edge)
    (hf : f ∉ T.exposedEdgesBefore e) : T.weight e ≤ T.weight f := by
  rw [T.mem_exposedEdgesBefore_iff, not_lt] at hf
  exact hf

/-- Forced-MEX for an actual proper initial segment in strict physical-weight
order.  The public statement derives both directions from the fixed target
tree: it does not assume that ranks below the MEX are themselves physical. -/
theorem t2_forced_mex (hL : IsLeech T) (e : T.Edge) :
    mexPos (T.prefixInternalDistances e) = T.weight e := by
  classical
  have hqpos : 0 < T.weight e := T.weight_pos e
  have hqnot : T.weight e ∉ T.prefixInternalDistances e := by
    intro hmem
    rw [prefixInternalDistances, Finset.mem_image] at hmem
    obtain ⟨p, hp, hpdist⟩ := hmem
    have hpinternal : T.PrefixInternal e p := by
      simpa using (Finset.mem_filter.mp hp).2
    have hpeq : p = T.edgePair e := hL.pairDist_injective <| by
      exact hpdist.trans (T.edgePair_dist e).symm
    subst p
    have hall := (T.prefixInternal_iff_path_lighter e (T.edgePair e)).1 hpinternal
    have hePath : e.1 ∈ T.pathEdges (T.edgeLeft e) (T.edgeRight e) := by
      rw [T.pathEdges_edge e]
      simp
    have hlt := hall e.1 hePath
    rw [T.weightOfPair_edge e] at hlt
    omega
  have hallBelow : ∀ {k : ℕ}, 0 < k → k < T.weight e →
      k ∈ T.prefixInternalDistances e := by
    intro k hkpos hklt
    have hqtarget : T.weight e ≤ targetN n :=
      (Finset.mem_Icc.mp (t1_edge_weight_mem_target hL e)).2
    have hkTarget : k ∈ Finset.Icc 1 (targetN n) := by
      rw [Finset.mem_Icc]
      omega
    obtain ⟨p, hp⟩ := hL.target_existsUnique k hkTarget
    have hpinternal : T.PrefixInternal e p :=
      (T.prefixInternal_iff_path_lighter e p).2 <| by
        intro f hf
        have hle := T.weightOfPair_le_dist_of_mem hf
        have hdist : T.dist p.left p.right = k := by
          simpa [PosIntTree.pairDist] using hp.1
        omega
    rw [prefixInternalDistances, Finset.mem_image]
    exact ⟨p, by simp [hpinternal], hp.1⟩
  apply Nat.le_antisymm
  · by_contra h
    have hlt : T.weight e < mexPos (T.prefixInternalDistances e) := by omega
    exact hqnot (pos_lt_mexPos_mem (T.prefixInternalDistances e) hqpos hlt)
  · by_contra h
    have hlt : mexPos (T.prefixInternalDistances e) < T.weight e := by omega
    exact mexPos_not_mem (T.prefixInternalDistances e)
      (hallBelow (mexPos_pos (T.prefixInternalDistances e)) hlt)

/-- Empty-prefix regression: when the chosen actual edge has weight one, the
positive MEX is one (never the zero-based MEX value zero). -/
theorem t2_empty_prefix_mex_one (hL : IsLeech T) (e : T.Edge)
    (he : T.weight e = 1) :
    mexPos (T.prefixInternalDistances e) = 1 := by
  rw [T.t2_forced_mex hL e, he]

/-- Claim-level forced-MEX/least-unexposed bundle for the actual prefix before
`e`. -/
theorem T2_forced_mex_initial_segment (hL : IsLeech T) (e : T.Edge) :
    e ∉ T.exposedEdgesBefore e ∧
    (∀ f : T.Edge, f ∉ T.exposedEdgesBefore e → T.weight e ≤ T.weight f) ∧
    (T.prefixForest e).IsAcyclic ∧
    mexPos (T.prefixInternalDistances e) = T.weight e := by
  exact ⟨T.chosenEdge_not_exposedBefore e, T.least_unexposed_weight e,
    T.prefixForest_isAcyclic e, T.t2_forced_mex hL e⟩

/-! The actual one-edge cut.  These declarations are shared by T2, T4, and
T5. -/

noncomputable def cutGraph (e : T.Edge) : SimpleGraph (Fin n) :=
  T.graph.deleteEdges {e.1}

theorem edge_isBridge (e : T.Edge) : T.graph.IsBridge e.1 := by
  exact (SimpleGraph.isAcyclic_iff_forall_edge_isBridge.mp T.isTree.IsAcyclic) e.2

theorem cut_endpoints_not_reachable (e : T.Edge) :
    ¬(T.cutGraph e).Reachable (T.edgeLeft e) (T.edgeRight e) := by
  have hb := T.edge_isBridge e
  rw [T.edge_eq_mk_endpoints e, SimpleGraph.isBridge_iff] at hb
  simpa only [cutGraph, SimpleGraph.deleteEdges, T.edge_eq_mk_endpoints e] using hb.2

/-- In a tree, two vertices remain connected after deleting `e` exactly when
their unique path avoids `e`. -/
theorem cut_reachable_iff_not_mem_pathEdges (e : T.Edge) (u v : Fin n) :
    (T.cutGraph e).Reachable u v ↔ e.1 ∉ T.pathEdges u v := by
  classical
  have hreach : (T.cutGraph e).Reachable u v ↔
      ∃ w : T.graph.Walk u v, e.1 ∉ w.edges := by
    simpa only [cutGraph, SimpleGraph.deleteEdges, T.edge_eq_mk_endpoints e] using
      (SimpleGraph.reachable_delete_edges_iff_exists_walk
        (G := T.graph) (v := T.edgeLeft e) (w := T.edgeRight e)
        (v' := u) (w' := v))
  rw [hreach]
  constructor
  · rintro ⟨w, hw⟩
    have hto : e.1 ∉ w.toPath.1.edges := by
      intro he
      exact hw (w.edges_toPath_subset he)
    have huniq : w.toPath = T.path u v := T.path_unique w.toPath
    intro hefin
    have hepath : e.1 ∈ (T.path u v).1.edges := by
      simpa [PosIntTree.pathEdges] using hefin
    rw [← huniq] at hepath
    exact hto hepath
  · intro havoid
    refine ⟨(T.path u v).1, ?_⟩
    intro he
    apply havoid
    simpa [PosIntTree.pathEdges] using he

def LeftCut (e : T.Edge) (u : Fin n) : Prop :=
  (T.cutGraph e).Reachable u (T.edgeLeft e)

def RightCut (e : T.Edge) (u : Fin n) : Prop :=
  (T.cutGraph e).Reachable u (T.edgeRight e)

theorem edgeLeft_mem_LeftCut (e : T.Edge) : T.LeftCut e (T.edgeLeft e) := by
  unfold LeftCut
  exact ⟨SimpleGraph.Walk.nil⟩

theorem edgeRight_mem_RightCut (e : T.Edge) : T.RightCut e (T.edgeRight e) := by
  unfold RightCut
  exact ⟨SimpleGraph.Walk.nil⟩

theorem LeftCut_disjoint_RightCut (e : T.Edge) (u : Fin n) :
    ¬(T.LeftCut e u ∧ T.RightCut e u) := by
  rintro ⟨hl, hr⟩
  exact T.cut_endpoints_not_reachable e (hl.symm.trans hr)

theorem cut_cover (e : T.Edge) (u : Fin n) : T.LeftCut e u ∨ T.RightCut e u := by
  classical
  by_cases hl : T.LeftCut e u
  · exact Or.inl hl
  · right
    have hefin : e.1 ∈ T.pathEdges u (T.edgeLeft e) := by
      by_contra hnot
      exact hl ((T.cut_reachable_iff_not_mem_pathEdges e u (T.edgeLeft e)).2 hnot)
    let p := T.path u (T.edgeLeft e)
    have heelist : e.1 ∈ p.1.edges := by
      simpa [PosIntTree.pathEdges, p] using hefin
    have hbmem : T.edgeRight e ∈ p.1.support := by
      rw [T.edge_eq_mk_endpoints e] at heelist
      exact p.1.snd_mem_support_of_mem_edges heelist
    let before := p.1.takeUntil (T.edgeRight e) hbmem
    let after := p.1.dropUntil (T.edgeRight e) hbmem
    have hafterPath : after.IsPath := p.2.dropUntil hbmem
    have hafterEq :
        (⟨after, hafterPath⟩ : T.graph.Path (T.edgeRight e) (T.edgeLeft e)) =
          SimpleGraph.Path.singleton (T.edge_adj e).symm :=
      T.isTree.IsAcyclic.path_unique _ _
    have heafter : e.1 ∈ after.edges := by
      rw [congrArg (fun q => q.1.edges) hafterEq]
      simp [SimpleGraph.Path.singleton, T.edge_eq_mk_endpoints e]
    have hbeforeAvoid : e.1 ∉ before.edges := by
      have hnodup := T.pathEdges_nodup u (T.edgeLeft e)
      have hsplit := p.1.take_spec hbmem
      rw [← hsplit, SimpleGraph.Walk.edges_append, List.nodup_append] at hnodup
      exact fun he => (hnodup.2.2 e.1 he e.1 heafter) rfl
    unfold RightCut
    rw [T.cut_reachable_iff_not_mem_pathEdges e u (T.edgeRight e)]
    intro hecanonical
    have hbeforePath : before.IsPath := p.2.takeUntil hbmem
    have hbeforeEq :
        (⟨before, hbeforePath⟩ : T.graph.Path u (T.edgeRight e)) =
          T.path u (T.edgeRight e) := T.path_unique _
    apply hbeforeAvoid
    rw [congrArg (fun q => q.1.edges) hbeforeEq]
    simpa [PosIntTree.pathEdges] using hecanonical

theorem leftCut_iff_not_rightCut (e : T.Edge) (u : Fin n) :
    T.LeftCut e u ↔ ¬T.RightCut e u := by
  constructor
  · intro hl hr
    exact T.LeftCut_disjoint_RightCut e u ⟨hl, hr⟩
  · intro hnr
    rcases T.cut_cover e u with hl | hr
    · exact hl
    · exact (hnr hr).elim

theorem rightCut_iff_not_leftCut (e : T.Edge) (u : Fin n) :
    T.RightCut e u ↔ ¬T.LeftCut e u := by
  rw [T.leftCut_iff_not_rightCut e u]
  tauto

theorem cutGraph_le (e : T.Edge) : T.cutGraph e ≤ T.graph := by
  exact SimpleGraph.deleteEdges_le _

theorem pathEdges_comm (u v : Fin n) : T.pathEdges u v = T.pathEdges v u := by
  classical
  let rp : T.graph.Path v u := ⟨(T.path u v).1.reverse, (T.path u v).2.reverse⟩
  have hrp : rp = T.path v u := T.path_unique rp
  unfold PosIntTree.pathEdges
  rw [← hrp]
  simp [rp]

theorem dist_comm (u v : Fin n) : T.dist u v = T.dist v u := by
  classical
  unfold PosIntTree.dist
  rw [T.pathEdges_comm u v]

theorem pairDist_pairOfDistinct (u v : Fin n) (huv : u ≠ v) :
    T.pairDist (VertexPair.ofDistinct u v huv) = T.dist u v := by
  by_cases h : u < v
  · simp [VertexPair.ofDistinct, h, PosIntTree.pairDist,
      VertexPair.left, VertexPair.right]
  · simp [VertexPair.ofDistinct, h, PosIntTree.pairDist,
      VertexPair.left, VertexPair.right, T.dist_comm]

/-- Actual path/cut characterization: the unique pair path uses `e` exactly
when its endpoints lie in opposite deletion components. -/
theorem mem_pathEdges_iff_opposite_cuts (e : T.Edge) (u v : Fin n) :
    e.1 ∈ T.pathEdges u v ↔
      (T.LeftCut e u ∧ T.RightCut e v) ∨
      (T.RightCut e u ∧ T.LeftCut e v) := by
  classical
  have hnotReach : e.1 ∈ T.pathEdges u v ↔ ¬(T.cutGraph e).Reachable u v := by
    rw [T.cut_reachable_iff_not_mem_pathEdges e u v]
    tauto
  rw [hnotReach]
  constructor
  · intro hnr
    rcases T.cut_cover e u with hul | hur <;>
      rcases T.cut_cover e v with hvl | hvr
    · exact (hnr (hul.trans hvl.symm)).elim
    · exact Or.inl ⟨hul, hvr⟩
    · exact Or.inr ⟨hur, hvl⟩
    · exact (hnr (hur.trans hvr.symm)).elim
  · rintro (⟨hul, hvr⟩ | ⟨hur, hvl⟩) huv
    · exact T.cut_endpoints_not_reachable e (hul.symm.trans (huv.trans hvr))
    · exact T.cut_endpoints_not_reachable e (hvl.symm.trans (huv.symm.trans hur))

/-- The actual-port additive decomposition for every cross pair of an actual
edge cut. -/
theorem cross_distance_decomposition (e : T.Edge) {u v : Fin n}
    (hu : T.LeftCut e u) (hv : T.RightCut e v) :
    T.dist u v = T.dist u (T.edgeLeft e) + T.weight e +
      T.dist (T.edgeRight e) v := by
  classical
  change (T.cutGraph e).Reachable u (T.edgeLeft e) at hu
  change (T.cutGraph e).Reachable v (T.edgeRight e) at hv
  obtain ⟨qL, hqL⟩ := hu.exists_isPath
  obtain ⟨qR, hqR⟩ := hv.symm.exists_isPath
  let pL : T.graph.Path u (T.edgeLeft e) :=
    ⟨qL.mapLe (T.cutGraph_le e), hqL.mapLe (T.cutGraph_le e)⟩
  let pR : T.graph.Path (T.edgeRight e) v :=
    ⟨qR.mapLe (T.cutGraph_le e), hqR.mapLe (T.cutGraph_le e)⟩
  have hdisjoint : pL.1.support.Disjoint pR.1.support := by
    rw [List.disjoint_left]
    intro x hxL hxR
    have hxLq : x ∈ qL.support := by simpa [pL] using hxL
    have hxRq : x ∈ qR.support := by simpa [pR] using hxR
    have hxa : (T.cutGraph e).Reachable x (T.edgeLeft e) :=
      (qL.dropUntil x hxLq).reachable
    have hbx : (T.cutGraph e).Reachable (T.edgeRight e) x :=
      (qR.takeUntil x hxRq).reachable
    exact T.cut_endpoints_not_reachable e (hxa.symm.trans hbx.symm)
  have hbnot : T.edgeRight e ∉ pL.1.support := by
    intro hb
    exact (List.disjoint_left.mp hdisjoint hb) pR.1.start_mem_support
  let pLE : T.graph.Walk u (T.edgeRight e) := pL.1.concat (T.edge_adj e)
  have hpLE : pLE.IsPath := pL.2.concat hbnot (T.edge_adj e)
  let route : T.graph.Walk u v := pLE.append pR.1
  have hroute : route.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append,
      List.nodup_append]
    refine ⟨hpLE.support_nodup, pR.2.support_nodup.tail, ?_⟩
    intro x hx y hy hxy
    subst y
    have hx' : x ∈ pL.1.support ∨ x = T.edgeRight e := by
      simpa [pLE] using hx
    rcases hx' with hxL | rfl
    · exact (List.disjoint_left.mp hdisjoint hxL) (List.mem_of_mem_tail hy)
    · have hnodup := pR.2.support_nodup
      have hcons : (T.edgeRight e :: pR.1.support.tail).Nodup := by
        rw [← pR.1.support_eq_cons]
        exact hnodup
      exact (List.nodup_cons.mp hcons).1 hy
  have hrouteDist : T.walkWeight route = T.dist u v :=
    T.path_walkWeight_eq_dist ⟨route, hroute⟩
  have hpLDist : T.walkWeight pL.1 = T.dist u (T.edgeLeft e) :=
    T.path_walkWeight_eq_dist pL
  have hpRDist : T.walkWeight pR.1 = T.dist (T.edgeRight e) v :=
    T.path_walkWeight_eq_dist pR
  have hwedge : T.weightOfPair s(T.edgeLeft e, T.edgeRight e) = T.weight e := by
    rw [← T.edge_eq_mk_endpoints e]
    exact T.weightOfPair_edge e
  calc
    T.dist u v = T.walkWeight route := hrouteDist.symm
    _ = T.walkWeight pL.1 + T.weight e + T.walkWeight pR.1 := by
      simp [route, pLE, PosIntTree.walkWeight, hwedge, List.sum_append, add_assoc]
    _ = T.dist u (T.edgeLeft e) + T.weight e + T.dist (T.edgeRight e) v := by
      rw [hpLDist, hpRDist]

end PosIntTree

end T2

/-! ## Shared exact cut enumerations -/

namespace PosIntTree

variable {n : ℕ} (T : PosIntTree n)

theorem pathEdges_self (u : Fin n) : T.pathEdges u u = ∅ := by
  classical
  let p0 : T.graph.Path u u := ⟨SimpleGraph.Walk.nil, by simp⟩
  have hp : p0 = T.path u u := T.path_unique p0
  unfold pathEdges
  rw [← hp]
  simp [p0]

@[simp] theorem dist_self (u : Fin n) : T.dist u u = 0 := by
  classical
  simp [dist, T.pathEdges_self u]

/-- Vertices on the endpoint-oriented sides of the deletion cut. -/
abbrev LeftVertex (e : T.Edge) := {u : Fin n // T.LeftCut e u}
abbrev RightVertex (e : T.Edge) := {u : Fin n // T.RightCut e u}

noncomputable instance (e : T.Edge) : Fintype (T.LeftVertex e) :=
  Fintype.ofFinite _
noncomputable instance (e : T.Edge) : Fintype (T.RightVertex e) :=
  Fintype.ofFinite _

/-- The endpoint-oriented left side size.  Reversing the orientation replaces
it by its complement, so all public checksum terms use `s * (n-s)`. -/
noncomputable def cutSize (e : T.Edge) : ℕ := Fintype.card (T.LeftVertex e)

noncomputable def rightVertexEquivComplement (e : T.Edge) :
    T.RightVertex e ≃ {u : Fin n // ¬T.LeftCut e u} :=
  Equiv.subtypeEquivProp <| funext fun u =>
    propext (T.rightCut_iff_not_leftCut e u)

theorem rightVertex_card (e : T.Edge) :
    Fintype.card (T.RightVertex e) = n - T.cutSize e := by
  classical
  calc
    Fintype.card (T.RightVertex e) =
        Fintype.card {u : Fin n // ¬T.LeftCut e u} :=
      Fintype.card_congr (T.rightVertexEquivComplement e)
    _ = n - Fintype.card (T.LeftVertex e) :=
      by simp
    _ = n - T.cutSize e := rfl

theorem cutSize_pos (e : T.Edge) : 0 < T.cutSize e := by
  classical
  unfold cutSize
  exact Fintype.card_pos_iff.mpr
    ⟨⟨T.edgeLeft e, T.edgeLeft_mem_LeftCut e⟩⟩

theorem rightVertex_card_pos (e : T.Edge) :
    0 < Fintype.card (T.RightVertex e) := by
  classical
  exact Fintype.card_pos_iff.mpr
    ⟨⟨T.edgeRight e, T.edgeRight_mem_RightCut e⟩⟩

theorem cutSize_lt_order (e : T.Edge) : T.cutSize e < n := by
  have hr := T.rightVertex_card_pos e
  rw [T.rightVertex_card e] at hr
  omega

/-- Indexed unordered pairs whose canonical path crosses a fixed actual edge. -/
abbrev CrossingPair (e : T.Edge) :=
  {p : VertexPair n // e.1 ∈ T.pathEdges p.left p.right}

/-- The path-crossing pair index is exactly the indexed Cartesian product of
the two actual deletion sides. -/
noncomputable def crossingPairEquiv (e : T.Edge) :
    T.LeftVertex e × T.RightVertex e ≃ T.CrossingPair e := by
  classical
  let er : T.RightVertex e ≃ {v : Fin n // ¬T.LeftCut e v} :=
    T.rightVertexEquivComplement e
  let ep : T.LeftVertex e × T.RightVertex e ≃
      T.LeftVertex e × {v : Fin n // ¬T.LeftCut e v} :=
    Equiv.prodCongr (Equiv.refl _) er
  let eo : T.LeftVertex e × T.RightVertex e ≃ OppositePair (T.LeftCut e) :=
    ep.trans (oppositePairEquiv (T.LeftCut e))
  let ec : OppositePair (T.LeftCut e) ≃ T.CrossingPair e :=
    Equiv.subtypeEquivProp <| funext fun p => propext <| by
      rw [T.mem_pathEdges_iff_opposite_cuts e p.left p.right]
      simp only [T.rightCut_iff_not_leftCut e]
  exact eo.trans ec

theorem crossingPair_card (e : T.Edge) :
    Fintype.card (T.CrossingPair e) = T.cutSize e * (n - T.cutSize e) := by
  calc
    Fintype.card (T.CrossingPair e) =
        Fintype.card (T.LeftVertex e × T.RightVertex e) :=
      Fintype.card_congr (T.crossingPairEquiv e).symm
    _ = Fintype.card (T.LeftVertex e) * Fintype.card (T.RightVertex e) :=
      Fintype.card_prod _ _
    _ = T.cutSize e * (n - T.cutSize e) := by
      rw [T.rightVertex_card e]
      rfl

end PosIntTree

/-! ## T4: actual path incidence and the cut checksum -/

section T4

variable {n : ℕ} {T : PosIntTree n}

namespace PosIntTree

/-- The `0/1` incidence of an actual physical edge in the canonical path of
an indexed unordered vertex pair. -/
noncomputable def pathIncidence (p : VertexPair n) (e : T.Edge) : ℕ :=
  if e.1 ∈ T.pathEdges p.left p.right then 1 else 0

theorem pathIncidence_row (p : VertexPair n) :
    LeechTrees.weightedRow T.pathIncidence T.weight p = T.pairDist p := by
  classical
  unfold LeechTrees.weightedRow pathIncidence pairDist
  simp only [ite_mul, one_mul, zero_mul]
  change (∑ e ∈ (Finset.univ : Finset T.Edge),
      if e.1 ∈ T.pathEdges p.left p.right then T.weight e else 0) =
      T.dist p.left p.right
  rw [← Finset.sum_filter]
  unfold dist
  apply Finset.sum_bij (fun e _ => e.1)
  · intro e he
    exact (Finset.mem_filter.mp he).2
  · intro e₁ he₁ e₂ he₂ hval
    exact Subtype.ext hval
  · intro x hx
    let e : T.Edge := T.edgeOfPathMem x hx
    refine ⟨e, ?_, rfl⟩
    simp [e, hx]
  · intro e he
    simp

theorem pathIncidence_column (e : T.Edge) :
    LeechTrees.columnCount T.pathIncidence e =
      T.cutSize e * (n - T.cutSize e) := by
  classical
  calc
    LeechTrees.columnCount T.pathIncidence e =
        Fintype.card (T.CrossingPair e) := by
      unfold LeechTrees.columnCount pathIncidence
      rw [← Finset.card_filter]
      simpa using (Fintype.card_subtype
        (fun p : VertexPair n => e.1 ∈ T.pathEdges p.left p.right)).symm
    _ = T.cutSize e * (n - T.cutSize e) := T.crossingPair_card e

end PosIntTree

namespace IsLeech

noncomputable def spectrumEquiv (hL : IsLeech T) :
    VertexPair n ≃ {k : ℕ // k ∈ Finset.Icc 1 (targetN n)} :=
  Equiv.ofBijective
    (fun p : VertexPair n =>
      (⟨T.pairDist p, hL.pairDist_mem p⟩ :
        {k : ℕ // k ∈ Finset.Icc 1 (targetN n)}))
    hL.bijective

end IsLeech

theorem sum_Icc_one_id (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, k) = N * (N + 1) / 2 := by
  have hsubset : Finset.Icc 1 N ⊆ Finset.range (N + 1) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    simp
    omega
  calc
    (∑ k ∈ Finset.Icc 1 N, k) = ∑ k ∈ Finset.range (N + 1), k := by
      apply Finset.sum_subset hsubset
      intro k hkrange hknot
      rw [Finset.mem_Icc] at hknot
      simp at hkrange
      push_neg at hknot
      omega
    _ = (N + 1) * N / 2 := Finset.sum_range_id (N + 1)
    _ = N * (N + 1) / 2 := by rw [Nat.mul_comm]

theorem t4_pair_distance_sum (hL : IsLeech T) :
    (∑ p : VertexPair n, T.pairDist p) =
      targetN n * (targetN n + 1) / 2 := by
  classical
  calc
    (∑ p : VertexPair n, T.pairDist p) =
        ∑ k : {k : ℕ // k ∈ Finset.Icc 1 (targetN n)}, k.1 := by
      apply Fintype.sum_equiv (hL.spectrumEquiv) T.pairDist Subtype.val
      intro p
      rfl
    _ = ∑ k ∈ Finset.Icc 1 (targetN n), k := by
      symm
      exact Finset.sum_subtype _ (fun _ => Iff.rfl) _
    _ = targetN n * (targetN n + 1) / 2 := sum_Icc_one_id _

/-- Claim-level T4: the row identity and actual edge-cut column count are
derived from canonical tree paths, and then double-counted. -/
theorem T4_cut_checksum (hL : IsLeech T) :
    (∑ e : T.Edge, T.cutSize e * (n - T.cutSize e) * T.weight e) =
      targetN n * (targetN n + 1) / 2 := by
  calc
    (∑ e : T.Edge, T.cutSize e * (n - T.cutSize e) * T.weight e) =
        ∑ p : VertexPair n, T.pairDist p := by
      exact LeechTrees.cutChecksum T.pathIncidence T.weight
        (fun e => T.cutSize e * (n - T.cutSize e)) T.pairDist
        T.pathIncidence_row T.pathIncidence_column
    _ = targetN n * (targetN n + 1) / 2 := t4_pair_distance_sum hL

theorem T4_order18_checksum {T : PosIntTree 18} (hL : IsLeech T) :
    (∑ e : T.Edge, T.cutSize e * (18 - T.cutSize e) * T.weight e) = 11781 := by
  simpa [targetN] using T4_cut_checksum hL

end T4

/-! ## T5: every-edge rooted direct sums and the capacity bound -/

section T5

variable {n : ℕ} {T : PosIntTree n}

namespace PosIntTree

noncomputable def leftDepth (e : T.Edge) (u : T.LeftVertex e) : ℕ :=
  T.dist u.1 (T.edgeLeft e)

noncomputable def rightDepth (e : T.Edge) (v : T.RightVertex e) : ℕ :=
  T.dist (T.edgeRight e) v.1

/-- The actual rooted cross sum, including the physical cut-edge weight. -/
noncomputable def rootedCrossSum (e : T.Edge)
    (x : T.LeftVertex e × T.RightVertex e) : ℕ :=
  T.leftDepth e x.1 + T.weight e + T.rightDepth e x.2

theorem left_right_ne (e : T.Edge) (u : T.LeftVertex e)
    (v : T.RightVertex e) : u.1 ≠ v.1 := by
  intro h
  apply T.LeftCut_disjoint_RightCut e u.1
  exact ⟨u.2, by simpa [h] using v.2⟩

noncomputable def crossVertexPair (e : T.Edge)
    (x : T.LeftVertex e × T.RightVertex e) : VertexPair n :=
  VertexPair.ofDistinct x.1.1 x.2.1 (T.left_right_ne e x.1 x.2)

theorem crossVertexPair_crosses (e : T.Edge)
    (x : T.LeftVertex e × T.RightVertex e) :
    e.1 ∈ T.pathEdges (T.crossVertexPair e x).left
      (T.crossVertexPair e x).right := by
  have hraw : e.1 ∈ T.pathEdges x.1.1 x.2.1 :=
    (T.mem_pathEdges_iff_opposite_cuts e x.1.1 x.2.1).2
      (Or.inl ⟨x.1.2, x.2.2⟩)
  by_cases hlt : x.1.1 < x.2.1
  · simpa [crossVertexPair, VertexPair.ofDistinct, hlt,
      VertexPair.left, VertexPair.right] using hraw
  · have hcomm := T.pathEdges_comm x.1.1 x.2.1
    simpa [crossVertexPair, VertexPair.ofDistinct, hlt,
      VertexPair.left, VertexPair.right, hcomm] using hraw

theorem crossingPairEquiv_apply_val (e : T.Edge)
    (x : T.LeftVertex e × T.RightVertex e) :
    (T.crossingPairEquiv e x).1 = T.crossVertexPair e x := by
  rfl

theorem crossVertexPair_injective (e : T.Edge) :
    Function.Injective (T.crossVertexPair e) := by
  intro x y hxy
  apply (T.crossingPairEquiv e).injective
  apply Subtype.ext
  simpa [T.crossingPairEquiv_apply_val e] using hxy

/-- Every cross distance is exactly the rooted direct sum through the actual
edge ports. -/
theorem pairDist_crossVertexPair (e : T.Edge)
    (x : T.LeftVertex e × T.RightVertex e) :
    T.pairDist (T.crossVertexPair e x) = T.rootedCrossSum e x := by
  unfold crossVertexPair
  rw [T.pairDist_pairOfDistinct x.1.1 x.2.1 (T.left_right_ne e x.1 x.2)]
  exact T.cross_distance_decomposition e x.1.2 x.2.2

theorem rootedCrossSum_injective (hL : IsLeech T) (e : T.Edge) :
    Function.Injective (T.rootedCrossSum e) := by
  intro x y hxy
  apply T.crossVertexPair_injective e
  apply hL.pairDist_injective
  rw [T.pairDist_crossVertexPair e, T.pairDist_crossVertexPair e]
  exact hxy

theorem leftDepth_injective (hL : IsLeech T) (e : T.Edge) :
    Function.Injective (T.leftDepth e) := by
  let v0 : T.RightVertex e :=
    ⟨T.edgeRight e, T.edgeRight_mem_RightCut e⟩
  intro u u' h
  have : (u, v0) = (u', v0) := T.rootedCrossSum_injective hL e <| by
    unfold rootedCrossSum
    rw [h]
  exact congrArg Prod.fst this

theorem rightDepth_injective (hL : IsLeech T) (e : T.Edge) :
    Function.Injective (T.rightDepth e) := by
  let u0 : T.LeftVertex e :=
    ⟨T.edgeLeft e, T.edgeLeft_mem_LeftCut e⟩
  intro v v' h
  have : (u0, v) = (u0, v') := T.rootedCrossSum_injective hL e <| by
    unfold rootedCrossSum
    rw [h]
  exact congrArg Prod.snd this

/-- The ordered integer difference criterion, with the endpoint-zero depths
retained as genuine indexed entries. -/
theorem rooted_difference_criterion (hL : IsLeech T) (e : T.Edge) :
    ∀ u u' : T.LeftVertex e, ∀ v v' : T.RightVertex e,
      (T.leftDepth e u : ℤ) - T.leftDepth e u' =
        (T.rightDepth e v' : ℤ) - T.rightDepth e v →
      u = u' ∧ v = v' := by
  intro u u' v v' hd
  have hsumZ : (T.leftDepth e u : ℤ) + T.rightDepth e v =
      (T.leftDepth e u' : ℤ) + T.rightDepth e v' := by
    linarith
  have hsumN : T.leftDepth e u + T.rightDepth e v =
      T.leftDepth e u' + T.rightDepth e v' := by
    exact_mod_cast hsumZ
  have hprod : (u, v) = (u', v') := T.rootedCrossSum_injective hL e <| by
    change T.leftDepth e u + T.weight e + T.rightDepth e v =
      T.leftDepth e u' + T.weight e + T.rightDepth e v'
    omega
  exact ⟨congrArg Prod.fst hprod, congrArg Prod.snd hprod⟩

/-- Exact actual-tree equivalence between indexed rooted-cross-sum
injectivity and the ordered integer depth-difference criterion. -/
theorem rootedCrossSum_injective_iff_difference_unique (e : T.Edge) :
    Function.Injective (T.rootedCrossSum e) ↔
      ∀ u u' : T.LeftVertex e, ∀ v v' : T.RightVertex e,
        (T.leftDepth e u : ℤ) - T.leftDepth e u' =
          (T.rightDepth e v' : ℤ) - T.rightDepth e v →
        u = u' ∧ v = v' := by
  constructor
  · intro hinj u u' v v' hd
    have hsumZ : (T.leftDepth e u : ℤ) + T.rightDepth e v =
        (T.leftDepth e u' : ℤ) + T.rightDepth e v' := by
      linarith
    have hsumN : T.leftDepth e u + T.rightDepth e v =
        T.leftDepth e u' + T.rightDepth e v' := by
      exact_mod_cast hsumZ
    have hp : (u, v) = (u', v') := hinj <| by
      change T.leftDepth e u + T.weight e + T.rightDepth e v =
        T.leftDepth e u' + T.weight e + T.rightDepth e v'
      omega
    exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
  · intro hcriterion x y hsum
    rcases x with ⟨u, v⟩
    rcases y with ⟨u', v'⟩
    have hsumN : T.leftDepth e u + T.rightDepth e v =
        T.leftDepth e u' + T.rightDepth e v' := by
      change T.leftDepth e u + T.weight e + T.rightDepth e v =
        T.leftDepth e u' + T.weight e + T.rightDepth e v' at hsum
      omega
    have hsumZ : (T.leftDepth e u : ℤ) + T.rightDepth e v =
        (T.leftDepth e u' : ℤ) + T.rightDepth e v' := by
      exact_mod_cast hsumN
    have hd : (T.leftDepth e u : ℤ) - T.leftDepth e u' =
        (T.rightDepth e v' : ℤ) - T.rightDepth e v := by
      linarith
    rcases hcriterion u u' v v' hd with ⟨hu, hv⟩
    exact Prod.ext hu hv

theorem rootedCrossSum_mem_target_tail (hL : IsLeech T) (e : T.Edge)
    (x : T.LeftVertex e × T.RightVertex e) :
    T.rootedCrossSum e x ∈ Finset.Icc (T.weight e) (targetN n) := by
  rw [Finset.mem_Icc]
  constructor
  · unfold rootedCrossSum
    omega
  · rw [← T.pairDist_crossVertexPair e]
    exact hL.pairDist_le_target _

theorem cutCapacity_pos (e : T.Edge) :
    0 < T.cutSize e * (n - T.cutSize e) := by
  rw [← T.rightVertex_card e]
  exact Nat.mul_pos (T.cutSize_pos e) (T.rightVertex_card_pos e)

/-- Every actual edge has enough target tail to hold all of its distinct
cross sums.  Equivalently `w_e ≤ N - s_e(n-s_e) + 1`. -/
theorem edge_weight_cap (hL : IsLeech T) (e : T.Edge) :
    T.weight e ≤ targetN n - T.cutSize e * (n - T.cutSize e) + 1 := by
  classical
  let encode : T.LeftVertex e × T.RightVertex e →
      {k : ℕ // k ∈ Finset.Icc (T.weight e) (targetN n)} := fun x =>
    ⟨T.rootedCrossSum e x, T.rootedCrossSum_mem_target_tail hL e x⟩
  have henc : Function.Injective encode := by
    intro x y h
    apply T.rootedCrossSum_injective hL e
    exact congrArg Subtype.val h
  have hcard := Fintype.card_le_of_injective encode henc
  have hcapacity : T.cutSize e * (n - T.cutSize e) ≤
      targetN n + 1 - T.weight e := by
    simpa [encode, Fintype.card_prod, T.rightVertex_card e,
      Fintype.card_subtype, Nat.card_Icc, cutSize] using hcard
  have hwle : T.weight e ≤ targetN n :=
    (Finset.mem_Icc.mp (t1_edge_weight_mem_target hL e)).2
  omega

end PosIntTree

/-- Claim-level T5 bundle for every actual physical edge. -/
theorem T5_every_edge_direct_sum (hL : IsLeech T) (e : T.Edge) :
    (∀ x : T.LeftVertex e × T.RightVertex e,
      T.pairDist (T.crossVertexPair e x) = T.rootedCrossSum e x) ∧
    Function.Injective (T.leftDepth e) ∧
    Function.Injective (T.rightDepth e) ∧
    Function.Injective (T.rootedCrossSum e) ∧
    (∀ u u' : T.LeftVertex e, ∀ v v' : T.RightVertex e,
      (T.leftDepth e u : ℤ) - T.leftDepth e u' =
        (T.rightDepth e v' : ℤ) - T.rightDepth e v →
      u = u' ∧ v = v') ∧
    (Function.Injective (T.rootedCrossSum e) ↔
      ∀ u u' : T.LeftVertex e, ∀ v v' : T.RightVertex e,
        (T.leftDepth e u : ℤ) - T.leftDepth e u' =
          (T.rightDepth e v' : ℤ) - T.rightDepth e v →
        u = u' ∧ v = v') ∧
    T.weight e ≤ targetN n - T.cutSize e * (n - T.cutSize e) + 1 := by
  exact ⟨T.pairDist_crossVertexPair e, T.leftDepth_injective hL e,
    T.rightDepth_injective hL e, T.rootedCrossSum_injective hL e,
    T.rooted_difference_criterion hL e,
    T.rootedCrossSum_injective_iff_difference_unique e,
    T.edge_weight_cap hL e⟩

end T5

/-! ## T3: root parity, Taylor's order condition, and order eighteen -/

section T3

variable {n : ℕ} {T : PosIntTree n}

namespace PosIntTree

/-- Across an actual edge, the two root distances plus the edge weight have
even total parity.  This is derived from the actual deletion sides. -/
theorem root_edge_even (r : Fin n) (e : T.Edge) :
    Even (T.dist r (T.edgeLeft e) + T.weight e +
      T.dist r (T.edgeRight e)) := by
  rcases T.cut_cover e r with hr | hr
  · have hroute := T.cross_distance_decomposition e hr
      (T.edgeRight_mem_RightCut e)
    rw [T.dist_self] at hroute
    refine ⟨T.dist r (T.edgeLeft e) + T.weight e, ?_⟩
    omega
  · have hroute := T.cross_distance_decomposition e
      (T.edgeLeft_mem_LeftCut e) hr
    rw [T.dist_self] at hroute
    rw [T.dist_comm r (T.edgeLeft e),
      T.dist_comm r (T.edgeRight e)]
    refine ⟨T.weight e + T.dist (T.edgeRight e) r, ?_⟩
    omega

theorem root_adjacent_even (r : Fin n) {u v : Fin n}
    (h : T.graph.Adj u v) :
    Even (T.dist r u + T.weightOfPair s(u, v) + T.dist r v) := by
  let e : T.Edge := ⟨s(u, v), h⟩
  have hw : T.weightOfPair s(T.edgeLeft e, T.edgeRight e) = T.weight e := by
    rw [← T.edge_eq_mk_endpoints e]
    exact T.weightOfPair_edge e
  have hs : s(u, v) = s(T.edgeLeft e, T.edgeRight e) :=
    T.edge_eq_mk_endpoints e
  rcases Sym2.eq_iff.mp hs with huv | huv
  · rcases huv with ⟨hu, hv⟩
    rw [hu, hv, hw]
    exact T.root_edge_even r e
  · rcases huv with ⟨hu, hv⟩
    rw [hu, hv]
    rw [show T.weightOfPair s(T.edgeRight e, T.edgeLeft e) = T.weight e by
      simpa only [Sym2.eq_swap] using hw]
    rcases T.root_edge_even r e with ⟨k, hk⟩
    exact ⟨k, by omega⟩

theorem root_walk_even (r : Fin n) {u v : Fin n}
    (p : T.graph.Walk u v) :
    Even (T.dist r u + T.walkWeight p + T.dist r v) := by
  induction p with
  | @nil u0 =>
      refine ⟨T.dist r u0, ?_⟩
      simp [walkWeight]
  | @cons u v w h p ih =>
      have hedge := T.root_adjacent_even r h
      rw [Nat.even_iff] at hedge ih ⊢
      change (T.dist r u +
        (T.weightOfPair s(u, v) + T.walkWeight p) + T.dist r w) % 2 = 0
      omega

/-- Root-parity XOR on every actual canonical pair path. -/
theorem root_path_even (r u v : Fin n) :
    Even (T.dist r u + T.dist u v + T.dist r v) := by
  have h := T.root_walk_even r (T.path u v).1
  rw [T.path_walkWeight_eq_dist (T.path u v)] at h
  exact h

theorem pairDist_odd_iff_root_opposite (r : Fin n) (p : VertexPair n) :
    T.pairDist p % 2 = 1 ↔
      (T.dist r p.left % 2 = 0 ∧ T.dist r p.right % 2 = 1) ∨
      (T.dist r p.left % 2 = 1 ∧ T.dist r p.right % 2 = 0) := by
  have hp := T.root_path_even r p.left p.right
  rw [Nat.even_iff] at hp
  unfold pairDist
  omega

/-- Size of the root-even vertex class. -/
noncomputable def parityClassSize (r : Fin n) : ℕ :=
  Fintype.card {u : Fin n // T.dist r u % 2 = 0}

theorem parityClassSize_le_order (r : Fin n) : T.parityClassSize r ≤ n := by
  classical
  unfold parityClassSize
  simpa using Fintype.card_le_of_injective
    (fun u : {u : Fin n // T.dist r u % 2 = 0} => u.1)
    (fun _ _ h => Subtype.ext h)

/-- Odd-distance indexed pairs are exactly the Cartesian product of the two
root-parity classes. -/
noncomputable def oddPairEquiv (r : Fin n) :
    ({u : Fin n // T.dist r u % 2 = 0} ×
      {v : Fin n // ¬T.dist r v % 2 = 0}) ≃
      {p : VertexPair n // T.pairDist p % 2 = 1} := by
  classical
  let eo := oppositePairEquiv (fun u : Fin n => T.dist r u % 2 = 0)
  let ep : OppositePair (fun u : Fin n => T.dist r u % 2 = 0) ≃
      {p : VertexPair n // T.pairDist p % 2 = 1} :=
    Equiv.subtypeEquivProp <| funext fun p => propext <| by
      rw [T.pairDist_odd_iff_root_opposite r p]
      have hl : T.dist r p.left % 2 < 2 := Nat.mod_lt _ (by omega)
      have hr : T.dist r p.right % 2 < 2 := Nat.mod_lt _ (by omega)
      omega
  exact eo.trans ep

theorem oddPair_card (r : Fin n) :
    Fintype.card {p : VertexPair n // T.pairDist p % 2 = 1} =
      T.parityClassSize r * (n - T.parityClassSize r) := by
  classical
  calc
    Fintype.card {p : VertexPair n // T.pairDist p % 2 = 1} =
        Fintype.card ({u : Fin n // T.dist r u % 2 = 0} ×
          {v : Fin n // ¬T.dist r v % 2 = 0}) :=
      Fintype.card_congr (T.oddPairEquiv r).symm
    _ = Fintype.card {u : Fin n // T.dist r u % 2 = 0} *
        Fintype.card {v : Fin n // ¬T.dist r v % 2 = 0} :=
      Fintype.card_prod _ _
    _ = T.parityClassSize r * (n - T.parityClassSize r) := by
      rw [Fintype.card_subtype_compl
        (fun u : Fin n => T.dist r u % 2 = 0)]
      simp [parityClassSize]

end PosIntTree

/-- Odd positive ranks in `1, ..., N`. -/
def oddTargetRanks (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun k => k % 2 = 1)

theorem oddTargetRanks_card (N : ℕ) :
    (oddTargetRanks N).card = (N + 1) / 2 := by
  induction N with
  | zero => simp [oddTargetRanks]
  | succ N ih =>
      have hle : (1 : ℕ) ≤ Order.succ N := by
        change 1 ≤ N + 1
        omega
      have hinterval : insert (N + 1) (Finset.Icc 1 N) =
          Finset.Icc 1 (N + 1) := by
        simpa only [Nat.succ_eq_add_one] using
          (Finset.insert_Icc_right_eq_Icc_succ hle)
      unfold oddTargetRanks at ih ⊢
      rw [← hinterval, Finset.filter_insert]
      by_cases hodd : (N + 1) % 2 = 1
      · have hnotmem : N + 1 ∉ (Finset.Icc 1 N).filter
            (fun k => k % 2 = 1) := by
          simp
        simp [hodd, hnotmem, ih]
        omega
      · have heven : (N + 1) % 2 = 0 := by omega
        simp [hodd, ih]
        omega

noncomputable def IsLeech.oddSpectrumEquiv (hL : IsLeech T) :
    {p : VertexPair n // T.pairDist p % 2 = 1} ≃
      {q : {k : ℕ // k ∈ Finset.Icc 1 (targetN n)} // q.1 % 2 = 1} :=
  Equiv.subtypeEquiv hL.spectrumEquiv (fun _ => Iff.rfl)

noncomputable def flattenOddTarget (n : ℕ) :
    {q : {k : ℕ // k ∈ Finset.Icc 1 (targetN n)} // q.1 % 2 = 1} ≃
      {k : ℕ // k ∈ oddTargetRanks (targetN n)} where
  toFun q := ⟨q.1.1, Finset.mem_filter.mpr ⟨q.1.2, q.2⟩⟩
  invFun k := ⟨⟨k.1, (Finset.mem_filter.mp k.2).1⟩,
    (Finset.mem_filter.mp k.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem oddPair_card_of_leech (hL : IsLeech T) :
    Fintype.card {p : VertexPair n // T.pairDist p % 2 = 1} =
      (targetN n + 1) / 2 := by
  classical
  letI : Fintype
      {q : {k : ℕ // k ∈ Finset.Icc 1 (targetN n)} // q.1 % 2 = 1} :=
    Fintype.ofFinite _
  calc
    Fintype.card {p : VertexPair n // T.pairDist p % 2 = 1} =
        Fintype.card
          {q : {k : ℕ // k ∈ Finset.Icc 1 (targetN n)} // q.1 % 2 = 1} :=
      Fintype.card_congr hL.oddSpectrumEquiv
    _ = Fintype.card {k : ℕ // k ∈ oddTargetRanks (targetN n)} :=
      Fintype.card_congr (flattenOddTarget n)
    _ = (oddTargetRanks (targetN n)).card := Fintype.card_coe _
    _ = (targetN n + 1) / 2 := oddTargetRanks_card _

/-- The exact Taylor parity equation, derived from the root XOR and the full
indexed target spectrum. -/
theorem t3_parity_equation (hL : IsLeech T) (r : Fin n) :
    T.parityClassSize r * (n - T.parityClassSize r) =
      (targetN n + 1) / 2 := by
  rw [← T.oddPair_card r, oddPair_card_of_leech hL]

theorem two_mul_targetN (n : ℕ) :
    2 * targetN n = n * (n - 1) := by
  rw [targetN, Nat.choose_two_right]
  have he := Nat.even_mul_pred_self n
  rw [Nat.even_iff] at he
  omega

private theorem taylor_cleared_nat (n a : ℕ)
    (h : a * (n - a) = (targetN n + 1) / 2) :
    4 * a * (n - a) = n * (n - 1) ∨
      4 * a * (n - a) = n * (n - 1) + 2 := by
  have hclear : 2 * (a * (n - a)) = targetN n ∨
      2 * (a * (n - a)) = targetN n + 1 := by
    omega
  rcases hclear with he | ho
  · left
    calc
      4 * a * (n - a) = 2 * (2 * (a * (n - a))) := by ring
      _ = 2 * targetN n := by rw [he]
      _ = n * (n - 1) := two_mul_targetN n
  · right
    calc
      4 * a * (n - a) = 2 * (2 * (a * (n - a))) := by ring
      _ = 2 * (targetN n + 1) := by rw [ho]
      _ = 2 * targetN n + 2 := by ring
      _ = n * (n - 1) + 2 := by rw [two_mul_targetN]

/-- Taylor's natural-number necessary order form.  A supplied root is the
explicit nonempty-order witness. -/
theorem t3_taylor_order_condition (hL : IsLeech T) (r : Fin n) :
    ∃ t : ℕ, n = t ^ 2 ∨ n = t ^ 2 + 2 := by
  let a := T.parityClassSize r
  have heq : a * (n - a) = (targetN n + 1) / 2 :=
    t3_parity_equation hL r
  have hclear := taylor_cleared_nat n a heq
  have ha : a ≤ n := T.parityClassSize_le_order r
  have hn : 1 ≤ n := by
    have hr := r.isLt
    omega
  have hclearInt :
      4 * (a : ℤ) * ((n : ℤ) - a) = (n : ℤ) * ((n : ℤ) - 1) ∨
      4 * (a : ℤ) * ((n : ℤ) - a) = (n : ℤ) * ((n : ℤ) - 1) + 2 := by
    rcases hclear with he | ho
    · left
      exact_mod_cast he
    · right
      exact_mod_cast ho
  obtain ⟨z, hz⟩ := LeechTrees.taylor_order_condition_of_parity_equation
    (n : ℤ) (a : ℤ) hclearInt
  refine ⟨z.natAbs, ?_⟩
  rcases hz with hz | hz
  · left
    have habs := congrArg Int.natAbs hz
    simpa using habs
  · right
    apply Int.ofNat_injective
    calc
      (n : ℤ) = z ^ 2 + 2 := hz
      _ = ((z.natAbs ^ 2 + 2 : ℕ) : ℤ) := by simp

/-- At order eighteen, the root-parity classes have sizes seven and eleven
(in either orientation). -/
theorem t3_order18_class_sizes {T : PosIntTree 18} (hL : IsLeech T)
    (r : Fin 18) :
    T.parityClassSize r = 7 ∨ T.parityClassSize r = 11 := by
  let a := T.parityClassSize r
  have ha : a ≤ 18 := T.parityClassSize_le_order r
  have heq : a * (18 - a) = 77 := by
    simpa [targetN] using t3_parity_equation hL r
  have hz : (a : ℤ) * (18 - (a : ℤ)) = 77 := by
    exact_mod_cast heq
  have hfactor : ((a : ℤ) - 7) * ((a : ℤ) - 11) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with h7 | h11
  · left
    exact_mod_cast (sub_eq_zero.mp h7)
  · right
    exact_mod_cast (sub_eq_zero.mp h11)

/-- Claim-level T3 bundle: graph parity, the exact class equation, Taylor's
natural order condition, and the specialized order-eighteen split. -/
theorem T3_taylor_parity_order18 {T : PosIntTree 18} (hL : IsLeech T)
    (r : Fin 18) :
    (∀ p : VertexPair 18,
      T.pairDist p % 2 = 1 ↔
        (T.dist r p.left % 2 = 0 ∧ T.dist r p.right % 2 = 1) ∨
        (T.dist r p.left % 2 = 1 ∧ T.dist r p.right % 2 = 0)) ∧
    T.parityClassSize r * (18 - T.parityClassSize r) = 77 ∧
    (∃ t : ℕ, 18 = t ^ 2 ∨ 18 = t ^ 2 + 2) ∧
    (T.parityClassSize r = 7 ∨ T.parityClassSize r = 11) := by
  refine ⟨T.pairDist_odd_iff_root_opposite r, ?_,
    t3_taylor_order_condition hL r, t3_order18_class_sizes hL r⟩
  simpa [targetN] using t3_parity_equation hL r

end T3

/-! ## T2 completion: actual-port merge block and persistence -/

section T2Completion

variable {n : ℕ} {T : PosIntTree n}

namespace PosIntTree

theorem prefixForest_le_cutGraph (e : T.Edge) :
    T.prefixForest e ≤ T.cutGraph e := by
  classical
  intro u v h
  rw [cutGraph, SimpleGraph.deleteEdges_adj]
  refine ⟨h.1, ?_⟩
  simp only [Set.mem_singleton_iff]
  intro heq
  have hw : T.weightOfPair s(u, v) = T.weight e := by
    rw [heq]
    exact T.weightOfPair_edge e
  have hlt := h.2
  rw [hw] at hlt
  exact (Nat.lt_irrefl _ hlt)

def PrefixLeft (e : T.Edge) (u : Fin n) : Prop :=
  (T.prefixForest e).Reachable u (T.edgeLeft e)

def PrefixRight (e : T.Edge) (u : Fin n) : Prop :=
  (T.prefixForest e).Reachable u (T.edgeRight e)

abbrev PrefixLeftVertex (e : T.Edge) := {u : Fin n // T.PrefixLeft e u}
abbrev PrefixRightVertex (e : T.Edge) := {u : Fin n // T.PrefixRight e u}

noncomputable instance (e : T.Edge) : Fintype (T.PrefixLeftVertex e) :=
  Fintype.ofFinite _
noncomputable instance (e : T.Edge) : Fintype (T.PrefixRightVertex e) :=
  Fintype.ofFinite _

theorem PrefixLeft.toLeftCut (e : T.Edge) {u : Fin n}
    (hu : T.PrefixLeft e u) : T.LeftCut e u := by
  obtain ⟨w⟩ := hu
  exact ⟨w.mapLe (T.prefixForest_le_cutGraph e)⟩

theorem PrefixRight.toRightCut (e : T.Edge) {u : Fin n}
    (hu : T.PrefixRight e u) : T.RightCut e u := by
  obtain ⟨w⟩ := hu
  exact ⟨w.mapLe (T.prefixForest_le_cutGraph e)⟩

noncomputable def prefixCutProduct (e : T.Edge) :
    T.PrefixLeftVertex e × T.PrefixRightVertex e →
      T.LeftVertex e × T.RightVertex e := fun x =>
  (⟨x.1.1, x.1.2.toLeftCut e⟩, ⟨x.2.1, x.2.2.toRightCut e⟩)

theorem prefixCutProduct_injective (e : T.Edge) :
    Function.Injective (T.prefixCutProduct e) := by
  intro x y h
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun z => z.1.1) h
  · apply Subtype.ext
    exact congrArg (fun z => z.2.1) h

/-- Actual-port Cartesian merge value for the two prefix components incident
to the chosen next edge. -/
noncomputable def prefixMergeSum (e : T.Edge)
    (x : T.PrefixLeftVertex e × T.PrefixRightVertex e) : ℕ :=
  T.dist x.1.1 (T.edgeLeft e) + T.weight e +
    T.dist (T.edgeRight e) x.2.1

theorem prefixMergeSum_eq_distance (e : T.Edge)
    (x : T.PrefixLeftVertex e × T.PrefixRightVertex e) :
    T.prefixMergeSum e x = T.dist x.1.1 x.2.1 := by
  exact (T.cross_distance_decomposition e
    (x.1.2.toLeftCut e) (x.2.2.toRightCut e)).symm

noncomputable def prefixMergePair (e : T.Edge)
    (x : T.PrefixLeftVertex e × T.PrefixRightVertex e) : VertexPair n :=
  T.crossVertexPair e (T.prefixCutProduct e x)

theorem pairDist_prefixMergePair (e : T.Edge)
    (x : T.PrefixLeftVertex e × T.PrefixRightVertex e) :
    T.pairDist (T.prefixMergePair e x) = T.prefixMergeSum e x := by
  unfold prefixMergePair
  rw [T.pairDist_crossVertexPair e]
  rfl

theorem prefixMergeSum_mem_target (hL : IsLeech T) (e : T.Edge)
    (x : T.PrefixLeftVertex e × T.PrefixRightVertex e) :
    T.prefixMergeSum e x ∈ Finset.Icc 1 (targetN n) := by
  rw [← T.pairDist_prefixMergePair e x]
  exact hL.pairDist_mem _

theorem prefixMergeSum_not_internal (hL : IsLeech T) (e : T.Edge)
    (x : T.PrefixLeftVertex e × T.PrefixRightVertex e) :
    T.prefixMergeSum e x ∉ T.prefixInternalDistances e := by
  classical
  intro hmem
  rw [prefixInternalDistances, Finset.mem_image] at hmem
  obtain ⟨p, hp, hpval⟩ := hmem
  have hpinternal : T.PrefixInternal e p := (Finset.mem_filter.mp hp).2
  have hpeq : p = T.prefixMergePair e x := hL.pairDist_injective <| by
    exact hpval.trans (T.pairDist_prefixMergePair e x).symm
  subst p
  have hcross : e.1 ∈ T.pathEdges (T.prefixMergePair e x).left
      (T.prefixMergePair e x).right := by
    exact T.crossVertexPair_crosses e (T.prefixCutProduct e x)
  have hlt := (T.prefixInternal_iff_path_lighter e
    (T.prefixMergePair e x)).1 hpinternal e.1 hcross
  rw [T.weightOfPair_edge e] at hlt
  exact (Nat.lt_irrefl _ hlt)

theorem prefixMergeSum_injective (hL : IsLeech T) (e : T.Edge) :
    Function.Injective (T.prefixMergeSum e) := by
  intro x y h
  apply T.prefixCutProduct_injective e
  apply T.rootedCrossSum_injective hL e
  exact h

theorem prefixForest_mono {e f : T.Edge} (hef : T.weight e ≤ T.weight f) :
    T.prefixForest e ≤ T.prefixForest f := by
  intro u v h
  exact ⟨h.1, lt_of_lt_of_le h.2 hef⟩

theorem prefixMergePair_orientation (e : T.Edge)
    (x : T.PrefixLeftVertex e × T.PrefixRightVertex e) :
    ((T.prefixMergePair e x).left = x.1.1 ∧
      (T.prefixMergePair e x).right = x.2.1) ∨
    ((T.prefixMergePair e x).left = x.2.1 ∧
      (T.prefixMergePair e x).right = x.1.1) := by
  unfold prefixMergePair crossVertexPair prefixCutProduct
  by_cases hlt : x.1.1 < x.2.1
  · left
    simp [VertexPair.ofDistinct, hlt, VertexPair.left, VertexPair.right]
  · right
    simp [VertexPair.ofDistinct, hlt, VertexPair.left, VertexPair.right]

theorem prefixMergePair_internal_of_lt {e f : T.Edge}
    (hef : T.weight e < T.weight f)
    (x : T.PrefixLeftVertex e × T.PrefixRightVertex e) :
    T.PrefixInternal f (T.prefixMergePair e x) := by
  obtain ⟨wL⟩ := x.1.2
  obtain ⟨wR⟩ := x.2.2
  let wLf := wL.mapLe (T.prefixForest_mono hef.le)
  let wRf := (wR.mapLe (T.prefixForest_mono hef.le)).reverse
  have hedge : (T.prefixForest f).Adj (T.edgeLeft e) (T.edgeRight e) := by
    constructor
    · exact T.edge_adj e
    · rw [← T.edge_eq_mk_endpoints e]
      simpa using hef
  have hraw : (T.prefixForest f).Reachable x.1.1 x.2.1 :=
    ⟨(wLf.concat hedge).append wRf⟩
  unfold PrefixInternal
  rcases T.prefixMergePair_orientation e x with h | h
  · rw [h.1, h.2]
    exact hraw
  · rw [h.1, h.2]
    exact hraw.symm

theorem prefixMergeSum_mem_later {e f : T.Edge}
    (hef : T.weight e < T.weight f)
    (x : T.PrefixLeftVertex e × T.PrefixRightVertex e) :
    T.prefixMergeSum e x ∈ T.prefixInternalDistances f := by
  classical
  rw [prefixInternalDistances, Finset.mem_image]
  refine ⟨T.prefixMergePair e x, ?_, T.pairDist_prefixMergePair e x⟩
  simp [T.prefixMergePair_internal_of_lt hef x]

theorem PrefixInternal.mono {e f : T.Edge} (hef : T.weight e ≤ T.weight f)
    {p : VertexPair n} (hp : T.PrefixInternal e p) :
    T.PrefixInternal f p := by
  rw [T.prefixInternal_iff_path_lighter f p]
  intro g hg
  exact lt_of_lt_of_le
    ((T.prefixInternal_iff_path_lighter e p).1 hp g hg) hef

theorem prefixInternalDistances_mono {e f : T.Edge}
    (hef : T.weight e ≤ T.weight f) :
    T.prefixInternalDistances e ⊆ T.prefixInternalDistances f := by
  classical
  intro k hk
  rw [prefixInternalDistances, Finset.mem_image] at hk ⊢
  obtain ⟨p, hp, rfl⟩ := hk
  refine ⟨p, ?_, rfl⟩
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨Finset.mem_univ p, hp.2.mono hef⟩

end PosIntTree

/-- Claim-level T2 completion: the forced positive MEX, the indexed
actual-port merge block, its collision-freeness, and monotone persistence. -/
theorem T2_forced_mex_merge_persistence (hL : IsLeech T) (e : T.Edge) :
    PosIntTree.mexPos (T.prefixInternalDistances e) = T.weight e ∧
    (∀ x : T.PrefixLeftVertex e × T.PrefixRightVertex e,
      T.prefixMergeSum e x = T.dist x.1.1 x.2.1) ∧
    Function.Injective (T.prefixMergeSum e) ∧
    (∀ x : T.PrefixLeftVertex e × T.PrefixRightVertex e,
      T.prefixMergeSum e x ∈ Finset.Icc 1 (targetN n)) ∧
    (∀ x : T.PrefixLeftVertex e × T.PrefixRightVertex e,
      T.prefixMergeSum e x ∉ T.prefixInternalDistances e) ∧
    (∀ f : T.Edge, T.weight e < T.weight f →
      ∀ x : T.PrefixLeftVertex e × T.PrefixRightVertex e,
        T.prefixMergeSum e x ∈ T.prefixInternalDistances f) ∧
    (∀ f : T.Edge, T.weight e ≤ T.weight f →
      T.prefixInternalDistances e ⊆ T.prefixInternalDistances f) := by
  exact ⟨T.t2_forced_mex hL e, T.prefixMergeSum_eq_distance e,
    T.prefixMergeSum_injective hL e, T.prefixMergeSum_mem_target hL e,
    T.prefixMergeSum_not_internal hL e,
    fun _ h => T.prefixMergeSum_mem_later h,
    fun _ h => T.prefixInternalDistances_mono h⟩

end T2Completion

end LeechTrees.Foundation
