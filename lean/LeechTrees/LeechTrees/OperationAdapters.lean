import LeechTrees.Extensions

/-!
# Exact literal operation adapters

This module separates literal graph operations from the smaller contradiction
certificates in `LeechTrees.Extension`.

* `LiteralWeightPreservingSubdivision` says that exactly one selected old
  edge is deleted, exactly two edges through one fresh vertex replace it,
  every other old edge and its weight are transported, and the two actual
  replacement weights sum to the selected old weight.
* `LiteralUnscaledBridge` says that two disjoint exhaustive named copies are
  joined by exactly one bridge, with every internal edge and weight unchanged.

The adapters below derive the old metric-retention records.  No reweighting,
vertex identification, scaling, or general gluing operation is represented.
-/

namespace LeechTrees.OperationAdapters

open LeechTrees.Foundation
open LeechTrees.Extension

/-! ## Weighted induced embeddings preserve the indexed metric -/

/-- An induced graph embedding that preserves every actual physical-edge
weight.  The induced (`↔`) graph embedding rules out chords between image
vertices; `weight_eq` rules out compensating internal reweightings. -/
structure WeightedGraphEmbedding {m n : ℕ}
    (T : PosIntTree m) (U : PosIntTree n) where
  embedding : T.graph ↪g U.graph
  weight_eq : ∀ e : T.Edge,
    U.weightOfPair (Sym2.map (fun x => embedding x) e.1) = T.weight e

namespace WeightedGraphEmbedding

variable {m n : ℕ} {T : PosIntTree m} {U : PosIntTree n}

theorem weightOfPair_map_adj (E : WeightedGraphEmbedding T U)
    {x y : Fin m} (hxy : T.graph.Adj x y) :
    U.weightOfPair s(E.embedding x, E.embedding y) =
      T.weightOfPair s(x, y) := by
  let e : T.Edge := ⟨s(x, y), hxy⟩
  calc
    U.weightOfPair s(E.embedding x, E.embedding y) =
        U.weightOfPair (Sym2.map (fun z => E.embedding z) e.1) := by
          simp [e]
    _ = T.weight e := E.weight_eq e
    _ = T.weightOfPair e.1 := (T.weightOfPair_edge e).symm
    _ = T.weightOfPair s(x, y) := rfl

theorem walkWeight_map (E : WeightedGraphEmbedding T U)
    {x y : Fin m} (p : T.graph.Walk x y) :
    U.walkWeight (p.map E.embedding.toHom) = T.walkWeight p := by
  induction p with
  | nil => simp [PosIntTree.walkWeight]
  | @cons x y z hxy p ih =>
      simp only [SimpleGraph.Walk.map_cons, PosIntTree.walkWeight,
        SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons]
      have hhead := E.weightOfPair_map_adj hxy
      simp only [SimpleGraph.Embedding.coe_toHom] at hhead ⊢
      unfold PosIntTree.walkWeight at ih
      rw [hhead, ih]

theorem dist_map (E : WeightedGraphEmbedding T U) (x y : Fin m) :
    U.dist (E.embedding x) (E.embedding y) = T.dist x y := by
  let q : U.graph.Path (E.embedding x) (E.embedding y) :=
    (T.path x y).mapEmbedding E.embedding
  calc
    U.dist (E.embedding x) (E.embedding y) = U.walkWeight q.1 :=
      (U.path_walkWeight_eq_dist q).symm
    _ = T.walkWeight (T.path x y).1 := E.walkWeight_map (T.path x y).1
    _ = T.dist x y := T.path_walkWeight_eq_dist (T.path x y)

noncomputable def retain (E : WeightedGraphEmbedding T U) :
    RetainsOldMetric T U where
  vertex := E.embedding.toEmbedding
  pairDist_eq := by
    intro p
    rw [mapVertexPair, U.pairDist_pairOfDistinct]
    simpa [PosIntTree.pairDist] using E.dist_map p.left p.right

end WeightedGraphEmbedding

/-! ## Exact literal subdivision -/

/-- Exact relation saying that `U` is obtained by replacing `oldEdge` of `T`
by a two-edge positive integral path through one fresh named vertex.

`remainderEmbedding` is induced on the old vertices after deleting precisely
`oldEdge`.  `edgeSet_eq` is the global no-extra/no-missing-edges clause.
The split equation is stated using the actual `U.weightOfPair` values of the
two displayed edges, so it cannot float free of the graph operation. -/
structure LiteralWeightPreservingSubdivision {m : ℕ}
    (T : PosIntTree m) (U : PosIntTree (m + 1)) where
  oldEdge : T.Edge
  remainderEmbedding :
    T.graph.deleteEdges ({oldEdge.1} : Set (Sym2 (Fin m))) ↪g U.graph
  newVertex : Fin (m + 1)
  new_not_old : ∀ x, newVertex ≠ remainderEmbedding x
  vertex_cover : ∀ z, z = newVertex ∨ ∃ x, remainderEmbedding x = z
  edgeSet_eq :
    U.graph.edgeSet =
      (Sym2.map (fun x => remainderEmbedding x) ''
        (T.graph.edgeSet \ ({oldEdge.1} : Set (Sym2 (Fin m))))) ∪
      ({s(remainderEmbedding (T.edgeLeft oldEdge), newVertex),
        s(newVertex, remainderEmbedding (T.edgeRight oldEdge))} :
          Set (Sym2 (Fin (m + 1))))
  old_weight_eq : ∀ e : T.Edge, e ≠ oldEdge →
    U.weightOfPair (Sym2.map (fun x => remainderEmbedding x) e.1) =
      T.weight e
  split_weight_sum :
    U.weightOfPair s(remainderEmbedding (T.edgeLeft oldEdge), newVertex) +
      U.weightOfPair s(newVertex, remainderEmbedding (T.edgeRight oldEdge)) =
        T.weight oldEdge

namespace LiteralWeightPreservingSubdivision

variable {m : ℕ} {T : PosIntTree m} {U : PosIntTree (m + 1)}

def oldVertex (S : LiteralWeightPreservingSubdivision T U) :
    Fin m ↪ Fin (m + 1) := S.remainderEmbedding.toEmbedding

@[simp] theorem oldVertex_apply (S : LiteralWeightPreservingSubdivision T U)
    (x : Fin m) : S.oldVertex x = S.remainderEmbedding x := rfl

def leftSegmentPair (S : LiteralWeightPreservingSubdivision T U) :
    Sym2 (Fin (m + 1)) :=
  s(S.oldVertex (T.edgeLeft S.oldEdge), S.newVertex)

def rightSegmentPair (S : LiteralWeightPreservingSubdivision T U) :
    Sym2 (Fin (m + 1)) :=
  s(S.newVertex, S.oldVertex (T.edgeRight S.oldEdge))

theorem leftSegmentPair_mem (S : LiteralWeightPreservingSubdivision T U) :
    S.leftSegmentPair ∈ U.graph.edgeSet := by
  rw [S.edgeSet_eq]
  simp [leftSegmentPair]

theorem rightSegmentPair_mem (S : LiteralWeightPreservingSubdivision T U) :
    S.rightSegmentPair ∈ U.graph.edgeSet := by
  rw [S.edgeSet_eq]
  simp [rightSegmentPair]

def leftSegmentEdge (S : LiteralWeightPreservingSubdivision T U) : U.Edge :=
  ⟨S.leftSegmentPair, S.leftSegmentPair_mem⟩

def rightSegmentEdge (S : LiteralWeightPreservingSubdivision T U) : U.Edge :=
  ⟨S.rightSegmentPair, S.rightSegmentPair_mem⟩

theorem leftSegment_adj (S : LiteralWeightPreservingSubdivision T U) :
    U.graph.Adj (S.oldVertex (T.edgeLeft S.oldEdge)) S.newVertex := by
  rw [← SimpleGraph.mem_edgeSet]
  exact S.leftSegmentPair_mem

theorem rightSegment_adj (S : LiteralWeightPreservingSubdivision T U) :
    U.graph.Adj S.newVertex (S.oldVertex (T.edgeRight S.oldEdge)) := by
  rw [← SimpleGraph.mem_edgeSet]
  exact S.rightSegmentPair_mem

theorem old_adj_of_ne (S : LiteralWeightPreservingSubdivision T U)
    {x y : Fin m} (hxy : T.graph.Adj x y)
    (hne : s(x, y) ≠ S.oldEdge.1) :
    U.graph.Adj (S.oldVertex x) (S.oldVertex y) := by
  apply S.remainderEmbedding.map_adj_iff.mpr
  simp [hxy, hne]

theorem split_edge_weight_sum
    (S : LiteralWeightPreservingSubdivision T U) :
    U.weight S.leftSegmentEdge + U.weight S.rightSegmentEdge =
      T.weight S.oldEdge := by
  rw [← U.weightOfPair_edge S.leftSegmentEdge,
    ← U.weightOfPair_edge S.rightSegmentEdge]
  simpa [leftSegmentEdge, rightSegmentEdge, leftSegmentPair,
    rightSegmentPair] using S.split_weight_sum

/-- Replace one adjacent old step by the literal two-edge split walk, and map
every other step through the induced remainder embedding. -/
noncomputable def liftEdgeWalk (S : LiteralWeightPreservingSubdivision T U)
    {x y : Fin m} (hxy : T.graph.Adj x y) :
    U.graph.Walk (S.oldVertex x) (S.oldVertex y) := by
  classical
  by_cases he : s(x, y) = S.oldEdge.1
  · have hs : s(x, y) =
        s(T.edgeLeft S.oldEdge, T.edgeRight S.oldEdge) :=
      he.trans (T.edge_eq_mk_endpoints S.oldEdge)
    by_cases hx : x = T.edgeLeft S.oldEdge
    · have hy : y = T.edgeRight S.oldEdge := by
        rcases Sym2.eq_iff.mp hs with hdir | hrev
        · exact hdir.2
        · have hfalse : False :=
            (ne_of_lt (T.edgeLeft_lt_edgeRight S.oldEdge))
              (hx.symm.trans hrev.1)
          exact hfalse.elim
      let q : U.graph.Walk
          (S.oldVertex (T.edgeLeft S.oldEdge))
          (S.oldVertex (T.edgeRight S.oldEdge)) :=
        .cons S.leftSegment_adj (.cons S.rightSegment_adj .nil)
      exact q.copy (congrArg S.oldVertex hx.symm)
        (congrArg S.oldVertex hy.symm)
    · have hxR : x = T.edgeRight S.oldEdge := by
        rcases Sym2.eq_iff.mp hs with hdir | hrev
        · exact (hx hdir.1).elim
        · exact hrev.1
      have hyL : y = T.edgeLeft S.oldEdge := by
        rcases Sym2.eq_iff.mp hs with hdir | hrev
        · exact (hx hdir.1).elim
        · exact hrev.2
      let q : U.graph.Walk
          (S.oldVertex (T.edgeRight S.oldEdge))
          (S.oldVertex (T.edgeLeft S.oldEdge)) :=
        .cons S.rightSegment_adj.symm (.cons S.leftSegment_adj.symm .nil)
      exact q.copy (congrArg S.oldVertex hxR.symm)
        (congrArg S.oldVertex hyL.symm)
  · exact (S.old_adj_of_ne hxy he).toWalk

theorem liftEdgeWalk_selected_reverse
    (S : LiteralWeightPreservingSubdivision T U)
    (hxy : T.graph.Adj (T.edgeRight S.oldEdge) (T.edgeLeft S.oldEdge)) :
    S.liftEdgeWalk hxy =
      .cons S.rightSegment_adj.symm (.cons S.leftSegment_adj.symm .nil) := by
  classical
  have he : s(T.edgeRight S.oldEdge, T.edgeLeft S.oldEdge) = S.oldEdge.1 := by
    calc
      s(T.edgeRight S.oldEdge, T.edgeLeft S.oldEdge) =
          s(T.edgeLeft S.oldEdge, T.edgeRight S.oldEdge) := by
            exact Sym2.eq_swap
      _ = S.oldEdge.1 := (T.edge_eq_mk_endpoints S.oldEdge).symm
  have hRL : T.edgeRight S.oldEdge ≠ T.edgeLeft S.oldEdge :=
    (ne_of_lt (T.edgeLeft_lt_edgeRight S.oldEdge)).symm
  simp [liftEdgeWalk, he, hRL]

/-- Recursively lift an old walk, replacing an occurrence of the selected
edge by the two split segments. -/
noncomputable def liftWalk (S : LiteralWeightPreservingSubdivision T U) :
    {x y : Fin m} → T.graph.Walk x y →
      U.graph.Walk (S.oldVertex x) (S.oldVertex y)
  | _, _, .nil => .nil
  | _, _, .cons h p => (S.liftEdgeWalk h).append (S.liftWalk p)

theorem liftEdgeWalk_support (S : LiteralWeightPreservingSubdivision T U)
    {x y : Fin m} (hxy : T.graph.Adj x y) :
    (S.liftEdgeWalk hxy).support =
      if s(x, y) = S.oldEdge.1 then
        [S.oldVertex x, S.newVertex, S.oldVertex y]
      else [S.oldVertex x, S.oldVertex y] := by
  classical
  by_cases he : s(x, y) = S.oldEdge.1
  · have hs : s(x, y) =
        s(T.edgeLeft S.oldEdge, T.edgeRight S.oldEdge) :=
      he.trans (T.edge_eq_mk_endpoints S.oldEdge)
    by_cases hx : x = T.edgeLeft S.oldEdge
    · have hy : y = T.edgeRight S.oldEdge := by
        rcases Sym2.eq_iff.mp hs with hdir | hrev
        · exact hdir.2
        · have hfalse : False :=
            (ne_of_lt (T.edgeLeft_lt_edgeRight S.oldEdge))
              (hx.symm.trans hrev.1)
          exact hfalse.elim
      subst x
      subst y
      simp [liftEdgeWalk, he]
    · have hxR : x = T.edgeRight S.oldEdge := by
        rcases Sym2.eq_iff.mp hs with hdir | hrev
        · exact (hx hdir.1).elim
        · exact hrev.1
      have hyL : y = T.edgeLeft S.oldEdge := by
        rcases Sym2.eq_iff.mp hs with hdir | hrev
        · exact (hx hdir.1).elim
        · exact hrev.2
      subst x
      subst y
      have hRL : T.edgeRight S.oldEdge ≠ T.edgeLeft S.oldEdge :=
        (ne_of_lt (T.edgeLeft_lt_edgeRight S.oldEdge)).symm
      simp [liftEdgeWalk, he, hRL]
  · simp [liftEdgeWalk, he]

theorem oldVertex_mem_liftEdgeWalk_support_iff
    (S : LiteralWeightPreservingSubdivision T U)
    {x y z : Fin m} (hxy : T.graph.Adj x y) :
    S.oldVertex z ∈ (S.liftEdgeWalk hxy).support ↔ z = x ∨ z = y := by
  rw [S.liftEdgeWalk_support]
  by_cases he : s(x, y) = S.oldEdge.1
  · simp only [if_pos he, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro (h | h | h)
      · exact Or.inl (S.oldVertex.injective h)
      · exact (S.new_not_old z h.symm).elim
      · exact Or.inr (S.oldVertex.injective h)
    · rintro (rfl | rfl) <;> simp
  · simp only [if_neg he, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro (h | h)
      · exact Or.inl (S.oldVertex.injective h)
      · exact Or.inr (S.oldVertex.injective h)
    · rintro (rfl | rfl) <;> simp

theorem newVertex_mem_liftEdgeWalk_support_iff
    (S : LiteralWeightPreservingSubdivision T U)
    {x y : Fin m} (hxy : T.graph.Adj x y) :
    S.newVertex ∈ (S.liftEdgeWalk hxy).support ↔
      s(x, y) = S.oldEdge.1 := by
  rw [S.liftEdgeWalk_support]
  by_cases he : s(x, y) = S.oldEdge.1
  · simp [he]
  · simp only [if_neg he, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro (h | h)
      · exact (S.new_not_old x h).elim
      · exact (S.new_not_old y h).elim
    · exact fun h => (he h).elim

theorem oldVertex_mem_liftWalk_support_iff
    (S : LiteralWeightPreservingSubdivision T U)
    {x y : Fin m} (p : T.graph.Walk x y) (z : Fin m) :
    S.oldVertex z ∈ (S.liftWalk p).support ↔ z ∈ p.support := by
  induction p with
  | @nil x => simp [liftWalk]
  | @cons x y w hxy p ih =>
      rw [liftWalk, SimpleGraph.Walk.mem_support_append_iff,
        S.oldVertex_mem_liftEdgeWalk_support_iff, ih]
      have hy : y ∈ p.support := p.start_mem_support
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
      aesop

theorem newVertex_mem_liftWalk_support_iff
    (S : LiteralWeightPreservingSubdivision T U)
    {x y : Fin m} (p : T.graph.Walk x y) :
    S.newVertex ∈ (S.liftWalk p).support ↔
      S.oldEdge.1 ∈ p.edges := by
  induction p with
  | @nil x => simp [liftWalk, S.new_not_old x]
  | @cons x y w hxy p ih =>
      rw [liftWalk, SimpleGraph.Walk.mem_support_append_iff,
        S.newVertex_mem_liftEdgeWalk_support_iff, ih]
      simp [SimpleGraph.Walk.edges_cons, eq_comm]

theorem liftWalk_isPath (S : LiteralWeightPreservingSubdivision T U)
    {x y : Fin m} (p : T.graph.Walk x y) (hp : p.IsPath) :
    (S.liftWalk p).IsPath := by
  induction p with
  | @nil x => simp [liftWalk]
  | @cons x y w hxy p ih =>
      have hpTail : p.IsPath := hp.of_cons
      have htail := ih hpTail
      have hxnot : x ∉ p.support :=
        (SimpleGraph.Walk.cons_isPath_iff hxy p).mp hp |>.2
      have hxnotLift : S.oldVertex x ∉ (S.liftWalk p).support := by
        rw [S.oldVertex_mem_liftWalk_support_iff]
        exact hxnot
      by_cases he : s(x, y) = S.oldEdge.1
      · have hedgeNot : S.oldEdge.1 ∉ p.edges := by
          have hn := hp.isTrail.edges_nodup
          simp only [SimpleGraph.Walk.edges_cons, List.nodup_cons] at hn
          simpa [he] using hn.1
        have hnewNot : S.newVertex ∉ (S.liftWalk p).support := by
          rw [S.newVertex_mem_liftWalk_support_iff]
          exact hedgeNot
        have hs : s(x, y) =
            s(T.edgeLeft S.oldEdge, T.edgeRight S.oldEdge) :=
          he.trans (T.edge_eq_mk_endpoints S.oldEdge)
        rcases Sym2.eq_iff.mp hs with hdir | hrev
        · rcases hdir with ⟨rfl, rfl⟩
          have hfirstNot :
              S.oldVertex (T.edgeLeft S.oldEdge) ∉
                (SimpleGraph.Walk.cons S.rightSegment_adj
                  (S.liftWalk p)).support := by
            rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
            exact ⟨(S.new_not_old _).symm, hxnotLift⟩
          have hpath :=
            (htail.cons hnewNot (h := S.rightSegment_adj)).cons hfirstNot
              (h := S.leftSegment_adj)
          simpa [liftWalk, liftEdgeWalk, he] using hpath
        · rcases hrev with ⟨rfl, rfl⟩
          have hRL : T.edgeRight S.oldEdge ≠ T.edgeLeft S.oldEdge :=
            (ne_of_lt (T.edgeLeft_lt_edgeRight S.oldEdge)).symm
          have hfirstNot :
              S.oldVertex (T.edgeRight S.oldEdge) ∉
                (SimpleGraph.Walk.cons S.leftSegment_adj.symm
                  (S.liftWalk p)).support := by
            rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
            exact ⟨(S.new_not_old _).symm, hxnotLift⟩
          have hpath :=
            (htail.cons hnewNot (h := S.leftSegment_adj.symm)).cons hfirstNot
              (h := S.rightSegment_adj.symm)
          simpa [liftWalk, liftEdgeWalk, he, hRL] using hpath
      · have hpath := htail.cons hxnotLift (h := S.old_adj_of_ne hxy he)
        simpa [liftWalk, liftEdgeWalk, he] using hpath

theorem liftEdgeWalk_weight (S : LiteralWeightPreservingSubdivision T U)
    {x y : Fin m} (hxy : T.graph.Adj x y) :
    U.walkWeight (S.liftEdgeWalk hxy) = T.weightOfPair s(x, y) := by
  classical
  by_cases he : s(x, y) = S.oldEdge.1
  · have hs : s(x, y) =
        s(T.edgeLeft S.oldEdge, T.edgeRight S.oldEdge) :=
      he.trans (T.edge_eq_mk_endpoints S.oldEdge)
    have hold : T.weightOfPair s(x, y) = T.weight S.oldEdge := by
      rw [he]
      exact T.weightOfPair_edge S.oldEdge
    rcases Sym2.eq_iff.mp hs with hdir | hrev
    · rcases hdir with ⟨rfl, rfl⟩
      rw [hold]
      simpa [liftEdgeWalk, he, PosIntTree.walkWeight,
        leftSegmentPair, rightSegmentPair] using S.split_weight_sum
    · rcases hrev with ⟨rfl, rfl⟩
      rw [hold]
      rw [S.liftEdgeWalk_selected_reverse hxy]
      change
        U.weightOfPair s(S.oldVertex (T.edgeRight S.oldEdge), S.newVertex) +
          U.weightOfPair s(S.newVertex, S.oldVertex (T.edgeLeft S.oldEdge)) =
            T.weight S.oldEdge
      calc
        U.weightOfPair s(S.oldVertex (T.edgeRight S.oldEdge), S.newVertex) +
            U.weightOfPair s(S.newVertex, S.oldVertex (T.edgeLeft S.oldEdge)) =
          U.weightOfPair s(S.newVertex, S.oldVertex (T.edgeRight S.oldEdge)) +
            U.weightOfPair s(S.oldVertex (T.edgeLeft S.oldEdge), S.newVertex) := by
              rw [show s(S.oldVertex (T.edgeRight S.oldEdge), S.newVertex) =
                    s(S.newVertex, S.oldVertex (T.edgeRight S.oldEdge)) from
                    Sym2.eq_swap,
                show s(S.newVertex, S.oldVertex (T.edgeLeft S.oldEdge)) =
                    s(S.oldVertex (T.edgeLeft S.oldEdge), S.newVertex) from
                    Sym2.eq_swap]
        _ = U.weightOfPair s(S.oldVertex (T.edgeLeft S.oldEdge), S.newVertex) +
            U.weightOfPair s(S.newVertex, S.oldVertex (T.edgeRight S.oldEdge)) :=
              Nat.add_comm _ _
        _ = T.weight S.oldEdge := by
          simpa [oldVertex] using S.split_weight_sum
  · let e : T.Edge := ⟨s(x, y), hxy⟩
    have hene : e ≠ S.oldEdge := by
      intro h
      exact he (congrArg Subtype.val h)
    have hw := S.old_weight_eq e hene
    have hw' :
        U.weightOfPair s(S.oldVertex x, S.oldVertex y) =
          T.weightOfPair s(x, y) := by
      calc
        U.weightOfPair s(S.oldVertex x, S.oldVertex y) =
            U.weightOfPair (Sym2.map (fun z => S.oldVertex z) e.1) := by
              simp [e]
        _ = T.weight e := by simpa [oldVertex] using hw
        _ = T.weightOfPair e.1 := (T.weightOfPair_edge e).symm
        _ = T.weightOfPair s(x, y) := rfl
    simpa [liftEdgeWalk, he, PosIntTree.walkWeight] using hw'

theorem walkWeight_append {n : ℕ} (V : PosIntTree n)
    {x y z : Fin n} (p : V.graph.Walk x y) (q : V.graph.Walk y z) :
    V.walkWeight (p.append q) = V.walkWeight p + V.walkWeight q := by
  simp [PosIntTree.walkWeight, SimpleGraph.Walk.edges_append,
    List.map_append, List.sum_append]

theorem liftWalk_weight (S : LiteralWeightPreservingSubdivision T U)
    {x y : Fin m} (p : T.graph.Walk x y) :
    U.walkWeight (S.liftWalk p) = T.walkWeight p := by
  induction p with
  | @nil x => simp [liftWalk, PosIntTree.walkWeight]
  | @cons x y z hxy p ih =>
      rw [liftWalk, walkWeight_append, S.liftEdgeWalk_weight, ih]
      simp [PosIntTree.walkWeight]

/-- Every old indexed distance is preserved by the literal subdivision. -/
theorem dist_oldVertex_eq (S : LiteralWeightPreservingSubdivision T U)
    (x y : Fin m) :
    U.dist (S.oldVertex x) (S.oldVertex y) = T.dist x y := by
  let q : U.graph.Path (S.oldVertex x) (S.oldVertex y) :=
    ⟨S.liftWalk (T.path x y).1,
      S.liftWalk_isPath (T.path x y).1 (T.path x y).2⟩
  calc
    U.dist (S.oldVertex x) (S.oldVertex y) = U.walkWeight q.1 :=
      (U.path_walkWeight_eq_dist q).symm
    _ = T.walkWeight (T.path x y).1 := S.liftWalk_weight (T.path x y).1
    _ = T.dist x y := T.path_walkWeight_eq_dist (T.path x y)

noncomputable def toRetainsOldMetric
    (S : LiteralWeightPreservingSubdivision T U) : RetainsOldMetric T U where
  vertex := S.oldVertex
  pairDist_eq := by
    intro p
    rw [mapVertexPair, U.pairDist_pairOfDistinct]
    simpa [PosIntTree.pairDist] using S.dist_oldVertex_eq p.left p.right

noncomputable def newPair
    (S : LiteralWeightPreservingSubdivision T U) : VertexPair (m + 1) :=
  VertexPair.ofDistinct (S.oldVertex (T.edgeLeft S.oldEdge)) S.newVertex
    ((S.new_not_old _).symm)

theorem newPair_fresh (S : LiteralWeightPreservingSubdivision T U) :
    ∀ p : VertexPair m,
      S.newPair ≠ mapVertexPair S.toRetainsOldMetric.vertex p := by
  intro p hp
  unfold newPair mapVertexPair at hp
  have hcases := (LeechTrees.QHop.VertexPair.ofDistinct_eq_iff
    ((S.new_not_old _).symm)
    (S.oldVertex.injective.ne (ne_of_lt p.left_lt_right))).mp hp
  rcases hcases with h | h
  · exact S.new_not_old p.right h.2
  · exact S.new_not_old p.left h.2

theorem pairDist_newPair_eq_leftWeight
    (S : LiteralWeightPreservingSubdivision T U) :
    U.pairDist S.newPair = U.weight S.leftSegmentEdge := by
  rw [newPair, U.pairDist_pairOfDistinct]
  let q : U.graph.Path
      (S.oldVertex (T.edgeLeft S.oldEdge)) S.newVertex :=
    ⟨S.leftSegment_adj.toWalk, SimpleGraph.Walk.IsPath.of_adj S.leftSegment_adj⟩
  calc
    U.dist (S.oldVertex (T.edgeLeft S.oldEdge)) S.newVertex =
        U.walkWeight q.1 := (U.path_walkWeight_eq_dist q).symm
    _ = U.weightOfPair S.leftSegmentPair := by
      simp [q, PosIntTree.walkWeight, leftSegmentPair]
    _ = U.weight S.leftSegmentEdge := U.weightOfPair_edge S.leftSegmentEdge

noncomputable def toWeightPreservingSubdivisionData
    (S : LiteralWeightPreservingSubdivision T U) :
    WeightPreservingSubdivisionData T U where
  retain := S.toRetainsOldMetric
  oldEdge := S.oldEdge
  newPair := S.newPair
  newPair_fresh := S.newPair_fresh
  newWeight_pos := by
    rw [S.pairDist_newPair_eq_leftWeight]
    exact U.weight_pos S.leftSegmentEdge
  newWeight_lt_old := by
    rw [S.pairDist_newPair_eq_leftWeight]
    have hsum := S.split_edge_weight_sum
    have hpos := U.weight_pos S.rightSegmentEdge
    omega

/-- Literal weight-preserving subdivision is impossible between two Leech
trees.  This is the operation-level D4 endpoint. -/
theorem no_literalWeightPreservingSubdivision
    (hT : IsLeech T) (hU : IsLeech U)
    (S : LiteralWeightPreservingSubdivision T U) : False :=
  no_weightPreservingSubdivision hT hU S.toWeightPreservingSubdivisionData

end LiteralWeightPreservingSubdivision

/-! ## Exact literal unscaled bridge gluing -/

/-- Exact relation saying that `U` is the disjoint, exhaustive union of the
two named induced input trees plus exactly one bridge between named ports.
All internal physical weights are retained verbatim. -/
structure LiteralUnscaledBridge {a b : ℕ}
    (A : PosIntTree a) (B : PosIntTree b) (U : PosIntTree (a + b)) where
  leftEmbedding : A.graph ↪g U.graph
  rightEmbedding : B.graph ↪g U.graph
  images_disjoint : ∀ x y, leftEmbedding x ≠ rightEmbedding y
  vertex_cover : ∀ z,
    (∃ x, leftEmbedding x = z) ∨ ∃ y, rightEmbedding y = z
  leftPort : Fin a
  rightPort : Fin b
  edgeSet_eq :
    U.graph.edgeSet =
      (Sym2.map (fun x => leftEmbedding x) '' A.graph.edgeSet) ∪
      (Sym2.map (fun y => rightEmbedding y) '' B.graph.edgeSet) ∪
      ({s(leftEmbedding leftPort, rightEmbedding rightPort)} :
        Set (Sym2 (Fin (a + b))))
  left_weight_eq : ∀ e : A.Edge,
    U.weightOfPair (Sym2.map (fun x => leftEmbedding x) e.1) = A.weight e
  right_weight_eq : ∀ e : B.Edge,
    U.weightOfPair (Sym2.map (fun y => rightEmbedding y) e.1) = B.weight e

namespace LiteralUnscaledBridge

variable {a b : ℕ} {A : PosIntTree a} {B : PosIntTree b}
  {U : PosIntTree (a + b)}

def bridgePair (G : LiteralUnscaledBridge A B U) : Sym2 (Fin (a + b)) :=
  s(G.leftEmbedding G.leftPort, G.rightEmbedding G.rightPort)

theorem bridgePair_mem (G : LiteralUnscaledBridge A B U) :
    G.bridgePair ∈ U.graph.edgeSet := by
  rw [G.edgeSet_eq]
  simp [bridgePair]

def bridgeEdge (G : LiteralUnscaledBridge A B U) : U.Edge :=
  ⟨G.bridgePair, G.bridgePair_mem⟩

theorem bridgeWeight_pos (G : LiteralUnscaledBridge A B U) :
    0 < U.weight G.bridgeEdge := U.weight_pos G.bridgeEdge

def leftWeightedEmbedding (G : LiteralUnscaledBridge A B U) :
    WeightedGraphEmbedding A U where
  embedding := G.leftEmbedding
  weight_eq := G.left_weight_eq

def rightWeightedEmbedding (G : LiteralUnscaledBridge A B U) :
    WeightedGraphEmbedding B U where
  embedding := G.rightEmbedding
  weight_eq := G.right_weight_eq

theorem dist_left_eq (G : LiteralUnscaledBridge A B U) (x y : Fin a) :
    U.dist (G.leftEmbedding x) (G.leftEmbedding y) = A.dist x y :=
  G.leftWeightedEmbedding.dist_map x y

theorem dist_right_eq (G : LiteralUnscaledBridge A B U) (x y : Fin b) :
    U.dist (G.rightEmbedding x) (G.rightEmbedding y) = B.dist x y :=
  G.rightWeightedEmbedding.dist_map x y

noncomputable def toUnscaledBridgeData
    (G : LiteralUnscaledBridge A B U) : UnscaledBridgeData A B U where
  left := G.leftWeightedEmbedding.retain
  right := G.rightWeightedEmbedding.retain
  images_disjoint := G.images_disjoint

/-- Literal unscaled bridge gluing of two nontrivial Leech trees is
impossible.  This is the non-singleton operation-level D4 endpoint. -/
theorem no_literalUnscaledBridge_of_nontrivial
    (hA : IsLeech A) (hB : IsLeech B) (hU : IsLeech U)
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (G : LiteralUnscaledBridge A B U) : False :=
  no_unscaledBridge_of_nontrivial hA hB hU ha hb G.toUnscaledBridgeData

end LiteralUnscaledBridge

end LeechTrees.OperationAdapters
