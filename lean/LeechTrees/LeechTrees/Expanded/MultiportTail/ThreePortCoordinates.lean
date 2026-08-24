import LeechTrees.OddQuotient.TwoPortCoordinates

/-!
# Three-anchor coordinates in one actual even component

The public input below is topological: it consists of actual named component
vertices together with membership in canonical paths of the actual tree.  No
coordinate equation, metric reconstruction, or coverage assertion is assumed.
From that path data the theorem derives the complete subtraction-free form of
the audited three-anchor coordinate equations.  The signed corollaries recover
the displayed half-sum formulas without truncated natural subtraction.

The separate parent section records the precise scoped converse interface.  It
does not assert the unaudited arbitrary-anchor package.
-/

namespace LeechTrees.OddQuotient.ThreePort

open LeechTrees.Foundation
open LeechTrees.OddEdges.T11Adapter

variable {n : ℕ}

/-- Which median arm contains the named projection.  The median itself is put
in arm zero by convention; all three resulting arm coordinates are still
zero. -/
inductive ProjectionArm where
  | arm0
  | arm1
  | arm2
  deriving DecidableEq, Repr, Fintype

/-- Actual named median/projection topology for three distinct ports and one
named vertex in a fixed even component.  Every field is canonical-path
membership in the supplied `PosIntTree`; there are no assumed coordinate
equalities in this structure. -/
structure PathFrame (T : PosIntTree n) (C : EvenComponent T)
    (p0 p1 p2 x : ComponentVertex T C) where
  ports_ne01 : p0 ≠ p1
  ports_ne02 : p0 ≠ p2
  ports_ne12 : p1 ≠ p2
  median : ComponentVertex T C
  projection : ComponentVertex T C
  median_on_01 : median.1 ∈ (T.path p0.1 p1.1).1.support
  median_on_02 : median.1 ∈ (T.path p0.1 p2.1).1.support
  median_on_12 : median.1 ∈ (T.path p1.1 p2.1).1.support
  projection_on_x0 : projection.1 ∈ (T.path x.1 p0.1).1.support
  projection_on_x1 : projection.1 ∈ (T.path x.1 p1.1).1.support
  projection_on_x2 : projection.1 ∈ (T.path x.1 p2.1).1.support
  arm : ProjectionArm
  arm_topology :
    match arm with
    | .arm0 =>
        projection.1 ∈ (T.path median.1 p0.1).1.support ∧
        median.1 ∈ (T.path projection.1 p1.1).1.support ∧
        median.1 ∈ (T.path projection.1 p2.1).1.support
    | .arm1 =>
        projection.1 ∈ (T.path median.1 p1.1).1.support ∧
        median.1 ∈ (T.path projection.1 p0.1).1.support ∧
        median.1 ∈ (T.path projection.1 p2.1).1.support
    | .arm2 =>
        projection.1 ∈ (T.path median.1 p2.1).1.support ∧
        median.1 ∈ (T.path projection.1 p0.1).1.support ∧
        median.1 ∈ (T.path projection.1 p1.1).1.support

/-- Halved distance splits exactly at an actual named path vertex in one even
component. -/
theorem rho_split_at_path_vertex (T : PosIntTree n) {C : EvenComponent T}
    {u v z : ComponentVertex T C}
    (hz : z.1 ∈ (T.path u.1 v.1).1.support) :
    rho T u v = rho T u z + rho T z v := by
  have hsplit := PosIntTree.dist_split_at_path_vertex T hz
  rw [dist_eq_two_mul_rho T u v, dist_eq_two_mul_rho T u z,
    dist_eq_two_mul_rho T z v] at hsplit
  omega

/-! ### The named median and the named nearest skeleton point -/

private theorem exists_first_common
    (T : PosIntTree n) {u v r : Fin n}
    (p : T.graph.Walk u r) (q : T.graph.Walk v r) :
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
        rcases (by simpa using hx :
            x = u ∨ x ∈ (p.takeUntil z hzp).support) with rfl | hxtail
        · exact (hu hxq).elim
        · exact hfirst x hxtail hxq

/-- The three canonical anchor paths in an actual tree have an actual named
common vertex.  This is the graph median, not a hidden point in a geometric
realization. -/
private theorem exists_named_three_median (T : PosIntTree n)
    (p0 p1 p2 : Fin n) :
    ∃ m : Fin n,
      m ∈ (T.path p0 p1).1.support ∧
      m ∈ (T.path p0 p2).1.support ∧
      m ∈ (T.path p1 p2).1.support := by
  classical
  let p := T.path p1 p0
  let q := T.path p2 p0
  obtain ⟨m, hmp, hmq, hfirst⟩ :=
    exists_first_common T p.1 q.1
  let a := p.1.takeUntil m hmp
  let b := q.1.takeUntil m hmq
  have ha : a.IsPath := p.2.takeUntil hmp
  have hb : b.IsPath := q.2.takeUntil hmq
  have hdisjoint : a.support.Disjoint b.reverse.support.tail := by
    rw [List.disjoint_left]
    intro x hxa hxb
    have hxbq : x ∈ q.1.support := by
      apply q.1.support_takeUntil_subset hmq
      have : x ∈ b.reverse.support := List.mem_of_mem_tail hxb
      simpa [b] using this
    have hxm : x = m := hfirst x (by simpa [a] using hxa) hxbq
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
  have hroute_eq :
      (⟨route, hroute⟩ : T.graph.Path p1 p2) = T.path p1 p2 :=
    T.path_unique _
  have hmroute : m ∈ route.support := by
    simp [route, a]
  have hm12 : m ∈ (T.path p1 p2).1.support := by
    rw [← hroute_eq]
    exact hmroute
  have hmp01 : m ∈ (T.path p0 p1).1.support := by
    let rp : T.graph.Path p0 p1 := ⟨p.1.reverse, p.2.reverse⟩
    have hrp : rp = T.path p0 p1 := T.path_unique rp
    rw [← hrp]
    simpa [rp, p] using hmp
  have hmp02 : m ∈ (T.path p0 p2).1.support := by
    let rq : T.graph.Path p0 p2 := ⟨q.1.reverse, q.2.reverse⟩
    have hrq : rq = T.path p0 p2 := T.path_unique rq
    rw [← hrq]
    simpa [rq, q] using hmq
  exact ⟨m, hmp01, hmp02, hm12⟩

/-- The actual subgraph spanned by the three anchors. -/
noncomputable def portSkeleton (T : PosIntTree n) (p0 p1 p2 : Fin n) :
    T.graph.Subgraph :=
  (T.path p0 p1).1.toSubgraph ⊔ (T.path p0 p2).1.toSubgraph

private theorem mem_portSkeleton_iff (T : PosIntTree n)
    (p0 p1 p2 v : Fin n) :
    v ∈ (portSkeleton T p0 p1 p2).verts ↔
      v ∈ (T.path p0 p1).1.support ∨
      v ∈ (T.path p0 p2).1.support := by
  simp [portSkeleton]

private theorem portSkeleton_connected (T : PosIntTree n)
    (p0 p1 p2 : Fin n) :
    (portSkeleton T p0 p1 p2).Connected := by
  apply (T.path p0 p1).1.toSubgraph_connected.sup
    (T.path p0 p2).1.toSubgraph_connected
  refine ⟨p0, ?_⟩
  simp

private theorem toPath_toSubgraph_le {G : SimpleGraph (Fin n)}
    {u v : Fin n} (w : G.Walk u v) :
    w.toPath.1.toSubgraph ≤ w.toSubgraph := by
  constructor
  · intro z hz
    rw [SimpleGraph.Walk.mem_verts_toSubgraph] at hz ⊢
    exact w.support_toPath_subset hz
  · intro a b hab
    rw [← SimpleGraph.Subgraph.mem_edgeSet] at hab ⊢
    rw [SimpleGraph.Walk.mem_edges_toSubgraph] at hab ⊢
    exact w.edges_toPath_subset hab

/-- Connected subgraphs of a tree are geodesically convex. -/
private theorem canonicalPath_toSubgraph_le (T : PosIntTree n)
    {H : T.graph.Subgraph} (hH : H.Connected) {u v : Fin n}
    (hu : u ∈ H.verts) (hv : v ∈ H.verts) :
    (T.path u v).1.toSubgraph ≤ H := by
  have hp := hH.preconnected
  rw [SimpleGraph.Subgraph.preconnected_iff_forall_exists_walk_subgraph] at hp
  obtain ⟨w, hw⟩ := hp hu hv
  have hpath : w.toPath = T.path u v := T.path_unique w.toPath
  rw [← hpath]
  exact (toPath_toSubgraph_le w).trans hw

private theorem path_support_comm (T : PosIntTree n) (u v x : Fin n) :
    x ∈ (T.path u v).1.support ↔ x ∈ (T.path v u).1.support := by
  let rp : T.graph.Path v u :=
    ⟨(T.path u v).1.reverse, (T.path u v).2.reverse⟩
  have hrp : rp = T.path v u := T.path_unique rp
  rw [← hrp]
  simp [rp]

/-- Linear order along one canonical path. -/
private theorem path_arm_cases (T : PosIntTree n) {a b m q : Fin n}
    (hm : m ∈ (T.path a b).1.support)
    (hq : q ∈ (T.path a b).1.support) :
    (q ∈ (T.path m a).1.support ∧
      m ∈ (T.path q b).1.support) ∨
    (q ∈ (T.path m b).1.support ∧
      m ∈ (T.path q a).1.support) := by
  classical
  let p := (T.path a b).1
  let iq := (p.takeUntil q hq).length
  let im := (p.takeUntil m hm).length
  have hq_get : p.getVert iq = q := by
    simpa [iq] using p.getVert_length_takeUntil hq
  have hm_get : p.getVert im = m := by
    simpa [im] using p.getVert_length_takeUntil hm
  rcases le_total iq im with hiq | him
  · have hq_take_m : q ∈ (p.takeUntil m hm).support := by
      have hget : (p.takeUntil m hm).getVert iq = q := by
        rw [p.getVert_takeUntil hm]
        · exact hq_get
        · simpa [im] using hiq
      rw [← hget]
      exact SimpleGraph.Walk.getVert_mem_support _ _
    have hq_ma : q ∈ (T.path m a).1.support := by
      let am : T.graph.Path a m :=
        ⟨p.takeUntil m hm, (T.path a b).2.takeUntil hm⟩
      have ham : am = T.path a m := T.path_unique am
      rw [path_support_comm T m a q, ← ham]
      exact hq_take_m
    have hm_drop_q : m ∈ (p.dropUntil q hq).support := by
      have hmP : m ∈ p.support := by simpa [p] using hm
      have hmSplit := hmP
      rw [← p.take_spec hq, SimpleGraph.Walk.mem_support_append_iff] at hmSplit
      rcases hmSplit with hm_take | hm_drop
      · by_cases hqm : q = m
        · rw [← hqm]
          exact (p.dropUntil q hq).start_mem_support
        · have hnot :=
            p.notMem_support_takeUntil_support_takeUntil_subset hqm hmP hq_take_m
          exact (hnot hm_take).elim
      · exact hm_drop
    have hm_qb : m ∈ (T.path q b).1.support := by
      let qb : T.graph.Path q b :=
        ⟨p.dropUntil q hq, (T.path a b).2.dropUntil hq⟩
      have hqb : qb = T.path q b := T.path_unique qb
      rw [← hqb]
      exact hm_drop_q
    exact Or.inl ⟨hq_ma, hm_qb⟩
  · have hm_take_q : m ∈ (p.takeUntil q hq).support := by
      have hget : (p.takeUntil q hq).getVert im = m := by
        rw [p.getVert_takeUntil hq]
        · exact hm_get
        · simpa [iq] using him
      rw [← hget]
      exact SimpleGraph.Walk.getVert_mem_support _ _
    have hm_qa : m ∈ (T.path q a).1.support := by
      let aq : T.graph.Path a q :=
        ⟨p.takeUntil q hq, (T.path a b).2.takeUntil hq⟩
      have haq : aq = T.path a q := T.path_unique aq
      rw [path_support_comm T q a m, ← haq]
      exact hm_take_q
    have hq_drop_m : q ∈ (p.dropUntil m hm).support := by
      have hqP : q ∈ p.support := by simpa [p] using hq
      have hqSplit := hqP
      rw [← p.take_spec hm, SimpleGraph.Walk.mem_support_append_iff] at hqSplit
      rcases hqSplit with hq_take | hq_drop
      · by_cases hqm : m = q
        · rw [← hqm]
          exact (p.dropUntil m hm).start_mem_support
        · have hnot :=
            p.notMem_support_takeUntil_support_takeUntil_subset hqm hqP hm_take_q
          exact (hnot hq_take).elim
      · exact hq_drop
    have hq_mb : q ∈ (T.path m b).1.support := by
      let mb : T.graph.Path m b :=
        ⟨p.dropUntil m hm, (T.path a b).2.dropUntil hm⟩
      have hmb : mb = T.path m b := T.path_unique mb
      rw [← hmb]
      exact hq_drop_m
    exact Or.inr ⟨hq_mb, hm_qa⟩

private theorem dist_pos_of_ne (T : PosIntTree n) (hL : IsLeech T)
    {u v : Fin n} (huv : u ≠ v) : 0 < T.dist u v := by
  rw [← T.pairDist_pairOfDistinct u v huv]
  exact hL.pairDist_pos _

/-- If `q` lies between `m` and `a`, and `m` lies between `a` and `b`,
then the path from `q` to `b` passes through `m`. -/
private theorem extend_through_path (T : PosIntTree n) (hL : IsLeech T)
    {q m a b : Fin n}
    (hqm : q ∈ (T.path m a).1.support)
    (hmab : m ∈ (T.path a b).1.support) :
    m ∈ (T.path q b).1.support := by
  have hma : m ∈ (T.path a m).1.support := by simp
  have hqam : q ∈ (T.path a m).1.support := by
    rwa [path_support_comm T a m q]
  have hqab : q ∈ (T.path a b).1.support := by
    let am : T.graph.Path a m :=
      ⟨(T.path a b).1.takeUntil m hmab,
        (T.path a b).2.takeUntil hmab⟩
    have ham : am = T.path a m := T.path_unique am
    have : q ∈ am.1.support := by simpa [ham] using hqam
    exact (T.path a b).1.support_takeUntil_subset hmab (by simpa [am] using this)
  rcases path_arm_cases T hmab hqab with hgood | hwrong
  · exact hgood.2
  · have h1 := PosIntTree.dist_split_at_path_vertex T hqm
    have h2 := PosIntTree.dist_split_at_path_vertex T hwrong.2
    have hzero : T.dist m q = 0 := by
      rw [T.dist_comm q m] at h2
      omega
    by_cases hmq : m = q
    · subst q
      simp
    · have hp := dist_pos_of_ne T hL hmq
      omega

/-- Every vertex of an actual Leech component has a named median/projection
frame.  The projection is constructed as the closest named vertex of the
actual connected port skeleton; convexity and positivity force it onto all
three vertex-to-port paths. -/
theorem exists_pathFrame (T : PosIntTree n) (hL : IsLeech T)
    {C : EvenComponent T} (p0 p1 p2 x : ComponentVertex T C)
    (hne01 : p0 ≠ p1) (hne02 : p0 ≠ p2) (hne12 : p1 ≠ p2) :
    Nonempty (PathFrame T C p0 p1 p2 x) := by
  classical
  obtain ⟨m, hm01, hm02, hm12⟩ :=
    exists_named_three_median T p0.1 p1.1 p2.1
  have hmC : componentOf T m = C := by
    calc
      componentOf T m = componentOf T p0.1 :=
        componentOf_eq_of_path_all_even T (by
          intro e he
          have hsub := pathEdges_suffix_subset T
            (show m ∈ (T.path p1.1 p0.1).1.support by
              rwa [path_support_comm T p1.1 p0.1 m]) he
          exact path_edge_even_of_component_eq T
            (p1.2.trans p0.2.symm) hsub)
      _ = C := p0.2
  let mC : ComponentVertex T C := ⟨m, hmC⟩
  let H := portSkeleton T p0.1 p1.1 p2.1
  let S : Finset (Fin n) := Finset.univ.filter fun v => v ∈ H.verts
  have hp0H : p0.1 ∈ H.verts := by
    exact (mem_portSkeleton_iff T p0.1 p1.1 p2.1 p0.1).2
      (Or.inl (T.path p0.1 p1.1).1.start_mem_support)
  have hSne : S.Nonempty := ⟨p0.1, by simp [S, hp0H]⟩
  obtain ⟨q, hqS, hqmin⟩ :=
    Finset.exists_min_image S (fun z => T.dist x.1 z) hSne
  have hqH : q ∈ H.verts := (Finset.mem_filter.mp hqS).2
  have hHconn : H.Connected := by
    simpa [H] using portSkeleton_connected T p0.1 p1.1 p2.1
  have hq_path (p : Fin n) (hpH : p ∈ H.verts) :
      q ∈ (T.path x.1 p).1.support := by
    obtain ⟨z, hzx, hzq, hgate, _, _⟩ :=
      PosIntTree.exists_root_gate T p x.1 q
    have hpath_le := canonicalPath_toSubgraph_le T hHconn hqH hpH
    have hzH : z ∈ H.verts :=
      hpath_le.1 ((SimpleGraph.Walk.mem_verts_toSubgraph _).2 hzq)
    by_contra hnot
    have hzq_ne : z ≠ q := by
      intro h
      subst z
      exact hnot hzx
    have hxsplit := PosIntTree.dist_split_at_path_vertex T hzx
    have hqsplit := PosIntTree.dist_split_at_path_vertex T hzq
    have hdecomp : T.dist x.1 q = T.dist x.1 z + T.dist z q := by
      rw [T.dist_comm q z] at hqsplit
      omega
    have hstrict : T.dist x.1 z < T.dist x.1 q := by
      have hpos := dist_pos_of_ne T hL hzq_ne
      omega
    have hzS : z ∈ S := by simp [S, hzH]
    exact (Nat.not_lt_of_ge (hqmin z hzS)) hstrict
  have hp0H' : p0.1 ∈ H.verts := hp0H
  have hp1H : p1.1 ∈ H.verts := by
    exact (mem_portSkeleton_iff T p0.1 p1.1 p2.1 p1.1).2
      (Or.inl (T.path p0.1 p1.1).1.end_mem_support)
  have hp2H : p2.1 ∈ H.verts := by
    exact (mem_portSkeleton_iff T p0.1 p1.1 p2.1 p2.1).2
      (Or.inr (T.path p0.1 p2.1).1.end_mem_support)
  have hqx0 := hq_path p0.1 hp0H'
  have hqx1 := hq_path p1.1 hp1H
  have hqx2 := hq_path p2.1 hp2H
  have hqC : componentOf T q = C := by
    rcases (mem_portSkeleton_iff T p0.1 p1.1 p2.1 q).1 hqH with hq01 | hq02
    · calc
        componentOf T q = componentOf T p1.1 :=
          componentOf_eq_of_path_all_even T (by
            intro e he
            exact path_edge_even_of_component_eq T (p0.2.trans p1.2.symm)
              (pathEdges_suffix_subset T hq01 he))
        _ = C := p1.2
    · calc
        componentOf T q = componentOf T p2.1 :=
          componentOf_eq_of_path_all_even T (by
            intro e he
            exact path_edge_even_of_component_eq T (p0.2.trans p2.2.symm)
              (pathEdges_suffix_subset T hq02 he))
        _ = C := p2.2
  let qC : ComponentVertex T C := ⟨q, hqC⟩
  have hne01' : p0.1 ≠ p1.1 := fun h => hne01 (Subtype.ext h)
  have hne02' : p0.1 ≠ p2.1 := fun h => hne02 (Subtype.ext h)
  have hne12' : p1.1 ≠ p2.1 := fun h => hne12 (Subtype.ext h)
  rcases (mem_portSkeleton_iff T p0.1 p1.1 p2.1 q).1 hqH with hq01 | hq02
  · rcases path_arm_cases T hm01 hq01 with hq0 | hq1
    · have hmq2 := extend_through_path T hL hq0.1 hm02
      exact ⟨{
        ports_ne01 := hne01
        ports_ne02 := hne02
        ports_ne12 := hne12
        median := mC
        projection := qC
        median_on_01 := hm01
        median_on_02 := hm02
        median_on_12 := hm12
        projection_on_x0 := hqx0
        projection_on_x1 := hqx1
        projection_on_x2 := hqx2
        arm := .arm0
        arm_topology := ⟨hq0.1, hq0.2, hmq2⟩ }⟩
    · have hm10 : m ∈ (T.path p1.1 p0.1).1.support := by
        rwa [path_support_comm T p1.1 p0.1 m]
      have hmq0 := extend_through_path T hL hq1.1 hm10
      have hmq2 := extend_through_path T hL hq1.1 hm12
      exact ⟨{
        ports_ne01 := hne01
        ports_ne02 := hne02
        ports_ne12 := hne12
        median := mC
        projection := qC
        median_on_01 := hm01
        median_on_02 := hm02
        median_on_12 := hm12
        projection_on_x0 := hqx0
        projection_on_x1 := hqx1
        projection_on_x2 := hqx2
        arm := .arm1
        arm_topology := ⟨hq1.1, hmq0, hmq2⟩ }⟩
  · rcases path_arm_cases T hm02 hq02 with hq0 | hq2
    · have hmq1 := extend_through_path T hL hq0.1 hm01
      exact ⟨{
        ports_ne01 := hne01
        ports_ne02 := hne02
        ports_ne12 := hne12
        median := mC
        projection := qC
        median_on_01 := hm01
        median_on_02 := hm02
        median_on_12 := hm12
        projection_on_x0 := hqx0
        projection_on_x1 := hqx1
        projection_on_x2 := hqx2
        arm := .arm0
        arm_topology := ⟨hq0.1, hmq1, hq0.2⟩ }⟩
    · have hm20 : m ∈ (T.path p2.1 p0.1).1.support := by
        rwa [path_support_comm T p2.1 p0.1 m]
      have hmq0 := extend_through_path T hL hq2.1 hm20
      have hm21 : m ∈ (T.path p2.1 p1.1).1.support := by
        rwa [path_support_comm T p2.1 p1.1 m]
      have hmq1 := extend_through_path T hL hq2.1 hm21
      exact ⟨{
        ports_ne01 := hne01
        ports_ne02 := hne02
        ports_ne12 := hne12
        median := mC
        projection := qC
        median_on_01 := hm01
        median_on_02 := hm02
        median_on_12 := hm12
        projection_on_x0 := hqx0
        projection_on_x1 := hqx1
        projection_on_x2 := hqx2
        arm := .arm2
        arm_topology := ⟨hq2.1, hmq0, hmq1⟩ }⟩

/-- The exact forward coordinate bundle.  `g0,g1,g2` are the integral values
whose doubles are the three signed half-sum numerators. -/
structure ForwardCoordinates (T : PosIntTree n) (C : EvenComponent T)
    (p0 p1 p2 x : ComponentVertex T C) where
  median : ComponentVertex T C
  projection : ComponentVertex T C
  A0 : ℕ
  A1 : ℕ
  A2 : ℕ
  h : ℕ
  t0 : ℕ
  t1 : ℕ
  t2 : ℕ
  g0 : ℕ
  g1 : ℕ
  g2 : ℕ
  A0_eq : A0 = rho T median p0
  A1_eq : A1 = rho T median p1
  A2_eq : A2 = rho T median p2
  h_eq : h = rho T projection x
  arm01 : rho T p0 p1 = A0 + A1
  arm02 : rho T p0 p2 = A0 + A2
  arm12 : rho T p1 p2 = A1 + A2
  atMostOne :
    (t1 = 0 ∧ t2 = 0) ∨ (t0 = 0 ∧ t2 = 0) ∨ (t0 = 0 ∧ t1 = 0)
  t0_le : t0 ≤ A0
  t1_le : t1 ≤ A1
  t2_le : t2 ≤ A2
  projection0 : rho T projection p0 + 2 * t0 = A0 + t0 + t1 + t2
  projection1 : rho T projection p1 + 2 * t1 = A1 + t0 + t1 + t2
  projection2 : rho T projection p2 + 2 * t2 = A2 + t0 + t1 + t2
  anchor0 : rho T p0 x = h + rho T projection p0
  anchor1 : rho T p1 x = h + rho T projection p1
  anchor2 : rho T p2 x = h + rho T projection p2
  g0_eq : g0 = h + t0
  g1_eq : g1 = h + t1
  g2_eq : g2 = h + t2
  g0_balance : rho T p1 x + rho T p2 x = rho T p1 p2 + 2 * g0
  g1_balance : rho T p0 x + rho T p2 x = rho T p0 p2 + 2 * g1
  g2_balance : rho T p0 x + rho T p1 x = rho T p0 p1 + 2 * g2
  height_is_min : min g0 (min g1 g2) = h

/-- The audited forward formulas, derived solely from an actual path frame. -/
theorem forwardCoordinates_of_pathFrame (T : PosIntTree n)
    {C : EvenComponent T} {p0 p1 p2 x : ComponentVertex T C}
    (F : PathFrame T C p0 p1 p2 x) :
    Nonempty (ForwardCoordinates T C p0 p1 p2 x) := by
  let A0 := rho T F.median p0
  let A1 := rho T F.median p1
  let A2 := rho T F.median p2
  let h := rho T F.projection x
  let t := rho T F.median F.projection

  have h01 := rho_split_at_path_vertex T F.median_on_01
  have h02 := rho_split_at_path_vertex T F.median_on_02
  have h12 := rho_split_at_path_vertex T F.median_on_12
  have hx0 := rho_split_at_path_vertex T F.projection_on_x0
  have hx1 := rho_split_at_path_vertex T F.projection_on_x1
  have hx2 := rho_split_at_path_vertex T F.projection_on_x2

  have harm0 : F.arm = .arm0 →
      rho T F.median p0 = rho T F.median F.projection +
        rho T F.projection p0 ∧
      rho T F.projection p1 = rho T F.projection F.median +
        rho T F.median p1 ∧
      rho T F.projection p2 = rho T F.projection F.median +
        rho T F.median p2 := by
    intro ha
    have htop := F.arm_topology
    rw [ha] at htop
    rcases htop with ⟨hq0, hm1, hm2⟩
    exact ⟨rho_split_at_path_vertex T hq0,
      rho_split_at_path_vertex T hm1,
      rho_split_at_path_vertex T hm2⟩
  have harm1 : F.arm = .arm1 →
      rho T F.median p1 = rho T F.median F.projection +
        rho T F.projection p1 ∧
      rho T F.projection p0 = rho T F.projection F.median +
        rho T F.median p0 ∧
      rho T F.projection p2 = rho T F.projection F.median +
        rho T F.median p2 := by
    intro ha
    have htop := F.arm_topology
    rw [ha] at htop
    rcases htop with ⟨hq1, hm0, hm2⟩
    exact ⟨rho_split_at_path_vertex T hq1,
      rho_split_at_path_vertex T hm0,
      rho_split_at_path_vertex T hm2⟩
  have harm2 : F.arm = .arm2 →
      rho T F.median p2 = rho T F.median F.projection +
        rho T F.projection p2 ∧
      rho T F.projection p0 = rho T F.projection F.median +
        rho T F.median p0 ∧
      rho T F.projection p1 = rho T F.projection F.median +
        rho T F.median p1 := by
    intro ha
    have htop := F.arm_topology
    rw [ha] at htop
    rcases htop with ⟨hq2, hm0, hm1⟩
    exact ⟨rho_split_at_path_vertex T hq2,
      rho_split_at_path_vertex T hm0,
      rho_split_at_path_vertex T hm1⟩

  cases ha : F.arm with
  | arm0 =>
      obtain ⟨ha0, ha1, ha2⟩ := harm0 ha
      refine ⟨{
        median := F.median
        projection := F.projection
        A0 := A0, A1 := A1, A2 := A2, h := h
        t0 := t, t1 := 0, t2 := 0
        g0 := h + t, g1 := h, g2 := h
        A0_eq := rfl, A1_eq := rfl, A2_eq := rfl, h_eq := rfl
        arm01 := by simpa [A0, A1, rho_comm T] using h01
        arm02 := by simpa [A0, A2, rho_comm T] using h02
        arm12 := by simpa [A1, A2, rho_comm T] using h12
        atMostOne := Or.inl ⟨rfl, rfl⟩
        t0_le := by simpa [A0, t] using Nat.le.intro ha0.symm
        t1_le := Nat.zero_le _
        t2_le := Nat.zero_le _
        projection0 := by simp [A0, t]; omega
        projection1 := by simp [A1, t, rho_comm T] at ha1 ⊢; omega
        projection2 := by simp [A2, t, rho_comm T] at ha2 ⊢; omega
        anchor0 := by simpa [h, rho_comm T] using hx0
        anchor1 := by simpa [h, rho_comm T] using hx1
        anchor2 := by simpa [h, rho_comm T] using hx2
        g0_eq := rfl, g1_eq := by simp, g2_eq := by simp
        g0_balance := by
          simp [h, t, rho_comm T] at h12 hx1 hx2 ha1 ha2 ⊢
          omega
        g1_balance := by
          simp [h, rho_comm T] at h02 hx0 hx2 ha0 ha2 ⊢
          omega
        g2_balance := by
          simp [h, rho_comm T] at h01 hx0 hx1 ha0 ha1 ⊢
          omega
        height_is_min := by simp }⟩
  | arm1 =>
      obtain ⟨ha1, ha0, ha2⟩ := harm1 ha
      refine ⟨{
        median := F.median
        projection := F.projection
        A0 := A0, A1 := A1, A2 := A2, h := h
        t0 := 0, t1 := t, t2 := 0
        g0 := h, g1 := h + t, g2 := h
        A0_eq := rfl, A1_eq := rfl, A2_eq := rfl, h_eq := rfl
        arm01 := by simpa [A0, A1, rho_comm T] using h01
        arm02 := by simpa [A0, A2, rho_comm T] using h02
        arm12 := by simpa [A1, A2, rho_comm T] using h12
        atMostOne := Or.inr (Or.inl ⟨rfl, rfl⟩)
        t0_le := Nat.zero_le _
        t1_le := by simpa [A1, t] using Nat.le.intro ha1.symm
        t2_le := Nat.zero_le _
        projection0 := by simp [A0, t, rho_comm T] at ha0 ⊢; omega
        projection1 := by simp [A1, t]; omega
        projection2 := by simp [A2, t, rho_comm T] at ha2 ⊢; omega
        anchor0 := by simpa [h, rho_comm T] using hx0
        anchor1 := by simpa [h, rho_comm T] using hx1
        anchor2 := by simpa [h, rho_comm T] using hx2
        g0_eq := by simp, g1_eq := rfl, g2_eq := by simp
        g0_balance := by
          simp [h, rho_comm T] at h12 hx1 hx2 ha1 ha2 ⊢
          omega
        g1_balance := by
          simp [h, t, rho_comm T] at h02 hx0 hx2 ha0 ha2 ⊢
          omega
        g2_balance := by
          simp [h, rho_comm T] at h01 hx0 hx1 ha0 ha1 ⊢
          omega
        height_is_min := by simp }⟩
  | arm2 =>
      obtain ⟨ha2, ha0, ha1⟩ := harm2 ha
      refine ⟨{
        median := F.median
        projection := F.projection
        A0 := A0, A1 := A1, A2 := A2, h := h
        t0 := 0, t1 := 0, t2 := t
        g0 := h, g1 := h, g2 := h + t
        A0_eq := rfl, A1_eq := rfl, A2_eq := rfl, h_eq := rfl
        arm01 := by simpa [A0, A1, rho_comm T] using h01
        arm02 := by simpa [A0, A2, rho_comm T] using h02
        arm12 := by simpa [A1, A2, rho_comm T] using h12
        atMostOne := Or.inr (Or.inr ⟨rfl, rfl⟩)
        t0_le := Nat.zero_le _
        t1_le := Nat.zero_le _
        t2_le := by simpa [A2, t] using Nat.le.intro ha2.symm
        projection0 := by simp [A0, t, rho_comm T] at ha0 ⊢; omega
        projection1 := by simp [A1, t, rho_comm T] at ha1 ⊢; omega
        projection2 := by simp [A2, t]; omega
        anchor0 := by simpa [h, rho_comm T] using hx0
        anchor1 := by simpa [h, rho_comm T] using hx1
        anchor2 := by simpa [h, rho_comm T] using hx2
        g0_eq := by simp, g1_eq := by simp, g2_eq := rfl
        g0_balance := by
          simp [h, rho_comm T] at h12 hx1 hx2 ha1 ha2 ⊢
          omega
        g1_balance := by
          simp [h, rho_comm T] at h02 hx0 hx2 ha0 ha2 ⊢
          omega
        g2_balance := by
          simp [h, t, rho_comm T] at h01 hx0 hx1 ha0 ha1 ⊢
          omega
        height_is_min := by simp }⟩

/-- Queryable actual-component forward endpoint: three distinct named anchors
give an exact median/projection/skeleton/fibre coordinate row for every named
vertex of the actual component. -/
theorem exists_forwardCoordinates (T : PosIntTree n) (hL : IsLeech T)
    {C : EvenComponent T} (p0 p1 p2 : ComponentVertex T C)
    (hne01 : p0 ≠ p1) (hne02 : p0 ≠ p2) (hne12 : p1 ≠ p2) :
    ∀ x : ComponentVertex T C,
      Nonempty (ForwardCoordinates T C p0 p1 p2 x) := by
  intro x
  obtain ⟨F⟩ := exists_pathFrame T hL p0 p1 p2 x hne01 hne02 hne12
  exact forwardCoordinates_of_pathFrame T F

namespace ForwardCoordinates

variable {T : PosIntTree n} {C : EvenComponent T}
  {p0 p1 p2 x : ComponentVertex T C}

/-- Signed recovery of the first `g` coordinate. -/
theorem int_g0_equation (F : ForwardCoordinates T C p0 p1 p2 x) :
    2 * (F.g0 : ℤ) =
      (rho T p1 x : ℤ) + (rho T p2 x : ℤ) -
        (rho T p1 p2 : ℤ) := by
  have h := F.g0_balance
  omega

theorem int_g1_equation (F : ForwardCoordinates T C p0 p1 p2 x) :
    2 * (F.g1 : ℤ) =
      (rho T p0 x : ℤ) + (rho T p2 x : ℤ) -
        (rho T p0 p2 : ℤ) := by
  have h := F.g1_balance
  omega

theorem int_g2_equation (F : ForwardCoordinates T C p0 p1 p2 x) :
    2 * (F.g2 : ℤ) =
      (rho T p0 x : ℤ) + (rho T p1 x : ℤ) -
        (rho T p0 p1 : ℤ) := by
  have h := F.g2_balance
  omega

/-- The indexed anchor-distance triple uniquely recovers `g0,g1,g2`, hence
the minimum height and the three arm coordinates. -/
theorem coordinates_unique (F G : ForwardCoordinates T C p0 p1 p2 x) :
    F.g0 = G.g0 ∧ F.g1 = G.g1 ∧ F.g2 = G.g2 ∧
      F.h = G.h ∧ F.t0 = G.t0 ∧ F.t1 = G.t1 ∧ F.t2 = G.t2 := by
  have hg0 : F.g0 = G.g0 := by
    have hF := F.g0_balance
    have hG := G.g0_balance
    omega
  have hg1 : F.g1 = G.g1 := by
    have hF := F.g1_balance
    have hG := G.g1_balance
    omega
  have hg2 : F.g2 = G.g2 := by
    have hF := F.g2_balance
    have hG := G.g2_balance
    omega
  have hh : F.h = G.h := by
    rw [← F.height_is_min, ← G.height_is_min, hg0, hg1, hg2]
  refine ⟨hg0, hg1, hg2, hh, ?_, ?_, ?_⟩
  · have hF := F.g0_eq; have hG := G.g0_eq; omega
  · have hF := F.g1_eq; have hG := G.g1_eq; omega
  · have hF := F.g2_eq; have hG := G.g2_eq; omega

end ForwardCoordinates

/-! ## Scoped parent converse -/

/-- Coordinate rows together with the exact named median/projection closure
used by the converse.  The formula is subtraction-free and therefore cannot
silently truncate a negative natural expression. -/
structure ClosedCoordinateRows (n : ℕ) where
  port0 : Fin n
  port1 : Fin n
  port2 : Fin n
  ports_ne01 : port0 ≠ port1
  ports_ne02 : port0 ≠ port2
  ports_ne12 : port1 ≠ port2
  median : Fin n
  projection : Fin n → Fin n
  A0 : ℕ
  A1 : ℕ
  A2 : ℕ
  height : Fin n → ℕ
  t0 : Fin n → ℕ
  t1 : Fin n → ℕ
  t2 : Fin n → ℕ
  anchorDistance : Fin n → Fin 3 → ℕ
  atMostOne : ∀ x,
    (t1 x = 0 ∧ t2 x = 0) ∨ (t0 x = 0 ∧ t2 x = 0) ∨
      (t0 x = 0 ∧ t1 x = 0)
  t0_le : ∀ x, t0 x ≤ A0
  t1_le : ∀ x, t1 x ≤ A1
  t2_le : ∀ x, t2 x ≤ A2
  row0 : ∀ x, anchorDistance x 0 + 2 * t0 x =
    height x + A0 + t0 x + t1 x + t2 x
  row1 : ∀ x, anchorDistance x 1 + 2 * t1 x =
    height x + A1 + t0 x + t1 x + t2 x
  row2 : ∀ x, anchorDistance x 2 + 2 * t2 x =
    height x + A2 + t0 x + t1 x + t2 x
  median_height : height median = 0
  median_t0 : t0 median = 0
  median_t1 : t1 median = 0
  median_t2 : t2 median = 0
  port0_height : height port0 = 0
  port0_t0 : t0 port0 = A0
  port0_t1 : t1 port0 = 0
  port0_t2 : t2 port0 = 0
  port1_height : height port1 = 0
  port1_t0 : t0 port1 = 0
  port1_t1 : t1 port1 = A1
  port1_t2 : t2 port1 = 0
  port2_height : height port2 = 0
  port2_t0 : t0 port2 = 0
  port2_t1 : t1 port2 = 0
  port2_t2 : t2 port2 = A2
  projection_height : ∀ x, height (projection x) = 0
  projection_t0 : ∀ x, t0 (projection x) = t0 x
  projection_t1 : ∀ x, t1 (projection x) = t1 x
  projection_t2 : ∀ x, t2 (projection x) = t2 x
  projection_unique : ∀ x z, height z = 0 →
    t0 z = t0 x → t1 z = t1 x → t2 z = t2 x → z = projection x

/-- A scoped parent choice: positive-height vertices choose a strictly lower
same-fibre parent; height-zero nonmedian vertices choose a strictly lower
point on their unique arm. -/
structure ParentChoice {n : ℕ} (R : ClosedCoordinateRows n) where
  parent : Fin n → Fin n
  parent_median : parent R.median = R.median
  same_fibre : ∀ x, x ≠ R.median → R.height x ≠ 0 →
    R.t0 (parent x) = R.t0 x ∧ R.t1 (parent x) = R.t1 x ∧
      R.t2 (parent x) = R.t2 x
  lower_height : ∀ x, x ≠ R.median → R.height x ≠ 0 →
    R.height (parent x) < R.height x
  skeleton_height : ∀ x, x ≠ R.median → R.height x = 0 →
    R.height (parent x) = 0
  skeleton_same_arm : ∀ x, x ≠ R.median → R.height x = 0 →
    ((0 < R.t0 x ∧ R.t0 (parent x) < R.t0 x ∧
        R.t1 (parent x) = 0 ∧ R.t2 (parent x) = 0) ∨
     (0 < R.t1 x ∧ R.t1 (parent x) < R.t1 x ∧
        R.t0 (parent x) = 0 ∧ R.t2 (parent x) = 0) ∨
     (0 < R.t2 x ∧ R.t2 (parent x) < R.t2 x ∧
        R.t0 (parent x) = 0 ∧ R.t1 (parent x) = 0))

namespace ParentChoice

variable {N : ℕ} {R : ClosedCoordinateRows N} (P : ParentChoice R)

/-- Distance from the named median in the decoded rooted parent tree. -/
def rootDepth (_P : ParentChoice R) (x : Fin N) : ℕ :=
  R.height x + R.t0 x + R.t1 x + R.t2 x

/-- One directed step toward the named median. -/
def Step (x y : Fin N) : Prop := x ≠ R.median ∧ P.parent x = y

/-- Reflexive transitive parent ancestry. -/
abbrev Reaches (x y : Fin N) : Prop := Relation.ReflTransGen P.Step x y

/-- Every nonmedian parent step is strictly descending.  This is the exact
cycle-prevention invariant of the optional-parent construction. -/
theorem rootDepth_parent_lt (x : Fin N) (hx : x ≠ R.median) :
    P.rootDepth (P.parent x) < P.rootDepth x := by
  by_cases hh : R.height x = 0
  · obtain hsk := P.skeleton_same_arm x hx hh
    rcases hsk with h0 | h1 | h2
    · rcases h0 with ⟨_, hlt, hp1, hp2⟩
      have hph := P.skeleton_height x hx hh
      have hz := R.atMostOne x
      rcases hz with h | h | h <;> simp_all [rootDepth]
    · rcases h1 with ⟨_, hlt, hp0, hp2⟩
      have hph := P.skeleton_height x hx hh
      have hz := R.atMostOne x
      rcases hz with h | h | h <;> simp_all [rootDepth]
    · rcases h2 with ⟨_, hlt, hp0, hp1⟩
      have hph := P.skeleton_height x hx hh
      have hz := R.atMostOne x
      rcases hz with h | h | h <;> simp_all [rootDepth]
  · have hl := P.lower_height x hx hh
    obtain ⟨ht0, ht1, ht2⟩ := P.same_fibre x hx hh
    simp only [rootDepth]
    omega

theorem rootDepth_step_lt {x y : Fin N} (hxy : P.Step x y) :
    P.rootDepth y < P.rootDepth x := by
  rcases hxy with ⟨hx, rfl⟩
  exact P.rootDepth_parent_lt x hx

theorem rootDepth_le_of_reaches {x y : Fin N} (hxy : P.Reaches x y) :
    P.rootDepth y ≤ P.rootDepth x := by
  induction hxy with
  | refl => exact Nat.le_refl _
  | tail hxy hyz ih =>
      exact (P.rootDepth_step_lt hyz).le.trans ih

theorem rootDepth_lt_of_reaches_of_ne {x y : Fin N}
    (hxy : P.Reaches x y) (hne : x ≠ y) :
    P.rootDepth y < P.rootDepth x := by
  rcases Relation.ReflTransGen.cases_head hxy with h | ⟨z, hxz, hzy⟩
  · exact (hne h).elim
  · exact (P.rootDepth_le_of_reaches hzy).trans_lt
      (P.rootDepth_step_lt hxz)

theorem reaches_antisymm {x y : Fin N}
    (hxy : P.Reaches x y) (hyx : P.Reaches y x) : x = y := by
  by_contra hne
  have h₁ := P.rootDepth_lt_of_reaches_of_ne hxy hne
  have h₂ := P.rootDepth_lt_of_reaches_of_ne hyx (Ne.symm hne)
  omega

/-- Every parent chain terminates at the named median. -/
theorem reaches_median (x : Fin N) : P.Reaches x R.median := by
  induction h : P.rootDepth x using Nat.strong_induction_on generalizing x with
  | h d ih =>
      by_cases hx : x = R.median
      · subst x
        exact Relation.ReflTransGen.refl
      · apply Relation.ReflTransGen.head
          (show P.Step x (P.parent x) from ⟨hx, rfl⟩)
        apply ih (P.rootDepth (P.parent x))
        · simpa [h] using P.rootDepth_parent_lt x hx
        · rfl

/-- No nonempty parent cycle can occur. -/
theorem no_parent_cycle (x : Fin N) (k : ℕ) (hk : 0 < k)
    (hne : ∀ j < k, (P.parent^[j]) x ≠ R.median) :
    (P.parent^[k]) x ≠ x := by
  intro hcycle
  have hdesc : ∀ j < k,
      P.rootDepth ((P.parent^[j + 1]) x) <
        P.rootDepth ((P.parent^[j]) x) := by
    intro j hj
    simpa [Function.iterate_succ_apply'] using
      P.rootDepth_parent_lt ((P.parent^[j]) x) (hne j hj)
  have hlt_all : ∀ j, 0 < j → j ≤ k →
      P.rootDepth ((P.parent^[j]) x) < P.rootDepth x := by
    intro j hj hjk
    induction j with
    | zero => omega
    | succ j ih =>
        have hlast := hdesc j (by omega)
        by_cases hj0 : j = 0
        · subst j
          simpa using hlast
        · have hprev := ih (by omega) (by omega)
          omega
  have hlt := hlt_all k hk (Nat.le_refl k)
  rw [hcycle] at hlt
  omega

/-! ### Decoding the parent choice as an actual positive integral tree -/

/-- The undirected graph containing exactly the nonmedian parent edges. -/
def graph : SimpleGraph (Fin N) where
  Adj x y := P.Step x y ∨ P.Step y x
  symm := by
    intro x y h
    exact h.elim Or.inr Or.inl
  loopless := by
    intro x h
    rcases h with h | h
    · exact (P.rootDepth_step_lt h).false
    · exact (P.rootDepth_step_lt h).false

theorem graph_adj_parent (x : Fin N) (hx : x ≠ R.median) :
    P.graph.Adj x (P.parent x) := Or.inl ⟨hx, rfl⟩

theorem graph_connected : P.graph.Connected := by
  rw [SimpleGraph.connected_iff]
  constructor
  · intro x y
    have hx : P.graph.Reachable x R.median := by
      exact Relation.reflTransGen_minimal (r' := P.graph.Reachable)
        (fun z => SimpleGraph.Reachable.refl z)
        (fun _ _ _ hab hbc => hab.trans hbc)
        (fun _ _ hstep => SimpleGraph.Adj.reachable (Or.inl hstep))
        (P.reaches_median x)
    have hy : P.graph.Reachable y R.median := by
      exact Relation.reflTransGen_minimal (r' := P.graph.Reachable)
        (fun z => SimpleGraph.Reachable.refl z)
        (fun _ _ _ hab hbc => hab.trans hbc)
        (fun _ _ hstep => SimpleGraph.Adj.reachable (Or.inl hstep))
        (P.reaches_median y)
    exact hx.trans hy.symm
  · exact ⟨R.median⟩

/-- A nonmedian name determines its actual undirected parent edge. -/
def edgeOfNonmedian (x : {x : Fin N // x ≠ R.median}) : P.graph.edgeSet :=
  ⟨s(x.1, P.parent x.1), P.graph_adj_parent x.1 x.2⟩

theorem edgeOfNonmedian_injective : Function.Injective P.edgeOfNonmedian := by
  intro x y hxy
  apply Subtype.ext
  have hs : s(x.1, P.parent x.1) = s(y.1, P.parent y.1) :=
    congrArg Subtype.val hxy
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
    Prod.swap_prod_mk] at hs
  rcases hs with hsame | hswap
  · exact hsame.1
  · have hxlt := P.rootDepth_parent_lt x.1 x.2
    have hylt := P.rootDepth_parent_lt y.1 y.2
    rw [hswap.2] at hxlt
    rw [← hswap.1] at hylt
    omega

theorem edgeOfNonmedian_surjective : Function.Surjective P.edgeOfNonmedian := by
  rintro ⟨e, he⟩
  induction e using Sym2.ind with
  | _ x y =>
      change P.graph.Adj x y at he
      rcases he with hxy | hyx
      · refine ⟨⟨x, hxy.1⟩, ?_⟩
        apply Subtype.ext
        simp [edgeOfNonmedian, hxy.2]
      · refine ⟨⟨y, hyx.1⟩, ?_⟩
        apply Subtype.ext
        simp [edgeOfNonmedian, hyx.2, Sym2.eq_swap]

noncomputable def nonmedianEdgeEquiv :
    {x : Fin N // x ≠ R.median} ≃ P.graph.edgeSet :=
  Equiv.ofBijective P.edgeOfNonmedian
    ⟨P.edgeOfNonmedian_injective, P.edgeOfNonmedian_surjective⟩

theorem graph_edge_card : Nat.card P.graph.edgeSet = N - 1 := by
  classical
  rw [← Nat.card_congr P.nonmedianEdgeEquiv]
  letI : Fintype {x : Fin N // x ≠ R.median} := Fintype.ofFinite _
  letI : Fintype {x : Fin N // x = R.median} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl (fun x : Fin N => x = R.median)]
  simp

theorem graph_isTree : P.graph.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨P.graph_connected, ?_⟩
  rw [P.graph_edge_card, Nat.card_fin]
  have hN : 0 < N := Nat.pos_of_ne_zero (fun h => Fin.elim0 (h ▸ R.median))
  omega

/-- The parent edge length is its positive root-depth drop. -/
noncomputable def edgeWeight (e : P.graph.edgeSet) : ℕ :=
  let x := P.nonmedianEdgeEquiv.symm e
  P.rootDepth x.1 - P.rootDepth (P.parent x.1)

theorem edgeWeight_pos (e : P.graph.edgeSet) : 0 < P.edgeWeight e := by
  let x := P.nonmedianEdgeEquiv.symm e
  have hx := P.rootDepth_parent_lt x.1 x.2
  exact Nat.sub_pos_of_lt hx

/-- The actual positive integral tree decoded from the parent flags. -/
noncomputable def decodedTree : PosIntTree N where
  graph := P.graph
  isTree := P.graph_isTree
  weight := P.edgeWeight
  weight_pos := P.edgeWeight_pos

@[simp] theorem decoded_parent_weight
    (x : {x : Fin N // x ≠ R.median}) :
    P.decodedTree.weight (P.edgeOfNonmedian x) =
      P.rootDepth x.1 - P.rootDepth (P.parent x.1) := by
  simp [decodedTree, edgeWeight, nonmedianEdgeEquiv]

private theorem decoded_path_of_reaches {x y : Fin N}
    (hxy : P.Reaches x y) :
    ∃ p : P.decodedTree.graph.Path x y,
      P.decodedTree.walkWeight p.1 = P.rootDepth x - P.rootDepth y ∧
      (∀ z ∈ p.1.support, P.rootDepth z ≤ P.rootDepth x) ∧
      (∀ z ∈ p.1.support, P.Reaches x z ∧ P.Reaches z y) := by
  induction hxy using Relation.ReflTransGen.head_induction_on with
  | refl =>
      refine ⟨⟨SimpleGraph.Walk.nil, by simp⟩, ?_, ?_, ?_⟩
      · simp [PosIntTree.walkWeight]
      · intro z hz
        have hz' : z = y := by simpa using hz
        subst z
        exact Nat.le_refl _
      · intro z hz
        have hz' : z = y := by simpa using hz
        subst z
        exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | @head x z hstep hreach ih =>
      rcases hstep with ⟨hx, hparent⟩
      subst z
      obtain ⟨p, hpweight, hpbound, hpreach⟩ := ih
      have hlt := P.rootDepth_parent_lt x hx
      have hxnot : x ∉ p.1.support := by
        intro hmem
        have hle := hpbound x hmem
        omega
      have hadj : P.decodedTree.graph.Adj x (P.parent x) :=
        P.graph_adj_parent x hx
      let route : P.decodedTree.graph.Path x y :=
        ⟨p.1.cons hadj, p.2.cons hxnot⟩
      refine ⟨route, ?_, ?_, ?_⟩
      · have hedge :
          P.decodedTree.weight
              (P.edgeOfNonmedian ⟨x, hx⟩) =
            P.rootDepth x - P.rootDepth (P.parent x) :=
          P.decoded_parent_weight ⟨x, hx⟩
        have hpair :
            P.decodedTree.weightOfPair s(x, P.parent x) =
              P.rootDepth x - P.rootDepth (P.parent x) := by
          rw [← hedge]
          exact P.decodedTree.weightOfPair_edge
            (P.edgeOfNonmedian ⟨x, hx⟩)
        have hpweight' :
            (p.1.edges.map P.decodedTree.weightOfPair).sum =
              P.rootDepth (P.parent x) - P.rootDepth y := by
          simpa only [PosIntTree.walkWeight] using hpweight
        simp only [route, PosIntTree.walkWeight,
          SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons]
        rw [hpair, hpweight']
        have hy_le : P.rootDepth y ≤ P.rootDepth (P.parent x) := by
          have := hpbound y p.1.end_mem_support
          exact this
        omega
      · intro v hv
        rcases (by simpa [route] using hv : v = x ∨ v ∈ p.1.support) with
          rfl | hvp
        · exact Nat.le_refl _
        · exact (hpbound v hvp).trans hlt.le
      · intro v hv
        rcases (by simpa [route] using hv : v = x ∨ v ∈ p.1.support) with
          rfl | hvp
        · exact ⟨Relation.ReflTransGen.refl,
            Relation.ReflTransGen.head ⟨hx, rfl⟩ hreach⟩
        · obtain ⟨hpv, hvy⟩ := hpreach v hvp
          exact ⟨Relation.ReflTransGen.head ⟨hx, rfl⟩ hpv, hvy⟩

/-- Exact decoded distance along every parent-ancestor chain. -/
theorem decoded_dist_of_reaches {x y : Fin N} (hxy : P.Reaches x y) :
    P.decodedTree.dist x y = P.rootDepth x - P.rootDepth y := by
  obtain ⟨p, hp, _, _⟩ := P.decoded_path_of_reaches hxy
  rw [← hp]
  exact (P.decodedTree.path_walkWeight_eq_dist p).symm

/-- In particular, the decoded root distance is exactly the coordinate
root depth. -/
theorem decoded_dist_to_median (x : Fin N) :
    P.decodedTree.dist x R.median = P.rootDepth x := by
  rw [P.decoded_dist_of_reaches (P.reaches_median x)]
  simp [rootDepth, R.median_height, R.median_t0,
    R.median_t1, R.median_t2]

/-- `m` is the lowest common parent-ancestor of `x` and `y`. -/
def IsMeet (x y m : Fin N) : Prop :=
  P.Reaches x m ∧ P.Reaches y m ∧
    ∀ z, P.Reaches x z → P.Reaches y z → P.Reaches m z

/-- Exact LCA distance formula in the actual decoded tree. -/
theorem decoded_dist_of_isMeet {x y m : Fin N} (hm : P.IsMeet x y m) :
    P.decodedTree.dist x y =
      (P.rootDepth x - P.rootDepth m) +
        (P.rootDepth y - P.rootDepth m) := by
  classical
  obtain ⟨px, hxw, _, hxreach⟩ := P.decoded_path_of_reaches hm.1
  obtain ⟨py, hyw, _, hyreach⟩ := P.decoded_path_of_reaches hm.2.1
  have hdisjoint : px.1.support.Disjoint py.1.reverse.support.tail := by
    rw [List.disjoint_left]
    intro z hzx hzy
    have hzy' : z ∈ py.1.support := by
      have : z ∈ py.1.reverse.support := List.mem_of_mem_tail hzy
      simpa using this
    obtain ⟨hxz, hzm₁⟩ := hxreach z hzx
    obtain ⟨hyz, hzm₂⟩ := hyreach z hzy'
    have hmz := hm.2.2 z hxz hyz
    have hzm : z = m := P.reaches_antisymm hzm₁ hmz
    subst z
    have hnodup : py.1.reverse.support.Nodup := py.2.reverse.support_nodup
    rw [py.1.reverse.support_eq_cons] at hnodup hzy
    exact (List.nodup_cons.mp hnodup).1 hzy
  let route : P.decodedTree.graph.Path x y :=
    ⟨px.1.append py.1.reverse, by
      rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append,
        List.nodup_append]
      refine ⟨px.2.support_nodup, py.2.reverse.support_nodup.tail, ?_⟩
      intro z hzx w hwy hzw
      subst w
      exact (List.disjoint_left.mp hdisjoint hzx) hwy⟩
  calc
    P.decodedTree.dist x y = P.decodedTree.walkWeight route.1 :=
      (P.decodedTree.path_walkWeight_eq_dist route).symm
    _ = P.decodedTree.walkWeight px.1 +
        P.decodedTree.walkWeight py.1 := by
      simp [route, PosIntTree.walkWeight, List.sum_append]
    _ = (P.rootDepth x - P.rootDepth m) +
        (P.rootDepth y - P.rootDepth m) := by rw [hxw, hyw]

end ParentChoice

/-! ### Exact scoped reconstruction endpoint -/

/-- The intended LCA with port zero, expressed entirely by the named
projection signature. -/
def anchorMeet0 {N : ℕ} (R : ClosedCoordinateRows N) (x : Fin N) : Fin N :=
  if R.t1 x = 0 ∧ R.t2 x = 0 then R.projection x else R.median

def anchorMeet1 {N : ℕ} (R : ClosedCoordinateRows N) (x : Fin N) : Fin N :=
  if R.t0 x = 0 ∧ R.t2 x = 0 then R.projection x else R.median

def anchorMeet2 {N : ℕ} (R : ClosedCoordinateRows N) (x : Fin N) : Fin N :=
  if R.t0 x = 0 ∧ R.t1 x = 0 then R.projection x else R.median

/-- The scoped converse asks only for parent combinatorics: the forced
skeleton and same-fibre parent choices must have the displayed named LCAs.
No distance equality or tree property is assumed; both are derived below.
This is precisely the parent-scoped converse of the audit, rather than the
held arbitrary-anchor package. -/
structure ScopedParentChoice {N : ℕ} (R : ClosedCoordinateRows N) where
  choice : ParentChoice R
  meet0 : ∀ x, choice.IsMeet x R.port0 (anchorMeet0 R x)
  meet1 : ∀ x, choice.IsMeet x R.port1 (anchorMeet1 R x)
  meet2 : ∀ x, choice.IsMeet x R.port2 (anchorMeet2 R x)

namespace ScopedParentChoice

variable {N : ℕ} {R : ClosedCoordinateRows N} (S : ScopedParentChoice R)

theorem rootDepth_anchorMeet0 (x : Fin N) :
    S.choice.rootDepth (anchorMeet0 R x) = R.t0 x := by
  rcases R.atMostOne x with h0 | h1 | h2
  · simp [anchorMeet0, h0, ParentChoice.rootDepth,
      R.projection_height, R.projection_t0,
      R.projection_t1, R.projection_t2]
  · rcases h1 with ⟨ht0, ht2⟩
    by_cases ht1 : R.t1 x = 0
    · simp [anchorMeet0, ht0, ht1, ht2, ParentChoice.rootDepth,
        R.projection_height, R.projection_t0,
        R.projection_t1, R.projection_t2]
    · simp [anchorMeet0, ht0, ht1, ht2, ParentChoice.rootDepth,
        R.median_height, R.median_t0, R.median_t1, R.median_t2]
  · rcases h2 with ⟨ht0, ht1⟩
    by_cases ht2 : R.t2 x = 0
    · simp [anchorMeet0, ht0, ht1, ht2, ParentChoice.rootDepth,
        R.projection_height, R.projection_t0,
        R.projection_t1, R.projection_t2]
    · simp [anchorMeet0, ht0, ht1, ht2, ParentChoice.rootDepth,
        R.median_height, R.median_t0, R.median_t1, R.median_t2]

theorem rootDepth_anchorMeet1 (x : Fin N) :
    S.choice.rootDepth (anchorMeet1 R x) = R.t1 x := by
  rcases R.atMostOne x with h0 | h1 | h2
  · rcases h0 with ⟨ht1, ht2⟩
    by_cases ht0 : R.t0 x = 0
    · simp [anchorMeet1, ht0, ht1, ht2, ParentChoice.rootDepth,
        R.projection_height, R.projection_t0,
        R.projection_t1, R.projection_t2]
    · simp [anchorMeet1, ht0, ht1, ht2, ParentChoice.rootDepth,
        R.median_height, R.median_t0, R.median_t1, R.median_t2]
  · simp [anchorMeet1, h1, ParentChoice.rootDepth,
      R.projection_height, R.projection_t0,
      R.projection_t1, R.projection_t2]
  · rcases h2 with ⟨ht0, ht1⟩
    by_cases ht2 : R.t2 x = 0
    · simp [anchorMeet1, ht0, ht1, ht2, ParentChoice.rootDepth,
        R.projection_height, R.projection_t0,
        R.projection_t1, R.projection_t2]
    · simp [anchorMeet1, ht0, ht1, ht2, ParentChoice.rootDepth,
        R.median_height, R.median_t0, R.median_t1, R.median_t2]

theorem rootDepth_anchorMeet2 (x : Fin N) :
    S.choice.rootDepth (anchorMeet2 R x) = R.t2 x := by
  rcases R.atMostOne x with h0 | h1 | h2
  · rcases h0 with ⟨ht1, ht2⟩
    by_cases ht0 : R.t0 x = 0
    · simp [anchorMeet2, ht0, ht1, ht2, ParentChoice.rootDepth,
        R.projection_height, R.projection_t0,
        R.projection_t1, R.projection_t2]
    · simp [anchorMeet2, ht0, ht1, ht2, ParentChoice.rootDepth,
        R.median_height, R.median_t0, R.median_t1, R.median_t2]
  · rcases h1 with ⟨ht0, ht2⟩
    by_cases ht1 : R.t1 x = 0
    · simp [anchorMeet2, ht0, ht1, ht2, ParentChoice.rootDepth,
        R.projection_height, R.projection_t0,
        R.projection_t1, R.projection_t2]
    · simp [anchorMeet2, ht0, ht1, ht2, ParentChoice.rootDepth,
        R.median_height, R.median_t0, R.median_t1, R.median_t2]
  · simp [anchorMeet2, h2, ParentChoice.rootDepth,
      R.projection_height, R.projection_t0,
      R.projection_t1, R.projection_t2]

theorem rootDepth_port0 : S.choice.rootDepth R.port0 = R.A0 := by
  simp [ParentChoice.rootDepth, R.port0_height, R.port0_t0,
    R.port0_t1, R.port0_t2]

theorem rootDepth_port1 : S.choice.rootDepth R.port1 = R.A1 := by
  simp [ParentChoice.rootDepth, R.port1_height, R.port1_t0,
    R.port1_t1, R.port1_t2]

theorem rootDepth_port2 : S.choice.rootDepth R.port2 = R.A2 := by
  simp [ParentChoice.rootDepth, R.port2_height, R.port2_t0,
    R.port2_t1, R.port2_t2]

/-- Exact recovery of every indexed distance to port zero in the actual
decoded positive integral tree. -/
theorem decoded_anchor0 (x : Fin N) :
    S.choice.decodedTree.dist x R.port0 = R.anchorDistance x 0 := by
  rw [S.choice.decoded_dist_of_isMeet (S.meet0 x)]
  rw [S.rootDepth_anchorMeet0 x, S.rootDepth_port0]
  simp only [ParentChoice.rootDepth]
  have ht := R.t0_le x
  have hr := R.row0 x
  omega

theorem decoded_anchor1 (x : Fin N) :
    S.choice.decodedTree.dist x R.port1 = R.anchorDistance x 1 := by
  rw [S.choice.decoded_dist_of_isMeet (S.meet1 x)]
  rw [S.rootDepth_anchorMeet1 x, S.rootDepth_port1]
  simp only [ParentChoice.rootDepth]
  have ht := R.t1_le x
  have hr := R.row1 x
  omega

theorem decoded_anchor2 (x : Fin N) :
    S.choice.decodedTree.dist x R.port2 = R.anchorDistance x 2 := by
  rw [S.choice.decoded_dist_of_isMeet (S.meet2 x)]
  rw [S.rootDepth_anchorMeet2 x, S.rootDepth_port2]
  simp only [ParentChoice.rootDepth]
  have ht := R.t2_le x
  have hr := R.row2 x
  omega

/-- Queryable scoped reconstruction endpoint: one actual positive integral
tree on exactly the named rows, with all three indexed anchor columns exact.
The construction introduces no vertex because its vertex type is `Fin N`. -/
theorem reconstructs_exact_named_component (S : ScopedParentChoice R) :
    ∃ T : PosIntTree N,
      (∀ x, T.dist x R.port0 = R.anchorDistance x 0) ∧
      (∀ x, T.dist x R.port1 = R.anchorDistance x 1) ∧
      (∀ x, T.dist x R.port2 = R.anchorDistance x 2) := by
  refine ⟨ParentChoice.decodedTree S.choice, ?_, ?_, ?_⟩
  · exact fun x => decoded_anchor0 S x
  · exact fun x => decoded_anchor1 S x
  · exact fun x => decoded_anchor2 S x

end ScopedParentChoice

end LeechTrees.OddQuotient.ThreePort
