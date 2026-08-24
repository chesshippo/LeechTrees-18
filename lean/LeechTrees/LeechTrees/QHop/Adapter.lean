import LeechTrees.Foundations
import LeechTrees.QHop.Kernel

open scoped BigOperators

namespace LeechTrees.QHop

open LeechTrees.Foundation
open SimpleGraph

theorem VertexPair.ofDistinct_eq_iff {n : ℕ} {a b c d : Fin n}
    (hab : a ≠ b) (hcd : c ≠ d) :
    VertexPair.ofDistinct a b hab = VertexPair.ofDistinct c d hcd ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  unfold VertexPair.ofDistinct
  split_ifs <;> simp_all <;> omega

/-! Small walk-list lemmas kept local to the T7 adapter. -/

theorem walk_edges_take {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (n : ℕ) :
    (p.take n).edges = p.edges.take n := by
  induction p generalizing n with
  | nil => simp [Walk.take]
  | cons h p ih =>
      cases n with
      | zero => simp [Walk.take]
      | succ n => simp [Walk.take, ih]

theorem walk_edges_drop {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (n : ℕ) :
    (p.drop n).edges = p.edges.drop n := by
  induction p generalizing n with
  | nil => simp [Walk.drop]
  | cons h p ih =>
      cases n with
      | zero => simp [Walk.drop]
      | succ n => simp [Walk.drop, ih]

theorem walk_edges_segment {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (a len : ℕ) :
    ((p.drop a).take len).edges = (p.edges.drop a).take len := by
  rw [walk_edges_take, walk_edges_drop]

theorem isPath_take {V : Type*} {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hp : p.IsPath) (n : ℕ) :
    (p.take n).IsPath := by
  rw [Walk.isPath_def, Walk.take_support_eq_support_take_succ]
  exact hp.support_nodup.take

theorem isPath_drop {V : Type*} {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hp : p.IsPath) (n : ℕ) :
    (p.drop n).IsPath := by
  rw [Walk.isPath_def, Walk.drop_support_eq_support_drop_min]
  exact hp.support_nodup.drop

theorem isPath_segment {V : Type*} {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hp : p.IsPath) (a len : ℕ) :
    ((p.drop a).take len).IsPath :=
  isPath_take (isPath_drop hp a) len

def listTuple15 {A : Type*} (l : List A) (h : l.length = 15) : Fin 15 → A :=
  fun i ↦ l.get (Fin.cast h.symm i)

theorem ofFn_listTuple15 {A : Type*} (l : List A) (h : l.length = 15) :
    List.ofFn (listTuple15 l h) = l := by
  apply List.ext_get_iff.mpr
  constructor
  · simp [h]
  · intro n hn₁ hn₂
    rw [List.get_ofFn]
    unfold listTuple15
    congr

/-! A concrete, single index type for all 42 intervals of lengths 1--3. -/

def shortLenNat (i : Fin 42) : ℕ :=
  if (i : ℕ) < 15 then 1 else if (i : ℕ) < 29 then 2 else 3

def shortStartNat (i : Fin 42) : ℕ :=
  if (i : ℕ) < 15 then i else if (i : ℕ) < 29 then i - 15 else i - 29

def shortEndNat (i : Fin 42) : ℕ := shortStartNat i + shortLenNat i

theorem shortStartNat_lt_sixteen (i : Fin 42) : shortStartNat i < 16 := by
  simp only [shortStartNat]
  split_ifs <;> omega

theorem shortEndNat_lt_sixteen (i : Fin 42) : shortEndNat i < 16 := by
  simp only [shortEndNat, shortStartNat, shortLenNat]
  split_ifs <;> omega

def shortStart (i : Fin 42) : Fin 16 :=
  ⟨shortStartNat i, shortStartNat_lt_sixteen i⟩

def shortEnd (i : Fin 42) : Fin 16 :=
  ⟨shortEndNat i, shortEndNat_lt_sixteen i⟩

theorem shortStart_lt_shortEnd (i : Fin 42) : shortStart i < shortEnd i := by
  simp only [shortStart, shortEnd, shortEndNat, Fin.mk_lt_mk]
  have : 0 < shortLenNat i := by
    simp only [shortLenNat]
    split_ifs <;> omega
  omega

theorem shortEndpoints_injective :
    Function.Injective (fun i : Fin 42 ↦ (shortStart i, shortEnd i)) := by
  intro i j hij
  have hs : shortStartNat i = shortStartNat j := by
    exact congrArg (fun p : Fin 16 × Fin 16 ↦ (p.1 : ℕ)) hij
  have he : shortEndNat i = shortEndNat j := by
    exact congrArg (fun p : Fin 16 × Fin 16 ↦ (p.2 : ℕ)) hij
  apply Fin.ext
  simp only [shortStartNat, shortEndNat, shortLenNat] at hs he
  split_ifs at hs he <;> omega

def shortValue (g : Fin 15 → ℕ) : Fin 42 → ℕ := ![
  g 0, g 1, g 2, g 3, g 4, g 5, g 6, g 7, g 8, g 9,
  g 10, g 11, g 12, g 13, g 14,
  g 0 + g 1, g 1 + g 2, g 2 + g 3, g 3 + g 4,
  g 4 + g 5, g 5 + g 6, g 6 + g 7, g 7 + g 8,
  g 8 + g 9, g 9 + g 10, g 10 + g 11, g 11 + g 12,
  g 12 + g 13, g 13 + g 14,
  g 0 + g 1 + g 2, g 1 + g 2 + g 3, g 2 + g 3 + g 4,
  g 3 + g 4 + g 5, g 4 + g 5 + g 6, g 5 + g 6 + g 7,
  g 6 + g 7 + g 8, g 7 + g 8 + g 9, g 8 + g 9 + g 10,
  g 9 + g 10 + g 11, g 10 + g 11 + g 12,
  g 11 + g 12 + g 13, g 12 + g 13 + g 14]

theorem ofFn_shortValue (g : Fin 15 → ℕ) :
    List.ofFn (shortValue g) = shortSums g := by
  rfl

theorem ofFn_fin_fifteen (g : Fin 15 → ℕ) :
    List.ofFn g =
      [g 0, g 1, g 2, g 3, g 4, g 5, g 6, g 7, g 8, g 9,
       g 10, g 11, g 12, g 13, g 14] := by
  simp only [List.ofFn_succ, List.ofFn_zero]
  rfl

theorem dist_getVert_add_eq_segmentWeight {n : ℕ} (T : PosIntTree n)
    {u v : Fin n} (p : T.graph.Walk u v) (hp : p.IsPath) (a len : ℕ) :
    T.dist (p.getVert a) (p.getVert (a + len)) =
      (((p.edges.drop a).take len).map T.weightOfPair).sum := by
  have hpath := T.path_walkWeight_eq_dist
    (⟨(p.drop a).take len, isPath_segment hp a len⟩ :
      T.graph.Path (p.getVert a) ((p.drop a).getVert len))
  have hpath' :
      T.walkWeight ((p.drop a).take len) =
        T.dist (p.getVert a) (p.getVert (a + len)) := by
    simpa only [Walk.drop_getVert] using hpath
  simpa [PosIntTree.walkWeight, walk_edges_segment] using hpath'.symm

theorem path_getVert_short_ne {n : ℕ} {T : PosIntTree n}
    {u v : Fin n} {p : T.graph.Walk u v} (hp : p.IsPath)
    (hlen : p.length = 15) (i : Fin 42) :
    p.getVert (shortStart i) ≠ p.getVert (shortEnd i) := by
  intro heq
  have hidx := hp.getVert_injOn
    (show (shortStart i : ℕ) ≤ p.length by
      rw [hlen]
      omega)
    (show (shortEnd i : ℕ) ≤ p.length by
      rw [hlen]
      omega)
    heq
  exact (ne_of_lt (shortStart_lt_shortEnd i)) (Fin.ext hidx)

noncomputable def shortEndpointPair {n : ℕ} {T : PosIntTree n}
    {u v : Fin n} (p : T.graph.Walk u v) (hp : p.IsPath)
    (hlen : p.length = 15) (i : Fin 42) : VertexPair n :=
  VertexPair.ofDistinct (p.getVert (shortStart i)) (p.getVert (shortEnd i))
    (path_getVert_short_ne hp hlen i)

theorem shortEndpointPair_injective {n : ℕ} {T : PosIntTree n}
    {u v : Fin n} {p : T.graph.Walk u v} (hp : p.IsPath)
    (hlen : p.length = 15) :
    Function.Injective (shortEndpointPair p hp hlen) := by
  intro i j hij
  have hpairs := (VertexPair.ofDistinct_eq_iff
    (path_getVert_short_ne hp hlen i)
    (path_getVert_short_ne hp hlen j)).mp hij
  rcases hpairs with hdir | hrev
  · have hs : shortStart i = shortStart j := by
      have hsi : (shortStart i : ℕ) ≤ p.length := by rw [hlen]; omega
      have hsj : (shortStart j : ℕ) ≤ p.length := by rw [hlen]; omega
      exact Fin.ext (hp.getVert_injOn hsi hsj hdir.1)
    have he : shortEnd i = shortEnd j := by
      have hei : (shortEnd i : ℕ) ≤ p.length := by rw [hlen]; omega
      have hej : (shortEnd j : ℕ) ≤ p.length := by rw [hlen]; omega
      exact Fin.ext (hp.getVert_injOn hei hej hdir.2)
    exact shortEndpoints_injective (Prod.ext hs he)
  · have hs : shortStart i = shortEnd j := by
      have hsi : (shortStart i : ℕ) ≤ p.length := by rw [hlen]; omega
      have hej : (shortEnd j : ℕ) ≤ p.length := by rw [hlen]; omega
      exact Fin.ext (hp.getVert_injOn hsi hej hrev.1)
    have he : shortEnd i = shortStart j := by
      have hei : (shortEnd i : ℕ) ≤ p.length := by rw [hlen]; omega
      have hsj : (shortStart j : ℕ) ≤ p.length := by rw [hlen]; omega
      exact Fin.ext (hp.getVert_injOn hei hsj hrev.2)
    have hi := shortStart_lt_shortEnd i
    have hj := shortStart_lt_shortEnd j
    omega

noncomputable def pathGaps {n : ℕ} (T : PosIntTree n)
    {u v : Fin n} (p : T.graph.Walk u v) (hlen : p.length = 15) : Fin 15 → ℕ :=
  listTuple15 (p.edges.map T.weightOfPair) (by simpa [p.length_edges] using hlen)

theorem weightOfPair_pos_of_mem_walk_edges {n : ℕ} (T : PosIntTree n)
    {u v : Fin n} (p : T.graph.Walk u v) {e : Sym2 (Fin n)}
    (he : e ∈ p.edges) : 0 < T.weightOfPair e := by
  have hedge : e ∈ T.graph.edgeSet := by
    induction e using Sym2.ind with
    | _ x y =>
        rw [SimpleGraph.mem_edgeSet]
        exact p.adj_of_mem_edges he
  let edge : T.Edge := ⟨e, hedge⟩
  change 0 < T.weightOfPair edge.1
  rw [T.weightOfPair_edge]
  exact T.weight_pos edge

theorem pathGaps_positive {n : ℕ} (T : PosIntTree n)
    {u v : Fin n} (p : T.graph.Walk u v) (hlen : p.length = 15) :
    ∀ i, 0 < pathGaps T p hlen i := by
  intro i
  unfold pathGaps listTuple15
  simp only [List.get_eq_getElem, List.getElem_map]
  apply weightOfPair_pos_of_mem_walk_edges T p
  exact List.get_mem _ _

theorem sum_pathGaps_eq_walkWeight {n : ℕ} (T : PosIntTree n)
    {u v : Fin n} (p : T.graph.Walk u v) (hlen : p.length = 15) :
    (∑ i, pathGaps T p hlen i) = T.walkWeight p := by
  have hlist := ofFn_listTuple15 (p.edges.map T.weightOfPair)
    (by simpa [p.length_edges] using hlen)
  simpa [pathGaps, PosIntTree.walkWeight] using congrArg List.sum hlist

theorem shortValue_eq_pairDist {n : ℕ} (T : PosIntTree n)
    {u v : Fin n} (p : T.graph.Walk u v) (hp : p.IsPath)
    (hlen : p.length = 15) (i : Fin 42) :
    shortValue (pathGaps T p hlen) i =
      T.pairDist (shortEndpointPair p hp hlen i) := by
  unfold shortEndpointPair
  rw [T.pairDist_pairOfDistinct]
  let g := pathGaps T p hlen
  have hlist : List.ofFn g = p.edges.map T.weightOfPair := by
    exact ofFn_listTuple15 (p.edges.map T.weightOfPair)
      (by simpa [p.length_edges] using hlen)
  have hseg := dist_getVert_add_eq_segmentWeight T p hp
    (shortStartNat i) (shortLenNat i)
  change shortValue g i =
    T.dist (p.getVert (shortStartNat i)) (p.getVert (shortEndNat i))
  rw [show shortEndNat i = shortStartNat i + shortLenNat i by rfl, hseg]
  rw [List.map_take, List.map_drop, ← hlist]
  rw [ofFn_fin_fifteen]
  fin_cases i <;>
    simp [shortValue, shortStartNat, shortLenNat, Nat.add_assoc]

theorem path_shortSums_nodup {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) {u v : Fin n} (p : T.graph.Walk u v)
    (hp : p.IsPath) (hlen : p.length = 15) :
    (shortSums (pathGaps T p hlen)).Nodup := by
  have hpairs : Function.Injective (shortEndpointPair p hp hlen) :=
    shortEndpointPair_injective hp hlen
  have hdist : Function.Injective
      (fun i : Fin 42 ↦ T.pairDist (shortEndpointPair p hp hlen i)) :=
    hL.pairDist_injective.comp hpairs
  have hvalues : Function.Injective (shortValue (pathGaps T p hlen)) := by
    intro i j hij
    apply hdist
    change T.pairDist (shortEndpointPair p hp hlen i) =
      T.pairDist (shortEndpointPair p hp hlen j)
    calc
      T.pairDist (shortEndpointPair p hp hlen i) =
          shortValue (pathGaps T p hlen) i :=
        (shortValue_eq_pairDist T p hp hlen i).symm
      _ = shortValue (pathGaps T p hlen) j := hij
      _ = T.pairDist (shortEndpointPair p hp hlen j) :=
        shortValue_eq_pairDist T p hp hlen j
  have hnodup := List.nodup_ofFn_ofInjective hvalues
  rwa [ofFn_shortValue] at hnodup

theorem path_endpoints_ne_of_length_fifteen {V : Type*} {G : SimpleGraph V}
    {u v : V} {p : G.Walk u v} (hp : p.IsPath) (hlen : p.length = 15) :
    u ≠ v := by
  intro huv
  have heq : p.getVert 0 = p.getVert p.length := by simp [huv]
  have hidx := hp.getVert_injOn (by omega : 0 ≤ p.length)
    (by omega : p.length ≤ p.length) heq
  omega

theorem pathGaps_total_le_153 {T : PosIntTree 18} (hL : IsLeech T)
    {u v : Fin 18} (p : T.graph.Walk u v) (hp : p.IsPath)
    (hlen : p.length = 15) :
    (∑ i, pathGaps T p hlen i) ≤ 153 := by
  have huv : u ≠ v := path_endpoints_ne_of_length_fifteen hp hlen
  have hbound := hL.pairDist_le_target (VertexPair.ofDistinct u v huv)
  rw [T.pairDist_pairOfDistinct] at hbound
  have hweight := sum_pathGaps_eq_walkWeight T p hlen
  have hpathdist := T.path_walkWeight_eq_dist (⟨p, hp⟩ : T.graph.Path u v)
  rw [hweight, hpathdist]
  norm_num [targetN] at hbound ⊢
  exact hbound

/-- No order-18 Leech tree contains a simple path of exactly fifteen edges. -/
theorem no_order18_simplePath_length_eq_fifteen
    (T : PosIntTree 18) (hL : IsLeech T)
    {u v : Fin 18} (p : T.graph.Walk u v) (hp : p.IsPath)
    (hlen : p.length = 15) : False := by
  exact no_fifteen_gap_sequence (pathGaps T p hlen)
    (pathGaps_positive T p hlen)
    (path_shortSums_nodup hL p hp hlen)
    (pathGaps_total_le_153 hL p hp hlen)

/-- Paper claim T7: every simple path in an order-18 Leech tree has at most
fourteen physical edges.  A longer path is reduced to its first fifteen
edges, so this is not merely an exclusion of paths of exactly length 15. -/
theorem order18_simplePath_length_le_14
    (T : PosIntTree 18) (hL : IsLeech T)
    {u v : Fin 18} (p : T.graph.Walk u v) (hp : p.IsPath) :
    p.length ≤ 14 := by
  by_contra hnot
  have h15 : 15 ≤ p.length := by omega
  let q := p.take 15
  have hqpath : q.IsPath := isPath_take hp 15
  have hqlen : q.length = 15 := by
    simp [q, Nat.min_eq_left h15]
  exact no_order18_simplePath_length_eq_fifteen T hL q hqpath hqlen

/-! ## Binding the T6 finite argument to actual order-18 cuts -/

noncomputable def order18SmallerSide (T : PosIntTree 18) (e : T.Edge) : ℕ :=
  min (T.cutSize e) (18 - T.cutSize e)

theorem order18SmallerSide_pos (T : PosIntTree 18) (e : T.Edge) :
    0 < order18SmallerSide T e := by
  have hl := T.cutSize_pos e
  have hu := T.cutSize_lt_order e
  unfold order18SmallerSide
  exact Nat.lt_min.mpr ⟨hl, by omega⟩

theorem order18SmallerSide_le_nine (T : PosIntTree 18) (e : T.Edge) :
    order18SmallerSide T e ≤ 9 := by
  have hu := T.cutSize_lt_order e
  unfold order18SmallerSide
  by_cases h : T.cutSize e ≤ 18 - T.cutSize e
  · rw [Nat.min_eq_left h]
    omega
  · rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h))]
    omega

theorem order18SmallerSide_coefficient (T : PosIntTree 18) (e : T.Edge) :
    order18SmallerSide T e * (18 - order18SmallerSide T e) =
      T.cutSize e * (18 - T.cutSize e) := by
  have hu : T.cutSize e ≤ 18 := (T.cutSize_lt_order e).le
  unfold order18SmallerSide
  by_cases h : T.cutSize e ≤ 18 - T.cutSize e
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h)),
      Nat.sub_sub_self hu, Nat.mul_comm]

theorem order18_edge_card (T : PosIntTree 18) : Fintype.card T.Edge = 17 := by
  have h : Fintype.card T.Edge + 1 = 18 := by
    simpa only [SimpleGraph.edgeFinset_card, Fintype.card_fin] using
      T.isTree.card_edgeFinset
  omega

noncomputable def coreMassWitness_of_count_bound (m k : ℕ)
    (hk : k ≤ 9) (hm : m + 2 * k ≤ 19) : CoreMassWitness m k := by
  refine
    { leftMass := k
      rightMass := k
      restMass := 18 - 2 * k
      left_ge := le_rfl
      right_ge := le_rfl
      rest_ge := by omega
      total := by omega }

/-- A temporary constructor boundary for the sole structural ingredient of
T6.  The following public claim theorem does not expose this boundary: its
argument is discharged by `order18_core_count_add` below. -/
noncomputable def order18CutDataOfCoreCount
    (T : PosIntTree 18) (hL : IsLeech T)
    (hcore : ∀ (k : ℕ), 1 ≤ k → k ≤ 9 →
      (Finset.univ.filter (fun e : T.Edge ↦ k ≤ order18SmallerSide T e)).card +
        2 * k ≤ 19) :
    Order18LeechCutData T.Edge := by
  classical
  let cut : Order18CutProfile T.Edge :=
    { smallerSide := order18SmallerSide T
      smallerSide_pos := order18SmallerSide_pos T
      smallerSide_le_nine := order18SmallerSide_le_nine T
      coreMass := by
        intro k hk hk9 hne
        exact coreMassWitness_of_count_bound _ k hk9 (hcore k hk hk9) }
  refine
    { cut := cut
      edge_count := order18_edge_card T
      weight := T.weight
      weight_pos := T.weight_pos
      weight_injective := t1_edge_weight_injective hL
      weight_one := ?_
      weight_two := ?_
      checksum := ?_ }
  · obtain ⟨e, he, _⟩ := t1_existsUnique_weight_one hL (by decide : 2 ≤ 18)
    exact ⟨e, he⟩
  · obtain ⟨e, he, _⟩ := t1_existsUnique_weight_two hL (by decide : 3 ≤ 18)
    exact ⟨e, he⟩
  · have hsum := T4_order18_checksum hL
    change (∑ e : T.Edge,
      (order18SmallerSide T e * (18 - order18SmallerSide T e)) * T.weight e) = 11781
    simpa only [order18SmallerSide_coefficient] using hsum

/-- The largest weight over the actual physical edge subtype. -/
noncomputable def largestPhysicalEdge (T : PosIntTree 18) : ℕ :=
  Finset.univ.sup T.weight

end LeechTrees.QHop
