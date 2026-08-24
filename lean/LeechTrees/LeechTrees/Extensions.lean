import LeechTrees.OddEdgesGraphAdapter
import LeechTrees.QHop.Adapter

/-!
# Exact path and unchanged-extension obstructions

This module formalizes the elementary obstruction package in the frozen
LeechTrees model.  Transformation predicates retain indexed old distances;
they do not identify a distance *support* with a multiset.
-/

open scoped BigOperators

namespace LeechTrees.Extension

open LeechTrees.Foundation

/-! ## Small finite-sum infrastructure -/

theorem two_mul_sum_one_add_range (r : ℕ) :
    2 * (∑ i ∈ Finset.range r, (1 + (i : ℤ))) = (r : ℤ) * ((r : ℤ) + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Finset.sum_range_succ]
      push_cast
      nlinarith

/-- The sum of `r` distinct positive natural numbers is at least
`1 + ... + r`, in a division-free form. -/
theorem card_mul_succ_le_two_mul_sum
    {A : Type*} [Fintype A] [DecidableEq A]
    (f : A → ℕ) (hpos : ∀ a, 0 < f a) (hinj : Function.Injective f) :
    Fintype.card A * (Fintype.card A + 1) ≤ 2 * ∑ a, f a := by
  classical
  let emb : A ↪ ℤ :=
    ⟨fun a => (f a : ℤ), fun _ _ h => hinj (Int.ofNat_inj.mp h)⟩
  let s : Finset ℤ := Finset.univ.map emb
  have hspos : ∀ x ∈ s, (1 : ℤ) ≤ x := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨a, -, rfl⟩
    change (1 : ℤ) ≤ (f a : ℤ)
    have hf : 1 ≤ f a := hpos a
    exact_mod_cast hf
  have hcard : s.card = Fintype.card A := by
    simp [s]
  have hsum : (∑ x ∈ s, x) = (∑ a : A, (f a : ℤ)) := by
    simp [s, emb]
  have hlo := Finset.sum_range_le_sum (s := s) (c := (1 : ℤ)) hspos
  rw [hcard, hsum] at hlo
  have htwice := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℤ) ≤ 2)
  rw [two_mul_sum_one_add_range] at htwice
  exact_mod_cast htwice

/-! ## A normalized, graph-level weighted-path presentation -/

def stepLeft {n : ℕ} (i : Fin (n - 1)) : Fin n := ⟨i, by omega⟩
def stepRight {n : ℕ} (i : Fin (n - 1)) : Fin n := ⟨i + 1, by omega⟩
def twoLeft {n : ℕ} (i : Fin (n - 2)) : Fin n := ⟨i, by omega⟩
def twoRight {n : ℕ} (i : Fin (n - 2)) : Fin n := ⟨i + 2, by omega⟩
def twoFirstStep {n : ℕ} (i : Fin (n - 2)) : Fin (n - 1) := ⟨i, by omega⟩
def twoSecondStep {n : ℕ} (i : Fin (n - 2)) : Fin (n - 1) := ⟨i + 1, by omega⟩

theorem stepLeft_ne_stepRight {n : ℕ} (i : Fin (n - 1)) :
    stepLeft i ≠ stepRight i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [stepLeft, stepRight] at hv
  omega

theorem twoLeft_ne_twoRight {n : ℕ} (i : Fin (n - 2)) :
    twoLeft i ≠ twoRight i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [twoLeft, twoRight] at hv
  omega

/-- An exact normalized presentation of a weighted path: vertices and all
physical edges are ordered, consecutive edge pairs are the ordered vertex
pairs, and the path metric is the corresponding interval-sum metric. -/
structure WeightedPathPresentation {n : ℕ} (T : PosIntTree n) (hn : 1 ≤ n) where
  vertexOrder : Fin n ≃ Fin n
  edgeOrder : Fin (n - 1) ≃ T.Edge
  edgePair_eq : ∀ i,
    T.edgePair (edgeOrder i) =
      VertexPair.ofDistinct (vertexOrder (stepLeft i)) (vertexOrder (stepRight i))
        (vertexOrder.injective.ne (stepLeft_ne_stepRight i))
  twoStepDist : ∀ i,
    T.dist (vertexOrder (twoLeft i)) (vertexOrder (twoRight i)) =
      T.weight (edgeOrder (twoFirstStep i)) +
        T.weight (edgeOrder (twoSecondStep i))
  endpointDist :
    T.dist (vertexOrder ⟨0, hn⟩) (vertexOrder ⟨n - 1, by omega⟩) =
      ∑ i, T.weight (edgeOrder i)

namespace WeightedPathPresentation

variable {n : ℕ} {T : PosIntTree n} {hn : 1 ≤ n}

noncomputable def stepPair (P : WeightedPathPresentation T hn)
    (i : Fin (n - 1)) : VertexPair n :=
  VertexPair.ofDistinct (P.vertexOrder (stepLeft i)) (P.vertexOrder (stepRight i))
    (P.vertexOrder.injective.ne (stepLeft_ne_stepRight i))

noncomputable def twoPair (P : WeightedPathPresentation T hn)
    (i : Fin (n - 2)) : VertexPair n :=
  VertexPair.ofDistinct (P.vertexOrder (twoLeft i)) (P.vertexOrder (twoRight i))
    (P.vertexOrder.injective.ne (twoLeft_ne_twoRight i))

theorem stepPair_injective (P : WeightedPathPresentation T hn) :
    Function.Injective P.stepPair := by
  intro i j hij
  rw [stepPair, stepPair, LeechTrees.QHop.VertexPair.ofDistinct_eq_iff] at hij
  rcases hij with h | h
  · have hs := P.vertexOrder.injective h.1
    apply Fin.ext
    simpa only [stepLeft] using congrArg (fun x : Fin n => x.val) hs
  · exfalso
    have h1 := congrArg Fin.val (P.vertexOrder.injective h.1)
    have h2 := congrArg Fin.val (P.vertexOrder.injective h.2)
    simp only [stepLeft, stepRight] at h1 h2
    omega

theorem twoPair_injective (P : WeightedPathPresentation T hn) :
    Function.Injective P.twoPair := by
  intro i j hij
  rw [twoPair, twoPair, LeechTrees.QHop.VertexPair.ofDistinct_eq_iff] at hij
  rcases hij with h | h
  · have hs := P.vertexOrder.injective h.1
    apply Fin.ext
    simpa only [twoLeft] using congrArg (fun x : Fin n => x.val) hs
  · exfalso
    have h1 := congrArg Fin.val (P.vertexOrder.injective h.1)
    have h2 := congrArg Fin.val (P.vertexOrder.injective h.2)
    simp only [twoLeft, twoRight] at h1 h2
    omega

theorem stepPair_ne_twoPair (P : WeightedPathPresentation T hn)
    (i : Fin (n - 1)) (j : Fin (n - 2)) : P.stepPair i ≠ P.twoPair j := by
  intro hij
  rw [stepPair, twoPair, LeechTrees.QHop.VertexPair.ofDistinct_eq_iff] at hij
  rcases hij with h | h
  · have h1 := congrArg Fin.val (P.vertexOrder.injective h.1)
    have h2 := congrArg Fin.val (P.vertexOrder.injective h.2)
    simp only [stepLeft, stepRight, twoLeft, twoRight] at h1 h2
    omega
  · have h1 := congrArg Fin.val (P.vertexOrder.injective h.1)
    have h2 := congrArg Fin.val (P.vertexOrder.injective h.2)
    simp only [stepLeft, stepRight, twoLeft, twoRight] at h1 h2
    omega

@[simp] theorem pairDist_stepPair (P : WeightedPathPresentation T hn)
    (i : Fin (n - 1)) : T.pairDist (P.stepPair i) = T.weight (P.edgeOrder i) := by
  rw [stepPair, ← P.edgePair_eq i, T.edgePair_dist]

@[simp] theorem pairDist_twoPair (P : WeightedPathPresentation T hn)
    (i : Fin (n - 2)) :
    T.pairDist (P.twoPair i) =
      T.weight (P.edgeOrder (twoFirstStep i)) +
        T.weight (P.edgeOrder (twoSecondStep i)) := by
  rw [twoPair, T.pairDist_pairOfDistinct]
  exact P.twoStepDist i

def combinedValue (P : WeightedPathPresentation T hn) :
    Fin (n - 1) ⊕ Fin (n - 2) → ℕ
  | Sum.inl i => T.weight (P.edgeOrder i)
  | Sum.inr i => T.weight (P.edgeOrder (twoFirstStep i)) +
      T.weight (P.edgeOrder (twoSecondStep i))

theorem combinedValue_eq_pairDist (P : WeightedPathPresentation T hn) :
    ∀ z, P.combinedValue z = T.pairDist
      (match z with | Sum.inl i => P.stepPair i | Sum.inr i => P.twoPair i)
  | Sum.inl i => (P.pairDist_stepPair i).symm
  | Sum.inr i => (P.pairDist_twoPair i).symm

theorem combinedValue_injective (P : WeightedPathPresentation T hn)
    (hL : IsLeech T) : Function.Injective P.combinedValue := by
  intro x y hxy
  rcases x with i | i <;> rcases y with j | j
  · apply congrArg Sum.inl
    apply P.stepPair_injective
    apply hL.pairDist_injective
    simpa only [P.pairDist_stepPair] using hxy
  · exfalso
    apply P.stepPair_ne_twoPair i j
    apply hL.pairDist_injective
    simpa only [P.pairDist_stepPair, P.pairDist_twoPair] using hxy
  · exfalso
    apply P.stepPair_ne_twoPair j i
    apply hL.pairDist_injective
    simpa only [P.pairDist_stepPair, P.pairDist_twoPair] using hxy.symm
  · apply congrArg Sum.inr
    apply P.twoPair_injective
    apply hL.pairDist_injective
    simpa only [P.pairDist_twoPair] using hxy

theorem combinedValue_pos (P : WeightedPathPresentation T hn)
    (hL : IsLeech T) : ∀ z, 0 < P.combinedValue z := by
  intro z
  rw [P.combinedValue_eq_pairDist]
  exact hL.pairDist_pos _

theorem adjacent_sum_identity_fin {k : ℕ} (g : Fin (k + 1) → ℕ) :
    (∑ i : Fin k, (g i.castSucc + g i.succ)) + g 0 + g (Fin.last k) =
      2 * ∑ i : Fin (k + 1), g i := by
  have hleft := Fin.sum_univ_castSucc g
  have hright := Fin.sum_univ_succ g
  rw [Finset.sum_add_distrib]
  omega

theorem adjacent_sum_identity (P : WeightedPathPresentation T hn)
    (hn3 : 3 ≤ n) :
    (∑ i : Fin (n - 2),
      (T.weight (P.edgeOrder (twoFirstStep i)) +
        T.weight (P.edgeOrder (twoSecondStep i)))) +
      T.weight (P.edgeOrder ⟨0, by omega⟩) +
      T.weight (P.edgeOrder ⟨n - 2, by omega⟩) =
        2 * ∑ i : Fin (n - 1), T.weight (P.edgeOrder i) := by
  let hshape : n - 1 = (n - 2) + 1 := by omega
  let g : Fin ((n - 2) + 1) → ℕ := fun i =>
    T.weight (P.edgeOrder (Fin.cast hshape.symm i))
  have h := adjacent_sum_identity_fin g
  have hfirst (i : Fin (n - 2)) :
      Fin.cast hshape.symm (Fin.castSucc i) = twoFirstStep i := by
    apply Fin.ext
    rfl
  have hsecond (i : Fin (n - 2)) :
      Fin.cast hshape.symm i.succ = twoSecondStep i := by
    apply Fin.ext
    rfl
  have hzero : Fin.cast hshape.symm (0 : Fin ((n - 2) + 1)) =
      (⟨0, by omega⟩ : Fin (n - 1)) := by
    apply Fin.ext
    rfl
  have hlast : Fin.cast hshape.symm (Fin.last (n - 2)) =
      (⟨n - 2, by omega⟩ : Fin (n - 1)) := by
    apply Fin.ext
    simp
  have hsum : (∑ i : Fin ((n - 2) + 1), g i) =
      ∑ i : Fin (n - 1), T.weight (P.edgeOrder i) := by
    symm
    apply Fintype.sum_equiv (finCongr hshape)
      (fun i : Fin (n - 1) => T.weight (P.edgeOrder i)) g
    intro i
    simp [g, finCongr]
  simp only [g] at h
  simp_rw [hfirst, hsecond] at h
  rw [hzero, hlast, hsum] at h
  exact h

end WeightedPathPresentation

/-- Exact obstruction for every normalized weighted path of order at least
five. -/
theorem no_weightedPathPresentation_of_five_le
    {n : ℕ} {T : PosIntTree n} (hL : IsLeech T) (hn : 5 ≤ n)
    (P : WeightedPathPresentation T (by omega)) : False := by
  let E : ℕ := ∑ i : Fin (n - 1), T.weight (P.edgeOrder i)
  let S : ℕ := ∑ z : Fin (n - 1) ⊕ Fin (n - 2), P.combinedValue z
  have hE : E ≤ targetN n := by
    have h := hL.pairDist_le_target
      (VertexPair.ofDistinct (P.vertexOrder ⟨0, by omega⟩)
        (P.vertexOrder ⟨n - 1, by omega⟩)
        (P.vertexOrder.injective.ne (by
          intro q
          have hq := congrArg Fin.val q
          simp at hq
          omega)))
    rw [T.pairDist_pairOfDistinct, P.endpointDist] at h
    exact h
  have hends :
      3 ≤ T.weight (P.edgeOrder ⟨0, by omega⟩) +
        T.weight (P.edgeOrder ⟨n - 2, by omega⟩) := by
    have hp0 := T.weight_pos (P.edgeOrder ⟨0, by omega⟩)
    have hplast := T.weight_pos (P.edgeOrder ⟨n - 2, by omega⟩)
    have hne : T.weight (P.edgeOrder ⟨0, by omega⟩) ≠
        T.weight (P.edgeOrder ⟨n - 2, by omega⟩) := by
      intro hw
      have he := t1_edge_weight_injective hL hw
      have hi := P.edgeOrder.injective he
      have hv : (0 : ℕ) = n - 2 := by
        simpa using congrArg Fin.val hi
      omega
    omega
  have hSsplit : S = E +
      ∑ i : Fin (n - 2),
        (T.weight (P.edgeOrder (twoFirstStep i)) +
          T.weight (P.edgeOrder (twoSecondStep i))) := by
    simp [S, E, WeightedPathPresentation.combinedValue, Fintype.sum_sum_type]
  have hadj := P.adjacent_sum_identity (by omega)
  have hupper : S + 3 ≤ 3 * targetN n := by
    rw [hSsplit]
    omega
  have hlower := card_mul_succ_le_two_mul_sum P.combinedValue
    (P.combinedValue_pos hL) (P.combinedValue_injective hL)
  have hcard : Fintype.card (Fin (n - 1) ⊕ Fin (n - 2)) =
      (n - 1) + (n - 2) := by simp
  rw [hcard] at hlower
  change ((n - 1) + (n - 2)) * ((n - 1) + (n - 2) + 1) ≤ 2 * S at hlower
  have hN := two_mul_targetN n
  have hn1 : n = (n - 1) + 1 := by omega
  have hn2 : n = (n - 2) + 2 := by omega
  nlinarith

/-! ## From an actual spanning path to the normalized presentation -/

namespace SpanningPathAdapter

variable {n : ℕ} (T : PosIntTree n)

noncomputable def edgeAt {u v : Fin n} (p : T.graph.Walk u v)
    (i : Fin p.length) : T.Edge :=
  ⟨s(p.getVert i, p.getVert (i + 1)), p.adj_getVert_succ i.isLt⟩

@[simp] theorem edgeAt_val {u v : Fin n} (p : T.graph.Walk u v)
    (i : Fin p.length) :
    (edgeAt T p i).1 = s(p.getVert i, p.getVert (i + 1)) := rfl

theorem edgeAt_injective {u v : Fin n} (p : T.graph.Walk u v)
    (hp : p.IsPath) : Function.Injective (edgeAt T p) := by
  intro i j hij
  have hs : s(p.getVert i, p.getVert (i + 1)) =
      s(p.getVert j, p.getVert (j + 1)) := congrArg Subtype.val hij
  rcases Sym2.eq_iff.mp hs with h | h
  · apply Fin.ext
    exact hp.getVert_injOn i.isLt.le j.isLt.le h.1
  · have h1 := hp.getVert_injOn i.isLt.le (by omega : (j : ℕ) + 1 ≤ p.length) h.1
    have h2 := hp.getVert_injOn (by omega : (i : ℕ) + 1 ≤ p.length) j.isLt.le h.2
    omega

theorem edgeAt_surjective {u v : Fin n} (p : T.graph.Walk u v)
    (hcover : ∀ e : T.Edge, e.1 ∈ p.edges) :
    Function.Surjective (edgeAt T p) := by
  intro e
  have he := hcover e
  rw [← p.mem_edges_toSubgraph, T.edge_eq_mk_endpoints e,
    SimpleGraph.Subgraph.mem_edgeSet] at he
  obtain ⟨i, hi, hil⟩ := p.toSubgraph_adj_iff.mp he
  let j : Fin p.length := ⟨i, hil⟩
  refine ⟨j, ?_⟩
  apply Subtype.ext
  change s(p.getVert i, p.getVert (i + 1)) = e.1
  rw [hi, ← T.edge_eq_mk_endpoints e]

noncomputable def edgeEquiv {u v : Fin n} (p : T.graph.Walk u v)
    (hp : p.IsPath) (hcover : ∀ e : T.Edge, e.1 ∈ p.edges) :
    Fin p.length ≃ T.Edge :=
  Equiv.ofBijective (edgeAt T p)
    ⟨edgeAt_injective T p hp, edgeAt_surjective T p hcover⟩

theorem edgePair_edgeAt {u v : Fin n} (p : T.graph.Walk u v)
    (i : Fin p.length) :
    T.edgePair (edgeAt T p i) =
      VertexPair.ofDistinct (p.getVert i) (p.getVert (i + 1))
        (p.adj_getVert_succ i.isLt).ne := by
  have hcanon : T.edgePair (edgeAt T p i) =
      VertexPair.ofDistinct (T.edgeLeft (edgeAt T p i))
        (T.edgeRight (edgeAt T p i))
        (ne_of_lt (T.edgeLeft_lt_edgeRight (edgeAt T p i))) := by
    symm
    simpa [PosIntTree.edgePair] using
      (VertexPair.ofDistinct_eq_of_lt
        (ne_of_lt (T.edgeLeft_lt_edgeRight (edgeAt T p i)))
        (T.edgeLeft_lt_edgeRight (edgeAt T p i)))
  rw [hcanon, LeechTrees.QHop.VertexPair.ofDistinct_eq_iff]
  have hs : s(T.edgeLeft (edgeAt T p i), T.edgeRight (edgeAt T p i)) =
      s(p.getVert i, p.getVert (i + 1)) := by
    simpa [edgeAt] using (T.edge_eq_mk_endpoints (edgeAt T p i)).symm
  exact Sym2.eq_iff.mp hs

theorem dist_two_steps {u v : Fin n} (p : T.graph.Walk u v)
    (hp : p.IsPath) (i : ℕ) (hi : i + 1 < p.length) :
    T.dist (p.getVert i) (p.getVert (i + 2)) =
      T.weight (edgeAt T p ⟨i, by omega⟩) +
        T.weight (edgeAt T p ⟨i + 1, hi⟩) := by
  have h01 := p.adj_getVert_succ (show i < p.length by omega)
  have h12 := p.adj_getVert_succ hi
  have h02 : p.getVert i ≠ p.getVert (i + 2) := by
    intro h
    have := hp.getVert_injOn (show i ≤ p.length by omega)
      (show i + 2 ≤ p.length by omega) h
    omega
  let w : T.graph.Walk (p.getVert i) (p.getVert (i + 2)) :=
    .cons h01 (.cons h12 .nil)
  have hw : w.IsPath := by
    simp [w, h02, h01.ne, h12.ne]
  have hd := T.path_walkWeight_eq_dist
    (⟨w, hw⟩ : T.graph.Path (p.getVert i) (p.getVert (i + 2)))
  rw [← hd]
  simp only [w, PosIntTree.walkWeight, SimpleGraph.Walk.edges_cons,
    SimpleGraph.Walk.edges_nil, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  rw [← T.weightOfPair_edge (edgeAt T p ⟨i, by omega⟩),
    ← T.weightOfPair_edge (edgeAt T p ⟨i + 1, hi⟩)]
  rfl

theorem dist_eq_total_of_cover {u v : Fin n}
    (hcover : ∀ e : T.Edge, e.1 ∈ T.pathEdges u v) :
    T.dist u v = ∑ e : T.Edge, T.weight e := by
  classical
  have hsum : (∑ e : T.Edge, T.weight e) =
      ∑ x ∈ T.pathEdges u v, T.weightOfPair x := by
    apply Finset.sum_bij (fun e _ => e.1)
    · intro e _
      exact hcover e
    · intro e₁ _ e₂ _ he
      exact Subtype.ext he
    · intro x hx
      exact ⟨T.edgeOfPathMem x hx, Finset.mem_univ _, rfl⟩
    · intro e _
      exact (T.weightOfPair_edge e).symm
  unfold PosIntTree.dist
  exact hsum.symm

noncomputable def presentationOfSpanningPath {u v : Fin n}
    (p : T.graph.Walk u v) (hp : p.IsPath)
    (hcover : ∀ e : T.Edge, e.1 ∈ p.edges)
    (hlen : p.length = n - 1) (hn : 1 ≤ n) :
    WeightedPathPresentation T hn := by
  let vf : Fin n → Fin n := fun i => p.getVert i
  have hvf : Function.Injective vf := by
    intro i j hij
    have hij' : p.getVert (i : ℕ) = p.getVert (j : ℕ) := by
      simpa [vf] using hij
    have hi : (i : ℕ) ≤ p.length := by
      rw [hlen]
      omega
    have hj : (j : ℕ) ≤ p.length := by
      rw [hlen]
      omega
    have hidx : (i : ℕ) = (j : ℕ) := hp.getVert_injOn hi hj hij'
    exact Fin.ext hidx
  let ve : Fin n ≃ Fin n := Equiv.ofBijective vf
    ((Fintype.bijective_iff_injective_and_card vf).2 ⟨hvf, rfl⟩)
  let pe : Fin p.length ≃ T.Edge := edgeEquiv T p hp hcover
  let ee : Fin (n - 1) ≃ T.Edge := (finCongr hlen.symm).trans pe
  refine
    { vertexOrder := ve
      edgeOrder := ee
      edgePair_eq := ?_
      twoStepDist := ?_
      endpointDist := ?_ }
  · intro i
    change T.edgePair (edgeAt T p (Fin.cast hlen.symm i)) = _
    rw [edgePair_edgeAt]
    change VertexPair.ofDistinct (p.getVert (i : ℕ))
      (p.getVert ((i : ℕ) + 1)) _ =
        VertexPair.ofDistinct (p.getVert (i : ℕ))
          (p.getVert ((i : ℕ) + 1)) _
    rfl
  · intro i
    change T.dist (p.getVert (twoLeft i)) (p.getVert (twoRight i)) =
      T.weight (edgeAt T p (Fin.cast hlen.symm (twoFirstStep i))) +
        T.weight (edgeAt T p (Fin.cast hlen.symm (twoSecondStep i)))
    have h := dist_two_steps T p hp i (by rw [hlen]; omega)
    convert h using 1
  · change T.dist (p.getVert 0) (p.getVert (n - 1)) =
      ∑ i : Fin (n - 1), T.weight (ee i)
    have hend : p.getVert (n - 1) = v := by
      rw [← hlen, p.getVert_length]
    have hstart : p.getVert 0 = u := p.getVert_zero
    rw [hstart, hend]
    have hpath : T.path u v = ⟨p, hp⟩ := (T.path_unique ⟨p, hp⟩).symm
    have hc : ∀ e : T.Edge, e.1 ∈ T.pathEdges u v := by
      intro e
      unfold PosIntTree.pathEdges
      rw [hpath]
      simpa using hcover e
    rw [dist_eq_total_of_cover T hc]
    apply Fintype.sum_equiv ee.symm T.weight (fun i => T.weight (ee i))
    intro e
    simp

end SpanningPathAdapter

noncomputable def physicalWeightSet {n : ℕ} (T : PosIntTree n) : Finset ℕ :=
  Finset.univ.image T.weight

theorem sum_weights_eq_target_of_physicalWeightSet_eq
    {n : ℕ} {T : PosIntTree n} (hL : IsLeech T)
    (hset : physicalWeightSet T = Finset.Icc 1 (n - 1)) :
    (∑ e : T.Edge, T.weight e) = targetN n := by
  classical
  have himage : (∑ k ∈ physicalWeightSet T, k) = ∑ e : T.Edge, T.weight e := by
    unfold physicalWeightSet
    rw [Finset.sum_image]
    intro e₁ _ e₂ _ h
    exact t1_edge_weight_injective hL h
  rw [← himage, hset, sum_Icc_one_id]
  cases n <;> simp [targetN, Nat.choose_two_right, Nat.mul_comm]

theorem every_edge_on_max_path_of_physicalWeightSet_eq
    {n : ℕ} {T : PosIntTree n} (hL : IsLeech T) (hn : 2 ≤ n)
    (hset : physicalWeightSet T = Finset.Icc 1 (n - 1)) :
    ∃ p : VertexPair n, T.pairDist p = targetN n ∧
      ∀ e : T.Edge, e.1 ∈ T.pathEdges p.left p.right := by
  classical
  have hmem : targetN n ∈ Finset.Icc 1 (targetN n) := by
    rw [Finset.mem_Icc]
    constructor
    · have hc := Nat.choose_le_choose 2 hn
      simpa [targetN] using hc
    · exact le_rfl
  obtain ⟨p, hp, -⟩ := hL.target_existsUnique (targetN n) hmem
  refine ⟨p, hp, ?_⟩
  intro e
  by_contra he
  let F : Finset T.Edge := Finset.univ.filter
    (fun f => f.1 ∈ T.pathEdges p.left p.right)
  have heF : e ∉ F := by simp [F, he]
  have hrow := T.pathIncidence_row p
  unfold LeechTrees.weightedRow PosIntTree.pathIncidence at hrow
  simp only [ite_mul, one_mul, zero_mul] at hrow
  rw [← Finset.sum_filter] at hrow
  change (∑ f ∈ F, T.weight f) = T.pairDist p at hrow
  have hsub : insert e F ⊆ (Finset.univ : Finset T.Edge) := by simp
  have hle : (∑ f ∈ insert e F, T.weight f) ≤
      ∑ f : T.Edge, T.weight f :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_insert heF, hrow, hp,
    sum_weights_eq_target_of_physicalWeightSet_eq hL hset] at hle
  have hpos := T.weight_pos e
  omega

/-- The generic small-edge-spectrum obstruction: at order at least five the
physical weights cannot be exactly `1,...,n-1`. -/
theorem physicalWeightSet_ne_initial_of_five_le
    {n : ℕ} {T : PosIntTree n} (hL : IsLeech T) (hn : 5 ≤ n) :
    physicalWeightSet T ≠ Finset.Icc 1 (n - 1) := by
  intro hset
  obtain ⟨q, hq, hcover⟩ :=
    every_edge_on_max_path_of_physicalWeightSet_eq hL (by omega) hset
  let p := (T.path q.left q.right).1
  have hp : p.IsPath := (T.path q.left q.right).2
  have hcEdges : ∀ e : T.Edge, e.1 ∈ p.edges := by
    intro e
    simpa [p, PosIntTree.pathEdges] using hcover e
  let pe := SpanningPathAdapter.edgeEquiv T p hp hcEdges
  have hcard : p.length = Fintype.card T.Edge := by
    simpa using Fintype.card_congr pe
  have htree := LeechTrees.OddEdges.GraphAdapter.physicalEdge_card_add_one T
  have hlen : p.length = n - 1 := by omega
  let P := SpanningPathAdapter.presentationOfSpanningPath T p hp hcEdges hlen (by omega)
  exact no_weightedPathPresentation_of_five_le hL hn P

/-! ## Exact retention of an old indexed metric -/

def mapVertexPair {m n : ℕ} (f : Fin m ↪ Fin n) (p : VertexPair m) : VertexPair n :=
  VertexPair.ofDistinct (f p.left) (f p.right)
    (f.injective.ne (ne_of_lt p.left_lt_right))

/-- The exact distance-level content of retaining an unchanged weighted
subtree.  Every old named vertex is embedded and every indexed old pair
distance is preserved. -/
structure RetainsOldMetric {m n : ℕ} (T : PosIntTree m) (U : PosIntTree n) where
  vertex : Fin m ↪ Fin n
  pairDist_eq : ∀ p, U.pairDist (mapVertexPair vertex p) = T.pairDist p

namespace RetainsOldMetric

variable {m n : ℕ} {T : PosIntTree m} {U : PosIntTree n}

theorem oldPairMap_injective (R : RetainsOldMetric T U) (hT : IsLeech T) :
    Function.Injective (mapVertexPair R.vertex) := by
  intro p q hpq
  apply hT.pairDist_injective
  rw [← R.pairDist_eq p, ← R.pairDist_eq q, hpq]

/-- Any genuinely new indexed pair in a Leech supertree has distance beyond
the complete retained old interval. -/
theorem fresh_pair_gt_target (R : RetainsOldMetric T U)
    (hT : IsLeech T) (hU : IsLeech U) (q : VertexPair n)
    (hfresh : ∀ p, q ≠ mapVertexPair R.vertex p) :
    targetN m < U.pairDist q := by
  by_contra hnot
  have hmem : U.pairDist q ∈ Finset.Icc 1 (targetN m) := by
    rw [Finset.mem_Icc]
    exact ⟨hU.pairDist_pos q, Nat.le_of_not_gt hnot⟩
  obtain ⟨p, hp, -⟩ := hT.target_existsUnique (U.pairDist q) hmem
  have heq : q = mapVertexPair R.vertex p := by
    apply hU.pairDist_injective
    rw [R.pairDist_eq p, hp]
  exact hfresh p heq

end RetainsOldMetric

/-! ## Exact one-leaf tail characterization -/

noncomputable def rootedDepthSet {m : ℕ} (T : PosIntTree m) (v : Fin m) : Finset ℕ :=
  Finset.univ.image (fun u => T.dist v u)

noncomputable def newLeafDistanceSet {m : ℕ} (T : PosIntTree m)
    (v : Fin m) (q : ℕ) : Finset ℕ :=
  Finset.univ.image (fun u => q + T.dist v u)

def CompletesOneLeafTail {m : ℕ} (T : PosIntTree m) (v : Fin m) (q : ℕ) : Prop :=
  newLeafDistanceSet T v q = Finset.Icc (targetN m + 1) (targetN m + m)

/-- Exact characterization of when the `m` new leaf distances complete the
new target tail. -/
theorem completesOneLeafTail_iff {m : ℕ} (T : PosIntTree m) (v : Fin m)
    (q : ℕ) (hm : 1 ≤ m) :
    CompletesOneLeafTail T v q ↔
      q = targetN m + 1 ∧ rootedDepthSet T v = Finset.range m := by
  classical
  constructor
  · intro h
    have hqmem : q ∈ Finset.Icc (targetN m + 1) (targetN m + m) := by
      rw [← h]
      exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, by simp⟩
    have hlowmem : targetN m + 1 ∈ newLeafDistanceSet T v q := by
      rw [h]
      simp only [Finset.mem_Icc]
      omega
    rcases Finset.mem_image.mp hlowmem with ⟨u, -, hu⟩
    have hq : q = targetN m + 1 := by
      rw [Finset.mem_Icc] at hqmem
      omega
    refine ⟨hq, ?_⟩
    ext d
    constructor
    · intro hd
      rcases Finset.mem_image.mp hd with ⟨u, -, rfl⟩
      have hnew : q + T.dist v u ∈ Finset.Icc (targetN m + 1) (targetN m + m) := by
        rw [← h]
        exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
      rw [Finset.mem_Icc] at hnew
      simp only [Finset.mem_range]
      omega
    · intro hd
      simp only [Finset.mem_range] at hd
      have htail : targetN m + 1 + d ∈
          Finset.Icc (targetN m + 1) (targetN m + m) := by
        rw [Finset.mem_Icc]
        omega
      rw [← h] at htail
      rcases Finset.mem_image.mp htail with ⟨u, -, hu⟩
      apply Finset.mem_image.mpr
      refine ⟨u, Finset.mem_univ _, ?_⟩
      omega
  · rintro ⟨hq, hdepth⟩
    subst q
    ext d
    constructor
    · intro hd
      rcases Finset.mem_image.mp hd with ⟨u, -, rfl⟩
      have hdu : T.dist v u ∈ Finset.range m := by
        rw [← hdepth]
        exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
      simp only [Finset.mem_range] at hdu
      rw [Finset.mem_Icc]
      omega
    · intro hd
      rw [Finset.mem_Icc] at hd
      have hdelta : d - (targetN m + 1) ∈ Finset.range m := by
        simp only [Finset.mem_range]
        omega
      rw [← hdepth] at hdelta
      rcases Finset.mem_image.mp hdelta with ⟨u, -, hu⟩
      apply Finset.mem_image.mpr
      refine ⟨u, Finset.mem_univ _, ?_⟩
      omega

/-! ## Literal subdivision and unscaled gluing collisions -/

/-- Exact data used by a weight-preserving subdivision: all old distances
remain, and a genuinely new adjacent pair has positive weight strictly below
the subdivided old physical edge. -/
structure WeightPreservingSubdivisionData {m : ℕ}
    (T : PosIntTree m) (U : PosIntTree (m + 1)) where
  retain : RetainsOldMetric T U
  oldEdge : T.Edge
  newPair : VertexPair (m + 1)
  newPair_fresh : ∀ p, newPair ≠ mapVertexPair retain.vertex p
  newWeight_pos : 0 < U.pairDist newPair
  newWeight_lt_old : U.pairDist newPair < T.weight oldEdge

/-- A weight-preserving subdivision necessarily duplicates an already
retained old distance. -/
theorem no_weightPreservingSubdivision
    {m : ℕ} {T : PosIntTree m} {U : PosIntTree (m + 1)}
    (hT : IsLeech T) (hU : IsLeech U)
    (S : WeightPreservingSubdivisionData T U) : False := by
  have hnew := S.retain.fresh_pair_gt_target hT hU S.newPair S.newPair_fresh
  have hold := (Finset.mem_Icc.mp (t1_edge_weight_mem_target hT S.oldEdge)).2
  have hlt := S.newWeight_lt_old
  omega

/-- Two old indexed metrics embedded on disjoint named vertex sets.  A literal
unscaled bridge gluing supplies this data before its bridge edge is added. -/
structure UnscaledBridgeData {a b n : ℕ}
    (A : PosIntTree a) (B : PosIntTree b) (U : PosIntTree n) where
  left : RetainsOldMetric A U
  right : RetainsOldMetric B U
  images_disjoint : ∀ x y, left.vertex x ≠ right.vertex y

/-- Joining two unchanged nontrivial Leech trees already duplicates distance
one, independently of the positive bridge weight. -/
theorem no_unscaledBridge_of_nontrivial
    {a b n : ℕ} {A : PosIntTree a} {B : PosIntTree b} {U : PosIntTree n}
    (hA : IsLeech A) (hB : IsLeech B) (hU : IsLeech U)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (G : UnscaledBridgeData A B U) : False := by
  have hmemA : 1 ∈ Finset.Icc 1 (targetN a) := by
    rw [Finset.mem_Icc]
    constructor
    · omega
    · have := Nat.choose_le_choose 2 ha
      simpa [targetN] using this
  have hmemB : 1 ∈ Finset.Icc 1 (targetN b) := by
    rw [Finset.mem_Icc]
    constructor
    · omega
    · have := Nat.choose_le_choose 2 hb
      simpa [targetN] using this
  obtain ⟨p, hp, -⟩ := hA.target_existsUnique 1 hmemA
  obtain ⟨q, hq, -⟩ := hB.target_existsUnique 1 hmemB
  have heq : mapVertexPair G.left.vertex p = mapVertexPair G.right.vertex q := by
    apply hU.pairDist_injective
    rw [G.left.pairDist_eq p, G.right.pairDist_eq q, hp, hq]
  rw [mapVertexPair, mapVertexPair,
    LeechTrees.QHop.VertexPair.ofDistinct_eq_iff] at heq
  rcases heq with h | h
  · exact G.images_disjoint p.left q.left h.1
  · exact G.images_disjoint p.left q.right h.1

end LeechTrees.Extension
