import LeechTrees.Foundations
import LeechTrees.OddEdges

/-!
# Concrete graph boundary for the odd-edge kernels

This file is deliberately separate from the frozen `Foundations.lean` and
`OddEdges.lean` sources.  It defines odd physical edges for the actual
`Foundation.PosIntTree.Edge` type and proves the graph-level facts that do not
require the still-missing quotient/decomposition constructions.

It contains no assumed `OneOddDecomposition`, `TwoOddGaussianData`, T11, or
T12 conclusion.
-/

namespace LeechTrees.OddEdges.GraphAdapter

open LeechTrees.Foundation

variable {n : ℕ} (T : PosIntTree n)

/-- The actual odd physical edges of a concrete positive-integral tree. -/
noncomputable def actualOddPhysicalEdges : Finset T.Edge :=
  Finset.univ.filter fun e => Odd (T.weight e)

/-- Exactly one actual physical edge has odd weight. -/
def ExactlyOneOddPhysicalEdge : Prop :=
  (actualOddPhysicalEdges T).card = 1

/-- Exactly two actual physical edges have odd weight. -/
def ExactlyTwoOddPhysicalEdges : Prop :=
  (actualOddPhysicalEdges T).card = 2

@[simp] theorem mem_actualOddPhysicalEdges_iff (e : T.Edge) :
    e ∈ actualOddPhysicalEdges T ↔ Odd (T.weight e) := by
  classical
  simp [actualOddPhysicalEdges]

theorem exactlyOne_iff_existsUnique :
    ExactlyOneOddPhysicalEdge T ↔ ∃! e : T.Edge, Odd (T.weight e) := by
  classical
  constructor
  · intro h
    obtain ⟨e, he⟩ := Finset.card_eq_one.mp h
    refine ⟨e, ?_, ?_⟩
    · have : e ∈ actualOddPhysicalEdges T := by simp [he]
      simpa using this
    · intro f hf
      have hmem : f ∈ actualOddPhysicalEdges T := by simpa using hf
      rw [he] at hmem
      simpa using hmem
  · rintro ⟨e, he, huniq⟩
    apply Finset.card_eq_one.mpr
    refine ⟨e, ?_⟩
    ext f
    constructor
    · intro hf
      have hfodd : Odd (T.weight f) := by simpa using hf
      simp [huniq f hfodd]
    · intro hf
      have hfe : f = e := by simpa using hf
      subst f
      simpa using he

/-- The unique actual odd edge, defined only from exact cardinality one. -/
noncomputable def uniqueOddEdge (hOne : ExactlyOneOddPhysicalEdge T) : T.Edge :=
  Classical.choose ((exactlyOne_iff_existsUnique T).mp hOne)

theorem uniqueOddEdge_odd (hOne : ExactlyOneOddPhysicalEdge T) :
    Odd (T.weight (uniqueOddEdge T hOne)) :=
  (Classical.choose_spec ((exactlyOne_iff_existsUnique T).mp hOne)).1

theorem oddEdge_eq_unique (hOne : ExactlyOneOddPhysicalEdge T)
    {e : T.Edge} (he : Odd (T.weight e)) :
    e = uniqueOddEdge T hOne :=
  (Classical.choose_spec ((exactlyOne_iff_existsUnique T).mp hOne)).2 e he

/-- In the one-odd branch the unique odd edge is the forced physical
weight-one edge. -/
theorem uniqueOddEdge_weight_one
    (hL : IsLeech T) (hn : 2 ≤ n)
    (hOne : ExactlyOneOddPhysicalEdge T) :
    T.weight (uniqueOddEdge T hOne) = 1 := by
  obtain ⟨e, he, _⟩ := t1_existsUnique_weight_one hL hn
  have heOdd : Odd (T.weight e) := by simp [he]
  have heu : e = uniqueOddEdge T hOne := oddEdge_eq_unique T hOne heOdd
  simpa [← heu] using he

/-- Every other physical edge in the one-odd branch has even weight. -/
theorem even_weight_of_ne_unique
    (hOne : ExactlyOneOddPhysicalEdge T) {e : T.Edge}
    (hne : e ≠ uniqueOddEdge T hOne) : Even (T.weight e) := by
  rw [← Nat.not_odd_iff_even]
  intro he
  exact hne (oddEdge_eq_unique T hOne he)

private theorem oddPathFilter_eq_inter_unique
    (hOne : ExactlyOneOddPhysicalEdge T) (u v : Fin n) :
    (T.pathEdges u v).filter (fun f => Odd (T.weightOfPair f)) =
      T.pathEdges u v ∩ {(uniqueOddEdge T hOne).1} := by
  classical
  ext f
  simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨hf, hfOdd⟩
    have hEdgeOdd : Odd (T.weight (T.edgeOfPathMem f hf)) := by
      rw [T.weight_edgeOfPathMem f hf]
      exact hfOdd
    have hEdge : T.edgeOfPathMem f hf = uniqueOddEdge T hOne :=
      oddEdge_eq_unique T hOne hEdgeOdd
    exact ⟨hf, congrArg Subtype.val hEdge⟩
  · rintro ⟨hf, rfl⟩
    exact ⟨hf, by simpa using uniqueOddEdge_odd T hOne⟩

/-- With exactly one odd physical edge, a distance is odd exactly when its
canonical path uses that edge.  This is the concrete graph-to-parity boundary
needed before any quotient construction. -/
theorem dist_odd_iff_unique_mem
    (hOne : ExactlyOneOddPhysicalEdge T) (u v : Fin n) :
    Odd (T.dist u v) ↔
      (uniqueOddEdge T hOne).1 ∈ T.pathEdges u v := by
  classical
  change Odd (∑ f ∈ T.pathEdges u v, T.weightOfPair f) ↔ _
  rw [Finset.odd_sum_iff_odd_card_odd,
    oddPathFilter_eq_inter_unique T hOne u v]
  by_cases hmem : (uniqueOddEdge T hOne).1 ∈ T.pathEdges u v <;>
    simp [hmem]

theorem pairDist_odd_iff_unique_mem
    (hOne : ExactlyOneOddPhysicalEdge T) (p : VertexPair n) :
    Odd (T.pairDist p) ↔
      (uniqueOddEdge T hOne).1 ∈ T.pathEdges p.left p.right := by
  exact dist_odd_iff_unique_mem T hOne p.left p.right

/-- Odd indexed pairs are exactly pairs on opposite sides of the actual
one-edge deletion. -/
theorem pairDist_odd_iff_opposite_unique_cuts
    (hOne : ExactlyOneOddPhysicalEdge T) (p : VertexPair n) :
    Odd (T.pairDist p) ↔
      (T.LeftCut (uniqueOddEdge T hOne) p.left ∧
        T.RightCut (uniqueOddEdge T hOne) p.right) ∨
      (T.RightCut (uniqueOddEdge T hOne) p.left ∧
        T.LeftCut (uniqueOddEdge T hOne) p.right) := by
  rw [pairDist_odd_iff_unique_mem T hOne,
    T.mem_pathEdges_iff_opposite_cuts]

/-- Multiplicity-preserving identification of all odd-distance vertex pairs
with the actual crossing-pair index for the unique odd edge. -/
noncomputable def oddPairEquivCrossingPair
    (hOne : ExactlyOneOddPhysicalEdge T) :
    {p : VertexPair n // Odd (T.pairDist p)} ≃
      T.CrossingPair (uniqueOddEdge T hOne) :=
  Equiv.subtypeEquivProp <| funext fun p => propext <|
    pairDist_odd_iff_unique_mem T hOne p

noncomputable def oddPairEquivModOne :
    {p : VertexPair n // Odd (T.pairDist p)} ≃
      {p : VertexPair n // T.pairDist p % 2 = 1} :=
  Equiv.subtypeEquivProp <| funext fun p =>
    propext (Nat.odd_iff (n := T.pairDist p))

/-- A finite tree on `Fin n` has exactly `n-1` physical edges, in a
subtraction-free form valid also at small orders. -/
theorem physicalEdge_card_add_one :
    Fintype.card T.Edge + 1 = n := by
  simpa only [SimpleGraph.edgeFinset_card, Fintype.card_fin] using
    T.isTree.card_edgeFinset

/-- The concrete odd-edge set agrees definitionally with the frozen generic
kernel's physical-edge filter. -/
theorem actualOddPhysicalEdges_eq_kernel :
    actualOddPhysicalEdges T = oddPhysicalEdges T.weight := by
  rfl

/-- Foundation T1 discharges the weight-two premise of the frozen generic
physical-edge parity corollary. -/
theorem order18_oddPhysicalEdgeCount_ne_seventeen
    (T : PosIntTree 18) (hL : IsLeech T) :
    (actualOddPhysicalEdges T).card ≠ 17 := by
  obtain ⟨e, he, _⟩ := t1_existsUnique_weight_two hL (by decide : 3 ≤ 18)
  have hcard : Fintype.card T.Edge = 17 := by
    have h := physicalEdge_card_add_one T
    omega
  rw [actualOddPhysicalEdges_eq_kernel]
  exact LeechTrees.OddEdges.order18_oddPhysicalEdgeCount_ne_seventeen
    T.weight hcard ⟨e, he⟩

/-- The number of odd target ranks in the exact Leech interval. -/
def oddTargetCount (n : ℕ) : ℕ :=
  (oddTargetRanks (targetN n)).card

/-- The complementary number of even target ranks. -/
def evenTargetCount (n : ℕ) : ℕ :=
  targetN n - oddTargetCount n

theorem oddTargetCount_eq :
    oddTargetCount n = (targetN n + 1) / 2 := by
  simp [oddTargetCount, oddTargetRanks_card]

/-- Exact indexed cardinality of the unique-odd cut product. -/
theorem uniqueOdd_crossingPair_card
    (hL : IsLeech T) (hOne : ExactlyOneOddPhysicalEdge T) :
    Fintype.card (T.CrossingPair (uniqueOddEdge T hOne)) =
      oddTargetCount n := by
  calc
    Fintype.card (T.CrossingPair (uniqueOddEdge T hOne)) =
        Fintype.card {p : VertexPair n // Odd (T.pairDist p)} :=
      (Fintype.card_congr (oddPairEquivCrossingPair T hOne)).symm
    _ = Fintype.card
        {p : VertexPair n // T.pairDist p % 2 = 1} :=
      Fintype.card_congr (oddPairEquivModOne T)
    _ = (targetN n + 1) / 2 := oddPair_card_of_leech hL
    _ = oddTargetCount n := (oddTargetCount_eq (n := n)).symm

theorem oddTargetCount_add_evenTargetCount :
    oddTargetCount n + evenTargetCount n = targetN n := by
  unfold evenTargetCount
  have hle : oddTargetCount n ≤ targetN n := by
    rw [oddTargetCount_eq]
    omega
  omega

/-- The alternating target interval has either equal odd/even counts, or one
extra odd rank.  This is the exact `target_case` required by T11. -/
theorem oddTargetCount_evenTargetCount_case :
    oddTargetCount n = evenTargetCount n ∨
      oddTargetCount n = evenTargetCount n + 1 := by
  unfold evenTargetCount
  rw [oddTargetCount_eq]
  omega

/-!
The remaining graph adapters are intentionally not declared here: constructing
them requires the exact quotient/depth equivalences listed in the companion
dependency report.  In particular, no proposition below is allowed to store
`¬ ExactlyOneOddPhysicalEdge T` or `Even (oddTargetCount n)` as input data.
-/

end LeechTrees.OddEdges.GraphAdapter
