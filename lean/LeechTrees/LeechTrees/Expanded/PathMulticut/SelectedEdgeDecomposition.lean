import LeechTrees.OddQuotient.RankPolynomial
import LeechTrees.Foundations

/-!
# Arbitrary selected-edge polynomial decomposition

This is the multiplicity-preserving polynomial identity for an arbitrary
family of actual named components and actual route ports.  The certificate is
noncircular: it consists of a genuine indexed pair partition and pointwise
distance decompositions.  It contains no coefficientwise target identity and
no injectivity assumption.  Consequently the theorem applies before asking
whether the ambient weighted tree is Leech.
-/

open scoped BigOperators Polynomial

namespace LeechTrees.PathMulticut

open LeechTrees.OddQuotient

noncomputable section

/-- Increasingly oriented pairs of distinct component names. -/
abbrev ComponentPair (Component : Type*) [LT Component] :=
  {q : Component × Component // q.1 < q.2}

namespace ComponentPair

def left {Component : Type*} [LT Component]
    (q : ComponentPair Component) : Component := q.1.1

def right {Component : Type*} [LT Component]
    (q : ComponentPair Component) : Component := q.1.2

end ComponentPair

/-- Exact data needed for the selected-edge gluing identity.

`pairPartition` says that every indexed ambient pair is either internal to one
named component or belongs to one ordered pair of distinct components.
`internal_distance` and `cross_distance` are pointwise metric statements.  In
the graph adapter, the latter is proved using the two actual exit ports and
the selected-edge route between them.
-/
structure SelectedEdgeDecomposition
    (Pair Component : Type*) [Fintype Pair] [Fintype Component]
    [LinearOrder Component] where
  Vertex : Component → Type*
  InternalPair : Component → Type*
  vertexFintype : ∀ C, Fintype (Vertex C)
  internalPairFintype : ∀ C, Fintype (InternalPair C)
  pairRank : Pair → ℕ
  internalRank : ∀ C, InternalPair C → ℕ
  leftDepth : ∀ q : ComponentPair Component, Vertex q.left → ℕ
  rightDepth : ∀ q : ComponentPair Component, Vertex q.right → ℕ
  routeLength : ComponentPair Component → ℕ
  pairPartition :
    Pair ≃
      (Σ C : Component, InternalPair C) ⊕
        (Σ q : ComponentPair Component, Vertex q.left × Vertex q.right)
  internal_distance : ∀ x : Σ C : Component, InternalPair C,
    pairRank (pairPartition.symm (Sum.inl x)) = internalRank x.1 x.2
  cross_distance :
    ∀ x : Σ q : ComponentPair Component, Vertex q.left × Vertex q.right,
      pairRank (pairPartition.symm (Sum.inr x)) =
        routeLength x.1 + leftDepth x.1 x.2.1 + rightDepth x.1 x.2.2

attribute [instance]
  SelectedEdgeDecomposition.vertexFintype
  SelectedEdgeDecomposition.internalPairFintype

namespace SelectedEdgeDecomposition

variable {Pair Component : Type*} [Fintype Pair] [Fintype Component]
  [LinearOrder Component]

/-- The exact internal polynomial of one named component. -/
def internalPoly (D : SelectedEdgeDecomposition Pair Component)
    (C : Component) : ℕ[X] :=
  rankPoly (D.internalRank C)

/-- Rooted distance polynomial from the named left exit port. -/
def leftRootedPoly (D : SelectedEdgeDecomposition Pair Component)
    (q : ComponentPair Component) : ℕ[X] :=
  rankPoly (D.leftDepth q)

/-- Rooted distance polynomial from the named right exit port. -/
def rightRootedPoly (D : SelectedEdgeDecomposition Pair Component)
    (q : ComponentPair Component) : ℕ[X] :=
  rankPoly (D.rightDepth q)

/-- One exact cross-component block, retaining all indexed multiplicities. -/
def crossPoly (D : SelectedEdgeDecomposition Pair Component)
    (q : ComponentPair Component) : ℕ[X] :=
  Polynomial.monomial (D.routeLength q) 1 *
    D.leftRootedPoly q * D.rightRootedPoly q

/-- Arbitrary selected-edge quotient gluing polynomial:

`P_T = Σ_i P_i + Σ_{i<j} z^{L_ij} R_{i,p_ij} R_{j,p_ji}`.

The proof is an indexed partition followed by the shifted Cartesian-product
convolution; no support-set deduplication is used.
-/
theorem selectedEdge_gluing_polynomial
    (D : SelectedEdgeDecomposition Pair Component) :
    rankPoly D.pairRank =
      (∑ C : Component, D.internalPoly C) +
        ∑ q : ComponentPair Component, D.crossPoly q := by
  classical
  let splitRank :
      (Σ C : Component, D.InternalPair C) ⊕
        (Σ q : ComponentPair Component,
          D.Vertex q.left × D.Vertex q.right) → ℕ :=
    Sum.elim
      (fun x => D.internalRank x.1 x.2)
      (fun x => D.routeLength x.1 + D.leftDepth x.1 x.2.1 +
        D.rightDepth x.1 x.2.2)
  have hreindex : rankPoly D.pairRank = rankPoly splitRank := by
    apply rankPoly_equiv D.pairPartition D.pairRank splitRank
    intro p
    cases hp : D.pairPartition p with
    | inl x =>
        have hback : D.pairPartition.symm (Sum.inl x) = p := by
          rw [← hp]
          simp
        simpa [splitRank, hback] using (D.internal_distance x).symm
    | inr x =>
        have hback : D.pairPartition.symm (Sum.inr x) = p := by
          rw [← hp]
          simp
        simpa [splitRank, hback] using (D.cross_distance x).symm
  rw [hreindex, rankPoly_sum, rankPoly_sigma, rankPoly_sigma]
  apply congrArg₂ (· + ·)
  · rfl
  · apply Finset.sum_congr rfl
    intro q hq
    exact rankPoly_shift_add_product
      (D.routeLength q) (D.leftDepth q) (D.rightDepth q)

/-- Coefficientwise form: a coefficient is the sum of the exact internal
fibre counts and exact shifted Cartesian-product fibre counts. -/
theorem selectedEdge_gluing_coefficient
    (D : SelectedEdgeDecomposition Pair Component) (k : ℕ) :
    (rankPoly D.pairRank).coeff k =
      (∑ C : Component,
        Fintype.card {x : D.InternalPair C // D.internalRank C x = k}) +
      ∑ q : ComponentPair Component,
        Fintype.card
          {z : D.Vertex q.left × D.Vertex q.right //
            D.routeLength q + D.leftDepth q z.1 + D.rightDepth q z.2 = k} := by
  rw [D.selectedEdge_gluing_polynomial]
  simp only [Polynomial.coeff_add, Polynomial.finset_sum_coeff,
    internalPoly, rankPoly_coeff, crossPoly, leftRootedPoly, rightRootedPoly,
    coeff_shifted_rankPoly_product]

/-- Coefficientwise equality to the interval target is literally equivalent
to the Leech multiplicity requirement: coefficient one on `1..N` and zero
elsewhere.  This theorem deliberately does not infer a tree lift from an
arbitrary polynomial decomposition. -/
theorem gluing_eq_target_iff_coefficients
    (D : SelectedEdgeDecomposition Pair Component) (N : ℕ) :
    rankPoly D.pairRank = ∑ d ∈ Finset.Icc 1 N, Polynomial.monomial d 1 ↔
      ∀ k,
        (rankPoly D.pairRank).coeff k = if k ∈ Finset.Icc 1 N then 1 else 0 := by
  constructor
  · intro h k
    rw [h, Polynomial.finset_sum_coeff]
    simp [Polynomial.coeff_monomial]
  · intro h
    apply Polynomial.ext
    intro k
    rw [h, Polynomial.finset_sum_coeff]
    simp [Polynomial.coeff_monomial]

end SelectedEdgeDecomposition

end

end LeechTrees.PathMulticut
