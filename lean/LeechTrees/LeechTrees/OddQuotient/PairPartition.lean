import LeechTrees.OddQuotient.QuotientRoutes
import LeechTrees.OddQuotient.RankPolynomial

/-!
# Indexed component-pair partition

The quotient index below ranges over every unordered pair of distinct even
components, not merely over adjacent quotient vertices.  It is oriented once
using the fixed named representative supplied by `componentRep`.  The final
equivalence partitions every global unordered named-vertex pair into exactly
one within-component index or exactly one Cartesian cross-component index.
-/

namespace LeechTrees.OddQuotient

open LeechTrees.Foundation

variable {n : ℕ}

/-- The fixed named representatives of distinct even components are
distinct. -/
theorem componentRep_injective (T : PosIntTree n) :
    Function.Injective (componentRep T) := by
  intro C D h
  have hc := congrArg (componentOf T) h
  simpa using hc

/-- An internal unordered pair in one component.  The inherited order on
the named vertices gives its unique increasing orientation. -/
abbrev InternalPair (T : PosIntTree n) (C : EvenComponent T) :=
  {z : ComponentVertex T C × ComponentVertex T C // z.1.1 < z.2.1}

/-- All within-component pairs, with their component retained as an index. -/
abbrev WithinIndex (T : PosIntTree n) :=
  Σ C : EvenComponent T, InternalPair T C

/-- Every unordered pair of distinct even components, oriented once by the
fixed named representatives.  This type includes nonadjacent component
pairs; restricting it to `quotientGraph.edgeSet` would be incorrect. -/
abbrev QuotientComponentPair (T : PosIntTree n) :=
  {q : EvenComponent T × EvenComponent T //
    componentRep T q.1 < componentRep T q.2}

namespace QuotientComponentPair

def left (q : QuotientComponentPair T) : EvenComponent T := q.1.1

def right (q : QuotientComponentPair T) : EvenComponent T := q.1.2

@[simp] theorem left_mk (C D : EvenComponent T)
    (h : componentRep T C < componentRep T D) :
    left (⟨(C, D), h⟩ : QuotientComponentPair T) = C := rfl

@[simp] theorem right_mk (C D : EvenComponent T)
    (h : componentRep T C < componentRep T D) :
    right (⟨(C, D), h⟩ : QuotientComponentPair T) = D := rfl

theorem ne (q : QuotientComponentPair T) : q.left ≠ q.right := by
  intro h
  have hlt : componentRep T q.left < componentRep T q.right := q.2
  exact (ne_of_lt hlt) (congrArg (componentRep T) h)

end QuotientComponentPair

/-- All cross-component endpoint pairs.  The base remembers one oriented
unordered component pair and the fibre is the full Cartesian product of its
two named vertex sets. -/
abbrev CrossIndex (T : PosIntTree n) :=
  Σ q : QuotientComponentPair T,
    ComponentVertex T q.left × ComponentVertex T q.right

private theorem componentRep_lt_reverse_of_ne_not_lt
    (T : PosIntTree n) {C D : EvenComponent T}
    (hne : C ≠ D) (hnot : ¬componentRep T C < componentRep T D) :
    componentRep T D < componentRep T C := by
  have hrepNe : componentRep T D ≠ componentRep T C := by
    intro h
    apply hne
    exact componentRep_injective T h.symm
  exact lt_of_le_of_ne (le_of_not_gt hnot) hrepNe

/-- Send one global pair to its unique within-component or cross-component
index. -/
noncomputable def pairToIndex (T : PosIntTree n) :
    VertexPair n → WithinIndex T ⊕ CrossIndex T := fun p =>
  let C := componentOf T p.left
  let D := componentOf T p.right
  if hCD : C = D then
    Sum.inl ⟨C,
      ⟨(⟨p.left, rfl⟩, ⟨p.right, hCD.symm⟩), p.left_lt_right⟩⟩
  else if hrep : componentRep T C < componentRep T D then
    Sum.inr ⟨⟨(C, D), hrep⟩,
      (⟨p.left, rfl⟩, ⟨p.right, rfl⟩)⟩
  else
    Sum.inr ⟨
      ⟨(D, C), componentRep_lt_reverse_of_ne_not_lt T hCD hrep⟩,
      (⟨p.right, rfl⟩, ⟨p.left, rfl⟩)⟩

/-- Forget an indexed within/cross pair back to the unique increasing global
`VertexPair`. -/
noncomputable def indexToPair (T : PosIntTree n) :
    WithinIndex T ⊕ CrossIndex T → VertexPair n
  | .inl z =>
      ⟨(z.2.1.1.1, z.2.1.2.1), z.2.2⟩
  | .inr z =>
      VertexPair.ofDistinct z.2.1.1 z.2.2.1 <| by
        intro h
        apply z.1.ne
        exact z.2.1.2.symm.trans
          ((congrArg (componentOf T) h).trans z.2.2.2)

private theorem ofDistinct_pair_left_right (p : VertexPair n) :
    VertexPair.ofDistinct p.left p.right
      (ne_of_lt p.left_lt_right) = p := by
  rw [VertexPair.ofDistinct_eq_of_lt (ne_of_lt p.left_lt_right)
    p.left_lt_right]
  apply VertexPair.ext <;> rfl

/-- The exact indexed partition of all global unordered named-vertex pairs.
In particular, its cross branch is a sigma of genuine Cartesian products,
so no component-pair block is duplicated or deduplicated. -/
noncomputable def vertexPairIndexEquiv (T : PosIntTree n) :
    VertexPair n ≃ WithinIndex T ⊕ CrossIndex T where
  toFun := pairToIndex T
  invFun := indexToPair T
  left_inv := by
    intro p
    unfold pairToIndex
    dsimp only
    by_cases hCD : componentOf T p.left = componentOf T p.right
    · simp [hCD, indexToPair]
      exact VertexPair.ext rfl rfl
    · by_cases hrep :
          componentRep T (componentOf T p.left) <
            componentRep T (componentOf T p.right)
      · simp [hCD, hrep, indexToPair, ofDistinct_pair_left_right]
      · have hrev : ¬p.right < p.left :=
          not_lt_of_ge p.left_lt_right.le
        simp [hCD, hrep, indexToPair, VertexPair.ofDistinct, hrev]
        apply VertexPair.ext <;> rfl
  right_inv := by
    intro z
    cases z with
    | inl z =>
        rcases z with ⟨C, w⟩
        rcases w with ⟨⟨uC, vC⟩, huv⟩
        rcases uC with ⟨u, hu⟩
        rcases vC with ⟨v, hv⟩
        cases hu
        have hcomp : componentOf T u = componentOf T v := hv.symm
        change pairToIndex T (⟨(u, v), huv⟩ : VertexPair n) = _
        unfold pairToIndex
        dsimp only [VertexPair.left, VertexPair.right]
        rw [dif_pos hcomp]
    | inr z =>
        rcases z with ⟨q, uv⟩
        rcases q with ⟨⟨C, D⟩, hCD⟩
        rcases uv with ⟨uC, vD⟩
        rcases uC with ⟨u, hu⟩
        rcases vD with ⟨v, hv⟩
        cases hu
        cases hv
        have hcomp : componentOf T u ≠ componentOf T v := by
          intro h
          exact (ne_of_lt hCD) (congrArg (componentRep T) h)
        have huv : u ≠ v := fun h =>
          hcomp (congrArg (componentOf T) h)
        by_cases hlt : u < v
        · change pairToIndex T (VertexPair.ofDistinct u v huv) = _
          rw [VertexPair.ofDistinct_eq_of_lt _ hlt]
          unfold pairToIndex
          dsimp only [VertexPair.left, VertexPair.right]
          have hrep :
              componentRep T (componentOf T u) <
                componentRep T (componentOf T v) := hCD
          rw [dif_neg hcomp, dif_pos hrep]
          apply congrArg Sum.inr
          apply Sigma.ext rfl
          apply heq_of_eq
          apply Prod.ext <;> apply Subtype.ext <;> rfl
        · have hvu : v < u :=
            lt_of_le_of_ne (le_of_not_gt hlt) huv.symm
          have hnotRev :
              ¬componentRep T (componentOf T v) <
                componentRep T (componentOf T u) :=
            not_lt_of_ge hCD.le
          have hcompRev : componentOf T v ≠ componentOf T u :=
            hcomp.symm
          change pairToIndex T (VertexPair.ofDistinct u v huv) = _
          unfold VertexPair.ofDistinct
          rw [dif_neg hlt]
          unfold pairToIndex
          dsimp only [VertexPair.left, VertexPair.right]
          rw [dif_neg hcompRev, dif_neg hnotRev]
          apply congrArg Sum.inr
          apply Sigma.ext rfl
          apply heq_of_eq
          apply Prod.ext <;> apply Subtype.ext <;> rfl

/-- The global pair recovered from an internal index has exactly its two
stored named endpoints. -/
@[simp] theorem indexToPair_internal (T : PosIntTree n)
    (z : WithinIndex T) :
    (indexToPair T (.inl z)).left = z.2.1.1.1 ∧
      (indexToPair T (.inl z)).right = z.2.1.2.1 := by
  exact ⟨rfl, rfl⟩

/-- A cross index recovers the same unordered endpoint pair, independently
of which endpoint is smaller in the global naming order. -/
theorem indexToPair_cross_sym2 (T : PosIntTree n)
    (z : CrossIndex T) :
    s((indexToPair T (.inr z)).left,
        (indexToPair T (.inr z)).right) =
      s(z.2.1.1, z.2.2.1) := by
  unfold indexToPair
  by_cases hlt : z.2.1.1 < z.2.2.1
  · simp [VertexPair.ofDistinct, hlt, VertexPair.left, VertexPair.right]
  · simp [VertexPair.ofDistinct, hlt, VertexPair.left, VertexPair.right,
      Sym2.eq_swap]

end LeechTrees.OddQuotient
