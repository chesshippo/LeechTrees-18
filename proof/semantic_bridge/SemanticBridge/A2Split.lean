import SemanticBridge.AdjacentRows

/-! # Formal exhaustiveness of the two production A2 weight-five prefixes -/

namespace Leech18SemanticBridge

open LeechTrees.Foundation
open LeechTrees.Foundation.FirstEdgeDossier

/-- The exact two-way weight-5 split used by the production A2 search.

The `Or` is deliberately ordered as the source: prefix I has the weight-5
edge endpoint-disjoint from the weight-4 edge, while prefix II attaches it to
the weight-4 edge.  Disjointness from weights 1 and 2 makes the latter
attachment occur at the far endpoint of the weight-4 edge. -/
def A2ProductionSplit {n : Nat} (T : PosIntTree n)
    (e1 e2 : T.Edge) : Prop :=
  ∃ e4 e5 : T.Edge,
    T.weight e4 = 4 ∧
    (∀ f : T.Edge, T.weight f = 4 → f = e4) ∧
    T.weight e5 = 5 ∧
    (∀ f : T.Edge, T.weight f = 5 → f = e5) ∧
    T.EdgeEndpointDisjoint e5 e1 ∧
    T.EdgeEndpointDisjoint e5 e2 ∧
    (T.EdgeEndpointDisjoint e5 e4 ∨ T.EdgeAdjacent e5 e4)

theorem adjacentMeetsTwoRow_implies_a2_production_split
    {n : Nat} {T : PosIntTree n} {e1 e2 : T.Edge}
    (h : AdjacentMeetsTwoRow T e1 e2) :
    A2ProductionSplit T e1 e2 := by
  rcases h.witness4 with ⟨e4, h4, h4unique, _h41, _h42⟩
  rcases h.forced5 with ⟨e5, h5, h5unique, _hspectrum, _hmex⟩
  have hne : e5 ≠ e4 := by
    intro heq
    have h45 : (4 : Nat) = 5 := h4.symm.trans (by simpa [heq] using h5)
    omega
  have h51 := h.weight5_disjoint_e1 e5 h5
  have h52 := h.weight5_disjoint_e2 e5 h5
  rcases T.edgeAdjacent_or_endpointDisjoint hne with hadj | hdis
  · exact ⟨e4, e5, h4, h4unique, h5, h5unique, h51, h52, Or.inr hadj⟩
  · exact ⟨e4, e5, h4, h4unique, h5, h5unique, h51, h52, Or.inl hdis⟩

end Leech18SemanticBridge
