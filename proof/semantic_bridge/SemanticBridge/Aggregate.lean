import SemanticBridge.A2Split
import SemanticBridge.DisjointRows

/-! # Aggregate eight-row bridge -/

namespace Leech18SemanticBridge

open LeechTrees.Foundation
open LeechTrees.Foundation.FirstEdgeDossier

/-- Every disjunct of the authoritative dossier maps to a descriptor whose
literal `seedEdges` compute the same incidence/support/MEX core. -/
theorem eightRowDossier_implies_some_realized_core
    {n : Nat} {T : PosIntTree n} {e1 e2 : T.Edge}
    (h : EightRowDossier T e1 e2) :
    ∃ d ∈ rowDescriptors, RealizedRowCore d T e1 e2 := by
  rcases h with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · exact ⟨row0Descriptor, by simp [rowDescriptors],
      adjacentNoneRow_implies_realized_core h0⟩
  · exact ⟨row1Descriptor, by simp [rowDescriptors],
      adjacentMeetsOneRow_implies_realized_core h1⟩
  · exact ⟨row2Descriptor, by simp [rowDescriptors],
      adjacentMeetsTwoRow_implies_realized_core h2⟩
  · exact ⟨row3Descriptor, by simp [rowDescriptors],
      adjacentMeetsBothRow_implies_realized_core h3⟩
  · exact ⟨row4Descriptor, by simp [rowDescriptors],
      disjointNoneRow_implies_realized_core h4⟩
  · exact ⟨row5Descriptor, by simp [rowDescriptors],
      disjointMeetsOneRow_implies_realized_core h5⟩
  · exact ⟨row6Descriptor, by simp [rowDescriptors],
      disjointMeetsTwoRow_implies_realized_core h6⟩
  · exact ⟨row7Descriptor, by simp [rowDescriptors],
      disjointMeetsBothRow_implies_realized_core h7⟩

/-- Compatibility theorem retaining the original public name and statement. -/
theorem eightRowDossier_implies_some_core {n : Nat} {T : PosIntTree n}
    {e1 e2 : T.Edge} (h : EightRowDossier T e1 e2) :
    ∃ d ∈ rowDescriptors, RowCore d T e1 e2 := by
  obtain ⟨d, hd, _hwellFormed, hcore⟩ :=
    eightRowDossier_implies_some_realized_core h
  exact ⟨d, hd, hcore⟩

/-- Strong formal end of the descriptor bridge. -/
theorem isLeech_implies_some_realized_seed_descriptor
    {n : Nat} {T : PosIntTree n} (hL : IsLeech T) (hn : 5 ≤ n) :
    ∃ e1 e2 : T.Edge, ∃ d ∈ rowDescriptors,
      T.weight e1 = 1 ∧ T.weight e2 = 2 ∧ RealizedRowCore d T e1 e2 := by
  obtain ⟨⟨e1, h1, _⟩, ⟨e2, h2, _⟩, hrows⟩ :=
    firstEdge_eightRowDossier hL hn
  obtain ⟨d, hd, hrealized⟩ :=
    eightRowDossier_implies_some_realized_core (hrows e1 e2 h1 h2)
  exact ⟨e1, e2, d, hd, h1, h2, hrealized⟩

/-- Compatibility theorem retaining the original public name and statement. -/
theorem isLeech_implies_some_seed_descriptor {n : Nat} {T : PosIntTree n}
    (hL : IsLeech T) (hn : 5 ≤ n) :
    ∃ e1 e2 : T.Edge, ∃ d ∈ rowDescriptors,
      T.weight e1 = 1 ∧ T.weight e2 = 2 ∧ RowCore d T e1 e2 := by
  obtain ⟨e1, e2, d, hd, h1, h2, _hwellFormed, hcore⟩ :=
    isLeech_implies_some_realized_seed_descriptor hL hn
  exact ⟨e1, e2, d, hd, h1, h2, hcore⟩

end Leech18SemanticBridge
