import LeechTrees.Expanded.FirstEdge.FirstEdgeDossier

/-!
# Exact formal boundary for the hybrid order-18 proof

The baseline theorem `firstEdge_eightRowDossier` exhausts every hypothetical
order-18 Leech tree into eight row propositions. The external computation is
responsible for establishing the eight corresponding exclusions. This file
contains only the kernel argument from those exclusions to nonexistence.
-/

namespace Leech18EndToEnd

open LeechTrees.Foundation
open LeechTrees.Foundation.FirstEdgeDossier

/-- The eight exact row-exclusion obligations discharged by the external
computer-assisted part of the proof. -/
structure RowExclusions : Prop where
  row0 :
    ∀ (T : PosIntTree 18) (_hL : IsLeech T) (e1 e2 : T.Edge),
      AdjacentNoneRow T e1 e2 → False
  row1 :
    ∀ (T : PosIntTree 18) (_hL : IsLeech T) (e1 e2 : T.Edge),
      AdjacentMeetsOneRow T e1 e2 → False
  row2 :
    ∀ (T : PosIntTree 18) (_hL : IsLeech T) (e1 e2 : T.Edge),
      AdjacentMeetsTwoRow T e1 e2 → False
  row3 :
    ∀ (T : PosIntTree 18) (_hL : IsLeech T) (e1 e2 : T.Edge),
      AdjacentMeetsBothRow T e1 e2 → False
  row4 :
    ∀ (T : PosIntTree 18) (_hL : IsLeech T) (e1 e2 : T.Edge),
      DisjointNoneRow T e1 e2 → False
  row5 :
    ∀ (T : PosIntTree 18) (_hL : IsLeech T) (e1 e2 : T.Edge),
      DisjointMeetsOneRow T e1 e2 → False
  row6 :
    ∀ (T : PosIntTree 18) (_hL : IsLeech T) (e1 e2 : T.Edge),
      DisjointMeetsTwoRow T e1 e2 → False
  row7 :
    ∀ (T : PosIntTree 18) (_hL : IsLeech T) (e1 e2 : T.Edge),
      DisjointMeetsBothRow T e1 e2 → False

/-- Exclusion of all eight exhaustive rows rules out an order-18 Leech tree. -/
theorem no_order18_leech_of_all_rows (cert : RowExclusions) :
    ¬ ∃ T : PosIntTree 18, IsLeech T := by
  rintro ⟨T, hL⟩
  obtain ⟨⟨e1, h1, _⟩, ⟨e2, h2, _⟩, rows⟩ :=
    firstEdge_eightRowDossier hL (by omega)
  rcases rows e1 e2 h1 h2 with
      h0 | h1row | h2row | h3 | h4 | h5 | h6 | h7
  · exact cert.row0 T hL e1 e2 h0
  · exact cert.row1 T hL e1 e2 h1row
  · exact cert.row2 T hL e1 e2 h2row
  · exact cert.row3 T hL e1 e2 h3
  · exact cert.row4 T hL e1 e2 h4
  · exact cert.row5 T hL e1 e2 h5
  · exact cert.row6 T hL e1 e2 h6
  · exact cert.row7 T hL e1 e2 h7

end Leech18EndToEnd

#check @LeechTrees.Foundation.FirstEdgeDossier.firstEdge_eightRowDossier
#print axioms LeechTrees.Foundation.FirstEdgeDossier.firstEdge_eightRowDossier

#check @Leech18EndToEnd.no_order18_leech_of_all_rows
#print axioms Leech18EndToEnd.no_order18_leech_of_all_rows
