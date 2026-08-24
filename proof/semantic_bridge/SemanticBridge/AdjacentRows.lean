import SemanticBridge.RowCore

/-! # The four adjacent first-pair rows -/

namespace Leech18SemanticBridge

open LeechTrees.Foundation
open LeechTrees.Foundation.FirstEdgeDossier

theorem adjacentNoneRow_implies_core {n : Nat} {T : PosIntTree n}
    {e1 e2 : T.Edge} (h : AdjacentNoneRow T e1 e2) :
    RowCore row0Descriptor T e1 e2 := by
  rcases h.witness4 with ⟨e4, h4, hunique, h41, h42⟩
  refine ⟨h.adjacent12, e4, h4, hunique, ⟨h41, h42⟩, ?_⟩
  simpa [row0Descriptor] using h.forced5

theorem adjacentMeetsOneRow_implies_core {n : Nat} {T : PosIntTree n}
    {e1 e2 : T.Edge} (h : AdjacentMeetsOneRow T e1 e2) :
    RowCore row1Descriptor T e1 e2 := by
  rcases h.witness4 with ⟨e4, h4, hunique, h41, h42⟩
  refine ⟨h.adjacent12, e4, h4, hunique, ⟨h41, h42⟩, ?_⟩
  simpa [row1Descriptor] using h.forced6

theorem adjacentMeetsTwoRow_implies_core {n : Nat} {T : PosIntTree n}
    {e1 e2 : T.Edge} (h : AdjacentMeetsTwoRow T e1 e2) :
    RowCore row2Descriptor T e1 e2 := by
  rcases h.witness4 with ⟨e4, h4, hunique, h41, h42⟩
  refine ⟨h.adjacent12, e4, h4, hunique, ⟨h41, h42⟩, ?_⟩
  simpa [row2Descriptor] using h.forced5

theorem adjacentMeetsBothRow_implies_core {n : Nat} {T : PosIntTree n}
    {e1 e2 : T.Edge} (h : AdjacentMeetsBothRow T e1 e2) :
    RowCore row3Descriptor T e1 e2 := by
  rcases h.witness4 with ⟨e4, h4, hunique, h41, h42⟩
  refine ⟨h.adjacent12, e4, h4, hunique, ⟨h41, h42⟩, ?_⟩
  simpa [row3Descriptor] using h.forced7

theorem adjacentNoneRow_implies_realized_core {n : Nat} {T : PosIntTree n}
    {e1 e2 : T.Edge} (h : AdjacentNoneRow T e1 e2) :
    RealizedRowCore row0Descriptor T e1 e2 :=
  ⟨row0Descriptor_wellFormed, adjacentNoneRow_implies_core h⟩

theorem adjacentMeetsOneRow_implies_realized_core
    {n : Nat} {T : PosIntTree n} {e1 e2 : T.Edge}
    (h : AdjacentMeetsOneRow T e1 e2) :
    RealizedRowCore row1Descriptor T e1 e2 :=
  ⟨row1Descriptor_wellFormed, adjacentMeetsOneRow_implies_core h⟩

theorem adjacentMeetsTwoRow_implies_realized_core
    {n : Nat} {T : PosIntTree n} {e1 e2 : T.Edge}
    (h : AdjacentMeetsTwoRow T e1 e2) :
    RealizedRowCore row2Descriptor T e1 e2 :=
  ⟨row2Descriptor_wellFormed, adjacentMeetsTwoRow_implies_core h⟩

theorem adjacentMeetsBothRow_implies_realized_core
    {n : Nat} {T : PosIntTree n} {e1 e2 : T.Edge}
    (h : AdjacentMeetsBothRow T e1 e2) :
    RealizedRowCore row3Descriptor T e1 e2 :=
  ⟨row3Descriptor_wellFormed, adjacentMeetsBothRow_implies_core h⟩

end Leech18SemanticBridge
