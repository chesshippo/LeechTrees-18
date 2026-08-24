import SemanticBridge.RowCore

/-! # The four disjoint first-pair rows -/

namespace Leech18SemanticBridge

open LeechTrees.Foundation
open LeechTrees.Foundation.FirstEdgeDossier

theorem disjointNoneRow_implies_core {n : Nat} {T : PosIntTree n}
    {e1 e2 : T.Edge} (h : DisjointNoneRow T e1 e2) :
    RowCore row4Descriptor T e1 e2 := by
  rcases h.witness3 with ⟨e3, h3, hunique, h31, h32⟩
  refine ⟨h.disjoint12, e3, h3, hunique, ⟨h31, h32⟩, ?_⟩
  simpa [row4Descriptor] using h.forced4

theorem disjointMeetsOneRow_implies_core {n : Nat} {T : PosIntTree n}
    {e1 e2 : T.Edge} (h : DisjointMeetsOneRow T e1 e2) :
    RowCore row5Descriptor T e1 e2 := by
  rcases h.witness3 with ⟨e3, h3, hunique, h31, h32⟩
  refine ⟨h.disjoint12, e3, h3, hunique, ⟨h31, h32⟩, ?_⟩
  simpa [row5Descriptor] using h.forced5

theorem disjointMeetsTwoRow_implies_core {n : Nat} {T : PosIntTree n}
    {e1 e2 : T.Edge} (h : DisjointMeetsTwoRow T e1 e2) :
    RowCore row6Descriptor T e1 e2 := by
  rcases h.witness3 with ⟨e3, h3, hunique, h31, h32⟩
  refine ⟨h.disjoint12, e3, h3, hunique, ⟨h31, h32⟩, ?_⟩
  simpa [row6Descriptor] using h.forced4

theorem disjointMeetsBothRow_implies_core {n : Nat} {T : PosIntTree n}
    {e1 e2 : T.Edge} (h : DisjointMeetsBothRow T e1 e2) :
    RowCore row7Descriptor T e1 e2 := by
  rcases h.witness3 with ⟨e3, h3, hunique, h31, h32, _hcut⟩
  refine ⟨h.disjoint12, e3, h3, hunique, ⟨h31, h32⟩, ?_⟩
  simpa [row7Descriptor] using h.forced7

theorem disjointNoneRow_implies_realized_core {n : Nat} {T : PosIntTree n}
    {e1 e2 : T.Edge} (h : DisjointNoneRow T e1 e2) :
    RealizedRowCore row4Descriptor T e1 e2 :=
  ⟨row4Descriptor_wellFormed, disjointNoneRow_implies_core h⟩

theorem disjointMeetsOneRow_implies_realized_core
    {n : Nat} {T : PosIntTree n} {e1 e2 : T.Edge}
    (h : DisjointMeetsOneRow T e1 e2) :
    RealizedRowCore row5Descriptor T e1 e2 :=
  ⟨row5Descriptor_wellFormed, disjointMeetsOneRow_implies_core h⟩

theorem disjointMeetsTwoRow_implies_realized_core
    {n : Nat} {T : PosIntTree n} {e1 e2 : T.Edge}
    (h : DisjointMeetsTwoRow T e1 e2) :
    RealizedRowCore row6Descriptor T e1 e2 :=
  ⟨row6Descriptor_wellFormed, disjointMeetsTwoRow_implies_core h⟩

theorem disjointMeetsBothRow_implies_realized_core
    {n : Nat} {T : PosIntTree n} {e1 e2 : T.Edge}
    (h : DisjointMeetsBothRow T e1 e2) :
    RealizedRowCore row7Descriptor T e1 e2 :=
  ⟨row7Descriptor_wellFormed, disjointMeetsBothRow_implies_core h⟩

end Leech18SemanticBridge
