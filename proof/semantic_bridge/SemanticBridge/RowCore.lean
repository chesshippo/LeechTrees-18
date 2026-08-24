import SemanticBridge.DescriptorWellFormed
import LeechTrees.Expanded.FirstEdge.FirstEdgeDossier

/-! # Formal projection shared by all eight rows -/

namespace Leech18SemanticBridge

open LeechTrees.Foundation
open LeechTrees.Foundation.FirstEdgeDossier

theorem mexPos_eq_of_positiveMexCondition {support : Finset Nat} {next : Nat}
    (h : PositiveMexCondition support next) :
    PosIntTree.mexPos support = next := by
  apply Nat.le_antisymm
  · by_contra hnot
    have hlt : next < PosIntTree.mexPos support := by omega
    exact h.2.1 (PosIntTree.pos_lt_mexPos_mem support h.1 hlt)
  · by_contra hnot
    have hlt : PosIntTree.mexPos support < next := by omega
    have hIco : PosIntTree.mexPos support ∈ Finset.Ico 1 next := by
      simp only [Finset.mem_Ico]
      exact ⟨PosIntTree.mexPos_pos support, hlt⟩
    have hsubset : Finset.Ico 1 next ⊆ support := by
      exact Finset.sdiff_eq_empty_iff_subset.mp h.2.2
    exact PosIntTree.mexPos_not_mem support (hsubset hIco)

def firstPairHolds {n : Nat} (r : FirstPairRelation)
    (T : PosIntTree n) (e1 e2 : T.Edge) : Prop :=
  match r with
  | .adjacent => T.EdgeAdjacent e1 e2
  | .disjoint => T.EdgeEndpointDisjoint e1 e2

def witnessContactHolds {n : Nat} (c : WitnessContact)
    (T : PosIntTree n) (e1 e2 witness : T.Edge) : Prop :=
  match c with
  | .none =>
      T.EdgeEndpointDisjoint witness e1 ∧
        T.EdgeEndpointDisjoint witness e2
  | .meetsWeightOne =>
      T.EdgeAdjacent witness e1 ∧ T.EdgeEndpointDisjoint witness e2
  | .meetsWeightTwo =>
      T.EdgeEndpointDisjoint witness e1 ∧ T.EdgeAdjacent witness e2
  | .meetsBoth => T.EdgeAdjacent witness e1 ∧ T.EdgeAdjacent witness e2

/-- The formal facts needed to identify the solver seed.  This is deliberately
a projection: row-specific path, cut, and future-edge side conditions may make
the formal row smaller, so forgetting them can only enlarge the searched set.

`DescriptorWellFormed d`, required by the aggregate theorem, independently
ties every field here to `d.seedEdges`. -/
def RowCore {n : Nat} (d : RowDescriptor)
    (T : PosIntTree n) (e1 e2 : T.Edge) : Prop :=
  firstPairHolds d.firstPair T e1 e2 ∧
    ∃ witness : T.Edge,
      T.weight witness = d.witnessWeight ∧
      (∀ f : T.Edge, T.weight f = d.witnessWeight → f = witness) ∧
      witnessContactHolds d.witnessContact T e1 e2 witness ∧
      ForcedPrefixEdge T d.nextWeight d.currentSupport.toFinset

/-- Explicit combined predicate used at the boundary.  Unlike the earlier
projection alone, this proposition cannot ignore `seedEdges`: its first field
computes all descriptor semantics from the literal numeric seed. -/
def RealizedRowCore {n : Nat} (d : RowDescriptor)
    (T : PosIntTree n) (e1 e2 : T.Edge) : Prop :=
  DescriptorWellFormed d ∧ RowCore d T e1 e2

end Leech18SemanticBridge
