import SemanticBridge.DescriptorData
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Executable semantics of a three-edge solver seed

`DescriptorWellFormed` is the missing data-level link: it computes incidence,
the complete distance support of a simple three-edge forest, and the positive
MEX directly from `RowDescriptor.seedEdges`, then requires those values to be
the descriptor fields used by the formal row proofs.
-/

namespace Leech18SemanticBridge

namespace SeedEdge

def meets (a b : SeedEdge) : Bool :=
  a.u == b.u || a.u == b.v || a.v == b.u || a.v == b.v

def sameUndirected (a b : SeedEdge) : Bool :=
  (a.u == b.u && a.v == b.v) || (a.u == b.v && a.v == b.u)

def containsVertex (a : SeedEdge) (x : Nat) : Bool :=
  a.u == x || a.v == x

end SeedEdge

/-- In a three-edge simple graph, the only possible cycle is a triangle.
Pairwise-meeting edges are acyclic exactly when all three share one center. -/
def seedTripleIsSimpleForest (a b c : SeedEdge) : Bool :=
  a.u != a.v && b.u != b.v && c.u != c.v &&
  !(a.sameUndirected b) && !(a.sameUndirected c) && !(b.sameUndirected c) &&
  (!(a.meets b && a.meets c && b.meets c) ||
    ((b.containsVertex a.u && c.containsVertex a.u) ||
     (b.containsVertex a.v && c.containsVertex a.v)))

def seedTripleIsPath (a b c : SeedEdge) : Bool :=
  (a.meets b && b.meets c && !(a.meets c)) ||
  (a.meets c && c.meets b && !(a.meets b)) ||
  (b.meets a && a.meets c && !(b.meets c))

def optionalDistance (condition : Bool) (distance : Nat) : Finset Nat :=
  if condition then {distance} else ∅

/-- All nonzero pair distances inside a simple forest with these three edges.
There are the three edge weights, one sum for each meeting pair, and the
three-edge sum exactly for a chain (never for a three-star). -/
def seedSupport3 (a b c : SeedEdge) : Finset Nat :=
  {a.weight, b.weight, c.weight} ∪
  optionalDistance (a.meets b) (a.weight + b.weight) ∪
  optionalDistance (a.meets c) (a.weight + c.weight) ∪
  optionalDistance (b.meets c) (b.weight + c.weight) ∪
  optionalDistance (seedTripleIsPath a b c) (a.weight + b.weight + c.weight)

def firstPairMatches (relation : FirstPairRelation) (meets : Bool) : Prop :=
  (match relation with
   | .adjacent => meets
   | .disjoint => !meets) = true

instance firstPairMatchesDecidable (relation : FirstPairRelation) (meets : Bool) :
    Decidable (firstPairMatches relation meets) := by
  unfold firstPairMatches
  infer_instance

def witnessContactMatches (contact : WitnessContact)
    (meetsOne meetsTwo : Bool) : Prop :=
  (match contact with
   | .none => !meetsOne && !meetsTwo
   | .meetsWeightOne => meetsOne && !meetsTwo
   | .meetsWeightTwo => !meetsOne && meetsTwo
   | .meetsBoth => meetsOne && meetsTwo) = true

instance witnessContactMatchesDecidable (contact : WitnessContact)
    (meetsOne meetsTwo : Bool) :
    Decidable (witnessContactMatches contact meetsOne meetsTwo) := by
  unfold witnessContactMatches
  infer_instance

/-- A finite, decidable characterization of the least missing positive value. -/
def PositiveMexCondition (support : Finset Nat) (next : Nat) : Prop :=
  0 < next ∧ next ∉ support ∧ Finset.Ico 1 next \ support = ∅

instance positiveMexConditionDecidable (support : Finset Nat) (next : Nat) :
    Decidable (PositiveMexCondition support next) := by
  unfold PositiveMexCondition
  infer_instance

/-- Executable checker for every semantic field used by a formal row.
Matching on a three-element list prevents an unused fourth edge or an implicit
truncation. -/
def descriptorWellFormedCheck (d : RowDescriptor) : Bool :=
  match d.seedEdges with
  | [one, two, witness] =>
      seedTripleIsSimpleForest one two witness &&
      decide (one.weight = 1) &&
      decide (two.weight = 2) &&
      decide (witness.weight = d.witnessWeight) &&
      decide (firstPairMatches d.firstPair (one.meets two)) &&
      decide (witnessContactMatches d.witnessContact
        (witness.meets one) (witness.meets two)) &&
      decide (d.currentSupport.Nodup) &&
      decide (d.currentSupport.toFinset = seedSupport3 one two witness) &&
      decide (PositiveMexCondition
        (seedSupport3 one two witness) d.nextWeight)
  | _ => false

/-- Proposition-level interface to the executable descriptor checker.  Its
outer Boolean equality has a decidability instance without unfolding `d`. -/
def DescriptorWellFormed (d : RowDescriptor) : Prop :=
  descriptorWellFormedCheck d = true

instance descriptorWellFormedDecidable (d : RowDescriptor) :
    Decidable (DescriptorWellFormed d) := by
  unfold DescriptorWellFormed
  infer_instance

theorem row0Descriptor_wellFormed : DescriptorWellFormed row0Descriptor := by decide
theorem row1Descriptor_wellFormed : DescriptorWellFormed row1Descriptor := by decide
theorem row2Descriptor_wellFormed : DescriptorWellFormed row2Descriptor := by decide
theorem row3Descriptor_wellFormed : DescriptorWellFormed row3Descriptor := by decide
theorem row4Descriptor_wellFormed : DescriptorWellFormed row4Descriptor := by decide
theorem row5Descriptor_wellFormed : DescriptorWellFormed row5Descriptor := by decide
theorem row6Descriptor_wellFormed : DescriptorWellFormed row6Descriptor := by decide
theorem row7Descriptor_wellFormed : DescriptorWellFormed row7Descriptor := by decide

theorem rowDescriptors_all_wellFormed :
    ∀ d ∈ rowDescriptors, DescriptorWellFormed d := by
  intro d hd
  simp [rowDescriptors] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row0Descriptor_wellFormed
  · exact row1Descriptor_wellFormed
  · exact row2Descriptor_wellFormed
  · exact row3Descriptor_wellFormed
  · exact row4Descriptor_wellFormed
  · exact row5Descriptor_wellFormed
  · exact row6Descriptor_wellFormed
  · exact row7Descriptor_wellFormed

end Leech18SemanticBridge
