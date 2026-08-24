import SemanticBridge.Aggregate

/-!
# Emitter and axiom audit for the eight-row semantic bridge

The proof/data implementation is split under `SemanticBridge/` so the replay
can elaborate one bounded module per Lean process.  This umbrella emits the
compiled descriptors consumed by the external source checker and audits only
the strongest public bridge declarations.
-/

namespace Leech18SemanticBridge

def firstPairCode : FirstPairRelation → String
  | .adjacent => "adjacent"
  | .disjoint => "disjoint"

def witnessContactCode : WitnessContact → String
  | .none => "none"
  | .meetsWeightOne => "weight_one"
  | .meetsWeightTwo => "weight_two"
  | .meetsBoth => "both"

def natListCode (xs : List Nat) : String :=
  String.intercalate "," (xs.map toString)

def seedEdgeCode (e : SeedEdge) : String :=
  s!"{e.u}-{e.v}-{e.weight}"

def seedEdgesCode (es : List SeedEdge) : String :=
  String.intercalate "," (es.map seedEdgeCode)

def descriptorLine (d : RowDescriptor) : String :=
  String.intercalate "\t" [
    "SEMANTIC_ROW", toString d.paperConfiguration, toString d.solverRow,
    d.leanRow, d.solverMode, d.sourceKind, firstPairCode d.firstPair,
    toString d.witnessWeight, witnessContactCode d.witnessContact,
    natListCode d.currentSupport, toString d.nextWeight,
    seedEdgesCode d.seedEdges]

#eval do
  for d in rowDescriptors do
    IO.println (descriptorLine d)

#print axioms rowDescriptors_all_wellFormed
#print axioms eightRowDossier_implies_some_realized_core
#print axioms isLeech_implies_some_realized_seed_descriptor
#print axioms adjacentMeetsTwoRow_implies_a2_production_split

end Leech18SemanticBridge
