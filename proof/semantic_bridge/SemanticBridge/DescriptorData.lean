import Mathlib.Data.List.Basic

/-!
# Static data for the eight-row semantic bridge

This module contains data only.  Proof modules import it in small, sequential
boundaries so that no bridge compilation needs to elaborate the entire file at
once.
-/

namespace Leech18SemanticBridge

inductive FirstPairRelation where
  | adjacent
  | disjoint
  deriving DecidableEq, Repr

inductive WitnessContact where
  | none
  | meetsWeightOne
  | meetsWeightTwo
  | meetsBoth
  deriving DecidableEq, Repr

structure SeedEdge where
  u : Nat
  v : Nat
  weight : Nat
  deriving DecidableEq, Repr

/-- Static data shared by a formal row and its production solver seed. -/
structure RowDescriptor where
  paperConfiguration : Nat
  solverRow : Nat
  leanRow : String
  solverMode : String
  sourceKind : String
  firstPair : FirstPairRelation
  witnessWeight : Nat
  witnessContact : WitnessContact
  currentSupport : List Nat
  nextWeight : Nat
  seedEdges : List SeedEdge
  deriving DecidableEq, Repr

def row0Descriptor : RowDescriptor where
  paperConfiguration := 1
  solverRow := 0
  leanRow := "AdjacentNoneRow"
  solverMode := "g001_row0"
  sourceKind := "direct_final5"
  firstPair := .adjacent
  witnessWeight := 4
  witnessContact := .none
  currentSupport := [1, 2, 3, 4]
  nextWeight := 5
  seedEdges := [
    { u := 0, v := 1, weight := 1 },
    { u := 1, v := 2, weight := 2 },
    { u := 3, v := 4, weight := 4 }]

def row1Descriptor : RowDescriptor where
  paperConfiguration := 2
  solverRow := 1
  leanRow := "AdjacentMeetsOneRow"
  solverMode := "g001_row1"
  sourceKind := "direct_prior"
  firstPair := .adjacent
  witnessWeight := 4
  witnessContact := .meetsWeightOne
  currentSupport := [1, 2, 3, 4, 5, 7]
  nextWeight := 6
  seedEdges := [
    { u := 1, v := 2, weight := 1 },
    { u := 2, v := 3, weight := 2 },
    { u := 0, v := 1, weight := 4 }]

def row2Descriptor : RowDescriptor where
  paperConfiguration := 3
  solverRow := 2
  leanRow := "AdjacentMeetsTwoRow"
  solverMode := "a2"
  sourceKind := "projected_a2_prior"
  firstPair := .adjacent
  witnessWeight := 4
  witnessContact := .meetsWeightTwo
  currentSupport := [1, 2, 3, 4, 6, 7]
  nextWeight := 5
  seedEdges := [
    { u := 0, v := 1, weight := 1 },
    { u := 1, v := 2, weight := 2 },
    { u := 2, v := 3, weight := 4 }]

def row3Descriptor : RowDescriptor where
  paperConfiguration := 4
  solverRow := 3
  leanRow := "AdjacentMeetsBothRow"
  solverMode := "g001_row3"
  sourceKind := "direct_final5"
  firstPair := .adjacent
  witnessWeight := 4
  witnessContact := .meetsBoth
  currentSupport := [1, 2, 3, 4, 5, 6]
  nextWeight := 7
  seedEdges := [
    { u := 0, v := 1, weight := 1 },
    { u := 0, v := 2, weight := 2 },
    { u := 0, v := 3, weight := 4 }]

def row4Descriptor : RowDescriptor where
  paperConfiguration := 5
  solverRow := 4
  leanRow := "DisjointNoneRow"
  solverMode := "g001_row4"
  sourceKind := "direct_final5"
  firstPair := .disjoint
  witnessWeight := 3
  witnessContact := .none
  currentSupport := [1, 2, 3]
  nextWeight := 4
  seedEdges := [
    { u := 0, v := 1, weight := 1 },
    { u := 2, v := 3, weight := 2 },
    { u := 4, v := 5, weight := 3 }]

def row5Descriptor : RowDescriptor where
  paperConfiguration := 6
  solverRow := 5
  leanRow := "DisjointMeetsOneRow"
  solverMode := "g001_row5"
  sourceKind := "direct_final5"
  firstPair := .disjoint
  witnessWeight := 3
  witnessContact := .meetsWeightOne
  currentSupport := [1, 2, 3, 4]
  nextWeight := 5
  seedEdges := [
    { u := 0, v := 1, weight := 1 },
    { u := 3, v := 4, weight := 2 },
    { u := 1, v := 2, weight := 3 }]

def row6Descriptor : RowDescriptor where
  paperConfiguration := 7
  solverRow := 6
  leanRow := "DisjointMeetsTwoRow"
  solverMode := "g001_row6"
  sourceKind := "direct_final5"
  firstPair := .disjoint
  witnessWeight := 3
  witnessContact := .meetsWeightTwo
  currentSupport := [1, 2, 3, 5]
  nextWeight := 4
  seedEdges := [
    { u := 0, v := 1, weight := 1 },
    { u := 2, v := 3, weight := 2 },
    { u := 3, v := 4, weight := 3 }]

def row7Descriptor : RowDescriptor where
  paperConfiguration := 8
  solverRow := 7
  leanRow := "DisjointMeetsBothRow"
  solverMode := "g001_row7"
  sourceKind := "direct_prior"
  firstPair := .disjoint
  witnessWeight := 3
  witnessContact := .meetsBoth
  currentSupport := [1, 2, 3, 4, 5, 6]
  nextWeight := 7
  seedEdges := [
    { u := 0, v := 1, weight := 1 },
    { u := 2, v := 3, weight := 2 },
    { u := 1, v := 2, weight := 3 }]

def rowDescriptors : List RowDescriptor := [
  row0Descriptor, row1Descriptor, row2Descriptor, row3Descriptor,
  row4Descriptor, row5Descriptor, row6Descriptor, row7Descriptor]

end Leech18SemanticBridge
