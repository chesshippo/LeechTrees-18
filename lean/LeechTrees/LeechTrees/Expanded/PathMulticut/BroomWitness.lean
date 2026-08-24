import LeechTrees.Foundations

/-!
# Actual six-vertex broom witness

Vertices `0,1,2,3,4,5` are `c,x,y,a,b,d`.  The graph has the five actual
edges `cx,xy,ca,cb,cd`.  All cut coefficients and multicut entries below are
defined from `PosIntTree.pathIncidence`; the vectors from the report occur
only as conclusions of graph computations.  Thus G024(c) is an actual
topology counterexample, not a hand-entered matrix.
-/

open scoped BigOperators

namespace LeechTrees.PathMulticut.BroomWitness

open LeechTrees.Foundation
open SimpleGraph

noncomputable section

def edgeFinset : Finset (Sym2 (Fin 6)) :=
  {s(0, 1), s(1, 2), s(0, 3), s(0, 4), s(0, 5)}

def edgeSet : Set (Sym2 (Fin 6)) := ↑edgeFinset

private instance edgeSetMembershipDecidable : DecidablePred (· ∈ edgeSet) :=
  fun e => inferInstanceAs (Decidable (e ∈ edgeFinset))

def graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet edgeSet

private instance graphAdjDecidable : DecidableRel graph.Adj := by
  intro u v
  change Decidable (s(u, v) ∈ edgeFinset ∧ u ≠ v)
  infer_instance

private theorem edgeSet_not_isDiag {e : Sym2 (Fin 6)}
    (he : e ∈ edgeSet) : ¬ e.IsDiag := by
  change e ∈ edgeFinset at he
  simp only [edgeFinset, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with (rfl | rfl | rfl | rfl | rfl) <;> decide

private theorem graph_edgeSet : graph.edgeSet = edgeSet := by
  rw [graph, SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  constructor
  · exact fun he => he.1
  · intro he
    exact ⟨he, edgeSet_not_isDiag he⟩

private theorem edgeSet_ncard : edgeSet.ncard = 5 := by
  simp [edgeSet, edgeFinset]

private theorem graph_connected : graph.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, ?_⟩
  intro v
  fin_cases v
  · exact SimpleGraph.Reachable.rfl
  · exact SimpleGraph.Adj.reachable (by decide)
  · exact (SimpleGraph.Adj.reachable (by decide : graph.Adj 0 1)).trans
      (SimpleGraph.Adj.reachable (by decide : graph.Adj 1 2))
  · exact SimpleGraph.Adj.reachable (by decide)
  · exact SimpleGraph.Adj.reachable (by decide)
  · exact SimpleGraph.Adj.reachable (by decide)

private theorem graph_isTree : graph.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨graph_connected, ?_⟩
  rw [_root_.Nat.card_coe_set_eq, graph_edgeSet, edgeSet_ncard, Nat.card_fin]

/-- A positive integral realization used only to expose the actual graph
API.  The counterexample subsequently puts two external physical-weight
assignments on this same indexed actual edge type. -/
def broom : PosIntTree 6 where
  graph := graph
  isTree := graph_isTree
  weight := fun _ => 1
  weight_pos := by intro e; omega

private instance broomAdjDecidable : DecidableRel broom.graph.Adj := by
  intro u v
  change Decidable (graph.Adj u v)
  exact graphAdjDecidable u v

private instance broomCutGraphAdjDecidable (e : broom.Edge) :
    DecidableRel (broom.cutGraph e).Adj :=
  show DecidableRel (broom.graph.deleteEdges {e.1}).Adj from inferInstance

private instance broomCutGraphReachableDecidable (e : broom.Edge) :
    DecidableRel (broom.cutGraph e).Reachable := inferInstance

private instance broomLeftCutDecidable (e : broom.Edge) (u : Fin 6) :
    Decidable (broom.LeftCut e u) :=
  inferInstanceAs (Decidable ((broom.cutGraph e).Reachable u (broom.edgeLeft e)))

def cx : broom.Edge := ⟨s(0, 1), by change graph.Adj 0 1; decide⟩
def xy : broom.Edge := ⟨s(1, 2), by change graph.Adj 1 2; decide⟩
def ca : broom.Edge := ⟨s(0, 3), by change graph.Adj 0 3; decide⟩
def cb : broom.Edge := ⟨s(0, 4), by change graph.Adj 0 4; decide⟩
def cd : broom.Edge := ⟨s(0, 5), by change graph.Adj 0 5; decide⟩

def edgeAt : Fin 5 → broom.Edge := ![cx, xy, ca, cb, cd]

theorem edgeAt_bijective : Function.Bijective edgeAt := by
  constructor
  · intro i j hij
    apply Fin.ext
    fin_cases i <;> fin_cases j <;>
      simp [edgeAt, cx, xy, ca, cb, cd] at hij ⊢
  · rintro ⟨e, he⟩
    have he' : e ∈ edgeSet := by
      rw [← graph_edgeSet]
      exact he
    change e ∈ edgeFinset at he'
    simp only [edgeFinset, Finset.mem_insert, Finset.mem_singleton] at he'
    rcases he' with (rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, Subtype.ext rfl⟩
    · exact ⟨1, Subtype.ext rfl⟩
    · exact ⟨2, Subtype.ext rfl⟩
    · exact ⟨3, Subtype.ext rfl⟩
    · exact ⟨4, Subtype.ext rfl⟩

noncomputable def edgeEquiv : Fin 5 ≃ broom.Edge :=
  Equiv.ofBijective edgeAt edgeAt_bijective

/-- The report's first actual edge assignment:
`cx,xy,ca,cb,cd = 5,1,2,3,4`. -/
def firstWeight (e : broom.Edge) : ℕ :=
  if e.1 = cx.1 then 5
  else if e.1 = xy.1 then 1
  else if e.1 = ca.1 then 2
  else if e.1 = cb.1 then 3
  else 4

/-- Swap weights one and four between `xy` and the centre leaf `cd`. -/
def secondWeight (e : broom.Edge) : ℕ :=
  if e.1 = cx.1 then 5
  else if e.1 = xy.1 then 4
  else if e.1 = ca.1 then 2
  else if e.1 = cb.1 then 3
  else 1

theorem firstWeight_edgeAt :
    firstWeight ∘ edgeAt = ![5, 1, 2, 3, 4] := by
  funext i
  fin_cases i <;> decide

theorem secondWeight_edgeAt :
    secondWeight ∘ edgeAt = ![5, 4, 2, 3, 1] := by
  funext i
  fin_cases i <;> decide

/-! ## Executable cut-side descriptions of the actual graph -/

def cxLeft (u : Fin 6) : Prop := u = 0 ∨ u = 3 ∨ u = 4 ∨ u = 5
def xyLeft (u : Fin 6) : Prop := u ≠ 2
def caLeft (u : Fin 6) : Prop := u ≠ 3
def cbLeft (u : Fin 6) : Prop := u ≠ 4
def cdLeft (u : Fin 6) : Prop := u ≠ 5

@[simp] theorem leftCut_cx (u : Fin 6) : broom.LeftCut cx u ↔ cxLeft u := by
  unfold PosIntTree.LeftCut
  unfold cxLeft
  letI : DecidableRel (broom.cutGraph cx).Reachable :=
    broomCutGraphReachableDecidable cx
  fin_cases u <;> decide

@[simp] theorem leftCut_xy (u : Fin 6) : broom.LeftCut xy u ↔ xyLeft u := by
  unfold PosIntTree.LeftCut
  unfold xyLeft
  letI : DecidableRel (broom.cutGraph xy).Reachable :=
    broomCutGraphReachableDecidable xy
  fin_cases u <;> decide

@[simp] theorem leftCut_ca (u : Fin 6) : broom.LeftCut ca u ↔ caLeft u := by
  unfold PosIntTree.LeftCut
  unfold caLeft
  letI : DecidableRel (broom.cutGraph ca).Reachable :=
    broomCutGraphReachableDecidable ca
  fin_cases u <;> decide

@[simp] theorem leftCut_cb (u : Fin 6) : broom.LeftCut cb u ↔ cbLeft u := by
  unfold PosIntTree.LeftCut
  unfold cbLeft
  letI : DecidableRel (broom.cutGraph cb).Reachable :=
    broomCutGraphReachableDecidable cb
  fin_cases u <;> decide

@[simp] theorem leftCut_cd (u : Fin 6) : broom.LeftCut cd u ↔ cdLeft u := by
  unfold PosIntTree.LeftCut
  unfold cdLeft
  letI : DecidableRel (broom.cutGraph cd).Reachable :=
    broomCutGraphReachableDecidable cd
  fin_cases u <;> decide

theorem pathIncidence_eq_opposite (p : VertexPair 6) (e : broom.Edge) :
    broom.pathIncidence p e =
      if (broom.LeftCut e p.left ∧ ¬ broom.LeftCut e p.right) ∨
          (¬ broom.LeftCut e p.left ∧ broom.LeftCut e p.right)
      then 1 else 0 := by
  unfold PosIntTree.pathIncidence
  simp only [broom.mem_pathEdges_iff_opposite_cuts,
    broom.rightCut_iff_not_leftCut]

/-! ## Actual cut and multicut matrices -/

def actualCutCoefficient (e : broom.Edge) : ℕ :=
  ∑ p : VertexPair 6, broom.pathIncidence p e

def actualMulticutEntry (e f : broom.Edge) : ℕ :=
  ∑ p : VertexPair 6,
    broom.pathIncidence p e * broom.pathIncidence p f

/-- Actual cut coefficients computed from the six-vertex graph. -/
theorem actualCutCoefficient_edgeAt (i : Fin 5) :
    actualCutCoefficient (edgeAt i) = ![8, 5, 5, 5, 5] i := by
  fin_cases i <;>
    simp only [actualCutCoefficient, pathIncidence_eq_opposite] <;>
    decide

/-- The complete actual `cx` row of the graph's multicut matrix. -/
theorem actualCentralMulticutRow (i : Fin 5) :
    actualMulticutEntry cx (edgeAt i) = ![8, 4, 2, 2, 2] i := by
  fin_cases i <;>
    simp only [actualMulticutEntry, pathIncidence_eq_opposite,
      leftCut_cx] <;>
    decide

theorem actual_named_multicut_entries :
    actualMulticutEntry cx xy = 4 ∧
    actualMulticutEntry cx ca = 2 ∧
    actualMulticutEntry cx cb = 2 ∧
    actualMulticutEntry cx cd = 2 := by
  have h1 := actualCentralMulticutRow 1
  have h2 := actualCentralMulticutRow 2
  have h3 := actualCentralMulticutRow 3
  have h4 := actualCentralMulticutRow 4
  norm_num [edgeAt] at h1 h2 h3 h4 ⊢
  exact ⟨h1, h2, h3, h4⟩

/-- Complete actual `(cut coefficient, assigned weight)` histogram, indexed
through the proved edge equivalence. -/
def actualCutHistogram (weight : broom.Edge → ℕ) : Finset (ℕ × ℕ) :=
  Finset.univ.image fun i : Fin 5 =>
    (actualCutCoefficient (edgeAt i), weight (edgeAt i))

/-- The complete graph-derived cut histograms agree. -/
theorem same_actual_cutCoefficient_weight_histogram :
    actualCutHistogram firstWeight = actualCutHistogram secondWeight := by
  simp_rw [actualCutHistogram, actualCutCoefficient_edgeAt]
  decide

/-- No multiplicity is lost by representing these two histograms as
finsets: each contains all five actual indexed edges. -/
theorem actual_cut_histograms_card_five :
    (actualCutHistogram firstWeight).card = 5 ∧
      (actualCutHistogram secondWeight).card = 5 := by
  simp_rw [actualCutHistogram, actualCutCoefficient_edgeAt]
  decide

/-- The actual central multicut moment for an edge assignment. -/
def actualCentralMoment (weight : broom.Edge → ℕ) : ℕ :=
  ∑ i : Fin 5,
    actualMulticutEntry cx (edgeAt i) * weight (edgeAt i)

/-- This indexed expression is genuinely the sum over every actual physical
edge, because `edgeAt` was proved bijective. -/
theorem actualCentralMoment_eq_edge_sum (weight : broom.Edge → ℕ) :
    actualCentralMoment weight =
      ∑ e : broom.Edge, actualMulticutEntry cx e * weight e := by
  unfold actualCentralMoment
  apply Fintype.sum_equiv edgeEquiv
  intro i
  rfl

/-- The two graph-derived multicut moments are exactly 62 and 68. -/
theorem actualCentralMoments_exact :
    actualCentralMoment firstWeight = 62 ∧
      actualCentralMoment secondWeight = 68 := by
  constructor <;>
    simp only [actualCentralMoment, actualCentralMulticutRow] <;>
    decide

/-- G024(c): an explicit actual graph proves that the complete cut histogram
does not determine its multicut matrix/moment. -/
theorem actual_histogram_does_not_determine_multicut :
    actualCutHistogram firstWeight = actualCutHistogram secondWeight ∧
    actualMulticutEntry cx xy ≠ actualMulticutEntry cx ca ∧
    actualCentralMoment firstWeight ≠ actualCentralMoment secondWeight := by
  refine ⟨same_actual_cutCoefficient_weight_histogram, ?_, ?_⟩
  · rw [actual_named_multicut_entries.1, actual_named_multicut_entries.2.1]
    decide
  · rw [actualCentralMoments_exact.1, actualCentralMoments_exact.2]
    decide

/-- The sound rearrangement threshold visibly distinguishes the placements:
the first fails 68, and the second attains equality. -/
theorem actual_first_fails_second_attains_lower_bound :
    actualCentralMoment firstWeight < 68 ∧
      actualCentralMoment secondWeight = 68 := by
  rw [actualCentralMoments_exact.1, actualCentralMoments_exact.2]
  decide

end

end LeechTrees.PathMulticut.BroomWitness
