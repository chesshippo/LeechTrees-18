import LeechTrees.OddQuotient.QuotientRoutes
import LeechTrees.FirstEdge
import LeechTrees.Expanded.MultiportTail.ThreeOddMasterCover
import LeechTrees.Expanded.BlockLifts.FourOddGaussianAdapter

/-!
# Actual-tree semantics of the 720-model / ten-master cover

This module supplies the semantic layer deliberately absent from the finite
index file.  Its witnesses name the four actual even components, the three
actual odd physical edges and all six actual endpoint ports.  Thus a model is
related to a `PosIntTree 18`, rather than merely to another finite label.

No solver status occurs anywhere in this file.
-/

namespace LeechTrees.OddQuotient.ThreeOddActualCover

open LeechTrees.Foundation
open LeechTrees.OddQuotient
open ThreeOddMasterCover
open LeechTrees.AdditionalBlockLifts

/-- Exactly three actual odd physical edges. -/
def ExactlyThreeOdd (T : PosIntTree 18) : Prop :=
  Fintype.card (OddBridge T) = 3

/-- Three odd bridges force exactly four actual even components. -/
theorem evenComponent_card_eq_four (T : PosIntTree 18)
    (h3 : ExactlyThreeOdd T) : Fintype.card (EvenComponent T) = 4 := by
  classical
  letI : Fintype (quotientGraph T).edgeSet := Fintype.ofFinite _
  have hedge : Fintype.card (quotientGraph T).edgeSet = 3 := by
    rw [← Fintype.card_congr (oddBridgeQuotientEdgeEquiv T)]
    exact h3
  have htree := quotientGraph_isTree T
  have hcard := htree.card_edgeFinset
  rw [SimpleGraph.edgeFinset_card, hedge] at hcard
  omega

/-- Endpoint component roles of the three quotient edges.  The two P4
patterns use `0-1-2-3`; the two star patterns use `0-1,0-2,0-3`. -/
def edgeSource : OpenPattern → Fin 3 → Fin 4
  | .p4SD, i => ⟨i.1, by omega⟩
  | .p4DD, i => ⟨i.1, by omega⟩
  | .starEED, _ => 0
  | .starDDD, _ => 0

def edgeTarget : OpenPattern → Fin 3 → Fin 4
  | .p4SD, i => ⟨i.1 + 1, by omega⟩
  | .p4DD, i => ⟨i.1 + 1, by omega⟩
  | .starEED, i => ⟨i.1 + 1, by omega⟩
  | .starDDD, i => ⟨i.1 + 1, by omega⟩

/-- The two actual quotient topologies before port-pattern normalization. -/
inductive QuotientKind where
  | p4
  | star
  deriving DecidableEq, Repr

def rawEdgeSource : QuotientKind → Fin 3 → Fin 4
  | .p4, i => ⟨i.1, by omega⟩
  | .star, _ => 0

def rawEdgeTarget : QuotientKind → Fin 3 → Fin 4
  | .p4, i => ⟨i.1 + 1, by omega⟩
  | .star, i => ⟨i.1 + 1, by omega⟩

/-- Actual P4/star quotient data, with no port-equality classification built
in.  The two bijections enumerate all actual components and all actual odd
physical edges. -/
structure QuotientWitness (T : PosIntTree 18) (q : QuotientKind) where
  component : Fin 4 → EvenComponent T
  component_bijective : Function.Bijective component
  bridge : Fin 3 → OddBridge T
  bridge_bijective : Function.Bijective bridge
  sourcePort : Fin 3 → Fin 18
  targetPort : Fin 3 → Fin 18
  edge_eq_ports : ∀ i, (bridge i).1.1 = s(sourcePort i, targetPort i)
  source_component : ∀ i,
    componentOf T (sourcePort i) = component (rawEdgeSource q i)
  target_component : ∀ i,
    componentOf T (targetPort i) = component (rawEdgeTarget q i)

/-- The port used by a bridge at its source/target role. -/
def sourcePortInComponent {T : PosIntTree 18} {p : OpenPattern}
    (component : Fin 4 → EvenComponent T)
    (sourcePort : Fin 3 → Fin 18)
    (source_component : ∀ i,
      componentOf T (sourcePort i) = component (edgeSource p i))
    (i : Fin 3) : ComponentVertex T (component (edgeSource p i)) :=
  ⟨sourcePort i, source_component i⟩

def targetPortInComponent {T : PosIntTree 18} {p : OpenPattern}
    (component : Fin 4 → EvenComponent T)
    (targetPort : Fin 3 → Fin 18)
    (target_component : ∀ i,
      componentOf T (targetPort i) = component (edgeTarget p i))
    (i : Fin 3) : ComponentVertex T (component (edgeTarget p i)) :=
  ⟨targetPort i, target_component i⟩

/-- Exact port equality pattern, stated on actual physical endpoint names. -/
def PortPatternHolds (p : OpenPattern)
    (sourcePort targetPort : Fin 3 → Fin 18) : Prop :=
  match p with
  | .p4SD => targetPort 0 = sourcePort 1 ∧
      targetPort 1 ≠ sourcePort 2
  | .p4DD => targetPort 0 ≠ sourcePort 1 ∧
      targetPort 1 ≠ sourcePort 2
  | .starEED => sourcePort 0 = sourcePort 1 ∧
      sourcePort 0 ≠ sourcePort 2
  | .starDDD => sourcePort 0 ≠ sourcePort 1 ∧
      sourcePort 0 ≠ sourcePort 2 ∧ sourcePort 1 ≠ sourcePort 2

/-- A concrete open P4/star quotient witness.  Both component and bridge
maps are bijections, so the fields enumerate all—not merely some—components
and odd physical edges. -/
structure PatternWitness (T : PosIntTree 18) (p : OpenPattern) where
  component : Fin 4 → EvenComponent T
  component_bijective : Function.Bijective component
  bridge : Fin 3 → OddBridge T
  bridge_bijective : Function.Bijective bridge
  sourcePort : Fin 3 → Fin 18
  targetPort : Fin 3 → Fin 18
  edge_eq_ports : ∀ i, (bridge i).1.1 = s(sourcePort i, targetPort i)
  source_component : ∀ i,
    componentOf T (sourcePort i) = component (edgeSource p i)
  target_component : ∀ i,
    componentOf T (targetPort i) = component (edgeTarget p i)
  ports : PortPatternHolds p sourcePort targetPort

namespace QuotientWitness

variable {T : PosIntTree 18}

theorem exactlyThreeOdd {q : QuotientKind} (W : QuotientWitness T q) :
    ExactlyThreeOdd T := by
  rw [ExactlyThreeOdd, ← Fintype.card_fin 3]
  exact Fintype.card_congr (Equiv.ofBijective W.bridge W.bridge_bijective).symm

/-- The witness supplies the whole actual quotient graph, not merely three
selected quotient edges. -/
theorem quotient_adj_iff {q : QuotientKind} (W : QuotientWitness T q)
    (i j : Fin 4) :
    (quotientGraph T).Adj (W.component i) (W.component j) ↔
      ∃ k : Fin 3,
        s(i, j) = s(rawEdgeSource q k, rawEdgeTarget q k) := by
  rw [quotientGraph_adj_iff]
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨k, rfl⟩ := W.bridge_bijective.2 e
    refine ⟨k, ?_⟩
    have hports : quotientEdgePair T (W.bridge k) =
        s(componentOf T (W.sourcePort k), componentOf T (W.targetPort k)) := by
      rw [quotientEdgePair, W.edge_eq_ports, Sym2.map_pair_eq]
    rw [hports, W.source_component, W.target_component] at he
    have hunmap : s(rawEdgeSource q k, rawEdgeTarget q k) = s(i, j) := by
      exact (Sym2.map.injective W.component_bijective.1) (by
        simpa only [Sym2.map_pair_eq] using he)
    exact hunmap.symm
  · rintro ⟨k, hk⟩
    refine ⟨W.bridge k, ?_⟩
    have hports : quotientEdgePair T (W.bridge k) =
        s(componentOf T (W.sourcePort k), componentOf T (W.targetPort k)) := by
      rw [quotientEdgePair, W.edge_eq_ports, Sym2.map_pair_eq]
    rw [hports, W.source_component, W.target_component]
    have hmap := congrArg (Sym2.map W.component) hk
    simpa [Sym2.map_pair_eq] using hmap.symm

def asP4SD (W : QuotientWitness T .p4)
    (hports : PortPatternHolds .p4SD W.sourcePort W.targetPort) :
    PatternWitness T .p4SD where
  component := W.component
  component_bijective := W.component_bijective
  bridge := W.bridge
  bridge_bijective := W.bridge_bijective
  sourcePort := W.sourcePort
  targetPort := W.targetPort
  edge_eq_ports := W.edge_eq_ports
  source_component := by simpa [edgeSource, rawEdgeSource] using W.source_component
  target_component := by simpa [edgeTarget, rawEdgeTarget] using W.target_component
  ports := hports

def asP4DD (W : QuotientWitness T .p4)
    (hports : PortPatternHolds .p4DD W.sourcePort W.targetPort) :
    PatternWitness T .p4DD where
  component := W.component
  component_bijective := W.component_bijective
  bridge := W.bridge
  bridge_bijective := W.bridge_bijective
  sourcePort := W.sourcePort
  targetPort := W.targetPort
  edge_eq_ports := W.edge_eq_ports
  source_component := by simpa [edgeSource, rawEdgeSource] using W.source_component
  target_component := by simpa [edgeTarget, rawEdgeTarget] using W.target_component
  ports := hports

def asStarEED (W : QuotientWitness T .star)
    (hports : PortPatternHolds .starEED W.sourcePort W.targetPort) :
    PatternWitness T .starEED where
  component := W.component
  component_bijective := W.component_bijective
  bridge := W.bridge
  bridge_bijective := W.bridge_bijective
  sourcePort := W.sourcePort
  targetPort := W.targetPort
  edge_eq_ports := W.edge_eq_ports
  source_component := by simpa [edgeSource, rawEdgeSource] using W.source_component
  target_component := by simpa [edgeTarget, rawEdgeTarget] using W.target_component
  ports := hports

def asStarDDD (W : QuotientWitness T .star)
    (hports : PortPatternHolds .starDDD W.sourcePort W.targetPort) :
    PatternWitness T .starDDD where
  component := W.component
  component_bijective := W.component_bijective
  bridge := W.bridge
  bridge_bijective := W.bridge_bijective
  sourcePort := W.sourcePort
  targetPort := W.targetPort
  edge_eq_ports := W.edge_eq_ports
  source_component := by simpa [edgeSource, rawEdgeSource] using W.source_component
  target_component := by simpa [edgeTarget, rawEdgeTarget] using W.target_component
  ports := hports

def rev3 (i : Fin 3) : Fin 3 := ⟨2 - i.1, by omega⟩
def rev4 (i : Fin 4) : Fin 4 := ⟨3 - i.1, by omega⟩

theorem rev3_involutive : Function.Involutive rev3 := by
  intro i
  apply Fin.ext
  simp [rev3]
  omega

theorem rev4_involutive : Function.Involutive rev4 := by
  intro i
  apply Fin.ext
  simp [rev4]
  omega

/-- Reverse the actual P4, swapping both bridge orientation and component
order. -/
def reverseP4 (W : QuotientWitness T .p4) : QuotientWitness T .p4 where
  component := fun i => W.component (rev4 i)
  component_bijective :=
    W.component_bijective.comp rev4_involutive.bijective
  bridge := fun i => W.bridge (rev3 i)
  bridge_bijective := W.bridge_bijective.comp rev3_involutive.bijective
  sourcePort := fun i => W.targetPort (rev3 i)
  targetPort := fun i => W.sourcePort (rev3 i)
  edge_eq_ports := by
    intro i
    rw [W.edge_eq_ports]
    exact Sym2.eq_swap
  source_component := by
    intro i
    rw [W.target_component]
    apply congrArg W.component
    apply Fin.ext
    simp [rawEdgeTarget, rawEdgeSource, rev3, rev4]
    omega
  target_component := by
    intro i
    rw [W.source_component]
    apply congrArg W.component
    apply Fin.ext
    simp [rawEdgeTarget, rawEdgeSource, rev3, rev4]

def starSwap02 : Equiv.Perm (Fin 3) where
  toFun := ![0, 2, 1]
  invFun := ![0, 2, 1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def starSwap02Four : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 3, 2]
  invFun := ![0, 1, 3, 2]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def starCycle12 : Equiv.Perm (Fin 3) where
  toFun := ![1, 2, 0]
  invFun := ![2, 0, 1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def starCycle12Four : Equiv.Perm (Fin 4) where
  toFun := ![0, 2, 3, 1]
  invFun := ![0, 3, 1, 2]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- Reindex star leaves and their odd bridges by compatible permutations. -/
def reindexStar (W : QuotientWitness T .star)
    (π : Equiv.Perm (Fin 3)) (sigma : Equiv.Perm (Fin 4))
    (hcenter : sigma 0 = 0)
    (hleaf : ∀ i, sigma (rawEdgeTarget .star i) =
      rawEdgeTarget .star (π i)) : QuotientWitness T .star where
  component := fun i => W.component (sigma i)
  component_bijective := W.component_bijective.comp sigma.bijective
  bridge := fun i => W.bridge (π i)
  bridge_bijective := W.bridge_bijective.comp π.bijective
  sourcePort := fun i => W.sourcePort (π i)
  targetPort := fun i => W.targetPort (π i)
  edge_eq_ports := fun i => W.edge_eq_ports (π i)
  source_component := by
    intro i
    rw [W.source_component]
    apply congrArg W.component
    simpa [rawEdgeSource] using hcenter.symm
  target_component := by
    intro i
    rw [W.target_component]
    apply congrArg W.component
    exact (hleaf i).symm

end QuotientWitness

/-- Intrinsic scope predicate for the open branch after the separately closed
common-port cases.  It begins with actual quotient/component/bridge data; it
does not assume one of the four normalized labels. -/
def OpenMultiport (T : PosIntTree 18) : Prop :=
  (∃ W : QuotientWitness T .p4,
    ¬(W.targetPort 0 = W.sourcePort 1 ∧
      W.targetPort 1 = W.sourcePort 2)) ∨
  (∃ W : QuotientWitness T .star,
    ¬(W.sourcePort 0 = W.sourcePort 1 ∧
      W.sourcePort 0 = W.sourcePort 2))

theorem exactlyThreeOdd_of_openMultiport {T : PosIntTree 18}
    (hopen : OpenMultiport T) : ExactlyThreeOdd T := by
  rcases hopen with ⟨W, _⟩ | ⟨W, _⟩
  · exact W.exactlyThreeOdd
  · exact W.exactlyThreeOdd

/-- Every actual open quotient normalizes, using only P4 reversal or star-leaf
permutation, to exactly one of the four promoted port patterns. -/
theorem patternWitness_of_openMultiport {T : PosIntTree 18}
    (hopen : OpenMultiport T) :
    Nonempty (Σ p : OpenPattern, PatternWitness T p) := by
  rcases hopen with ⟨W, hopen⟩ | ⟨W, hopen⟩
  · by_cases h0 : W.targetPort 0 = W.sourcePort 1
    · by_cases h1 : W.targetPort 1 = W.sourcePort 2
      · exact (hopen ⟨h0, h1⟩).elim
      · exact ⟨⟨.p4SD, W.asP4SD ⟨h0, h1⟩⟩⟩
    · by_cases h1 : W.targetPort 1 = W.sourcePort 2
      · let V := W.reverseP4
        have hv0 : V.targetPort 0 = V.sourcePort 1 := by
          simpa [V, QuotientWitness.reverseP4, QuotientWitness.rev3] using h1.symm
        have hv1 : V.targetPort 1 ≠ V.sourcePort 2 := by
          intro hv
          apply h0
          simpa [V, QuotientWitness.reverseP4, QuotientWitness.rev3] using hv.symm
        exact ⟨⟨.p4SD, V.asP4SD ⟨hv0, hv1⟩⟩⟩
      · exact ⟨⟨.p4DD, W.asP4DD ⟨h0, h1⟩⟩⟩
  · by_cases h01 : W.sourcePort 0 = W.sourcePort 1
    · by_cases h02 : W.sourcePort 0 = W.sourcePort 2
      · exact (hopen ⟨h01, h02⟩).elim
      · exact ⟨⟨.starEED, W.asStarEED ⟨h01, h02⟩⟩⟩
    · by_cases h02 : W.sourcePort 0 = W.sourcePort 2
      · let V := W.reindexStar QuotientWitness.starSwap02
          QuotientWitness.starSwap02Four (by rfl) (by
            intro i
            fin_cases i <;> rfl)
        have hv01 : V.sourcePort 0 = V.sourcePort 1 := by
          simpa [V, QuotientWitness.reindexStar,
            QuotientWitness.starSwap02] using h02
        have hv02 : V.sourcePort 0 ≠ V.sourcePort 2 := by
          simpa [V, QuotientWitness.reindexStar,
            QuotientWitness.starSwap02] using h01
        exact ⟨⟨.starEED, V.asStarEED ⟨hv01, hv02⟩⟩⟩
      · by_cases h12 : W.sourcePort 1 = W.sourcePort 2
        · let V := W.reindexStar QuotientWitness.starCycle12
            QuotientWitness.starCycle12Four (by rfl) (by
              intro i
              fin_cases i <;> rfl)
          have hv01 : V.sourcePort 0 = V.sourcePort 1 := by
            simpa [V, QuotientWitness.reindexStar,
              QuotientWitness.starCycle12] using h12
          have hv02 : V.sourcePort 0 ≠ V.sourcePort 2 := by
            intro hv
            apply h01
            simpa [V, QuotientWitness.reindexStar,
              QuotientWitness.starCycle12] using hv.symm
          exact ⟨⟨.starEED, V.asStarEED ⟨hv01, hv02⟩⟩⟩
        · exact ⟨⟨.starDDD, W.asStarDDD ⟨h01, h02, h12⟩⟩⟩

namespace PatternWitness

variable {T : PosIntTree 18} {p : OpenPattern} (W : PatternWitness T p)

private theorem component_role_eq_of_vertex_eq
    {x y : Fin 18} {i j : Fin 4}
    (hx : componentOf T x = W.component i)
    (hy : componentOf T y = W.component j) (hxy : x = y) : i = j := by
  apply W.component_bijective.1
  rw [← hx, ← hy, hxy]

/-- In P4-DD no two distinct actual odd bridges share a physical endpoint. -/
theorem p4DD_bridge_endpoint_disjoint
    (W : PatternWitness T .p4DD) {i j : Fin 3} (hij : i ≠ j) :
    T.EdgeEndpointDisjoint (W.bridge i).1 (W.bridge j).1 := by
  intro v hvi hvj
  have hi : v = W.sourcePort i ∨ v = W.targetPort i := by
    rw [W.edge_eq_ports] at hvi
    simpa [eq_comm] using hvi
  have hj : v = W.sourcePort j ∨ v = W.targetPort j := by
    rw [W.edge_eq_ports] at hvj
    simpa [eq_comm] using hvj
  rcases hi with his | hit <;> rcases hj with hjs | hjt
  · have hr := W.component_role_eq_of_vertex_eq
      (W.source_component i) (W.source_component j) (his.symm.trans hjs)
    apply hij
    apply Fin.ext
    simpa [edgeSource] using congrArg Fin.val hr
  · have hr := W.component_role_eq_of_vertex_eq
      (W.source_component i) (W.target_component j) (his.symm.trans hjt)
    have hp := W.ports
    fin_cases i <;> fin_cases j <;>
      simp [edgeSource, edgeTarget] at hr hij
    all_goals simp [PortPatternHolds] at hp
    all_goals aesop
  · have hr := W.component_role_eq_of_vertex_eq
      (W.target_component i) (W.source_component j) (hit.symm.trans hjs)
    have hp := W.ports
    fin_cases i <;> fin_cases j <;>
      simp [edgeSource, edgeTarget] at hr hij
    all_goals simp [PortPatternHolds] at hp
    all_goals aesop
  · have hr := W.component_role_eq_of_vertex_eq
      (W.target_component i) (W.target_component j) (hit.symm.trans hjt)
    apply hij
    apply Fin.ext
    simpa [edgeTarget] using congrArg Fin.val hr

/-- In star-DDD no two distinct actual odd bridges share a physical endpoint. -/
theorem starDDD_bridge_endpoint_disjoint
    (W : PatternWitness T .starDDD) {i j : Fin 3} (hij : i ≠ j) :
    T.EdgeEndpointDisjoint (W.bridge i).1 (W.bridge j).1 := by
  intro v hvi hvj
  have hi : v = W.sourcePort i ∨ v = W.targetPort i := by
    rw [W.edge_eq_ports] at hvi
    simpa [eq_comm] using hvi
  have hj : v = W.sourcePort j ∨ v = W.targetPort j := by
    rw [W.edge_eq_ports] at hvj
    simpa [eq_comm] using hvj
  rcases hi with his | hit <;> rcases hj with hjs | hjt
  · have hp := W.ports
    fin_cases i <;> fin_cases j <;> simp at hij
    all_goals simp [PortPatternHolds] at hp
    all_goals aesop
  · have hr := W.component_role_eq_of_vertex_eq
      (W.source_component i) (W.target_component j) (his.symm.trans hjt)
    fin_cases i <;> fin_cases j <;>
      simp [edgeSource, edgeTarget] at hr
  · have hr := W.component_role_eq_of_vertex_eq
      (W.target_component i) (W.source_component j) (hit.symm.trans hjs)
    fin_cases i <;> fin_cases j <;>
      simp [edgeSource, edgeTarget] at hr
  · have hr := W.component_role_eq_of_vertex_eq
      (W.target_component i) (W.target_component j) (hit.symm.trans hjt)
    apply hij
    apply Fin.ext
    simpa [edgeTarget] using congrArg Fin.val hr

def toRawP4 (W : PatternWitness T p)
    (hp : p = .p4SD ∨ p = .p4DD) : QuotientWitness T .p4 where
  component := W.component
  component_bijective := W.component_bijective
  bridge := W.bridge
  bridge_bijective := W.bridge_bijective
  sourcePort := W.sourcePort
  targetPort := W.targetPort
  edge_eq_ports := W.edge_eq_ports
  source_component := by
    rcases hp with rfl | rfl <;>
      simpa [edgeSource, rawEdgeSource] using W.source_component
  target_component := by
    rcases hp with rfl | rfl <;>
      simpa [edgeTarget, rawEdgeTarget] using W.target_component

def toRawStar (W : PatternWitness T p)
    (hp : p = .starEED ∨ p = .starDDD) : QuotientWitness T .star where
  component := W.component
  component_bijective := W.component_bijective
  bridge := W.bridge
  bridge_bijective := W.bridge_bijective
  sourcePort := W.sourcePort
  targetPort := W.targetPort
  edge_eq_ports := W.edge_eq_ports
  source_component := by
    rcases hp with rfl | rfl <;>
      simpa [edgeSource, rawEdgeSource] using W.source_component
  target_component := by
    rcases hp with rfl | rfl <;>
      simpa [edgeTarget, rawEdgeTarget] using W.target_component

theorem openMultiport (W : PatternWitness T p) : OpenMultiport T := by
  cases p with
  | p4SD =>
      left
      refine ⟨W.toRawP4 W (Or.inl rfl), ?_⟩
      intro hclosed
      exact W.ports.2 hclosed.2
  | p4DD =>
      left
      refine ⟨W.toRawP4 W (Or.inr rfl), ?_⟩
      intro hclosed
      exact W.ports.1 hclosed.1
  | starEED =>
      right
      refine ⟨W.toRawStar W (Or.inl rfl), ?_⟩
      intro hclosed
      exact W.ports.2 hclosed.2
  | starDDD =>
      right
      refine ⟨W.toRawStar W (Or.inr rfl), ?_⟩
      intro hclosed
      exact W.ports.1 hclosed.1

noncomputable def componentEquiv : Fin 4 ≃ EvenComponent T :=
  Equiv.ofBijective W.component W.component_bijective

noncomputable def bridgeEquiv : Fin 3 ≃ OddBridge T :=
  Equiv.ofBijective W.bridge W.bridge_bijective

/-- Exact quotient adjacency in terms of the three enumerated actual
bridges. -/
theorem quotient_adj_iff (i j : Fin 4) :
    (quotientGraph T).Adj (W.component i) (W.component j) ↔
      ∃ k : Fin 3,
        s(i, j) = s(edgeSource p k, edgeTarget p k) := by
  rw [quotientGraph_adj_iff]
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨k, rfl⟩ := W.bridge_bijective.2 e
    refine ⟨k, ?_⟩
    have hports : quotientEdgePair T (W.bridge k) =
        s(componentOf T (W.sourcePort k), componentOf T (W.targetPort k)) := by
      rw [quotientEdgePair, W.edge_eq_ports, Sym2.map_pair_eq]
    rw [hports, W.source_component, W.target_component] at he
    have hunmap : s(edgeSource p k, edgeTarget p k) = s(i, j) := by
      exact (Sym2.map.injective W.component_bijective.1) (by
        simpa only [Sym2.map_pair_eq] using he)
    exact hunmap.symm
  · rintro ⟨k, hk⟩
    refine ⟨W.bridge k, ?_⟩
    have hports : quotientEdgePair T (W.bridge k) =
        s(componentOf T (W.sourcePort k), componentOf T (W.targetPort k)) := by
      rw [quotientEdgePair, W.edge_eq_ports, Sym2.map_pair_eq]
    rw [hports, W.source_component, W.target_component]
    have hmap := congrArg (Sym2.map W.component) hk
    simpa [Sym2.map_pair_eq] using hmap.symm

/-! ### The actual four-component quotient metric

The Gaussian phase filter is useful only after its distance matrix has been
derived from the actual quotient tree.  The following small path lemmas make
that derivation explicit: every displayed length is certified by an actual
quotient path and uniqueness of paths in `quotientGraph T`.
-/

private theorem quotientDistance_eq_pathLength
    {C D : EvenComponent T} (q : (quotientGraph T).Path C D) :
    quotientDistance T C D = q.1.length := by
  unfold quotientDistance
  rw [← quotientPath_unique T q]

private theorem quotientDistance_eq_zero
    (C : EvenComponent T) : quotientDistance T C C = 0 := by
  let q : (quotientGraph T).Path C C := ⟨SimpleGraph.Walk.nil, by simp⟩
  calc
    quotientDistance T C C = q.1.length :=
      quotientDistance_eq_pathLength q
    _ = 0 := by rfl

private theorem quotientDistance_eq_one_of_adj
    {C D : EvenComponent T} (hCD : (quotientGraph T).Adj C D) :
    quotientDistance T C D = 1 := by
  let q : (quotientGraph T).Path C D := SimpleGraph.Path.singleton hCD
  calc
    quotientDistance T C D = q.1.length :=
      quotientDistance_eq_pathLength q
    _ = 1 := by simp [q, SimpleGraph.Path.singleton]

private theorem quotientDistance_eq_two_of_chain
    {C D E : EvenComponent T}
    (hCD : (quotientGraph T).Adj C D)
    (hDE : (quotientGraph T).Adj D E) (hCE : C ≠ E) :
    quotientDistance T C E = 2 := by
  let walk : (quotientGraph T).Walk C E :=
    SimpleGraph.Walk.cons hCD
      (SimpleGraph.Walk.cons hDE SimpleGraph.Walk.nil)
  have hpath : walk.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simp [walk, hCD.ne, hDE.ne, hCE]
  let q : (quotientGraph T).Path C E := ⟨walk, hpath⟩
  calc
    quotientDistance T C E = q.1.length :=
      quotientDistance_eq_pathLength q
    _ = 2 := by simp [q, walk]

private theorem quotientDistance_eq_three_of_chain
    {C D E F : EvenComponent T}
    (hCD : (quotientGraph T).Adj C D)
    (hDE : (quotientGraph T).Adj D E)
    (hEF : (quotientGraph T).Adj E F)
    (hCE : C ≠ E) (hCF : C ≠ F) (hDF : D ≠ F) :
    quotientDistance T C F = 3 := by
  let walk : (quotientGraph T).Walk C F :=
    SimpleGraph.Walk.cons hCD
      (SimpleGraph.Walk.cons hDE
        (SimpleGraph.Walk.cons hEF SimpleGraph.Walk.nil))
  have hpath : walk.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simp [walk, hCD.ne, hDE.ne, hEF.ne, hCE, hCF, hDF]
  let q : (quotientGraph T).Path C F := ⟨walk, hpath⟩
  calc
    quotientDistance T C F = q.1.length :=
      quotientDistance_eq_pathLength q
    _ = 3 := by simp [q, walk]

/-- The literal distance matrix of the normalized four-vertex path. -/
def p4Distance4 : Fin 4 → Fin 4 → ℕ :=
  ![![0, 1, 2, 3],
    ![1, 0, 1, 2],
    ![2, 1, 0, 1],
    ![3, 2, 1, 0]]

/-- The literal distance matrix of the normalized three-leaf star. -/
def starDistance4 : Fin 4 → Fin 4 → ℕ :=
  ![![0, 1, 1, 1],
    ![1, 0, 2, 2],
    ![1, 2, 0, 2],
    ![1, 2, 2, 0]]

/-- Exact reindexed quotient distance for either promoted P4 port pattern. -/
theorem quotientDistance_eq_p4
    (hp : p = .p4SD ∨ p = .p4DD) (i j : Fin 4) :
    quotientDistance T (W.component i) (W.component j) = p4Distance4 i j := by
  have hne : ∀ {u v : Fin 4}, u ≠ v → W.component u ≠ W.component v := by
    intro u v huv h
    exact huv (W.component_bijective.1 h)
  have h01 : (quotientGraph T).Adj (W.component 0) (W.component 1) := by
    rcases hp with rfl | rfl <;>
      exact (W.quotient_adj_iff 0 1).2 ⟨0, rfl⟩
  have h12 : (quotientGraph T).Adj (W.component 1) (W.component 2) := by
    rcases hp with rfl | rfl <;>
      exact (W.quotient_adj_iff 1 2).2 ⟨1, rfl⟩
  have h23 : (quotientGraph T).Adj (W.component 2) (W.component 3) := by
    rcases hp with rfl | rfl <;>
      exact (W.quotient_adj_iff 2 3).2 ⟨2, rfl⟩
  fin_cases i <;> fin_cases j
  · simpa [p4Distance4] using
      quotientDistance_eq_zero (T := T) (W.component 0)
  · simpa [p4Distance4] using quotientDistance_eq_one_of_adj (T := T) h01
  · simpa [p4Distance4] using
      quotientDistance_eq_two_of_chain (T := T) h01 h12 (hne (by decide))
  · simpa [p4Distance4] using
      quotientDistance_eq_three_of_chain (T := T) h01 h12 h23
        (hne (by decide)) (hne (by decide)) (hne (by decide))
  · simpa [p4Distance4] using quotientDistance_eq_one_of_adj (T := T) h01.symm
  · simpa [p4Distance4] using
      quotientDistance_eq_zero (T := T) (W.component 1)
  · simpa [p4Distance4] using quotientDistance_eq_one_of_adj (T := T) h12
  · simpa [p4Distance4] using
      quotientDistance_eq_two_of_chain (T := T) h12 h23 (hne (by decide))
  · simpa [p4Distance4] using
      quotientDistance_eq_two_of_chain (T := T) h12.symm h01.symm
        (hne (by decide))
  · simpa [p4Distance4] using quotientDistance_eq_one_of_adj (T := T) h12.symm
  · simpa [p4Distance4] using
      quotientDistance_eq_zero (T := T) (W.component 2)
  · simpa [p4Distance4] using quotientDistance_eq_one_of_adj (T := T) h23
  · simpa [p4Distance4] using
      quotientDistance_eq_three_of_chain (T := T) h23.symm h12.symm h01.symm
        (hne (by decide)) (hne (by decide)) (hne (by decide))
  · simpa [p4Distance4] using
      quotientDistance_eq_two_of_chain (T := T) h23.symm h12.symm
        (hne (by decide))
  · simpa [p4Distance4] using quotientDistance_eq_one_of_adj (T := T) h23.symm
  · simpa [p4Distance4] using
      quotientDistance_eq_zero (T := T) (W.component 3)

/-- Exact reindexed quotient distance for either promoted star port pattern. -/
theorem quotientDistance_eq_star
    (hp : p = .starEED ∨ p = .starDDD) (i j : Fin 4) :
    quotientDistance T (W.component i) (W.component j) = starDistance4 i j := by
  have hne : ∀ {u v : Fin 4}, u ≠ v → W.component u ≠ W.component v := by
    intro u v huv h
    exact huv (W.component_bijective.1 h)
  have h01 : (quotientGraph T).Adj (W.component 0) (W.component 1) := by
    rcases hp with rfl | rfl <;>
      exact (W.quotient_adj_iff 0 1).2 ⟨0, rfl⟩
  have h02 : (quotientGraph T).Adj (W.component 0) (W.component 2) := by
    rcases hp with rfl | rfl <;>
      exact (W.quotient_adj_iff 0 2).2 ⟨1, rfl⟩
  have h03 : (quotientGraph T).Adj (W.component 0) (W.component 3) := by
    rcases hp with rfl | rfl <;>
      exact (W.quotient_adj_iff 0 3).2 ⟨2, rfl⟩
  fin_cases i <;> fin_cases j
  · simpa [starDistance4] using
      quotientDistance_eq_zero (T := T) (W.component 0)
  · simpa [starDistance4] using quotientDistance_eq_one_of_adj (T := T) h01
  · simpa [starDistance4] using quotientDistance_eq_one_of_adj (T := T) h02
  · simpa [starDistance4] using quotientDistance_eq_one_of_adj (T := T) h03
  · simpa [starDistance4] using quotientDistance_eq_one_of_adj (T := T) h01.symm
  · simpa [starDistance4] using
      quotientDistance_eq_zero (T := T) (W.component 1)
  · simpa [starDistance4] using
      quotientDistance_eq_two_of_chain (T := T) h01.symm h02 (hne (by decide))
  · simpa [starDistance4] using
      quotientDistance_eq_two_of_chain (T := T) h01.symm h03 (hne (by decide))
  · simpa [starDistance4] using quotientDistance_eq_one_of_adj (T := T) h02.symm
  · simpa [starDistance4] using
      quotientDistance_eq_two_of_chain (T := T) h02.symm h01 (hne (by decide))
  · simpa [starDistance4] using
      quotientDistance_eq_zero (T := T) (W.component 2)
  · simpa [starDistance4] using
      quotientDistance_eq_two_of_chain (T := T) h02.symm h03 (hne (by decide))
  · simpa [starDistance4] using quotientDistance_eq_one_of_adj (T := T) h03.symm
  · simpa [starDistance4] using
      quotientDistance_eq_two_of_chain (T := T) h03.symm h01 (hne (by decide))
  · simpa [starDistance4] using
      quotientDistance_eq_two_of_chain (T := T) h03.symm h02 (hne (by decide))
  · simpa [starDistance4] using
      quotientDistance_eq_zero (T := T) (W.component 3)

/-- The actual gauged imbalance of the component in normalized role `i`. -/
noncomputable def phaseCoordinate (i : Fin 4) : ℤ :=
  componentCoordinate T (W.component 0) (W.component i)

/-- Reindex the actual Leech Gaussian identity along the witness's component
bijection.  No scalar row or phase condition is assumed. -/
theorem reindexed_gaussian_identity (hL : IsLeech T) :
    gaussianReal
        (fun i j => quotientDistance T (W.component i) (W.component j))
        W.phaseCoordinate = 18 ∧
      gaussianImag
        (fun i j => quotientDistance T (W.component i) (W.component j))
        W.phaseCoordinate = 2 := by
  have hactual := actual_fourOdd_gaussian_identity T hL (W.component 0)
  have hreindex := gaussian_equiv W.componentEquiv (quotientDistance T)
    (componentCoordinate T (W.component 0))
  constructor
  · calc
      gaussianReal
          (fun i j => quotientDistance T (W.component i) (W.component j))
          W.phaseCoordinate =
          gaussianReal (quotientDistance T)
            (componentCoordinate T (W.component 0)) := by
              simpa [phaseCoordinate, componentEquiv] using hreindex.1
      _ = 18 := hactual.1
  · calc
      gaussianImag
          (fun i j => quotientDistance T (W.component i) (W.component j))
          W.phaseCoordinate =
          gaussianImag (quotientDistance T)
            (componentCoordinate T (W.component 0)) := by
              simpa [phaseCoordinate, componentEquiv] using hreindex.2
      _ = 2 := hactual.2

private theorem gaussianReal_p4Distance4 (x : Fin 4 → ℤ) :
    gaussianReal p4Distance4 x =
      (x 0 - x 2) ^ 2 + (x 1 - x 3) ^ 2 := by
  unfold gaussianReal
  simp only [Fin.sum_univ_four]
  simp [p4Distance4, iPowReal]
  ring

private theorem gaussianImag_p4Distance4 (x : Fin 4 → ℤ) :
    gaussianImag p4Distance4 x =
      2 * (x 0 * x 1 + x 1 * x 2 + x 2 * x 3 - x 0 * x 3) := by
  unfold gaussianImag
  simp only [Fin.sum_univ_four]
  simp [p4Distance4, iPowImag]
  ring

private theorem gaussianReal_starDistance4 (x : Fin 4 → ℤ) :
    gaussianReal starDistance4 x =
      x 0 ^ 2 + 2 * (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) -
        (x 1 + x 2 + x 3) ^ 2 := by
  unfold gaussianReal
  simp only [Fin.sum_univ_four]
  simp [starDistance4, iPowReal]
  ring

private theorem gaussianImag_starDistance4 (x : Fin 4 → ℤ) :
    gaussianImag starDistance4 x =
      2 * x 0 * (x 1 + x 2 + x 3) := by
  unfold gaussianImag
  simp only [Fin.sum_univ_four]
  simp [starDistance4, iPowImag]
  ring

/-- The actual P4 imbalance row satisfies exactly the two equations used to
define the twenty promoted signatures. -/
theorem p4_gaussian_equations (hL : IsLeech T)
    (hp : p = .p4SD ∨ p = .p4DD) :
    (W.phaseCoordinate 0 - W.phaseCoordinate 2) ^ 2 +
        (W.phaseCoordinate 1 - W.phaseCoordinate 3) ^ 2 = 18 ∧
      W.phaseCoordinate 0 * W.phaseCoordinate 1 +
        W.phaseCoordinate 1 * W.phaseCoordinate 2 +
        W.phaseCoordinate 2 * W.phaseCoordinate 3 -
      W.phaseCoordinate 0 * W.phaseCoordinate 3 = 1 := by
  have h := W.reindexed_gaussian_identity hL
  have hd :
      (fun i j => quotientDistance T (W.component i) (W.component j)) =
        p4Distance4 := by
    funext i j
    exact W.quotientDistance_eq_p4 hp i j
  rw [hd, gaussianReal_p4Distance4, gaussianImag_p4Distance4] at h
  exact ⟨h.1, by nlinarith [h.2]⟩

/-- The actual star imbalance row has unit centre/leaf product and leaf norm
nine.  This is the scalar source of the `(even,even,odd)` leaf phase rule. -/
theorem star_gaussian_normalization (hL : IsLeech T)
    (hp : p = .starEED ∨ p = .starDDD) :
    W.phaseCoordinate 0 *
        (W.phaseCoordinate 1 + W.phaseCoordinate 2 + W.phaseCoordinate 3) = 1 ∧
      W.phaseCoordinate 1 ^ 2 + W.phaseCoordinate 2 ^ 2 +
      W.phaseCoordinate 3 ^ 2 = 9 := by
  have h := W.reindexed_gaussian_identity hL
  have hd :
      (fun i j => quotientDistance T (W.component i) (W.component j)) =
        starDistance4 := by
    funext i j
    exact W.quotientDistance_eq_star hp i j
  rw [hd, gaussianReal_starDistance4, gaussianImag_starDistance4] at h
  have hprod : W.phaseCoordinate 0 *
      (W.phaseCoordinate 1 + W.phaseCoordinate 2 + W.phaseCoordinate 3) = 1 := by
    nlinarith [h.2]
  have hsign :
      (W.phaseCoordinate 0 = 1 ∧
          W.phaseCoordinate 1 + W.phaseCoordinate 2 + W.phaseCoordinate 3 = 1) ∨
        (W.phaseCoordinate 0 = -1 ∧
          W.phaseCoordinate 1 + W.phaseCoordinate 2 + W.phaseCoordinate 3 = -1) := by
    exact Int.mul_eq_one_iff_eq_one_or_neg_one.mp hprod
  refine ⟨hprod, ?_⟩
  have hreal := h.1
  rcases hsign with ⟨hx, hs⟩ | ⟨hx, hs⟩ <;>
    rw [hx, hs] at hreal <;> norm_num at hreal <;> nlinarith [hreal]

private theorem emod_two_sum_eq_one_of_sq_sum_eq_nine
    (a b c : ℤ) (h : a ^ 2 + b ^ 2 + c ^ 2 = 9) :
    a % 2 + b % 2 + c % 2 = 1 := by
  have haLower : -3 ≤ a := by nlinarith [sq_nonneg b, sq_nonneg c]
  have haUpper : a ≤ 3 := by nlinarith [sq_nonneg b, sq_nonneg c]
  have hbLower : -3 ≤ b := by nlinarith [sq_nonneg a, sq_nonneg c]
  have hbUpper : b ≤ 3 := by nlinarith [sq_nonneg a, sq_nonneg c]
  have hcLower : -3 ≤ c := by nlinarith [sq_nonneg a, sq_nonneg b]
  have hcUpper : c ≤ 3 := by nlinarith [sq_nonneg a, sq_nonneg b]
  interval_cases a <;> interval_cases b <;> interval_cases c
  all_goals norm_num at h
  all_goals norm_num

/-- Actual number of named vertices in one enumerated even component. -/
noncomputable def componentSize (i : Fin 4) : ℕ :=
  Fintype.card (ComponentVertex T (W.component i))

noncomputable def sizeRow : SizeRow :=
  ⟨W.componentSize 0, W.componentSize 1,
    W.componentSize 2, W.componentSize 3⟩

/-- The four actual components partition all 18 named vertices. -/
theorem componentSize_sum :
    W.componentSize 0 + W.componentSize 1 +
      W.componentSize 2 + W.componentSize 3 = 18 := by
  let e : (Σ C : EvenComponent T, ComponentVertex T C) ≃ Fin 18 :=
    Equiv.sigmaFiberEquiv (componentOf T)
  have htotal :
      (∑ C : EvenComponent T, Fintype.card (ComponentVertex T C)) = 18 := by
    rw [← Fintype.card_sigma, Fintype.card_congr e]
    rfl
  have hsum := (Equiv.sum_comp W.componentEquiv
    (fun C : EvenComponent T => Fintype.card (ComponentVertex T C))).trans htotal
  simpa [componentSize, Fin.sum_univ_four] using hsum

/-- Every actual component is nonempty. -/
theorem componentSize_pos (i : Fin 4) : 0 < W.componentSize i := by
  obtain ⟨v, hv⟩ := (W.component i).exists_rep
  exact Fintype.card_pos_iff.mpr ⟨⟨v, hv⟩⟩

private theorem reindexed_sevenColor_budgets
    (hL : IsLeech T) :
    (∑ i : Fin 4,
      if sevenColor T hL (W.component i) then W.componentSize i else 0) = 7 ∧
    (∑ i : Fin 4,
      if sevenColor T hL (W.component i) then 0 else W.componentSize i) = 11 := by
  have h := sevenColor_budgets T hL
  constructor
  · have hsum := (Equiv.sum_comp W.componentEquiv (fun C : EvenComponent T =>
      if sevenColor T hL C then componentOrder T C else 0)).trans h.1
    simpa [componentSize, componentOrder] using hsum
  · have hsum := (Equiv.sum_comp W.componentEquiv (fun C : EvenComponent T =>
      if sevenColor T hL C then 0 else componentOrder T C)).trans h.2
    simpa [componentSize, componentOrder] using hsum

theorem p4_component_size_budgets
    (W : PatternWitness T .p4SD) (hL : IsLeech T) :
    (W.componentSize 0 + W.componentSize 2 = 7 ∧
      W.componentSize 1 + W.componentSize 3 = 11) ∨
    (W.componentSize 0 + W.componentSize 2 = 11 ∧
      W.componentSize 1 + W.componentSize 3 = 7) := by
  have h01 : (quotientGraph T).Adj (W.component 0) (W.component 1) :=
    (W.quotient_adj_iff 0 1).2 ⟨0, rfl⟩
  have h12 : (quotientGraph T).Adj (W.component 1) (W.component 2) :=
    (W.quotient_adj_iff 1 2).2 ⟨1, rfl⟩
  have h23 : (quotientGraph T).Adj (W.component 2) (W.component 3) :=
    (W.quotient_adj_iff 2 3).2 ⟨2, rfl⟩
  have hc01 := sevenColor_adjacent T hL h01
  have hc12 := sevenColor_adjacent T hL h12
  have hc23 := sevenColor_adjacent T hL h23
  have hb := W.reindexed_sevenColor_budgets hL
  simp only [Fin.sum_univ_four] at hb
  cases h0 : sevenColor T hL (W.component 0) <;>
    cases h1 : sevenColor T hL (W.component 1) <;>
    cases h2 : sevenColor T hL (W.component 2) <;>
    cases h3 : sevenColor T hL (W.component 3)
  all_goals simp [h0, h1, h2, h3] at hc01 hc12 hc23
  all_goals simp [h0, h1, h2, h3] at hb ⊢
  all_goals omega

theorem p4DD_component_size_budgets
    (W : PatternWitness T .p4DD) (hL : IsLeech T) :
    (W.componentSize 0 + W.componentSize 2 = 7 ∧
      W.componentSize 1 + W.componentSize 3 = 11) ∨
    (W.componentSize 0 + W.componentSize 2 = 11 ∧
      W.componentSize 1 + W.componentSize 3 = 7) := by
  have h01 : (quotientGraph T).Adj (W.component 0) (W.component 1) :=
    (W.quotient_adj_iff 0 1).2 ⟨0, rfl⟩
  have h12 : (quotientGraph T).Adj (W.component 1) (W.component 2) :=
    (W.quotient_adj_iff 1 2).2 ⟨1, rfl⟩
  have h23 : (quotientGraph T).Adj (W.component 2) (W.component 3) :=
    (W.quotient_adj_iff 2 3).2 ⟨2, rfl⟩
  have hc01 := sevenColor_adjacent T hL h01
  have hc12 := sevenColor_adjacent T hL h12
  have hc23 := sevenColor_adjacent T hL h23
  have hb := W.reindexed_sevenColor_budgets hL
  simp only [Fin.sum_univ_four] at hb
  cases h0 : sevenColor T hL (W.component 0) <;>
    cases h1 : sevenColor T hL (W.component 1) <;>
    cases h2 : sevenColor T hL (W.component 2) <;>
    cases h3 : sevenColor T hL (W.component 3)
  all_goals simp [h0, h1, h2, h3] at hc01 hc12 hc23
  all_goals simp [h0, h1, h2, h3] at hb ⊢
  all_goals omega

theorem star_component_size_budgets
    {p : OpenPattern} (W : PatternWitness T p) (hL : IsLeech T)
    (hp : p = .starEED ∨ p = .starDDD) :
    (W.componentSize 0 = 7 ∧
      W.componentSize 1 + W.componentSize 2 + W.componentSize 3 = 11) ∨
    (W.componentSize 0 = 11 ∧
      W.componentSize 1 + W.componentSize 2 + W.componentSize 3 = 7) := by
  have hadj : ∀ i : Fin 3,
      (quotientGraph T).Adj (W.component 0)
        (W.component ⟨i.1 + 1, by omega⟩) := by
    intro i
    rcases hp with rfl | rfl <;>
      exact (W.quotient_adj_iff 0 ⟨i.1 + 1, by omega⟩).2 ⟨i, rfl⟩
  have hc01 := sevenColor_adjacent T hL (hadj 0)
  have hc02 := sevenColor_adjacent T hL (hadj 1)
  have hc03 := sevenColor_adjacent T hL (hadj 2)
  have hb := W.reindexed_sevenColor_budgets hL
  simp only [Fin.sum_univ_four] at hb
  cases h0 : sevenColor T hL (W.component 0) <;>
    cases h1 : sevenColor T hL (W.component 1) <;>
    cases h2 : sevenColor T hL (W.component 2) <;>
    cases h3 : sevenColor T hL (W.component 3)
  all_goals simp [h0, h1, h2, h3] at hc01 hc02 hc03
  all_goals simp [h0, h1, h2, h3] at hb ⊢
  all_goals omega

/-- Validity of each actual normalized component coordinate.  This is the
magnitude/parity bridge from actual vertices to the promoted scalar filter. -/
theorem phaseCoordinate_valid (i : Fin 4) :
    ScalarDatum.Valid
      ⟨W.phaseCoordinate i, W.componentSize i⟩ := by
  simpa [phaseCoordinate, componentSize, componentOrder] using
    componentDatum_valid T (W.component 0) (W.component i)

/-- The actual P4 imbalance tuple, not an independently supplied signature. -/
noncomputable def actualP4Signature : P4Signature :=
  ⟨W.phaseCoordinate 0, W.phaseCoordinate 1,
    W.phaseCoordinate 2, W.phaseCoordinate 3⟩

/-- Actual P4 Gaussian equations and component validity force membership in
the complete twenty-signature list. -/
theorem actualP4Signature_mem (hL : IsLeech T)
    (hp : p = .p4SD ∨ p = .p4DD) :
    W.actualP4Signature ∈ p4SignedSignatures := by
  have h := W.p4_gaussian_equations hL hp
  apply p4SignedSignatures_complete W.actualP4Signature
  · simpa [actualP4Signature] using h.1
  · simpa [actualP4Signature] using h.2

/-- The P4 phase-table filter is derived from actual component coordinates. -/
theorem p4PhaseCompatible_of_actual (hL : IsLeech T)
    (hp : p = .p4SD ∨ p = .p4DD) :
    p4PhaseCompatible W.sizeRow = true := by
  let x := W.actualP4Signature
  have hxmem : x ∈ p4SignedSignatures := by
    simpa [x] using W.actualP4Signature_mem hL hp
  have h0 := W.phaseCoordinate_valid 0
  have h1 := W.phaseCoordinate_valid 1
  have h2 := W.phaseCoordinate_valid 2
  have h3 := W.phaseCoordinate_valid 3
  rw [p4PhaseCompatible, List.any_eq_true]
  refine ⟨x, hxmem, ?_⟩
  simp only [signatureCompatible, Bool.and_eq_true, parityCompatible,
    decide_eq_true_eq]
  simpa [x, actualP4Signature, sizeRow] using
    (And.intro (And.intro (And.intro h0.2 h1.2) h2.2) h3.2)

/-- The star leaf parity filter is likewise forced by the actual Gaussian
norm-nine equation and the actual component parity identities. -/
theorem exactlyOneOdd_of_actual_star (hL : IsLeech T)
    (hp : p = .starEED ∨ p = .starDDD) :
    exactlyOneOdd (W.componentSize 1) (W.componentSize 2)
      (W.componentSize 3) = true := by
  have hnorm := (W.star_gaussian_normalization hL hp).2
  have hmod := emod_two_sum_eq_one_of_sq_sum_eq_nine
    (W.phaseCoordinate 1) (W.phaseCoordinate 2) (W.phaseCoordinate 3) hnorm
  have h1 := W.phaseCoordinate_valid 1
  have h2 := W.phaseCoordinate_valid 2
  have h3 := W.phaseCoordinate_valid 3
  rw [h1.2.2, h2.2.2, h3.2.2] at hmod
  have hcast :
      ((W.componentSize 1 % 2 : ℕ) : ℤ) +
        ((W.componentSize 2 % 2 : ℕ) : ℤ) +
        ((W.componentSize 3 % 2 : ℕ) : ℤ) = 1 := by
    simpa using hmod
  have hnat : W.componentSize 1 % 2 + W.componentSize 2 % 2 +
      W.componentSize 3 % 2 = 1 := by
    exact_mod_cast hcast
  rw [exactlyOneOdd, decide_eq_true_eq]
  exact hnat

private noncomputable def weightOneEdge (hL : IsLeech T) : T.Edge :=
  Classical.choose (t1_existsUnique_weight_one hL (by omega))

private theorem weightOneEdge_weight (hL : IsLeech T) :
    T.weight (weightOneEdge hL) = 1 :=
  (Classical.choose_spec (t1_existsUnique_weight_one hL (by omega))).1

/-- The unique physical weight-one edge is one of the three actual odd
bridges, hence has a unique bridge-position index. -/
noncomputable def unitBridge (hL : IsLeech T) : Fin 3 := by
  have hodd : Odd (T.weight (weightOneEdge hL)) := by
    simp [weightOneEdge_weight hL]
  exact W.bridgeEquiv.symm ⟨weightOneEdge hL, hodd⟩

theorem unitBridge_weight (hL : IsLeech T) :
    T.weight (W.bridge (W.unitBridge hL)).1 = 1 := by
  have hodd : Odd (T.weight (weightOneEdge hL)) := by
    simp [weightOneEdge_weight hL]
  have heq : W.bridge (W.unitBridge hL) =
      (⟨weightOneEdge hL, hodd⟩ : OddBridge T) := by
    exact W.bridgeEquiv.apply_symm_apply ⟨weightOneEdge hL, hodd⟩
  simpa [heq] using weightOneEdge_weight hL

end PatternWitness

/-- Intrinsic exact finite-table eligibility of an actual pattern witness.
The row is computed from actual component cardinalities; it is not supplied
as an unrelated record. -/
def TableEligible {T : PosIntTree 18} {p : OpenPattern}
    (W : PatternWitness T p) : Prop :=
  match p with
  | .p4SD => W.sizeRow ∈ p4SizeRows .p4SD
  | .p4DD => W.sizeRow ∈ p4SizeRows .p4DD
  | .starEED | .starDDD => W.sizeRow ∈ starSizeRows

/-- Transparent form of the inherited promoted phase conditions, evaluated
on the actual component-size row.  Unlike `TableEligible`, this does not
assume membership in a generated list. -/
def PromotedPhaseEligible {T : PosIntTree 18} {p : OpenPattern}
    (W : PatternWitness T p) : Prop :=
  match p with
  | .p4SD | .p4DD =>
      ((W.sizeRow.a + W.sizeRow.c = 7 ∧
          W.sizeRow.b + W.sizeRow.d = 11) ∨
        (W.sizeRow.a + W.sizeRow.c = 11 ∧
          W.sizeRow.b + W.sizeRow.d = 7)) ∧
        p4PhaseCompatible W.sizeRow = true
  | .starEED | .starDDD =>
      ((W.sizeRow.a = 7 ∧
          W.sizeRow.b + W.sizeRow.c + W.sizeRow.d = 11) ∨
        (W.sizeRow.a = 11 ∧
          W.sizeRow.b + W.sizeRow.c + W.sizeRow.d = 7)) ∧
        exactlyOneOdd W.sizeRow.b W.sizeRow.c W.sizeRow.d = true

/-- All promoted colour/phase conditions are consequences of the actual
`IsLeech` tree.  In particular this theorem does not assume a generated-row
membership, a phase-table hit, or any model index. -/
theorem promotedPhaseEligible_of_actual
    {T : PosIntTree 18} {p : OpenPattern}
    (W : PatternWitness T p) (hL : IsLeech T) :
    PromotedPhaseEligible W := by
  cases p with
  | p4SD =>
      refine ⟨?_, W.p4PhaseCompatible_of_actual hL (Or.inl rfl)⟩
      simpa [PatternWitness.sizeRow] using W.p4_component_size_budgets hL
  | p4DD =>
      refine ⟨?_, W.p4PhaseCompatible_of_actual hL (Or.inr rfl)⟩
      simpa [PatternWitness.sizeRow] using W.p4DD_component_size_budgets hL
  | starEED =>
      refine ⟨?_, ?_⟩
      · simpa [PatternWitness.sizeRow] using
          W.star_component_size_budgets hL (Or.inl rfl)
      · simpa [PatternWitness.sizeRow] using
          W.exactlyOneOdd_of_actual_star hL (Or.inl rfl)
  | starDDD =>
      refine ⟨?_, ?_⟩
      · simpa [PatternWitness.sizeRow] using
          W.star_component_size_budgets hL (Or.inr rfl)
      · simpa [PatternWitness.sizeRow] using
          W.exactlyOneOdd_of_actual_star hL (Or.inr rfl)

private theorem two_le_componentSize_of_two
    {T : PosIntTree 18} {p : OpenPattern} (W : PatternWitness T p)
    (i : Fin 4) {x y : Fin 18}
    (hx : componentOf T x = W.component i)
    (hy : componentOf T y = W.component i) (hxy : x ≠ y) :
    2 ≤ W.componentSize i := by
  let encode : Bool → ComponentVertex T (W.component i) := fun b =>
    if b then ⟨x, hx⟩ else ⟨y, hy⟩
  have hinj : Function.Injective encode := by
    intro a b hab
    cases a <;> cases b <;> simp [encode] at hab ⊢
    · exact (hxy hab.symm).elim
    · exact (hxy hab).elim
  simpa [PatternWitness.componentSize] using
    Fintype.card_le_of_injective encode hinj

theorem tableEligible_of_promotedPhase
    {T : PosIntTree 18} {p : OpenPattern} (W : PatternWitness T p)
    (hphase : PromotedPhaseEligible W) : TableEligible W := by
  have hpos : 0 < W.sizeRow.a ∧ 0 < W.sizeRow.b ∧
      0 < W.sizeRow.c ∧ 0 < W.sizeRow.d := by
    simpa [PatternWitness.sizeRow] using
      ⟨W.componentSize_pos 0, W.componentSize_pos 1,
        W.componentSize_pos 2, W.componentSize_pos 3⟩
  cases p with
  | p4SD =>
      rw [TableEligible, mem_p4SizeRows_iff]
      refine ⟨hpos.1, hpos.2.1, hpos.2.2.1, hpos.2.2.2,
        hphase.1, ?_, hphase.2⟩
      simp [p4PortCondition]
      exact two_le_componentSize_of_two W 2
        (by simpa [edgeTarget] using W.target_component 1)
        (by simpa [edgeSource] using W.source_component 2) W.ports.2
  | p4DD =>
      rw [TableEligible, mem_p4SizeRows_iff]
      refine ⟨hpos.1, hpos.2.1, hpos.2.2.1, hpos.2.2.2,
        hphase.1, ?_, hphase.2⟩
      rw [p4PortCondition, decide_eq_true_eq]
      exact ⟨two_le_componentSize_of_two W 1
          (by simpa [edgeTarget] using W.target_component 0)
          (by simpa [edgeSource] using W.source_component 1) W.ports.1,
        two_le_componentSize_of_two W 2
          (by simpa [edgeTarget] using W.target_component 1)
          (by simpa [edgeSource] using W.source_component 2) W.ports.2⟩
  | starEED =>
      rw [TableEligible, mem_starSizeRows_iff]
      exact ⟨hpos.1, hpos.2.1, hpos.2.2.1, hpos.2.2.2,
        hphase.1, hphase.2⟩
  | starDDD =>
      rw [TableEligible, mem_starSizeRows_iff]
      exact ⟨hpos.1, hpos.2.1, hpos.2.2.1, hpos.2.2.2,
        hphase.1, hphase.2⟩

/-- Unconditional actual-tree finite-table eligibility in the open normalized
branch. -/
theorem tableEligible_of_actual
    {T : PosIntTree 18} {p : OpenPattern}
    (W : PatternWitness T p) (hL : IsLeech T) : TableEligible W :=
  tableEligible_of_promotedPhase W (promotedPhaseEligible_of_actual W hL)

/-- An old-model index realizes an actual tree exactly when its decoded
pattern, concrete size row, and unit-bridge position agree with actual
component/edge data. -/
structure RealizesLegacyModel (T : PosIntTree 18) (hL : IsLeech T)
    (M : LegacyModel) where
  witness : PatternWitness T M.pattern
  sizeRow_eq : M.sizeRow = witness.sizeRow
  unitBridge_eq : M.unitBridge = witness.unitBridge hL

/-- Actual-tree-to-model direction for every exact table-eligible open
pattern.  The returned index contains the actual regenerated row and actual
unit physical edge. -/
theorem exists_legacyModel_of_actual
    {T : PosIntTree 18} (hL : IsLeech T) {p : OpenPattern}
    (W : PatternWitness T p) (helig : TableEligible W) :
    Nonempty (Σ M : LegacyModel, RealizesLegacyModel T hL M) := by
  cases p with
  | p4SD =>
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp helig
      let M : LegacyModel := .inl (i, W.unitBridge hL)
      exact ⟨⟨M, { witness := W, sizeRow_eq := hi, unitBridge_eq := rfl }⟩⟩

  | p4DD =>
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp helig
      let M : LegacyModel := .inr (.inl (i, W.unitBridge hL))
      exact ⟨⟨M, { witness := W, sizeRow_eq := hi, unitBridge_eq := rfl }⟩⟩
  | starEED =>
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp helig
      let M : LegacyModel := .inr (.inr (.inl (i, W.unitBridge hL)))
      exact ⟨⟨M, { witness := W, sizeRow_eq := hi, unitBridge_eq := rfl }⟩⟩
  | starDDD =>
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp helig
      let M : LegacyModel := .inr (.inr (.inr (i, W.unitBridge hL)))
      exact ⟨⟨M, { witness := W, sizeRow_eq := hi, unitBridge_eq := rfl }⟩⟩

theorem exists_legacyModel_of_promoted_actual
    {T : PosIntTree 18} (hL : IsLeech T) {p : OpenPattern}
    (W : PatternWitness T p) (hphase : PromotedPhaseEligible W) :
    Nonempty (Σ M : LegacyModel, RealizesLegacyModel T hL M) :=
  exists_legacyModel_of_actual hL W
    (tableEligible_of_promotedPhase W hphase)

/-- Actual open-branch forward representation into the exact 720-model
universe.  Quotient normalization, colour budgets and Gaussian phase
conditions are all derived from the actual `IsLeech` tree. -/
theorem exists_legacyModel_of_openMultiport
    {T : PosIntTree 18} (hL : IsLeech T) (hopen : OpenMultiport T) :
    Nonempty (Σ M : LegacyModel, RealizesLegacyModel T hL M) := by
  obtain ⟨⟨p, W⟩⟩ := patternWitness_of_openMultiport hopen
  exact exists_legacyModel_of_actual hL W (tableEligible_of_actual W hL)

theorem openMultiport_of_realizes
    {T : PosIntTree 18} {hL : IsLeech T} {M : LegacyModel}
    (hM : RealizesLegacyModel T hL M) : OpenMultiport T :=
  hM.witness.openMultiport

/-- Converse: every semantic old-model realization exposes an actual
table-eligible open quotient witness. -/
theorem eligible_of_realizes {T : PosIntTree 18} {hL : IsLeech T}
    {M : LegacyModel} (hM : RealizesLegacyModel T hL M) :
    TableEligible hM.witness := by
  cases M with
  | inl M =>
      change hM.witness.sizeRow ∈ p4SizeRows .p4SD
      rw [← hM.sizeRow_eq]
      exact List.get_mem (p4SizeRows .p4SD) M.1
  | inr M =>
      cases M with
      | inl M =>
          change hM.witness.sizeRow ∈ p4SizeRows .p4DD
          rw [← hM.sizeRow_eq]
          exact List.get_mem (p4SizeRows .p4DD) M.1
      | inr M =>
          cases M with
          | inl M =>
              change hM.witness.sizeRow ∈ starSizeRows
              rw [← hM.sizeRow_eq]
              exact List.get_mem starSizeRows M.1
          | inr M =>
              change hM.witness.sizeRow ∈ starSizeRows
              rw [← hM.sizeRow_eq]
              exact List.get_mem starSizeRows M.1

/-! ## Assignment-set form of the ten-master cover -/

/-- Actual structural low case.  The weight-four conclusions in cases one
and two, and its absence in case three, are retained explicitly. -/
def LowCaseHolds (T : PosIntTree 18) : LowDistanceCase → Prop
  | .path3_edge4 =>
      ∃ e1 e2 : T.Edge,
        T.weight e1 = 1 ∧ T.weight e2 = 2 ∧
        T.EdgeAdjacent e1 e2 ∧
        (¬ ∃ e3 : T.Edge, T.weight e3 = 3) ∧
        ∃! e4 : T.Edge, T.weight e4 = 4
  | .edge3_nonadj_edge4 =>
      ∃ e1 e2 e3 : T.Edge,
        T.weight e1 = 1 ∧ T.weight e2 = 2 ∧ T.weight e3 = 3 ∧
        T.EdgeEndpointDisjoint e1 e2 ∧
        T.EdgeEndpointDisjoint e1 e3 ∧
        ∃! e4 : T.Edge, T.weight e4 = 4
  | .edge3_adj_path4 =>
      ∃ e1 e2 e3 : T.Edge,
        T.weight e1 = 1 ∧ T.weight e2 = 2 ∧ T.weight e3 = 3 ∧
        T.EdgeEndpointDisjoint e1 e2 ∧
        T.EdgeAdjacent e1 e3 ∧
        ¬ ∃ e4 : T.Edge, T.weight e4 = 4

private noncomputable def pathWeightList {T : PosIntTree 18}
    {u v : Fin 18} (p : T.graph.Path u v) : List ℕ :=
  p.1.edges.map T.weightOfPair

private theorem pathWeightList_positive {T : PosIntTree 18}
    {u v : Fin 18} (p : T.graph.Path u v) :
    ∀ w ∈ pathWeightList p, 0 < w := by
  intro w hw
  rw [pathWeightList, List.mem_map] at hw
  obtain ⟨e, he, rfl⟩ := hw
  let actual : T.Edge := ⟨e, p.1.edges_subset_edgeSet he⟩
  change 0 < T.weightOfPair actual.1
  rw [T.weightOfPair_edge]
  exact T.weight_pos actual

private theorem pathWeightList_nodup {T : PosIntTree 18}
    (hL : IsLeech T) {u v : Fin 18} (p : T.graph.Path u v) :
    (pathWeightList p).Nodup := by
  unfold pathWeightList
  apply (List.nodup_map_iff_inj_on p.2.isTrail.edges_nodup).2
  intro e he f hf hw
  let actualE : T.Edge := ⟨e, p.1.edges_subset_edgeSet he⟩
  let actualF : T.Edge := ⟨f, p.1.edges_subset_edgeSet hf⟩
  have hw' : T.weight actualE = T.weight actualF := by
    rw [← T.weightOfPair_edge actualE, ← T.weightOfPair_edge actualF]
    exact hw
  have hef : actualE = actualF := t1_edge_weight_injective hL hw'
  exact congrArg Subtype.val hef

private theorem positive_nodup_sum_four_shape {weights : List ℕ}
    (positive : ∀ w ∈ weights, 0 < w) (nodup : weights.Nodup)
    (total : weights.sum = 4) :
    weights = [4] ∨ weights = [1, 3] ∨ weights = [3, 1] := by
  cases weights with
  | nil => simp at total
  | cons a as =>
      cases as with
      | nil =>
          left
          simp only [List.sum_cons, List.sum_nil, add_zero] at total
          simp [total]
      | cons b bs =>
          cases bs with
          | nil =>
              have ha : 0 < a := positive a (by simp)
              have hb : 0 < b := positive b (by simp)
              have habne : a ≠ b := by
                intro h
                exact (List.nodup_cons.mp nodup).1 (by simp [h])
              simp only [List.sum_cons, List.sum_nil, add_zero] at total
              have hab : (a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1) := by omega
              rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr rfl)
          | cons c cs =>
              have ha : 0 < a := positive a (by simp)
              have hb : 0 < b := positive b (by simp)
              have hc : 0 < c := positive c (by simp)
              have hab : a ≠ b := by
                intro h
                exact (List.nodup_cons.mp nodup).1 (by simp [h])
              have hac : a ≠ c := by
                intro h
                exact (List.nodup_cons.mp nodup).1 (by simp [h])
              have hbc : b ≠ c := by
                intro h
                exact (List.nodup_cons.mp
                  (List.nodup_cons.mp nodup).2).1 (by simp [h])
              simp only [List.sum_cons] at total
              omega

private def edgeOfAdj {T : PosIntTree 18} {u v : Fin 18}
    (h : T.graph.Adj u v) : T.Edge :=
  ⟨s(u, v), by rwa [SimpleGraph.mem_edgeSet]⟩

private theorem edgeOfAdj_weight {T : PosIntTree 18} {u v : Fin 18}
    (h : T.graph.Adj u v) :
    T.weight (edgeOfAdj h) = T.weightOfPair s(u, v) := by
  exact (T.weightOfPair_edge (edgeOfAdj h)).symm

private theorem physicalEdge_of_singleton_weightList {T : PosIntTree 18}
    {u v : Fin 18} (p : T.graph.Path u v) {k : ℕ}
    (hlist : pathWeightList p = [k]) :
    ∃ e : T.Edge, T.weight e = k := by
  have hlen : p.1.length = 1 := by
    have hweights : (pathWeightList p).length = p.1.length := by
      simpa only [pathWeightList, List.length_map] using p.1.length_edges
    have h := congrArg List.length hlist
    simp only [List.length_cons, List.length_nil] at h
    omega
  have hpnon : ¬p.1.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    omega
  let e := edgeOfAdj (p.1.adj_snd hpnon)
  have hcons := p.1.cons_tail_eq hpnon
  have hlist' := hlist
  unfold pathWeightList at hlist'
  rw [← hcons] at hlist'
  simp only [SimpleGraph.Walk.edges_cons, List.map_cons] at hlist'
  refine ⟨e, ?_⟩
  rw [edgeOfAdj_weight]
  simpa using congrArg List.head? hlist'

private theorem adjacentEdges_of_pair_weightList {T : PosIntTree 18}
    {u v : Fin 18} (p : T.graph.Path u v) {a b : ℕ}
    (hlist : pathWeightList p = [a, b]) :
    ∃ eA eB : T.Edge,
      T.weight eA = a ∧ T.weight eB = b ∧ T.EdgeAdjacent eA eB := by
  have hlen : p.1.length = 2 := by
    have hweights : (pathWeightList p).length = p.1.length := by
      simpa only [pathWeightList, List.length_map] using p.1.length_edges
    have h := congrArg List.length hlist
    simp only [List.length_cons, List.length_nil] at h
    omega
  have hpnon : ¬p.1.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    omega
  have htailLen : p.1.tail.length = 1 := by
    have h := p.1.length_tail_add_one hpnon
    omega
  have htailnon : ¬p.1.tail.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    omega
  let eA := edgeOfAdj (p.1.adj_snd hpnon)
  let eB := edgeOfAdj (p.1.tail.adj_snd htailnon)
  have hcons := p.1.cons_tail_eq hpnon
  have htailCons := p.1.tail.cons_tail_eq htailnon
  have hlist' := hlist
  unfold pathWeightList at hlist'
  rw [← hcons] at hlist'
  simp only [SimpleGraph.Walk.edges_cons, List.map_cons] at hlist'
  have hwa : T.weightOfPair s(u, p.1.snd) = a := by
    simpa using congrArg List.head? hlist'
  have htail : p.1.tail.edges.map T.weightOfPair = [b] := by
    simpa using congrArg List.tail hlist'
  rw [← htailCons] at htail
  simp only [SimpleGraph.Walk.edges_cons, List.map_cons] at htail
  have hwb : T.weightOfPair s(p.1.snd, p.1.tail.snd) = b := by
    simpa using congrArg List.head? htail
  have hne : eA ≠ eB := by
    intro heq
    have hval := congrArg Subtype.val heq
    have hnot : s(u, p.1.snd) ∉ p.1.tail.edges := by
      have hn := p.2.isTrail.edges_nodup
      rw [← hcons] at hn
      exact (List.nodup_cons.mp hn).1
    apply hnot
    change (eA : Sym2 (Fin 18)) ∈ p.1.tail.edges
    rw [hval]
    rw [← htailCons]
    simp [eB, edgeOfAdj]
  refine ⟨eA, eB, ?_, ?_, hne, p.1.snd, ?_, ?_⟩
  · simpa [eA, edgeOfAdj_weight] using hwa
  · simpa [eB, edgeOfAdj_weight] using hwb
  · simp [eA, edgeOfAdj]
  · simp [eB, edgeOfAdj]

private theorem weightFourPath_shape {T : PosIntTree 18}
    (hL : IsLeech T) {u v : Fin 18} (p : T.graph.Path u v)
    (htotal : T.walkWeight p.1 = 4) :
    (∃ e4 : T.Edge, T.weight e4 = 4) ∨
      ∃ e1 e3 : T.Edge,
        T.weight e1 = 1 ∧ T.weight e3 = 3 ∧ T.EdgeAdjacent e1 e3 := by
  have hsum : (pathWeightList p).sum = 4 := htotal
  rcases positive_nodup_sum_four_shape (pathWeightList_positive p)
      (pathWeightList_nodup hL p) hsum with h4 | h13 | h31
  · exact Or.inl (physicalEdge_of_singleton_weightList p h4)
  · exact Or.inr (adjacentEdges_of_pair_weightList p h13)
  · obtain ⟨e3, e1, h3, h1, hadj⟩ :=
      adjacentEdges_of_pair_weightList p h31
    exact Or.inr ⟨e1, e3, h1, h3,
      (T.edgeAdjacent_comm e1 e3).2 hadj⟩

private theorem existsUnique_edge_of_weight {T : PosIntTree 18}
    (hL : IsLeech T) {k : ℕ} (h : ∃ e : T.Edge, T.weight e = k) :
    ∃! e : T.Edge, T.weight e = k := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, he, fun f hf => t1_edge_weight_injective hL (hf.trans he.symm)⟩

private theorem existsUnique_weight_four_of_one_three_disjoint
    {T : PosIntTree 18} (hL : IsLeech T)
    (e1 e3 : T.Edge) (h1 : T.weight e1 = 1)
    (h3 : T.weight e3 = 3) (hdis : T.EdgeEndpointDisjoint e1 e3) :
    ∃! e4 : T.Edge, T.weight e4 = 4 := by
  have h4mem : 4 ∈ Finset.Icc 1 (targetN 18) := by norm_num [targetN, Nat.choose]
  obtain ⟨pair4, hp4, _⟩ := hL.target_existsUnique 4 h4mem
  have hwalk : T.walkWeight (T.path pair4.left pair4.right).1 = 4 := by
    rw [T.path_walkWeight_eq_dist]
    exact hp4
  rcases weightFourPath_shape hL (T.path pair4.left pair4.right) hwalk with
    h4 | ⟨f1, f3, hf1, hf3, hfadj⟩
  · exact existsUnique_edge_of_weight hL h4
  · have he1 : f1 = e1 := t1_edge_weight_injective hL (hf1.trans h1.symm)
    have he3 : f3 = e3 := t1_edge_weight_injective hL (hf3.trans h3.symm)
    subst f1
    subst f3
    obtain ⟨v, hv1, hv3⟩ := hfadj.2
    exact (hdis v hv1 hv3).elim

private theorem adjacent_one_three_no_weight_four
    {T : PosIntTree 18} (hL : IsLeech T)
    (e1 e3 : T.Edge) (h1 : T.weight e1 = 1)
    (h3 : T.weight e3 = 3) (hadj : T.EdgeAdjacent e1 e3) :
    ¬ ∃ e4 : T.Edge, T.weight e4 = 4 := by
  rintro ⟨e4, h4⟩
  obtain ⟨v, hv1, hv3⟩ := hadj.2
  let x : Fin 18 := Sym2.Mem.other hv1
  let y : Fin 18 := Sym2.Mem.other hv3
  have he1 : s(v, x) = e1.1 := Sym2.other_spec hv1
  have he3 : s(v, y) = e3.1 := Sym2.other_spec hv3
  have hvx : T.graph.Adj v x := by
    rw [← SimpleGraph.mem_edgeSet, he1]
    exact e1.2
  have hvy : T.graph.Adj v y := by
    rw [← SimpleGraph.mem_edgeSet, he3]
    exact e3.2
  have hxy : x ≠ y := by
    intro h
    apply hadj.1
    apply Subtype.ext
    rw [← he1, ← he3, h]
  let walk : T.graph.Walk x y :=
    SimpleGraph.Walk.cons hvx.symm
      (SimpleGraph.Walk.cons hvy SimpleGraph.Walk.nil)
  have hpath : walk.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simp [walk, hvx.ne.symm, hvy.ne, hxy]
  let p : T.graph.Path x y := ⟨walk, hpath⟩
  have hw1 : T.weightOfPair s(x, v) = 1 := by
    rw [Sym2.eq_swap, he1, T.weightOfPair_edge, h1]
  have hw3 : T.weightOfPair s(v, y) = 3 := by
    rw [he3, T.weightOfPair_edge, h3]
  have hdist : T.dist x y = 4 := by
    rw [← T.path_walkWeight_eq_dist p]
    simp [p, walk, PosIntTree.walkWeight, hw1, hw3]
  let pairXY := VertexPair.ofDistinct x y hxy
  have hpairs : pairXY = T.edgePair e4 := by
    apply hL.pairDist_injective
    rw [T.pairDist_pairOfDistinct, hdist, T.edgePair_dist, h4]
  have he4 : e4.1 = s(x, y) := by
    calc
      e4.1 = s((T.edgePair e4).left, (T.edgePair e4).right) :=
        T.edge_eq_mk_endpoints e4
      _ = s(pairXY.left, pairXY.right) := by rw [hpairs]
      _ = s(x, y) := by
        by_cases hxylt : x < y <;>
          simp [pairXY, VertexPair.ofDistinct, hxylt,
            VertexPair.left, VertexPair.right, Sym2.eq_swap]
  have hdirect : T.graph.Adj x y := by
    rw [← SimpleGraph.mem_edgeSet, ← he4]
    exact e4.2
  let direct : T.graph.Path x y := SimpleGraph.Path.singleton hdirect
  have heq : p = direct :=
    (T.path_unique p).trans (T.path_unique direct).symm
  have hlen := congrArg (fun q : T.graph.Path x y => q.1.length) heq
  simp [p, walk, direct, SimpleGraph.Path.singleton] at hlen

/-- The source's distance-3/4 trichotomy, now derived from the actual
`IsLeech` tree. -/
theorem exists_lowCase {T : PosIntTree 18} (hL : IsLeech T) :
    ∃ c : LowDistanceCase, LowCaseHolds T c := by
  obtain ⟨e1, h1, _⟩ := t1_existsUnique_weight_one hL (by omega)
  obtain ⟨e2, h2, _⟩ := t1_existsUnique_weight_two hL (by omega)
  rcases firstEdge_split_of_weights hL (by omega) e1 e2 h1 h2 with
    hcase1 | hcase23
  · exact ⟨.path3_edge4, e1, e2, h1, h2,
      hcase1.1, hcase1.2.1, hcase1.2.2⟩
  · obtain ⟨hdis12, e3, h3, huniq3⟩ := hcase23
    have hne13 : e1 ≠ e3 := by
      intro h
      have := congrArg T.weight h
      omega
    by_cases hmeet : ∃ v : Fin 18, v ∈ e1.1 ∧ v ∈ e3.1
    · have hadj13 : T.EdgeAdjacent e1 e3 := ⟨hne13, hmeet⟩
      exact ⟨.edge3_adj_path4, e1, e2, e3, h1, h2, h3,
        hdis12, hadj13,
        adjacent_one_three_no_weight_four hL e1 e3 h1 h3 hadj13⟩
    · have hdis13 : T.EdgeEndpointDisjoint e1 e3 := by
        intro v hv1 hv3
        exact hmeet ⟨v, hv1, hv3⟩
      exact ⟨.edge3_nonadj_edge4, e1, e2, e3, h1, h2, h3,
        hdis12, hdis13,
        existsUnique_weight_four_of_one_three_disjoint hL e1 e3 h1 h3 hdis13⟩

private theorem lowCase_unique {T : PosIntTree 18} (hL : IsLeech T)
    {c d : LowDistanceCase} (hc : LowCaseHolds T c)
    (hd : LowCaseHolds T d) : c = d := by
  cases c <;> cases d
  · rfl
  · rcases hc with ⟨_, _, _, _, _, hno3, _⟩
    rcases hd with ⟨_, _, e3, _, _, h3, _⟩
    exact (hno3 ⟨e3, h3⟩).elim
  · rcases hc with ⟨_, _, _, _, _, hno3, _⟩
    rcases hd with ⟨_, _, e3, _, _, h3, _⟩
    exact (hno3 ⟨e3, h3⟩).elim
  · rcases hd with ⟨_, _, _, _, _, hno3, _⟩
    rcases hc with ⟨_, _, e3, _, _, h3, _⟩
    exact (hno3 ⟨e3, h3⟩).elim
  · rfl
  · rcases hc with ⟨e1, _, e3, h1, _, h3, _, hdis, _⟩
    rcases hd with ⟨f1, _, f3, hf1, _, hf3, _, hadj, _⟩
    have he1 : e1 = f1 := t1_edge_weight_injective hL (h1.trans hf1.symm)
    have he3 : e3 = f3 := t1_edge_weight_injective hL (h3.trans hf3.symm)
    subst f1
    subst f3
    obtain ⟨v, hv1, hv3⟩ := hadj.2
    exact (hdis v hv1 hv3).elim
  · rcases hd with ⟨_, _, _, _, _, hno3, _⟩
    rcases hc with ⟨_, _, e3, _, _, h3, _⟩
    exact (hno3 ⟨e3, h3⟩).elim
  · rcases hc with ⟨e1, _, e3, h1, _, h3, _, hadj, _⟩
    rcases hd with ⟨f1, _, f3, hf1, _, hf3, _, hdis, _⟩
    have he1 : e1 = f1 := t1_edge_weight_injective hL (h1.trans hf1.symm)
    have he3 : e3 = f3 := t1_edge_weight_injective hL (h3.trans hf3.symm)
    subst f1
    subst f3
    obtain ⟨v, hv1, hv3⟩ := hadj.2
    exact (hdis v hv1 hv3).elim
  · rfl

theorem existsUnique_lowCase {T : PosIntTree 18} (hL : IsLeech T) :
    ∃! c : LowDistanceCase, LowCaseHolds T c := by
  obtain ⟨c, hc⟩ := exists_lowCase hL
  exact ⟨c, hc, fun d hd => lowCase_unique hL hd hc⟩

private theorem no_adjacent_one_three_of_oddBridges_separated
    {T : PosIntTree 18} {p : OpenPattern} (W : PatternWitness T p)
    (hsep : ∀ {i j : Fin 3}, i ≠ j →
      T.EdgeEndpointDisjoint (W.bridge i).1 (W.bridge j).1) :
    ¬ LowCaseHolds T .edge3_adj_path4 := by
  rintro ⟨e1, _, e3, h1, _, h3, _, hadj, _⟩
  let b1 : OddBridge T := ⟨e1, by simp [h1]⟩
  let b3 : OddBridge T := ⟨e3, by rw [h3]; norm_num⟩
  obtain ⟨i, hi⟩ := W.bridge_bijective.2 b1
  obtain ⟨j, hj⟩ := W.bridge_bijective.2 b3
  have hij : i ≠ j := by
    intro h
    subst j
    have hb : b1 = b3 := hi.symm.trans hj
    have he : e1 = e3 := congrArg (fun b : OddBridge T => b.1) hb
    have hw := congrArg T.weight he
    omega
  have hdis := hsep hij
  obtain ⟨v, hv1, hv3⟩ := hadj.2
  apply hdis v
  · have he : (W.bridge i).1 = e1 := by
      exact congrArg (fun b : OddBridge T => b.1) hi
    simpa [he] using hv1
  · have he : (W.bridge j).1 = e3 := by
      exact congrArg (fun b : OddBridge T => b.1) hj
    simpa [he] using hv3

/-- A semantic old assignment is an actual tree together with a particular
old model realization. -/
abbrev OldAssignment (T : PosIntTree 18) (hL : IsLeech T) :=
  Σ M : LegacyModel, RealizesLegacyModel T hL M

/-- Exact semantic representation equivalence for the scoped open branch:
an actual open quotient has an index in the concrete 720-model universe, and
every realized such index exposes an actual open quotient witness. -/
theorem openMultiport_iff_oldAssignment_nonempty
    {T : PosIntTree 18} (hL : IsLeech T) :
    OpenMultiport T ↔ Nonempty (OldAssignment T hL) := by
  constructor
  · intro hopen
    obtain ⟨⟨M, hM⟩⟩ := exists_legacyModel_of_openMultiport hL hopen
    exact ⟨⟨M, hM⟩⟩
  · rintro ⟨A⟩
    exact openMultiport_of_realizes A.2

/-- A semantic master assignment keeps the same actual tree and old
assignment, and adds exactly the low case named by its ten-row master. -/
structure MasterRealization {T : PosIntTree 18} {hL : IsLeech T}
    (m : Master) (A : OldAssignment T hL) : Prop where
  pattern_eq : A.1.pattern = m.1.1
  low : LowCaseHolds T m.1.2

/-- Actual geometry makes every realized low case admissible for its pattern;
in particular the adjacent `1+3` case is impossible in P4-DD and star-DDD. -/
theorem caseAdmissible_of_actual
    {T : PosIntTree 18} {hL : IsLeech T}
    (A : OldAssignment T hL) (c : LowDistanceCase)
    (hc : LowCaseHolds T c) : caseAdmissible A.1.pattern c := by
  cases c with
  | path3_edge4 => cases A.1.pattern <;> decide
  | edge3_nonadj_edge4 => cases A.1.pattern <;> decide
  | edge3_adj_path4 =>
      cases hpat : A.1.pattern with
      | p4SD => decide
      | starEED => decide
      | p4DD =>
          exfalso
          have W : PatternWitness T .p4DD := by
            simpa [hpat] using A.2.witness
          exact no_adjacent_one_three_of_oddBridges_separated W
            (fun hij => W.p4DD_bridge_endpoint_disjoint hij) hc
      | starDDD =>
          exfalso
          have W : PatternWitness T .starDDD := by
            simpa [hpat] using A.2.witness
          exact no_adjacent_one_three_of_oddBridges_separated W
            (fun hij => W.starDDD_bridge_endpoint_disjoint hij) hc

/-- Exact set equality behind the ten-master cover.  This theorem is stated
on actual assignments, not just pattern labels. -/
theorem old_assignment_iff_ten_master_union
    {T : PosIntTree 18} {hL : IsLeech T}
    (hlow : ∃! c : LowDistanceCase, LowCaseHolds T c) :
    (Nonempty (OldAssignment T hL) ↔
      ∃ m : Master, ∃ A : OldAssignment T hL, MasterRealization m A) := by
  constructor
  · rintro ⟨A⟩
    have hadm := caseAdmissible_of_actual A hlow.choose hlow.choose_spec.1
    have hm := existsUnique_master A.1.pattern hlow.choose hadm
    refine ⟨hm.choose, A, ?_⟩
    have hpair := hm.choose_spec.1
    exact {
      pattern_eq := (congrArg Prod.fst hpair).symm
      low := by
        rw [congrArg Prod.snd hpair]
        exact hlow.choose_spec.1 }
  · rintro ⟨m, A, _⟩
    exact ⟨A⟩

theorem old_assignment_iff_actual_ten_master_union
    {T : PosIntTree 18} (hL : IsLeech T) :
    (Nonempty (OldAssignment T hL) ↔
      ∃ m : Master, ∃ A : OldAssignment T hL, MasterRealization m A) :=
  old_assignment_iff_ten_master_union (existsUnique_lowCase hL)

/-- Queryable partition endpoint: every actual old assignment lies in exactly
one of the ten master assignment sets. -/
theorem existsUnique_masterRealization
    {T : PosIntTree 18} (hL : IsLeech T) (A : OldAssignment T hL) :
    ∃! m : Master, MasterRealization m A := by
  let low := Classical.choose (existsUnique_lowCase hL)
  have hlow : LowCaseHolds T low :=
    (Classical.choose_spec (existsUnique_lowCase hL)).1
  have hadm := caseAdmissible_of_actual A low hlow
  obtain ⟨m, hm, hmuniq⟩ := existsUnique_master A.1.pattern low hadm
  refine ⟨m, ⟨(congrArg Prod.fst hm).symm, ?_⟩, ?_⟩
  · rw [congrArg Prod.snd hm]
    exact hlow
  intro m' hm'
  have hcase : m'.1.2 = low :=
    (Classical.choose_spec (existsUnique_lowCase hL)).2 m'.1.2 hm'.low
  apply Subtype.ext
  apply Prod.ext
  · exact hm'.pattern_eq.symm.trans (congrArg Prod.fst hm).symm
  · exact hcase.trans (congrArg Prod.snd hm).symm

/-- Combined queryable G021 endpoint: every actual open quotient is represented
by a concrete old-model assignment lying in exactly one of the ten master
assignment sets. -/
theorem exists_assignment_unique_master_of_openMultiport
    {T : PosIntTree 18} (hL : IsLeech T) (hopen : OpenMultiport T) :
    ∃ A : OldAssignment T hL, ∃! m : Master, MasterRealization m A := by
  obtain ⟨A⟩ := (openMultiport_iff_oldAssignment_nonempty hL).1 hopen
  exact ⟨A, existsUnique_masterRealization hL A⟩

/-- Literal assignment-set equality for the ten-master cover. -/
theorem old_assignment_set_eq_ten_master_union
    {T : PosIntTree 18} (hL : IsLeech T) :
    (Set.univ : Set (OldAssignment T hL)) =
      ⋃ m : Master, {A | MasterRealization m A} := by
  ext A
  constructor
  · intro _
    obtain ⟨m, hm, _⟩ := existsUnique_masterRealization hL A
    exact Set.mem_iUnion.mpr ⟨m, hm⟩
  · intro _
    exact Set.mem_univ A

/-- The exact cardinalities used by the semantic cover. -/
theorem exact_index_universe_and_master_table :
    Fintype.card LegacyModel = 720 ∧ Fintype.card Master = 10 :=
  ⟨legacyModel_card, master_card⟩

end LeechTrees.OddQuotient.ThreeOddActualCover
