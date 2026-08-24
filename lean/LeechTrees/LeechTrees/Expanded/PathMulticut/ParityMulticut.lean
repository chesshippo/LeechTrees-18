import LeechTrees.ParityTailExactBundle
import LeechTrees.LeafRange
import LeechTrees.Expanded.PathMulticut.RankAllocation
import LeechTrees.Expanded.PathMulticut.PathSegmentStatistics

/-!
# Actual parity-resolved punctured multicut rearrangement

This file connects the generic rearrangement theorem to actual indexed pair
paths of a `PosIntTree`.  `IsLeech` supplies the nonedge-pair/nonphysical-rank
bijection; an ordering object supplies only sorted enumerations of those
actual finite types.  The rank permutation and every equality condition are
then derived rather than assumed.
-/

open scoped BigOperators

namespace LeechTrees.PathMulticut

open LeechTrees.Foundation
open LeechTrees.ParityTail
open LeechTrees.ParityTail.GraphAdapterV1
open LeechTrees.ParityTail.T8Collinear
open LeechTrees.ParityTail.T8ExactBundle

noncomputable section

/-! ## Exact parity coincidence entries -/

/-- The parity-channel coincidence entry for every nonempty collinear selected
edge set has the exact outer-component formula.  Singleton `F` gives the
diagonal entries (18), while `F={e,f}` gives the off-diagonal entries (19).
-/
theorem exact_collinear_parity_entries {n : ℕ}
    (T : PosIntTree n) (r : Fin n) (F : Finset T.Edge)
    (hF : F.Nonempty) (hcol : (pathSupport T F).Nonempty) :
    ∃ left right : Finset (Fin n),
      actualCF T F = left.card * right.card ∧
      actualKF T r F = signedMass (rootParitySign T r) left *
        signedMass (rootParitySign T r) right ∧
      2 * (actualEvenPathCount T F : ℤ) =
        ((left.card * right.card : ℕ) : ℤ) +
          signedMass (rootParitySign T r) left *
            signedMass (rootParitySign T r) right ∧
      2 * (actualOddPathCount T F : ℤ) =
        ((left.card * right.card : ℕ) : ℤ) -
          signedMass (rootParitySign T r) left *
            signedMass (rootParitySign T r) right := by
  obtain ⟨q₀, near, far, hq₀, hnear, hfar, hto, hfrom,
      E, hsign, hcard, hsigned⟩ :=
    T8_actual_collinear_extreme_outer_components
      T (rootParitySign T r) F hF hcol
  let left := rootOuterSet T q₀.left near
  let right := awayOuterSet T q₀.left far
  have hcounts := T8_actual_parity_counts_CF_KF T r F
  change actualEvenPathCount T F + actualOddPathCount T F =
      actualPathCoefficient T F ∧
    2 * (actualEvenPathCount T F : ℤ) =
      (actualPathCoefficient T F : ℤ) +
        actualSignedPathCoefficient T (rootParitySign T r) F ∧
    2 * (actualOddPathCount T F : ℤ) =
      (actualPathCoefficient T F : ℤ) -
        actualSignedPathCoefficient T (rootParitySign T r) F at hcounts
  refine ⟨left, right, ?_, ?_, ?_, ?_⟩
  · exact hcard
  · exact hsigned
  · rw [hcard, hsigned] at hcounts
    exact hcounts.2.1
  · rw [hcard, hsigned] at hcounts
    exact hcounts.2.2

/-! ## Literal signed second-moment equation (20) -/

/-- The coherent signed singleton/pair coefficient expansion.  The singleton
term is `x_e(4-x_e)` and each pair term is
`y_{e|f} y_{f|e}` by `exact_collinear_parity_entries`; using `actualKF`
keeps all those signs tied to the same root character. -/
noncomputable def actualSignedSecondMomentExpansion
    (T : PosIntTree 18) (r : Fin 18) : ℤ :=
  ((physicalEdgeList T).map fun e =>
      actualKF T r {e} * physicalWeightInt T e ^ 2).sum +
    2 * pairSum (physicalEdgeList T) (fun e f =>
      actualKF T r {e, f} * physicalWeightInt T e *
        physicalWeightInt T f)

private theorem list_sum_map_sub {α : Type*} (l : List α)
    (f g : α → ℤ) :
    (l.map f).sum - (l.map g).sum =
      (l.map fun x => f x - g x).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      calc
        f a + (l.map f).sum - (g a + (l.map g).sum) =
            (f a - g a) + ((l.map f).sum - (l.map g).sum) := by ring
        _ = (f a - g a) + (l.map fun x => f x - g x).sum := by rw [ih]

private theorem pairSum_sub {α : Type*} (l : List α)
    (f g : α → α → ℤ) :
    pairSum l f - pairSum l g =
      pairSum l (fun x y => f x y - g x y) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [pairSum_cons]
      rw [← list_sum_map_sub l (f a) (g a), ← ih]
      ring

/-- Difference of the even and odd actual path coefficients is the signed
coincidence coefficient `K_F` for the one common root character. -/
theorem actualParityPathCount_sub_eq_actualKF {n : ℕ}
    (T : PosIntTree n) (r : Fin n) (F : Finset T.Edge) :
    (actualParityPathCount T F 0 : ℤ) -
        actualParityPathCount T F 1 = actualKF T r F := by
  change (actualEvenPathCount T F : ℤ) -
      actualOddPathCount T F = actualKF T r F
  obtain ⟨hsum, heven, hodd⟩ := T8_actual_parity_counts_CF_KF T r F
  omega

theorem singletonCoefficient_sub_eq_actualKF {n : ℕ}
    (T : PosIntTree n) (r : Fin n) (e : T.Edge) :
    singletonCoefficient (pairParityBlock T 0) (pathIncidenceInt T) e -
      singletonCoefficient (pairParityBlock T 1) (pathIncidenceInt T) e =
        actualKF T r {e} := by
  rw [singletonCoefficient_eq_actualParityPathCount,
    singletonCoefficient_eq_actualParityPathCount]
  exact actualParityPathCount_sub_eq_actualKF T r {e}

theorem pairCoefficient_sub_eq_actualKF {n : ℕ}
    (T : PosIntTree n) (r : Fin n) (e f : T.Edge) :
    pairCoefficient (pairParityBlock T 0) (pathIncidenceInt T) e f -
      pairCoefficient (pairParityBlock T 1) (pathIncidenceInt T) e f =
        actualKF T r {e, f} := by
  rw [pairCoefficient_eq_actualParityPathCount,
    pairCoefficient_eq_actualParityPathCount]
  exact actualParityPathCount_sub_eq_actualKF T r {e, f}

/-- Equation (20), first in exact coefficient form: no independently chosen
edge signs occur, because every `actualKF` uses the same root character. -/
theorem order18_signed_second_moment_eq_neg11781
    {T : PosIntTree 18} (hL : IsLeech T) (r : Fin 18) :
    actualSignedSecondMomentExpansion T r = -11781 := by
  have hm := T8_actual_order18_parity_moment_system hL
  have hdiff : actualMomentExpansion2 T 0 -
      actualMomentExpansion2 T 1 = -11781 := by
    omega
  have hsingle :
      ((physicalEdgeList T).map (fun e =>
          singletonCoefficient (pairParityBlock T 0)
              (pathIncidenceInt T) e * physicalWeightInt T e ^ 2)).sum -
        ((physicalEdgeList T).map (fun e =>
          singletonCoefficient (pairParityBlock T 1)
              (pathIncidenceInt T) e * physicalWeightInt T e ^ 2)).sum =
        ((physicalEdgeList T).map (fun e =>
          actualKF T r {e} * physicalWeightInt T e ^ 2)).sum := by
      rw [list_sum_map_sub]
      apply congrArg List.sum
      apply List.map_congr_left
      intro e he
      rw [← singletonCoefficient_sub_eq_actualKF T r e]
      ring
  have hpairs :
      pairSum (physicalEdgeList T) (fun e f =>
          pairCoefficient (pairParityBlock T 0) (pathIncidenceInt T) e f *
            physicalWeightInt T e * physicalWeightInt T f) -
        pairSum (physicalEdgeList T) (fun e f =>
          pairCoefficient (pairParityBlock T 1) (pathIncidenceInt T) e f *
            physicalWeightInt T e * physicalWeightInt T f) =
        pairSum (physicalEdgeList T) (fun e f =>
          actualKF T r {e, f} * physicalWeightInt T e *
            physicalWeightInt T f) := by
      rw [pairSum_sub]
      apply pairSum_congr
      intro e f
      rw [← pairCoefficient_sub_eq_actualKF T r e f]
      ring
  rw [← hdiff]
  unfold actualSignedSecondMomentExpansion actualMomentExpansion2
  rw [← hsingle, ← hpairs]
  ring

/-- Unsigned companion to (20), retained at the same graph level. -/
theorem order18_unsigned_second_moment_eq_1205589
    {T : PosIntTree 18} (hL : IsLeech T) :
    actualMomentExpansion2 T 0 + actualMomentExpansion2 T 1 = 1205589 := by
  obtain ⟨h1e, h1o, h2e, h2o, h3e, h3o⟩ :=
    T8_actual_order18_parity_moment_system hL
  omega

/-- One ledger-facing bundle for G011: exact topology entries for every
nonempty actual collinear support, the signed order-18 equation, and its
unsigned companion. -/
theorem order18_parity_multicut_full_bundle
    {T : PosIntTree 18} (hL : IsLeech T) (r : Fin 18) :
    actualSignedSecondMomentExpansion T r = -11781 ∧
    actualMomentExpansion2 T 0 + actualMomentExpansion2 T 1 = 1205589 ∧
    ∀ F : Finset T.Edge, F.Nonempty → (pathSupport T F).Nonempty →
      ∃ left right : Finset (Fin 18),
        actualCF T F = left.card * right.card ∧
        actualKF T r F = signedMass (rootParitySign T r) left *
          signedMass (rootParitySign T r) right ∧
        2 * (actualEvenPathCount T F : ℤ) =
          ((left.card * right.card : ℕ) : ℤ) +
            signedMass (rootParitySign T r) left *
              signedMass (rootParitySign T r) right ∧
        2 * (actualOddPathCount T F : ℤ) =
          ((left.card * right.card : ℕ) : ℤ) -
            signedMass (rootParitySign T r) left *
              signedMass (rootParitySign T r) right := by
  refine ⟨order18_signed_second_moment_eq_neg11781 hL r,
    order18_unsigned_second_moment_eq_1205589 hL, ?_⟩
  intro F hF hcol
  exact exact_collinear_parity_entries T r F hF hcol

/-- Matrix notation expanded into actual indexed paths:
`aᵀ M^p w = Σ_{q in channel p} qScore(q) pairDist(q)`.
-/
def pathScore {n : ℕ} (T : PosIntTree n)
    (a : T.Edge → ℝ) (q : VertexPair n) : ℝ :=
  ∑ e : T.Edge, a e * (T.pathIncidence q e : ℝ)

def parityChannelMoment {n : ℕ} (T : PosIntTree n)
    (parity : ℕ) (a : T.Edge → ℝ) : ℝ :=
  ∑ q ∈ (Finset.univ.filter fun q : VertexPair n =>
      T.pairDist q % 2 = parity),
    pathScore T a q * T.pairDist q

def parityCoincidenceEntry {n : ℕ} (T : PosIntTree n)
    (parity : ℕ) (e f : T.Edge) : ℕ :=
  ∑ q ∈ (Finset.univ.filter fun q : VertexPair n =>
      T.pairDist q % 2 = parity),
    T.pathIncidence q e * T.pathIncidence q f

/-- A matrix entry is literally the number of actual paths of the selected
parity containing both displayed edges.  This is the missing bridge from the
matrix notation in (18)--(19) to the graph-level `pathSupport` count. -/
theorem parityCoincidenceEntry_eq_actualParityPathCount {n : ℕ}
    (T : PosIntTree n) (parity : ℕ) (e f : T.Edge) :
    parityCoincidenceEntry T parity e f =
      actualParityPathCount T {e, f} parity := by
  classical
  calc
    parityCoincidenceEntry T parity e f =
        ∑ q ∈ pairParityBlock T parity,
          if e.1 ∈ T.pathEdges q.left q.right ∧
              f.1 ∈ T.pathEdges q.left q.right then 1 else 0 := by
      unfold parityCoincidenceEntry pairParityBlock
      apply Finset.sum_congr rfl
      intro q hq
      simp only [PosIntTree.pathIncidence]
      by_cases he : e.1 ∈ T.pathEdges q.left q.right <;>
        by_cases hf : f.1 ∈ T.pathEdges q.left q.right <;>
        simp [he, hf]
    _ = ((pairParityBlock T parity).filter fun q =>
          e.1 ∈ T.pathEdges q.left q.right ∧
            f.1 ∈ T.pathEdges q.left q.right).card := by
      simp
    _ = actualParityPathCount T {e, f} parity := by
      apply congrArg Finset.card
      ext q
      simp only [pairParityBlock, pathSupport, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, forall_eq_or_imp, forall_eq]
      tauto

abbrev ParityCrossingPair {n : ℕ} (T : PosIntTree n)
    (e : T.Edge) (parity : ℕ) :=
  {q : VertexPair n // T.pairDist q % 2 = parity ∧
    e.1 ∈ T.pathEdges q.left q.right}

/-- The fixed-cut parity rows are exactly the parity-filtered Cartesian
product of the two actual deletion sides. -/
noncomputable def parityCrossingPairEquiv {n : ℕ} (T : PosIntTree n)
    (e : T.Edge) (parity : ℕ) :
    {x : T.LeftVertex e × T.RightVertex e //
      T.rootedCrossSum e x % 2 = parity} ≃
      ParityCrossingPair T e parity where
  toFun x := ⟨(T.crossingPairEquiv e x.1).1, by
    constructor
    · rw [T.crossingPairEquiv_apply_val e,
        T.pairDist_crossVertexPair e]
      exact x.2
    · exact (T.crossingPairEquiv e x.1).2⟩
  invFun q := ⟨(T.crossingPairEquiv e).symm ⟨q.1, q.2.2⟩, by
    have hpair := congrArg Subtype.val
      ((T.crossingPairEquiv e).apply_symm_apply ⟨q.1, q.2.2⟩)
    rw [T.crossingPairEquiv_apply_val e] at hpair
    have hparity := q.2.1
    rw [← hpair, T.pairDist_crossVertexPair e] at hparity
    exact hparity⟩
  left_inv x := by
    apply Subtype.ext
    exact (T.crossingPairEquiv e).symm_apply_apply x.1
  right_inv q := by
    apply Subtype.ext
    change ((T.crossingPairEquiv e)
      ((T.crossingPairEquiv e).symm ⟨q.1, q.2.2⟩)).1 = q.1
    exact congrArg Subtype.val
      ((T.crossingPairEquiv e).apply_symm_apply ⟨q.1, q.2.2⟩)

/-- Diagonal matrix entries count the actual parity-filtered cut rectangle. -/
theorem parityCoincidenceEntry_diag_eq_crossParityDomain_card {n : ℕ}
    (T : PosIntTree n) (parity : ℕ) (e : T.Edge) :
    parityCoincidenceEntry T parity e e =
      (crossParityDomain T e parity).card := by
  classical
  calc
    parityCoincidenceEntry T parity e e =
        (Finset.univ.filter fun q : VertexPair n =>
          T.pairDist q % 2 = parity ∧
            e.1 ∈ T.pathEdges q.left q.right).card := by
      unfold parityCoincidenceEntry
      calc
        (∑ q ∈ (Finset.univ.filter fun q : VertexPair n =>
            T.pairDist q % 2 = parity),
            T.pathIncidence q e * T.pathIncidence q e) =
            ∑ q ∈ (Finset.univ.filter fun q : VertexPair n =>
              T.pairDist q % 2 = parity),
              if e.1 ∈ T.pathEdges q.left q.right then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro q hq
          by_cases he : e.1 ∈ T.pathEdges q.left q.right <;>
            simp [PosIntTree.pathIncidence, he]
        _ = _ := by
          rw [← Finset.filter_filter, Finset.card_eq_sum_ones]
          simp only [Finset.sum_filter]
    _ = Fintype.card (ParityCrossingPair T e parity) := by
      simpa only [ParityCrossingPair] using
        (Fintype.card_subtype (fun q : VertexPair n =>
          T.pairDist q % 2 = parity ∧
            e.1 ∈ T.pathEdges q.left q.right)).symm
    _ = Fintype.card {x : T.LeftVertex e × T.RightVertex e //
          T.rootedCrossSum e x % 2 = parity} :=
      Fintype.card_congr (parityCrossingPairEquiv T e parity).symm
    _ = (crossParityDomain T e parity).card := by
      simpa only [crossParityDomain] using
        (Fintype.card_subtype (fun x : T.LeftVertex e × T.RightVertex e =>
          T.rootedCrossSum e x % 2 = parity))

/-- Literal diagonal entries (18), stated for the actual matrix entry and
the common normalized order-18 parity character. -/
theorem order18_parityCoincidenceEntry_diagonal
    {T : PosIntTree 18} (hL : IsLeech T) (r : Fin 18) (e : T.Edge) :
    2 * (parityCoincidenceEntry T 0 e e : ℤ) =
        (((T.cutSize e) * (18 - T.cutSize e) : ℕ) : ℤ) +
          leftImbalance18 T r e * (4 - leftImbalance18 T r e) ∧
    2 * (parityCoincidenceEntry T 1 e e : ℤ) =
        (((T.cutSize e) * (18 - T.cutSize e) : ℕ) : ℤ) -
          leftImbalance18 T r e * (4 - leftImbalance18 T r e) := by
  have hjoined := T8_actual_order18_edge_joined_counts hL r e
  rw [parityCoincidenceEntry_diag_eq_crossParityDomain_card,
    parityCoincidenceEntry_diag_eq_crossParityDomain_card,
    ← crossParityBlock_card T hL e 0,
    ← crossParityBlock_card T hL e 1]
  exact hjoined

/-- Literal off-diagonal entries (19).  For any two distinct actual edges the
common witness path and its extreme outer components are constructed, so no
collinearity or path-support witness is left to the caller. -/
theorem parityCoincidenceEntry_offDiagonal_outer_components {n : ℕ}
    (T : PosIntTree n) (r : Fin n) (e f : T.Edge) (hef : e ≠ f) :
    ∃ (q₀ : VertexPair n) (near far : T.Edge),
      q₀ ∈ pathSupport T {e, f} ∧ near ∈ ({e, f} : Finset T.Edge) ∧
      far ∈ ({e, f} : Finset T.Edge) ∧
      2 * (parityCoincidenceEntry T 0 e f : ℤ) =
        (((rootOuterSet T q₀.left near).card *
          (awayOuterSet T q₀.left far).card : ℕ) : ℤ) +
        signedMass (rootParitySign T r) (rootOuterSet T q₀.left near) *
          signedMass (rootParitySign T r) (awayOuterSet T q₀.left far) ∧
      2 * (parityCoincidenceEntry T 1 e f : ℤ) =
        (((rootOuterSet T q₀.left near).card *
          (awayOuterSet T q₀.left far).card : ℕ) : ℤ) -
        signedMass (rootParitySign T r) (rootOuterSet T q₀.left near) *
          signedMass (rootParitySign T r) (awayOuterSet T q₀.left far) := by
  obtain ⟨q, he, hf⟩ :=
    LeechTrees.LeafRange.exists_pair_containing_two_edges T e f hef
  have hq : q ∈ pathSupport T {e, f} := by
    simp only [pathSupport, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    exact ⟨he, hf⟩
  obtain ⟨q₀, near, far, hq₀, hnear, hfar, hto, hfrom,
      E, hsign, hcard, hsigned⟩ :=
    T8_actual_collinear_extreme_outer_components T (rootParitySign T r)
      {e, f} (by simp) ⟨q, hq⟩
  have hcounts := T8_actual_parity_counts_CF_KF T r {e, f}
  have hentry0 := parityCoincidenceEntry_eq_actualParityPathCount T 0 e f
  have hentry1 := parityCoincidenceEntry_eq_actualParityPathCount T 1 e f
  change actualEvenPathCount T {e, f} + actualOddPathCount T {e, f} =
      actualPathCoefficient T {e, f} ∧
    2 * (actualEvenPathCount T {e, f} : ℤ) =
      (actualPathCoefficient T {e, f} : ℤ) +
        actualSignedPathCoefficient T (rootParitySign T r) {e, f} ∧
    2 * (actualOddPathCount T {e, f} : ℤ) =
      (actualPathCoefficient T {e, f} : ℤ) -
        actualSignedPathCoefficient T (rootParitySign T r) {e, f} at hcounts
  rw [hcard, hsigned] at hcounts
  refine ⟨q₀, near, far, hq₀, hnear, hfar, ?_, ?_⟩
  · rw [hentry0]
    exact hcounts.2.1
  · rw [hentry1]
    exact hcounts.2.2

/-- Full (18)--(19) matrix-entry bundle: every diagonal and every distinct
off-diagonal entry is now an actual graph endpoint. -/
theorem order18_parityCoincidenceEntry_full_bundle
    {T : PosIntTree 18} (hL : IsLeech T) (r : Fin 18) :
    (∀ e : T.Edge,
      2 * (parityCoincidenceEntry T 0 e e : ℤ) =
          (((T.cutSize e) * (18 - T.cutSize e) : ℕ) : ℤ) +
            leftImbalance18 T r e * (4 - leftImbalance18 T r e) ∧
      2 * (parityCoincidenceEntry T 1 e e : ℤ) =
          (((T.cutSize e) * (18 - T.cutSize e) : ℕ) : ℤ) -
            leftImbalance18 T r e * (4 - leftImbalance18 T r e)) ∧
    (∀ e f : T.Edge, e ≠ f →
      ∃ (q₀ : VertexPair 18) (near far : T.Edge),
        q₀ ∈ pathSupport T {e, f} ∧ near ∈ ({e, f} : Finset T.Edge) ∧
        far ∈ ({e, f} : Finset T.Edge) ∧
        2 * (parityCoincidenceEntry T 0 e f : ℤ) =
          (((rootOuterSet T q₀.left near).card *
            (awayOuterSet T q₀.left far).card : ℕ) : ℤ) +
          signedMass (rootParitySign T r) (rootOuterSet T q₀.left near) *
            signedMass (rootParitySign T r) (awayOuterSet T q₀.left far) ∧
        2 * (parityCoincidenceEntry T 1 e f : ℤ) =
          (((rootOuterSet T q₀.left near).card *
            (awayOuterSet T q₀.left far).card : ℕ) : ℤ) -
          signedMass (rootParitySign T r) (rootOuterSet T q₀.left near) *
            signedMass (rootParitySign T r) (awayOuterSet T q₀.left far)) := by
  constructor
  · exact order18_parityCoincidenceEntry_diagonal hL r
  · intro e f hef
    exact parityCoincidenceEntry_offDiagonal_outer_components T r e f hef

abbrev ActualChannelNonedgePair {n : ℕ} (T : PosIntTree n)
    (parity : ℕ) :=
  {q : VertexPair n //
    T.pairDist q % 2 = parity ∧ ∀ e : T.Edge, q ≠ T.edgePair e}

abbrev ActualChannelNonphysicalRank {n : ℕ} (T : PosIntTree n)
    (parity : ℕ) :=
  {d : {d : ℕ // d ∈ Finset.Icc 1 (targetN n)} //
    d.1 % 2 = parity ∧ ∀ e : T.Edge, d.1 ≠ T.weight e}

/-- Contribution of the endpoint pairs of physical edges in one parity
channel. -/
def physicalChannelContribution {n : ℕ} (T : PosIntTree n)
    (parity : ℕ) (a : T.Edge → ℝ) : ℝ :=
  ∑ e ∈ (Finset.univ.filter fun e : T.Edge =>
      T.weight e % 2 = parity),
    a e * T.weight e

def physicalPairSet {n : ℕ} (T : PosIntTree n) : Finset (VertexPair n) :=
  Finset.univ.image T.edgePair

theorem pathScore_edgePair {n : ℕ} (T : PosIntTree n)
    (a : T.Edge → ℝ) (e : T.Edge) :
    pathScore T a (T.edgePair e) = a e := by
  classical
  unfold pathScore PosIntTree.pathIncidence
  simp only [T.edgePair_left, T.edgePair_right, T.pathEdges_edge e,
    Finset.mem_singleton]
  calc
    (∑ x : T.Edge, a x * ((if x.1 = e.1 then 1 else 0 : ℕ) : ℝ)) =
        ∑ x : T.Edge, if x = e then a x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : x = e
      · subst x
        simp
      · have hval : x.1 ≠ e.1 := fun hv => h (Subtype.ext hv)
        simp [h, hval]
    _ = a e := by simp

theorem physicalChannelPairSet_eq_image {n : ℕ} (T : PosIntTree n)
    (parity : ℕ) :
    ((Finset.univ.filter fun q : VertexPair n =>
        T.pairDist q % 2 = parity).filter fun q =>
          q ∈ physicalPairSet T) =
      ((Finset.univ.filter fun e : T.Edge =>
        T.weight e % 2 = parity).image T.edgePair) := by
  classical
  apply Finset.ext
  intro q
  constructor
  · intro hq
    obtain ⟨hqchannel, hqphysical⟩ := Finset.mem_filter.mp hq
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hqphysical
    subst q
    apply Finset.mem_image.mpr
    exact ⟨e, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, by simpa using (Finset.mem_filter.mp hqchannel).2⟩, rfl⟩
  · intro hq
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hq
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by simpa using (Finset.mem_filter.mp he).2⟩
    · exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩

theorem parityChannelMoment_eq_matrix {n : ℕ} (T : PosIntTree n)
    (parity : ℕ) (a : T.Edge → ℝ) :
    parityChannelMoment T parity a =
      ∑ e : T.Edge, ∑ f : T.Edge,
        a e * (parityCoincidenceEntry T parity e f : ℝ) * T.weight f := by
  classical
  let channel : Finset (VertexPair n) :=
    Finset.univ.filter fun q => T.pairDist q % 2 = parity
  have hdist (q : VertexPair n) :
      (T.pairDist q : ℝ) =
        ∑ f : T.Edge, (T.pathIncidence q f : ℝ) * T.weight f := by
    exact_mod_cast (T.pathIncidence_row q).symm
  unfold parityChannelMoment pathScore
  change (∑ q ∈ channel,
      (∑ e : T.Edge, a e * (T.pathIncidence q e : ℝ)) *
        T.pairDist q) = _
  simp_rw [hdist]
  calc
    (∑ q ∈ channel,
        (∑ e : T.Edge, a e * (T.pathIncidence q e : ℝ)) *
          ∑ f : T.Edge, (T.pathIncidence q f : ℝ) * T.weight f) =
        ∑ q ∈ channel, ∑ e : T.Edge, ∑ f : T.Edge,
          a e * (T.pathIncidence q e : ℝ) *
            (T.pathIncidence q f : ℝ) * T.weight f := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f hf
      ring
    _ = ∑ e : T.Edge, ∑ f : T.Edge, ∑ q ∈ channel,
          a e * (T.pathIncidence q e : ℝ) *
            (T.pathIncidence q f : ℝ) * T.weight f := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.sum_comm]
    _ = _ := by
      unfold parityCoincidenceEntry
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro f hf
      push_cast
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      ring

/-- Split the actual parity-channel moment into the fixed physical endpoint
pairs and the actual nonedge subtype. -/
theorem parityChannelMoment_eq_physical_add_nonedge {n : ℕ}
    {T : PosIntTree n} (_hL : IsLeech T) (parity : ℕ)
    (a : T.Edge → ℝ) :
    parityChannelMoment T parity a =
      physicalChannelContribution T parity a +
        ∑ q : ActualChannelNonedgePair T parity,
          pathScore T a q.1 * T.pairDist q.1 := by
  classical
  let channel : Finset (VertexPair n) :=
    Finset.univ.filter fun q => T.pairDist q % 2 = parity
  let term : VertexPair n → ℝ := fun q =>
    pathScore T a q * T.pairDist q
  have hsplit := Finset.sum_filter_add_sum_filter_not
    channel (fun q => q ∈ physicalPairSet T) term
  have hphysicalSet :
      channel.filter (fun q => q ∈ physicalPairSet T) =
        ((Finset.univ.filter fun e : T.Edge =>
          T.weight e % 2 = parity).image T.edgePair) := by
    exact physicalChannelPairSet_eq_image T parity
  have hphysical :
      (∑ q ∈ channel.filter (fun q => q ∈ physicalPairSet T), term q) =
        physicalChannelContribution T parity a := by
    rw [hphysicalSet]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro e he
      simp [term, pathScore_edgePair]
    · intro e he f hf hef
      exact edgePair_injective T hef
  have hnonedge :
      (∑ q ∈ channel.filter (fun q => q ∉ physicalPairSet T), term q) =
        ∑ q : ActualChannelNonedgePair T parity,
          pathScore T a q.1 * T.pairDist q.1 := by
    simpa only [term] using
      (Finset.sum_subtype
        (channel.filter (fun q => q ∉ physicalPairSet T))
        (by
          intro q
          constructor
          · intro hq
            obtain ⟨hqchannel, hqnot⟩ := Finset.mem_filter.mp hq
            refine ⟨(Finset.mem_filter.mp hqchannel).2, ?_⟩
            intro e hqe
            apply hqnot
            exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, hqe.symm⟩
          · rintro ⟨hparity, hne⟩
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hparity⟩, ?_⟩
            intro hphysical
            obtain ⟨e, _he, heq⟩ := Finset.mem_image.mp hphysical
            exact hne e heq.symm)
        term)
  unfold parityChannelMoment
  change (∑ q ∈ channel, term q) = _
  rw [← hsplit, hphysical, hnonedge]

/-! ## Actual punctured channel spectrum equivalence -/

/-- `IsLeech` restricts to a bijection in each parity channel after puncturing
all physical endpoint pairs/ranks. -/
noncomputable def actualChannelSpectrumEquiv {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) (parity : ℕ) :
    ActualChannelNonedgePair T parity ≃
      ActualChannelNonphysicalRank T parity where
  toFun q :=
    ⟨hL.spectrumEquiv q.1, q.2.1, by
      intro e he
      apply q.2.2 e
      apply hL.pairDist_injective
      simpa using he⟩
  invFun d :=
    ⟨(hL.spectrumEquiv).symm d.1,
      by
        have hs := congrArg Subtype.val
          ((hL.spectrumEquiv).apply_symm_apply d.1)
        change T.pairDist ((hL.spectrumEquiv).symm d.1) = d.1.1 at hs
        rw [hs]
        exact d.2.1,
      by
        intro e he
        apply d.2.2 e
        have hs := congrArg Subtype.val
          ((hL.spectrumEquiv).apply_symm_apply d.1)
        change T.pairDist ((hL.spectrumEquiv).symm d.1) = d.1.1 at hs
        calc
          d.1.1 = T.pairDist ((hL.spectrumEquiv).symm d.1) := hs.symm
          _ = T.pairDist (T.edgePair e) := congrArg T.pairDist he
          _ = T.weight e := T.edgePair_dist e⟩
  left_inv q := by
    apply Subtype.ext
    exact (hL.spectrumEquiv).symm_apply_apply q.1
  right_inv d := by
    apply Subtype.ext
    exact (hL.spectrumEquiv).apply_symm_apply d.1

@[simp] theorem actualChannelSpectrumEquiv_value {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) (parity : ℕ)
    (q : ActualChannelNonedgePair T parity) :
    (actualChannelSpectrumEquiv hL parity q).1.1 = T.pairDist q.1 := rfl

/-- Sorted enumerations of the actual punctured channel.  No rank assignment
is stored here; it is derived from `actualChannelSpectrumEquiv`. -/
structure ActualParityMulticutOrdering {n : ℕ} (T : PosIntTree n)
    (hL : IsLeech T) (parity L : ℕ) (a : T.Edge → ℝ) where
  pairOrder : Fin L ≃ ActualChannelNonedgePair T parity
  rankOrder : Fin L ≃ ActualChannelNonphysicalRank T parity
  score_mono : Monotone (fun i => pathScore T a (pairOrder i).1)
  rank_mono : Monotone (fun i => ((rankOrder i).1.1 : ℝ))

/-- The ordering object in (16) is constructed for every actual tree/channel
by sorting arbitrary finite enumerations.  Thus the graph-level theorem has no
residual "assume sorted enumerations exist" premise. -/
noncomputable def actualParityMulticutOrdering {n : ℕ}
    (T : PosIntTree n) (hL : IsLeech T) (parity : ℕ)
    (a : T.Edge → ℝ) :
    ActualParityMulticutOrdering T hL parity
      (Fintype.card (ActualChannelNonphysicalRank T parity)) a := by
  let L := Fintype.card (ActualChannelNonphysicalRank T parity)
  have hcard : Fintype.card (ActualChannelNonedgePair T parity) = L :=
    Fintype.card_congr (actualChannelSpectrumEquiv hL parity)
  let pairBase : Fin L ≃ ActualChannelNonedgePair T parity :=
    (finCongr hcard.symm).trans
      (Fintype.equivFin (ActualChannelNonedgePair T parity)).symm
  let rankBase : Fin L ≃ ActualChannelNonphysicalRank T parity :=
    (Fintype.equivFin (ActualChannelNonphysicalRank T parity)).symm
  let scoreKey : Fin L → ℝ := fun i => pathScore T a (pairBase i).1
  let rankKey : Fin L → ℝ := fun i => ((rankBase i).1.1 : ℝ)
  exact {
    pairOrder := (Tuple.sort scoreKey).trans pairBase
    rankOrder := (Tuple.sort rankKey).trans rankBase
    score_mono := by
      simpa [scoreKey, Function.comp_def] using Tuple.monotone_sort scoreKey
    rank_mono := by
      simpa [rankKey, Function.comp_def] using Tuple.monotone_sort rankKey }

theorem exists_actualParityMulticutOrdering {n : ℕ}
    (T : PosIntTree n) (hL : IsLeech T) (parity : ℕ)
    (a : T.Edge → ℝ) :
    Nonempty (ActualParityMulticutOrdering T hL parity
      (Fintype.card (ActualChannelNonphysicalRank T parity)) a) :=
  ⟨actualParityMulticutOrdering T hL parity a⟩

namespace ActualParityMulticutOrdering

variable {n parity L : ℕ} {T : PosIntTree n} {hL : IsLeech T}
  {a : T.Edge → ℝ}

def actualPermutation (O : ActualParityMulticutOrdering T hL parity L a) :
    Equiv.Perm (Fin L) :=
  O.pairOrder.trans
    ((actualChannelSpectrumEquiv hL parity).trans O.rankOrder.symm)

def sortedScore (O : ActualParityMulticutOrdering T hL parity L a) :
    Fin L → ℝ := fun i => pathScore T a (O.pairOrder i).1

def sortedRank (O : ActualParityMulticutOrdering T hL parity L a) :
    Fin L → ℝ := fun i => ((O.rankOrder i).1.1 : ℝ)

def actualNonedgeMoment
    (O : ActualParityMulticutOrdering T hL parity L a) : ℝ :=
  rankDot O.sortedScore (O.sortedRank ∘ O.actualPermutation)

theorem actualPermutation_rank
    (O : ActualParityMulticutOrdering T hL parity L a) (i : Fin L) :
    (O.rankOrder (O.actualPermutation i)).1.1 =
      T.pairDist (O.pairOrder i).1 := by
  simp [actualPermutation]

/-- The middle dot product in the rearrangement theorem is the actual
nonedge part of `aᵀM^p w`, and adding the fixed endpoint contribution recovers
the full actual parity-channel moment. -/
theorem parityChannelMoment_eq_fixed_add_actual
    (O : ActualParityMulticutOrdering T hL parity L a) :
    parityChannelMoment T parity a =
      physicalChannelContribution T parity a + O.actualNonedgeMoment := by
  rw [parityChannelMoment_eq_physical_add_nonedge hL parity a]
  congr 1
  calc
    (∑ q : ActualChannelNonedgePair T parity,
        pathScore T a q.1 * T.pairDist q.1) =
        ∑ i : Fin L,
          pathScore T a (O.pairOrder i).1 *
            T.pairDist (O.pairOrder i).1 := by
      symm
      apply Fintype.sum_equiv O.pairOrder
      intro i
      rfl
    _ = O.actualNonedgeMoment := by
      unfold actualNonedgeMoment rankDot sortedScore sortedRank
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Function.comp_apply]
      rw [show ((O.rankOrder (O.actualPermutation i)).1.1 : ℝ) =
          (T.pairDist (O.pairOrder i).1 : ℝ) by
        exact_mod_cast O.actualPermutation_rank i]

/-- Sharp parity-resolved, physical-rank-punctured multicut rearrangement.
Both equality cases are exact iff statements, including negative scores and
score ties. -/
theorem actual_punctured_multicut_rearrangement
    (O : ActualParityMulticutOrdering T hL parity L a) :
    lowerRankDot
        (fun i => pathScore T a (O.pairOrder i).1)
        (fun i => ((O.rankOrder i).1.1 : ℝ)) ≤
      rankDot
        (fun i => pathScore T a (O.pairOrder i).1)
        ((fun i => ((O.rankOrder i).1.1 : ℝ)) ∘ O.actualPermutation) ∧
    rankDot
        (fun i => pathScore T a (O.pairOrder i).1)
        ((fun i => ((O.rankOrder i).1.1 : ℝ)) ∘ O.actualPermutation) ≤
      upperRankDot
        (fun i => pathScore T a (O.pairOrder i).1)
        (fun i => ((O.rankOrder i).1.1 : ℝ)) ∧
    (rankDot
        (fun i => pathScore T a (O.pairOrder i).1)
        ((fun i => ((O.rankOrder i).1.1 : ℝ)) ∘ O.actualPermutation) =
        upperRankDot
          (fun i => pathScore T a (O.pairOrder i).1)
          (fun i => ((O.rankOrder i).1.1 : ℝ)) ↔
      Monovary
        (fun i => pathScore T a (O.pairOrder i).1)
        ((fun i => ((O.rankOrder i).1.1 : ℝ)) ∘ O.actualPermutation)) ∧
    (rankDot
        (fun i => pathScore T a (O.pairOrder i).1)
        ((fun i => ((O.rankOrder i).1.1 : ℝ)) ∘ O.actualPermutation) =
        lowerRankDot
          (fun i => pathScore T a (O.pairOrder i).1)
          (fun i => ((O.rankOrder i).1.1 : ℝ)) ↔
      Antivary
        (fun i => pathScore T a (O.pairOrder i).1)
        ((fun i => ((O.rankOrder i).1.1 : ℝ)) ∘ O.actualPermutation)) :=
  sharp_rank_rearrangement _ _ O.actualPermutation O.score_mono O.rank_mono

/-- Literal formula (16), including the fixed endpoint-pair contribution.
The equality iff clauses are unchanged by adding that fixed term. -/
theorem actual_punctured_multicut_rearrangement_with_physical
    (O : ActualParityMulticutOrdering T hL parity L a) :
    physicalChannelContribution T parity a +
        lowerRankDot O.sortedScore O.sortedRank ≤
      physicalChannelContribution T parity a + O.actualNonedgeMoment ∧
    physicalChannelContribution T parity a + O.actualNonedgeMoment ≤
      physicalChannelContribution T parity a +
        upperRankDot O.sortedScore O.sortedRank ∧
    (physicalChannelContribution T parity a + O.actualNonedgeMoment =
        physicalChannelContribution T parity a +
          upperRankDot O.sortedScore O.sortedRank ↔
      Monovary O.sortedScore (O.sortedRank ∘ O.actualPermutation)) ∧
    (physicalChannelContribution T parity a + O.actualNonedgeMoment =
        physicalChannelContribution T parity a +
          lowerRankDot O.sortedScore O.sortedRank ↔
      Antivary O.sortedScore (O.sortedRank ∘ O.actualPermutation)) := by
  exact sharp_rank_rearrangement_with_fixed
    (physicalChannelContribution T parity a) O.sortedScore O.sortedRank
      O.actualPermutation O.score_mono O.rank_mono

end ActualParityMulticutOrdering

/-- The complete conclusion of (16), packaged so the public graph endpoint
does not take a preconstructed ordering object. -/
def CanonicalPuncturedMulticutConclusion {n parity L : ℕ}
    {T : PosIntTree n} {hL : IsLeech T} {a : T.Edge → ℝ}
    (O : ActualParityMulticutOrdering T hL parity L a) : Prop :=
  physicalChannelContribution T parity a +
        lowerRankDot O.sortedScore O.sortedRank ≤
      physicalChannelContribution T parity a + O.actualNonedgeMoment ∧
  physicalChannelContribution T parity a + O.actualNonedgeMoment ≤
      physicalChannelContribution T parity a +
        upperRankDot O.sortedScore O.sortedRank ∧
  (physicalChannelContribution T parity a + O.actualNonedgeMoment =
      physicalChannelContribution T parity a +
        upperRankDot O.sortedScore O.sortedRank ↔
    Monovary O.sortedScore (O.sortedRank ∘ O.actualPermutation)) ∧
  (physicalChannelContribution T parity a + O.actualNonedgeMoment =
      physicalChannelContribution T parity a +
        lowerRankDot O.sortedScore O.sortedRank ↔
    Antivary O.sortedScore (O.sortedRank ∘ O.actualPermutation))

/-- Formula (16) with the sorted enumerations constructed internally from the
actual graph.  In particular, callers supply only `T`, `IsLeech`, the parity
channel, and the edge score vector; both sharp equality iff clauses survive. -/
theorem canonical_actual_punctured_multicut_rearrangement {n : ℕ}
    (T : PosIntTree n) (hL : IsLeech T) (parity : ℕ)
    (a : T.Edge → ℝ) :
    CanonicalPuncturedMulticutConclusion
      (actualParityMulticutOrdering T hL parity a) := by
  unfold CanonicalPuncturedMulticutConclusion
  exact ActualParityMulticutOrdering.actual_punctured_multicut_rearrangement_with_physical
    (actualParityMulticutOrdering T hL parity a)

end

end LeechTrees.PathMulticut
