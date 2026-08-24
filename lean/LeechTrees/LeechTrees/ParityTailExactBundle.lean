import LeechTrees.ParityTailCollinear

/-!
# Ledger-exact public bundle for T8

This isolated module only packages the already compiled actual-tree T8
geometry, parity counts, moment coefficients, and order-18 cut algebra in the
literal form used by the preprint ledger.
-/

open scoped BigOperators

namespace LeechTrees.ParityTail.T8ExactBundle

open LeechTrees.Foundation
open LeechTrees.ParityTail.GraphAdapterV1
open LeechTrees.ParityTail.T8Collinear

noncomputable section

/-! ## Extreme edges and characterized outer components -/

/-- The actual collinear branch with the witness path, extreme selected
edges, nested-cut characterization, endpoint-pair equivalence, and the two
factorizations all retained in one public statement. -/
theorem T8_actual_collinear_extreme_outer_components {n : ℕ}
    (T : PosIntTree n) (sign : Fin n → ℤ) (F : Finset T.Edge)
    (hF : F.Nonempty) (hcol : (pathSupport T F).Nonempty) :
    ∃ (q₀ : VertexPair n) (near far : T.Edge),
      q₀ ∈ pathSupport T F ∧ near ∈ F ∧ far ∈ F ∧
      (∀ f ∈ F, ∀ x,
        OrientedCut.Away T q₀.left f x →
          OrientedCut.Away T q₀.left near x) ∧
      (∀ f ∈ F, ∀ x,
        OrientedCut.Away T q₀.left far x →
          OrientedCut.Away T q₀.left f x) ∧
      ∃ E : {q : VertexPair n // q ∈ pathSupport T F} ≃
          ({u : Fin n // u ∈ rootOuterSet T q₀.left near} ×
            {v : Fin n // v ∈ awayOuterSet T q₀.left far}),
        (∀ q, sign q.1.left * sign q.1.right =
          sign (E q).1.1 * sign (E q).2.1) ∧
        actualPathCoefficient T F =
          (rootOuterSet T q₀.left near).card *
            (awayOuterSet T q₀.left far).card ∧
        actualSignedPathCoefficient T sign F =
          signedMass sign (rootOuterSet T q₀.left near) *
            signedMass sign (awayOuterSet T q₀.left far) := by
  obtain ⟨q₀, hq₀⟩ := hcol
  obtain ⟨near, far, hnear, hfar, toNear, fromFar⟩ :=
    exists_extreme_edges T F hF q₀ hq₀
  let E := supportOuterFinsetEquiv T q₀.left F near far
    hnear hfar toNear fromFar
  let cert : OuterCertificate T sign F := {
    left := rootOuterSet T q₀.left near
    right := awayOuterSet T q₀.left far
    equiv := E
    sign_product := supportOuterFinsetEquiv_sign_product
      T q₀.left F near far hnear hfar toNear fromFar sign }
  have hfactor := T8_actual_collinear_outer_factorization T sign F cert
  exact ⟨q₀, near, far, hq₀, hnear, hfar, toNear, fromFar, E,
    cert.sign_product, hfactor.1, hfactor.2⟩

/-! ## Actual `C_F^p`, `C_F`, and `K_F` -/

/-- Actual indexed pair paths of parity `p` containing every edge of `F`.
This is an index count, not a distance-value image count. -/
def actualParityPathCount {n : ℕ} (T : PosIntTree n)
    (F : Finset T.Edge) (p : ℕ) : ℕ :=
  ((pathSupport T F).filter fun q => T.pairDist q % 2 = p).card

/-- The paper's actual `C_F^+`. -/
abbrev actualEvenPathCount {n : ℕ} (T : PosIntTree n)
    (F : Finset T.Edge) : ℕ := actualParityPathCount T F 0

/-- The paper's actual `C_F^-`. -/
abbrev actualOddPathCount {n : ℕ} (T : PosIntTree n)
    (F : Finset T.Edge) : ℕ := actualParityPathCount T F 1

/-- The paper's actual ordinary coefficient `C_F`. -/
abbrev actualCF {n : ℕ} (T : PosIntTree n) (F : Finset T.Edge) : ℕ :=
  actualPathCoefficient T F

/-- The paper's actual signed coefficient `K_F`, using its root sign. -/
abbrev actualKF {n : ℕ} (T : PosIntTree n) (r : Fin n)
    (F : Finset T.Edge) : ℤ :=
  actualSignedPathCoefficient T (rootParitySign T r) F

private def pairRootSign {n : ℕ} (T : PosIntTree n) (r : Fin n)
    (q : VertexPair n) : ℤ :=
  rootParitySign T r q.left * rootParitySign T r q.right

private theorem pairRootSign_pm {n : ℕ} (T : PosIntTree n)
    (r : Fin n) (q : VertexPair n) :
    pairRootSign T r q = 1 ∨ pairRootSign T r q = -1 := by
  rcases rootParitySign_pm T r q.left with hl | hl <;>
    rcases rootParitySign_pm T r q.right with hr | hr <;>
    simp [pairRootSign, hl, hr]

theorem actualEvenPathCount_eq_positiveCount {n : ℕ}
    (T : PosIntTree n) (r : Fin n) (F : Finset T.Edge) :
    actualEvenPathCount T F =
      positiveCount (pairRootSign T r) (pathSupport T F) := by
  classical
  unfold actualEvenPathCount actualParityPathCount positiveCount
  congr 1
  ext q
  simp only [Finset.mem_filter]
  rw [show pairRootSign T r q = paritySign (T.pairDist q) by
    exact rootParitySign_pairDist T r q]
  rw [paritySign_eq_one_iff_mod_two]

theorem actualOddPathCount_eq_negativeCount {n : ℕ}
    (T : PosIntTree n) (r : Fin n) (F : Finset T.Edge) :
    actualOddPathCount T F =
      negativeCount (pairRootSign T r) (pathSupport T F) := by
  classical
  unfold actualOddPathCount actualParityPathCount negativeCount
  congr 1
  ext q
  simp only [Finset.mem_filter]
  rw [show pairRootSign T r q = paritySign (T.pairDist q) by
    exact rootParitySign_pairDist T r q]
  rw [paritySign_eq_neg_one_iff_mod_two]

theorem actualKF_eq_signedMass {n : ℕ} (T : PosIntTree n)
    (r : Fin n) (F : Finset T.Edge) :
    actualKF T r F = signedMass (pairRootSign T r) (pathSupport T F) := by
  unfold actualKF actualSignedPathCoefficient signedMass pairRootSign
  change (∑ q ∈ (pathSupport T F).attach,
      rootParitySign T r q.1.left * rootParitySign T r q.1.right) =
    ∑ q ∈ pathSupport T F,
      rootParitySign T r q.left * rootParitySign T r q.right
  simpa using (Finset.sum_attach (pathSupport T F)
    (fun q : VertexPair n =>
      rootParitySign T r q.left * rootParitySign T r q.right))

/-- Literal actual-tree form of
`C_F^+ + C_F^- = C_F`, `2C_F^+ = C_F + K_F`, and
`2C_F^- = C_F - K_F`. -/
theorem T8_actual_parity_counts_CF_KF {n : ℕ}
    (T : PosIntTree n) (r : Fin n) (F : Finset T.Edge) :
    actualEvenPathCount T F + actualOddPathCount T F = actualCF T F ∧
    2 * (actualEvenPathCount T F : ℤ) =
      (actualCF T F : ℤ) + actualKF T r F ∧
    2 * (actualOddPathCount T F : ℤ) =
      (actualCF T F : ℤ) - actualKF T r F := by
  have hsum := positiveCount_add_negativeCount
    (pairRootSign T r) (pathSupport T F)
    (fun q hq => pairRootSign_pm T r q)
  have hdiff := signedMass_eq_count_sub
    (pairRootSign T r) (pathSupport T F)
    (fun q hq => pairRootSign_pm T r q)
  have hsumZ :
      (positiveCount (pairRootSign T r) (pathSupport T F) : ℤ) +
        negativeCount (pairRootSign T r) (pathSupport T F) =
          (actualCF T F : ℤ) := by
    exact_mod_cast hsum
  have hK : actualKF T r F =
      (positiveCount (pairRootSign T r) (pathSupport T F) : ℤ) -
        negativeCount (pairRootSign T r) (pathSupport T F) := by
    rw [actualKF_eq_signedMass]
    exact hdiff
  have heven := actualEvenPathCount_eq_positiveCount T r F
  have hodd := actualOddPathCount_eq_negativeCount T r F
  constructor
  · rw [heven, hodd]
    exact hsum
  constructor
  · rw [heven, hK]
    omega
  · rw [hodd, hK]
    omega

/-! ## Moment-coefficient bridges -/

theorem singletonCoefficient_eq_actualParityPathCount {n : ℕ}
    (T : PosIntTree n) (p : ℕ) (e : T.Edge) :
    singletonCoefficient (pairParityBlock T p) (pathIncidenceInt T) e =
      (actualParityPathCount T {e} p : ℤ) := by
  classical
  calc
    singletonCoefficient (pairParityBlock T p) (pathIncidenceInt T) e =
        (((pairParityBlock T p).filter fun q =>
          e.1 ∈ T.pathEdges q.left q.right).card : ℤ) := by
      unfold singletonCoefficient
      simp [pathIncidenceInt, PosIntTree.pathIncidence]
    _ = (actualParityPathCount T {e} p : ℤ) := by
      congr 1
      apply congrArg Finset.card
      ext q
      simp [pairParityBlock, pathSupport, and_comm]

theorem pairCoefficient_eq_actualParityPathCount {n : ℕ}
    (T : PosIntTree n) (p : ℕ) (e f : T.Edge) :
    pairCoefficient (pairParityBlock T p) (pathIncidenceInt T) e f =
      (actualParityPathCount T {e, f} p : ℤ) := by
  classical
  calc
    pairCoefficient (pairParityBlock T p) (pathIncidenceInt T) e f =
        ∑ q ∈ pairParityBlock T p,
          if e.1 ∈ T.pathEdges q.left q.right ∧
              f.1 ∈ T.pathEdges q.left q.right then (1 : ℤ) else 0 := by
      unfold pairCoefficient
      apply Finset.sum_congr rfl
      intro q hq
      simp only [pathIncidenceInt, PosIntTree.pathIncidence]
      by_cases he : e.1 ∈ T.pathEdges q.left q.right <;>
        by_cases hf : f.1 ∈ T.pathEdges q.left q.right <;>
        simp [he, hf]
    _ = ((((pairParityBlock T p).filter fun q =>
          e.1 ∈ T.pathEdges q.left q.right ∧
            f.1 ∈ T.pathEdges q.left q.right).card : ℕ) : ℤ) := by
      simp
    _ = (actualParityPathCount T {e, f} p : ℤ) := by
      congr 1
      apply congrArg Finset.card
      ext q
      simp only [pairParityBlock, pathSupport, Finset.mem_filter,
        Finset.mem_univ, true_and]
      simp only [Finset.mem_insert, Finset.mem_singleton,
        forall_eq_or_imp, forall_eq]
      tauto

theorem tripleCoefficient_eq_actualParityPathCount {n : ℕ}
    (T : PosIntTree n) (p : ℕ) (e f g : T.Edge) :
    tripleCoefficient (pairParityBlock T p) (pathIncidenceInt T) e f g =
      (actualParityPathCount T {e, f, g} p : ℤ) := by
  classical
  calc
    tripleCoefficient (pairParityBlock T p) (pathIncidenceInt T) e f g =
        ∑ q ∈ pairParityBlock T p,
          if e.1 ∈ T.pathEdges q.left q.right ∧
              f.1 ∈ T.pathEdges q.left q.right ∧
              g.1 ∈ T.pathEdges q.left q.right then (1 : ℤ) else 0 := by
      unfold tripleCoefficient
      apply Finset.sum_congr rfl
      intro q hq
      simp only [pathIncidenceInt, PosIntTree.pathIncidence]
      by_cases he : e.1 ∈ T.pathEdges q.left q.right <;>
        by_cases hf : f.1 ∈ T.pathEdges q.left q.right <;>
        by_cases hg : g.1 ∈ T.pathEdges q.left q.right <;>
        simp [he, hf, hg]
    _ = ((((pairParityBlock T p).filter fun q =>
          e.1 ∈ T.pathEdges q.left q.right ∧
            f.1 ∈ T.pathEdges q.left q.right ∧
              g.1 ∈ T.pathEdges q.left q.right).card : ℕ) : ℤ) := by
      simp
    _ = (actualParityPathCount T {e, f, g} p : ℤ) := by
      congr 1
      apply congrArg Finset.card
      ext q
      simp only [pairParityBlock, pathSupport, Finset.mem_filter,
        Finset.mem_univ, true_and]
      simp only [Finset.mem_insert, Finset.mem_singleton,
        forall_eq_or_imp, forall_eq]
      tauto

/-- One ledger-facing conjunction identifying every raw moment coefficient
with the corresponding actual indexed `C_F^p`. -/
theorem T8_actual_moment_coefficients_are_parity_counts {n : ℕ}
    (T : PosIntTree n) (p : ℕ) (e f g : T.Edge) :
    singletonCoefficient (pairParityBlock T p) (pathIncidenceInt T) e =
        (actualParityPathCount T {e} p : ℤ) ∧
    pairCoefficient (pairParityBlock T p) (pathIncidenceInt T) e f =
        (actualParityPathCount T {e, f} p : ℤ) ∧
    tripleCoefficient (pairParityBlock T p) (pathIncidenceInt T) e f g =
        (actualParityPathCount T {e, f, g} p : ℤ) := by
  exact ⟨singletonCoefficient_eq_actualParityPathCount T p e,
    pairCoefficient_eq_actualParityPathCount T p e f,
    tripleCoefficient_eq_actualParityPathCount T p e f g⟩

/-- The actual triple coefficient vanishes whenever no canonical pair path
contains the three displayed physical edges. -/
theorem T8_actual_noncollinear_tripleCoefficient_zero {n : ℕ}
    (T : PosIntTree n) (p : ℕ) (e f g : T.Edge)
    (noncollinear : ¬∃ q : VertexPair n,
      e.1 ∈ T.pathEdges q.left q.right ∧
      f.1 ∈ T.pathEdges q.left q.right ∧
      g.1 ∈ T.pathEdges q.left q.right) :
    tripleCoefficient (pairParityBlock T p) (pathIncidenceInt T) e f g = 0 := by
  rw [tripleCoefficient_eq_actualParityPathCount]
  unfold actualParityPathCount
  have hs : pathSupport T {e, f, g} = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    apply noncollinear
    have hcontains := (Finset.mem_filter.mp hq).2
    exact ⟨q, hcontains e (by simp), hcontains f (by simp),
      hcontains g (by simp)⟩
  rw [hs]
  simp

/-! ## Joined order-18 edge identities -/

/-- Literal joined order-18 identities
`2h⁺ = c + κ` and `2h⁻ = c - κ` for every actual edge, with
`c = s(18-s)`, `x` the normalized left mass, and `κ = x(4-x)`. -/
theorem T8_actual_order18_edge_joined_counts
    {T : PosIntTree 18} (hL : IsLeech T) (r : Fin 18) (e : T.Edge) :
    2 * ((crossParityBlock T e 0).card : ℤ) =
        (((T.cutSize e) * (18 - T.cutSize e) : ℕ) : ℤ) +
          leftImbalance18 T r e * (4 - leftImbalance18 T r e) ∧
    2 * ((crossParityBlock T e 1).card : ℤ) =
        (((T.cutSize e) * (18 - T.cutSize e) : ℕ) : ℤ) -
          leftImbalance18 T r e * (4 - leftImbalance18 T r e) := by
  have halg := T8_signed_cross_count_algebra
    (leftPositive18 T r e) (leftNegative18 T r e)
    (rightPositive18 T r e) (rightNegative18 T r e)
  have ha := leftCounts_total18 T r e
  have hb := rightCounts_total18 T r e
  have hg := cutGlobalSignEquation18 hL r e
  have hy : (rightPositive18 T r e : ℤ) - rightNegative18 T r e =
      4 - leftImbalance18 T r e := by
    unfold leftImbalance18
    omega
  rcases halg with ⟨hplus, hminus, -, -⟩
  constructor
  · rw [crossParityBlock_zero_card18 hL r e]
    rw [ha, hb, hy] at hplus
    exact hplus
  · rw [crossParityBlock_one_card18 hL r e]
    rw [ha, hb, hy] at hminus
    exact hminus

/-- The joined count equations together with the exact parity and side
bounds on `x`. -/
theorem T8_actual_order18_edge_counts_and_feasibility
    {T : PosIntTree 18} (hL : IsLeech T) (r : Fin 18) (e : T.Edge) :
    (2 * ((crossParityBlock T e 0).card : ℤ) =
        (((T.cutSize e) * (18 - T.cutSize e) : ℕ) : ℤ) +
          leftImbalance18 T r e * (4 - leftImbalance18 T r e) ∧
      2 * ((crossParityBlock T e 1).card : ℤ) =
        (((T.cutSize e) * (18 - T.cutSize e) : ℕ) : ℤ) -
          leftImbalance18 T r e * (4 - leftImbalance18 T r e)) ∧
    (leftImbalance18 T r e % 2 = (T.cutSize e : ℤ) % 2 ∧
      -(T.cutSize e : ℤ) ≤ leftImbalance18 T r e ∧
      leftImbalance18 T r e ≤ (T.cutSize e : ℤ) ∧
      -((18 - T.cutSize e : ℕ) : ℤ) ≤ 4 - leftImbalance18 T r e ∧
      4 - leftImbalance18 T r e ≤ ((18 - T.cutSize e : ℕ) : ℤ)) := by
  exact ⟨T8_actual_order18_edge_joined_counts hL r e,
    T8_actual_order18_side_feasibility hL r e⟩

end

end LeechTrees.ParityTail.T8ExactBundle
