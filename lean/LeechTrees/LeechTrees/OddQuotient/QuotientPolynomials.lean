import LeechTrees.OddQuotient.PairPartition

/-!
# Odd-quotient rank polynomials

This file uses the exact canonical route between every pair of distinct even
components.  Its cross terms retain the actual first bridge port, last bridge
port, and every intermediate port separation stored by `routeShift`.

All statements are forward identities for an existing `PosIntTree`.  No
polynomial identity below is a quotient certificate or a realization
converse.
-/

open scoped BigOperators Polynomial

namespace LeechTrees.OddQuotient

open LeechTrees.Foundation

variable {n : ℕ}

/-! ## A nonempty head-tail presentation of each canonical cross route -/

/-- Data exposing the first edge of the canonical quotient path.  Distinct
component endpoints make that path nonempty. -/
structure CanonicalRouteData (T : PosIntTree n)
    (q : QuotientComponentPair T) where
  next : EvenComponent T
  head : (quotientGraph T).Adj q.left next
  tail : (quotientGraph T).Walk next q.right
  isPath :
    (SimpleGraph.Walk.cons head tail :
      (quotientGraph T).Walk q.left q.right).IsPath
  eq_quotientPath :
    (SimpleGraph.Walk.cons head tail :
      (quotientGraph T).Walk q.left q.right) =
        (quotientPath T q.left q.right).1

theorem canonicalRouteData_nonempty (T : PosIntTree n)
    (q : QuotientComponentPair T) :
    Nonempty (CanonicalRouteData T q) := by
  obtain ⟨D, h, p, hp⟩ :=
    (quotientPath T q.left q.right).1.exists_eq_cons_of_ne q.ne
  refine ⟨{
    next := D
    head := h
    tail := p
    isPath := ?_
    eq_quotientPath := hp.symm }⟩
  rw [← hp]
  exact (quotientPath T q.left q.right).2

/-- The proof-irrelevant chosen head-tail presentation of the exact canonical
quotient path. -/
noncomputable def canonicalRouteData (T : PosIntTree n)
    (q : QuotientComponentPair T) : CanonicalRouteData T q :=
  Classical.choice (canonicalRouteData_nonempty T q)

/-- The canonical route, displayed as a nonempty walk. -/
noncomputable def canonicalRouteWalk (T : PosIntTree n)
    (q : QuotientComponentPair T) :
    (quotientGraph T).Walk q.left q.right :=
  .cons (canonicalRouteData T q).head (canonicalRouteData T q).tail

theorem canonicalRouteWalk_isPath (T : PosIntTree n)
    (q : QuotientComponentPair T) :
    (canonicalRouteWalk T q).IsPath :=
  (canonicalRouteData T q).isPath

theorem canonicalRouteWalk_eq_quotientPath (T : PosIntTree n)
    (q : QuotientComponentPair T) :
    canonicalRouteWalk T q = (quotientPath T q.left q.right).1 :=
  (canonicalRouteData T q).eq_quotientPath

/-- Parity of the number of actual odd bridges on the canonical quotient
route. -/
noncomputable def quotientPairParity (T : PosIntTree n)
    (q : QuotientComponentPair T) : ℕ :=
  (canonicalRouteWalk T q).length % 2

theorem quotientPairParity_lt_two (T : PosIntTree n)
    (q : QuotientComponentPair T) : quotientPairParity T q < 2 := by
  exact Nat.mod_lt _ (by omega)

/-- The actual first port in the left endpoint component. -/
noncomputable def canonicalSourcePort (T : PosIntTree n)
    (q : QuotientComponentPair T) : ComponentVertex T q.left :=
  (orientedBridgeOfAdj T (canonicalRouteData T q).head).sourcePort

/-- The actual last port in the right endpoint component. -/
noncomputable def canonicalTargetPort (T : PosIntTree n)
    (q : QuotientComponentPair T) : ComponentVertex T q.right :=
  routeTerminal T (canonicalRouteData T q).tail
    (orientedBridgeOfAdj T (canonicalRouteData T q).head).targetPort

/-- The endpoint-independent route shift: bridge half-weights,
`floor(k/2)`, and every scaled intermediate entry/exit-port separation. -/
noncomputable def canonicalRouteShift (T : PosIntTree n)
    (q : QuotientComponentPair T) : ℕ :=
  routeShift T (canonicalRouteData T q).head
    (canonicalRouteData T q).tail

/-! ## Internal, rooted, and cross-component polynomials -/

/-- Half-rank of one indexed internal pair. -/
noncomputable def internalRank (T : PosIntTree n)
    {C : EvenComponent T} (p : InternalPair T C) : ℕ :=
  rho T p.1.1 p.1.2

/-- The internal-pair polynomial `S_C`. -/
noncomputable def internalPoly (T : PosIntTree n)
    (C : EvenComponent T) : ℕ[X] :=
  rankPoly (internalRank T : InternalPair T C → ℕ)

/-- The rooted-depth polynomial at one actual named component vertex. -/
noncomputable def rootedPoly (T : PosIntTree n)
    {C : EvenComponent T} (root : ComponentVertex T C) : ℕ[X] :=
  rankPoly (fun x : ComponentVertex T C => rho T x root)

/-- Half-rank assigned to one endpoint pair in a fixed quotient block. -/
noncomputable def crossRank (T : PosIntTree n)
    (q : QuotientComponentPair T)
    (z : ComponentVertex T q.left × ComponentVertex T q.right) : ℕ :=
  canonicalRouteShift T q +
    rho T z.1 (canonicalSourcePort T q) +
    rho T z.2 (canonicalTargetPort T q)

/-- The full multiplicity-preserving polynomial of one unordered pair of
distinct even components. -/
noncomputable def crossPoly (T : PosIntTree n)
    (q : QuotientComponentPair T) : ℕ[X] :=
  rankPoly (crossRank T q)

/-- One cross block is exactly a shifted product of the two rooted endpoint
polynomials.  Polynomial multiplication, together with `rankPoly_coeff`,
retains the full number of endpoint pairs at every repeated exponent. -/
theorem crossPoly_eq_shifted_rooted_product (T : PosIntTree n)
    (q : QuotientComponentPair T) :
    crossPoly T q =
      Polynomial.monomial (canonicalRouteShift T q) 1 *
        rootedPoly T (canonicalSourcePort T q) *
        rootedPoly T (canonicalTargetPort T q) := by
  unfold crossPoly crossRank rootedPoly
  exact rankPoly_shift_add_product
    (canonicalRouteShift T q)
    (fun x : ComponentVertex T q.left =>
      rho T x (canonicalSourcePort T q))
    (fun y : ComponentVertex T q.right =>
      rho T y (canonicalTargetPort T q))

/-- Coefficientwise shifted Cartesian-product count for one quotient block. -/
theorem crossPoly_coeff (T : PosIntTree n)
    (q : QuotientComponentPair T) (k : ℕ) :
    (crossPoly T q).coeff k =
      Fintype.card
        {z : ComponentVertex T q.left × ComponentVertex T q.right //
          canonicalRouteShift T q +
            rho T z.1 (canonicalSourcePort T q) +
            rho T z.2 (canonicalTargetPort T q) = k} := by
  exact rankPoly_coeff _ _

/-! ## Recovery of the actual global distance -/

private theorem crossIndex_endpoints_ne (T : PosIntTree n)
    (z : CrossIndex T) : z.2.1.1 ≠ z.2.2.1 := by
  intro h
  apply z.1.ne
  exact z.2.1.2.symm.trans
    ((congrArg (componentOf T) h).trans z.2.2.2)

/-- Internal half-rank is exact for the global pair recovered from the
within-component index. -/
theorem pairDist_indexToPair_internal (T : PosIntTree n)
    (z : WithinIndex T) :
    T.pairDist (indexToPair T (.inl z)) =
      2 * internalRank T z.2 := by
  exact dist_eq_two_mul_rho T z.2.1.1 z.2.1.2

/-- Cross half-rank and route parity recover the exact global pair distance. -/
theorem pairDist_indexToPair_cross (T : PosIntTree n)
    (z : CrossIndex T) :
    T.pairDist (indexToPair T (.inr z)) =
      2 * crossRank T z.1 z.2 + quotientPairParity T z.1 := by
  rw [indexToPair, T.pairDist_pairOfDistinct _ _
    (crossIndex_endpoints_ne T z)]
  have hroute := dist_eq_endpoint_rhos_routeShift T
    (canonicalRouteData T z.1).head
    (canonicalRouteData T z.1).tail
    (canonicalRouteData T z.1).isPath z.2.1 z.2.2
  have htargetComm :
      rho T
          (routeTerminal T (canonicalRouteData T z.1).tail
            (orientedBridgeOfAdj T
              (canonicalRouteData T z.1).head).targetPort)
          z.2.2 =
        rho T z.2.2
          (routeTerminal T (canonicalRouteData T z.1).tail
            (orientedBridgeOfAdj T
              (canonicalRouteData T z.1).head).targetPort) :=
    rho_comm T _ _
  rw [htargetComm] at hroute
  simp only [canonicalRouteWalk, canonicalSourcePort, canonicalTargetPort,
    canonicalRouteShift, quotientPairParity, crossRank] at hroute ⊢
  omega

/-- The rank carried by either branch of the exact pair partition. -/
noncomputable def pairIndexRank (T : PosIntTree n) :
    WithinIndex T ⊕ CrossIndex T → ℕ
  | .inl z => internalRank T z.2
  | .inr z => crossRank T z.1 z.2

/-- The parity carried by either branch of the exact pair partition. -/
noncomputable def pairIndexParity (T : PosIntTree n) :
    WithinIndex T ⊕ CrossIndex T → ℕ
  | .inl _ => 0
  | .inr z => quotientPairParity T z.1

theorem pairDist_div_two_indexToPair (T : PosIntTree n)
    (z : WithinIndex T ⊕ CrossIndex T) :
    T.pairDist (indexToPair T z) / 2 = pairIndexRank T z := by
  cases z with
  | inl z =>
      rw [pairDist_indexToPair_internal]
      simp [pairIndexRank]
  | inr z =>
      rw [pairDist_indexToPair_cross]
      have hp := quotientPairParity_lt_two T z.1
      simp only [pairIndexRank]
      omega

theorem pairDist_mod_two_indexToPair (T : PosIntTree n)
    (z : WithinIndex T ⊕ CrossIndex T) :
    T.pairDist (indexToPair T z) % 2 = pairIndexParity T z := by
  cases z with
  | inl z =>
      rw [pairDist_indexToPair_internal]
      simp [pairIndexParity]
  | inr z =>
      rw [pairDist_indexToPair_cross]
      have hp := quotientPairParity_lt_two T z.1
      simp only [pairIndexParity]
      omega

theorem pairIndexRank_vertexPairIndexEquiv (T : PosIntTree n)
    (p : VertexPair n) :
    pairIndexRank T (vertexPairIndexEquiv T p) = T.pairDist p / 2 := by
  have h := pairDist_div_two_indexToPair T (vertexPairIndexEquiv T p)
  have hinv :
      indexToPair T (vertexPairIndexEquiv T p) = p :=
    (vertexPairIndexEquiv T).left_inv p
  rw [hinv] at h
  exact h.symm

theorem pairIndexParity_vertexPairIndexEquiv (T : PosIntTree n)
    (p : VertexPair n) :
    pairIndexParity T (vertexPairIndexEquiv T p) =
      T.pairDist p % 2 := by
  have h := pairDist_mod_two_indexToPair T (vertexPairIndexEquiv T p)
  have hinv :
      indexToPair T (vertexPairIndexEquiv T p) = p :=
    (vertexPairIndexEquiv T).left_inv p
  rw [hinv] at h
  exact h.symm

/-! ## Unconditional all-pair polynomial decomposition -/

/-- The full half-rank polynomial on the actual indexed global pairs. -/
noncomputable def allHalfRankPoly (T : PosIntTree n) : ℕ[X] :=
  rankPoly (fun p : VertexPair n => T.pairDist p / 2)

/-- Before parity separation, all actual pairs split into the disjoint union
of all internal component polynomials and all distinct component-pair cross
polynomials. -/
theorem allHalfRankPoly_decomposition (T : PosIntTree n) :
    allHalfRankPoly T =
      (∑ C : EvenComponent T, internalPoly T C) +
        ∑ q : QuotientComponentPair T, crossPoly T q := by
  calc
    allHalfRankPoly T = rankPoly (pairIndexRank T) := by
      unfold allHalfRankPoly
      exact rankPoly_equiv (vertexPairIndexEquiv T)
        (fun p : VertexPair n => T.pairDist p / 2)
        (pairIndexRank T)
        (pairIndexRank_vertexPairIndexEquiv T)
    _ = rankPoly (fun z : WithinIndex T => internalRank T z.2) +
          rankPoly (fun z : CrossIndex T => crossRank T z.1 z.2) :=
      by
        have hrank :
            pairIndexRank T =
              Sum.elim
                (fun z : WithinIndex T => internalRank T z.2)
                (fun z : CrossIndex T => crossRank T z.1 z.2) := by
          funext z
          cases z <;> rfl
        rw [hrank]
        exact rankPoly_sum _ _
    _ = (∑ C : EvenComponent T, internalPoly T C) +
          ∑ q : QuotientComponentPair T, crossPoly T q := by
      rw [rankPoly_sigma, rankPoly_sigma]
      rfl

end LeechTrees.OddQuotient
