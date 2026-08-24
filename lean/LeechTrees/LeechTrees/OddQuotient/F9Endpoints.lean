import LeechTrees.OddQuotient.QuotientPolynomials

/-!
# Coefficientwise F9 endpoints

This file separates the exact indexed global pairs by distance parity, then
reindexes the two classes through `IsLeech`.  The odd half-ranks are exactly
`0, ..., O-1`, where `O = (targetN n + 1) / 2`; the even half-ranks are
exactly `1, ..., E`, where `E = targetN n / 2`.

All final statements are coefficient equalities.  No support equality is
used as a substitute for multiplicity, and no converse realization claim is
made.
-/

open scoped BigOperators Polynomial

namespace LeechTrees.OddQuotient

open LeechTrees.Foundation

variable {n : ℕ}

/-! ## Indexed odd/even pair types and quotient blocks -/

abbrev OddVertexPair (T : PosIntTree n) :=
  {p : VertexPair n // T.pairDist p % 2 = 1}

abbrev EvenVertexPair (T : PosIntTree n) :=
  {p : VertexPair n // T.pairDist p % 2 = 0}

abbrev OddQuotientComponentPair (T : PosIntTree n) :=
  {q : QuotientComponentPair T // quotientPairParity T q = 1}

abbrev EvenQuotientComponentPair (T : PosIntTree n) :=
  {q : QuotientComponentPair T // quotientPairParity T q = 0}

abbrev OddCrossIndex (T : PosIntTree n) :=
  Σ q : OddQuotientComponentPair T,
    ComponentVertex T q.1.left × ComponentVertex T q.1.right

abbrev EvenCrossIndex (T : PosIntTree n) :=
  Σ q : EvenQuotientComponentPair T,
    ComponentVertex T q.1.left × ComponentVertex T q.1.right

/-- Predicate on the exact within/cross partition selecting odd-distance
pairs.  The within branch is empty because all its physical edges are even. -/
def OddPairIndexPred (T : PosIntTree n) :
    WithinIndex T ⊕ CrossIndex T → Prop
  | .inl _ => False
  | .inr z => quotientPairParity T z.1 = 1

/-- Predicate on the exact within/cross partition selecting even-distance
pairs. -/
def EvenPairIndexPred (T : PosIntTree n) :
    WithinIndex T ⊕ CrossIndex T → Prop
  | .inl _ => True
  | .inr z => quotientPairParity T z.1 = 0

abbrev OddIndexedPair (T : PosIntTree n) :=
  {z : WithinIndex T ⊕ CrossIndex T // OddPairIndexPred T z}

abbrev EvenIndexedPair (T : PosIntTree n) :=
  {z : WithinIndex T ⊕ CrossIndex T // EvenPairIndexPred T z}

theorem pair_odd_iff_index_odd (T : PosIntTree n) (p : VertexPair n) :
    T.pairDist p % 2 = 1 ↔
      OddPairIndexPred T (vertexPairIndexEquiv T p) := by
  rw [← pairIndexParity_vertexPairIndexEquiv T p]
  cases vertexPairIndexEquiv T p <;>
    simp [OddPairIndexPred, pairIndexParity]

theorem pair_even_iff_index_even (T : PosIntTree n) (p : VertexPair n) :
    T.pairDist p % 2 = 0 ↔
      EvenPairIndexPred T (vertexPairIndexEquiv T p) := by
  rw [← pairIndexParity_vertexPairIndexEquiv T p]
  cases vertexPairIndexEquiv T p <;>
    simp [EvenPairIndexPred, pairIndexParity]

/-- Odd actual pairs transported into the exact indexed component
partition. -/
noncomputable def oddPairIndexEquiv (T : PosIntTree n) :
    OddVertexPair T ≃ OddIndexedPair T :=
  Equiv.subtypeEquiv (vertexPairIndexEquiv T)
    (pair_odd_iff_index_odd T)

/-- Even actual pairs transported into the exact indexed component
partition. -/
noncomputable def evenPairIndexEquiv (T : PosIntTree n) :
    EvenVertexPair T ≃ EvenIndexedPair T :=
  Equiv.subtypeEquiv (vertexPairIndexEquiv T)
    (pair_even_iff_index_even T)

/-- Removing the impossible internal odd branch and moving the parity
predicate onto the sigma base gives precisely the odd quotient blocks. -/
noncomputable def oddIndexedBlockEquiv (T : PosIntTree n) :
    OddIndexedPair T ≃ OddCrossIndex T :=
  calc
    OddIndexedPair T ≃
        {_z : WithinIndex T // False} ⊕
          {z : CrossIndex T // quotientPairParity T z.1 = 1} :=
      Equiv.subtypeSum
    _ ≃ {z : CrossIndex T // quotientPairParity T z.1 = 1} :=
      Equiv.emptySum _ _
    _ ≃ OddCrossIndex T :=
      Equiv.subtypeSigmaEquiv
        (fun q : QuotientComponentPair T =>
          ComponentVertex T q.left × ComponentVertex T q.right)
        (fun q => quotientPairParity T q = 1)

/-- The even indexed pairs consist of every internal block plus the
even-length cross blocks. -/
noncomputable def evenIndexedBlockEquiv (T : PosIntTree n) :
    EvenIndexedPair T ≃ WithinIndex T ⊕ EvenCrossIndex T :=
  calc
    EvenIndexedPair T ≃
        {_z : WithinIndex T // True} ⊕
          {z : CrossIndex T // quotientPairParity T z.1 = 0} :=
      Equiv.subtypeSum
    _ ≃ WithinIndex T ⊕
          {z : CrossIndex T // quotientPairParity T z.1 = 0} :=
      Equiv.sumCongr (Equiv.subtypeUnivEquiv fun _ => True.intro)
        (Equiv.refl _)
    _ ≃ WithinIndex T ⊕ EvenCrossIndex T :=
      Equiv.sumCongr (Equiv.refl _)
        (Equiv.subtypeSigmaEquiv
          (fun q : QuotientComponentPair T =>
            ComponentVertex T q.left × ComponentVertex T q.right)
          (fun q => quotientPairParity T q = 0))

/-- Exact odd-pair to odd quotient-block equivalence. -/
noncomputable def oddPairBlockEquiv (T : PosIntTree n) :
    OddVertexPair T ≃ OddCrossIndex T :=
  (oddPairIndexEquiv T).trans (oddIndexedBlockEquiv T)

/-- Exact even-pair to internal-or-even-cross-block equivalence. -/
noncomputable def evenPairBlockEquiv (T : PosIntTree n) :
    EvenVertexPair T ≃ WithinIndex T ⊕ EvenCrossIndex T :=
  (evenPairIndexEquiv T).trans (evenIndexedBlockEquiv T)

/-! ## Odd/even half-rank polynomial decompositions -/

noncomputable def oddHalfRankPoly (T : PosIntTree n) : ℕ[X] :=
  rankPoly (fun p : OddVertexPair T => T.pairDist p.1 / 2)

noncomputable def evenHalfRankPoly (T : PosIntTree n) : ℕ[X] :=
  rankPoly (fun p : EvenVertexPair T => T.pairDist p.1 / 2)

noncomputable def oddBlockRank (T : PosIntTree n)
    (z : OddCrossIndex T) : ℕ :=
  crossRank T z.1.1 z.2

noncomputable def evenBlockRank (T : PosIntTree n) :
    WithinIndex T ⊕ EvenCrossIndex T → ℕ
  | .inl z => internalRank T z.2
  | .inr z => crossRank T z.1.1 z.2

theorem oddPairBlockEquiv_rank (T : PosIntTree n)
    (p : OddVertexPair T) :
    oddBlockRank T (oddPairBlockEquiv T p) =
      T.pairDist p.1 / 2 := by
  calc
    oddBlockRank T (oddPairBlockEquiv T p) =
        pairIndexRank T (oddPairIndexEquiv T p).1 := by
      change oddBlockRank T
          (oddIndexedBlockEquiv T (oddPairIndexEquiv T p)) =
        pairIndexRank T (oddPairIndexEquiv T p).1
      generalize hy : oddPairIndexEquiv T p = y
      rcases y with ⟨z, hz⟩
      cases z with
      | inl _ => exact False.elim hz
      | inr _ => rfl
    _ = T.pairDist p.1 / 2 := by
      change pairIndexRank T (vertexPairIndexEquiv T p.1) = _
      exact pairIndexRank_vertexPairIndexEquiv T p.1

theorem evenPairBlockEquiv_rank (T : PosIntTree n)
    (p : EvenVertexPair T) :
    evenBlockRank T (evenPairBlockEquiv T p) =
      T.pairDist p.1 / 2 := by
  have hrank := pairIndexRank_vertexPairIndexEquiv T p.1
  generalize hz : vertexPairIndexEquiv T p.1 = z at hrank
  cases z with
  | inl z =>
      simpa [evenPairBlockEquiv, evenPairIndexEquiv,
        evenIndexedBlockEquiv, evenBlockRank, pairIndexRank,
        Equiv.trans_apply, hz] using hrank
  | inr z =>
      simpa [evenPairBlockEquiv, evenPairIndexEquiv,
        evenIndexedBlockEquiv, evenBlockRank, pairIndexRank,
        Equiv.trans_apply, hz] using hrank

/-- Unconditional coefficient-preserving odd quotient decomposition. -/
theorem oddHalfRankPoly_decomposition (T : PosIntTree n) :
    oddHalfRankPoly T =
      ∑ q : OddQuotientComponentPair T, crossPoly T q.1 := by
  calc
    oddHalfRankPoly T = rankPoly (oddBlockRank T) := by
      unfold oddHalfRankPoly
      exact rankPoly_equiv (oddPairBlockEquiv T)
        (fun p : OddVertexPair T => T.pairDist p.1 / 2)
        (oddBlockRank T) (oddPairBlockEquiv_rank T)
    _ = ∑ q : OddQuotientComponentPair T, crossPoly T q.1 := by
      rw [rankPoly_sigma]
      rfl

/-- Unconditional coefficient-preserving even quotient decomposition. -/
theorem evenHalfRankPoly_decomposition (T : PosIntTree n) :
    evenHalfRankPoly T =
      (∑ C : EvenComponent T, internalPoly T C) +
        ∑ q : EvenQuotientComponentPair T, crossPoly T q.1 := by
  calc
    evenHalfRankPoly T = rankPoly (evenBlockRank T) := by
      unfold evenHalfRankPoly
      exact rankPoly_equiv (evenPairBlockEquiv T)
        (fun p : EvenVertexPair T => T.pairDist p.1 / 2)
        (evenBlockRank T) (evenPairBlockEquiv_rank T)
    _ = rankPoly (fun z : WithinIndex T => internalRank T z.2) +
          rankPoly (fun z : EvenCrossIndex T => crossRank T z.1.1 z.2) :=
      by
        have hrank :
            evenBlockRank T =
              Sum.elim
                (fun z : WithinIndex T => internalRank T z.2)
                (fun z : EvenCrossIndex T => crossRank T z.1.1 z.2) := by
          funext z
          cases z <;> rfl
        rw [hrank]
        exact rankPoly_sum _ _
    _ = (∑ C : EvenComponent T, internalPoly T C) +
          ∑ q : EvenQuotientComponentPair T, crossPoly T q.1 := by
      rw [rankPoly_sigma, rankPoly_sigma]
      rfl

/-! ## Exact `IsLeech` reindexing of the target interval -/

/-- Odd target distances, still carrying their membership in the full
positive target interval. -/
abbrev OddTargetDistance (N : ℕ) :=
  {d : {k : ℕ // k ∈ Finset.Icc 1 N} // d.1 % 2 = 1}

/-- Even target distances, still carrying their membership in the full
positive target interval. -/
abbrev EvenTargetDistance (N : ℕ) :=
  {d : {k : ℕ // k ∈ Finset.Icc 1 N} // d.1 % 2 = 0}

/-- Odd distances `1,3,...` reindexed by their exact half-ranks
`0,...,(N+1)/2-1`. -/
def oddTargetHalfEquiv (N : ℕ) :
    OddTargetDistance N ≃ Fin ((N + 1) / 2) where
  toFun d := ⟨d.1.1 / 2, by
    have hmem := Finset.mem_Icc.mp d.1.2
    omega⟩
  invFun i :=
    ⟨⟨2 * i.1 + 1, by
      rw [Finset.mem_Icc]
      have hi := i.isLt
      constructor <;> omega⟩, by
        change (2 * i.1 + 1) % 2 = 1
        omega⟩
  left_inv := by
    intro d
    apply Subtype.ext
    apply Subtype.ext
    change 2 * (d.1.1 / 2) + 1 = d.1.1
    have hpar := d.2
    omega
  right_inv := by
    intro i
    apply Fin.ext
    change (2 * i.1 + 1) / 2 = i.1
    omega

/-- Even positive distances `2,4,...` reindexed by their exact half-ranks
`1,...,N/2`. -/
def evenTargetHalfEquiv (N : ℕ) :
    EvenTargetDistance N ≃ {k : ℕ // k ∈ Finset.Icc 1 (N / 2)} where
  toFun d := ⟨d.1.1 / 2, by
    rw [Finset.mem_Icc]
    have hmem := Finset.mem_Icc.mp d.1.2
    omega⟩
  invFun k :=
    ⟨⟨2 * k.1, by
      have hk := k.2
      rw [Finset.mem_Icc] at hk ⊢
      omega⟩, by
        change (2 * k.1) % 2 = 0
        omega⟩
  left_inv := by
    intro d
    apply Subtype.ext
    apply Subtype.ext
    change 2 * (d.1.1 / 2) = d.1.1
    have hpar := d.2
    omega
  right_inv := by
    intro k
    apply Subtype.ext
    change (2 * k.1) / 2 = k.1
    omega

/-- Restriction of the full indexed Leech spectrum to its even distances. -/
noncomputable def IsLeech.evenSpectrumEquiv {T : PosIntTree n}
    (hL : IsLeech T) :
    EvenVertexPair T ≃ EvenTargetDistance (targetN n) :=
  Equiv.subtypeEquiv hL.spectrumEquiv (fun _ => Iff.rfl)

/-- Actual odd pairs reindexed by exactly `Fin O`. -/
noncomputable def IsLeech.oddHalfRankEquiv {T : PosIntTree n}
    (hL : IsLeech T) :
    OddVertexPair T ≃ Fin ((targetN n + 1) / 2) :=
  hL.oddSpectrumEquiv.trans (oddTargetHalfEquiv (targetN n))

/-- Actual even pairs reindexed by exactly the positive interval
`1,...,E`. -/
noncomputable def IsLeech.evenHalfRankEquiv {T : PosIntTree n}
    (hL : IsLeech T) :
    EvenVertexPair T ≃
      {k : ℕ // k ∈ Finset.Icc 1 (targetN n / 2)} :=
  (LeechTrees.OddQuotient.IsLeech.evenSpectrumEquiv hL).trans
    (evenTargetHalfEquiv (targetN n))

@[simp] theorem IsLeech.oddHalfRankEquiv_val {T : PosIntTree n}
    (hL : IsLeech T) (p : OddVertexPair T) :
    ((LeechTrees.OddQuotient.IsLeech.oddHalfRankEquiv hL p :
        Fin ((targetN n + 1) / 2)) : ℕ) =
      T.pairDist p.1 / 2 := rfl

@[simp] theorem IsLeech.evenHalfRankEquiv_val {T : PosIntTree n}
    (hL : IsLeech T) (p : EvenVertexPair T) :
    (LeechTrees.OddQuotient.IsLeech.evenHalfRankEquiv hL p).1 =
      T.pairDist p.1 / 2 := rfl

noncomputable local instance targetIntervalFintype (M : ℕ) :
    Fintype {k : ℕ // k ∈ Finset.Icc 1 M} :=
  Fintype.ofFinite _

noncomputable def oddTargetHalfRankPoly (N : ℕ) : ℕ[X] :=
  rankPoly (fun k : Fin ((N + 1) / 2) => (k : ℕ))

noncomputable def evenTargetHalfRankPoly (N : ℕ) : ℕ[X] := by
  letI : Fintype {k : ℕ // k ∈ Finset.Icc 1 (N / 2)} :=
    Fintype.ofFinite _
  exact rankPoly (fun k : {k : ℕ // k ∈ Finset.Icc 1 (N / 2)} => k.1)

private theorem card_fin_value_fibre (m k : ℕ) :
    Fintype.card {i : Fin m // (i : ℕ) = k} =
      if k < m then 1 else 0 := by
  classical
  by_cases hk : k < m
  · rw [if_pos hk]
    let target : Fin m := ⟨k, hk⟩
    calc
      Fintype.card {i : Fin m // (i : ℕ) = k} =
          Fintype.card {i : Fin m // i = target} := by
        apply Fintype.card_congr
        exact Equiv.subtypeEquivRight fun i => by
          constructor
          · intro h
            apply Fin.ext
            exact h
          · intro h
            subst i
            rfl
      _ = 1 := Fintype.card_subtype_eq target
  · rw [if_neg hk, Fintype.card_eq_zero_iff]
    exact ⟨fun i => hk (by
      rw [← i.2]
      exact i.1.isLt)⟩

private theorem card_finset_value_fibre (s : Finset ℕ) (k : ℕ) :
    Fintype.card {i : {a : ℕ // a ∈ s} // i.1 = k} =
      if k ∈ s then 1 else 0 := by
  classical
  by_cases hk : k ∈ s
  · rw [if_pos hk]
    let target : {a : ℕ // a ∈ s} := ⟨k, hk⟩
    calc
      Fintype.card {i : {a : ℕ // a ∈ s} // i.1 = k} =
          Fintype.card {i : {a : ℕ // a ∈ s} // i = target} := by
        apply Fintype.card_congr
        exact Equiv.subtypeEquivRight fun i => by
          constructor
          · intro h
            apply Subtype.ext
            exact h
          · intro h
            subst i
            rfl
      _ = 1 := Fintype.card_subtype_eq target
  · rw [if_neg hk, Fintype.card_eq_zero_iff]
    exact ⟨fun i => hk (by
      rw [← i.2]
      exact i.1.2)⟩

theorem oddHalfRankPoly_eq_target {T : PosIntTree n}
    (hL : IsLeech T) :
    oddHalfRankPoly T = oddTargetHalfRankPoly (targetN n) := by
  unfold oddHalfRankPoly oddTargetHalfRankPoly
  exact rankPoly_equiv
    (LeechTrees.OddQuotient.IsLeech.oddHalfRankEquiv hL) _ _
    (LeechTrees.OddQuotient.IsLeech.oddHalfRankEquiv_val hL)

theorem evenHalfRankPoly_eq_target {T : PosIntTree n}
    (hL : IsLeech T) :
    evenHalfRankPoly T = evenTargetHalfRankPoly (targetN n) := by
  letI : Fintype
      {k : ℕ // k ∈ Finset.Icc 1 (targetN n / 2)} :=
    Fintype.ofFinite _
  unfold evenHalfRankPoly evenTargetHalfRankPoly
  exact rankPoly_equiv
    (LeechTrees.OddQuotient.IsLeech.evenHalfRankEquiv hL) _ _
    (LeechTrees.OddQuotient.IsLeech.evenHalfRankEquiv_val hL)

theorem oddTargetHalfRankPoly_coeff (N k : ℕ) :
    (oddTargetHalfRankPoly N).coeff k =
      if k < (N + 1) / 2 then 1 else 0 := by
  unfold oddTargetHalfRankPoly
  rw [rankPoly_coeff]
  exact card_fin_value_fibre _ _

theorem evenTargetHalfRankPoly_coeff (N k : ℕ) :
    (evenTargetHalfRankPoly N).coeff k =
      if k ∈ Finset.Icc 1 (N / 2) then 1 else 0 := by
  letI : Fintype {a : ℕ // a ∈ Finset.Icc 1 (N / 2)} :=
    Fintype.ofFinite _
  unfold evenTargetHalfRankPoly
  rw [rankPoly_coeff]
  by_cases hk : k ∈ Finset.Icc 1 (N / 2)
  · rw [if_pos hk]
    let target : {a : ℕ // a ∈ Finset.Icc 1 (N / 2)} := ⟨k, hk⟩
    calc
      Fintype.card
          {i : {a : ℕ // a ∈ Finset.Icc 1 (N / 2)} // i.1 = k} =
          Fintype.card
            {i : {a : ℕ // a ∈ Finset.Icc 1 (N / 2)} //
              i = target} := by
        apply Fintype.card_congr
        exact Equiv.subtypeEquivRight fun i => by
          constructor
          · intro h
            apply Subtype.ext
            exact h
          · intro h
            subst i
            rfl
      _ = 1 := Fintype.card_subtype_eq target
  · rw [if_neg hk, Fintype.card_eq_zero_iff]
    exact ⟨fun i => hk (by
      rw [← i.2]
      exact i.1.2)⟩

/-! ## Paper-facing F9 identities -/

/-- F9 odd polynomial identity: every odd half-rank occurs once, and no
other coefficient occurs. -/
theorem F9_odd_polynomial {T : PosIntTree n} (hL : IsLeech T) :
    (∑ q : OddQuotientComponentPair T, crossPoly T q.1) =
      oddTargetHalfRankPoly (targetN n) := by
  rw [← oddHalfRankPoly_decomposition T]
  exact oddHalfRankPoly_eq_target hL

/-- F9 even polynomial identity: internal pairs and positive-even quotient
routes jointly realize each even half-rank once. -/
theorem F9_even_polynomial {T : PosIntTree n} (hL : IsLeech T) :
    (∑ C : EvenComponent T, internalPoly T C) +
        (∑ q : EvenQuotientComponentPair T, crossPoly T q.1) =
      evenTargetHalfRankPoly (targetN n) := by
  rw [← evenHalfRankPoly_decomposition T]
  exact evenHalfRankPoly_eq_target hL

/-- Explicit coefficientwise odd endpoint. -/
theorem F9_odd_coefficient {T : PosIntTree n} (hL : IsLeech T) (k : ℕ) :
    (∑ q : OddQuotientComponentPair T, crossPoly T q.1).coeff k =
      if k < (targetN n + 1) / 2 then 1 else 0 := by
  rw [F9_odd_polynomial hL]
  exact oddTargetHalfRankPoly_coeff _ _

/-- Explicit coefficientwise even endpoint. -/
theorem F9_even_coefficient {T : PosIntTree n} (hL : IsLeech T) (k : ℕ) :
    ((∑ C : EvenComponent T, internalPoly T C) +
        ∑ q : EvenQuotientComponentPair T, crossPoly T q.1).coeff k =
      if k ∈ Finset.Icc 1 (targetN n / 2) then 1 else 0 := by
  rw [F9_even_polynomial hL]
  exact evenTargetHalfRankPoly_coeff _ _

/-- One paper-facing conjunction collecting the two coefficientwise F9
identities.  It contains no lift or realization converse. -/
theorem F9_coefficientwise_odd_quotient {T : PosIntTree n}
    (hL : IsLeech T) :
    (∀ k : ℕ,
      (∑ q : OddQuotientComponentPair T, crossPoly T q.1).coeff k =
        if k < (targetN n + 1) / 2 then 1 else 0) ∧
    (∀ k : ℕ,
      ((∑ C : EvenComponent T, internalPoly T C) +
          ∑ q : EvenQuotientComponentPair T, crossPoly T q.1).coeff k =
        if k ∈ Finset.Icc 1 (targetN n / 2) then 1 else 0) := by
  exact ⟨F9_odd_coefficient hL, F9_even_coefficient hL⟩

end LeechTrees.OddQuotient
