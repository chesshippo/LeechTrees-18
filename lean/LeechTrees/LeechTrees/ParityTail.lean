import LeechTrees.CombinatorialCore

/-!
# Parity-resolved path moments and tail arithmetic

This module is an isolated proof lane for ledger claims T8--T10b.  It proves
the finite algebra, spacing, saturation, and concrete order-18 arithmetic
without assuming existence of a Leech tree or any computational cut cap.

The graph-theoretic wrapper is deliberately separate: the declarations below
make the indexed path and outer-component interfaces explicit, so a later
wrapper must derive them from the common `PosIntTree` / `IsLeech` foundation.
-/

open scoped BigOperators

namespace LeechTrees.ParityTail

/-! ## Unordered pair/triple sums along a fixed edge enumeration -/

section ListSums

variable {α R : Type*} [CommRing R]

/-- Sum a function over all pairs in a list, with the first list occurrence
preceding the second.  For a duplicate-free edge enumeration this is the
usual unordered `e < f` sum. -/
def pairSum : List α → (α → α → R) → R
  | [], _ => 0
  | a :: l, f => (l.map (f a)).sum + pairSum l f

/-- Sum a function over all triples in a list, in occurrence order. -/
def tripleSum : List α → (α → α → α → R) → R
  | [], _ => 0
  | a :: l, f => pairSum l (f a) + tripleSum l f

@[simp] theorem pairSum_nil (f : α → α → R) : pairSum [] f = 0 := rfl

@[simp] theorem pairSum_cons (a : α) (l : List α) (f : α → α → R) :
    pairSum (a :: l) f = (l.map (f a)).sum + pairSum l f := rfl

@[simp] theorem tripleSum_nil (f : α → α → α → R) :
    tripleSum [] f = 0 := rfl

@[simp] theorem tripleSum_cons (a : α) (l : List α)
    (f : α → α → α → R) :
    tripleSum (a :: l) f = pairSum l (f a) + tripleSum l f := rfl

/-- Pointwise congruence for `pairSum`. -/
theorem pairSum_congr (l : List α) {f g : α → α → R}
    (h : ∀ a b, f a b = g a b) : pairSum l f = pairSum l g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [pairSum_cons, pairSum_cons, ih]
      congr 1
      exact congrArg List.sum (List.map_congr_left fun b _ => h a b)

private theorem sum_map_mul_left (c : R) (l : List α) (f : α → R) :
    (l.map (fun a => c * f a)).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, mul_add]

private theorem sum_map_mul_right (c : R) (l : List α) (f : α → R) :
    (l.map (fun a => f a * c)).sum = (l.map f).sum * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, add_mul]

private theorem sum_map_add (l : List α) (f g : α → R) :
    (l.map (fun a => f a + g a)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      abel

private theorem pairSum_mul_left (c : R) (l : List α) (f : α → α → R) :
    pairSum l (fun a b => c * f a b) = c * pairSum l f := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [pairSum_cons, pairSum_cons, ih, sum_map_mul_left]
      ring

/-- Quadratic multinomial expansion grouped into singleton and unordered-pair
terms. -/
theorem list_sum_sq (l : List α) (x : α → R) :
    (l.map x).sum ^ 2 =
      (l.map (fun e => x e ^ 2)).sum +
        2 * pairSum l (fun e f => x e * x f) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
        pairSum_cons]
      calc
        (x a + (l.map x).sum) ^ 2 =
            x a ^ 2 + (l.map x).sum ^ 2 + 2 * x a * (l.map x).sum := by ring
        _ = x a ^ 2 +
              ((l.map (fun e => x e ^ 2)).sum +
                2 * pairSum l (fun e f => x e * x f)) +
              2 * x a * (l.map x).sum := by rw [ih]
        _ = x a ^ 2 + (l.map (fun e => x e ^ 2)).sum +
              2 * ((l.map (fun f => x a * x f)).sum +
                pairSum l (fun e f => x e * x f)) := by
          rw [sum_map_mul_left]
          ring

/-- Cubic multinomial expansion grouped into singleton, unordered-pair, and
unordered-triple terms.  The coefficients are exactly `1`, `3`, and `6`;
the pair summand contains the two exponent placements. -/
theorem list_sum_cube (l : List α) (x : α → R) :
    (l.map x).sum ^ 3 =
      (l.map (fun e => x e ^ 3)).sum +
        3 * pairSum l (fun e f => x e ^ 2 * x f + x e * x f ^ 2) +
        6 * tripleSum l (fun e f g => x e * x f * x g) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have hsquare := list_sum_sq l x
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
        pairSum_cons, tripleSum_cons]
      have hsqLeft :
          (l.map (fun f => x a ^ 2 * x f)).sum =
            x a ^ 2 * (l.map x).sum := sum_map_mul_left _ _ _
      have hsqRight :
          (l.map (fun f => x a * x f ^ 2)).sum =
            x a * (l.map (fun f => x f ^ 2)).sum := sum_map_mul_left _ _ _
      have htriple :
          pairSum l (fun e f => x a * x e * x f) =
            x a * pairSum l (fun e f => x e * x f) := by
        calc
          pairSum l (fun e f => x a * x e * x f) =
              pairSum l (fun e f => x a * (x e * x f)) := by
            apply pairSum_congr l
            intro e f
            ring
          _ = x a * pairSum l (fun e f => x e * x f) :=
            pairSum_mul_left _ _ _
      calc
        (x a + (l.map x).sum) ^ 3 =
            x a ^ 3 + (l.map x).sum ^ 3 +
              3 * x a ^ 2 * (l.map x).sum +
              3 * x a * (l.map x).sum ^ 2 := by ring
        _ = x a ^ 3 +
              ((l.map (fun e => x e ^ 3)).sum +
                3 * pairSum l
                  (fun e f => x e ^ 2 * x f + x e * x f ^ 2) +
                6 * tripleSum l (fun e f g => x e * x f * x g)) +
              3 * x a ^ 2 * (l.map x).sum +
              3 * x a * ((l.map (fun e => x e ^ 2)).sum +
                2 * pairSum l (fun e f => x e * x f)) := by
          rw [ih, hsquare]
        _ = x a ^ 3 + (l.map (fun e => x e ^ 3)).sum +
              3 * ((l.map
                (fun f => x a ^ 2 * x f + x a * x f ^ 2)).sum +
                pairSum l
                  (fun e f => x e ^ 2 * x f + x e * x f ^ 2)) +
              6 * (pairSum l (fun f g => x a * x f * x g) +
                tripleSum l (fun e f g => x e * x f * x g)) := by
          rw [sum_map_add]
          rw [hsqLeft, hsqRight, htriple]
          ring

/-- Pointwise congruence for `tripleSum`. -/
theorem tripleSum_congr (l : List α) {f g : α → α → α → R}
    (h : ∀ a b c, f a b c = g a b c) : tripleSum l f = tripleSum l g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [tripleSum_cons, tripleSum_cons, ih]
      congr 1
      exact pairSum_congr l (fun b c => h a b c)

/-- Congruence for a mapped list sum when equality is known on the list. -/
theorem sum_map_congr (l : List α) {f g : α → R}
    (h : ∀ a ∈ l, f a = g a) : (l.map f).sum = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [h a (by simp), ih]
      intro b hb
      exact h b (by simp [hb])

end ListSums

/-! ## Indexed 0/1 path incidence and parity-restricted moments -/

section IndexedMoments

variable {Pair Edge : Type*}

/-- The sum of the edge weights selected by a `0/1` incidence row. -/
def pathValue (edges : List Edge) (weight : Edge → ℤ)
    (uses : Pair → Edge → ℤ) (p : Pair) : ℤ :=
  (edges.map (fun e => weight e * uses p e)).sum

/-- Number (cast to `ℤ`) of selected pair rows using one edge. -/
def singletonCoefficient (pairs : Finset Pair) (uses : Pair → Edge → ℤ)
    (e : Edge) : ℤ :=
  ∑ p ∈ pairs, uses p e

/-- Number (cast to `ℤ`) of selected pair rows using two specified edges. -/
def pairCoefficient (pairs : Finset Pair) (uses : Pair → Edge → ℤ)
    (e f : Edge) : ℤ :=
  ∑ p ∈ pairs, uses p e * uses p f

/-- Number (cast to `ℤ`) of selected pair rows using three specified edges. -/
def tripleCoefficient (pairs : Finset Pair) (uses : Pair → Edge → ℤ)
    (e f g : Edge) : ℤ :=
  ∑ p ∈ pairs, uses p e * uses p f * uses p g

private theorem sum_pairs_list (pairs : Finset Pair) (l : List Edge)
    (f : Pair → Edge → ℤ) :
    (∑ p ∈ pairs, (l.map (f p)).sum) =
      (l.map (fun e => ∑ p ∈ pairs, f p e)).sum := by
  induction l with
  | nil => simp
  | cons e l ih => simp [ih, Finset.sum_add_distrib]

private theorem sum_pairs_pairSum (pairs : Finset Pair) (l : List Edge)
    (f : Pair → Edge → Edge → ℤ) :
    (∑ p ∈ pairs, pairSum l (f p)) =
      pairSum l (fun e g => ∑ p ∈ pairs, f p e g) := by
  induction l with
  | nil => simp
  | cons e l ih =>
      simp only [pairSum_cons, Finset.sum_add_distrib, ih]
      rw [sum_pairs_list]

private theorem sum_pairs_tripleSum (pairs : Finset Pair) (l : List Edge)
    (f : Pair → Edge → Edge → Edge → ℤ) :
    (∑ p ∈ pairs, tripleSum l (f p)) =
      tripleSum l (fun e g h => ∑ p ∈ pairs, f p e g h) := by
  induction l with
  | nil => simp
  | cons e l ih =>
      simp only [tripleSum_cons, Finset.sum_add_distrib, ih]
      rw [sum_pairs_pairSum]

private theorem zero_one_sq {z : ℤ} (hz : z = 0 ∨ z = 1) : z ^ 2 = z := by
  rcases hz with rfl | rfl <;> norm_num

private theorem zero_one_cube {z : ℤ} (hz : z = 0 ∨ z = 1) : z ^ 3 = z := by
  rcases hz with rfl | rfl <;> norm_num

/-- Parity-restricted first path moment.  The finset `pairs` may be the even
or odd pair block (or any other selected block). -/
theorem first_path_moment
    (edges : List Edge) (weight : Edge → ℤ) (uses : Pair → Edge → ℤ)
    (pairs : Finset Pair) :
    (∑ p ∈ pairs, pathValue edges weight uses p) =
      (edges.map (fun e => singletonCoefficient pairs uses e * weight e)).sum := by
  unfold pathValue singletonCoefficient
  rw [sum_pairs_list]
  apply sum_map_congr
  intro e he
  rw [Finset.sum_mul]
  ring_nf

/-- Parity-restricted second path moment with coefficients `1` and `2`. -/
theorem second_path_moment [DecidableEq Pair]
    (edges : List Edge) (weight : Edge → ℤ) (uses : Pair → Edge → ℤ)
    (pairs : Finset Pair)
    (zero_one : ∀ p ∈ pairs, ∀ e, uses p e = 0 ∨ uses p e = 1) :
    (∑ p ∈ pairs, pathValue edges weight uses p ^ 2) =
      (edges.map (fun e => singletonCoefficient pairs uses e * weight e ^ 2)).sum +
        2 * pairSum edges
          (fun e f => pairCoefficient pairs uses e f * weight e * weight f) := by
  have hdiag :
      (edges.map (fun e => ∑ p ∈ pairs, (weight e * uses p e) ^ 2)).sum =
        (edges.map
          (fun e => singletonCoefficient pairs uses e * weight e ^ 2)).sum := by
    apply sum_map_congr
    intro e he
    unfold singletonCoefficient
    calc
      (∑ p ∈ pairs, (weight e * uses p e) ^ 2) =
          ∑ p ∈ pairs, uses p e * weight e ^ 2 := by
        apply Finset.sum_congr rfl
        intro p hp
        have hu := zero_one p hp e
        rw [mul_pow, zero_one_sq hu]
        ring
      _ = (∑ p ∈ pairs, uses p e) * weight e ^ 2 := by
        rw [Finset.sum_mul]
  have hpairs :
      pairSum edges (fun e f =>
        ∑ p ∈ pairs, weight e * uses p e * (weight f * uses p f)) =
      pairSum edges (fun e f =>
        pairCoefficient pairs uses e f * weight e * weight f) := by
    apply pairSum_congr edges
    intro e f
    unfold pairCoefficient
    calc
      (∑ p ∈ pairs, weight e * uses p e * (weight f * uses p f)) =
          ∑ p ∈ pairs, (uses p e * uses p f) * (weight e * weight f) := by
        apply Finset.sum_congr rfl
        intro p hp
        ring
      _ = (∑ p ∈ pairs, uses p e * uses p f) *
          (weight e * weight f) := by rw [Finset.sum_mul]
      _ = (∑ p ∈ pairs, uses p e * uses p f) * weight e * weight f := by
        ring
  simp_rw [pathValue, list_sum_sq]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_pairs_list,
    sum_pairs_pairSum, hdiag, hpairs]

/-- Parity-restricted third path moment with coefficients `1`, `3`, and `6`.
The pair term contains both exponent placements, exactly as in T8. -/
theorem third_path_moment [DecidableEq Pair]
    (edges : List Edge) (weight : Edge → ℤ) (uses : Pair → Edge → ℤ)
    (pairs : Finset Pair)
    (zero_one : ∀ p ∈ pairs, ∀ e, uses p e = 0 ∨ uses p e = 1) :
    (∑ p ∈ pairs, pathValue edges weight uses p ^ 3) =
      (edges.map (fun e => singletonCoefficient pairs uses e * weight e ^ 3)).sum +
        3 * pairSum edges (fun e f =>
          pairCoefficient pairs uses e f *
            (weight e ^ 2 * weight f + weight e * weight f ^ 2)) +
        6 * tripleSum edges (fun e f g =>
          tripleCoefficient pairs uses e f g * weight e * weight f * weight g) := by
  have hdiag :
      (edges.map (fun e => ∑ p ∈ pairs, (weight e * uses p e) ^ 3)).sum =
        (edges.map
          (fun e => singletonCoefficient pairs uses e * weight e ^ 3)).sum := by
    apply sum_map_congr
    intro e he
    unfold singletonCoefficient
    calc
      (∑ p ∈ pairs, (weight e * uses p e) ^ 3) =
          ∑ p ∈ pairs, uses p e * weight e ^ 3 := by
        apply Finset.sum_congr rfl
        intro p hp
        have hu := zero_one p hp e
        rw [mul_pow, zero_one_cube hu]
        ring
      _ = (∑ p ∈ pairs, uses p e) * weight e ^ 3 := by
        rw [Finset.sum_mul]
  have hpairs :
      pairSum edges (fun e f => ∑ p ∈ pairs,
        ((weight e * uses p e) ^ 2 * (weight f * uses p f) +
          weight e * uses p e * (weight f * uses p f) ^ 2)) =
      pairSum edges (fun e f =>
        pairCoefficient pairs uses e f *
          (weight e ^ 2 * weight f + weight e * weight f ^ 2)) := by
    apply pairSum_congr edges
    intro e f
    unfold pairCoefficient
    calc
      (∑ p ∈ pairs,
          ((weight e * uses p e) ^ 2 * (weight f * uses p f) +
            weight e * uses p e * (weight f * uses p f) ^ 2)) =
          ∑ p ∈ pairs, (uses p e * uses p f) *
            (weight e ^ 2 * weight f + weight e * weight f ^ 2) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hue := zero_one p hp e
        have huf := zero_one p hp f
        rw [mul_pow, mul_pow, zero_one_sq hue, zero_one_sq huf]
        ring
      _ = (∑ p ∈ pairs, uses p e * uses p f) *
          (weight e ^ 2 * weight f + weight e * weight f ^ 2) := by
        rw [Finset.sum_mul]
  have htriples :
      tripleSum edges (fun e f g => ∑ p ∈ pairs,
        weight e * uses p e * (weight f * uses p f) *
          (weight g * uses p g)) =
      tripleSum edges (fun e f g =>
        tripleCoefficient pairs uses e f g * weight e * weight f * weight g) := by
    apply tripleSum_congr edges
    intro e f g
    unfold tripleCoefficient
    calc
      (∑ p ∈ pairs, weight e * uses p e * (weight f * uses p f) *
          (weight g * uses p g)) =
          ∑ p ∈ pairs, (uses p e * uses p f * uses p g) *
            (weight e * weight f * weight g) := by
        apply Finset.sum_congr rfl
        intro p hp
        ring
      _ = (∑ p ∈ pairs, uses p e * uses p f * uses p g) *
          (weight e * weight f * weight g) := by rw [Finset.sum_mul]
      _ = (∑ p ∈ pairs, uses p e * uses p f * uses p g) *
          weight e * weight f * weight g := by ring
  simp_rw [pathValue, list_sum_cube]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, sum_pairs_list, sum_pairs_pairSum,
    sum_pairs_tripleSum, hdiag, hpairs, htriples]

end IndexedMoments

/-! ## Signed outer-component factorization -/

section SignedOuter

variable {Vertex : Type*}

/-- Signed mass of a finite vertex set. -/
def signedMass (sign : Vertex → ℤ) (s : Finset Vertex) : ℤ :=
  ∑ v ∈ s, sign v

/-- The uniquely oriented Cartesian endpoint block between two disjoint outer
components.  In the tree adapter, this is identified with the unordered pairs
whose path contains the selected nonempty collinear edge set. -/
def outerPairs (left right : Finset Vertex) : Finset (Vertex × Vertex) :=
  left ×ˢ right

/-- Signed endpoint coefficient of an oriented endpoint block. -/
def signedPairCoefficient (sign : Vertex → ℤ)
    (pairs : Finset (Vertex × Vertex)) : ℤ :=
  ∑ uv ∈ pairs, sign uv.1 * sign uv.2

/-- Ordinary outer coefficient factors as the product of component orders. -/
theorem outerPairs_card (left right : Finset Vertex) :
    (outerPairs left right).card = left.card * right.card := by
  simp [outerPairs]

/-- The signed outer coefficient factors as the product of signed masses. -/
theorem signedOuterCoefficient_factor
    (sign : Vertex → ℤ) (left right : Finset Vertex) :
    signedPairCoefficient sign (outerPairs left right) =
      signedMass sign left * signedMass sign right := by
  classical
  simp only [signedPairCoefficient, outerPairs, signedMass,
    Finset.sum_product]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  rw [← Finset.mul_sum]

/-- Exact outer-component conclusion after a graph argument identifies the
support pairs with the oriented Cartesian block. -/
theorem outer_component_factorization
    (sign : Vertex → ℤ) (support : Finset (Vertex × Vertex))
    (left right : Finset Vertex)
    (support_eq : support = outerPairs left right) :
    support.card = left.card * right.card ∧
      signedPairCoefficient sign support =
        signedMass sign left * signedMass sign right := by
  subst support
  exact ⟨outerPairs_card left right,
    signedOuterCoefficient_factor sign left right⟩

/-- Non-collinear branch: an empty support has both ordinary and signed
coefficient zero. -/
theorem noncollinear_zero_coefficients
    (sign : Vertex → ℤ) (support : Finset (Vertex × Vertex))
    (support_empty : support = ∅) :
    support.card = 0 ∧ signedPairCoefficient sign support = 0 := by
  subst support
  simp [signedPairCoefficient]

/-- Replacing every root sign by a common sign multiple does not change any
pair product. -/
theorem pair_sign_root_invariant
    (sign sign' : Vertex → ℤ) (c : ℤ)
    (hc : c = 1 ∨ c = -1)
    (hchange : ∀ v, sign' v = c * sign v) :
    ∀ u v, sign' u * sign' v = sign u * sign v := by
  intro u v
  rw [hchange u, hchange v]
  rcases hc with rfl | rfl <;> ring

/-- The signed coefficient is therefore independent of the chosen parity
root (up to the common global sign supplied by the tree parity lemma). -/
theorem signedPairCoefficient_root_invariant
    (sign sign' : Vertex → ℤ) (c : ℤ)
    (hc : c = 1 ∨ c = -1)
    (hchange : ∀ v, sign' v = c * sign v)
    (pairs : Finset (Vertex × Vertex)) :
    signedPairCoefficient sign' pairs = signedPairCoefficient sign pairs := by
  unfold signedPairCoefficient
  apply Finset.sum_congr rfl
  intro uv huv
  exact pair_sign_root_invariant sign sign' c hc hchange uv.1 uv.2

/-- Positive sign count in a finite vertex set. -/
def positiveCount (sign : Vertex → ℤ) (s : Finset Vertex) : ℕ :=
  (s.filter fun v => sign v = 1).card

/-- Negative sign count in a finite vertex set. -/
def negativeCount (sign : Vertex → ℤ) (s : Finset Vertex) : ℕ :=
  (s.filter fun v => sign v = -1).card

/-- A genuine `±1` sign mass is positive count minus negative count. -/
theorem signedMass_eq_count_sub [DecidableEq Vertex]
    (sign : Vertex → ℤ) (s : Finset Vertex)
    (pm_one : ∀ v ∈ s, sign v = 1 ∨ sign v = -1) :
    signedMass sign s =
      (positiveCount sign s : ℤ) - (negativeCount sign s : ℤ) := by
  classical
  unfold signedMass positiveCount negativeCount
  calc
    (∑ v ∈ s, sign v) =
        ∑ v ∈ s, (if sign v = 1 then (1 : ℤ) else -1) := by
      apply Finset.sum_congr rfl
      intro v hv
      rcases pm_one v hv with h | h
      · simp [h]
      · simp [h]
    _ = ((s.filter fun v => sign v = 1).card : ℤ) -
          ((s.filter fun v => sign v = -1).card : ℤ) := by
      have hneg :
          (s.filter fun v => ¬ sign v = 1) =
            s.filter fun v => sign v = -1 := by
        ext v
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hv, hn⟩
          exact ⟨hv, (pm_one v hv).resolve_left hn⟩
        · rintro ⟨hv, hminus⟩
          refine ⟨hv, ?_⟩
          intro hone
          omega
      calc
        (∑ v ∈ s, if sign v = 1 then (1 : ℤ) else -1) =
            ∑ v ∈ s,
              ((if sign v = 1 then (1 : ℤ) else 0) -
                (if sign v = 1 then (0 : ℤ) else 1)) := by
          apply Finset.sum_congr rfl
          intro v hv
          by_cases h : sign v = 1 <;> simp [h]
        _ = (∑ v ∈ s, if sign v = 1 then (1 : ℤ) else 0) -
              (∑ v ∈ s, if sign v = 1 then (0 : ℤ) else 1) := by
          rw [Finset.sum_sub_distrib]
        _ = ((s.filter fun v => sign v = 1).card : ℤ) -
              ((s.filter fun v => ¬ sign v = 1).card : ℤ) := by
          congr 1
          · simp
          · calc
              (∑ v ∈ s, if sign v = 1 then (0 : ℤ) else 1) =
                  ∑ v ∈ s, if ¬ sign v = 1 then (1 : ℤ) else 0 := by
                apply Finset.sum_congr rfl
                intro v hv
                by_cases h : sign v = 1 <;> simp [h]
              _ = ((s.filter fun v => ¬ sign v = 1).card : ℤ) := by
                simpa using
                  (Finset.sum_boole (R := ℤ) (fun v => ¬ sign v = 1) s)
        _ = ((s.filter fun v => sign v = 1).card : ℤ) -
              ((s.filter fun v => sign v = -1).card : ℤ) := by rw [hneg]

end SignedOuter

/-! ## Public T8 statement layer -/

/-- Root-distance parity sign. -/
def paritySign (distanceFromRoot : ℕ) : ℤ :=
  (-1 : ℤ) ^ distanceFromRoot

theorem paritySign_add (a b : ℕ) :
    paritySign a * paritySign b = paritySign (a + b) := by
  simp [paritySign, pow_add]

/-- Root signs depend only on distance parity.  This is the small algebraic
bridge needed after a graph adapter proves the usual path-length congruence
modulo two. -/
theorem paritySign_eq_of_mod_two {a b : ℕ} (h : a % 2 = b % 2) :
    paritySign a = paritySign b := by
  change (-1 : ℤ) ^ a = (-1 : ℤ) ^ b
  rw [neg_one_pow_eq_pow_mod_two a, neg_one_pow_eq_pow_mod_two b, h]

/-- Exact doubled even/odd outer counts, stated with natural counts and all
casts visible.  This avoids any unproved divisibility or truncated
subtraction hidden in `(C ± K)/2`. -/
theorem T8_signed_cross_count_algebra
    (aPlus aMinus bPlus bMinus : ℕ) :
    2 * ((aPlus * bPlus + aMinus * bMinus : ℕ) : ℤ) =
      (((aPlus + aMinus) * (bPlus + bMinus) : ℕ) : ℤ) +
        ((aPlus : ℤ) - aMinus) * ((bPlus : ℤ) - bMinus) ∧
    2 * ((aPlus * bMinus + aMinus * bPlus : ℕ) : ℤ) =
      (((aPlus + aMinus) * (bPlus + bMinus) : ℕ) : ℤ) -
        ((aPlus : ℤ) - aMinus) * ((bPlus : ℤ) - bMinus) ∧
    0 ≤ ((aPlus * bPlus + aMinus * bMinus : ℕ) : ℤ) ∧
    0 ≤ ((aPlus * bMinus + aMinus * bPlus : ℕ) : ℤ) := by
  constructor
  · push_cast
    ring
  constructor
  · push_cast
    ring
  constructor <;> positivity

/-- Public T8 collinear branch.  The graph adapter owes the displayed support
equality by choosing the two extreme selected edges and orienting the two
disjoint outer components. -/
theorem T8_collinear_outer_components
    {Vertex : Type*} [DecidableEq Vertex]
    (sign : Vertex → ℤ) (support : Finset (Vertex × Vertex))
    (left right : Finset Vertex)
    (support_eq : support = outerPairs left right) :
    support.card = left.card * right.card ∧
      signedPairCoefficient sign support =
        signedMass sign left * signedMass sign right :=
  outer_component_factorization sign support left right support_eq

/-- Public T8 non-collinear branch.  The graph adapter owes emptiness from the
fact that no simple path contains the selected nonempty edge set. -/
theorem T8_noncollinear_outer_components
    {Vertex : Type*} [DecidableEq Vertex]
    (sign : Vertex → ℤ) (support : Finset (Vertex × Vertex))
    (support_empty : support = ∅) :
    support.card = 0 ∧ signedPairCoefficient sign support = 0 :=
  noncollinear_zero_coefficients sign support support_empty

/-- Public T8 path-moment statement.  `pairs` is one parity block of indexed
unordered vertex pairs; `uses` is the actual `0/1` path indicator; `edges` is
a duplicate-free enumeration supplied by the finite tree adapter.  The three
conclusions are precisely the degree-one, degree-two, and degree-three
identities with coefficients `1`, `2`, `3`, and `6`. -/
theorem T8_parity_resolved_path_moments
    {Pair Edge : Type*} [DecidableEq Pair]
    (edges : List Edge) (weight : Edge → ℤ) (uses : Pair → Edge → ℤ)
    (pairs : Finset Pair)
    (zero_one : ∀ p ∈ pairs, ∀ e, uses p e = 0 ∨ uses p e = 1) :
    ((∑ p ∈ pairs, pathValue edges weight uses p) =
      (edges.map
        (fun e => singletonCoefficient pairs uses e * weight e)).sum) ∧
    ((∑ p ∈ pairs, pathValue edges weight uses p ^ 2) =
      (edges.map
        (fun e => singletonCoefficient pairs uses e * weight e ^ 2)).sum +
        2 * pairSum edges
          (fun e f => pairCoefficient pairs uses e f * weight e * weight f)) ∧
    ((∑ p ∈ pairs, pathValue edges weight uses p ^ 3) =
      (edges.map
        (fun e => singletonCoefficient pairs uses e * weight e ^ 3)).sum +
        3 * pairSum edges (fun e f =>
          pairCoefficient pairs uses e f *
            (weight e ^ 2 * weight f + weight e * weight f ^ 2)) +
        6 * tripleSum edges (fun e f g =>
          tripleCoefficient pairs uses e f g * weight e * weight f * weight g)) := by
  exact ⟨first_path_moment edges weight uses pairs,
    second_path_moment edges weight uses pairs zero_one,
    third_path_moment edges weight uses pairs zero_one⟩

/-! ## Parity tails, two-step spacing, and saturation -/

/-- Least candidate at least `w` with residue `p` modulo two.  The intended
use has `p < 2`. -/
def parityStart (w p : ℕ) : ℕ :=
  if w % 2 = p then w else w + 1

/-- Target values in `[w,N]` with residue `p` modulo two. -/
def parityTail (N w p : ℕ) : Finset ℕ :=
  (Finset.Icc w N).filter fun t => t % 2 = p

theorem parityStart_le_of_le
    {w p t : ℕ} (hp : p < 2) (hwt : w ≤ t) (ht : t % 2 = p) :
    parityStart w p ≤ t := by
  unfold parityStart
  split_ifs with hw
  · exact hwt
  · have hwmod : w % 2 < 2 := Nat.mod_lt _ (by omega)
    have htmod : t % 2 < 2 := Nat.mod_lt _ (by omega)
    omega

theorem parityStart_mod_two {w p : ℕ} (hp : p < 2) :
    parityStart w p % 2 = p := by
  unfold parityStart
  split_ifs with hw
  · exact hw
  · have hwmod : w % 2 < 2 := Nat.mod_lt _ (by omega)
    omega

theorem parityStart_ge (w p : ℕ) : w ≤ parityStart w p := by
  unfold parityStart
  split_ifs <;> omega

/-- A strictly increasing natural sequence with constant parity advances by
at least two at each index. -/
theorem ordered_parity_spacing
    {h L p : ℕ} (f : Fin h ↪o ℕ)
    (floor : ∀ i, L ≤ f i)
    (sameParity : ∀ i, f i % 2 = p) :
    ∀ i : Fin h, L + 2 * (i : ℕ) ≤ f i := by
  intro i
  have aux : ∀ j (hj : j < h), L + 2 * j ≤ f ⟨j, hj⟩ := by
    intro j
    induction j with
    | zero =>
        intro hj
        simpa using floor ⟨0, hj⟩
    | succ j ih =>
        intro hj
        have hj' : j < h := lt_trans (Nat.lt_succ_self j) hj
        have hprev := ih hj'
        have hstrict : f ⟨j, hj'⟩ < f ⟨j + 1, hj⟩ := by
          apply f.strictMono
          simp
        have hparPrev := sameParity ⟨j, hj'⟩
        have hparNext := sameParity ⟨j + 1, hj⟩
        omega
  exact aux i i.isLt

/-- Enumerating a finite natural set increasingly preserves its power sum. -/
theorem sum_eq_sum_orderEmb
    (block : Finset ℕ) {h k : ℕ} (card_eq : block.card = h) :
    (∑ t ∈ block, t ^ k) =
      ∑ i : Fin h, (block.orderEmbOfFin card_eq i) ^ k := by
  classical
  let f : Fin h ↪o ℕ := block.orderEmbOfFin card_eq
  have hmap : Finset.map f.toEmbedding Finset.univ = block :=
    block.map_orderEmbOfFin_univ card_eq
  calc
    (∑ t ∈ block, t ^ k) =
        ∑ t ∈ Finset.map f.toEmbedding Finset.univ, t ^ k := by rw [hmap]
    _ = ∑ i : Fin h, (f i) ^ k := by simp
    _ = ∑ i : Fin h, (block.orderEmbOfFin card_eq i) ^ k := rfl

/-- Exact T9 order-statistic lower bound for any positive power.  The block
is an actual set (so global distance injectivity has already been used), every
member lies at least at `w`, and every member has parity `p`. -/
theorem parity_spacing_lower_moment
    (block : Finset ℕ) (w p h k : ℕ)
    (hp : p < 2) (card_eq : block.card = h)
    (lower : ∀ t ∈ block, w ≤ t)
    (parity : ∀ t ∈ block, t % 2 = p) :
    (∑ j ∈ Finset.range h, (parityStart w p + 2 * j) ^ k) ≤
      ∑ t ∈ block, t ^ k := by
  classical
  let f : Fin h ↪o ℕ := block.orderEmbOfFin card_eq
  have hfloor : ∀ i, parityStart w p ≤ f i := by
    intro i
    have hmem : f i ∈ block := block.orderEmbOfFin_mem card_eq i
    exact parityStart_le_of_le hp (lower (f i) hmem) (parity (f i) hmem)
  have hpar : ∀ i, f i % 2 = p := by
    intro i
    exact parity (f i) (block.orderEmbOfFin_mem card_eq i)
  have hpoint := ordered_parity_spacing f hfloor hpar
  rw [sum_eq_sum_orderEmb block card_eq]
  have hsum :
      (∑ i : Fin h, (parityStart w p + 2 * (i : ℕ)) ^ k) ≤
        ∑ i : Fin h, (f i) ^ k := by
    apply Finset.sum_le_sum
    intro i hi
    exact Nat.pow_le_pow_left (hpoint i) k
  rw [← Fin.sum_univ_eq_sum_range
    (fun j => (parityStart w p + 2 * j) ^ k) h]
  simpa only using hsum

/-- Upper moment budget inherited from containment in a target parity class. -/
theorem parity_block_upper_moment
    {block target : Finset ℕ} (k : ℕ) (contained : block ⊆ target) :
    (∑ t ∈ block, t ^ k) ≤ ∑ t ∈ target, t ^ k := by
  exact Finset.sum_le_sum_of_subset_of_nonneg contained (by simp)

/-- T9 largest-element capacity.  The positivity hypothesis is essential: it
selects the last element of the increasing enumeration. -/
theorem parity_spacing_capacity
    (block : Finset ℕ) (N w p h : ℕ)
    (hp : p < 2) (hpos : 0 < h) (card_eq : block.card = h)
    (contained : block ⊆ parityTail N w p) :
    parityStart w p + 2 * (h - 1) ≤ N := by
  classical
  let f : Fin h ↪o ℕ := block.orderEmbOfFin card_eq
  have hlower : ∀ t ∈ block, w ≤ t := by
    intro t ht
    have htail := Finset.mem_filter.mp (contained ht)
    exact (Finset.mem_Icc.mp htail.1).1
  have hparity : ∀ t ∈ block, t % 2 = p := by
    intro t ht
    exact (Finset.mem_filter.mp (contained ht)).2
  have hfloor : ∀ i, parityStart w p ≤ f i := by
    intro i
    have hmem : f i ∈ block := block.orderEmbOfFin_mem card_eq i
    exact parityStart_le_of_le hp (hlower (f i) hmem) (hparity (f i) hmem)
  have hpar : ∀ i, f i % 2 = p := by
    intro i
    exact hparity (f i) (block.orderEmbOfFin_mem card_eq i)
  let last : Fin h := ⟨h - 1, Nat.sub_lt hpos Nat.zero_lt_one⟩
  have hspace := ordered_parity_spacing f hfloor hpar last
  have hmem : f last ∈ parityTail N w p :=
    contained (block.orderEmbOfFin_mem card_eq last)
  have hupper : f last ≤ N := by
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hmem).1).2
  exact hspace.trans hupper

/-- Full T9 spacing/budget package through degrees one, two, and three. -/
theorem T9_parity_tail_spacing
    (block : Finset ℕ) (N w p h : ℕ)
    (hp : p < 2) (hpos : 0 < h) (card_eq : block.card = h)
    (contained : block ⊆ parityTail N w p) :
    ((∑ j ∈ Finset.range h, (parityStart w p + 2 * j)) ≤ ∑ t ∈ block, t) ∧
    ((∑ j ∈ Finset.range h, (parityStart w p + 2 * j) ^ 2) ≤
      ∑ t ∈ block, t ^ 2) ∧
    ((∑ j ∈ Finset.range h, (parityStart w p + 2 * j) ^ 3) ≤
      ∑ t ∈ block, t ^ 3) ∧
    ((∑ t ∈ block, t) ≤ ∑ t ∈ parityTail N w p, t) ∧
    ((∑ t ∈ block, t ^ 2) ≤ ∑ t ∈ parityTail N w p, t ^ 2) ∧
    ((∑ t ∈ block, t ^ 3) ≤ ∑ t ∈ parityTail N w p, t ^ 3) ∧
    parityStart w p + 2 * (h - 1) ≤ N := by
  have hlower : ∀ t ∈ block, w ≤ t := by
    intro t ht
    have htail := Finset.mem_filter.mp (contained ht)
    exact (Finset.mem_Icc.mp htail.1).1
  have hparity : ∀ t ∈ block, t % 2 = p := by
    intro t ht
    exact (Finset.mem_filter.mp (contained ht)).2
  constructor
  · simpa using parity_spacing_lower_moment block w p h 1 hp card_eq hlower hparity
  constructor
  · exact parity_spacing_lower_moment block w p h 2 hp card_eq hlower hparity
  constructor
  · exact parity_spacing_lower_moment block w p h 3 hp card_eq hlower hparity
  constructor
  · simpa using parity_block_upper_moment 1 contained
  constructor
  · exact parity_block_upper_moment 2 contained
  constructor
  · exact parity_block_upper_moment 3 contained
  · exact parity_spacing_capacity block N w p h hp hpos card_eq contained

/-- T9 saturated-tail conclusion: this identifies the value set of one block,
not its indexed ownership and not a rooted-side realization. -/
theorem T9_saturated_parity_tail
    {block : Finset ℕ} (N w p : ℕ)
    (contained : block ⊆ parityTail N w p)
    (same_card : block.card = (parityTail N w p).card) :
    block = parityTail N w p :=
  LeechTrees.saturatedFiniteBlock contained same_card

/-! ## Exact order-18 constants and conditional weights 67/68 -/

/-- The complete even target class at order 18. -/
def order18EvenTargets : Finset ℕ := parityTail 153 1 0

/-- The complete odd target class at order 18. -/
def order18OddTargets : Finset ℕ := parityTail 153 1 1

/-- Exact target counts and first three moments used by T8. -/
theorem T8_order18_target_moments :
    order18EvenTargets.card = 76 ∧
    order18OddTargets.card = 77 ∧
    (∑ t ∈ order18EvenTargets, t) = 5852 ∧
    (∑ t ∈ order18OddTargets, t) = 5929 ∧
    (∑ t ∈ order18EvenTargets, t ^ 2) = 596904 ∧
    (∑ t ∈ order18OddTargets, t ^ 2) = 608685 ∧
    (∑ t ∈ order18EvenTargets, t ^ 3) = 68491808 ∧
    (∑ t ∈ order18OddTargets, t ^ 3) = 70300153 := by
  decide

theorem weight67_even_tail_card : (parityTail 153 67 0).card = 43 := by
  decide

theorem weight67_odd_tail_card : (parityTail 153 67 1).card = 44 := by
  decide

theorem weight68_odd_tail_card : (parityTail 153 68 1).card = 43 := by
  decide

/-- Closed arithmetic kernel of the weight-67 implication.  The sign parity
and bounds are the exact consequences of a signed `9|9` split with total mass
four; the last two inequalities are the doubled parity-tail capacities. -/
theorem weight67_imbalance_arithmetic
    (x : ℤ)
    (x_odd : x % 2 = 1)
    (lower : -5 ≤ x) (upper : x ≤ 9)
    (even_capacity : 81 + x * (4 - x) ≤ 86)
    (odd_capacity : 81 - x * (4 - x) ≤ 88) :
    x = -1 ∨ x = 1 ∨ x = 3 ∨ x = 5 := by
  interval_cases x <;> norm_num at *

/-- Integer arithmetic kernel used by the public count-level T10 statement. -/
theorem weight67_nine_nine_arithmetic
    (aPlus aMinus bPlus bMinus x : ℤ)
    (evenBlock oddBlock : Finset ℕ)
    (haPlus : 0 ≤ aPlus) (haMinus : 0 ≤ aMinus)
    (hbPlus : 0 ≤ bPlus) (hbMinus : 0 ≤ bMinus)
    (sideA : aPlus + aMinus = 9)
    (sideB : bPlus + bMinus = 9)
    (x_def : x = aPlus - aMinus)
    (global_sign : (aPlus + bPlus) - (aMinus + bMinus) = 4)
    (even_card : 2 * (evenBlock.card : ℤ) =
      81 + x * (4 - x))
    (odd_card : 2 * (oddBlock.card : ℤ) =
      81 - x * (4 - x))
    (even_contained : evenBlock ⊆ parityTail 153 67 0)
    (odd_contained : oddBlock ⊆ parityTail 153 67 1) :
    x = -1 ∨ x = 1 ∨ x = 3 ∨ x = 5 := by
  have hxodd : x % 2 = 1 := by
    omega
  have hxlower : -5 ≤ x := by
    omega
  have hxupper : x ≤ 9 := by
    omega
  have hevenNat : evenBlock.card ≤ 43 := by
    calc
      evenBlock.card ≤ (parityTail 153 67 0).card :=
        Finset.card_le_card even_contained
      _ = 43 := weight67_even_tail_card
  have hoddNat : oddBlock.card ≤ 44 := by
    calc
      oddBlock.card ≤ (parityTail 153 67 1).card :=
        Finset.card_le_card odd_contained
      _ = 44 := weight67_odd_tail_card
  have heven : 81 + x * (4 - x) ≤ 86 := by
    omega
  have hodd : 81 - x * (4 - x) ≤ 88 := by
    norm_num at odd_card ⊢
    omega
  exact weight67_imbalance_arithmetic x hxodd hxlower hxupper heven hodd

/-- Public count-level form of T10.  The four natural numbers are the actual
positive/negative vertex counts on the two sides of one hypothetical `9|9`
edge of weight 67.  The block-cardinality hypotheses expose the graph
adapter's exact same-sign/opposite-sign identifications; containment exposes
the `IsLeech` range, injectivity, and path-parity obligations.  The theorem
contains no largest-edge, existence, or exclusion assertion. -/
theorem T10_weight67_nine_nine
    (aPlus aMinus bPlus bMinus : ℕ) (x : ℤ)
    (evenBlock oddBlock : Finset ℕ)
    (sideA : aPlus + aMinus = 9)
    (sideB : bPlus + bMinus = 9)
    (x_def : x = (aPlus : ℤ) - aMinus)
    (global_sign :
      ((aPlus : ℤ) + bPlus) - ((aMinus : ℤ) + bMinus) = 4)
    (even_card :
      evenBlock.card = aPlus * bPlus + aMinus * bMinus)
    (odd_card :
      oddBlock.card = aPlus * bMinus + aMinus * bPlus)
    (even_contained : evenBlock ⊆ parityTail 153 67 0)
    (odd_contained : oddBlock ⊆ parityTail 153 67 1) :
    x = -1 ∨ x = 1 ∨ x = 3 ∨ x = 5 := by
  rcases T8_signed_cross_count_algebra aPlus aMinus bPlus bMinus with
    ⟨hevenAlg, hoddAlg, -, -⟩
  have hsideA : (aPlus : ℤ) + aMinus = 9 := by exact_mod_cast sideA
  have hsideB : (bPlus : ℤ) + bMinus = 9 := by exact_mod_cast sideB
  have hy : (bPlus : ℤ) - bMinus = 4 - x := by
    omega
  have hevenFormula :
      2 * (evenBlock.card : ℤ) = 81 + x * (4 - x) := by
    calc
      2 * (evenBlock.card : ℤ) =
          2 * ((aPlus * bPlus + aMinus * bMinus : ℕ) : ℤ) := by
            rw [even_card]
      _ = (((aPlus + aMinus) * (bPlus + bMinus) : ℕ) : ℤ) +
          ((aPlus : ℤ) - aMinus) * ((bPlus : ℤ) - bMinus) := hevenAlg
      _ = 81 + x * (4 - x) := by
        rw [sideA, sideB, ← x_def, hy]
        norm_num
  have hoddFormula :
      2 * (oddBlock.card : ℤ) = 81 - x * (4 - x) := by
    calc
      2 * (oddBlock.card : ℤ) =
          2 * ((aPlus * bMinus + aMinus * bPlus : ℕ) : ℤ) := by
            rw [odd_card]
      _ = (((aPlus + aMinus) * (bPlus + bMinus) : ℕ) : ℤ) -
          ((aPlus : ℤ) - aMinus) * ((bPlus : ℤ) - bMinus) := hoddAlg
      _ = 81 - x * (4 - x) := by
        rw [sideA, sideB, ← x_def, hy]
        norm_num
  exact weight67_nine_nine_arithmetic
    (aPlus : ℤ) (aMinus : ℤ) (bPlus : ℤ) (bMinus : ℤ) x
    evenBlock oddBlock (by positivity) (by positivity) (by positivity)
    (by positivity) hsideA hsideB x_def global_sign hevenFormula hoddFormula
    even_contained odd_contained

/-- The first 43 positive odd residuals. -/
def oddResidual43 : Finset ℕ :=
  (Finset.range 43).image fun j => 2 * j + 1

theorem weight68_odd_tail_residual_image :
    (parityTail 153 68 1).image (fun t => t - 68) = oddResidual43 := by
  decide

theorem oddResidual43_moments :
    (∑ t ∈ oddResidual43, t) = 1849 ∧
    (∑ t ∈ oddResidual43, t ^ 2) = 105995 ∧
    (∑ t ∈ oddResidual43, t ^ 3) = 6835753 := by
  decide

theorem weight68_odd_tail_moments :
    (∑ t ∈ parityTail 153 68 1, t) = 4773 ∧
    (∑ t ∈ parityTail 153 68 1, t ^ 2) = 556291 ∧
    (∑ t ∈ parityTail 153 68 1, t ^ 3) = 67628637 := by
  decide

/-- Arithmetic saturation kernel used by the public T10b statement. -/
theorem weight68_saturated_odd_arithmetic
    (x : ℤ) (oddBlock : Finset ℕ)
    (extreme_mass : x = -1 ∨ x = 5)
    (odd_card : 2 * (oddBlock.card : ℤ) =
      81 - x * (4 - x))
    (odd_contained : oddBlock ⊆ parityTail 153 68 1) :
    oddBlock = parityTail 153 68 1 ∧
    oddBlock.image (fun t => t - 68) = oddResidual43 ∧
    (∑ t ∈ oddBlock.image (fun t => t - 68), t) = 1849 ∧
    (∑ t ∈ oddBlock.image (fun t => t - 68), t ^ 2) = 105995 ∧
    (∑ t ∈ oddBlock.image (fun t => t - 68), t ^ 3) = 6835753 ∧
    (∑ t ∈ oddBlock, t) = 4773 ∧
    (∑ t ∈ oddBlock, t ^ 2) = 556291 ∧
    (∑ t ∈ oddBlock, t ^ 3) = 67628637 := by
  have hcard : oddBlock.card = 43 := by
    rcases extreme_mass with rfl | rfl <;> norm_num at odd_card ⊢ <;> omega
  have hsaturated : oddBlock = parityTail 153 68 1 := by
    apply T9_saturated_parity_tail 153 68 1 odd_contained
    rw [hcard, weight68_odd_tail_card]
  have hresidual : oddBlock.image (fun t => t - 68) = oddResidual43 := by
    rw [hsaturated]
    exact weight68_odd_tail_residual_image
  rcases oddResidual43_moments with ⟨hr1, hr2, hr3⟩
  rcases weight68_odd_tail_moments with ⟨hb1, hb2, hb3⟩
  refine ⟨hsaturated, hresidual, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hresidual] using hr1
  · simpa [hresidual] using hr2
  · simpa [hresidual] using hr3
  · simpa [hsaturated] using hb1
  · simpa [hsaturated] using hb2
  · simpa [hsaturated] using hb3

/-- Exact public T10b implication.  The natural side counts, `9|9` equations,
global signed mass `4`, side imbalance, and opposite-sign block cardinality
are all explicit.  Containment is the still-owed graph/`IsLeech` adapter
premise.  For `x=-1` or `x=5` the odd tail saturates, giving the exact
residual set and residual/block moments.  No witness or exclusion is
asserted. -/
theorem T10b_weight68_nine_nine
    (aPlus aMinus bPlus bMinus : ℕ) (x : ℤ)
    (oddBlock : Finset ℕ)
    (sideA : aPlus + aMinus = 9)
    (sideB : bPlus + bMinus = 9)
    (x_def : x = (aPlus : ℤ) - aMinus)
    (global_sign :
      ((aPlus : ℤ) + bPlus) - ((aMinus : ℤ) + bMinus) = 4)
    (extreme_mass : x = -1 ∨ x = 5)
    (odd_card :
      oddBlock.card = aPlus * bMinus + aMinus * bPlus)
    (odd_contained : oddBlock ⊆ parityTail 153 68 1) :
    oddBlock = parityTail 153 68 1 ∧
    oddBlock.image (fun t => t - 68) = oddResidual43 ∧
    (∑ t ∈ oddBlock.image (fun t => t - 68), t) = 1849 ∧
    (∑ t ∈ oddBlock.image (fun t => t - 68), t ^ 2) = 105995 ∧
    (∑ t ∈ oddBlock.image (fun t => t - 68), t ^ 3) = 6835753 ∧
    (∑ t ∈ oddBlock, t) = 4773 ∧
    (∑ t ∈ oddBlock, t ^ 2) = 556291 ∧
    (∑ t ∈ oddBlock, t ^ 3) = 67628637 := by
  rcases T8_signed_cross_count_algebra aPlus aMinus bPlus bMinus with
    ⟨-, hoddAlg, -, -⟩
  have hy : (bPlus : ℤ) - bMinus = 4 - x := by
    omega
  have hoddFormula :
      2 * (oddBlock.card : ℤ) = 81 - x * (4 - x) := by
    calc
      2 * (oddBlock.card : ℤ) =
          2 * ((aPlus * bMinus + aMinus * bPlus : ℕ) : ℤ) := by
            rw [odd_card]
      _ = (((aPlus + aMinus) * (bPlus + bMinus) : ℕ) : ℤ) -
          ((aPlus : ℤ) - aMinus) * ((bPlus : ℤ) - bMinus) := hoddAlg
      _ = 81 - x * (4 - x) := by
        rw [sideA, sideB, ← x_def, hy]
        norm_num
  exact weight68_saturated_odd_arithmetic x oddBlock extreme_mass
    hoddFormula odd_contained

/-! ## Advertised second-odd-weight capacity core -/

/-- Injection-level form of the advertised companion capacity.

In the tree adapter, `LowEven` indexes the `t` even target ranks below
`q₂ = 2t+1` and injects into the internal same-component pair pool;
`LowOdd` indexes the `t` odd target ranks below `q₂` and injects into the
Cartesian pair pool across the unique weight-one edge.  This theorem proves
the capacity conclusion once those two localization injections have actually
been constructed.  It does not define `q₂` when fewer than two odd physical
edges exist and asserts no lift or exclusion. -/
theorem q2_capacity_from_low_rank_injections
    {LowEven LowOdd Internal A B : Type*}
    [Fintype LowEven] [Fintype LowOdd] [Fintype Internal]
    [Fintype A] [Fintype B]
    (q₂ t : ℕ)
    (q₂_def : q₂ = 2 * t + 1)
    (lowEven_card : Fintype.card LowEven = t)
    (lowOdd_card : Fintype.card LowOdd = t)
    (encodeEven : LowEven → Internal)
    (encodeOdd : LowOdd → A × B)
    (encodeEven_injective : Function.Injective encodeEven)
    (encodeOdd_injective : Function.Injective encodeOdd) :
    q₂ ≤ 2 * min (Fintype.card Internal)
      (Fintype.card A * Fintype.card B) + 1 := by
  have hinternal : t ≤ Fintype.card Internal := by
    rw [← lowEven_card]
    exact Fintype.card_le_of_injective encodeEven encodeEven_injective
  have hbridge : t ≤ Fintype.card A * Fintype.card B := by
    rw [← lowOdd_card]
    exact LeechTrees.card_le_product_of_injective encodeOdd encodeOdd_injective
  exact LeechTrees.secondOddWeight_from_two_capacities
    q₂ t (Fintype.card Internal) (Fintype.card A * Fintype.card B)
    q₂_def hinternal hbridge

end LeechTrees.ParityTail
