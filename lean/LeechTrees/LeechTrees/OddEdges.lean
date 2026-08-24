import LeechTrees.CombinatorialCore

/-!
# Odd physical-edge obstructions

This module is deliberately standalone over `LeechTrees.CombinatorialCore`.
It separates the graph-to-decomposition bridge from the algebraic obstruction:
no theorem below treats a desired odd-edge conclusion as an input.
-/

open scoped BigOperators

namespace LeechTrees.OddEdges

/-! ## Exact interval direct sums and signed imbalance -/

/-- An indexed, unique direct sum `X ⊕ Y = {0, ..., C-1}`.

The equivalence retains ownership and multiplicity: it is stronger than an
equality of sumset supports. -/
structure IntervalDirectSum (X Y : Finset ℕ) (C : ℕ) where
  equiv : (↥X × ↥Y) ≃ Fin C
  sum_eq : ∀ p, (equiv p : ℕ) = (p.1 : ℕ) + (p.2 : ℕ)

/-- Alternating evaluation of a finite depth set. -/
def signedImbalance (X : Finset ℕ) : ℤ :=
  ∑ x ∈ X, (-1 : ℤ) ^ x

/-- The enlarged rooted-LCA condition used in the audited order-25 terminal
argument.  Every genuine rooted-tree distance has such a witness. -/
def RealizesInternalRank (X : Finset ℕ) (rank : ℕ) : Prop :=
  ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧
    ∃ z ∈ X, z ≤ x ∧ z ≤ y ∧ rank + 2 * z = x + y

theorem IntervalDirectSum.card_mul (h : IntervalDirectSum X Y C) :
    X.card * Y.card = C := by
  have hc := Fintype.card_congr h.equiv
  simpa using hc

theorem IntervalDirectSum.sum_lt
    (h : IntervalDirectSum X Y C) {x y : ℕ}
    (hx : x ∈ X) (hy : y ∈ Y) : x + y < C := by
  let p : ↥X × ↥Y := (⟨x, hx⟩, ⟨y, hy⟩)
  have hp := (h.equiv p).isLt
  simpa [p, h.sum_eq p] using hp

theorem IntervalDirectSum.eq_of_sum_eq
    (h : IntervalDirectSum X Y C)
    {x x' y y' : ℕ}
    (hx : x ∈ X) (hx' : x' ∈ X) (hy : y ∈ Y) (hy' : y' ∈ Y)
    (hsum : x + y = x' + y') : x = x' ∧ y = y' := by
  let p : ↥X × ↥Y := (⟨x, hx⟩, ⟨y, hy⟩)
  let p' : ↥X × ↥Y := (⟨x', hx'⟩, ⟨y', hy'⟩)
  have he : h.equiv p = h.equiv p' := by
    apply Fin.ext
    simpa [p, p', h.sum_eq p, h.sum_eq p'] using hsum
  have hp : p = p' := h.equiv.injective he
  exact ⟨congrArg (fun q => (q.1 : ℕ)) hp,
    congrArg (fun q => (q.2 : ℕ)) hp⟩

theorem IntervalDirectSum.exists_repr
    (h : IntervalDirectSum X Y C) {k : ℕ} (hk : k < C) :
    ∃ x ∈ X, ∃ y ∈ Y, x + y = k := by
  let q : Fin C := ⟨k, hk⟩
  let p := h.equiv.symm q
  refine ⟨p.1, p.1.property, p.2, p.2.property, ?_⟩
  have he := h.sum_eq p
  have hi : h.equiv p = q := h.equiv.apply_symm_apply q
  rw [hi] at he
  exact he.symm

def IntervalDirectSum.comm (h : IntervalDirectSum X Y C) :
    IntervalDirectSum Y X C where
  equiv := (Equiv.prodComm ↑Y ↑X).trans h.equiv
  sum_eq := by
    intro p
    simpa [Nat.add_comm] using h.sum_eq (p.2, p.1)

theorem alternating_sum_range (C : ℕ) :
    (∑ k ∈ Finset.range C, (-1 : ℤ) ^ k) =
      if Even C then 0 else 1 := by
  have heven : ∀ m : ℕ,
      (∑ k ∈ Finset.range (2 * m), (-1 : ℤ) ^ k) = 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
          Finset.sum_range_succ, Finset.sum_range_succ, ih]
        have hmEven : Even (2 * m) := ⟨m, by omega⟩
        have hmOdd : Odd (2 * m + 1) := ⟨m, by omega⟩
        rw [hmEven.neg_one_pow, hmOdd.neg_one_pow]
        norm_num
  by_cases hC : Even C
  · rcases hC with ⟨m, hm⟩
    have hCm : C = 2 * m := by omega
    rw [hCm, if_pos]
    · exact heven m
    · exact ⟨m, by omega⟩
  · have hCodd : Odd C := Nat.not_even_iff_odd.mp hC
    rcases hCodd with ⟨m, hm⟩
    have hCm : C = 2 * m + 1 := by omega
    rw [hCm, if_neg, Finset.sum_range_succ, heven]
    have hmEven : Even (2 * m) := ⟨m, by omega⟩
    rw [hmEven.neg_one_pow]
    norm_num
    intro hbad
    rcases hbad with ⟨k, hk⟩
    omega

theorem IntervalDirectSum.signedImbalance_mul
    (h : IntervalDirectSum X Y C) :
    signedImbalance X * signedImbalance Y =
      if Even C then 0 else 1 := by
  have hx : signedImbalance X = ∑ x : ↥X, (-1 : ℤ) ^ (x : ℕ) := by
    unfold signedImbalance
    exact (Finset.sum_attach X (fun x => (-1 : ℤ) ^ x)).symm
  have hy : signedImbalance Y = ∑ y : ↥Y, (-1 : ℤ) ^ (y : ℕ) := by
    unfold signedImbalance
    exact (Finset.sum_attach Y (fun y => (-1 : ℤ) ^ y)).symm
  rw [hx, hy]
  calc
    (∑ x : ↥X, (-1 : ℤ) ^ (x : ℕ)) *
        (∑ y : ↥Y, (-1 : ℤ) ^ (y : ℕ)) =
        ∑ p : ↥X × ↥Y, (-1 : ℤ) ^ ((p.1 : ℕ) + (p.2 : ℕ)) := by
          rw [Fintype.sum_prod_type]
          simp only [pow_add]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
    _ = ∑ k : Fin C, (-1 : ℤ) ^ (k : ℕ) := by
      apply Fintype.sum_equiv h.equiv
      intro p
      rw [h.sum_eq p]
    _ = ∑ k ∈ Finset.range C, (-1 : ℤ) ^ k := by
      exact Fin.sum_univ_eq_sum_range (fun k => (-1 : ℤ) ^ k) C
    _ = if Even C then 0 else 1 := alternating_sum_range C

/-! ## The repaired initial-block lemma -/

private theorem blockBoundary_add_small
    {r x s : ℕ} (hr : 0 < r) (hx : r ∣ x) (hs : s < r) :
    r * ((x + s) / r) = x := by
  rcases hx with ⟨u, rfl⟩
  rw [Nat.mul_add_div hr]
  have hsdiv : s / r = 0 := Nat.div_eq_of_lt hs
  rw [hsdiv]
  simp

theorem IntervalDirectSum.first_missing_lt
    (h : IntervalDirectSum X Y C)
    (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    {r : ℕ} (_hr : 0 < r)
    (hbelow : ∀ k < r, k ∈ X)
    (hYpos : ∃ y ∈ Y, 0 < y) : r < C := by
  rcases hYpos with ⟨y, hyY, hypos⟩
  have hyC := h.sum_lt h0X hyY
  have hry : r ≤ y := by
    by_contra hnot
    have hyr : y < r := by omega
    have hyX := hbelow y hyr
    have hu := h.eq_of_sum_eq hyX h0X h0Y hyY (by omega)
    omega
  omega

theorem IntervalDirectSum.first_missing_mem_other
    (h : IntervalDirectSum X Y C)
    (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    {r : ℕ} (_hr : 0 < r)
    (hbelow : ∀ k < r, k ∈ X)
    (hrnot : r ∉ X)
    (hrC : r < C) : r ∈ Y := by
  rcases h.exists_repr hrC with ⟨x, hxX, y, hyY, hxy⟩
  have hy_not_small : ¬(0 < y ∧ y < r) := by
    rintro ⟨hypos, hyr⟩
    have hyX := hbelow y hyr
    have hu := h.eq_of_sum_eq hyX h0X h0Y hyY (by omega)
    omega
  by_cases hy0 : y = 0
  · subst y
    simp only [add_zero] at hxy
    subst x
    exact (hrnot hxX).elim
  · have hypos : 0 < y := by omega
    have : r ≤ y := by omega
    have hx0 : x = 0 := by omega
    have hyr : y = r := by omega
    simpa [hyr] using hyY

/-- Simultaneous block classification.  This is the induction hidden in many
informal mixed-radix proofs: `X` is constant on each length-`r` block and
every member of `Y` is a multiple of `r`. -/
theorem IntervalDirectSum.block_classification
    (h : IntervalDirectSum X Y C)
    (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    {r : ℕ} (hr : 0 < r)
    (hbelow : ∀ k < r, k ∈ X)
    (hrnot : r ∉ X)
    (hYpos : ∃ y ∈ Y, 0 < y) :
    ∀ k < C,
      (k ∈ X ↔ r * (k / r) ∈ X) ∧
      (k ∈ Y → r ∣ k) := by
  have hrC := h.first_missing_lt h0X h0Y hr hbelow hYpos
  have hrY := h.first_missing_mem_other h0X h0Y hr hbelow hrnot hrC
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hkC
      let b := r * (k / r)
      let s := k % r
      have hslt : s < r := Nat.mod_lt k hr
      have hdecomp : b + s = k := by
        simpa [b, s] using Nat.div_add_mod k r
      by_cases hs0 : s = 0
      · have hkb : k = b := by omega
        have hbdvd : r ∣ b := ⟨k / r, by simp [b]⟩
        have hbb : r * (b / r) = b :=
          blockBoundary_add_small hr hbdvd hr
        constructor
        · simp [hkb, hbb]
        · intro hkY
          refine ⟨k / r, ?_⟩
          omega
      · have hspos : 0 < s := by omega
        have hb_lt : b < k := by omega
        have hbC : b < C := by omega
        have ihb := ih b hb_lt hbC

        have hb_to_k : b ∈ X → k ∈ X := by
          intro hbX
          rcases h.exists_repr hkC with ⟨x, hxX, y, hyY, hxy⟩
          by_cases hy0 : y = 0
          · subst y
            simpa using hxy ▸ hxX
          have hypos : 0 < y := by omega
          by_cases hyk : y = k
          · subst y
            have hx0 : x = 0 := by omega
            subst x
            have hrsX : r - s ∈ X := by
              apply hbelow
              omega
            have heq : b + r = (r - s) + k := by omega
            have hu := h.eq_of_sum_eq hbX hrsX hrY hyY heq
            have hb_eq_r : b = r := by
              dsimp [b]
              rw [hu.2]
              rw [Nat.div_self (by omega)]
              simp
            omega
          · have hylt : y < k := by omega
            have hyC : y < C := by omega
            have hydvd : r ∣ y := (ih y hylt hyC).2 hyY
            have hxlt : x < k := by omega
            have hxC : x < C := by omega
            have hxbX : r * (x / r) ∈ X :=
              (ih x hxlt hxC).1.mp hxX
            rcases hydvd with ⟨v, hv⟩
            have hxdec := Nat.div_add_mod x r
            have hxmodlt := Nat.mod_lt x hr
            have heqxy : x + y = b + s := hxy.trans hdecomp.symm
            have hxmod : x % r = s := by
              have hm := congrArg (fun t : ℕ => t % r) heqxy
              simp [Nat.add_mod, hv, b, Nat.mod_eq_of_lt hslt] at hm
              exact hm
            have hboundary : r * (x / r) + y = b := by
              omega
            have hu := h.eq_of_sum_eq hxbX hbX hyY h0Y hboundary
            omega

        have hk_to_b : k ∈ X → b ∈ X := by
          intro hkX
          rcases h.exists_repr hbC with ⟨x, hxX, y, hyY, hxy⟩
          by_cases hy0 : y = 0
          · subst y
            simpa using hxy ▸ hxX
          have hypos : 0 < y := by omega
          have hylt : y < k := by omega
          have hyC : y < C := by omega
          have hydvd : r ∣ y := (ih y hylt hyC).2 hyY
          have hbdvd : r ∣ b := ⟨k / r, by simp [b]⟩
          have hxydvd : r ∣ x + y := hxy ▸ hbdvd
          have hxdvd : r ∣ x := (Nat.dvd_add_iff_left hydvd).2 hxydvd
          have hxlt : x < k := by omega
          have hxC : x < C := by omega
          have hxslt : x + s < k := by omega
          have hxsC : x + s < C := by omega
          have hboundxs : r * ((x + s) / r) = x :=
            blockBoundary_add_small hr hxdvd hslt
          have hxsX : x + s ∈ X := by
            apply (ih (x + s) hxslt hxsC).1.mpr
            simpa [hboundxs] using hxX
          have hsumk : (x + s) + y = k := by omega
          have hu := h.eq_of_sum_eq hxsX hkX hyY h0Y hsumk
          omega

        constructor
        · exact ⟨hk_to_b, hb_to_k⟩
        · intro hkY
          by_cases hbX : b ∈ X
          · have hkX := hb_to_k hbX
            have hu := h.eq_of_sum_eq hkX h0X h0Y hkY (by omega)
            omega
          · rcases h.exists_repr hbC with ⟨x, hxX, y, hyY, hxy⟩
            have hy0 : y ≠ 0 := by
              intro hyzero
              subst y
              apply hbX
              simpa using hxy ▸ hxX
            have hypos : 0 < y := by omega
            have hylt : y < k := by omega
            have hyC : y < C := by omega
            have hydvd : r ∣ y := (ih y hylt hyC).2 hyY
            have hbdvd : r ∣ b := ⟨k / r, by simp [b]⟩
            have hxydvd : r ∣ x + y := hxy ▸ hbdvd
            have hxdvd : r ∣ x := (Nat.dvd_add_iff_left hydvd).2 hxydvd
            have hxslt : x + s < k := by omega
            have hxsC : x + s < C := by omega
            have hboundxs : r * ((x + s) / r) = x :=
              blockBoundary_add_small hr hxdvd hslt
            have hxsX : x + s ∈ X := by
              apply (ih (x + s) hxslt hxsC).1.mpr
              simpa [hboundxs] using hxX
            have hsumk : (x + s) + y = k := by omega
            have hu := h.eq_of_sum_eq hxsX h0X hyY hkY (by simpa using hsumk)
            omega

/-- Repaired terminal-partial-block argument.  In the terminal case owned by
`X`, the positive element of `Y` is what forces a sum past `C-1`. -/
theorem IntervalDirectSum.firstRadix_dvd_length
    (h : IntervalDirectSum X Y C)
    (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    {r : ℕ} (hr : 0 < r)
    (hbelow : ∀ k < r, k ∈ X)
    (hrnot : r ∉ X)
    (hYpos : ∃ y ∈ Y, 0 < y) : r ∣ C := by
  have hclass := h.block_classification h0X h0Y hr hbelow hrnot hYpos
  let b := r * (C / r)
  let s := C % r
  have hslt : s < r := Nat.mod_lt C hr
  have hdecomp : b + s = C := by
    simpa [b, s] using Nat.div_add_mod C r
  by_cases hs0 : s = 0
  · refine ⟨C / r, ?_⟩
    omega
  · have hspos : 0 < s := by omega
    have hbC : b < C := by omega
    rcases h.exists_repr hbC with ⟨x, hxX, y, hyY, hxy⟩
    by_cases hy0 : y = 0
    · subst y
      have hxb : x = b := by omega
      subst x
      rcases hYpos with ⟨v, hvY, hvpos⟩
      have hvC : v < C := by
        have := h.sum_lt h0X hvY
        omega
      have hvdvd := (hclass v hvC).2 hvY
      rcases hvdvd with ⟨q, hq⟩
      have hvr : r ≤ v := by
        rw [hq]
        have hqpos : 0 < q := by
          by_contra hq0
          have : q = 0 := by omega
          have hvzero : v = 0 := by simp [hq, this]
          omega
        exact Nat.le_mul_of_pos_right r hqpos
      have hbad := h.sum_lt hxX hvY
      omega
    · have hypos : 0 < y := by omega
      have hyC : y < C := by omega
      have hydvd := (hclass y hyC).2 hyY
      have hbdvd : r ∣ b := ⟨C / r, by simp [b]⟩
      have hxydvd : r ∣ x + y := hxy ▸ hbdvd
      have hxdvd : r ∣ x := (Nat.dvd_add_iff_left hydvd).2 hxydvd
      have hxsC : x + s < C := by omega
      have hboundxs : r * ((x + s) / r) = x :=
        blockBoundary_add_small hr hxdvd hslt
      have hxsX : x + s ∈ X := by
        apply (hclass (x + s) hxsC).1.mpr
        simpa [hboundxs] using hxX
      have hbad := h.sum_lt hxsX hyY
      omega

private def quotientBlocks (S : Finset ℕ) (r m : ℕ) : Finset ℕ :=
  (Finset.range m).filter (fun q => r * q ∈ S)

theorem IntervalDirectSum.firstRadix_dvd_card_left
    (h : IntervalDirectSum X Y C)
    (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    {r : ℕ} (hr : 0 < r)
    (hbelow : ∀ k < r, k ∈ X)
    (hrnot : r ∉ X)
    (hYpos : ∃ y ∈ Y, 0 < y) : r ∣ X.card := by
  have hrC := h.firstRadix_dvd_length h0X h0Y hr hbelow hrnot hYpos
  rcases hrC with ⟨m, hm⟩
  have hclass := h.block_classification h0X h0Y hr hbelow hrnot hYpos
  let Q := quotientBlocks X r m
  have hCeq : C = r * m := by omega
  have qbound {x : ℕ} (hxC : x < C) : x / r < m := by
    by_contra hnot
    have hmq : m ≤ x / r := by omega
    have hmul : r * m ≤ r * (x / r) := Nat.mul_le_mul_left r hmq
    have hxdec := Nat.div_add_mod x r
    omega
  let toQ : ↥X → Fin r × ↥Q := fun x =>
    (⟨(x : ℕ) % r, Nat.mod_lt x hr⟩,
      ⟨(x : ℕ) / r, by
        simp only [Q, quotientBlocks, Finset.mem_filter, Finset.mem_range]
        exact ⟨qbound (h.sum_lt x.property h0Y),
          (hclass x (h.sum_lt x.property h0Y)).1.mp x.property⟩⟩)
  let fromQ : Fin r × ↥Q → ↥X := fun p =>
    ⟨r * (p.2 : ℕ) + (p.1 : ℕ), by
      have hqmem : r * (p.2 : ℕ) ∈ X := by
        exact (Finset.mem_filter.mp p.2.property).2
      have hqbound : (p.2 : ℕ) < m := by
        exact Finset.mem_range.mp (Finset.mem_filter.mp p.2.property).1
      have hvalC : r * (p.2 : ℕ) + (p.1 : ℕ) < C := by
        have hmuls : r * ((p.2 : ℕ) + 1) ≤ r * m :=
          Nat.mul_le_mul_left r (by omega)
        have hnext : r * ((p.2 : ℕ) + 1) =
            r * (p.2 : ℕ) + r := by ring
        omega
      apply (hclass _ hvalC).1.mpr
      rw [blockBoundary_add_small hr ⟨p.2, rfl⟩ p.1.isLt]
      exact hqmem⟩
  let e : ↥X ≃ Fin r × ↥Q :=
    { toFun := toQ
      invFun := fromQ
      left_inv := by
        intro x
        apply Subtype.ext
        dsimp [toQ, fromQ]
        exact Nat.div_add_mod x r
      right_inv := by
        intro p
        apply Prod.ext
        · apply Fin.ext
          dsimp [toQ, fromQ]
          simp [Nat.mod_eq_of_lt p.1.isLt]
        · apply Subtype.ext
          dsimp [toQ, fromQ]
          rw [Nat.mul_add_div hr]
          rw [Nat.div_eq_of_lt p.1.isLt]
          simp }
  have hc := Fintype.card_congr e
  refine ⟨Q.card, ?_⟩
  simpa [Q] using hc

/-- The actual quotient interval factorization supplied by the repaired block
scan.  The factor containing the initial block loses the radix `r`; the
opposite factor keeps its cardinality. -/
theorem IntervalDirectSum.firstRadix_quotient
    (h : IntervalDirectSum X Y C)
    (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    {r : ℕ} (hr : 0 < r)
    (hbelow : ∀ k < r, k ∈ X)
    (hrnot : r ∉ X)
    (hYpos : ∃ y ∈ Y, 0 < y) :
    ∃ X' Y' : Finset ℕ,
      ∃ _hsum : IntervalDirectSum X' Y' (C / r),
      X.card = r * X'.card ∧ Y.card = Y'.card ∧
      (∀ q, q ∈ X' ↔ q < C / r ∧ r * q ∈ X) ∧
      (∀ q, q ∈ Y' ↔ q < C / r ∧ r * q ∈ Y) := by
  have hrCdiv := h.firstRadix_dvd_length h0X h0Y hr hbelow hrnot hYpos
  let m := C / r
  have hCeq : C = r * m := by
    rcases hrCdiv with ⟨u, hu⟩
    have hm : C / r = u := by
      rw [hu, Nat.mul_div_cancel_left _ hr]
    simp [m, hm, hu]
  have hclass := h.block_classification h0X h0Y hr hbelow hrnot hYpos
  let X' := quotientBlocks X r m
  let Y' := quotientBlocks Y r m

  have mult_bound {q : ℕ} (hq : r * q < C) : q < m := by
    by_contra hnot
    have hmq : m ≤ q := by omega
    have hmul : r * m ≤ r * q := Nat.mul_le_mul_left r hmq
    omega

  let addQ : ↥X' × ↥Y' → Fin m := fun p =>
    ⟨(p.1 : ℕ) + (p.2 : ℕ), by
      have hx : r * (p.1 : ℕ) ∈ X :=
        (Finset.mem_filter.mp p.1.property).2
      have hy : r * (p.2 : ℕ) ∈ Y :=
        (Finset.mem_filter.mp p.2.property).2
      have hsum := h.sum_lt hx hy
      have hmul : r * ((p.1 : ℕ) + (p.2 : ℕ)) =
          r * (p.1 : ℕ) + r * (p.2 : ℕ) := by ring
      nlinarith⟩

  have addQ_injective : Function.Injective addQ := by
    intro p p' he
    have hsumq : (p.1 : ℕ) + (p.2 : ℕ) =
        (p'.1 : ℕ) + (p'.2 : ℕ) := congrArg Fin.val he
    have hx : r * (p.1 : ℕ) ∈ X :=
      (Finset.mem_filter.mp p.1.property).2
    have hx' : r * (p'.1 : ℕ) ∈ X :=
      (Finset.mem_filter.mp p'.1.property).2
    have hy : r * (p.2 : ℕ) ∈ Y :=
      (Finset.mem_filter.mp p.2.property).2
    have hy' : r * (p'.2 : ℕ) ∈ Y :=
      (Finset.mem_filter.mp p'.2.property).2
    have hu := h.eq_of_sum_eq hx hx' hy hy' (by
      rw [← mul_add, ← mul_add, hsumq])
    apply Prod.ext
    · apply Subtype.ext
      exact Nat.mul_left_cancel hr hu.1
    · apply Subtype.ext
      exact Nat.mul_left_cancel hr hu.2

  have addQ_surjective : Function.Surjective addQ := by
    intro k
    have hrkC : r * (k : ℕ) < C := by
      have hstep : (k : ℕ) + 1 ≤ m := by omega
      have hmul := Nat.mul_le_mul_left r hstep
      have hnext : r * ((k : ℕ) + 1) = r * (k : ℕ) + r := by ring
      omega
    rcases h.exists_repr hrkC with ⟨x, hxX, y, hyY, hxy⟩
    have hyC : y < C := by simpa using h.sum_lt h0X hyY
    have hydvd := (hclass y hyC).2 hyY
    have htargetdvd : r ∣ x + y := hxy ▸ dvd_mul_right r (k : ℕ)
    have hxdvd : r ∣ x := (Nat.dvd_add_iff_left hydvd).2 htargetdvd
    rcases hxdvd with ⟨qx, hqx⟩
    rcases hydvd with ⟨qy, hqy⟩
    have hqxC : r * qx < C := by simpa [hqx] using h.sum_lt hxX h0Y
    have hqyC : r * qy < C := by simpa [hqy] using h.sum_lt h0X hyY
    have hqxmem : qx ∈ X' := by
      simp only [X', quotientBlocks, Finset.mem_filter, Finset.mem_range]
      exact ⟨mult_bound hqxC, by simpa [hqx] using hxX⟩
    have hqymem : qy ∈ Y' := by
      simp only [Y', quotientBlocks, Finset.mem_filter, Finset.mem_range]
      exact ⟨mult_bound hqyC, by simpa [hqy] using hyY⟩
    let p : ↥X' × ↥Y' := (⟨qx, hqxmem⟩, ⟨qy, hqymem⟩)
    refine ⟨p, ?_⟩
    apply Fin.ext
    dsimp [addQ, p]
    have hmul : r * (qx + qy) = r * (k : ℕ) := by
      calc
        r * (qx + qy) = r * qx + r * qy := by ring
        _ = x + y := by rw [← hqx, ← hqy]
        _ = r * (k : ℕ) := hxy
    exact Nat.mul_left_cancel hr hmul

  let hquot : IntervalDirectSum X' Y' m :=
    { equiv := Equiv.ofBijective addQ ⟨addQ_injective, addQ_surjective⟩
      sum_eq := by intro p; rfl }

  let toY : ↥Y → ↥Y' := fun y =>
    ⟨(y : ℕ) / r, by
      have hyC : (y : ℕ) < C := by simpa using h.sum_lt h0X y.property
      have hydvd := (hclass y hyC).2 y.property
      have hbound : (y : ℕ) / r < m := by
        rcases hydvd with ⟨q, hq⟩
        have hqbound : q < m := mult_bound (by simpa [hq] using hyC)
        simpa [hq, Nat.mul_div_cancel_left q hr] using hqbound
      simp only [Y', quotientBlocks, Finset.mem_filter, Finset.mem_range]
      refine ⟨hbound, ?_⟩
      rcases hydvd with ⟨q, hq⟩
      simpa [hq, Nat.mul_div_cancel_left q hr] using y.property⟩
  let fromY : ↥Y' → ↥Y := fun q =>
    ⟨r * (q : ℕ), (Finset.mem_filter.mp q.property).2⟩
  let eY : ↥Y ≃ ↥Y' :=
    { toFun := toY
      invFun := fromY
      left_inv := by
        intro y
        apply Subtype.ext
        dsimp [toY, fromY]
        have hyC : (y : ℕ) < C := by simpa using h.sum_lt h0X y.property
        rcases (hclass y hyC).2 y.property with ⟨q, hq⟩
        simp [hq, Nat.mul_div_cancel_left q hr]
      right_inv := by
        intro q
        apply Subtype.ext
        dsimp [toY, fromY]
        rw [Nat.mul_div_cancel_left _ hr] }
  have hcY : Y.card = Y'.card := by
    simpa using Fintype.card_congr eY
  have hcOrig := h.card_mul
  have hcQuot := hquot.card_mul
  have hYposCard : 0 < Y.card := Finset.card_pos.mpr ⟨0, h0Y⟩
  have hcX : X.card = r * X'.card := by
    rw [hcY] at hcOrig hYposCard
    rw [hCeq] at hcOrig
    have heq : X.card * Y'.card = (r * X'.card) * Y'.card := by
      calc
        X.card * Y'.card = r * m := hcOrig
        _ = r * (X'.card * Y'.card) := by rw [hcQuot]
        _ = (r * X'.card) * Y'.card := by ring
    exact Nat.mul_right_cancel hYposCard heq
  refine ⟨X', Y', hquot, hcX, hcY, ?_, ?_⟩
  · intro q
    simp [X', quotientBlocks, m]
  · intro q
    simp [Y', quotientBlocks, m]

theorem Finset.exists_pos_of_one_lt_card
    {S : Finset ℕ} (hcard : 1 < S.card) : ∃ x ∈ S, 0 < x := by
  rcases Finset.one_lt_card_iff.mp hcard with ⟨x, y, hx, hy, hxy⟩
  by_cases hx0 : x = 0
  · exact ⟨y, hy, by omega⟩
  · exact ⟨x, hx, by omega⟩

theorem IntervalDirectSum.exists_firstRadix
    (h : IntervalDirectSum X Y C)
    (h0X : 0 ∈ X) (h0Y : 0 ∈ Y) (h1X : 1 ∈ X)
    (hYpos : ∃ y ∈ Y, 0 < y) :
    ∃ r : ℕ, 2 ≤ r ∧ (∀ k < r, k ∈ X) ∧ r ∉ X := by
  rcases hYpos with ⟨y, hyY, hypos⟩
  have hy_not_X : y ∉ X := by
    intro hyX
    have hu := h.eq_of_sum_eq hyX h0X h0Y hyY (by omega)
    omega
  have hexists : ∃ k : ℕ, k ∉ X := ⟨y, hy_not_X⟩
  let r := Nat.find hexists
  have hrnot : r ∉ X := Nat.find_spec hexists
  have hbelow : ∀ k < r, k ∈ X := by
    intro k hk
    by_contra hnot
    have hle := Nat.find_min' hexists hnot
    omega
  have hr2 : 2 ≤ r := by
    have hrpos : 0 < r := by
      by_contra h
      have : r = 0 := by omega
      exact hrnot (this ▸ h0X)
    by_contra h
    have : r = 1 := by omega
    exact hrnot (this ▸ h1X)
  exact ⟨r, hr2, hbelow, hrnot⟩

/-! ## Exact internal-rank ownership for the one-odd decomposition -/

/-- Unordered pairs of distinct elements of the depth set, represented as
edges of the complete simple graph. -/
abbrev DepthEdge (X : Finset ℕ) :=
  (⊤ : SimpleGraph ↥X).edgeSet

theorem card_depthEdge (X : Finset ℕ) :
    Fintype.card (DepthEdge X) = X.card.choose 2 := by
  classical
  rw [← SimpleGraph.edgeFinset_card,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  simp

theorem realizedInternalRank_dvd
    {X : Finset ℕ} {rank r : ℕ}
    (hall : ∀ x ∈ X, r ∣ x)
    (hreal : RealizesInternalRank X rank) : r ∣ rank := by
  rcases hreal with ⟨x, hx, y, hy, hxy, z, hz, hzx, hzy, heq⟩
  have hxdiv := hall x hx
  have hydiv := hall y hy
  have hzdiv := hall z hz
  have hsum : r ∣ x + y := dvd_add hxdiv hydiv
  have htwice : r ∣ 2 * z := dvd_mul_of_dvd_right hzdiv 2
  have htotal : r ∣ rank + 2 * z := heq ▸ hsum
  exact (Nat.dvd_add_iff_left htwice).2 htotal

/-- Exact, indexed ownership of the internal half-ranks `1,...,M`. -/
structure InternalRankPartition (X Y : Finset ℕ) (M : ℕ) where
  rankEquiv : (DepthEdge X ⊕ DepthEdge Y) ≃ Fin M
  realizes_left : ∀ e : DepthEdge X,
    RealizesInternalRank X ((rankEquiv (Sum.inl e) : ℕ) + 1)
  realizes_right : ∀ e : DepthEdge Y,
    RealizesInternalRank Y ((rankEquiv (Sum.inr e) : ℕ) + 1)

theorem InternalRankPartition.realizes_either
    (p : InternalRankPartition X Y M) {k : ℕ} (hk : k < M) :
    RealizesInternalRank X (k + 1) ∨ RealizesInternalRank Y (k + 1) := by
  let q : Fin M := ⟨k, hk⟩
  cases he : p.rankEquiv.symm q with
  | inl e =>
      left
      have hforward : p.rankEquiv (Sum.inl e) = q := by
        rw [← he]
        exact p.rankEquiv.apply_symm_apply q
      have hval : (p.rankEquiv (Sum.inl e) : ℕ) = k :=
        congrArg Fin.val hforward
      simpa [hval] using p.realizes_left e
  | inr e =>
      right
      have hforward : p.rankEquiv (Sum.inr e) = q := by
        rw [← he]
        exact p.rankEquiv.apply_symm_apply q
      have hval : (p.rankEquiv (Sum.inr e) : ℕ) = k :=
        congrArg Fin.val hforward
      simpa [hval] using p.realizes_right e

/-- Pigeonhole consequence used when one quotient factor is divisible by an
odd first radix.  The injection is built from the frozen indexed partition;
no cardinality bound is accepted as a premise. -/
theorem InternalRankPartition.nonmultiple_capacity_left
    (p : InternalRankPartition X Y M)
    {r : ℕ} (hallY : ∀ y ∈ Y, r ∣ y) :
    M - M / r ≤ X.card.choose 2 := by
  classical
  let R := (Finset.range M).filter (fun k => ¬r ∣ k + 1)
  have hleft (k : ↥R) :
      ∃ e : DepthEdge X,
        p.rankEquiv.symm ⟨(k : ℕ), (Finset.mem_range.mp
          (Finset.mem_filter.mp k.property).1)⟩ = Sum.inl e := by
    let fk : Fin M := ⟨(k : ℕ), Finset.mem_range.mp
      (Finset.mem_filter.mp k.property).1⟩
    cases hpre : p.rankEquiv.symm fk with
    | inl e =>
        refine ⟨e, ?_⟩
        simp
    | inr e =>
        have hreal := p.realizes_right e
        have hdiv := realizedInternalRank_dvd hallY hreal
        have hnot := (Finset.mem_filter.mp k.property).2
        have hfin : p.rankEquiv (Sum.inr e) = fk := by
          rw [← hpre]
          exact p.rankEquiv.apply_symm_apply fk
        have heval : (p.rankEquiv (Sum.inr e) : ℕ) = (k : ℕ) :=
          congrArg Fin.val hfin
        exact (hnot (by simpa [heval] using hdiv)).elim
  let encode : ↥R → DepthEdge X := fun k => Classical.choose (hleft k)
  have encode_spec (k : ↥R) :
      p.rankEquiv.symm ⟨(k : ℕ), Finset.mem_range.mp
        (Finset.mem_filter.mp k.property).1⟩ = Sum.inl (encode k) :=
    Classical.choose_spec (hleft k)
  have hinj : Function.Injective encode := by
    intro k l hkl
    have hpre : p.rankEquiv.symm
        ⟨(k : ℕ), Finset.mem_range.mp (Finset.mem_filter.mp k.property).1⟩ =
        p.rankEquiv.symm
        ⟨(l : ℕ), Finset.mem_range.mp (Finset.mem_filter.mp l.property).1⟩ := by
      rw [encode_spec k, encode_spec l, hkl]
    have hfin := p.rankEquiv.symm.injective hpre
    apply Subtype.ext
    exact congrArg Fin.val hfin
  have hcardle : R.card ≤ Fintype.card (DepthEdge X) := by
    simpa using Fintype.card_le_of_injective encode hinj
  have hmult : ((Finset.range M).filter (fun k => r ∣ k + 1)).card = M / r :=
    Nat.card_multiples M r
  have hRcard : R.card = M - M / r := by
    have hpartition :
        ((Finset.range M).filter (fun k => r ∣ k + 1)).card + R.card = M := by
      simpa [R] using Finset.filter_card_add_filter_neg_card_eq_card
        (s := Finset.range M) (p := fun k => r ∣ k + 1)
    rw [hmult] at hpartition
    omega
  rw [hRcard] at hcardle
  rw [card_depthEdge X] at hcardle
  exact hcardle

/-! ## One-odd necessary decomposition and parity alternatives -/

/-- Exact indexed data forced after deleting the unique odd edge and halving
all even component weights.  The graph layer must construct this object; the
obstruction below does not assume its conclusion.  `X` is oriented to be the
factor containing half-rank `1`. -/
structure OneOddDecomposition (n : ℕ) where
  N : ℕ
  C : ℕ
  M : ℕ
  leftOrder : ℕ
  rightOrder : ℕ
  X : Finset ℕ
  Y : Finset ℕ
  pair_twice : 2 * N = n * (n - 1)
  target_split : N = C + M
  target_case : C = M ∨ C = M + 1
  component_orders : leftOrder + rightOrder = n
  cross_count : leftOrder * rightOrder = C
  card_X : X.card = leftOrder
  card_Y : Y.card = rightOrder
  zero_X : 0 ∈ X
  zero_Y : 0 ∈ Y
  one_X : 1 ∈ X
  crossRanks : IntervalDirectSum X Y C
  internalRanks : InternalRankPartition X Y M
  parity_even : Even M →
    (leftOrder : ℤ) ^ 2 + (rightOrder : ℤ) ^ 2 -
      signedImbalance X ^ 2 - signedImbalance Y ^ 2 = 2 * M
  parity_odd : Odd M →
    (leftOrder : ℤ) ^ 2 + (rightOrder : ℤ) ^ 2 -
      signedImbalance X ^ 2 - signedImbalance Y ^ 2 = 2 * ((M : ℤ) + 1)

theorem OneOddDecomposition.component_nontrivial
    (d : OneOddDecomposition n) (hn : 18 ≤ n) :
    2 ≤ d.leftOrder ∧ 2 ≤ d.rightOrder := by
  have hNC : d.N ≤ 2 * d.C := by
    have hs := d.target_split
    rcases d.target_case with h | h <;> omega
  have hprod : n * (n - 1) ≤ 4 * (d.leftOrder * d.rightOrder) := by
    rw [← d.pair_twice, d.cross_count]
    omega
  constructor
  · by_contra hleft
    have hle : d.leftOrder ≤ 1 := by omega
    have hnsub : n - 1 + 1 = n := by omega
    nlinarith [d.component_orders]
  · by_contra hright
    have hle : d.rightOrder ≤ 1 := by omega
    have hnsub : n - 1 + 1 = n := by omega
    nlinarith [d.component_orders]

theorem OneOddDecomposition.positive_right_depth
    (d : OneOddDecomposition n) (hn : 18 ≤ n) :
    ∃ y ∈ d.Y, 0 < y := by
  have hcard : 1 < d.Y.card := by
    rw [d.card_Y]
    exact (d.component_nontrivial hn).2
  rcases Finset.one_lt_card_iff.mp hcard with ⟨x, y, hx, hy, hxy⟩
  by_cases hx0 : x = 0
  · exact ⟨y, hy, by omega⟩
  · exact ⟨x, hx, by omega⟩

theorem OneOddDecomposition.exists_firstRadix
    (d : OneOddDecomposition n) (hn : 18 ≤ n) :
    ∃ r : ℕ, 2 ≤ r ∧ (∀ k < r, k ∈ d.X) ∧ r ∉ d.X := by
  rcases d.positive_right_depth hn with ⟨y, hyY, hypos⟩
  have hy_not_X : y ∉ d.X := by
    intro hyX
    have hu := d.crossRanks.eq_of_sum_eq hyX d.zero_X d.zero_Y hyY (by omega)
    omega
  have hexists : ∃ k : ℕ, k ∉ d.X := ⟨y, hy_not_X⟩
  let r := Nat.find hexists
  have hrnot : r ∉ d.X := Nat.find_spec hexists
  have hbelow : ∀ k < r, k ∈ d.X := by
    intro k hk
    by_contra hnot
    have hle := Nat.find_min' hexists hnot
    omega
  have hr2 : 2 ≤ r := by
    have hrpos : 0 < r := by
      by_contra h
      have : r = 0 := by omega
      exact hrnot (this ▸ d.zero_X)
    by_contra h
    have : r = 1 := by omega
    exact hrnot (this ▸ d.one_X)
  exact ⟨r, hr2, hbelow, hrnot⟩

theorem OneOddDecomposition.gap_square_cases
    (d : OneOddDecomposition n) (hn : 1 ≤ n) :
    (((d.leftOrder : ℤ) - d.rightOrder) ^ 2 = n) ∨
    (((d.leftOrder : ℤ) - d.rightOrder) ^ 2 = (n : ℤ) - 2) := by
  have hp0 : (2 * d.N : ℤ) = (n : ℤ) * (n - 1 : ℕ) := by
    exact_mod_cast d.pair_twice
  have hn1 : 1 ≤ n := by omega
  have hnsub : ((n - 1 : ℕ) : ℤ) + 1 = n := by
    exact_mod_cast Nat.sub_add_cancel hn1
  have hp : (2 * d.N : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
    nlinarith
  have hs : (d.N : ℤ) = d.C + d.M := by exact_mod_cast d.target_split
  have ho : (d.leftOrder : ℤ) + d.rightOrder = n := by
    exact_mod_cast d.component_orders
  have hc : (d.leftOrder : ℤ) * d.rightOrder = d.C := by
    exact_mod_cast d.cross_count
  rcases d.target_case with heq | hsucc
  · left
    have heqz : (d.C : ℤ) = d.M := by exact_mod_cast heq
    nlinarith
  · right
    have hsuccz : (d.C : ℤ) = d.M + 1 := by exact_mod_cast hsucc
    nlinarith

theorem OneOddDecomposition.C_even
    (d : OneOddDecomposition n) (hn : 5 ≤ n) : Even d.C := by
  by_contra hnot
  have hCodd : Odd d.C := Nat.not_even_iff_odd.mp hnot
  have hprod := d.crossRanks.signedImbalance_mul
  simp only [hnot, if_false] at hprod
  have hdx : signedImbalance d.X ^ 2 = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hprod with h | h
    · simp [h.1]
    · simp [h.1]
  have hdy : signedImbalance d.Y ^ 2 = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hprod with h | h
    · simp [h.2]
    · simp [h.2]
  have ho : (d.leftOrder : ℤ) + d.rightOrder = n := by
    exact_mod_cast d.component_orders
  have hc : (d.leftOrder : ℤ) * d.rightOrder = d.C := by
    exact_mod_cast d.cross_count
  have hs : (d.N : ℤ) = d.C + d.M := by exact_mod_cast d.target_split
  have hp0 : (2 * d.N : ℤ) = (n : ℤ) * (n - 1 : ℕ) := by
    exact_mod_cast d.pair_twice
  have hn1 : 1 ≤ n := by omega
  have hnsub : ((n - 1 : ℕ) : ℤ) + 1 = n := by
    exact_mod_cast Nat.sub_add_cancel hn1
  have hp : (2 * d.N : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
    nlinarith
  rcases d.target_case with heq | hsucc
  · have hModd : Odd d.M := heq ▸ hCodd
    have hpar := d.parity_odd hModd
    have heqz : (d.C : ℤ) = d.M := by exact_mod_cast heq
    nlinarith
  · have hMeven : Even d.M := by
      rcases hCodd with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      omega
    have hpar := d.parity_even hMeven
    have hsuccz : (d.C : ℤ) = d.M + 1 := by exact_mod_cast hsucc
    nlinarith

theorem OneOddDecomposition.imbalance_square_sum
    (d : OneOddDecomposition n) (hC : Even d.C) :
    signedImbalance d.X ^ 2 + signedImbalance d.Y ^ 2 =
      ((d.leftOrder : ℤ) - d.rightOrder) ^ 2 := by
  have ho : (d.leftOrder : ℤ) + d.rightOrder = n := by
    exact_mod_cast d.component_orders
  have hc : (d.leftOrder : ℤ) * d.rightOrder = d.C := by
    exact_mod_cast d.cross_count
  rcases d.target_case with heq | hsucc
  · have hMeven : Even d.M := heq ▸ hC
    have hpar := d.parity_even hMeven
    nlinarith
  · have hModd : Odd d.M := by
      rcases hC with ⟨k, hk⟩
      refine ⟨k - 1, ?_⟩
      have hMpos : 0 < d.M := by
        by_contra h
        have hM0 : d.M = 0 := by omega
        have hC1 : d.C = 1 := by omega
        have hcprod := d.cross_count
        have hcards := d.crossRanks.card_mul
        omega
      omega
    have hpar := d.parity_odd hModd
    nlinarith

theorem signedImbalance_eq_card_of_even_divisor
    {S : Finset ℕ} {r : ℕ} (hr : Even r)
    (hall : ∀ x ∈ S, r ∣ x) :
    signedImbalance S = S.card := by
  unfold signedImbalance
  calc
    (∑ x ∈ S, (-1 : ℤ) ^ x) = ∑ x ∈ S, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro x hx
      rcases hall x hx with ⟨q, rfl⟩
      rw [hr.mul_right q |>.neg_one_pow]
    _ = S.card := by simp

/-- All consequences of the first repaired block that are used below.  In
particular, the capacity inequality is derived from the indexed ownership of
internal ranks, rather than stored in `OneOddDecomposition`. -/
theorem OneOddDecomposition.firstRadix_constraints
    (d : OneOddDecomposition n) (hn : 18 ≤ n)
    {r : ℕ} (hr : 0 < r)
    (hbelow : ∀ k < r, k ∈ d.X) (hrnot : r ∉ d.X) :
    r ∣ d.C ∧ r ∣ d.leftOrder ∧
      (∀ y ∈ d.Y, r ∣ y) ∧
      d.M - d.M / r ≤ d.leftOrder.choose 2 := by
  have hYpos := d.positive_right_depth hn
  have hclass := d.crossRanks.block_classification d.zero_X d.zero_Y hr
    hbelow hrnot hYpos
  have hallY : ∀ y ∈ d.Y, r ∣ y := by
    intro y hy
    have hyC : y < d.C := by simpa using d.crossRanks.sum_lt d.zero_X hy
    exact (hclass y hyC).2 hy
  have hrC := d.crossRanks.firstRadix_dvd_length d.zero_X d.zero_Y hr
    hbelow hrnot hYpos
  have hrX := d.crossRanks.firstRadix_dvd_card_left d.zero_X d.zero_Y hr
    hbelow hrnot hYpos
  have hcap := d.internalRanks.nonmultiple_capacity_left hallY
  rw [d.card_X] at hrX hcap
  exact ⟨hrC, hrX, hallY, hcap⟩

theorem OneOddDecomposition.firstRadix_not_even
    (d : OneOddDecomposition n) (hn : 18 ≤ n)
    {r : ℕ} (hr : 0 < r)
    (hbelow : ∀ k < r, k ∈ d.X) (hrnot : r ∉ d.X) :
    ¬ Even r := by
  intro hre
  have hC := d.C_even (by omega)
  have hYpos := d.positive_right_depth hn
  have hclass := d.crossRanks.block_classification d.zero_X d.zero_Y hr
    hbelow hrnot hYpos
  have hallY : ∀ y ∈ d.Y, r ∣ y := by
    intro y hy
    have hyC : y < d.C := by simpa using d.crossRanks.sum_lt d.zero_X hy
    exact (hclass y hyC).2 hy
  have hdy : signedImbalance d.Y = d.Y.card :=
    signedImbalance_eq_card_of_even_divisor hre hallY
  have hprod := d.crossRanks.signedImbalance_mul
  simp only [hC, if_pos] at hprod
  rw [hdy] at hprod
  have hcardpos : 0 < d.Y.card := Finset.card_pos.mpr ⟨0, d.zero_Y⟩
  have hcardne : (d.Y.card : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hcardpos
  have hdx : signedImbalance d.X = 0 :=
    (mul_eq_zero.mp hprod).resolve_right hcardne
  have hsum := d.imbalance_square_sum hC
  rw [hdx, hdy, d.card_Y] at hsum
  simp only [zero_pow (by decide : 2 ≠ 0), zero_add] at hsum
  have hsquares := sq_eq_sq_iff_eq_or_eq_neg.mp hsum
  have horders : (d.leftOrder : ℤ) + d.rightOrder = n := by
    exact_mod_cast d.component_orders
  have hnontriv := d.component_nontrivial hn
  have hgap := d.gap_square_cases (by omega)
  rcases hsquares with hs | hs <;> rcases hgap with hg | hg <;>
    nlinarith

theorem OneOddDecomposition.firstRadix_odd
    (d : OneOddDecomposition n) (hn : 18 ≤ n)
    {r : ℕ} (hr : 0 < r)
    (hbelow : ∀ k < r, k ∈ d.X) (hrnot : r ∉ d.X) :
    Odd r :=
  Nat.not_even_iff_odd.mp (d.firstRadix_not_even hn hr hbelow hrnot)

private theorem two_mul_choose_two (m : ℕ) :
    2 * m.choose 2 = m * (m - 1) := by
  rw [Nat.choose_two_right]
  apply Nat.mul_div_cancel'
  by_cases hm : Even m
  · rcases hm with ⟨q, hq⟩
    refine ⟨q * (m - 1), ?_⟩
    rw [hq]
    ring
  · rcases Nat.not_even_iff_odd.mp hm with ⟨q, hq⟩
    refine ⟨m * q, ?_⟩
    have hmpos : 0 < m := by omega
    have hm1 : m - 1 = q + q := by omega
    rw [hm1]
    ring

private theorem large_order_choose_bound
    {n A B C M : ℕ}
    (hn : 49 ≤ n) (_hA : 2 ≤ A) (hB : 2 ≤ B) (hAB : A ≤ B)
    (horder : A + B = n) (hcross : A * B = C)
    (htarget : C = M ∨ C = M + 1)
    (hgap : (((A : ℤ) - B) ^ 2 = n) ∨
      (((A : ℤ) - B) ^ 2 = (n : ℤ) - 2)) :
    3 * B.choose 2 < 2 * M := by
  let h := B - A
  have hh : A + h = B := by simp [h, Nat.add_sub_of_le hAB]
  have hhz : (B : ℤ) = A + h := by exact_mod_cast hh.symm
  have hhnonneg : (0 : ℤ) ≤ h := by positivity
  have hnz : (49 : ℤ) ≤ n := by exact_mod_cast hn
  have hsq : (h : ℤ) ^ 2 ≤ n := by
    rcases hgap with hg | hg <;> rw [hhz] at hg <;> nlinarith
  have hn7 : (7 : ℤ) * h ≤ n := by
    by_cases hh7 : h ≤ 7
    · have hh7z : (h : ℤ) ≤ 7 := by exact_mod_cast hh7
      nlinarith
    · have hh7z : (7 : ℤ) ≤ h := by exact_mod_cast (by omega : 7 ≤ h)
      nlinarith [mul_nonneg hhnonneg (sub_nonneg.mpr hh7z)]
  have horderz : (A : ℤ) + B = n := by exact_mod_cast horder
  have hbase : (0 : ℤ) ≤ (A : ℤ) - 3 * h := by
    nlinarith
  have hBz : (2 : ℤ) ≤ B := by exact_mod_cast hB
  have hnonneg : (0 : ℤ) ≤ (B : ℤ) * ((A : ℤ) - 3 * h) :=
    mul_nonneg (by positivity) hbase
  have hBsub : ((B - 1 : ℕ) : ℤ) = (B : ℤ) - 1 := by
    have := Nat.sub_add_cancel (by omega : 1 ≤ B)
    omega
  have hchooseNat := two_mul_choose_two B
  have hchoose : (2 : ℤ) * B.choose 2 = (B : ℤ) * ((B : ℤ) - 1) := by
    have hchoose' : (2 : ℤ) * B.choose 2 =
        (B : ℤ) * ((B - 1 : ℕ) : ℤ) := by
      exact_mod_cast hchooseNat
    rwa [hBsub] at hchoose'
  have hcrossz : (C : ℤ) = A * B := by exact_mod_cast hcross.symm
  have hid :
      (4 : ℤ) * ((A : ℤ) * B) - 3 * (B : ℤ) * ((B : ℤ) - 1) =
        (B : ℤ) * ((A : ℤ) - 3 * h + 3) := by
    rw [hhz]
    ring
  have hstrict : (3 : ℤ) * (B : ℤ) * ((B : ℤ) - 1) < 4 * M := by
    rcases htarget with heq | hsucc
    · have heqz : (M : ℤ) = C := by exact_mod_cast heq.symm
      nlinarith
    · have hsuccz : (C : ℤ) = M + 1 := by exact_mod_cast hsucc
      nlinarith
  have hfinal : (6 : ℤ) * B.choose 2 < 4 * M := by
    nlinarith
  have hfinalNat : 6 * B.choose 2 < 4 * M := by exact_mod_cast hfinal
  omega

theorem OneOddDecomposition.large_order_impossible
    (d : OneOddDecomposition n) (hn : 49 ≤ n) : False := by
  have hn18 : 18 ≤ n := by omega
  rcases d.exists_firstRadix hn18 with ⟨r, hr2, hbelow, hrnot⟩
  have hrodd := d.firstRadix_odd hn18 (by omega) hbelow hrnot
  have hr3 : 3 ≤ r := by
    rcases hrodd with ⟨q, hq⟩
    omega

  obtain ⟨hrC, hrLeft, hallY, hcap⟩ :=
    d.firstRadix_constraints hn18 (by omega) hbelow hrnot
  have hdivle : d.M / r ≤ d.M / 3 :=
    Nat.div_le_div_left hr3 (by omega)
  have hmuldiv : 3 * (d.M / 3) ≤ d.M := Nat.mul_div_le d.M 3
  have hrestore : d.M - d.M / r + d.M / r = d.M :=
    Nat.sub_add_cancel (Nat.div_le_self d.M r)
  have hlower : 2 * d.M ≤ 3 * d.leftOrder.choose 2 := by omega
  have hnontriv := d.component_nontrivial hn18
  have hgap := d.gap_square_cases (by omega)
  by_cases hle : d.leftOrder ≤ d.rightOrder
  · have hstrict := large_order_choose_bound hn hnontriv.1 hnontriv.2 hle
      d.component_orders d.cross_count d.target_case hgap
    have hmono : d.leftOrder.choose 2 ≤ d.rightOrder.choose 2 :=
      Nat.choose_mono 2 hle
    omega
  · have hle' : d.rightOrder ≤ d.leftOrder := by omega
    have hstrict := large_order_choose_bound hn hnontriv.2 hnontriv.1 hle'
      (by simpa [Nat.add_comm] using d.component_orders)
      (by simpa [Nat.mul_comm] using d.cross_count)
      d.target_case (by
        rcases hgap with hg | hg
        · left; nlinarith
        · right; nlinarith)
    omega

theorem OneOddDecomposition.residual_orders
    (d : OneOddDecomposition n) (hn : 18 ≤ n) (hn49 : n < 49) :
    n = 18 ∨ n = 25 ∨ n = 27 ∨ n = 36 ∨ n = 38 := by
  let h := Int.natAbs ((d.leftOrder : ℤ) - d.rightOrder)
  have habs := Int.natAbs_sq ((d.leftOrder : ℤ) - d.rightOrder)
  have hgap := d.gap_square_cases (by omega)
  have hsquare : h ^ 2 = n ∨ h ^ 2 = n - 2 := by
    rcases hgap with hg | hg
    · left
      have hz : ((h : ℤ) ^ 2) = n := by simpa [h] using habs.trans hg
      exact_mod_cast hz
    · right
      have hnsub : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
      have hz : ((h : ℤ) ^ 2) = (n - 2 : ℕ) := by
        rw [hnsub]
        simpa [h] using habs.trans hg
      exact_mod_cast hz
  have hh : h ≤ 6 := by
    rcases hsquare with hs | hs
    · nlinarith
    · have hrestore : n - 2 + 2 = n := Nat.sub_add_cancel (by omega)
      nlinarith
  interval_cases h <;> norm_num at hsquare <;> omega

private theorem order18_impossible (d : OneOddDecomposition 18) : False := by
  have hC := d.C_even (by norm_num)
  rcases hC with ⟨q, hq⟩
  have hp := d.pair_twice
  have hs := d.target_split
  rcases d.target_case with heq | hsucc <;> norm_num at hp <;> omega

private theorem order36_impossible (d : OneOddDecomposition 36) : False := by
  have hC := d.C_even (by norm_num)
  rcases hC with ⟨q, hq⟩
  have hp := d.pair_twice
  have hs := d.target_split
  rcases d.target_case with heq | hsucc <;> norm_num at hp <;> omega

private theorem no_rank_four_spacing15
    {X : Finset ℕ}
    (hdec : ∀ x ∈ X, ∃ i u : ℕ, u < 3 ∧ x = 15 * i + u) :
    ¬ RealizesInternalRank X 4 := by
  rintro ⟨x, hx, y, hy, hxy, z, hz, hzx, hzy, heq⟩
  rcases hdec x hx with ⟨i, p, hp, rfl⟩
  rcases hdec y hy with ⟨j, q, hq, rfl⟩
  rcases hdec z hz with ⟨k, t, ht, rfl⟩
  have hik : i = k := by omega
  have hjk : j = k := by omega
  have hpq : p = q := by omega
  apply hxy
  omega

private theorem no_rank_four_spacing30
    {X : Finset ℕ}
    (hdec : ∀ x ∈ X, ∃ i u : ℕ, u < 3 ∧ x = 30 * i + u) :
    ¬ RealizesInternalRank X 4 := by
  rintro ⟨x, hx, y, hy, hxy, z, hz, hzx, hzy, heq⟩
  rcases hdec x hx with ⟨i, p, hp, rfl⟩
  rcases hdec y hy with ⟨j, q, hq, rfl⟩
  rcases hdec z hz with ⟨k, t, ht, rfl⟩
  have hik : i = k := by omega
  have hjk : j = k := by omega
  have hpq : p = q := by omega
  apply hxy
  omega

private theorem no_rank_fiftyTwo_spacing6
    {X : Finset ℕ}
    (hdec : ∀ x ∈ X, ∃ i u : ℕ, i < 5 ∧ u < 3 ∧ x = 6 * i + u) :
    ¬ RealizesInternalRank X 52 := by
  rintro ⟨x, hx, y, hy, hxy, z, hz, hzx, hzy, heq⟩
  rcases hdec x hx with ⟨i, p, hi, hp, rfl⟩
  rcases hdec y hy with ⟨j, q, hj, hq, rfl⟩
  rcases hdec z hz with ⟨k, t, hk, ht, rfl⟩
  have hij : i = j := by omega
  have hpq : p = q := by omega
  apply hxy
  omega

private theorem no_rank_fiftyTwo_spacing30_three
    {X : Finset ℕ}
    (hdec : ∀ x ∈ X, ∃ i u : ℕ, i < 5 ∧ u < 2 ∧ x = 30 * i + 3 * u) :
    ¬ RealizesInternalRank X 52 := by
  rintro ⟨x, hx, y, hy, hxy, z, hz, hzx, hzy, heq⟩
  rcases hdec x hx with ⟨i, p, hi, hp, rfl⟩
  rcases hdec y hy with ⟨j, q, hj, hq, rfl⟩
  rcases hdec z hz with ⟨k, t, hk, ht, rfl⟩
  omega

private theorem order25_impossible (d : OneOddDecomposition 25) : False := by
  have hp := d.pair_twice
  norm_num at hp
  have hs := d.target_split
  have hvals : d.C = 150 ∧ d.M = 150 := by
    rcases d.target_case with heq | hsucc <;> omega
  have horder := d.component_orders
  have hcross := d.cross_count
  rw [hvals.1] at hcross
  have hleftle : d.leftOrder ≤ 25 := by omega
  have hord : d.leftOrder = 10 ∨ d.leftOrder = 15 := by
    interval_cases d.leftOrder <;> norm_num at hcross <;> omega
  rcases d.exists_firstRadix (by norm_num) with ⟨r, hr2, hbelow, hrnot⟩
  have hrodd := d.firstRadix_odd (by norm_num) (by omega) hbelow hrnot
  obtain ⟨hrC, hrLeft, hallY, hcap⟩ :=
    d.firstRadix_constraints (by norm_num) (by omega) hbelow hrnot
  rw [hvals.1] at hrC
  rw [hvals.2] at hcap
  rcases hord with hord | hord
  · rw [hord] at hrLeft hcap
    have hrle : r ≤ 10 := Nat.le_of_dvd (by omega) hrLeft
    interval_cases r <;> norm_num [Nat.choose_two_right] at *
  · have hright : d.rightOrder = 10 := by omega
    rw [hord] at hrLeft hcap
    have hrle : r ≤ 15 := Nat.le_of_dvd (by omega) hrLeft
    have hr_eq : r = 3 := by
      interval_cases r <;> norm_num [Nat.choose_two_right] at *
    subst r
    have hclass3 := d.crossRanks.block_classification d.zero_X d.zero_Y
      (by norm_num : 0 < 3) hbelow hrnot (d.positive_right_depth (by norm_num))
    rcases d.crossRanks.firstRadix_quotient d.zero_X d.zero_Y
        (by norm_num : 0 < 3) hbelow hrnot
        (d.positive_right_depth (by norm_num)) with
      ⟨P, Q, hPQ, hXPcard, hYQcard, hPmem, hQmem⟩
    have hPQ50 : IntervalDirectSum P Q 50 := by
      simpa [hvals.1] using hPQ
    have hPcard : P.card = 5 := by
      have hxcard := d.card_X
      rw [hord] at hxcard
      omega
    have hQcard : Q.card = 10 := by
      have hycard := d.card_Y
      rw [hright] at hycard
      omega
    have hP0 : 0 ∈ P := by
      apply (hPmem 0).2
      constructor
      · simp [hvals.1]
      · simpa using d.zero_X
    have hQ0 : 0 ∈ Q := by
      apply (hQmem 0).2
      constructor
      · simp [hvals.1]
      · simpa using d.zero_Y
    have hP1not : 1 ∉ P := by
      intro hP1
      exact hrnot ((hPmem 1).1 hP1).2
    have hQ1 : 1 ∈ Q := by
      rcases hPQ50.exists_repr (by norm_num : 1 < 50) with
        ⟨p, hpP, q, hqQ, hpq⟩
      by_cases hp0 : p = 0
      · have hq1 : q = 1 := by omega
        simpa [hq1] using hqQ
      · have hp1 : p = 1 := by omega
        exact (hP1not (hp1 ▸ hpP)).elim
    have hPpos : ∃ p ∈ P, 0 < p :=
      Finset.exists_pos_of_one_lt_card (by rw [hPcard]; norm_num)
    let hQP : IntervalDirectSum Q P 50 := hPQ50.comm
    rcases hQP.exists_firstRadix hQ0 hP0 hQ1 hPpos with
      ⟨s, hs2, hsbelow, hsnot⟩
    have hspos : 0 < s := by omega
    have hclassS := hQP.block_classification hQ0 hP0 hspos hsbelow hsnot hPpos
    have hsCard := hQP.firstRadix_dvd_card_left hQ0 hP0 hspos
      hsbelow hsnot hPpos
    rw [hQcard] at hsCard
    have hsle : s ≤ 10 := Nat.le_of_dvd (by norm_num) hsCard
    have hsCases : s = 2 ∨ s = 5 ∨ s = 10 := by
      rcases hsCard with ⟨v, hv⟩
      interval_cases s <;> omega
    have hallP : ∀ p ∈ P, s ∣ p := by
      intro p hpP
      have hp50 : p < 50 := by simpa using hQP.sum_lt hQ0 hpP
      exact (hclassS p hp50).2 hpP
    have hXdec : ∀ x ∈ d.X,
        ∃ i u : ℕ, u < 3 ∧ x = 3 * s * i + u := by
      intro x hx
      have hxC : x < d.C := by simpa using d.crossRanks.sum_lt hx d.zero_Y
      have hboundary := (hclass3 x hxC).1.mp hx
      have hqbound : x / 3 < d.C / 3 := by
        rw [hvals.1]
        omega
      have hqP := (hPmem (x / 3)).2 ⟨hqbound, hboundary⟩
      rcases hallP (x / 3) hqP with ⟨i, hi⟩
      refine ⟨i, x % 3, Nat.mod_lt x (by norm_num), ?_⟩
      have hdivmod := Nat.div_add_mod x 3
      calc
        x = 3 * (x / 3) + x % 3 := hdivmod.symm
        _ = 3 * (s * i) + x % 3 := by rw [hi]
        _ = 3 * s * i + x % 3 := by ring
    rcases hsCases with rfl | rfl | rfl
    · have hQP25data := hQP.firstRadix_quotient hQ0 hP0
          (by norm_num : 0 < 2) hsbelow hsnot hPpos
      rcases hQP25data with
        ⟨Q₁, P₁, hQ₁P₁, hQQ₁card, hPP₁card, hQ₁mem, hP₁mem⟩
      have hQ₁P₁25 : IntervalDirectSum Q₁ P₁ 25 := by
        simpa using hQ₁P₁
      have hQ₁card : Q₁.card = 5 := by omega
      have hP₁card : P₁.card = 5 := by omega
      have hQ₁0 : 0 ∈ Q₁ := by
        apply (hQ₁mem 0).2
        exact ⟨by norm_num, by simpa using hQ0⟩
      have hP₁0 : 0 ∈ P₁ := by
        apply (hP₁mem 0).2
        exact ⟨by norm_num, by simpa using hP0⟩
      have hQ₁1not : 1 ∉ Q₁ := by
        intro h
        exact hsnot ((hQ₁mem 1).1 h).2
      have hP₁1 : 1 ∈ P₁ := by
        rcases hQ₁P₁25.exists_repr (by norm_num : 1 < 25) with
          ⟨q, hq, p, hp', heq⟩
        by_cases hq0 : q = 0
        · have hp1 : p = 1 := by omega
          simpa [hp1] using hp'
        · have hq1 : q = 1 := by omega
          exact (hQ₁1not (hq1 ▸ hq)).elim
      have hQ₁pos : ∃ q ∈ Q₁, 0 < q :=
        Finset.exists_pos_of_one_lt_card (by rw [hQ₁card]; norm_num)
      let hP₁Q₁ : IntervalDirectSum P₁ Q₁ 25 := hQ₁P₁25.comm
      rcases hP₁Q₁.exists_firstRadix hP₁0 hQ₁0 hP₁1 hQ₁pos with
        ⟨t, ht2, htbelow, htnot⟩
      have htpos : 0 < t := by omega
      have htCard := hP₁Q₁.firstRadix_dvd_card_left hP₁0 hQ₁0
        htpos htbelow htnot hQ₁pos
      rw [hP₁card] at htCard
      have htle : t ≤ 5 := Nat.le_of_dvd (by norm_num) htCard
      have hteq : t = 5 := by
        rcases htCard with ⟨v, hv⟩
        interval_cases t <;> omega
      subst t
      have hclassT := hP₁Q₁.block_classification hP₁0 hQ₁0
        (by norm_num : 0 < 5) htbelow htnot hQ₁pos
      have hallQ₁ : ∀ q ∈ Q₁, 5 ∣ q := by
        intro q hq
        have hq25 : q < 25 := by simpa using hP₁Q₁.sum_lt hP₁0 hq
        exact (hclassT q hq25).2 hq
      have hRangeP₁ : Finset.range 5 = P₁ := by
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          exact htbelow x (Finset.mem_range.mp hx)
        · simp [hP₁card]
      have hdecX6 : ∀ x ∈ d.X,
          ∃ i u : ℕ, i < 5 ∧ u < 3 ∧ x = 6 * i + u := by
        intro x hx
        rcases hXdec x hx with ⟨i, u, hu, hxu⟩
        have hiP : 2 * i ∈ P := by
          have hxC : x < d.C := by simpa using d.crossRanks.sum_lt hx d.zero_Y
          have hb := (hclass3 x hxC).1.mp hx
          have hqi : x / 3 = 2 * i := by omega
          have := (hPmem (x / 3)).2
            ⟨by rw [hvals.1]; omega, hb⟩
          simpa [hqi] using this
        have hi25 : i < 25 := by
          have h2i50 := hPQ50.sum_lt hiP hQ0
          omega
        have hiP₁ : i ∈ P₁ := (hP₁mem i).2 ⟨hi25, hiP⟩
        have hi5 : i < 5 := by
          apply Finset.mem_range.mp
          rw [hRangeP₁]
          exact hiP₁
        exact ⟨i, u, hi5, hu, by omega⟩
      have hdecY30 : ∀ y ∈ d.Y,
          ∃ i u : ℕ, i < 5 ∧ u < 2 ∧ y = 30 * i + 3 * u := by
        intro y hy
        rcases hallY y hy with ⟨q, hq⟩
        have hqBound : q < d.C / 3 := by
          have hyC : y < d.C := by simpa using d.crossRanks.sum_lt d.zero_X hy
          rw [hq] at hyC
          rw [hvals.1] at hyC ⊢
          norm_num at hyC ⊢
          omega
        have hqQ : q ∈ Q := by
          apply (hQmem q).2
          constructor
          · exact hqBound
          · rw [← hq]
            exact hy
        let u := q % 2
        let q₁ := q / 2
        have hu : u < 2 := Nat.mod_lt q (by norm_num)
        have hq50 : q < 50 := by simpa using hPQ50.sum_lt hP0 hqQ
        have hboundary := (hclassS q hq50).1.mp hqQ
        have hq₁mem : q₁ ∈ Q₁ := by
          apply (hQ₁mem q₁).2
          exact ⟨by omega, by simpa [q₁] using hboundary⟩
        rcases hallQ₁ q₁ hq₁mem with ⟨i, hi⟩
        have hi5 : i < 5 := by omega
        refine ⟨i, u, hi5, hu, ?_⟩
        have hdivmod := Nat.div_add_mod q 2
        dsimp [q₁, u] at hi ⊢
        rw [hi] at hdivmod
        omega
      rcases d.internalRanks.realizes_either (k := 51) (by
          rw [hvals.2]; norm_num) with hleft | hright'
      · exact no_rank_fiftyTwo_spacing6 hdecX6 hleft
      · exact no_rank_fiftyTwo_spacing30_three hdecY30 hright'
    · have hdec15 : ∀ x ∈ d.X,
          ∃ i u : ℕ, u < 3 ∧ x = 15 * i + u := by
        intro x hx
        rcases hXdec x hx with ⟨i, u, hu, heq⟩
        exact ⟨i, u, hu, by omega⟩
      rcases d.internalRanks.realizes_either (k := 3) (by
          rw [hvals.2]; norm_num) with hleft | hright'
      · exact no_rank_four_spacing15 hdec15 hleft
      · have hdiv := realizedInternalRank_dvd hallY hright'
        norm_num at hdiv
    · have hdec30 : ∀ x ∈ d.X,
          ∃ i u : ℕ, u < 3 ∧ x = 30 * i + u := by
        intro x hx
        rcases hXdec x hx with ⟨i, u, hu, heq⟩
        exact ⟨i, u, hu, by omega⟩
      rcases d.internalRanks.realizes_either (k := 3) (by
          rw [hvals.2]; norm_num) with hleft | hright'
      · exact no_rank_four_spacing30 hdec30 hleft
      · have hdiv := realizedInternalRank_dvd hallY hright'
        norm_num at hdiv

private theorem order27_impossible (d : OneOddDecomposition 27) : False := by
  have hp := d.pair_twice
  norm_num at hp
  have hs := d.target_split
  have hvals : d.C = 176 ∧ d.M = 175 := by
    rcases d.target_case with heq | hsucc <;> omega
  have horder := d.component_orders
  have hcross := d.cross_count
  rw [hvals.1] at hcross
  have hleftle : d.leftOrder ≤ 27 := by omega
  have hord : d.leftOrder = 11 ∨ d.leftOrder = 16 := by
    interval_cases d.leftOrder <;> norm_num at hcross <;> omega
  rcases d.exists_firstRadix (by norm_num) with ⟨r, hr2, hbelow, hrnot⟩
  have hrodd := d.firstRadix_odd (by norm_num) (by omega) hbelow hrnot
  obtain ⟨hrC, hrLeft, hallY, hcap⟩ :=
    d.firstRadix_constraints (by norm_num) (by omega) hbelow hrnot
  rw [hvals.1] at hrC
  rw [hvals.2] at hcap
  rcases hord with hord | hord
  · rw [hord] at hrLeft hcap
    have hrle : r ≤ 11 := Nat.le_of_dvd (by omega) hrLeft
    interval_cases r <;> norm_num [Nat.choose_two_right] at *
  · rw [hord] at hrLeft hcap
    have hrle : r ≤ 16 := Nat.le_of_dvd (by omega) hrLeft
    interval_cases r <;> norm_num [Nat.choose_two_right] at *

private theorem order38_impossible (d : OneOddDecomposition 38) : False := by
  have hp := d.pair_twice
  norm_num at hp
  have hs := d.target_split
  have hvals : d.C = 352 ∧ d.M = 351 := by
    rcases d.target_case with heq | hsucc <;> omega
  have horder := d.component_orders
  have hcross := d.cross_count
  rw [hvals.1] at hcross
  have hleftle : d.leftOrder ≤ 38 := by omega
  have hord : d.leftOrder = 16 ∨ d.leftOrder = 22 := by
    interval_cases d.leftOrder <;> norm_num at hcross <;> omega
  rcases d.exists_firstRadix (by norm_num) with ⟨r, hr2, hbelow, hrnot⟩
  have hrodd := d.firstRadix_odd (by norm_num) (by omega) hbelow hrnot
  obtain ⟨hrC, hrLeft, hallY, hcap⟩ :=
    d.firstRadix_constraints (by norm_num) (by omega) hbelow hrnot
  rw [hvals.1] at hrC
  rw [hvals.2] at hcap
  rcases hord with hord | hord
  · rw [hord] at hrLeft hcap
    have hrle : r ≤ 16 := Nat.le_of_dvd (by omega) hrLeft
    interval_cases r <;> norm_num [Nat.choose_two_right] at *
  · rw [hord] at hrLeft hcap
    have hrle : r ≤ 22 := Nat.le_of_dvd (by omega) hrLeft
    interval_cases r <;> norm_num [Nat.choose_two_right] at *

/-- T11's complete decomposition-level obstruction.  This includes the
large-order argument, all five residual orders, the repaired terminal-block
step, and the three exhaustive order-25 quotient cases. -/
theorem oneOddDecomposition_impossible
    {n : ℕ} (hn : 18 ≤ n) (d : OneOddDecomposition n) : False := by
  by_cases hn49 : 49 ≤ n
  · exact d.large_order_impossible hn49
  · have hnlt : n < 49 := by omega
    rcases d.residual_orders hn hnlt with
      h18 | h25 | h27 | h36 | h38
    · subst n
      exact order18_impossible d
    · subst n
      exact order25_impossible d
    · subst n
      exact order27_impossible d
    · subst n
      exact order36_impossible d
    · subst n
      exact order38_impossible d

/-! The central pinned project intentionally has no concrete weighted-tree
type.  Consequently the graph adapter is exposed as a named proposition,
separate from the proved kernel.  It asks only for the decomposition data and
does not contain T11's negative conclusion. -/

def OneOddGraphToDecompositionBridge
    {Tree : Type*} (order : Tree → ℕ)
    (IsLeech ExactlyOneOddPhysicalEdge : Tree → Prop) : Prop :=
  ∀ T, IsLeech T → ExactlyOneOddPhysicalEdge T →
    Nonempty (OneOddDecomposition (order T))

theorem t11_of_oneOddGraphToDecompositionBridge
    {Tree : Type*} (order : Tree → ℕ)
    (IsLeech ExactlyOneOddPhysicalEdge : Tree → Prop)
    (bridge : OneOddGraphToDecompositionBridge order IsLeech
      ExactlyOneOddPhysicalEdge) :
    ∀ T, IsLeech T → 18 ≤ order T → ¬ ExactlyOneOddPhysicalEdge T := by
  intro T hLeech hn hOne
  rcases bridge T hLeech hOne with ⟨d⟩
  exact oneOddDecomposition_impossible hn d

/-! ## Integer square gaps used by the exact two-odd theorem -/

private theorem abs_sq (z : ℤ) : |z| ^ 2 = z ^ 2 := by
  simp [pow_two]

theorem no_square_gap_three
    {s z : ℤ} (hs : 5 ≤ s ^ 2) : s ^ 2 - z ^ 2 ≠ 3 := by
  intro hgap
  have hzlt : z ^ 2 < s ^ 2 := by omega
  have habslt : |z| < |s| := (sq_lt_sq.mp hzlt)
  have hsabs : 3 ≤ |s| := by
    by_contra h
    have hle : |s| ≤ 2 := by omega
    have hnonneg : 0 ≤ |s| := abs_nonneg s
    have hp : 0 ≤ (2 - |s|) * (2 + |s|) :=
      mul_nonneg (by omega) (by omega)
    have hsq := abs_sq s
    nlinarith
  have hdiff : 5 ≤ |s| ^ 2 - |z| ^ 2 := by
    have hzn : 0 ≤ |z| := abs_nonneg z
    by_cases hzsmall : |z| ≤ 1
    · have hp1 : 0 ≤ (|s| - 3) * (|s| + 3) :=
        mul_nonneg (by omega) (by omega)
      have hp2 : 0 ≤ (1 - |z|) * (1 + |z|) :=
        mul_nonneg (by omega) (by omega)
      nlinarith
    · have hp : 0 ≤ (|s| - |z| - 1) * (|s| + |z|) :=
        mul_nonneg (by omega) (by omega)
      nlinarith
  rw [abs_sq s, abs_sq z] at hdiff
  omega

theorem no_consecutive_nonzero_squares
    {s z : ℤ} (hs : 1 ≤ s ^ 2) : z ^ 2 ≠ s ^ 2 + 1 := by
  intro hgap
  have hslt : s ^ 2 < z ^ 2 := by omega
  have habslt : |s| < |z| := sq_lt_sq.mp hslt
  have hdiff : 3 ≤ |z| ^ 2 - |s| ^ 2 := by
    have hsabs : 1 ≤ |s| := by
      by_contra h
      have hsnonneg : 0 ≤ |s| := abs_nonneg s
      have : |s| = 0 := by omega
      have hzero : s = 0 := abs_eq_zero.mp this
      simp [hzero] at hs
    have hp : 0 ≤ (|z| - |s| - 1) * (|z| + |s|) :=
      mul_nonneg (by omega) (by positivity)
    nlinarith
  rw [abs_sq z, abs_sq s] at hdiff
  omega

/-! ## Exact Gaussian algebra for two odd physical edges -/

/-- The decomposition-level data produced by the arbitrary-port two-odd
quotient identities after coefficientwise evaluation at `-1`.

`order_case` is Taylor's parity consequence; `odd_eval` and the two
`gaussian_*` fields are the two independently derived quotient evaluations.
None of these fields assumes the desired conclusion `Even O`. -/
structure TwoOddGaussianData (n O E : ℕ) where
  s : ℤ
  xi : ℤ
  eta : ℤ
  chi : ℤ
  order_case :
    ((n : ℤ) = s ^ 2 ∧ O = E) ∨
    ((n : ℤ) = s ^ 2 + 2 ∧ O = E + 1)
  odd_eval : Odd O → eta * (xi + chi) = 1
  gaussian_even : Even E → (xi - chi) ^ 2 + eta ^ 2 = n
  gaussian_odd : Odd E → (xi - chi) ^ 2 + eta ^ 2 = (n : ℤ) - 2

theorem twoOdd_oddTargetCount_even
    {n O E : ℕ} (hn : 5 ≤ n) (d : TwoOddGaussianData n O E) :
    Even O := by
  by_contra hnot
  have hOodd : Odd O := Nat.not_even_iff_odd.mp hnot
  have hprod := d.odd_eval hOodd
  have heta : d.eta ^ 2 = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hprod with h | h
    · simp [h.1]
    · simp [h.1]
  rcases d.order_case with hsq | hsq2
  · have hEodd : Odd E := hsq.2 ▸ hOodd
    have hg := d.gaussian_odd hEodd
    have hnz : (n : ℤ) = d.s ^ 2 := by exact_mod_cast hsq.1
    have hslarge : 5 ≤ d.s ^ 2 := by omega
    exact (no_square_gap_three (s := d.s) (z := d.xi - d.chi) hslarge) (by
      nlinarith)
  · have hEeven : Even E := by
      rcases hOodd with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      omega
    have hg := d.gaussian_even hEeven
    have hspos : 1 ≤ d.s ^ 2 := by omega
    exact (no_consecutive_nonzero_squares
      (s := d.s) (z := d.xi - d.chi) hspos) (by nlinarith)

/-- Separately named graph-to-Gaussian adapter obligation for T12.  Its
conclusion is the exact coefficient-evaluation data, not the desired parity
statement. -/
def TwoOddGraphToGaussianBridge
    {Tree : Type*} (order oddTargetCount evenTargetCount : Tree → ℕ)
    (IsLeech ExactlyTwoOddPhysicalEdges : Tree → Prop) : Prop :=
  ∀ T, IsLeech T → ExactlyTwoOddPhysicalEdges T →
    Nonempty (TwoOddGaussianData (order T) (oddTargetCount T)
      (evenTargetCount T))

theorem t12_of_twoOddGraphToGaussianBridge
    {Tree : Type*} (order oddTargetCount evenTargetCount : Tree → ℕ)
    (IsLeech ExactlyTwoOddPhysicalEdges : Tree → Prop)
    (bridge : TwoOddGraphToGaussianBridge order oddTargetCount
      evenTargetCount IsLeech ExactlyTwoOddPhysicalEdges) :
    ∀ T, IsLeech T → 5 ≤ order T → ExactlyTwoOddPhysicalEdges T →
      Even (oddTargetCount T) := by
  intro T hLeech hn hTwo
  rcases bridge T hLeech hTwo with ⟨d⟩
  exact twoOdd_oddTargetCount_even hn d

/-! ## The physical-weight-two parity corollary -/

def oddPhysicalEdges {Edge : Type*} [Fintype Edge]
    (weight : Edge → ℕ) : Finset Edge :=
  Finset.univ.filter (fun e => Odd (weight e))

theorem oddPhysicalEdgeCount_ne_edgeCount_of_weight_two
    {Edge : Type*} [Fintype Edge] [DecidableEq Edge]
    (weight : Edge → ℕ)
    (physical_two : ∃ e, weight e = 2) :
    (oddPhysicalEdges weight).card ≠ Fintype.card Edge := by
  rintro hcard
  have hall : oddPhysicalEdges weight = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa [oddPhysicalEdges] using hcard
  rcases physical_two with ⟨e, he⟩
  have heodd : Odd (weight e) := by
    have : e ∈ oddPhysicalEdges weight := by rw [hall]; simp
    simpa [oddPhysicalEdges] using this
  rw [he] at heodd
  norm_num at heodd

theorem order18_oddPhysicalEdgeCount_ne_seventeen
    {Edge : Type*} [Fintype Edge] [DecidableEq Edge]
    (weight : Edge → ℕ)
    (edge_count : Fintype.card Edge = 17)
    (physical_two : ∃ e, weight e = 2) :
    (oddPhysicalEdges weight).card ≠ 17 := by
  intro h
  apply oddPhysicalEdgeCount_ne_edgeCount_of_weight_two weight physical_two
  omega

end LeechTrees.OddEdges
