import LeechTrees.ParityTailExactBundle

/-!
# Punctured path-segment blocks and direct-sum statistics

The graph lemmas identify the exact intersection of a selected path block with
the physical weights.  The abstract ordered block then proves the two-sided
order-statistic inequalities without replacing indexed distances by a support
set.  The final section records the exact direct-sum variance identity.
-/

open scoped BigOperators

namespace LeechTrees.PathMulticut

open LeechTrees.Foundation
open LeechTrees.ParityTail.GraphAdapterV1

noncomputable section

/-! ## Actual graph-level puncturing -/

/-- The physical weight set, with multiplicity safely irrelevant because a
Leech tree has injective physical weights. -/
def physicalWeightSet {n : ℕ} (T : PosIntTree n) : Finset ℕ :=
  Finset.univ.image T.weight

/-- The distance values of all indexed vertex pairs whose path contains every
edge of `F`. -/
def selectedPathDistanceSet {n : ℕ} (T : PosIntTree n)
    (F : Finset T.Edge) : Finset ℕ :=
  (pathSupport T F).image T.pairDist

/-- Distinct physical edges have distinct indexed endpoint pairs, independently
of any spectrum hypothesis. -/
theorem edgePair_injective {n : ℕ} (T : PosIntTree n) :
    Function.Injective T.edgePair := by
  intro e f h
  apply Subtype.ext
  rw [T.edge_eq_mk_endpoints e, T.edge_eq_mk_endpoints f]
  have hl : T.edgeLeft e = T.edgeLeft f := by
    simpa using congrArg VertexPair.left h
  have hr : T.edgeRight e = T.edgeRight f := by
    simpa using congrArg VertexPair.right h
  rw [hl, hr]

@[simp] theorem weight_mem_physicalWeightSet {n : ℕ} (T : PosIntTree n)
    (e : T.Edge) : T.weight e ∈ physicalWeightSet T := by
  classical
  exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩

/-- If an actual selected-path distance is also a physical weight, its indexed
pair is the endpoint pair of that physical edge. -/
theorem pair_eq_edgePair_of_selected_distance_eq_weight {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) {F : Finset T.Edge}
    {p : VertexPair n} (_hp : p ∈ pathSupport T F) {e : T.Edge}
    (hpe : T.pairDist p = T.weight e) :
    p = T.edgePair e := by
  apply hL.pairDist_injective
  simpa using hpe

/-- Exact one-edge puncture: a cut block meets the physical weights in the
weight of that edge and no other physical weight. -/
theorem singleton_selectedPathDistance_inter_physical {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) (e : T.Edge) :
    selectedPathDistanceSet T {e} ∩ physicalWeightSet T = {T.weight e} := by
  classical
  apply Finset.ext
  intro w
  constructor
  · intro hw
    obtain ⟨hblock, hphysical⟩ := Finset.mem_inter.mp hw
    obtain ⟨p, hp, hpw⟩ := Finset.mem_image.mp hblock
    obtain ⟨f, hf, hfw⟩ := Finset.mem_image.mp hphysical
    have hpf : p = T.edgePair f :=
      pair_eq_edgePair_of_selected_distance_eq_weight hL hp (hpw.trans hfw.symm)
    have hepath : e.1 ∈ T.pathEdges (T.edgeLeft f) (T.edgeRight f) := by
      simpa [pathSupport, hpf] using hp
    rw [T.pathEdges_edge f] at hepath
    have hef : e = f := Subtype.ext (Finset.mem_singleton.mp hepath)
    subst f
    simpa [hpf] using hpw.symm
  · intro hw
    have hw' : w = T.weight e := Finset.mem_singleton.mp hw
    subst w
    apply Finset.mem_inter.mpr
    constructor
    · apply Finset.mem_image.mpr
      refine ⟨T.edgePair e, ?_, T.edgePair_dist e⟩
      simp [pathSupport, T.pathEdges_edge e]
    · exact weight_mem_physicalWeightSet T e

/-- A selected path block containing at least two physical edges contains no
physical weight at all.  This is the graph-level form of the multi-edge
puncture, with no assumption that the support is nonempty. -/
theorem selectedPathDistance_inter_physical_eq_empty_of_two_le {n : ℕ}
    {T : PosIntTree n} (hL : IsLeech T) {F : Finset T.Edge}
    (hF : 2 ≤ F.card) :
    selectedPathDistanceSet T F ∩ physicalWeightSet T = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨hblock, hphysical⟩ := Finset.mem_inter.mp hw
  obtain ⟨p, hp, hpw⟩ := Finset.mem_image.mp hblock
  obtain ⟨e, he, hew⟩ := Finset.mem_image.mp hphysical
  have hpeq : p = T.edgePair e :=
    pair_eq_edgePair_of_selected_distance_eq_weight hL hp (hpw.trans hew.symm)
  have hsubset : F ⊆ {e} := by
    intro f hf
    have hfpath : f.1 ∈ T.pathEdges (T.edgeLeft e) (T.edgeRight e) := by
      have hfpath' := (Finset.mem_filter.mp hp).2 f hf
      simpa [hpeq] using hfpath'
    rw [T.pathEdges_edge e] at hfpath
    exact Finset.mem_singleton.mpr (Subtype.ext (Finset.mem_singleton.mp hfpath))
  have hcard : F.card ≤ 1 := by
    simpa using Finset.card_le_card hsubset
  omega

/-! ## Generic order statistics of the punctured direct-sum block -/

/-- A sorted, multiplicity-preserving path block embedded into a sorted list
of eligible punctured ranks.  `place` records the actual rank occupied by each
indexed pair; its injectivity is the spectrum-uniqueness input. -/
structure OrderedPuncturedBlock (a b M : ℕ) where
  leftDepth : Fin a → ℕ
  rightDepth : Fin b → ℕ
  eligibleOffset : Fin M → ℕ
  place : Fin a × Fin b ↪ Fin M
  left_strict : StrictMono leftDepth
  right_strict : StrictMono rightDepth
  eligible_strict : StrictMono eligibleOffset
  place_value : ∀ z, eligibleOffset (place z) = leftDepth z.1 + rightDepth z.2

/-- If `q` distinct positions of a strictly increasing rank list have value at
most `v`, then its `(q-1)`st entry is at most `v`. -/
theorem ordered_lower_of_many_le {M : ℕ} (rank : Fin M → ℕ)
    (hrank : StrictMono rank) {α : Type*} [DecidableEq α]
    (place : α ↪ Fin M) (s : Finset α) (v : ℕ)
    (hpos : 0 < s.card) (hfit : s.card ≤ M)
    (hle : ∀ x ∈ s, rank (place x) ≤ v) :
    rank ⟨s.card - 1, by omega⟩ ≤ v := by
  classical
  by_contra hnot
  have hvlt : v < rank ⟨s.card - 1, by omega⟩ := Nat.lt_of_not_ge hnot
  let q : Fin M := ⟨s.card - 1, by omega⟩
  have hsub : s.image place ⊆ Finset.Iio q := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [Finset.mem_Iio]
    exact hrank.lt_iff_lt.mp (lt_of_le_of_lt (hle x hx) hvlt)
  have hcardImage : (s.image place).card = s.card :=
    Finset.card_image_of_injective s place.injective
  have hcard := Finset.card_le_card hsub
  rw [hcardImage] at hcard
  simp [q] at hcard
  omega

/-- Dual order-statistic lemma from `q` distinct positions at least `v`. -/
theorem ordered_upper_of_many_ge {M : ℕ} (rank : Fin M → ℕ)
    (hrank : StrictMono rank) {α : Type*} [DecidableEq α]
    (place : α ↪ Fin M) (s : Finset α) (v : ℕ)
    (hpos : 0 < s.card) (hfit : s.card ≤ M)
    (hge : ∀ x ∈ s, v ≤ rank (place x)) :
    v ≤ rank ⟨M - s.card, by omega⟩ := by
  classical
  by_contra hnot
  have hvlt : rank ⟨M - s.card, by omega⟩ < v := Nat.lt_of_not_ge hnot
  let q : Fin M := ⟨M - s.card, by omega⟩
  have hsub : s.image place ⊆ Finset.Ioi q := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [Finset.mem_Ioi]
    exact hrank.lt_iff_lt.mp (lt_of_lt_of_le hvlt (hge x hx))
  have hcardImage : (s.image place).card = s.card :=
    Finset.card_image_of_injective s place.injective
  have hcard := Finset.card_le_card hsub
  rw [hcardImage] at hcard
  simp [q] at hcard
  omega

/-- The southwest/northeast rectangle bounds of formula (8), with the exact
zero-based indices from the research note. -/
theorem OrderedPuncturedBlock.rectangle_order_statistics
    {a b M : ℕ} (B : OrderedPuncturedBlock a b M)
    (hfit : a * b ≤ M) (i : Fin a) (j : Fin b) :
      B.eligibleOffset
        ⟨(i.1 + 1) * (j.1 + 1) - 1, by
          have hi : i.1 + 1 ≤ a := Nat.succ_le_iff.mpr i.2
          have hj : j.1 + 1 ≤ b := Nat.succ_le_iff.mpr j.2
          have hprod : (i.1 + 1) * (j.1 + 1) ≤ M :=
            (Nat.mul_le_mul hi hj).trans hfit
          have hprodPos : 0 < (i.1 + 1) * (j.1 + 1) :=
            Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
          omega⟩ ≤
      B.leftDepth i + B.rightDepth j ∧
    B.leftDepth i + B.rightDepth j ≤
      B.eligibleOffset
        ⟨M - ((a - i.1) * (b - j.1)), by
          have hi : 0 < a - i.1 := Nat.sub_pos_of_lt i.2
          have hj : 0 < b - j.1 := Nat.sub_pos_of_lt j.2
          have hab : 0 < (a - i.1) * (b - j.1) := Nat.mul_pos hi hj
          have hle : (a - i.1) * (b - j.1) ≤ a * b :=
            Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
          omega⟩ := by
  classical
  let southwest : Finset (Fin a × Fin b) := Finset.Iic i ×ˢ Finset.Iic j
  let northeast : Finset (Fin a × Fin b) := Finset.Ici i ×ˢ Finset.Ici j
  have hsCard : southwest.card = (i.1 + 1) * (j.1 + 1) := by
    simp [southwest]
  have hnCard : northeast.card = (a - i.1) * (b - j.1) := by
    simp [northeast]
  have hsPos : 0 < southwest.card := by simp [hsCard]
  have hnPos : 0 < northeast.card := by
    rw [hnCard]
    exact Nat.mul_pos (Nat.sub_pos_of_lt i.2) (Nat.sub_pos_of_lt j.2)
  have hsFit : southwest.card ≤ M := by
    rw [hsCard]
    have hi : i.1 + 1 ≤ a := Nat.succ_le_iff.mpr i.2
    have hj : j.1 + 1 ≤ b := Nat.succ_le_iff.mpr j.2
    exact (Nat.mul_le_mul hi hj).trans hfit
  have hnFit : northeast.card ≤ M := by
    rw [hnCard]
    exact (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)).trans hfit
  have hsLe : ∀ z ∈ southwest,
      B.eligibleOffset (B.place z) ≤ B.leftDepth i + B.rightDepth j := by
    intro z hz
    rw [B.place_value]
    obtain ⟨hz1, hz2⟩ := Finset.mem_product.mp hz
    exact Nat.add_le_add
      (B.left_strict.monotone (Finset.mem_Iic.mp hz1))
      (B.right_strict.monotone (Finset.mem_Iic.mp hz2))
  have hnGe : ∀ z ∈ northeast,
      B.leftDepth i + B.rightDepth j ≤ B.eligibleOffset (B.place z) := by
    intro z hz
    rw [B.place_value]
    obtain ⟨hz1, hz2⟩ := Finset.mem_product.mp hz
    exact Nat.add_le_add
      (B.left_strict.monotone (Finset.mem_Ici.mp hz1))
      (B.right_strict.monotone (Finset.mem_Ici.mp hz2))
  constructor
  · have h := ordered_lower_of_many_le B.eligibleOffset B.eligible_strict
      B.place southwest (B.leftDepth i + B.rightDepth j) hsPos hsFit hsLe
    simpa [hsCard] using h
  · have h := ordered_upper_of_many_ge B.eligibleOffset B.eligible_strict
      B.place northeast (B.leftDepth i + B.rightDepth j) hnPos hnFit hnGe
    simpa [hnCard] using h

/-! ## Exact direct-sum variance -/

/-- Integer numerator of the variance of an indexed finite family. -/
def indexedDelta {α : Type*} [Fintype α] (x : α → ℤ) : ℤ :=
  (Fintype.card α : ℤ) * (∑ i, (x i) ^ 2) - (∑ i, x i) ^ 2

/-- Pairwise-difference presentation of twice the variance numerator. -/
theorem two_mul_indexedDelta_eq_pairwise {α : Type*} [Fintype α]
    (x : α → ℤ) :
    2 * indexedDelta x = ∑ i : α, ∑ j : α, (x i - x j) ^ 2 := by
  classical
  unfold indexedDelta
  simp only [sub_sq, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [show (∑ i, x i) ^ 2 = ∑ i, ∑ j, x i * x j by
    rw [pow_two, Fintype.sum_mul_sum]]
  have hdouble :
      (∑ i, ∑ j, 2 * x i * x j) =
        2 * (∑ i, ∑ j, x i * x j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    simp only [mul_assoc]
  rw [hdouble]
  ring

/-- A strictly increasing finite natural sequence has at least the index gap
between every two entries. -/
theorem strictMono_nat_index_gap {m : ℕ} (x : Fin m → ℕ)
    (hx : StrictMono x) {i j : Fin m} (hij : i ≤ j) :
    j.1 - i.1 ≤ x j - x i := by
  classical
  have hsub : (Finset.Icc i j).image x ⊆ Finset.Icc (x i) (x j) := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hik, hkj⟩ := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨hx.monotone hik, hx.monotone hkj⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hx.injective] at hcard
  simp only [Fin.card_Icc, Nat.card_Icc] at hcard
  omega

private theorem standard_pair_sq_le {m : ℕ} (x : Fin m → ℕ)
    (hx : StrictMono x) (i j : Fin m) :
    ((i.1 : ℤ) - j.1) ^ 2 ≤ ((x i : ℤ) - x j) ^ 2 := by
  rcases le_total i j with hij | hji
  · have hgap := strictMono_nat_index_gap x hx hij
    have hxij := hx.monotone hij
    have hgapZ : (((j.1 - i.1 : ℕ) : ℤ)) ≤
        ((x j - x i : ℕ) : ℤ) := by exact_mod_cast hgap
    rw [Nat.cast_sub (show i.1 ≤ j.1 from hij), Nat.cast_sub hxij] at hgapZ
    have hindex : (0 : ℤ) ≤ (j.1 : ℤ) - i.1 := by omega
    calc
      ((i.1 : ℤ) - j.1) ^ 2 = ((j.1 : ℤ) - i.1) ^ 2 := by ring
      _ ≤ ((x j : ℤ) - x i) ^ 2 := by
        simpa [pow_two] using mul_self_le_mul_self hindex hgapZ
      _ = ((x i : ℤ) - x j) ^ 2 := by ring
  · have hgap := strictMono_nat_index_gap x hx hji
    have hxji := hx.monotone hji
    have hgapZ : (((i.1 - j.1 : ℕ) : ℤ)) ≤
        ((x i - x j : ℕ) : ℤ) := by exact_mod_cast hgap
    rw [Nat.cast_sub (show j.1 ≤ i.1 from hji), Nat.cast_sub hxji] at hgapZ
    have hindex : (0 : ℤ) ≤ (i.1 : ℤ) - j.1 := by omega
    calc
      ((i.1 : ℤ) - j.1) ^ 2 ≤ ((x i : ℤ) - x j) ^ 2 := by
        simpa [pow_two] using mul_self_le_mul_self hindex hgapZ

private theorem twice_sum_fin_val (m : ℕ) :
    2 * (∑ i : Fin m, (i.1 : ℤ)) =
      (m : ℤ) * ((m : ℤ) - 1) := by
  rw [Fin.sum_univ_eq_sum_range]
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      push_cast
      nlinarith

private theorem six_times_sum_fin_val_sq (m : ℕ) :
    6 * (∑ i : Fin m, (i.1 : ℤ) ^ 2) =
      (m : ℤ) * ((m : ℤ) - 1) * (2 * (m : ℤ) - 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (i : ℤ) ^ 2) m]
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      push_cast
      nlinarith [sq_nonneg (m : ℤ)]

/-- The exact variance numerator of `m` consecutive integers. -/
theorem twelve_mul_indexedDelta_finVal (m : ℕ) :
    12 * indexedDelta (fun i : Fin m => (i.1 : ℤ)) =
      (m : ℤ) ^ 2 * ((m : ℤ) ^ 2 - 1) := by
  have hsum := twice_sum_fin_val m
  have hsq := six_times_sum_fin_val_sq m
  have hsumsq := congrArg (fun z : ℤ => z ^ 2) hsum
  unfold indexedDelta
  simp only [Fintype.card_fin]
  nlinarith

/-- Exact discrete variance lower bound for a sorted list of `m` distinct
integers, in division-free form. -/
theorem twelve_mul_indexedDelta_ge_consecutive {m : ℕ}
    (x : Fin m → ℕ) (hx : StrictMono x) :
    (m : ℤ) ^ 2 * ((m : ℤ) ^ 2 - 1) ≤
      12 * indexedDelta (fun i => (x i : ℤ)) := by
  have hpair :
      (∑ i : Fin m, ∑ j : Fin m,
          ((i.1 : ℤ) - j.1) ^ 2) ≤
        ∑ i : Fin m, ∑ j : Fin m,
          ((x i : ℤ) - x j) ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact standard_pair_sq_le x hx i j
  rw [← two_mul_indexedDelta_eq_pairwise,
    ← two_mul_indexedDelta_eq_pairwise] at hpair
  rw [← twelve_mul_indexedDelta_finVal]
  linarith

/-- Equality in the discrete variance bound forces every adjacent gap to be
one; hence the sorted set is a consecutive interval. -/
theorem indexedDelta_equality_forces_consecutive {m : ℕ}
    (x : Fin m → ℕ) (hx : StrictMono x)
    (heq : 12 * indexedDelta (fun i => (x i : ℤ)) =
      (m : ℤ) ^ 2 * ((m : ℤ) ^ 2 - 1)) :
    ∀ k : Fin (m - 1),
      x ⟨k.1 + 1, by omega⟩ = x ⟨k.1, by omega⟩ + 1 := by
  have hdelta : indexedDelta (fun i : Fin m => (x i : ℤ)) =
      indexedDelta (fun i : Fin m => (i.1 : ℤ)) := by
    have hstd := twelve_mul_indexedDelta_finVal m
    linarith
  have hfull :
      (∑ i : Fin m, ∑ j : Fin m,
          ((i.1 : ℤ) - j.1) ^ 2) =
        ∑ i : Fin m, ∑ j : Fin m,
          ((x i : ℤ) - x j) ^ 2 := by
    rw [← two_mul_indexedDelta_eq_pairwise,
      ← two_mul_indexedDelta_eq_pairwise, hdelta]
  have houter := (Finset.sum_eq_sum_iff_of_le fun i _ => by
    apply Finset.sum_le_sum
    intro j hj
    exact standard_pair_sq_le x hx i j).mp hfull
  intro k
  let i : Fin m := ⟨k.1, by omega⟩
  let j : Fin m := ⟨k.1 + 1, by omega⟩
  have hinner := houter i (Finset.mem_univ i)
  have hterm := (Finset.sum_eq_sum_iff_of_le fun z _ =>
    standard_pair_sq_le x hx i z).mp hinner j (Finset.mem_univ j)
  have hij : i < j := by
    simp [i, j]
  have hxlt := hx hij
  have hvals : j.1 = i.1 + 1 := by simp [i, j]
  change ((i.1 : ℤ) - j.1) ^ 2 =
    ((x i : ℤ) - x j) ^ 2 at hterm
  have : x j = x i + 1 := by
    rw [hvals] at hterm
    nlinarith
  simpa [i, j] using this

/-- Variance lower bound for an arbitrary finite injective integer family;
the sorted enumeration is constructed rather than assumed. -/
theorem indexedDelta_injective_ge_consecutive {α : Type*} [Fintype α]
    (f : α → ℕ) (hinj : Function.Injective f) :
    let m := Fintype.card α
    (m : ℤ) ^ 2 * ((m : ℤ) ^ 2 - 1) ≤
      12 * indexedDelta (fun a => (f a : ℤ)) := by
  let m := Fintype.card α
  let base : Fin m ≃ α := (Fintype.equivFin α).symm
  let key : Fin m → ℕ := fun i => f (base i)
  let order : Fin m ≃ α := (Tuple.sort key).trans base
  let sorted : Fin m → ℕ := fun i => f (order i)
  have hmono : Monotone sorted := by
    simpa [sorted, order, key, Function.comp_def] using Tuple.monotone_sort key
  have hstrict : StrictMono sorted := hmono.strictMono_of_injective
    (hinj.comp order.injective)
  have hdelta : indexedDelta (fun i : Fin m => (sorted i : ℤ)) =
      indexedDelta (fun a : α => (f a : ℤ)) := by
    unfold indexedDelta
    have hsq : (∑ i : Fin m, (sorted i : ℤ) ^ 2) =
        ∑ a : α, (f a : ℤ) ^ 2 := by
      apply Fintype.sum_equiv order
      intro i
      rfl
    have hsum : (∑ i : Fin m, (sorted i : ℤ)) =
        ∑ a : α, (f a : ℤ) := by
      apply Fintype.sum_equiv order
      intro i
      rfl
    rw [hsq, hsum]
    simp [m]
  rw [← hdelta]
  exact twelve_mul_indexedDelta_ge_consecutive sorted hstrict

/-- Direct expansion of the variance of the indexed Cartesian sum.  No
injectivity is needed for the identity; injectivity is only what identifies
the indexed family with the finite sumset in the graph application. -/
theorem indexedDelta_add_product {α β : Type*} [Fintype α] [Fintype β]
    (x : α → ℤ) (y : β → ℤ) :
    indexedDelta (fun z : α × β => x z.1 + y z.2) =
      (Fintype.card β : ℤ) ^ 2 * indexedDelta x +
        (Fintype.card α : ℤ) ^ 2 * indexedDelta y := by
  classical
  have hsum :
      (∑ z : α × β, (x z.1 + y z.2)) =
        (Fintype.card β : ℤ) * (∑ a, x a) +
          (Fintype.card α : ℤ) * (∑ b, y b) := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← Finset.mul_sum]
  have hsq :
      (∑ z : α × β, (x z.1 + y z.2) ^ 2) =
        (Fintype.card β : ℤ) * (∑ a, x a ^ 2) +
          2 * (∑ a, x a) * (∑ b, y b) +
          (Fintype.card α : ℤ) * (∑ b, y b ^ 2) := by
    rw [Fintype.sum_prod_type]
    simp only [add_sq, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  unfold indexedDelta
  rw [hsum, hsq]
  simp only [Fintype.card_prod, Nat.cast_mul]
  ring

/-- An injective direct sum has exactly `|α||β|` distinct values. -/
theorem card_image_add_product_of_injective {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (x : α → ℤ) (y : β → ℤ)
    (hinj : Function.Injective (fun z : α × β => x z.1 + y z.2)) :
    ((Finset.univ : Finset (α × β)).image
      (fun z => x z.1 + y z.2)).card = Fintype.card α * Fintype.card β := by
  classical
  rw [Finset.card_image_of_injective _ hinj]
  simp

/-- For an injective Cartesian sum, the set-based variance numerator equals
the indexed numerator used in `indexedDelta_add_product`. -/
theorem finsetDelta_image_add_product {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (x : α → ℤ) (y : β → ℤ)
    (hinj : Function.Injective (fun z : α × β => x z.1 + y z.2)) :
    let S := (Finset.univ : Finset (α × β)).image
      (fun z => x z.1 + y z.2)
    (S.card : ℤ) * (∑ s ∈ S, s ^ 2) - (∑ s ∈ S, s) ^ 2 =
      (Fintype.card β : ℤ) ^ 2 * indexedDelta x +
        (Fintype.card α : ℤ) ^ 2 * indexedDelta y := by
  classical
  dsimp
  rw [Finset.card_image_of_injective _ hinj]
  have hsum :
      (∑ s ∈ (Finset.univ : Finset (α × β)).image
          (fun z => x z.1 + y z.2), s) =
        ∑ z : α × β, (x z.1 + y z.2) := by
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact hinj hab
  have hsq :
      (∑ s ∈ (Finset.univ : Finset (α × β)).image
          (fun z => x z.1 + y z.2), s ^ 2) =
        ∑ z : α × β, (x z.1 + y z.2) ^ 2 := by
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact hinj hab
  rw [hsum, hsq]
  exact indexedDelta_add_product x y

end

end LeechTrees.PathMulticut
