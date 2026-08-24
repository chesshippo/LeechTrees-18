import LeechTrees.EdgeHole
import LeechTrees.FirstEdge
import LeechTrees.ParityTailGraphAdapter
import LeechTrees.Expanded.MultiportTail.ParityTailConditionalAtoms

/-!
# Actual-tree adapters for the conditional q=67/q=66 parity tails

This module is the physical layer required by the frozen hostile G023
promotion receipt.  The four compressed rows and the two raw depth rows below
are *constructed* from an actual `PosIntTree 18` and an actual `9|9` cut.
None of directness, range, imbalance, the q=67/q=66 product alternatives, or
the seven-hole direct sum is accepted as caller-supplied row data.

The module contains no coefficient enumeration, rooted-tree lift, feasibility
claim, q=67 exclusion, or largest-edge conclusion.
-/

namespace LeechTrees.ParityTailConditional.Actual

open scoped BigOperators
open LeechTrees.Foundation
open LeechTrees.ParityTail.GraphAdapterV1
open LeechTrees.ParityTailConditional.SevenHoleRows

/-! ## Parity-filtered half-depth images -/

variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev EvenDomain (f : α → ℕ) := {x : α // f x % 2 = 0}
abbrev OddDomain (f : α → ℕ) := {x : α // f x % 2 = 1}

noncomputable def evenHalfSet (f : α → ℕ) : Finset ℕ :=
  Finset.univ.image fun x : EvenDomain f => f x.1 / 2

noncomputable def oddHalfSet (f : α → ℕ) : Finset ℕ :=
  Finset.univ.image fun x : OddDomain f => f x.1 / 2

omit [Fintype α] [DecidableEq α] in
private theorem half_value_injective_of_fixed_remainder
    (f : α → ℕ) (hf : Function.Injective f) (r : ℕ) (_hr : r < 2) :
    Function.Injective (fun x : {x : α // f x % 2 = r} => f x.1 / 2) := by
  intro x y hxy
  apply Subtype.ext
  apply hf
  change f x.1 / 2 = f y.1 / 2 at hxy
  calc
    f x.1 = f x.1 % 2 + 2 * (f x.1 / 2) :=
      (Nat.mod_add_div (f x.1) 2).symm
    _ = r + 2 * (f x.1 / 2) := by rw [x.2]
    _ = r + 2 * (f y.1 / 2) := by rw [hxy]
    _ = f y.1 % 2 + 2 * (f y.1 / 2) := by rw [y.2]
    _ = f y.1 := Nat.mod_add_div (f y.1) 2

noncomputable def evenHalfEquiv (f : α → ℕ) (hf : Function.Injective f) :
    EvenDomain f ≃ ↥(evenHalfSet f) := by
  classical
  let g : EvenDomain f → ↥(evenHalfSet f) := fun x =>
    ⟨f x.1 / 2, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩
  exact Equiv.ofBijective g
    ⟨fun _ _ h =>
        half_value_injective_of_fixed_remainder f hf 0 (by omega)
          (congrArg Subtype.val h),
      fun y => by
        rcases Finset.mem_image.mp y.2 with ⟨x, _, hx⟩
        refine ⟨x, Subtype.ext ?_⟩
        exact hx⟩

noncomputable def oddHalfEquiv (f : α → ℕ) (hf : Function.Injective f) :
    OddDomain f ≃ ↥(oddHalfSet f) := by
  classical
  let g : OddDomain f → ↥(oddHalfSet f) := fun x =>
    ⟨f x.1 / 2, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩
  exact Equiv.ofBijective g
    ⟨fun _ _ h =>
        half_value_injective_of_fixed_remainder f hf 1 (by omega)
          (congrArg Subtype.val h),
      fun y => by
        rcases Finset.mem_image.mp y.2 with ⟨x, _, hx⟩
        refine ⟨x, Subtype.ext ?_⟩
        exact hx⟩

omit [DecidableEq α] in
private theorem even_odd_domain_card (f : α → ℕ) :
    Fintype.card (EvenDomain f) + Fintype.card (OddDomain f) =
      Fintype.card α := by
  classical
  rw [Fintype.card_subtype, Fintype.card_subtype]
  let S : Finset α := Finset.univ.filter fun x => f x % 2 = 0
  have hpart := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset α)) (p := fun x => f x % 2 = 0)
  have hodd : (Finset.univ.filter fun x => ¬f x % 2 = 0) =
      Finset.univ.filter fun x => f x % 2 = 1 := by
    ext x
    have hlt := Nat.mod_lt (f x) (by omega : 0 < 2)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  simpa [S, hodd] using hpart

omit [DecidableEq α] in
theorem evenHalfSet_card_add_oddHalfSet_card
    (f : α → ℕ) (hf : Function.Injective f) :
    (evenHalfSet f).card + (oddHalfSet f).card = Fintype.card α := by
  classical
  rw [← Fintype.card_coe, ← Fintype.card_congr (evenHalfEquiv f hf),
    ← Fintype.card_coe, ← Fintype.card_congr (oddHalfEquiv f hf)]
  exact even_odd_domain_card f

private theorem twice_half_of_even {d : ℕ} (hd : d % 2 = 0) :
    2 * (d / 2) = d := by
  have h := Nat.mod_add_div d 2
  omega

private theorem twice_half_add_one_of_odd {d : ℕ} (hd : d % 2 = 1) :
    2 * (d / 2) + 1 = d := by
  have h := Nat.mod_add_div d 2
  omega

/-! ## Actual raw rows and the seven-hole constructor -/

variable {T : PosIntTree 18}

noncomputable def leftRawDepthSet (T : PosIntTree 18) (e : T.Edge) : Finset ℕ :=
  Finset.univ.image (T.leftDepth e)

noncomputable def rightRawDepthSet (T : PosIntTree 18) (e : T.Edge) : Finset ℕ :=
  Finset.univ.image (T.rightDepth e)

theorem zero_mem_leftRawDepthSet (T : PosIntTree 18) (e : T.Edge) :
    0 ∈ leftRawDepthSet T e := by
  classical
  let u : T.LeftVertex e := ⟨T.edgeLeft e, T.edgeLeft_mem_LeftCut e⟩
  rw [leftRawDepthSet, Finset.mem_image]
  refine ⟨u, Finset.mem_univ _, ?_⟩
  simp [u, PosIntTree.leftDepth]

theorem zero_mem_rightRawDepthSet (T : PosIntTree 18) (e : T.Edge) :
    0 ∈ rightRawDepthSet T e := by
  classical
  let v : T.RightVertex e := ⟨T.edgeRight e, T.edgeRight_mem_RightCut e⟩
  rw [rightRawDepthSet, Finset.mem_image]
  refine ⟨v, Finset.mem_univ _, ?_⟩
  simp [v, PosIntTree.rightDepth]

/-- Receipt atoms F--G start from these actual rows.  In particular the
direct sum and the bound are consequences of the indexed spectrum. -/
noncomputable def actualSevenHoleRows
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 66)
    (hs : T.cutSize e = 9) : SevenHoleRows where
  DA := leftRawDepthSet T e
  DB := rightRawDepthSet T e
  cardA := by
    classical
    rw [leftRawDepthSet, Finset.card_image_of_injective _
      (T.leftDepth_injective hL e), Finset.card_univ]
    change T.cutSize e = 9
    exact hs
  cardB := by
    classical
    rw [rightRawDepthSet, Finset.card_image_of_injective _
      (T.rightDepth_injective hL e), Finset.card_univ,
      T.rightVertex_card e, hs]
  zeroA := zero_mem_leftRawDepthSet T e
  zeroB := zero_mem_rightRawDepthSet T e
  add_injective := by
    classical
    intro x y hxy
    rcases Finset.mem_image.mp x.1.2 with ⟨ux, _, hux⟩
    rcases Finset.mem_image.mp x.2.2 with ⟨vx, _, hvx⟩
    rcases Finset.mem_image.mp y.1.2 with ⟨uy, _, huy⟩
    rcases Finset.mem_image.mp y.2.2 with ⟨vy, _, hvy⟩
    have hsum : T.leftDepth e ux + T.rightDepth e vx =
        T.leftDepth e uy + T.rightDepth e vy := by
      simpa [hux, hvx, huy, hvy] using hxy
    have hp : (ux, vx) = (uy, vy) := T.rootedCrossSum_injective hL e <| by
      simp only [PosIntTree.rootedCrossSum]
      omega
    apply Prod.ext <;> apply Subtype.ext
    · simpa [hux, huy] using congrArg (fun z => T.leftDepth e z.1) hp
    · simpa [hvx, hvy] using congrArg (fun z => T.rightDepth e z.2) hp
  sum_le := by
    classical
    intro a ha b hb
    rcases Finset.mem_image.mp ha with ⟨u, _, hu⟩
    rcases Finset.mem_image.mp hb with ⟨v, _, hv⟩
    have htail := (Finset.mem_Icc.mp
      (T.rootedCrossSum_mem_target_tail hL e (u, v))).2
    simp only [PosIntTree.rootedCrossSum] at htail
    rw [hu, hv, hw] at htail
    norm_num [targetN, Nat.choose] at htail ⊢
    omega

theorem actual_seven_hole_card
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 66)
    (hs : T.cutSize e = 9) :
    ((actualSevenHoleRows hL e hw hs).H).card = 7 :=
  SevenHoleRows.H_card _

theorem actual_seven_hole_convolution
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 66)
    (hs : T.cutSize e = 9) (m : ℕ) [NeZero m]
    (hm : m = 4 ∨ m = 8 ∨ m = 11) (r : ZMod m) :
    (actualSevenHoleRows hL e hw hs).cyclicConvolution m r +
      residueCount (actualSevenHoleRows hL e hw hs).H m r = 88 / m :=
  by
    have hm0 : m ≠ 0 := by
      rcases hm with rfl | rfl | rfl <;> norm_num
    letI : NeZero m := ⟨hm0⟩
    exact SevenHoleRows.residue_convolution _ m hm r

end LeechTrees.ParityTailConditional.Actual

namespace LeechTrees.ParityTailConditional.Actual

open scoped BigOperators
open LeechTrees.Foundation
open LeechTrees.ParityTail.GraphAdapterV1
open LeechTrees.ParityTailConditional.SevenHoleRows

/-! ## The four actual half-depth rows -/

variable {T : PosIntTree 18}

noncomputable def actualHalfDepthRows
    (hL : IsLeech T) (e : T.Edge) (hs : T.cutSize e = 9) : HalfDepthRows where
  P := evenHalfSet (T.leftDepth e)
  R := oddHalfSet (T.leftDepth e)
  Q := evenHalfSet (T.rightDepth e)
  S := oddHalfSet (T.rightDepth e)
  sideA_card := by
    rw [evenHalfSet_card_add_oddHalfSet_card _
      (T.leftDepth_injective hL e)]
    change T.cutSize e = 9
    exact hs
  sideB_card := by
    rw [evenHalfSet_card_add_oddHalfSet_card _
      (T.rightDepth_injective hL e), T.rightVertex_card e, hs]
  rootP := by
    classical
    let u : EvenDomain (T.leftDepth e) :=
      ⟨⟨T.edgeLeft e, T.edgeLeft_mem_LeftCut e⟩, by
        simp [PosIntTree.leftDepth]⟩
    exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, by
      simp [u, PosIntTree.leftDepth]⟩
  rootQ := by
    classical
    let v : EvenDomain (T.rightDepth e) :=
      ⟨⟨T.edgeRight e, T.edgeRight_mem_RightCut e⟩, by
        simp [PosIntTree.rightDepth]⟩
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, by
      simp [v, PosIntTree.rightDepth]⟩

private noncomputable def evenDecode
    (hL : IsLeech T) (e : T.Edge) (hs : T.cutSize e = 9) :
    (actualHalfDepthRows hL e hs).EvenIndex →
      T.LeftVertex e × T.RightVertex e
  | .inl x =>
      (((evenHalfEquiv (T.leftDepth e) (T.leftDepth_injective hL e)).symm x.1).1,
        ((evenHalfEquiv (T.rightDepth e) (T.rightDepth_injective hL e)).symm x.2).1)
  | .inr x =>
      (((oddHalfEquiv (T.leftDepth e) (T.leftDepth_injective hL e)).symm x.1).1,
        ((oddHalfEquiv (T.rightDepth e) (T.rightDepth_injective hL e)).symm x.2).1)

private noncomputable def oddDecode
    (hL : IsLeech T) (e : T.Edge) (hs : T.cutSize e = 9) :
    (actualHalfDepthRows hL e hs).OddIndex →
      T.LeftVertex e × T.RightVertex e
  | .inl x =>
      (((evenHalfEquiv (T.leftDepth e) (T.leftDepth_injective hL e)).symm x.1).1,
        ((oddHalfEquiv (T.rightDepth e) (T.rightDepth_injective hL e)).symm x.2).1)
  | .inr x =>
      (((oddHalfEquiv (T.leftDepth e) (T.leftDepth_injective hL e)).symm x.1).1,
        ((evenHalfEquiv (T.rightDepth e) (T.rightDepth_injective hL e)).symm x.2).1)

private theorem evenDecode_injective
    (hL : IsLeech T) (e : T.Edge) (hs : T.cutSize e = 9) :
    Function.Injective (evenDecode hL e hs) := by
  intro i j hij
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          simp only [evenDecode] at hij
          apply congrArg Sum.inl
          apply Prod.ext
          · apply (evenHalfEquiv (T.leftDepth e)
              (T.leftDepth_injective hL e)).symm.injective
            apply Subtype.ext
            apply Subtype.ext
            exact congrArg (fun z => z.1.1) hij
          · apply (evenHalfEquiv (T.rightDepth e)
              (T.rightDepth_injective hL e)).symm.injective
            apply Subtype.ext
            apply Subtype.ext
            exact congrArg (fun z => z.2.1) hij
      | inr j =>
          simp only [evenDecode] at hij
          exfalso
          have hdepth := congrArg (fun z => T.leftDepth e z.1) hij
          change T.leftDepth e ((evenHalfEquiv (T.leftDepth e)
            (T.leftDepth_injective hL e)).symm i.1).1 =
              T.leftDepth e ((oddHalfEquiv (T.leftDepth e)
                (T.leftDepth_injective hL e)).symm j.1).1 at hdepth
          have he := ((evenHalfEquiv (T.leftDepth e)
            (T.leftDepth_injective hL e)).symm i.1).2
          have ho := ((oddHalfEquiv (T.leftDepth e)
            (T.leftDepth_injective hL e)).symm j.1).2
          omega
  | inr i =>
      cases j with
      | inl j =>
          simp only [evenDecode] at hij
          exfalso
          have hdepth := congrArg (fun z => T.leftDepth e z.1) hij
          change T.leftDepth e ((oddHalfEquiv (T.leftDepth e)
            (T.leftDepth_injective hL e)).symm i.1).1 =
              T.leftDepth e ((evenHalfEquiv (T.leftDepth e)
                (T.leftDepth_injective hL e)).symm j.1).1 at hdepth
          have ho := ((oddHalfEquiv (T.leftDepth e)
            (T.leftDepth_injective hL e)).symm i.1).2
          have he := ((evenHalfEquiv (T.leftDepth e)
            (T.leftDepth_injective hL e)).symm j.1).2
          omega
      | inr j =>
          simp only [evenDecode] at hij
          apply congrArg Sum.inr
          apply Prod.ext
          · apply (oddHalfEquiv (T.leftDepth e)
              (T.leftDepth_injective hL e)).symm.injective
            apply Subtype.ext
            apply Subtype.ext
            exact congrArg (fun z => z.1.1) hij
          · apply (oddHalfEquiv (T.rightDepth e)
              (T.rightDepth_injective hL e)).symm.injective
            apply Subtype.ext
            apply Subtype.ext
            exact congrArg (fun z => z.2.1) hij

private theorem oddDecode_injective
    (hL : IsLeech T) (e : T.Edge) (hs : T.cutSize e = 9) :
    Function.Injective (oddDecode hL e hs) := by
  intro i j hij
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          simp only [oddDecode] at hij
          apply congrArg Sum.inl
          apply Prod.ext
          · apply (evenHalfEquiv (T.leftDepth e)
              (T.leftDepth_injective hL e)).symm.injective
            apply Subtype.ext
            apply Subtype.ext
            exact congrArg (fun z => z.1.1) hij
          · apply (oddHalfEquiv (T.rightDepth e)
              (T.rightDepth_injective hL e)).symm.injective
            apply Subtype.ext
            apply Subtype.ext
            exact congrArg (fun z => z.2.1) hij
      | inr j =>
          simp only [oddDecode] at hij
          exfalso
          have hdepth := congrArg (fun z => T.leftDepth e z.1) hij
          change T.leftDepth e ((evenHalfEquiv (T.leftDepth e)
            (T.leftDepth_injective hL e)).symm i.1).1 =
              T.leftDepth e ((oddHalfEquiv (T.leftDepth e)
                (T.leftDepth_injective hL e)).symm j.1).1 at hdepth
          have he := ((evenHalfEquiv (T.leftDepth e)
            (T.leftDepth_injective hL e)).symm i.1).2
          have ho := ((oddHalfEquiv (T.leftDepth e)
            (T.leftDepth_injective hL e)).symm j.1).2
          omega
  | inr i =>
      cases j with
      | inl j =>
          simp only [oddDecode] at hij
          exfalso
          have hdepth := congrArg (fun z => T.leftDepth e z.1) hij
          change T.leftDepth e ((oddHalfEquiv (T.leftDepth e)
            (T.leftDepth_injective hL e)).symm i.1).1 =
              T.leftDepth e ((evenHalfEquiv (T.leftDepth e)
                (T.leftDepth_injective hL e)).symm j.1).1 at hdepth
          have ho := ((oddHalfEquiv (T.leftDepth e)
            (T.leftDepth_injective hL e)).symm i.1).2
          have he := ((evenHalfEquiv (T.leftDepth e)
            (T.leftDepth_injective hL e)).symm j.1).2
          omega
      | inr j =>
          simp only [oddDecode] at hij
          apply congrArg Sum.inr
          apply Prod.ext
          · apply (oddHalfEquiv (T.leftDepth e)
              (T.leftDepth_injective hL e)).symm.injective
            apply Subtype.ext
            apply Subtype.ext
            exact congrArg (fun z => z.1.1) hij
          · apply (evenHalfEquiv (T.rightDepth e)
              (T.rightDepth_injective hL e)).symm.injective
            apply Subtype.ext
            apply Subtype.ext
            exact congrArg (fun z => z.2.1) hij

private theorem evenDecode_value
    (hL : IsLeech T) (e : T.Edge) (hs : T.cutSize e = 9)
    (i : (actualHalfDepthRows hL e hs).EvenIndex) :
    T.edgeOffset e (evenDecode hL e hs i) =
      2 * (actualHalfDepthRows hL e hs).evenExponent i := by
  cases i with
  | inl i =>
      let u := (evenHalfEquiv (T.leftDepth e)
        (T.leftDepth_injective hL e)).symm i.1
      let v := (evenHalfEquiv (T.rightDepth e)
        (T.rightDepth_injective hL e)).symm i.2
      have huHalf := congrArg Subtype.val
        ((evenHalfEquiv (T.leftDepth e)
          (T.leftDepth_injective hL e)).apply_symm_apply i.1)
      have hvHalf := congrArg Subtype.val
        ((evenHalfEquiv (T.rightDepth e)
          (T.rightDepth_injective hL e)).apply_symm_apply i.2)
      have huRaw := twice_half_of_even u.2
      have hvRaw := twice_half_of_even v.2
      change T.leftDepth e u.1 + T.rightDepth e v.1 =
        2 * (i.1.1 + i.2.1)
      change T.leftDepth e u.1 / 2 = i.1.1 at huHalf
      change T.rightDepth e v.1 / 2 = i.2.1 at hvHalf
      omega
  | inr i =>
      let u := (oddHalfEquiv (T.leftDepth e)
        (T.leftDepth_injective hL e)).symm i.1
      let v := (oddHalfEquiv (T.rightDepth e)
        (T.rightDepth_injective hL e)).symm i.2
      have huHalf := congrArg Subtype.val
        ((oddHalfEquiv (T.leftDepth e)
          (T.leftDepth_injective hL e)).apply_symm_apply i.1)
      have hvHalf := congrArg Subtype.val
        ((oddHalfEquiv (T.rightDepth e)
          (T.rightDepth_injective hL e)).apply_symm_apply i.2)
      have huRaw := twice_half_add_one_of_odd u.2
      have hvRaw := twice_half_add_one_of_odd v.2
      change T.leftDepth e u.1 + T.rightDepth e v.1 =
        2 * (i.1.1 + i.2.1 + 1)
      change T.leftDepth e u.1 / 2 = i.1.1 at huHalf
      change T.rightDepth e v.1 / 2 = i.2.1 at hvHalf
      omega

private theorem oddDecode_value
    (hL : IsLeech T) (e : T.Edge) (hs : T.cutSize e = 9)
    (i : (actualHalfDepthRows hL e hs).OddIndex) :
    T.edgeOffset e (oddDecode hL e hs i) =
      2 * (actualHalfDepthRows hL e hs).oddExponent i + 1 := by
  cases i with
  | inl i =>
      let u := (evenHalfEquiv (T.leftDepth e)
        (T.leftDepth_injective hL e)).symm i.1
      let v := (oddHalfEquiv (T.rightDepth e)
        (T.rightDepth_injective hL e)).symm i.2
      have huHalf := congrArg Subtype.val
        ((evenHalfEquiv (T.leftDepth e)
          (T.leftDepth_injective hL e)).apply_symm_apply i.1)
      have hvHalf := congrArg Subtype.val
        ((oddHalfEquiv (T.rightDepth e)
          (T.rightDepth_injective hL e)).apply_symm_apply i.2)
      have huRaw := twice_half_of_even u.2
      have hvRaw := twice_half_add_one_of_odd v.2
      change T.leftDepth e u.1 + T.rightDepth e v.1 =
        2 * (i.1.1 + i.2.1) + 1
      change T.leftDepth e u.1 / 2 = i.1.1 at huHalf
      change T.rightDepth e v.1 / 2 = i.2.1 at hvHalf
      omega
  | inr i =>
      let u := (oddHalfEquiv (T.leftDepth e)
        (T.leftDepth_injective hL e)).symm i.1
      let v := (evenHalfEquiv (T.rightDepth e)
        (T.rightDepth_injective hL e)).symm i.2
      have huHalf := congrArg Subtype.val
        ((oddHalfEquiv (T.leftDepth e)
          (T.leftDepth_injective hL e)).apply_symm_apply i.1)
      have hvHalf := congrArg Subtype.val
        ((evenHalfEquiv (T.rightDepth e)
          (T.rightDepth_injective hL e)).apply_symm_apply i.2)
      have huRaw := twice_half_add_one_of_odd u.2
      have hvRaw := twice_half_of_even v.2
      change T.leftDepth e u.1 + T.rightDepth e v.1 =
        2 * (i.1.1 + i.2.1) + 1
      change T.leftDepth e u.1 / 2 = i.1.1 at huHalf
      change T.rightDepth e v.1 / 2 = i.2.1 at hvHalf
      omega

theorem actual_evenExponent_injective
    (hL : IsLeech T) (e : T.Edge) (hs : T.cutSize e = 9) :
    Function.Injective (actualHalfDepthRows hL e hs).evenExponent := by
  intro i j hij
  apply evenDecode_injective hL e hs
  apply T.edgeOffset_injective hL e
  rw [evenDecode_value hL e hs, evenDecode_value hL e hs, hij]

theorem actual_oddExponent_injective
    (hL : IsLeech T) (e : T.Edge) (hs : T.cutSize e = 9) :
    Function.Injective (actualHalfDepthRows hL e hs).oddExponent := by
  intro i j hij
  apply oddDecode_injective hL e hs
  apply T.edgeOffset_injective hL e
  rw [oddDecode_value hL e hs, oddDecode_value hL e hs, hij]

theorem actual_evenExponent_range_q67
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 67)
    (hs : T.cutSize e = 9) :
    ∀ i, (actualHalfDepthRows hL e hs).evenExponent i ≤ 43 := by
  intro i
  have hi := T.edgeOffset_mem_interval hL e (evenDecode hL e hs i)
  rw [PosIntTree.edgeOffsetInterval, Finset.mem_Icc] at hi
  rw [evenDecode_value hL e hs i] at hi
  norm_num [targetN, Nat.choose, hw] at hi ⊢
  omega

theorem actual_oddExponent_range_q67
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 67)
    (hs : T.cutSize e = 9) :
    ∀ i, (actualHalfDepthRows hL e hs).oddExponent i ≤ 42 := by
  intro i
  have hi := T.edgeOffset_mem_interval hL e (oddDecode hL e hs i)
  rw [PosIntTree.edgeOffsetInterval, Finset.mem_Icc] at hi
  rw [oddDecode_value hL e hs i] at hi
  norm_num [targetN, Nat.choose, hw] at hi ⊢
  omega

theorem actual_evenExponent_range_q66
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 66)
    (hs : T.cutSize e = 9) :
    ∀ i, (actualHalfDepthRows hL e hs).evenExponent i ≤ 43 := by
  intro i
  have hi := T.edgeOffset_mem_interval hL e (evenDecode hL e hs i)
  rw [PosIntTree.edgeOffsetInterval, Finset.mem_Icc] at hi
  rw [evenDecode_value hL e hs i] at hi
  norm_num [targetN, Nat.choose, hw] at hi ⊢
  omega

theorem actual_oddExponent_range_q66
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 66)
    (hs : T.cutSize e = 9) :
    ∀ i, (actualHalfDepthRows hL e hs).oddExponent i ≤ 43 := by
  intro i
  have hi := T.edgeOffset_mem_interval hL e (oddDecode hL e hs i)
  rw [PosIntTree.edgeOffsetInterval, Finset.mem_Icc] at hi
  rw [oddDecode_value hL e hs i] at hi
  norm_num [targetN, Nat.choose, hw] at hi ⊢
  omega

private theorem even_parity_cases {a b k : ℕ} (h : a + b = 2 * k) :
    (a % 2 = 0 ∧ b % 2 = 0) ∨ (a % 2 = 1 ∧ b % 2 = 1) := by
  have ha := Nat.mod_lt a (by omega : 0 < 2)
  have hb := Nat.mod_lt b (by omega : 0 < 2)
  have had := Nat.mod_add_div a 2
  have hbd := Nat.mod_add_div b 2
  omega

private theorem odd_parity_cases {a b k : ℕ} (h : a + b = 2 * k + 1) :
    (a % 2 = 0 ∧ b % 2 = 1) ∨ (a % 2 = 1 ∧ b % 2 = 0) := by
  have ha := Nat.mod_lt a (by omega : 0 < 2)
  have hb := Nat.mod_lt b (by omega : 0 < 2)
  have had := Nat.mod_add_div a 2
  have hbd := Nat.mod_add_div b 2
  omega

/-- Exact physical support adapter: compressed even exponents are precisely
the even actual rooted offsets, with no collapse of indexed multiplicity. -/
theorem mem_actual_even_image_iff_crossOffset
    (hL : IsLeech T) (e : T.Edge) (hs : T.cutSize e = 9) (k : ℕ) :
    k ∈ imageSet (actualHalfDepthRows hL e hs).evenExponent ↔
      2 * k ∈ T.crossOffsetSpectrum e := by
  classical
  constructor
  · intro hk
    rcases Finset.mem_image.mp hk with ⟨i, _, hi⟩
    rw [PosIntTree.crossOffsetSpectrum, Finset.mem_image]
    refine ⟨evenDecode hL e hs i, Finset.mem_univ _, ?_⟩
    rw [evenDecode_value hL e hs i, hi]
  · intro hk
    rw [PosIntTree.crossOffsetSpectrum, Finset.mem_image] at hk
    rcases hk with ⟨x, _, hx⟩
    have hsum : T.leftDepth e x.1 + T.rightDepth e x.2 = 2 * k := by
      simpa [PosIntTree.edgeOffset] using hx
    rcases even_parity_cases hsum with h00 | h11
    · let u : EvenDomain (T.leftDepth e) := ⟨x.1, h00.1⟩
      let v : EvenDomain (T.rightDepth e) := ⟨x.2, h00.2⟩
      let i : (actualHalfDepthRows hL e hs).EvenIndex := Sum.inl
        ((evenHalfEquiv (T.leftDepth e) (T.leftDepth_injective hL e) u),
          (evenHalfEquiv (T.rightDepth e) (T.rightDepth_injective hL e) v))
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      have hi := evenDecode_value hL e hs i
      have hdecode : evenDecode hL e hs i = x := by
        apply Prod.ext <;> apply Subtype.ext <;>
          simp [i, u, v, evenDecode]
      rw [hdecode, hx] at hi
      omega
    · let u : OddDomain (T.leftDepth e) := ⟨x.1, h11.1⟩
      let v : OddDomain (T.rightDepth e) := ⟨x.2, h11.2⟩
      let i : (actualHalfDepthRows hL e hs).EvenIndex := Sum.inr
        ((oddHalfEquiv (T.leftDepth e) (T.leftDepth_injective hL e) u),
          (oddHalfEquiv (T.rightDepth e) (T.rightDepth_injective hL e) v))
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      have hi := evenDecode_value hL e hs i
      have hdecode : evenDecode hL e hs i = x := by
        apply Prod.ext <;> apply Subtype.ext <;>
          simp [i, u, v, evenDecode]
      rw [hdecode, hx] at hi
      omega

/-- Exact physical support adapter for the odd actual rooted offsets. -/
theorem mem_actual_odd_image_iff_crossOffset
    (hL : IsLeech T) (e : T.Edge) (hs : T.cutSize e = 9) (k : ℕ) :
    k ∈ imageSet (actualHalfDepthRows hL e hs).oddExponent ↔
      2 * k + 1 ∈ T.crossOffsetSpectrum e := by
  classical
  constructor
  · intro hk
    rcases Finset.mem_image.mp hk with ⟨i, _, hi⟩
    rw [PosIntTree.crossOffsetSpectrum, Finset.mem_image]
    refine ⟨oddDecode hL e hs i, Finset.mem_univ _, ?_⟩
    rw [oddDecode_value hL e hs i, hi]
  · intro hk
    rw [PosIntTree.crossOffsetSpectrum, Finset.mem_image] at hk
    rcases hk with ⟨x, _, hx⟩
    have hsum : T.leftDepth e x.1 + T.rightDepth e x.2 = 2 * k + 1 := by
      simpa [PosIntTree.edgeOffset] using hx
    rcases odd_parity_cases hsum with h01 | h10
    · let u : EvenDomain (T.leftDepth e) := ⟨x.1, h01.1⟩
      let v : OddDomain (T.rightDepth e) := ⟨x.2, h01.2⟩
      let i : (actualHalfDepthRows hL e hs).OddIndex := Sum.inl
        ((evenHalfEquiv (T.leftDepth e) (T.leftDepth_injective hL e) u),
          (oddHalfEquiv (T.rightDepth e) (T.rightDepth_injective hL e) v))
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      have hi := oddDecode_value hL e hs i
      have hdecode : oddDecode hL e hs i = x := by
        apply Prod.ext <;> apply Subtype.ext <;>
          simp [i, u, v, oddDecode]
      rw [hdecode, hx] at hi
      omega
    · let u : OddDomain (T.leftDepth e) := ⟨x.1, h10.1⟩
      let v : EvenDomain (T.rightDepth e) := ⟨x.2, h10.2⟩
      let i : (actualHalfDepthRows hL e hs).OddIndex := Sum.inr
        ((oddHalfEquiv (T.leftDepth e) (T.leftDepth_injective hL e) u),
          (evenHalfEquiv (T.rightDepth e) (T.rightDepth_injective hL e) v))
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      have hi := oddDecode_value hL e hs i
      have hdecode : oddDecode hL e hs i = x := by
        apply Prod.ext <;> apply Subtype.ext <;>
          simp [i, u, v, oddDecode]
      rw [hdecode, hx] at hi
      omega

private theorem actual_q67_individual_bounds
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 67)
    (hs : T.cutSize e = 9) :
    (∀ x ∈ (actualHalfDepthRows hL e hs).P, x ≤ 43) ∧
    (∀ x ∈ (actualHalfDepthRows hL e hs).Q, x ≤ 43) ∧
    (∀ x ∈ (actualHalfDepthRows hL e hs).R, x ≤ 42) ∧
    (∀ x ∈ (actualHalfDepthRows hL e hs).S, x ≤ 42) := by
  let D := actualHalfDepthRows hL e hs
  have hE := actual_evenExponent_range_q67 hL e hw hs
  have hO := actual_oddExponent_range_q67 hL e hw hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    let i : D.EvenIndex := Sum.inl (⟨x, hx⟩, ⟨0, D.rootQ⟩)
    simpa [i, D, HalfDepthRows.evenExponent] using hE i
  · intro x hx
    let i : D.EvenIndex := Sum.inl (⟨0, D.rootP⟩, ⟨x, hx⟩)
    simpa [i, D, HalfDepthRows.evenExponent] using hE i
  · intro x hx
    let i : D.OddIndex := Sum.inr (⟨x, hx⟩, ⟨0, D.rootQ⟩)
    simpa [i, D, HalfDepthRows.oddExponent] using hO i
  · intro x hx
    let i : D.OddIndex := Sum.inl (⟨0, D.rootP⟩, ⟨x, hx⟩)
    simpa [i, D, HalfDepthRows.oddExponent] using hO i

private theorem actual_q66_individual_bounds
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 66)
    (hs : T.cutSize e = 9) :
    (∀ x ∈ (actualHalfDepthRows hL e hs).P, x ≤ 43) ∧
    (∀ x ∈ (actualHalfDepthRows hL e hs).Q, x ≤ 43) := by
  let D := actualHalfDepthRows hL e hs
  have hE := actual_evenExponent_range_q66 hL e hw hs
  constructor
  · intro x hx
    let i : D.EvenIndex := Sum.inl (⟨x, hx⟩, ⟨0, D.rootQ⟩)
    simpa [i, D, HalfDepthRows.evenExponent] using hE i
  · intro x hx
    let i : D.EvenIndex := Sum.inl (⟨0, D.rootP⟩, ⟨x, hx⟩)
    simpa [i, D, HalfDepthRows.evenExponent] using hE i

private theorem root_dist_leftDepth (T : PosIntTree 18) (e : T.Edge)
    (u : T.LeftVertex e) :
    T.dist (T.edgeLeft e) u.1 = T.leftDepth e u := by
  rw [T.dist_comm]
  rfl

private theorem root_dist_rightDepth (T : PosIntTree 18) (e : T.Edge)
    (v : T.RightVertex e) :
    T.dist (T.edgeLeft e) v.1 = T.weight e + T.rightDepth e v := by
  have h := T.cross_distance_decomposition e
    (T.edgeLeft_mem_LeftCut e) v.2
  simpa [PosIntTree.leftDepth, PosIntTree.rightDepth] using h

private noncomputable def oddEdgeRootEvenEquiv
    (T : PosIntTree 18) (e : T.Edge) (hodd : T.weight e % 2 = 1) :
    EvenDomain (T.leftDepth e) ⊕ OddDomain (T.rightDepth e) ≃
      {u : Fin 18 // T.dist (T.edgeLeft e) u % 2 = 0} where
  toFun
    | .inl u => ⟨u.1.1, by rw [root_dist_leftDepth]; exact u.2⟩
    | .inr v => ⟨v.1.1, by
        rw [root_dist_rightDepth]
        have hwlt := Nat.mod_lt (T.weight e) (by omega : 0 < 2)
        have hvlt := Nat.mod_lt (T.rightDepth e v.1) (by omega : 0 < 2)
        have hwdec := Nat.mod_add_div (T.weight e) 2
        have hvdec := Nat.mod_add_div (T.rightDepth e v.1) 2
        omega⟩
  invFun u := by
    by_cases hleft : T.LeftCut e u.1
    · exact Sum.inl ⟨⟨u.1, hleft⟩, by
        rw [← root_dist_leftDepth]
        exact u.2⟩
    · have hright : T.RightCut e u.1 :=
        (T.rightCut_iff_not_leftCut e u.1).2 hleft
      exact Sum.inr ⟨⟨u.1, hright⟩, by
        have hd := root_dist_rightDepth T e ⟨u.1, hright⟩
        have hu := u.2
        rw [hd] at hu
        have hwlt := Nat.mod_lt (T.weight e) (by omega : 0 < 2)
        have hvlt := Nat.mod_lt (T.rightDepth e ⟨u.1, hright⟩)
          (by omega : 0 < 2)
        have hwdec := Nat.mod_add_div (T.weight e) 2
        have hvdec := Nat.mod_add_div (T.rightDepth e ⟨u.1, hright⟩) 2
        omega⟩
  left_inv x := by
    cases x with
    | inl u => simp [u.1.2]
    | inr v =>
        have hnleft : ¬T.LeftCut e v.1 := by
          intro hl
          exact T.LeftCut_disjoint_RightCut e v.1 ⟨hl, v.1.2⟩
        simp [hnleft]
  right_inv u := by
    by_cases hleft : T.LeftCut e u.1 <;> simp [hleft]

private noncomputable def evenEdgeRootEvenEquiv
    (T : PosIntTree 18) (e : T.Edge) (heven : T.weight e % 2 = 0) :
    EvenDomain (T.leftDepth e) ⊕ EvenDomain (T.rightDepth e) ≃
      {u : Fin 18 // T.dist (T.edgeLeft e) u % 2 = 0} where
  toFun
    | .inl u => ⟨u.1.1, by rw [root_dist_leftDepth]; exact u.2⟩
    | .inr v => ⟨v.1.1, by
        rw [root_dist_rightDepth]
        have hwlt := Nat.mod_lt (T.weight e) (by omega : 0 < 2)
        have hvlt := Nat.mod_lt (T.rightDepth e v.1) (by omega : 0 < 2)
        have hwdec := Nat.mod_add_div (T.weight e) 2
        have hvdec := Nat.mod_add_div (T.rightDepth e v.1) 2
        omega⟩
  invFun u := by
    by_cases hleft : T.LeftCut e u.1
    · exact Sum.inl ⟨⟨u.1, hleft⟩, by
        rw [← root_dist_leftDepth]
        exact u.2⟩
    · have hright : T.RightCut e u.1 :=
        (T.rightCut_iff_not_leftCut e u.1).2 hleft
      exact Sum.inr ⟨⟨u.1, hright⟩, by
        have hd := root_dist_rightDepth T e ⟨u.1, hright⟩
        have hu := u.2
        rw [hd] at hu
        have hwlt := Nat.mod_lt (T.weight e) (by omega : 0 < 2)
        have hvlt := Nat.mod_lt (T.rightDepth e ⟨u.1, hright⟩)
          (by omega : 0 < 2)
        have hwdec := Nat.mod_add_div (T.weight e) 2
        have hvdec := Nat.mod_add_div (T.rightDepth e ⟨u.1, hright⟩) 2
        omega⟩
  left_inv x := by
    cases x with
    | inl u => simp [u.1.2]
    | inr v =>
        have hnleft : ¬T.LeftCut e v.1 := by
          intro hl
          exact T.LeftCut_disjoint_RightCut e v.1 ⟨hl, v.1.2⟩
        simp [hnleft]
  right_inv u := by
    by_cases hleft : T.LeftCut e u.1 <;> simp [hleft]

private theorem actual_P_card
    (hL : IsLeech T) (e : T.Edge) (hs : T.cutSize e = 9) :
    (actualHalfDepthRows hL e hs).P.card =
      Fintype.card (EvenDomain (T.leftDepth e)) := by
  change (evenHalfSet (T.leftDepth e)).card = _
  rw [← Fintype.card_coe,
    ← Fintype.card_congr (evenHalfEquiv (T.leftDepth e)
      (T.leftDepth_injective hL e))]

private theorem actual_R_card
    (hL : IsLeech T) (e : T.Edge) (hs : T.cutSize e = 9) :
    (actualHalfDepthRows hL e hs).R.card =
      Fintype.card (OddDomain (T.leftDepth e)) := by
  change (oddHalfSet (T.leftDepth e)).card = _
  rw [← Fintype.card_coe,
    ← Fintype.card_congr (oddHalfEquiv (T.leftDepth e)
      (T.leftDepth_injective hL e))]

private theorem actual_Q_card
    (hL : IsLeech T) (e : T.Edge) (hs : T.cutSize e = 9) :
    (actualHalfDepthRows hL e hs).Q.card =
      Fintype.card (EvenDomain (T.rightDepth e)) := by
  change (evenHalfSet (T.rightDepth e)).card = _
  rw [← Fintype.card_coe,
    ← Fintype.card_congr (evenHalfEquiv (T.rightDepth e)
      (T.rightDepth_injective hL e))]

private theorem actual_S_card
    (hL : IsLeech T) (e : T.Edge) (hs : T.cutSize e = 9) :
    (actualHalfDepthRows hL e hs).S.card =
      Fintype.card (OddDomain (T.rightDepth e)) := by
  change (oddHalfSet (T.rightDepth e)).card = _
  rw [← Fintype.card_coe,
    ← Fintype.card_congr (oddHalfEquiv (T.rightDepth e)
      (T.rightDepth_injective hL e))]

/-- The odd-edge `±4` relation is derived from the actual global parity
class, not installed as a field of an assumed row record. -/
theorem actual_odd_edge_imbalance
    (hL : IsLeech T) (e : T.Edge) (hodd : T.weight e % 2 = 1)
    (hs : T.cutSize e = 9) :
    (actualHalfDepthRows hL e hs).deltaA -
        (actualHalfDepthRows hL e hs).deltaB = 4 ∨
      (actualHalfDepthRows hL e hs).deltaA -
        (actualHalfDepthRows hL e hs).deltaB = -4 := by
  let D := actualHalfDepthRows hL e hs
  have hcard := Fintype.card_congr (oddEdgeRootEvenEquiv T e hodd)
  have hclass := t3_order18_class_sizes hL (T.edgeLeft e)
  rw [Fintype.card_sum] at hcard
  change Fintype.card (EvenDomain (T.leftDepth e)) +
      Fintype.card (OddDomain (T.rightDepth e)) =
        T.parityClassSize (T.edgeLeft e) at hcard
  have hP := actual_P_card hL e hs
  have hR := actual_R_card hL e hs
  have hQ := actual_Q_card hL e hs
  have hS := actual_S_card hL e hs
  have hA := D.sideA_card
  have hB := D.sideB_card
  simp only [HalfDepthRows.deltaA, HalfDepthRows.deltaB]
  rcases hclass with h7 | h11
  · right
    simp only [D] at hA hB ⊢
    omega
  · left
    simp only [D] at hA hB ⊢
    omega

/-- The even-edge `±4` relation is likewise intrinsic to the actual tree. -/
theorem actual_even_edge_imbalance
    (hL : IsLeech T) (e : T.Edge) (heven : T.weight e % 2 = 0)
    (hs : T.cutSize e = 9) :
    (actualHalfDepthRows hL e hs).deltaA +
        (actualHalfDepthRows hL e hs).deltaB = 4 ∨
      (actualHalfDepthRows hL e hs).deltaA +
        (actualHalfDepthRows hL e hs).deltaB = -4 := by
  let D := actualHalfDepthRows hL e hs
  have hcard := Fintype.card_congr (evenEdgeRootEvenEquiv T e heven)
  have hclass := t3_order18_class_sizes hL (T.edgeLeft e)
  rw [Fintype.card_sum] at hcard
  change Fintype.card (EvenDomain (T.leftDepth e)) +
      Fintype.card (EvenDomain (T.rightDepth e)) =
        T.parityClassSize (T.edgeLeft e) at hcard
  have hP := actual_P_card hL e hs
  have hR := actual_R_card hL e hs
  have hQ := actual_Q_card hL e hs
  have hS := actual_S_card hL e hs
  have hA := D.sideA_card
  have hB := D.sideB_card
  simp only [HalfDepthRows.deltaA, HalfDepthRows.deltaB]
  rcases hclass with h7 | h11
  · right
    simp only [D] at hA hB ⊢
    omega
  · left
    simp only [D] at hA hB ⊢
    omega

private theorem card_le_interval_of_injective
    {β : Type*} [Fintype β] (f : β → ℕ)
    (hf : Function.Injective f) (m : ℕ) (hrange : ∀ x, f x ≤ m) :
    Fintype.card β ≤ m + 1 := by
  let g : β → Fin (m + 1) := fun x => ⟨f x, Nat.lt_succ_of_le (hrange x)⟩
  have hg : Function.Injective g := by
    intro x y hxy
    apply hf
    exact congrArg Fin.val hxy
  simpa using Fintype.card_le_of_injective g hg

private theorem actual_q67_product_bound
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 67)
    (hs : T.cutSize e = 9) :
    -3 ≤ (actualHalfDepthRows hL e hs).deltaA *
        (actualHalfDepthRows hL e hs).deltaB ∧
      (actualHalfDepthRows hL e hs).deltaA *
        (actualHalfDepthRows hL e hs).deltaB ≤ 5 := by
  let D := actualHalfDepthRows hL e hs
  have hE := actual_evenExponent_range_q67 hL e hw hs
  have hO := actual_oddExponent_range_q67 hL e hw hs
  have hEc : Fintype.card D.EvenIndex ≤ 44 :=
    card_le_interval_of_injective D.evenExponent
      (actual_evenExponent_injective hL e hs) 43 hE
  have hOc : Fintype.card D.OddIndex ≤ 43 :=
    card_le_interval_of_injective D.oddExponent
      (actual_oddExponent_injective hL e hs) 42 hO
  have himb := actual_odd_edge_imbalance hL e (by norm_num [hw]) hs
  have hA := D.sideA_card
  have hB := D.sideB_card
  have hPle : D.P.card ≤ 9 := by omega
  have hQle : D.Q.card ≤ 9 := by omega
  have hR : D.R.card = 9 - D.P.card := by omega
  have hS : D.S.card = 9 - D.Q.card := by omega
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_coe] at hEc hOc
  change D.deltaA - D.deltaB = 4 ∨ D.deltaA - D.deltaB = -4 at himb
  change -3 ≤ D.deltaA * D.deltaB ∧ D.deltaA * D.deltaB ≤ 5
  simp only [HalfDepthRows.deltaA, HalfDepthRows.deltaB] at himb ⊢
  rw [hR, hS] at hEc hOc himb ⊢
  interval_cases hP : D.P.card <;> interval_cases hQ : D.Q.card
  all_goals norm_num at hEc
  all_goals norm_num at hOc
  all_goals norm_num at himb
  all_goals norm_num

private theorem actual_q66_product_cases
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 66)
    (hs : T.cutSize e = 9) :
    (actualHalfDepthRows hL e hs).deltaA *
        (actualHalfDepthRows hL e hs).deltaB = -5 ∨
      (actualHalfDepthRows hL e hs).deltaA *
        (actualHalfDepthRows hL e hs).deltaB = 3 := by
  let D := actualHalfDepthRows hL e hs
  have hE := actual_evenExponent_range_q66 hL e hw hs
  have hO := actual_oddExponent_range_q66 hL e hw hs
  have hEc : Fintype.card D.EvenIndex ≤ 44 :=
    card_le_interval_of_injective D.evenExponent
      (actual_evenExponent_injective hL e hs) 43 hE
  have hOc : Fintype.card D.OddIndex ≤ 44 :=
    card_le_interval_of_injective D.oddExponent
      (actual_oddExponent_injective hL e hs) 43 hO
  have himb := actual_even_edge_imbalance hL e (by norm_num [hw]) hs
  have hA := D.sideA_card
  have hB := D.sideB_card
  have hPle : D.P.card ≤ 9 := by omega
  have hQle : D.Q.card ≤ 9 := by omega
  have hR : D.R.card = 9 - D.P.card := by omega
  have hS : D.S.card = 9 - D.Q.card := by omega
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_coe] at hEc hOc
  change D.deltaA + D.deltaB = 4 ∨ D.deltaA + D.deltaB = -4 at himb
  change D.deltaA * D.deltaB = -5 ∨ D.deltaA * D.deltaB = 3
  simp only [HalfDepthRows.deltaA, HalfDepthRows.deltaB] at himb ⊢
  rw [hR, hS] at hEc hOc himb ⊢
  interval_cases hP : D.P.card <;> interval_cases hQ : D.Q.card
  all_goals norm_num at hEc
  all_goals norm_num at hOc
  all_goals norm_num at himb
  all_goals norm_num

/-- Actual q=67 constructor.  All fields are proved from `T`, `hL`, and the
actual balanced weight-67 edge. -/
noncomputable def actualQ67System
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 67)
    (hs : T.cutSize e = 9) : Q67System where
  toHalfDepthRows := actualHalfDepthRows hL e hs
  even_direct := actual_evenExponent_injective hL e hs
  odd_direct := actual_oddExponent_injective hL e hs
  P_bound := (actual_q67_individual_bounds hL e hw hs).1
  Q_bound := (actual_q67_individual_bounds hL e hw hs).2.1
  R_bound := (actual_q67_individual_bounds hL e hw hs).2.2.1
  S_bound := (actual_q67_individual_bounds hL e hw hs).2.2.2
  even_range := actual_evenExponent_range_q67 hL e hw hs
  odd_range := actual_oddExponent_range_q67 hL e hw hs
  imbalance_relation := actual_odd_edge_imbalance hL e (by norm_num [hw]) hs
  product_bound := actual_q67_product_bound hL e hw hs

/-- Actual q=66 constructor, including the derived `-5`/`3` alternative. -/
noncomputable def actualQ66System
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 66)
    (hs : T.cutSize e = 9) : Q66System where
  toHalfDepthRows := actualHalfDepthRows hL e hs
  even_direct := actual_evenExponent_injective hL e hs
  odd_direct := actual_oddExponent_injective hL e hs
  all_bound := by
    intro x hx
    rcases hx with hP | hR | hQ | hS
    · exact (actual_q66_individual_bounds hL e hw hs).1 x hP
    · let D := actualHalfDepthRows hL e hs
      let i : D.OddIndex := Sum.inr (⟨x, hR⟩, ⟨0, D.rootQ⟩)
      simpa [i, D, HalfDepthRows.oddExponent] using
        actual_oddExponent_range_q66 hL e hw hs i
    · exact (actual_q66_individual_bounds hL e hw hs).2 x hQ
    · let D := actualHalfDepthRows hL e hs
      let i : D.OddIndex := Sum.inl (⟨0, D.rootP⟩, ⟨x, hS⟩)
      simpa [i, D, HalfDepthRows.oddExponent] using
        actual_oddExponent_range_q66 hL e hw hs i
  even_range := actual_evenExponent_range_q66 hL e hw hs
  odd_range := actual_oddExponent_range_q66 hL e hw hs
  imbalance_relation := actual_even_edge_imbalance hL e (by norm_num [hw]) hs
  product_cases := actual_q66_product_cases hL e hw hs

theorem actual_q67_three_shapes
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 67)
    (hs : T.cutSize e = 9) :
    let D := actualQ67System hL e hw hs
    (D.deltaA = -1 ∧ D.deltaB = -5) ∨
    (D.deltaA = -5 ∧ D.deltaB = -1) ∨
    (D.deltaA = 1 ∧ D.deltaB = 5) ∨
    (D.deltaA = 5 ∧ D.deltaB = 1) ∨
    (D.deltaA = 1 ∧ D.deltaB = -3) ∨
    (D.deltaA = -3 ∧ D.deltaB = 1) ∨
    (D.deltaA = 3 ∧ D.deltaB = -1) ∨
    (D.deltaA = -1 ∧ D.deltaB = 3) :=
  Q67System.complete_delta_shapes (actualQ67System hL e hw hs)

/-- Receipt atom B as one actual-tree endpoint.  Each of the three shape
classes is bundled with its exact principal hole equation and the cardinality
of the complementary block.  The displayed delta pairs, together with the
two nine-vertex side-cardinality equations in `D`, determine the dimensions
listed in the receipt. -/
theorem actual_q67_three_shapes_and_holes
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 67)
    (hs : T.cutSize e = 9) :
    let D := actualQ67System hL e hw hs
    ((((D.deltaA = -1 ∧ D.deltaB = -5) ∨
        (D.deltaA = -5 ∧ D.deltaB = -1)) ∧
        ∃ j ∈ Finset.Icc 1 43,
          holes D.evenExponent 43 = {j} ∧
          (holes D.oddExponent 42).card = 5) ∨
      (((D.deltaA = 1 ∧ D.deltaB = 5) ∨
        (D.deltaA = 5 ∧ D.deltaB = 1)) ∧
        ∃ j ∈ Finset.Icc 1 43,
          holes D.evenExponent 43 = {j} ∧
          (holes D.oddExponent 42).card = 5) ∨
      (D.deltaA * D.deltaB = -3 ∧
        ∃ j ∈ Finset.Icc 0 42,
          holes D.oddExponent 42 = {j} ∧
          (holes D.evenExponent 43).card = 5 ∧
          0 ∉ holes D.evenExponent 43)) := by
  dsimp only
  let D := actualQ67System hL e hw hs
  change
    ((((D.deltaA = -1 ∧ D.deltaB = -5) ∨
        (D.deltaA = -5 ∧ D.deltaB = -1)) ∧
        ∃ j ∈ Finset.Icc 1 43,
          holes D.evenExponent 43 = {j} ∧
          (holes D.oddExponent 42).card = 5) ∨
      (((D.deltaA = 1 ∧ D.deltaB = 5) ∨
        (D.deltaA = 5 ∧ D.deltaB = 1)) ∧
        ∃ j ∈ Finset.Icc 1 43,
          holes D.evenExponent 43 = {j} ∧
          (holes D.oddExponent 42).card = 5) ∨
      (D.deltaA * D.deltaB = -3 ∧
        ∃ j ∈ Finset.Icc 0 42,
          holes D.oddExponent 42 = {j} ∧
          (holes D.evenExponent 43).card = 5 ∧
          0 ∉ holes D.evenExponent 43))
  rcases D.three_shape_disjunction with hneg | hpos | hthree
  · left
    refine ⟨hneg, D.product_five_exact_hole_system ?_⟩
    rcases hneg with ⟨hA, hB⟩ | ⟨hA, hB⟩ <;> norm_num [hA, hB]
  · right
    left
    refine ⟨hpos, D.product_five_exact_hole_system ?_⟩
    rcases hpos with ⟨hA, hB⟩ | ⟨hA, hB⟩ <;> norm_num [hA, hB]
  · exact Or.inr (Or.inr
      ⟨hthree, D.product_neg_three_exact_hole_system hthree⟩)

theorem actual_q66_branch_shapes
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 66)
    (hs : T.cutSize e = 9) :
    let D := actualQ66System hL e hw hs
    ((D.deltaA = 1 ∧ D.deltaB = -5) ∨
      (D.deltaA = 5 ∧ D.deltaB = -1) ∨
      (D.deltaA = -1 ∧ D.deltaB = 5) ∨
      (D.deltaA = -5 ∧ D.deltaB = 1)) ∨
    ((D.deltaA = 1 ∧ D.deltaB = 3) ∨
      (D.deltaA = 3 ∧ D.deltaB = 1) ∨
      (D.deltaA = -1 ∧ D.deltaB = -3) ∨
      (D.deltaA = -3 ∧ D.deltaB = -1)) := by
  exact Q66System.complete_branch_delta_shapes (actualQ66System hL e hw hs)

/-! ## Actual boundary incidence: small physical edges and the maximum path -/

noncomputable def weightOneEdge (hL : IsLeech T) : T.Edge :=
  Classical.choose (t1_existsUnique_weight_one hL (by omega))

noncomputable def weightTwoEdge (hL : IsLeech T) : T.Edge :=
  Classical.choose (t1_existsUnique_weight_two hL (by omega))

theorem weightOneEdge_weight (hL : IsLeech T) :
    T.weight (weightOneEdge hL) = 1 :=
  (Classical.choose_spec (t1_existsUnique_weight_one hL (by omega))).1

theorem weightTwoEdge_weight (hL : IsLeech T) :
    T.weight (weightTwoEdge hL) = 2 :=
  (Classical.choose_spec (t1_existsUnique_weight_two hL (by omega))).1

noncomputable def maximumPair (hL : IsLeech T) : VertexPair 18 :=
  Classical.choose (hL.target_existsUnique 153 (by norm_num [targetN, Nat.choose]))

theorem maximumPair_dist (hL : IsLeech T) :
    T.pairDist (maximumPair hL) = 153 :=
  (Classical.choose_spec
    (hL.target_existsUnique 153 (by norm_num [targetN, Nat.choose]))).1

private theorem sym2_pairOfDistinct (u v : Fin 18) (huv : u ≠ v) :
    s((VertexPair.ofDistinct u v huv).left,
      (VertexPair.ofDistinct u v huv).right) = s(u, v) := by
  by_cases h : u < v
  · simp [VertexPair.ofDistinct, h, VertexPair.left, VertexPair.right]
  · simp [VertexPair.ofDistinct, h, VertexPair.left, VertexPair.right,
      Sym2.eq_swap]

private theorem endpoint_mem_edgePair_eq
    (f : T.Edge) (u v : Fin 18) (huv : u ≠ v)
    (hp : VertexPair.ofDistinct u v huv = T.edgePair f) :
    u ∈ f.1 ∧ v ∈ f.1 := by
  have hf : f.1 = s(u, v) := by
    calc
      f.1 = s(T.edgeLeft f, T.edgeRight f) := T.edge_eq_mk_endpoints f
      _ = s((T.edgePair f).left, (T.edgePair f).right) := rfl
      _ = s((VertexPair.ofDistinct u v huv).left,
          (VertexPair.ofDistinct u v huv).right) := by rw [hp]
      _ = s(u, v) := sym2_pairOfDistinct u v huv
  rw [hf]
  simp

private theorem edgeLeft_mem_edge (e : T.Edge) : T.edgeLeft e ∈ e.1 := by
  rw [T.edge_eq_mk_endpoints e]
  simp

private theorem edgeRight_mem_edge (e : T.Edge) : T.edgeRight e ∈ e.1 := by
  rw [T.edge_eq_mk_endpoints e]
  simp

/-- For every actual target residual, rooted-offset membership is equivalent
to path incidence of the uniquely named target pair. -/
theorem crossOffset_mem_iff_named_target_path
    (hL : IsLeech T) (e : T.Edge) (r : ℕ)
    (hr : T.weight e + r ∈ Finset.Icc 1 153) :
    r ∈ T.crossOffsetSpectrum e ↔
      e.1 ∈ T.pathEdges
        (Classical.choose (hL.target_existsUnique (T.weight e + r)
          (by simpa [targetN] using hr))).left
        (Classical.choose (hL.target_existsUnique (T.weight e + r)
          (by simpa [targetN] using hr))).right := by
  classical
  let p : VertexPair 18 := Classical.choose
    (hL.target_existsUnique (T.weight e + r) (by simpa [targetN] using hr))
  have hp : T.pairDist p = T.weight e + r :=
    (Classical.choose_spec
      (hL.target_existsUnique (T.weight e + r)
        (by simpa [targetN] using hr))).1
  change r ∈ T.crossOffsetSpectrum e ↔
    e.1 ∈ T.pathEdges p.left p.right
  constructor
  · intro hm
    rw [PosIntTree.crossOffsetSpectrum, Finset.mem_image] at hm
    rcases hm with ⟨x, _, hx⟩
    have hdist : T.pairDist (T.crossVertexPair e x) = T.pairDist p := by
      rw [T.pairDist_crossVertexPair e,
        ← T.weight_add_edgeOffset e x, hx, hp]
    have heq := hL.pairDist_injective hdist
    simpa [heq] using T.crossVertexPair_crosses e x
  · intro hpath
    obtain ⟨x, hx⟩ := T.exists_cross_index_of_crossing e p hpath
    rw [PosIntTree.crossOffsetSpectrum, Finset.mem_image]
    refine ⟨x, Finset.mem_univ _, ?_⟩
    have hdist : T.rootedCrossSum e x = T.weight e + r := by
      rw [← T.pairDist_crossVertexPair e, hx, hp]
    rw [← T.weight_add_edgeOffset e x] at hdist
    omega

theorem crossOffset_maximum_iff
    (hL : IsLeech T) (e : T.Edge) (r : ℕ)
    (hr : T.weight e + r = 153) :
    r ∈ T.crossOffsetSpectrum e ↔
      e.1 ∈ T.pathEdges (maximumPair hL).left (maximumPair hL).right := by
  have htarget : T.weight e + r ∈ Finset.Icc 1 153 := by
    rw [hr]
    simp
  rw [crossOffset_mem_iff_named_target_path hL e r htarget]
  let p : VertexPair 18 := Classical.choose
    (hL.target_existsUnique (T.weight e + r)
      (by simpa [targetN] using htarget))
  have hp : T.pairDist p = 153 := by
    have hp' := (Classical.choose_spec
      (hL.target_existsUnique (T.weight e + r)
        (by simpa [targetN] using htarget))).1
    exact hp'.trans hr
  have heq : p = maximumPair hL :=
    hL.pairDist_injective (hp.trans (maximumPair_dist hL).symm)
  simp only [p] at heq
  rw [heq]

private theorem adjacent_edge_residual_mem
    (e f : T.Edge) (hadj : T.EdgeAdjacent e f) :
    T.weight f ∈ T.crossOffsetSpectrum e := by
  classical
  obtain ⟨v, hve, hvf⟩ := hadj.2
  let x : Fin 18 := Sym2.Mem.other hve
  let y : Fin 18 := Sym2.Mem.other hvf
  have he : s(v, x) = e.1 := Sym2.other_spec hve
  have hf : s(v, y) = f.1 := Sym2.other_spec hvf
  have hvx : T.graph.Adj v x := by
    rw [← SimpleGraph.mem_edgeSet, he]
    exact e.2
  have hvy : T.graph.Adj v y := by
    rw [← SimpleGraph.mem_edgeSet, hf]
    exact f.2
  have hxy : x ≠ y := by
    intro h
    apply hadj.1
    apply Subtype.ext
    rw [← he, ← hf, h]
  let walkXY : T.graph.Walk x y :=
    SimpleGraph.Walk.cons hvx.symm
      (SimpleGraph.Walk.cons hvy SimpleGraph.Walk.nil)
  have hwalkPath : walkXY.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simp [walkXY, hvx.ne.symm, hvy.ne, hxy]
  let pathXY : T.graph.Path x y := ⟨walkXY, hwalkPath⟩
  have hwx : T.weightOfPair s(x, v) = T.weight e := by
    calc
      T.weightOfPair s(x, v) = T.weightOfPair s(v, x) := by rw [Sym2.eq_swap]
      _ = T.weightOfPair e.1 := by rw [he]
      _ = T.weight e := T.weightOfPair_edge e
  have hwy : T.weightOfPair s(v, y) = T.weight f := by
    calc
      T.weightOfPair s(v, y) = T.weightOfPair f.1 := by rw [hf]
      _ = T.weight f := T.weightOfPair_edge f
  have hdist : T.dist x y = T.weight e + T.weight f := by
    calc
      T.dist x y = T.walkWeight pathXY.1 :=
        (T.path_walkWeight_eq_dist pathXY).symm
      _ = T.weight e + T.weight f := by
        simp [pathXY, walkXY, PosIntTree.walkWeight, hwx, hwy]
  let p : VertexPair 18 := VertexPair.ofDistinct x y hxy
  have hpdist : T.pairDist p = T.weight e + T.weight f := by
    rw [T.pairDist_pairOfDistinct]
    exact hdist
  have hpathEq : pathXY = T.path x y := T.path_unique pathXY
  have hcrossXY : e.1 ∈ T.pathEdges x y := by
    unfold PosIntTree.pathEdges
    rw [← hpathEq]
    simp [pathXY, walkXY, ← he, Sym2.eq_swap]
  have hcross : e.1 ∈ T.pathEdges p.left p.right := by
    by_cases hlt : x < y
    · simpa [p, VertexPair.ofDistinct, hlt, VertexPair.left,
        VertexPair.right] using hcrossXY
    · simpa [p, VertexPair.ofDistinct, hlt, VertexPair.left,
        VertexPair.right, T.pathEdges_comm] using hcrossXY
  obtain ⟨z, hz⟩ := T.exists_cross_index_of_crossing e p hcross
  rw [PosIntTree.crossOffsetSpectrum, Finset.mem_image]
  refine ⟨z, Finset.mem_univ _, ?_⟩
  have hroot : T.rootedCrossSum e z = T.weight e + T.weight f := by
    rw [← T.pairDist_crossVertexPair e, hz, hpdist]
  rw [← T.weight_add_edgeOffset e z] at hroot
  omega

private theorem left_depth_edge_adjacent
    (hL : IsLeech T) (e f : T.Edge) (u : T.LeftVertex e) (r : ℕ)
    (hur : T.leftDepth e u = r) (hfr : T.weight f = r)
    (hrpos : 0 < r) (her : T.weight e ≠ r) :
    T.EdgeAdjacent e f := by
  have hune : u.1 ≠ T.edgeLeft e := by
    intro hu
    have hz : T.leftDepth e u = 0 := by
      simp [PosIntTree.leftDepth, hu]
    omega
  let p : VertexPair 18 :=
    VertexPair.ofDistinct u.1 (T.edgeLeft e) hune
  have hpdist : T.pairDist p = r := by
    rw [T.pairDist_pairOfDistinct]
    simpa [p, PosIntTree.leftDepth] using hur
  have hfdist : T.pairDist (T.edgePair f) = r := by
    rw [T.edgePair_dist, hfr]
  have hp : p = T.edgePair f :=
    hL.pairDist_injective (hpdist.trans hfdist.symm)
  have hmem := (endpoint_mem_edgePair_eq f u.1 (T.edgeLeft e) hune hp).2
  refine ⟨?_, T.edgeLeft e, edgeLeft_mem_edge e, hmem⟩
  intro hef
  have hw := congrArg T.weight hef
  rw [hfr] at hw
  exact her hw

private theorem right_depth_edge_adjacent
    (hL : IsLeech T) (e f : T.Edge) (v : T.RightVertex e) (r : ℕ)
    (hvr : T.rightDepth e v = r) (hfr : T.weight f = r)
    (hrpos : 0 < r) (her : T.weight e ≠ r) :
    T.EdgeAdjacent e f := by
  have hvne : T.edgeRight e ≠ v.1 := by
    intro hv
    have hz : T.rightDepth e v = 0 := by
      simp [PosIntTree.rightDepth, hv]
    omega
  let p : VertexPair 18 :=
    VertexPair.ofDistinct (T.edgeRight e) v.1 hvne
  have hpdist : T.pairDist p = r := by
    rw [T.pairDist_pairOfDistinct]
    simpa [p, PosIntTree.rightDepth] using hvr
  have hfdist : T.pairDist (T.edgePair f) = r := by
    rw [T.edgePair_dist, hfr]
  have hp : p = T.edgePair f :=
    hL.pairDist_injective (hpdist.trans hfdist.symm)
  have hmem := (endpoint_mem_edgePair_eq f (T.edgeRight e) v.1 hvne hp).1
  refine ⟨?_, T.edgeRight e, edgeRight_mem_edge e, hmem⟩
  intro hef
  have hw := congrArg T.weight hef
  rw [hfr] at hw
  exact her hw

theorem crossOffset_one_iff_weightOne_adjacent
    (hL : IsLeech T) (e : T.Edge)
    (he : T.weight e = 66 ∨ T.weight e = 67) :
    1 ∈ T.crossOffsetSpectrum e ↔
      T.EdgeAdjacent e (weightOneEdge hL) := by
  classical
  constructor
  · intro hm
    rw [PosIntTree.crossOffsetSpectrum, Finset.mem_image] at hm
    rcases hm with ⟨x, _, hx⟩
    have hsum : T.leftDepth e x.1 + T.rightDepth e x.2 = 1 := by
      simpa [PosIntTree.edgeOffset] using hx
    rcases (show
        (T.leftDepth e x.1 = 1 ∧ T.rightDepth e x.2 = 0) ∨
        (T.leftDepth e x.1 = 0 ∧ T.rightDepth e x.2 = 1) by omega) with
      hleft | hright
    · exact left_depth_edge_adjacent hL e (weightOneEdge hL) x.1 1
        hleft.1 (weightOneEdge_weight hL) (by omega) (by rcases he with h | h <;> omega)
    · exact right_depth_edge_adjacent hL e (weightOneEdge hL) x.2 1
        hright.2 (weightOneEdge_weight hL) (by omega) (by rcases he with h | h <;> omega)
  · intro hadj
    simpa [weightOneEdge_weight hL] using
      adjacent_edge_residual_mem e (weightOneEdge hL) hadj

private theorem one_one_cross_offset_impossible
    (hL : IsLeech T) (e : T.Edge)
    (x : T.LeftVertex e × T.RightVertex e)
    (hleft : T.leftDepth e x.1 = 1)
    (hright : T.rightDepth e x.2 = 1) : False := by
  have hLne : x.1.1 ≠ T.edgeLeft e := by
    intro h
    have : T.leftDepth e x.1 = 0 := by simp [PosIntTree.leftDepth, h]
    omega
  have hRne : T.edgeRight e ≠ x.2.1 := by
    intro h
    have : T.rightDepth e x.2 = 0 := by simp [PosIntTree.rightDepth, h]
    omega
  let pL : VertexPair 18 :=
    VertexPair.ofDistinct x.1.1 (T.edgeLeft e) hLne
  let pR : VertexPair 18 :=
    VertexPair.ofDistinct (T.edgeRight e) x.2.1 hRne
  have hpLdist : T.pairDist pL = 1 := by
    rw [T.pairDist_pairOfDistinct]
    simpa [pL, PosIntTree.leftDepth] using hleft
  have hpRdist : T.pairDist pR = 1 := by
    rw [T.pairDist_pairOfDistinct]
    simpa [pR, PosIntTree.rightDepth] using hright
  have hpair : pL = pR := hL.pairDist_injective (hpLdist.trans hpRdist.symm)
  have hpLL : T.LeftCut e pL.left ∧ T.LeftCut e pL.right := by
    by_cases hlt : x.1.1 < T.edgeLeft e
    · simpa [pL, VertexPair.ofDistinct, hlt, VertexPair.left,
        VertexPair.right] using ⟨x.1.2, T.edgeLeft_mem_LeftCut e⟩
    · simpa [pL, VertexPair.ofDistinct, hlt, VertexPair.left,
        VertexPair.right] using ⟨T.edgeLeft_mem_LeftCut e, x.1.2⟩
  have hpRR : T.RightCut e pR.left ∧ T.RightCut e pR.right := by
    by_cases hlt : T.edgeRight e < x.2.1
    · simpa [pR, VertexPair.ofDistinct, hlt, VertexPair.left,
        VertexPair.right] using ⟨T.edgeRight_mem_RightCut e, x.2.2⟩
    · simpa [pR, VertexPair.ofDistinct, hlt, VertexPair.left,
        VertexPair.right] using ⟨x.2.2, T.edgeRight_mem_RightCut e⟩
  rw [hpair] at hpLL
  exact T.LeftCut_disjoint_RightCut e pR.left ⟨hpLL.1, hpRR.1⟩

theorem crossOffset_two_iff_weightTwo_adjacent
    (hL : IsLeech T) (e : T.Edge)
    (he : T.weight e = 66 ∨ T.weight e = 67) :
    2 ∈ T.crossOffsetSpectrum e ↔
      T.EdgeAdjacent e (weightTwoEdge hL) := by
  classical
  constructor
  · intro hm
    rw [PosIntTree.crossOffsetSpectrum, Finset.mem_image] at hm
    rcases hm with ⟨x, _, hx⟩
    have hsum : T.leftDepth e x.1 + T.rightDepth e x.2 = 2 := by
      simpa [PosIntTree.edgeOffset] using hx
    rcases (show
        (T.leftDepth e x.1 = 2 ∧ T.rightDepth e x.2 = 0) ∨
        (T.leftDepth e x.1 = 0 ∧ T.rightDepth e x.2 = 2) ∨
        (T.leftDepth e x.1 = 1 ∧ T.rightDepth e x.2 = 1) by omega) with
      hleft | hright | honeone
    · exact left_depth_edge_adjacent hL e (weightTwoEdge hL) x.1 2
        hleft.1 (weightTwoEdge_weight hL) (by omega) (by rcases he with h | h <;> omega)
    · exact right_depth_edge_adjacent hL e (weightTwoEdge hL) x.2 2
        hright.2 (weightTwoEdge_weight hL) (by omega) (by rcases he with h | h <;> omega)
    · exact (one_one_cross_offset_impossible hL e x honeone.1 honeone.2).elim
  · intro hadj
    simpa [weightTwoEdge_weight hL] using
      adjacent_edge_residual_mem e (weightTwoEdge hL) hadj

/-- Receipt atom C, now ending at actual physical incidence and the actual
unique distance-153 path. -/
theorem actual_q67_product_five_boundary
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 67)
    (hs : T.cutSize e = 9) {j : ℕ}
    (hholes : holes (actualQ67System hL e hw hs).evenExponent 43 = {j})
    (hj : j ∈ Finset.Icc 1 43) :
    (j ≠ 1 ↔ T.EdgeAdjacent e (weightTwoEdge hL)) ∧
      (j ≠ 43 ↔ e.1 ∈ T.pathEdges
        (maximumPair hL).left (maximumPair hL).right) := by
  let D := actualQ67System hL e hw hs
  have hrow := D.product_five_boundary_memberships hholes hj
  constructor
  · calc
      j ≠ 1 ↔ 1 ∈ imageSet D.evenExponent := hrow.1
      _ ↔ 2 ∈ T.crossOffsetSpectrum e := by
        simpa [D, actualQ67System] using
          mem_actual_even_image_iff_crossOffset hL e hs 1
      _ ↔ T.EdgeAdjacent e (weightTwoEdge hL) :=
        crossOffset_two_iff_weightTwo_adjacent hL e (Or.inr hw)
  · calc
      j ≠ 43 ↔ 43 ∈ imageSet D.evenExponent := hrow.2
      _ ↔ 86 ∈ T.crossOffsetSpectrum e := by
        simpa [D, actualQ67System] using
          mem_actual_even_image_iff_crossOffset hL e hs 43
      _ ↔ e.1 ∈ T.pathEdges
          (maximumPair hL).left (maximumPair hL).right :=
        crossOffset_maximum_iff hL e 86 (by omega)

theorem actual_q67_product_neg_three_boundary
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 67)
    (hs : T.cutSize e = 9) {j : ℕ}
    (hholes : holes (actualQ67System hL e hw hs).oddExponent 42 = {j})
    (_hj : j ∈ Finset.Icc 0 42) :
    j ≠ 0 ↔ T.EdgeAdjacent e (weightOneEdge hL) := by
  let D := actualQ67System hL e hw hs
  calc
    j ≠ 0 ↔ 0 ∉ holes D.oddExponent 42 := by rw [hholes]; simp [ne_comm]
    _ ↔ 0 ∈ imageSet D.oddExponent :=
      not_mem_holes_iff_mem_image _ (by simp [interval])
    _ ↔ 1 ∈ T.crossOffsetSpectrum e := by
      simpa [D, actualQ67System] using
        mem_actual_odd_image_iff_crossOffset hL e hs 0
    _ ↔ T.EdgeAdjacent e (weightOneEdge hL) :=
      crossOffset_one_iff_weightOne_adjacent hL e (Or.inr hw)

theorem actual_q66_negative_five_boundary
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 66)
    (hs : T.cutSize e = 9) {j : ℕ}
    (hholes : holes (actualQ66System hL e hw hs).oddExponent 43 = {j})
    (hj : j ∈ Finset.Icc 0 43) :
    (j ≠ 0 ↔ T.EdgeAdjacent e (weightOneEdge hL)) ∧
      (j ≠ 43 ↔ e.1 ∈ T.pathEdges
        (maximumPair hL).left (maximumPair hL).right) := by
  let D := actualQ66System hL e hw hs
  have hrow := D.negative_five_boundary_memberships hholes hj
  constructor
  · calc
      j ≠ 0 ↔ 0 ∈ D.R ∨ 0 ∈ D.S := hrow.1
      _ ↔ 0 ∈ imageSet D.oddExponent := D.zero_mem_odd_image_iff.symm
      _ ↔ 1 ∈ T.crossOffsetSpectrum e := by
        simpa [D, actualQ66System] using
          mem_actual_odd_image_iff_crossOffset hL e hs 0
      _ ↔ T.EdgeAdjacent e (weightOneEdge hL) :=
        crossOffset_one_iff_weightOne_adjacent hL e (Or.inl hw)
  · calc
      j ≠ 43 ↔ 43 ∈ imageSet D.oddExponent := hrow.2
      _ ↔ 87 ∈ T.crossOffsetSpectrum e := by
        simpa [D, actualQ66System] using
          mem_actual_odd_image_iff_crossOffset hL e hs 43
      _ ↔ e.1 ∈ T.pathEdges
          (maximumPair hL).left (maximumPair hL).right :=
        crossOffset_maximum_iff hL e 87 (by omega)

theorem actual_q66_product_three_low_boundary
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 66)
    (hs : T.cutSize e = 9) {j₁ j₂ : ℕ}
    (hholes : holes (actualQ66System hL e hw hs).evenExponent 43 = {j₁, j₂})
    (hj₁ : j₁ ∈ Finset.Icc 1 43) (hj₂ : j₂ ∈ Finset.Icc 1 43) :
    1 ∉ ({j₁, j₂} : Finset ℕ) ↔
      T.EdgeAdjacent e (weightTwoEdge hL) := by
  let D := actualQ66System hL e hw hs
  calc
    1 ∉ ({j₁, j₂} : Finset ℕ) ↔ 1 ∈ imageSet D.evenExponent :=
      D.product_three_low_boundary_membership hholes hj₁ hj₂
    _ ↔ 2 ∈ T.crossOffsetSpectrum e := by
      simpa [D, actualQ66System] using
        mem_actual_even_image_iff_crossOffset hL e hs 1
    _ ↔ T.EdgeAdjacent e (weightTwoEdge hL) :=
      crossOffset_two_iff_weightTwo_adjacent hL e (Or.inl hw)

/-- The derivative and alternating checksums no longer need a separately
assumed image equation: the exact hole equation plus the actual range derives
it. -/
theorem actual_q67_negative_five_checksums
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 67)
    (hs : T.cutSize e = 9) {j : ℕ}
    (hA : (actualQ67System hL e hw hs).deltaA = -1)
    (hB : (actualQ67System hL e hw hs).deltaB = -5)
    (hj : j ∈ interval 43)
    (hholes : holes (actualQ67System hL e hw hs).evenExponent 43 = {j}) :
    (2 * rowSum (actualQ67System hL e hw hs).P +
        4 * rowSum (actualQ67System hL e hw hs).Q +
        7 * rowSum (actualQ67System hL e hw hs).R +
        5 * rowSum (actualQ67System hL e hw hs).S + 35 = 946 - j) ∧
      (alternatingMass (actualQ67System hL e hw hs).P *
          alternatingMass (actualQ67System hL e hw hs).Q -
          alternatingMass (actualQ67System hL e hw hs).R *
          alternatingMass (actualQ67System hL e hw hs).S =
        (-1 : ℤ) ^ (j + 1)) := by
  let D := actualQ67System hL e hw hs
  have himage : imageSet D.evenExponent = interval 43 \ {j} :=
    image_eq_interval_sdiff_of_holes_eq D.evenExponent 43 {j}
      D.even_range hholes
  exact ⟨D.negative_five_derivative_checksum hA hB hj himage,
    D.product_five_alternating_checksum hj himage⟩

theorem actual_q67_product_neg_three_checksums
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 67)
    (hs : T.cutSize e = 9) {j : ℕ}
    (hA : (actualQ67System hL e hw hs).deltaA = 1)
    (hB : (actualQ67System hL e hw hs).deltaB = -3)
    (hj : j ∈ interval 42)
    (hholes : holes (actualQ67System hL e hw hs).oddExponent 42 = {j}) :
    (6 * rowSum (actualQ67System hL e hw hs).P +
        5 * rowSum (actualQ67System hL e hw hs).S +
        3 * rowSum (actualQ67System hL e hw hs).R +
        4 * rowSum (actualQ67System hL e hw hs).Q = 903 - j) ∧
      (alternatingMass (actualQ67System hL e hw hs).P *
          alternatingMass (actualQ67System hL e hw hs).S +
          alternatingMass (actualQ67System hL e hw hs).R *
          alternatingMass (actualQ67System hL e hw hs).Q =
        1 - (-1 : ℤ) ^ j) := by
  let D := actualQ67System hL e hw hs
  have himage : imageSet D.oddExponent = interval 42 \ {j} :=
    image_eq_interval_sdiff_of_holes_eq D.oddExponent 42 {j}
      D.odd_range hholes
  exact ⟨D.product_neg_three_derivative_checksum hA hB hj himage,
    D.product_neg_three_alternating_checksum hj himage⟩

/-! ## Actual depth-span inequalities -/

private noncomputable def sortedEquiv {β : Type*} [Fintype β]
    (key : β → ℕ) : Fin (Fintype.card β) ≃ β :=
  let base : Fin (Fintype.card β) ≃ β := (Fintype.equivFin β).symm
  let tupleKey : Fin (Fintype.card β) → ℕ := fun i => key (base i)
  (Tuple.sort tupleKey).trans base

private theorem sortedEquiv_strictMono {β : Type*} [Fintype β]
    (key : β → ℕ) (hinj : Function.Injective key) :
    StrictMono (fun i => key (sortedEquiv key i)) := by
  let base : Fin (Fintype.card β) ≃ β := (Fintype.equivFin β).symm
  let tupleKey : Fin (Fintype.card β) → ℕ := fun i => key (base i)
  have hmono : Monotone (fun i => key (sortedEquiv key i)) := by
    simpa [sortedEquiv, base, tupleKey, Function.comp_def] using
      Tuple.monotone_sort tupleKey
  exact hmono.strictMono_of_injective (hinj.comp (sortedEquiv key).injective)

private theorem pathEdges_subset_via_root
    (T : PosIntTree 18) (u v r : Fin 18) :
    T.pathEdges u v ⊆ T.pathEdges u r ∪ T.pathEdges r v := by
  intro f hf
  rw [Finset.mem_union]
  let ef : T.Edge := ⟨f, T.pathEdges_subset_edgeSet u v hf⟩
  have hopp := (T.mem_pathEdges_iff_opposite_cuts ef u v).1 hf
  rcases T.cut_cover ef r with hrL | hrR
  · rcases hopp with ⟨huL, hvR⟩ | ⟨huR, hvL⟩
    · exact Or.inr <| by
        simpa [ef] using (T.mem_pathEdges_iff_opposite_cuts ef r v).2
          (Or.inl ⟨hrL, hvR⟩)
    · exact Or.inl <| by
        simpa [ef] using (T.mem_pathEdges_iff_opposite_cuts ef u r).2
          (Or.inr ⟨huR, hrL⟩)
  · rcases hopp with ⟨huL, hvR⟩ | ⟨huR, hvL⟩
    · exact Or.inl <| by
        simpa [ef] using (T.mem_pathEdges_iff_opposite_cuts ef u r).2
          (Or.inl ⟨huL, hrR⟩)
    · exact Or.inr <| by
        simpa [ef] using (T.mem_pathEdges_iff_opposite_cuts ef r v).2
          (Or.inr ⟨hrR, hvL⟩)

private theorem dist_triangle
    (T : PosIntTree 18) (u v r : Fin 18) :
    T.dist u v ≤ T.dist u r + T.dist r v := by
  classical
  unfold PosIntTree.dist
  calc
    (∑ f ∈ T.pathEdges u v, T.weightOfPair f) ≤
        ∑ f ∈ T.pathEdges u r ∪ T.pathEdges r v, T.weightOfPair f :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (pathEdges_subset_via_root T u v r) (fun _ _ _ => Nat.zero_le _)
    _ ≤ (∑ f ∈ T.pathEdges u r, T.weightOfPair f) +
        ∑ f ∈ T.pathEdges r v, T.weightOfPair f := by
      have hsum := Finset.sum_union_inter
        (s₁ := T.pathEdges u r) (s₂ := T.pathEdges r v)
        (f := T.weightOfPair)
      omega

private noncomputable def leftNineIndex (e : T.Edge) (hs : T.cutSize e = 9)
    (i : Fin 9) : Fin (Fintype.card (T.LeftVertex e)) :=
  ⟨i.1, by change i.1 < T.cutSize e; rw [hs]; exact i.2⟩

private noncomputable def rightNineIndex (e : T.Edge) (hs : T.cutSize e = 9)
    (i : Fin 9) : Fin (Fintype.card (T.RightVertex e)) :=
  ⟨i.1, by rw [T.rightVertex_card e, hs]; norm_num⟩

private theorem leftNineIndex_injective (e : T.Edge) (hs : T.cutSize e = 9) :
    Function.Injective (leftNineIndex e hs) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun z : Fin (Fintype.card (T.LeftVertex e)) => z.1) h

private theorem rightNineIndex_injective (e : T.Edge) (hs : T.cutSize e = 9) :
    Function.Injective (rightNineIndex e hs) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun z : Fin (Fintype.card (T.RightVertex e)) => z.1) h

noncomputable def leftVertexAt
    (_hL : IsLeech T) (e : T.Edge) (hs : T.cutSize e = 9) (i : Fin 9) :
    T.LeftVertex e :=
  sortedEquiv (T.leftDepth e) (leftNineIndex e hs i)

noncomputable def rightVertexAt
    (_hL : IsLeech T) (e : T.Edge) (hs : T.cutSize e = 9) (i : Fin 9) :
    T.RightVertex e :=
  sortedEquiv (T.rightDepth e) (rightNineIndex e hs i)

noncomputable def leftSortedDepth
    (hL : IsLeech T) (e : T.Edge) (hs : T.cutSize e = 9) (i : Fin 9) : ℕ :=
  T.leftDepth e (leftVertexAt hL e hs i)

noncomputable def rightSortedDepth
    (hL : IsLeech T) (e : T.Edge) (hs : T.cutSize e = 9) (i : Fin 9) : ℕ :=
  T.rightDepth e (rightVertexAt hL e hs i)

theorem leftSortedDepth_strictMono
    (hL : IsLeech T) (e : T.Edge) (hs : T.cutSize e = 9) :
    StrictMono (leftSortedDepth hL e hs) := by
  intro i j hij
  exact sortedEquiv_strictMono (T.leftDepth e)
    (T.leftDepth_injective hL e)
    (show leftNineIndex e hs i < leftNineIndex e hs j by exact hij)

theorem rightSortedDepth_strictMono
    (hL : IsLeech T) (e : T.Edge) (hs : T.cutSize e = 9) :
    StrictMono (rightSortedDepth hL e hs) := by
  intro i j hij
  exact sortedEquiv_strictMono (T.rightDepth e)
    (T.rightDepth_injective hL e)
    (show rightNineIndex e hs i < rightNineIndex e hs j by exact hij)

private noncomputable def leftInternalPair
    (hL : IsLeech T) (e : T.Edge) (hs : T.cutSize e = 9)
    (p : VertexPair 9) : VertexPair 18 :=
  VertexPair.ofDistinct (leftVertexAt hL e hs p.left).1
    (leftVertexAt hL e hs p.right).1 (by
      intro h
      have hv : leftVertexAt hL e hs p.left =
          leftVertexAt hL e hs p.right := Subtype.ext h
      have hi := (sortedEquiv (T.leftDepth e)).injective hv
      have hi' := leftNineIndex_injective e hs hi
      exact (ne_of_lt p.left_lt_right) hi')

private noncomputable def rightInternalPair
    (hL : IsLeech T) (e : T.Edge) (hs : T.cutSize e = 9)
    (p : VertexPair 9) : VertexPair 18 :=
  VertexPair.ofDistinct (rightVertexAt hL e hs p.left).1
    (rightVertexAt hL e hs p.right).1 (by
      intro h
      have hv : rightVertexAt hL e hs p.left =
          rightVertexAt hL e hs p.right := Subtype.ext h
      have hi := (sortedEquiv (T.rightDepth e)).injective hv
      have hi' := rightNineIndex_injective e hs hi
      exact (ne_of_lt p.left_lt_right) hi')

private theorem leftInternalPair_injective
    (hL : IsLeech T) (e : T.Edge) (hs : T.cutSize e = 9) :
    Function.Injective (leftInternalPair hL e hs) := by
  intro p q hpq
  have hsym0 := congrArg (fun z : VertexPair 18 => s(z.left, z.right)) hpq
  have hsym : s((leftVertexAt hL e hs p.left).1,
      (leftVertexAt hL e hs p.right).1) =
      s((leftVertexAt hL e hs q.left).1,
        (leftVertexAt hL e hs q.right).1) := by
    simpa only [leftInternalPair, sym2_pairOfDistinct] using hsym0
  have hpair : s(p.left, p.right) = s(q.left, q.right) := by
    have hinj : Function.Injective (fun i : Fin 9 =>
        (leftVertexAt hL e hs i).1) := by
      intro i j hij
      have hv : leftVertexAt hL e hs i = leftVertexAt hL e hs j := Subtype.ext hij
      exact leftNineIndex_injective e hs ((sortedEquiv _).injective hv)
    apply Sym2.map.injective hinj
    simpa only [Sym2.map_pair_eq] using hsym
  apply VertexPair.ext
  · simpa [le_of_lt p.left_lt_right, le_of_lt q.left_lt_right] using
      congrArg Sym2.inf hpair
  · simpa [le_of_lt p.left_lt_right, le_of_lt q.left_lt_right] using
      congrArg Sym2.sup hpair

private theorem rightInternalPair_injective
    (hL : IsLeech T) (e : T.Edge) (hs : T.cutSize e = 9) :
    Function.Injective (rightInternalPair hL e hs) := by
  intro p q hpq
  have hsym0 := congrArg (fun z : VertexPair 18 => s(z.left, z.right)) hpq
  have hsym : s((rightVertexAt hL e hs p.left).1,
      (rightVertexAt hL e hs p.right).1) =
      s((rightVertexAt hL e hs q.left).1,
        (rightVertexAt hL e hs q.right).1) := by
    simpa only [rightInternalPair, sym2_pairOfDistinct] using hsym0
  have hpair : s(p.left, p.right) = s(q.left, q.right) := by
    have hinj : Function.Injective (fun i : Fin 9 =>
        (rightVertexAt hL e hs i).1) := by
      intro i j hij
      have hv : rightVertexAt hL e hs i = rightVertexAt hL e hs j := Subtype.ext hij
      exact rightNineIndex_injective e hs ((sortedEquiv _).injective hv)
    apply Sym2.map.injective hinj
    simpa only [Sym2.map_pair_eq] using hsym
  apply VertexPair.ext
  · simpa [le_of_lt p.left_lt_right, le_of_lt q.left_lt_right] using
      congrArg Sym2.inf hpair
  · simpa [le_of_lt p.left_lt_right, le_of_lt q.left_lt_right] using
      congrArg Sym2.sup hpair

private theorem left_internal_distance_le_top_two
    (hL : IsLeech T) (e : T.Edge) (hs : T.cutSize e = 9)
    (p : VertexPair 9) :
    T.pairDist (leftInternalPair hL e hs p) ≤
      leftSortedDepth hL e hs ⟨7, by omega⟩ +
        leftSortedDepth hL e hs ⟨8, by omega⟩ := by
  have htri := dist_triangle T
    (leftVertexAt hL e hs p.left).1
    (leftVertexAt hL e hs p.right).1 (T.edgeLeft e)
  have hleftIndex : p.left ≤ (⟨7, by omega⟩ : Fin 9) := by
    change p.left.1 ≤ 7
    have hpOrder := p.left_lt_right
    have hpBound := p.right.isLt
    omega
  have hrightIndex : p.right ≤ (⟨8, by omega⟩ : Fin 9) := by
    change p.right.1 ≤ 8
    exact Nat.le_pred_of_lt p.right.isLt
  have hleftDepth := (leftSortedDepth_strictMono hL e hs).monotone hleftIndex
  have hrightDepth := (leftSortedDepth_strictMono hL e hs).monotone hrightIndex
  have hleftDist : T.dist (leftVertexAt hL e hs p.left).1 (T.edgeLeft e) ≤
      leftSortedDepth hL e hs ⟨7, by omega⟩ := by
    simpa only [leftSortedDepth, PosIntTree.leftDepth] using hleftDepth
  have hrightDist : T.dist (T.edgeLeft e) (leftVertexAt hL e hs p.right).1 ≤
      leftSortedDepth hL e hs ⟨8, by omega⟩ := by
    rw [T.dist_comm]
    simpa only [leftSortedDepth, PosIntTree.leftDepth] using hrightDepth
  simpa [leftInternalPair, T.pairDist_pairOfDistinct] using
      htri.trans (Nat.add_le_add hleftDist hrightDist)

private theorem right_internal_distance_le_top_two
    (hL : IsLeech T) (e : T.Edge) (hs : T.cutSize e = 9)
    (p : VertexPair 9) :
    T.pairDist (rightInternalPair hL e hs p) ≤
      rightSortedDepth hL e hs ⟨7, by omega⟩ +
        rightSortedDepth hL e hs ⟨8, by omega⟩ := by
  have htri := dist_triangle T
    (rightVertexAt hL e hs p.left).1
    (rightVertexAt hL e hs p.right).1 (T.edgeRight e)
  have hleftIndex : p.left ≤ (⟨7, by omega⟩ : Fin 9) := by
    change p.left.1 ≤ 7
    have hpOrder := p.left_lt_right
    have hpBound := p.right.isLt
    omega
  have hrightIndex : p.right ≤ (⟨8, by omega⟩ : Fin 9) := by
    change p.right.1 ≤ 8
    exact Nat.le_pred_of_lt p.right.isLt
  have hleftDepth := (rightSortedDepth_strictMono hL e hs).monotone hleftIndex
  have hrightDepth := (rightSortedDepth_strictMono hL e hs).monotone hrightIndex
  have hleftDist : T.dist (rightVertexAt hL e hs p.left).1 (T.edgeRight e) ≤
      rightSortedDepth hL e hs ⟨7, by omega⟩ := by
    rw [T.dist_comm]
    simpa only [rightSortedDepth, PosIntTree.rightDepth] using hleftDepth
  have hrightDist : T.dist (T.edgeRight e) (rightVertexAt hL e hs p.right).1 ≤
      rightSortedDepth hL e hs ⟨8, by omega⟩ := by
    simpa only [rightSortedDepth, PosIntTree.rightDepth] using hrightDepth
  simpa [rightInternalPair, T.pairDist_pairOfDistinct] using
      htri.trans (Nat.add_le_add hleftDist hrightDist)

private theorem thirty_six_le_left_top_two
    (hL : IsLeech T) (e : T.Edge) (hs : T.cutSize e = 9) :
    36 ≤ leftSortedDepth hL e hs ⟨7, by omega⟩ +
      leftSortedDepth hL e hs ⟨8, by omega⟩ := by
  let M := leftSortedDepth hL e hs ⟨7, by omega⟩ +
    leftSortedDepth hL e hs ⟨8, by omega⟩
  let encode : VertexPair 9 → Fin M := fun p =>
    ⟨T.pairDist (leftInternalPair hL e hs p) - 1, by
      have hpos := hL.pairDist_pos (leftInternalPair hL e hs p)
      have hle := left_internal_distance_le_top_two hL e hs p
      exact lt_of_lt_of_le (Nat.sub_lt hpos (by omega)) hle⟩
  have hinj : Function.Injective encode := by
    intro p q hpq
    apply leftInternalPair_injective hL e hs
    apply hL.pairDist_injective
    have hp := hL.pairDist_pos (leftInternalPair hL e hs p)
    have hq := hL.pairDist_pos (leftInternalPair hL e hs q)
    have hsub := congrArg Fin.val hpq
    change T.pairDist (leftInternalPair hL e hs p) - 1 =
      T.pairDist (leftInternalPair hL e hs q) - 1 at hsub
    calc
      T.pairDist (leftInternalPair hL e hs p) =
          (T.pairDist (leftInternalPair hL e hs p) - 1) + 1 :=
        (Nat.sub_add_cancel hp).symm
      _ = (T.pairDist (leftInternalPair hL e hs q) - 1) + 1 := by rw [hsub]
      _ = T.pairDist (leftInternalPair hL e hs q) := Nat.sub_add_cancel hq
  have hc := Fintype.card_le_of_injective encode hinj
  have h36 : Fintype.card (VertexPair 9) = 36 := by decide
  simpa [M, h36] using hc

private theorem thirty_six_le_right_top_two
    (hL : IsLeech T) (e : T.Edge) (hs : T.cutSize e = 9) :
    36 ≤ rightSortedDepth hL e hs ⟨7, by omega⟩ +
      rightSortedDepth hL e hs ⟨8, by omega⟩ := by
  let M := rightSortedDepth hL e hs ⟨7, by omega⟩ +
    rightSortedDepth hL e hs ⟨8, by omega⟩
  let encode : VertexPair 9 → Fin M := fun p =>
    ⟨T.pairDist (rightInternalPair hL e hs p) - 1, by
      have hpos := hL.pairDist_pos (rightInternalPair hL e hs p)
      have hle := right_internal_distance_le_top_two hL e hs p
      exact lt_of_lt_of_le (Nat.sub_lt hpos (by omega)) hle⟩
  have hinj : Function.Injective encode := by
    intro p q hpq
    apply rightInternalPair_injective hL e hs
    apply hL.pairDist_injective
    have hp := hL.pairDist_pos (rightInternalPair hL e hs p)
    have hq := hL.pairDist_pos (rightInternalPair hL e hs q)
    have hsub := congrArg Fin.val hpq
    change T.pairDist (rightInternalPair hL e hs p) - 1 =
      T.pairDist (rightInternalPair hL e hs q) - 1 at hsub
    calc
      T.pairDist (rightInternalPair hL e hs p) =
          (T.pairDist (rightInternalPair hL e hs p) - 1) + 1 :=
        (Nat.sub_add_cancel hp).symm
      _ = (T.pairDist (rightInternalPair hL e hs q) - 1) + 1 := by rw [hsub]
      _ = T.pairDist (rightInternalPair hL e hs q) := Nat.sub_add_cancel hq
  have hc := Fintype.card_le_of_injective encode hinj
  have h36 : Fintype.card (VertexPair 9) = 36 := by decide
  simpa [M, h36] using hc

/-- Receipt atom G's span endpoint, with all five substantive inequalities
derived from the actual tree and the actual balanced weight-66 cut. -/
theorem actual_q66_depth_span
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 66)
    (hs : T.cutSize e = 9) :
    36 ≤ leftSortedDepth hL e hs ⟨7, by omega⟩ +
        leftSortedDepth hL e hs ⟨8, by omega⟩ ∧
      36 ≤ rightSortedDepth hL e hs ⟨7, by omega⟩ +
        rightSortedDepth hL e hs ⟨8, by omega⟩ ∧
      19 ≤ leftSortedDepth hL e hs ⟨8, by omega⟩ ∧
      19 ≤ rightSortedDepth hL e hs ⟨8, by omega⟩ ∧
      leftSortedDepth hL e hs ⟨8, by omega⟩ +
        rightSortedDepth hL e hs ⟨8, by omega⟩ ≤ 87 := by
  have hA := thirty_six_le_left_top_two hL e hs
  have hB := thirty_six_le_right_top_two hL e hs
  have h78 : (7 : Fin 9) < 8 := by decide
  have hAstr := leftSortedDepth_strictMono hL e hs h78
  have hBstr := rightSortedDepth_strictMono hL e hs h78
  let x : T.LeftVertex e × T.RightVertex e :=
    (leftVertexAt hL e hs ⟨8, by omega⟩,
      rightVertexAt hL e hs ⟨8, by omega⟩)
  have htail := (Finset.mem_Icc.mp
    (T.rootedCrossSum_mem_target_tail hL e x)).2
  simp only [PosIntTree.rootedCrossSum] at htail
  change leftSortedDepth hL e hs ⟨8, by omega⟩ + T.weight e +
      rightSortedDepth hL e hs ⟨8, by omega⟩ ≤ targetN 18 at htail
  norm_num [targetN, Nat.choose, hw] at htail
  exact ⟨hA, hB, depth_span_bounds _ _ _ _ hA hB hAstr hBstr (by omega)⟩

/-! ## Coherent raw/half-hole parity and the final actual Gaussian endpoint -/

theorem actual_raw_image_eq_crossOffset
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 66)
    (hs : T.cutSize e = 9) :
    imageSet (actualSevenHoleRows hL e hw hs).addExponent =
      T.crossOffsetSpectrum e := by
  classical
  ext k
  constructor
  · intro hk
    rcases Finset.mem_image.mp hk with ⟨z, _, hz⟩
    rcases Finset.mem_image.mp z.1.2 with ⟨u, _, hu⟩
    rcases Finset.mem_image.mp z.2.2 with ⟨v, _, hv⟩
    rw [PosIntTree.crossOffsetSpectrum, Finset.mem_image]
    refine ⟨(u, v), Finset.mem_univ _, ?_⟩
    change T.leftDepth e u + T.rightDepth e v = k
    change z.1.1 + z.2.1 = k at hz
    rw [hu, hv]
    exact hz
  · intro hk
    rw [PosIntTree.crossOffsetSpectrum, Finset.mem_image] at hk
    rcases hk with ⟨x, _, hx⟩
    let a : ↥(actualSevenHoleRows hL e hw hs).DA :=
      ⟨T.leftDepth e x.1, Finset.mem_image.mpr
        ⟨x.1, Finset.mem_univ _, rfl⟩⟩
    let b : ↥(actualSevenHoleRows hL e hw hs).DB :=
      ⟨T.rightDepth e x.2, Finset.mem_image.mpr
        ⟨x.2, Finset.mem_univ _, rfl⟩⟩
    rw [imageSet, Finset.mem_image]
    refine ⟨(a, b), Finset.mem_univ _, ?_⟩
    simpa [SevenHoleRows.addExponent, a, b, PosIntTree.edgeOffset] using hx

theorem actual_raw_even_hole_iff_half_hole
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 66)
    (hs : T.cutSize e = 9) {j : ℕ} (hj : j ≤ 43) :
    2 * j ∈ (actualSevenHoleRows hL e hw hs).H ↔
      j ∈ holes (actualQ66System hL e hw hs).evenExponent 43 := by
  let R := actualSevenHoleRows hL e hw hs
  let D := actualQ66System hL e hw hs
  have hsupp := mem_actual_even_image_iff_crossOffset hL e hs j
  have himage := actual_raw_image_eq_crossOffset hL e hw hs
  simp only [SevenHoleRows.H, holes, Finset.mem_sdiff]
  rw [himage]
  simp only [interval, Finset.mem_Icc, Nat.zero_le, true_and]
  constructor
  · rintro ⟨_, hn⟩
    exact ⟨hj, fun hm => hn (hsupp.mp (by simpa [D, actualQ66System] using hm))⟩
  · rintro ⟨_, hn⟩
    refine ⟨by omega, ?_⟩
    intro hm
    apply hn
    have : j ∈ imageSet (actualHalfDepthRows hL e hs).evenExponent :=
      hsupp.mpr hm
    simpa [D, actualQ66System] using this

theorem actual_raw_odd_hole_iff_half_hole
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 66)
    (hs : T.cutSize e = 9) {j : ℕ} (hj : j ≤ 43) :
    2 * j + 1 ∈ (actualSevenHoleRows hL e hw hs).H ↔
      j ∈ holes (actualQ66System hL e hw hs).oddExponent 43 := by
  let R := actualSevenHoleRows hL e hw hs
  let D := actualQ66System hL e hw hs
  have hsupp := mem_actual_odd_image_iff_crossOffset hL e hs j
  have himage := actual_raw_image_eq_crossOffset hL e hw hs
  simp only [SevenHoleRows.H, holes, Finset.mem_sdiff]
  rw [himage]
  simp only [interval, Finset.mem_Icc, Nat.zero_le, true_and]
  constructor
  · rintro ⟨_, hn⟩
    exact ⟨hj, fun hm => hn (hsupp.mp (by simpa [D, actualQ66System] using hm))⟩
  · rintro ⟨_, hn⟩
    refine ⟨by omega, ?_⟩
    intro hm
    apply hn
    have : j ∈ imageSet (actualHalfDepthRows hL e hs).oddExponent :=
      hsupp.mpr hm
    simpa [D, actualQ66System] using this

private theorem actual_raw_even_holes_eq_image
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 66)
    (hs : T.cutSize e = 9) :
    (actualSevenHoleRows hL e hw hs).H.filter (fun h => h % 2 = 0) =
      (holes (actualQ66System hL e hw hs).evenExponent 43).image
        (fun j => 2 * j) := by
  classical
  ext h
  constructor
  · intro hh
    have hhH := (Finset.mem_filter.mp hh).1
    have hpar := (Finset.mem_filter.mp hh).2
    have hbound := (Finset.mem_Icc.mp
      ((actualSevenHoleRows hL e hw hs).H_subset_one_87 hhH)).2
    let j := h / 2
    have hj : j ≤ 43 := by omega
    have htwo : 2 * j = h := by
      have hd := Nat.mod_add_div h 2
      omega
    rw [Finset.mem_image]
    exact ⟨j, (actual_raw_even_hole_iff_half_hole hL e hw hs hj).mp
      (by simpa [htwo] using hhH), htwo⟩
  · intro hh
    rcases Finset.mem_image.mp hh with ⟨j, hj, rfl⟩
    have hjrange := (Finset.mem_sdiff.mp hj).1
    have hjle := (Finset.mem_Icc.mp hjrange).2
    rw [Finset.mem_filter]
    exact ⟨(actual_raw_even_hole_iff_half_hole hL e hw hs hjle).2 hj,
      by simp⟩

private theorem actual_raw_odd_holes_eq_image
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 66)
    (hs : T.cutSize e = 9) :
    (actualSevenHoleRows hL e hw hs).H.filter (fun h => h % 2 = 1) =
      (holes (actualQ66System hL e hw hs).oddExponent 43).image
        (fun j => 2 * j + 1) := by
  classical
  ext h
  constructor
  · intro hh
    have hhH := (Finset.mem_filter.mp hh).1
    have hpar := (Finset.mem_filter.mp hh).2
    have hbound := (Finset.mem_Icc.mp
      ((actualSevenHoleRows hL e hw hs).H_subset_one_87 hhH)).2
    let j := h / 2
    have hj : j ≤ 43 := by omega
    have htwo : 2 * j + 1 = h := by
      have hd := Nat.mod_add_div h 2
      omega
    rw [Finset.mem_image]
    exact ⟨j, (actual_raw_odd_hole_iff_half_hole hL e hw hs hj).mp
      (by simpa [htwo] using hhH), htwo⟩
  · intro hh
    rcases Finset.mem_image.mp hh with ⟨j, hj, rfl⟩
    have hjrange := (Finset.mem_sdiff.mp hj).1
    have hjle := (Finset.mem_Icc.mp hjrange).2
    rw [Finset.mem_filter]
    exact ⟨(actual_raw_odd_hole_iff_half_hole hL e hw hs hjle).2 hj,
      by simp⟩

private theorem raw_even_hole_card_eq_half
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 66)
    (hs : T.cutSize e = 9) :
    ((actualSevenHoleRows hL e hw hs).H.filter (fun h => h % 2 = 0)).card =
      (holes (actualQ66System hL e hw hs).evenExponent 43).card := by
  rw [actual_raw_even_holes_eq_image hL e hw hs,
    Finset.card_image_of_injective]
  intro x y hxy
  change 2 * x = 2 * y at hxy
  omega

private theorem raw_odd_hole_card_eq_half
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 66)
    (hs : T.cutSize e = 9) :
    ((actualSevenHoleRows hL e hw hs).H.filter (fun h => h % 2 = 1)).card =
      (holes (actualQ66System hL e hw hs).oddExponent 43).card := by
  rw [actual_raw_odd_holes_eq_image hL e hw hs,
    Finset.card_image_of_injective]
  intro x y hxy
  change 2 * x + 1 = 2 * y + 1 at hxy
  omega

private theorem residueCount_even_four (S : Finset ℕ) :
    residueCount S 4 0 + residueCount S 4 2 =
      (S.filter fun h => h % 2 = 0).card := by
  classical
  unfold residueCount
  have hdis : Disjoint
      (S.filter fun h : ℕ => (h : ZMod 4) = 0)
      (S.filter fun h : ℕ => (h : ZMod 4) = 2) := by
    rw [Finset.disjoint_left]
    intro h h0 h2
    have hz := (Finset.mem_filter.mp h0).2
    have ht := (Finset.mem_filter.mp h2).2
    have hfalse : (0 : ZMod 4) = 2 := hz.symm.trans ht
    exact (by decide : (0 : ZMod 4) ≠ 2) hfalse
  rw [← Finset.card_union_of_disjoint hdis]
  congr 1
  ext h
  have h0 : ((h : ZMod 4) = 0) ↔ h % 4 = 0 := by
    simpa [Nat.ModEq] using (ZMod.natCast_eq_natCast_iff h 0 4)
  have h2 : ((h : ZMod 4) = 2) ↔ h % 4 = 2 := by
    simpa [Nat.ModEq] using (ZMod.natCast_eq_natCast_iff h 2 4)
  simp only [Finset.mem_union, Finset.mem_filter, h0, h2]
  have hpar : h % 4 = 0 ∨ h % 4 = 2 ↔ h % 2 = 0 := by omega
  constructor
  · rintro (⟨hS, hr⟩ | ⟨hS, hr⟩)
    · exact ⟨hS, hpar.mp (Or.inl hr)⟩
    · exact ⟨hS, hpar.mp (Or.inr hr)⟩
  · rintro ⟨hS, heven⟩
    rcases hpar.mpr heven with hr | hr
    · exact Or.inl ⟨hS, hr⟩
    · exact Or.inr ⟨hS, hr⟩

private theorem residueCount_odd_four (S : Finset ℕ) :
    residueCount S 4 1 + residueCount S 4 3 =
      (S.filter fun h => h % 2 = 1).card := by
  classical
  unfold residueCount
  have hdis : Disjoint
      (S.filter fun h : ℕ => (h : ZMod 4) = 1)
      (S.filter fun h : ℕ => (h : ZMod 4) = 3) := by
    rw [Finset.disjoint_left]
    intro h h1 h3
    have ho := (Finset.mem_filter.mp h1).2
    have ht := (Finset.mem_filter.mp h3).2
    have hfalse : (1 : ZMod 4) = 3 := ho.symm.trans ht
    exact (by decide : (1 : ZMod 4) ≠ 3) hfalse
  rw [← Finset.card_union_of_disjoint hdis]
  congr 1
  ext h
  have h1 : ((h : ZMod 4) = 1) ↔ h % 4 = 1 := by
    simpa [Nat.ModEq] using (ZMod.natCast_eq_natCast_iff h 1 4)
  have h3 : ((h : ZMod 4) = 3) ↔ h % 4 = 3 := by
    simpa [Nat.ModEq] using (ZMod.natCast_eq_natCast_iff h 3 4)
  simp only [Finset.mem_union, Finset.mem_filter, h1, h3]
  have hpar : h % 4 = 1 ∨ h % 4 = 3 ↔ h % 2 = 1 := by omega
  constructor
  · rintro (⟨hS, hr⟩ | ⟨hS, hr⟩)
    · exact ⟨hS, hpar.mp (Or.inl hr)⟩
    · exact ⟨hS, hpar.mp (Or.inr hr)⟩
  · rintro ⟨hS, hodd⟩
    rcases hpar.mpr hodd with hr | hr
    · exact Or.inl ⟨hS, hr⟩
    · exact Or.inr ⟨hS, hr⟩

theorem actual_q66_hole_parity_totals
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 66)
    (hs : T.cutSize e = 9) :
    (((actualQ66System hL e hw hs).deltaA *
          (actualQ66System hL e hw hs).deltaB = -5) →
      residueCount (actualSevenHoleRows hL e hw hs).H 4 0 +
          residueCount (actualSevenHoleRows hL e hw hs).H 4 2 = 6 ∧
        residueCount (actualSevenHoleRows hL e hw hs).H 4 1 +
          residueCount (actualSevenHoleRows hL e hw hs).H 4 3 = 1) ∧
    (((actualQ66System hL e hw hs).deltaA *
          (actualQ66System hL e hw hs).deltaB = 3) →
      residueCount (actualSevenHoleRows hL e hw hs).H 4 0 +
          residueCount (actualSevenHoleRows hL e hw hs).H 4 2 = 2 ∧
        residueCount (actualSevenHoleRows hL e hw hs).H 4 1 +
          residueCount (actualSevenHoleRows hL e hw hs).H 4 3 = 5) := by
  have hc := (actualQ66System hL e hw hs).branch_hole_counts
  have heven := residueCount_even_four (actualSevenHoleRows hL e hw hs).H
  have hodd := residueCount_odd_four (actualSevenHoleRows hL e hw hs).H
  have hrawE := raw_even_hole_card_eq_half hL e hw hs
  have hrawO := raw_odd_hole_card_eq_half hL e hw hs
  constructor
  · intro hp
    have hh := hc.1 hp
    omega
  · intro hp
    have hh := hc.2 hp
    omega

theorem actual_raw_hole_sum_split
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 66)
    (hs : T.cutSize e = 9) :
    (∑ h ∈ (actualSevenHoleRows hL e hw hs).H, h) =
      (∑ k ∈ holes (actualQ66System hL e hw hs).evenExponent 43, 2 * k) +
      ∑ j ∈ holes (actualQ66System hL e hw hs).oddExponent 43, (2 * j + 1) := by
  classical
  let R := actualSevenHoleRows hL e hw hs
  let HE := holes (actualQ66System hL e hw hs).evenExponent 43
  let HO := holes (actualQ66System hL e hw hs).oddExponent 43
  have hdis : Disjoint (R.H.filter fun h => h % 2 = 0)
      (R.H.filter fun h => h % 2 = 1) := by
    rw [Finset.disjoint_left]
    intro h he ho
    have he' := (Finset.mem_filter.mp he).2
    have ho' := (Finset.mem_filter.mp ho).2
    omega
  have hpart : (R.H.filter fun h => h % 2 = 0) ∪
      (R.H.filter fun h => h % 2 = 1) = R.H := by
    ext h
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hh, _⟩ | ⟨hh, _⟩)
      · exact hh
      · exact hh
    · intro hh
      have hm := Nat.mod_lt h (by omega : 0 < 2)
      by_cases he : h % 2 = 0
      · exact Or.inl ⟨hh, he⟩
      · exact Or.inr ⟨hh, by omega⟩
  calc
    (∑ h ∈ R.H, h) =
        (∑ h ∈ R.H.filter (fun h => h % 2 = 0), h) +
          ∑ h ∈ R.H.filter (fun h => h % 2 = 1), h := by
      rw [← Finset.sum_union hdis, hpart]
    _ = (∑ k ∈ HE, 2 * k) + ∑ j ∈ HO, (2 * j + 1) := by
      rw [actual_raw_even_holes_eq_image hL e hw hs,
        actual_raw_odd_holes_eq_image hL e hw hs]
      congr 1
      · rw [Finset.sum_image]
        intro x _ y _ hxy
        change 2 * x = 2 * y at hxy
        omega
      · rw [Finset.sum_image]
        intro x _ y _ hxy
        change 2 * x + 1 = 2 * y + 1 at hxy
        omega

/-- Receipt atom F's specialized mod-nine consequences, now tied to the same
actual raw hole set and the same q=66 half-depth system. -/
theorem actual_q66_specialized_congruences
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 66)
    (hs : T.cutSize e = 9) :
    let D := actualQ66System hL e hw hs
    ((D.deltaA * D.deltaB = -5) →
      ∃ j ∈ Finset.Icc 0 43,
        holes D.oddExponent 43 = {j} ∧
        (∑ k ∈ holes D.evenExponent 43, k) + j ≡ 1 [MOD 9]) ∧
    ((D.deltaA * D.deltaB = 3) →
      ∃ j₁ j₂ : ℕ,
        j₁ ∈ Finset.Icc 1 43 ∧ j₂ ∈ Finset.Icc 1 43 ∧ j₁ ≠ j₂ ∧
        holes D.evenExponent 43 = {j₁, j₂} ∧
        (∑ j ∈ holes D.evenExponent 43, j) +
          (∑ h ∈ holes D.oddExponent 43, h) ≡ 8 [MOD 9]) := by
  dsimp
  let D := actualQ66System hL e hw hs
  let R := actualSevenHoleRows hL e hw hs
  have hsplit := actual_raw_hole_sum_split hL e hw hs
  have hmod := R.hole_sum_mod_nine
  have hraw :
      (∑ k ∈ holes D.evenExponent 43, 2 * k) +
        (∑ j ∈ holes D.oddExponent 43, (2 * j + 1)) ≡ 3 [MOD 9] := by
    rw [Nat.ModEq]
    rw [← hsplit]
    exact hmod
  constructor
  · intro hp
    obtain ⟨j, hj, hodd, hevenCard, _⟩ := D.negative_five_exact_holes hp
    refine ⟨j, hj, hodd, ?_⟩
    have hraw' := hraw
    rw [hodd] at hraw'
    simp at hraw'
    exact six_even_one_odd_congruence
      (holes D.evenExponent 43) j hevenCard hraw'
  · intro hp
    obtain ⟨j₁, j₂, hj₁, hj₂, hne, heven, hoddCard⟩ :=
      D.product_three_exact_holes hp
    refine ⟨j₁, j₂, hj₁, hj₂, hne, heven, ?_⟩
    have hevenCard : (holes D.evenExponent 43).card = 2 :=
      D.branch_hole_counts.2 hp |>.1
    exact two_even_five_odd_congruence
      (holes D.evenExponent 43) (holes D.oddExponent 43)
      hevenCard hoddCard hraw

/-- Final atom-H endpoint with no branch, norm-product, or parity-total
premise supplied by the caller. -/
theorem actual_q66_gaussian_prefilter
    (hL : IsLeech T) (e : T.Edge) (hw : T.weight e = 66)
    (hs : T.cutSize e = 9) :
    let D := actualQ66System hL e hw hs
    let R := actualSevenHoleRows hL e hw hs
    (D.deltaA * D.deltaB = -5 ∧
      (gaussianNorm (residueCount R.DA 4 0) (residueCount R.DA 4 1)
          (residueCount R.DA 4 2) (residueCount R.DA 4 3) = 1 ∨
       gaussianNorm (residueCount R.DB 4 0) (residueCount R.DB 4 1)
          (residueCount R.DB 4 2) (residueCount R.DB 4 3) = 1)) ∨
    (D.deltaA * D.deltaB = 3 ∧
      (gaussianNorm (residueCount R.DA 4 0) (residueCount R.DA 4 1)
          (residueCount R.DA 4 2) (residueCount R.DA 4 3) = 1 ∨
       gaussianNorm (residueCount R.DB 4 0) (residueCount R.DB 4 1)
          (residueCount R.DB 4 2) (residueCount R.DB 4 3) = 1 ∨
       (gaussianNorm (residueCount R.H 4 0) (residueCount R.H 4 1)
          (residueCount R.H 4 2) (residueCount R.H 4 3) = 25 ∧
        gaussianNorm (residueCount R.DA 4 0) (residueCount R.DA 4 1)
          (residueCount R.DA 4 2) (residueCount R.DA 4 3) = 5 ∧
        gaussianNorm (residueCount R.DB 4 0) (residueCount R.DB 4 1)
          (residueCount R.DB 4 2) (residueCount R.DB 4 3) = 5 ∧
        residueCount R.H 4 0 = 1 ∧ residueCount R.H 4 2 = 1 ∧
          ((residueCount R.H 4 1 = 5 ∧ residueCount R.H 4 3 = 0) ∨
           (residueCount R.H 4 1 = 0 ∧ residueCount R.H 4 3 = 5))))) := by
  dsimp
  let D := actualQ66System hL e hw hs
  let R := actualSevenHoleRows hL e hw hs
  rcases D.product_cases with hp | hp
  · left
    refine ⟨hp, ?_⟩
    have hpar := (actual_q66_hole_parity_totals hL e hw hs).1 hp
    exact R.negative_five_gaussian_prefilter hpar.1 hpar.2
  · right
    refine ⟨hp, ?_⟩
    have hpar := (actual_q66_hole_parity_totals hL e hw hs).2 hp
    exact R.product_three_gaussian_prefilter hpar.1 hpar.2

end LeechTrees.ParityTailConditional.Actual
