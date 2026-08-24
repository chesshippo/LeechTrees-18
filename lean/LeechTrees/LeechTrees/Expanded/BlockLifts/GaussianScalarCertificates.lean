import Mathlib

/-!
# Scalar Gaussian identities and exact high-component certificates

This module formalizes the human symbolic content of claims G019 and G022.
The certificates live only in the promoted scalar necessary-condition layer:
they are not weighted-tree, component-spectrum, port, or Leech-spectrum
realisations.  No computational census count occurs in a theorem.
-/

open scoped BigOperators

namespace LeechTrees.AdditionalBlockLifts

/-! ## Gaussian-pair arithmetic -/

/-- Real part of `i^d`. -/
def iPowReal (d : ℕ) : ℤ :=
  match d % 4 with
  | 0 => 1
  | 1 => 0
  | 2 => -1
  | _ => 0

/-- Imaginary part of `i^d`. -/
def iPowImag (d : ℕ) : ℤ :=
  match d % 4 with
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | _ => -1

@[simp] theorem iPowReal_zero : iPowReal 0 = 1 := by rfl
@[simp] theorem iPowImag_zero : iPowImag 0 = 0 := by rfl

/-- Scalar real part of `x^T K x`, where `K_uv=i^distance(u,v)`. -/
def gaussianReal {V : Type*} [Fintype V]
    (distance : V → V → ℕ) (x : V → ℤ) : ℤ :=
  ∑ u, ∑ v, x u * x v * iPowReal (distance u v)

/-- Scalar imaginary part of `x^T K x`. -/
def gaussianImag {V : Type*} [Fintype V]
    (distance : V → V → ℕ) (x : V → ℤ) : ℤ :=
  ∑ u, ∑ v, x u * x v * iPowImag (distance u v)

/-- The target alternating evaluations of distances `1,...,153`. -/
theorem order18_target_gaussian_evaluation :
    (18 + 2 * (∑ k ∈ Finset.Icc 1 76, (-1 : ℤ) ^ k),
      2 * (∑ k ∈ Finset.Icc 0 76, (-1 : ℤ) ^ k)) = (18, 2) := by
  norm_num [Finset.sum_Icc_succ_top]

/-! ## Exact component-signature domain -/

/-- One component's scalar order and gauged imbalance. -/
structure ScalarDatum where
  imbalance : ℤ
  order : ℕ
  deriving DecidableEq, Repr

/-- Exact arithmetic signature domain: positive order, magnitude bounded by
the order, and matching parity. -/
def ScalarDatum.Valid (d : ScalarDatum) : Prop :=
  0 < d.order ∧ |d.imbalance| ≤ (d.order : ℤ) ∧
    d.imbalance % 2 = (d.order : ℤ) % 2

/-- Any two parity-class sizes give an admissible component signature. -/
theorem scalarDatum_valid_of_class_sizes (plus minus : ℕ)
    (hne : 0 < plus + minus) :
    ScalarDatum.Valid
      { imbalance := (plus : ℤ) - minus, order := plus + minus } := by
  constructor
  · exact hne
  constructor
  · rw [abs_le]
    constructor <;> push_cast <;> omega
  · push_cast
    omega

/-- Conversely, parity and magnitude expose integral nonnegative class sizes.
This is the exactness of the signature domain at the scalar layer. -/
theorem scalarDatum_class_sizes_of_valid
    (d : ScalarDatum) (hd : d.Valid) :
    ∃ plus minus : ℤ,
      0 ≤ plus ∧ 0 ≤ minus ∧
      plus + minus = d.order ∧
      plus - minus = d.imbalance := by
  have heven : Even ((d.order : ℤ) - d.imbalance) := by
    rw [Int.even_iff]
    have hp := hd.2.2
    omega
  obtain ⟨minus, hminus⟩ := heven
  refine ⟨(d.order : ℤ) - minus, minus, ?_, ?_, ?_, ?_⟩
  · have habs := (abs_le.mp hd.2.1).1
    omega
  · have habs := (abs_le.mp hd.2.1).2
    omega
  · omega
  · omega

/-! ## Depth-two scalar formula and explicit witnesses -/

structure ScalarBranch where
  child : ScalarDatum
  grandchildren : List ScalarDatum
  deriving DecidableEq, Repr

structure HighScalarCertificate where
  root : ScalarDatum
  branches : List ScalarBranch
  deriving DecidableEq, Repr

def ScalarBranch.grandImbalanceSum (b : ScalarBranch) : ℤ :=
  (b.grandchildren.map ScalarDatum.imbalance).sum

def HighScalarCertificate.componentCount (w : HighScalarCertificate) : ℕ :=
  1 + w.branches.length +
    (w.branches.map fun b => b.grandchildren.length).sum

def HighScalarCertificate.childImbalanceSum
    (w : HighScalarCertificate) : ℤ :=
  (w.branches.map fun b => b.child.imbalance).sum

def HighScalarCertificate.childSquareSum
    (w : HighScalarCertificate) : ℤ :=
  (w.branches.map fun b => b.child.imbalance ^ 2).sum

def HighScalarCertificate.grandImbalanceSum
    (w : HighScalarCertificate) : ℤ :=
  (w.branches.map ScalarBranch.grandImbalanceSum).sum

def HighScalarCertificate.grandSquareSum
    (w : HighScalarCertificate) : ℤ :=
  (w.branches.map fun b =>
    (b.grandchildren.map fun d => d.imbalance ^ 2).sum).sum

def HighScalarCertificate.branchGrandSquareSum
    (w : HighScalarCertificate) : ℤ :=
  (w.branches.map fun b => b.grandImbalanceSum ^ 2).sum

def HighScalarCertificate.childGrandProductSum
    (w : HighScalarCertificate) : ℤ :=
  (w.branches.map fun b =>
    b.child.imbalance * b.grandImbalanceSum).sum

/-- Closed real part of the depth-two rooted recurrence. -/
def HighScalarCertificate.realPart (w : HighScalarCertificate) : ℤ :=
  let a := w.root.imbalance
  let Y := w.childImbalanceSum
  let V := w.childSquareSum
  let S := w.grandImbalanceSum
  let U := w.grandSquareSum
  let SS := w.branchGrandSquareSum
  (a - S) ^ 2 - Y ^ 2 + 2 * (V - SS) + 2 * U

/-- Closed imaginary part of the depth-two rooted recurrence. -/
def HighScalarCertificate.imagPart (w : HighScalarCertificate) : ℤ :=
  let a := w.root.imbalance
  let Y := w.childImbalanceSum
  let S := w.grandImbalanceSum
  let YS := w.childGrandProductSum
  2 * ((a - S) * Y + 2 * YS)

/-- The aggregate formula follows by expanding
`Z_root=(a-S)+iY`, `Z_child=y+iS_j`, and
`F=Z_root^2+2*sum_(v != root) Z_v^2`. -/
theorem depthTwo_scalar_gaussian_expansion
    (a Y V S U SS YS : ℤ) :
    let rootReal := a - S
    let rootImag := Y
    let childRealSquares := V
    let childImagSquares := SS
    let grandRealSquares := U
    ((rootReal ^ 2 - rootImag ^ 2) +
        2 * (childRealSquares - childImagSquares) +
        2 * grandRealSquares,
      2 * rootReal * rootImag + 4 * YS) =
    ((a - S) ^ 2 - Y ^ 2 + 2 * (V - SS) + 2 * U,
      2 * ((a - S) * Y + 2 * YS)) := by
  dsimp
  apply Prod.ext
  · ring
  · ring

/-- Gaussian integer represented by its real and imaginary coordinates. -/
structure GaussianPair where
  re : ℤ
  im : ℤ
  deriving DecidableEq, Repr

def GaussianPair.square (z : GaussianPair) : GaussianPair :=
  ⟨z.re ^ 2 - z.im ^ 2, 2 * z.re * z.im⟩

def GaussianPair.add (z w : GaussianPair) : GaussianPair :=
  ⟨z.re + w.re, z.im + w.im⟩

def GaussianPair.smul (k : ℤ) (z : GaussianPair) : GaussianPair :=
  ⟨k * z.re, k * z.im⟩

def GaussianPair.listSum (zs : List GaussianPair) : GaussianPair :=
  ⟨(zs.map GaussianPair.re).sum, (zs.map GaussianPair.im).sum⟩

private theorem list_sum_flatMap {α : Type*}
    (f : α → List ℤ) (xs : List α) :
    (xs.flatMap f).sum = (xs.map fun x => (f x).sum).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.sum_append, List.map_cons,
        List.sum_cons, ih]

private theorem list_sum_map_sub {α : Type*}
    (f g : α → ℤ) (xs : List α) :
    (xs.map fun x => f x - g x).sum =
      (xs.map f).sum - (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring

/-- Actual rooted Gaussian subtotal of one child branch,
`Z_j=y_j+i*S_j`. -/
def ScalarBranch.rootedZ (b : ScalarBranch) : GaussianPair :=
  ⟨b.child.imbalance, b.grandImbalanceSum⟩

private theorem branch_square_real_sum (bs : List ScalarBranch) :
    (bs.map (GaussianPair.re ∘ fun b => b.rootedZ.square)).sum =
      (bs.map fun b => b.child.imbalance ^ 2).sum -
        (bs.map fun b => b.grandImbalanceSum ^ 2).sum := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
      change b.child.imbalance ^ 2 - b.grandImbalanceSum ^ 2 +
          (bs.map (GaussianPair.re ∘ fun b => b.rootedZ.square)).sum =
        b.child.imbalance ^ 2 + (bs.map fun b => b.child.imbalance ^ 2).sum -
          (b.grandImbalanceSum ^ 2 +
            (bs.map fun b => b.grandImbalanceSum ^ 2).sum)
      rw [ih]
      ring

private theorem branch_square_imag_sum (bs : List ScalarBranch) :
    (bs.map (GaussianPair.im ∘ fun b => b.rootedZ.square)).sum =
      2 * (bs.map fun b => b.child.imbalance * b.grandImbalanceSum).sum := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
      change 2 * b.child.imbalance * b.grandImbalanceSum +
          (bs.map (GaussianPair.im ∘ fun b => b.rootedZ.square)).sum =
        2 * (b.child.imbalance * b.grandImbalanceSum +
          (bs.map fun b => b.child.imbalance * b.grandImbalanceSum).sum)
      rw [ih]
      ring

private theorem grand_square_real_sum (bs : List ScalarBranch) :
    ((bs.flatMap fun b =>
      b.grandchildren.map fun d => (GaussianPair.mk d.imbalance 0).square).map
        GaussianPair.re).sum =
      (bs.map fun b =>
        (b.grandchildren.map fun d => d.imbalance ^ 2).sum).sum := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons, ih]
      congr 1
      induction b.grandchildren with
      | nil => rfl
      | cons d ds ih' =>
          simpa [GaussianPair.square] using ih'

private theorem grand_square_imag_sum (bs : List ScalarBranch) :
    ((bs.flatMap fun b =>
      b.grandchildren.map fun d => (GaussianPair.mk d.imbalance 0).square).map
        GaussianPair.im).sum = 0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        ih]
      suffices h :
          ((b.grandchildren.map fun d =>
            (GaussianPair.mk d.imbalance 0).square).map
              GaussianPair.im).sum = 0 by
        rw [h, zero_add]
      induction b.grandchildren with
      | nil => rfl
      | cons d ds ih' =>
          simpa [GaussianPair.square] using ih'

/-- Actual rooted subtotal at the depth-two quotient root,
`Z_0=(a-S)+iY`. -/
def HighScalarCertificate.rootedZ (w : HighScalarCertificate) : GaussianPair :=
  ⟨w.root.imbalance - w.grandImbalanceSum, w.childImbalanceSum⟩

/-- Rooted-recurrence evaluation
`Z_root^2 + 2*sum_child Z_child^2 + 2*sum_grand z^2` of the
actual depth-two quotient encoded by the certificate. -/
def HighScalarCertificate.rootedGaussianForm
    (w : HighScalarCertificate) : GaussianPair :=
  let childSquares :=
    GaussianPair.listSum (w.branches.map fun b => b.rootedZ.square)
  let grandSquares := GaussianPair.listSum
    (w.branches.flatMap fun b =>
      b.grandchildren.map fun d => (GaussianPair.mk d.imbalance 0).square)
  w.rootedZ.square |>.add (GaussianPair.smul 2 childSquares) |>.add
    (GaussianPair.smul 2 grandSquares)

/-- Exact correspondence between the rooted quotient recurrence and the
closed scalar formula.  This is the G019 adapter from each explicit quotient
certificate to `x^T K_Q x`; it does not assume the target value. -/
theorem rootedGaussianForm_eq_scalar_formula
    (w : HighScalarCertificate) :
    w.rootedGaussianForm = ⟨w.realPart, w.imagPart⟩ := by
  unfold HighScalarCertificate.rootedGaussianForm
  dsimp only [GaussianPair.add, GaussianPair.smul, GaussianPair.listSum,
    HighScalarCertificate.rootedZ]
  simp only [List.map_map]
  apply congrArg₂ GaussianPair.mk
  · unfold HighScalarCertificate.realPart
      HighScalarCertificate.childImbalanceSum
      HighScalarCertificate.childSquareSum
      HighScalarCertificate.grandImbalanceSum
      HighScalarCertificate.grandSquareSum
      HighScalarCertificate.branchGrandSquareSum
      ScalarBranch.grandImbalanceSum
    rw [branch_square_real_sum, grand_square_real_sum]
    simp only [ScalarBranch.grandImbalanceSum]
    simp only [GaussianPair.square]
  · unfold HighScalarCertificate.imagPart
      HighScalarCertificate.childImbalanceSum
      HighScalarCertificate.grandImbalanceSum
      HighScalarCertificate.childGrandProductSum
      ScalarBranch.grandImbalanceSum
    rw [branch_square_imag_sum, grand_square_imag_sum]
    simp only [ScalarBranch.grandImbalanceSum]
    simp only [GaussianPair.square]
    ring

def HighScalarCertificate.colorSevenOrder
    (w : HighScalarCertificate) : ℕ :=
  w.root.order +
    (w.branches.map fun b =>
      (b.grandchildren.map ScalarDatum.order).sum).sum

def HighScalarCertificate.colorElevenOrder
    (w : HighScalarCertificate) : ℕ :=
  (w.branches.map fun b => b.child.order).sum

def HighScalarCertificate.Valid
    (c : ℕ) (w : HighScalarCertificate) : Prop :=
  w.componentCount = c ∧
  w.root.Valid ∧
  (∀ b ∈ w.branches,
    b.child.Valid ∧ ∀ d ∈ b.grandchildren, d.Valid) ∧
  w.colorSevenOrder = 7 ∧
  w.colorElevenOrder = 11 ∧
  w.realPart = 18 ∧ w.imagPart = 2

private def d (x : ℤ) (m : ℕ) : ScalarDatum := ⟨x, m⟩
private def br (x : ℤ) (m : ℕ)
    (g : List ScalarDatum := []) : ScalarBranch := ⟨d x m, g⟩

/-- Fifteen explicit certificate rows.  Grandchildren are stored in their
actual parent branch, so `sum S_j^2` and `sum y_j*S_j` are checked rather than
inferred from marginal lists. -/
def highScalarCertificate : ℕ → HighScalarCertificate
  | 4 => ⟨d 1 7, [br 2 8, br (-2) 2, br 1 1]⟩
  | 5 => ⟨d 1 7, [br 2 6, br (-2) 2, br 1 1, br 0 2]⟩
  | 6 => ⟨d 1 7, [br 2 4, br (-2) 2, br 1 1, br 0 2, br 0 2]⟩
  | 7 => ⟨d 1 7,
      [br 2 2, br (-2) 2, br 1 1, br 0 2, br 0 2, br 0 2]⟩
  | 8 => ⟨d 1 7,
      [br 1 3, br 1 1, br 1 1, br (-1) 1, br (-2) 2, br 1 1,
        br 0 2]⟩
  | 9 => ⟨d 1 7,
      [br 1 1, br 1 1, br 1 1, br (-1) 1, br (-2) 2, br 1 1,
        br 0 2, br 0 2]⟩
  | 10 => ⟨d 1 7,
      [br 1 3, br 1 1, br 1 1, br (-1) 1,
        br (-1) 1, br (-1) 1, br (-1) 1, br 1 1, br 1 1]⟩
  | 11 => ⟨d 1 7,
      [br 1 1, br 1 1, br 1 1, br (-1) 1,
        br (-1) 1, br (-1) 1, br (-1) 1, br 1 1, br 1 1, br 0 2]⟩
  | 12 => ⟨d 0 6,
      [br 0 2 [d 1 1],
        br 1 1, br 1 1, br 1 1, br 1 1,
        br (-1) 1, br (-1) 1, br (-1) 1, br (-1) 1, br (-1) 1]⟩
  | 13 => ⟨d 0 4,
      [br 0 2 [d 1 1, d 0 2],
        br 1 1, br 1 1, br 1 1, br 1 1,
        br (-1) 1, br (-1) 1, br (-1) 1, br (-1) 1, br (-1) 1]⟩
  | 14 => ⟨d 0 2,
      [br 0 2 [d 1 1, d 0 2, d 0 2],
        br 1 1, br 1 1, br 1 1, br 1 1,
        br (-1) 1, br (-1) 1, br (-1) 1, br (-1) 1, br (-1) 1]⟩
  | 15 => ⟨d 0 4,
      [br (-1) 1 [d 1 1, d 1 1, d (-1) 1],
        br 1 1, br 1 1, br 1 1, br 1 1,
        br (-1) 1, br (-1) 1, br (-1) 1,
        br (-1) 1, br (-1) 1, br (-1) 1]⟩
  | 16 => ⟨d 0 2,
      [br (-1) 1 [d 1 1, d 1 1, d (-1) 1, d 0 2],
        br 1 1, br 1 1, br 1 1, br 1 1,
        br (-1) 1, br (-1) 1, br (-1) 1,
        br (-1) 1, br (-1) 1, br (-1) 1]⟩
  | 17 => ⟨d (-2) 2,
      [br (-1) 1 [d (-1) 1, d (-1) 1],
        br (-1) 1 [d (-1) 1], br (-1) 1 [d (-1) 1],
        br (-1) 1 [d (-1) 1],
        br 1 1, br 1 1, br 1 1, br 1 1,
        br (-1) 1, br (-1) 1, br (-1) 1]⟩
  | 18 => ⟨d 1 1,
      [br 1 1 [d 1 1, d 1 1, d 1 1, d 1 1, d (-1) 1, d (-1) 1],
        br 1 1, br 1 1, br 1 1, br 1 1, br 1 1, br 1 1,
        br (-1) 1, br (-1) 1, br (-1) 1, br (-1) 1]⟩
  | _ => ⟨d 0 0, []⟩

/-- Exact certificate theorem for every surviving component count. -/
theorem high_component_scalar_flexibility
    (c : ℕ) (hcLower : 4 ≤ c) (hcUpper : c ≤ 18) :
    (highScalarCertificate c).Valid c := by
  interval_cases c <;>
    norm_num [HighScalarCertificate.Valid, highScalarCertificate,
      HighScalarCertificate.componentCount, ScalarDatum.Valid,
      HighScalarCertificate.colorSevenOrder,
      HighScalarCertificate.colorElevenOrder,
      HighScalarCertificate.realPart, HighScalarCertificate.imagPart,
      HighScalarCertificate.childImbalanceSum,
      HighScalarCertificate.childSquareSum,
      HighScalarCertificate.grandImbalanceSum,
      HighScalarCertificate.grandSquareSum,
      HighScalarCertificate.branchGrandSquareSum,
      HighScalarCertificate.childGrandProductSum,
      ScalarBranch.grandImbalanceSum, d, br] at hcLower hcUpper ⊢

/-- Every explicit row evaluates to the promoted Gaussian target through the
rooted quotient recurrence itself. -/
theorem high_component_rooted_gaussian_certificates
    (c : ℕ) (hcLower : 4 ≤ c) (hcUpper : c ≤ 18) :
    (highScalarCertificate c).rootedGaussianForm = ⟨18, 2⟩ := by
  rw [rootedGaussianForm_eq_scalar_formula]
  have h := high_component_scalar_flexibility c hcLower hcUpper
  exact congrArg₂ GaussianPair.mk h.2.2.2.2.2.1 h.2.2.2.2.2.2

/-! ## Literal depth-two quotient carried by every certificate -/

def HighScalarCertificate.branchAt (w : HighScalarCertificate)
    (b : Fin w.branches.length) : ScalarBranch :=
  w.branches.get b

def HighScalarCertificate.grandAt (w : HighScalarCertificate)
    (b : Fin w.branches.length)
    (g : Fin (w.branchAt b).grandchildren.length) : ScalarDatum :=
  (w.branchAt b).grandchildren.get g

private theorem sum_fin_get_eq_map_sum {α M : Type*}
    [AddCommMonoid M] (xs : List α) (f : α → M) :
    (∑ i : Fin xs.length, f (xs.get i)) = (xs.map f).sum := by
  simpa only [List.get_eq_getElem] using
    (Fin.sum_univ_fun_getElem xs f)

/-- Vertices of the literal rooted depth-two quotient: the root, one child
per branch, and the grandchildren retained under their actual parent. -/
abbrev HighScalarCertificate.QuotientVertex (w : HighScalarCertificate) :=
  Unit ⊕ (Σ b : Fin w.branches.length,
    Unit ⊕ Fin (w.branchAt b).grandchildren.length)

def HighScalarCertificate.quotientImbalance (w : HighScalarCertificate) :
    w.QuotientVertex → ℤ
  | .inl _ => w.root.imbalance
  | .inr ⟨b, .inl _⟩ => (w.branchAt b).child.imbalance
  | .inr ⟨b, .inr g⟩ => (w.grandAt b g).imbalance

/-- Literal graph distance in the depth-two rooted tree encoded by `w`. -/
def HighScalarCertificate.quotientDistance (w : HighScalarCertificate) :
    w.QuotientVertex → w.QuotientVertex → ℕ
  | .inl _, .inl _ => 0
  | .inl _, .inr ⟨_, .inl _⟩ => 1
  | .inr ⟨_, .inl _⟩, .inl _ => 1
  | .inl _, .inr ⟨_, .inr _⟩ => 2
  | .inr ⟨_, .inr _⟩, .inl _ => 2
  | .inr ⟨b, .inl _⟩, .inr ⟨c, .inl _⟩ => if b = c then 0 else 2
  | .inr ⟨b, .inl _⟩, .inr ⟨c, .inr _⟩ => if b = c then 1 else 3
  | .inr ⟨b, .inr _⟩, .inr ⟨c, .inl _⟩ => if b = c then 1 else 3
  | .inr ⟨b, .inr g⟩, .inr ⟨c, .inr h⟩ =>
      if (⟨b, g⟩ : Σ b : Fin w.branches.length,
          Fin (w.branchAt b).grandchildren.length) = ⟨c, h⟩ then 0
      else if b = c then 2 else 4

theorem HighScalarCertificate.quotientVertex_card
    (w : HighScalarCertificate) :
    Fintype.card w.QuotientVertex = w.componentCount := by
  unfold HighScalarCertificate.QuotientVertex
    HighScalarCertificate.componentCount
  simp only [Fintype.card_sum, Fintype.card_unique, Fintype.card_sigma,
    Fintype.card_fin, HighScalarCertificate.branchAt]
  rw [Finset.sum_add_distrib]
  rw [sum_fin_get_eq_map_sum w.branches
    (fun b => b.grandchildren.length)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  simp [Nat.add_assoc]

private theorem sum_mul_sum_eq_double_sum
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → ℤ) (g : κ → ℤ) :
    (∑ i, f i) * (∑ j, g j) = ∑ i, ∑ j, f i * g j :=
  Fintype.sum_mul_sum f g

private theorem sigma_sum_ite_fst_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (i : ι) (f : (Σ b, κ b) → ℤ) :
    (∑ u, if i = u.1 then f u else 0) = ∑ j, f ⟨i, j⟩ := by
  rw [Fintype.sum_sigma]
  change (∑ b : ι, ∑ j : κ b,
    if i = b then f ⟨b, j⟩ else 0) = ∑ j, f ⟨i, j⟩
  rw [Fintype.sum_eq_single i]
  · simp
  · intro b hb
    simp [Ne.symm hb]

private theorem signed_double_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : ι → ℤ) :
    (∑ i, ∑ j, f i * g j * (if i = j then 1 else -1)) =
      2 * (∑ i, f i * g i) - (∑ i, f i) * (∑ j, g j) := by
  calc
    _ = ∑ i, ∑ j,
        (2 * (if i = j then f i * g j else 0) - f i * g j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : i = j
      · subst j
        simp only [if_true]
        ring
      · simp [h]
    _ = _ := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← Finset.sum_mul, Fintype.sum_ite_eq]

private theorem sigma_sameFiber_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (f : (Σ i, κ i) → ℤ) :
    (∑ u, ∑ v, if u.1 = v.1 then f u * f v else 0) =
      ∑ i, (∑ j, f ⟨i, j⟩) ^ 2 := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_two, sum_mul_sum_eq_double_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact sigma_sum_ite_fst_eq i
    (fun v => f ⟨i, j⟩ * f v)

private theorem sigma_diagonal_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℤ) :
    (∑ u, ∑ v, if u = v then f u * f v else 0) =
      ∑ u, f u ^ 2 := by
  simp [pow_two]

private theorem sigma_block_real_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    [∀ i, DecidableEq (κ i)]
    (f : (Σ i, κ i) → ℤ) :
    (∑ u, ∑ v, f u * f v *
      (if u = v then 1 else if u.1 = v.1 then -1 else 1)) =
      (∑ u, f u) ^ 2 -
        2 * (∑ i, (∑ j, f ⟨i, j⟩) ^ 2) +
        2 * (∑ u, f u ^ 2) := by
  classical
  calc
    _ = ∑ u, ∑ v,
        (f u * f v -
          2 * (if u.1 = v.1 then f u * f v else 0) +
          2 * (if u = v then f u * f v else 0)) := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      by_cases huv : u = v
      · subst v
        simp
      · by_cases hb : u.1 = v.1
        · simp [huv, hb]
          ring
        · simp [huv, hb]
    _ = (∑ u, ∑ v, f u * f v) -
          2 * (∑ u, ∑ v,
            if u.1 = v.1 then f u * f v else 0) +
          2 * (∑ u, ∑ v, if u = v then f u * f v else 0) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul]
    _ = _ := by
      rw [← sum_mul_sum_eq_double_sum f f,
        sigma_sameFiber_sum f, sigma_diagonal_sum f]
      simp only [pow_two]

private theorem sigma_signed_cross_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (f : ι → ℤ) (g : (Σ i, κ i) → ℤ) :
    (∑ i, ∑ u, f i * g u * (if i = u.1 then 1 else -1)) =
      2 * (∑ i, f i * (∑ j, g ⟨i, j⟩)) -
    (∑ i, f i) * (∑ u, g u) := by
  classical
  have hsame (i : ι) :
      (∑ u : Σ b, κ b, if i = u.1 then f i * g u else 0) =
        f i * (∑ j, g ⟨i, j⟩) := by
    rw [sigma_sum_ite_fst_eq]
    rw [Finset.mul_sum]
  calc
    _ = ∑ i, ∑ u,
        (2 * (if i = u.1 then f i * g u else 0) - f i * g u) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro u hu
      by_cases h : i = u.1
      · simp [h]
        ring
      · simp [h]
    _ = ∑ i,
        (2 * (f i * (∑ j, g ⟨i, j⟩)) - f i * (∑ u, g u)) := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hsame]
    _ = _ := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← Finset.sum_mul]

private theorem sigma_signed_cross_sum_rev
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (f : ι → ℤ) (g : (Σ i, κ i) → ℤ) :
    (∑ u, ∑ i, g u * f i * (if u.1 = i then 1 else -1)) =
      2 * (∑ i, f i * (∑ j, g ⟨i, j⟩)) -
        (∑ i, f i) * (∑ u, g u) := by
  calc
    _ = ∑ i, ∑ u, f i * g u * (if i = u.1 then 1 else -1) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro u hu
      by_cases h : i = u.1
      · subst i
        simp [mul_comm]
      · have hrev : u.1 ≠ i := by
          intro h'
          exact h h'.symm
        simp [h, hrev, mul_comm]
    _ = _ := sigma_signed_cross_sum f g

private abbrev DepthTwoVertex {ι : Type*} (κ : ι → Type*) :=
  Unit ⊕ (Σ i, Unit ⊕ κ i)

private def depthTwoCoordinate {ι : Type*} {κ : ι → Type*}
    (a : ℤ) (y : ι → ℤ) (z : ∀ i, κ i → ℤ) :
    DepthTwoVertex κ → ℤ
  | .inl _ => a
  | .inr ⟨i, .inl _⟩ => y i
  | .inr ⟨i, .inr j⟩ => z i j

private def depthTwoDistance {ι : Type*} [DecidableEq ι]
    {κ : ι → Type*} [∀ i, DecidableEq (κ i)] :
    DepthTwoVertex κ → DepthTwoVertex κ → ℕ
  | .inl _, .inl _ => 0
  | .inl _, .inr ⟨_, .inl _⟩ => 1
  | .inr ⟨_, .inl _⟩, .inl _ => 1
  | .inl _, .inr ⟨_, .inr _⟩ => 2
  | .inr ⟨_, .inr _⟩, .inl _ => 2
  | .inr ⟨i, .inl _⟩, .inr ⟨j, .inl _⟩ => if i = j then 0 else 2
  | .inr ⟨i, .inl _⟩, .inr ⟨j, .inr _⟩ => if i = j then 1 else 3
  | .inr ⟨i, .inr _⟩, .inr ⟨j, .inl _⟩ => if i = j then 1 else 3
  | .inr ⟨i, .inr g⟩, .inr ⟨j, .inr h⟩ =>
      if (⟨i, g⟩ : Σ i, κ i) = ⟨j, h⟩ then 0
      else if i = j then 2 else 4

private theorem iPowReal_one : iPowReal 1 = 0 := by rfl
private theorem iPowReal_two : iPowReal 2 = -1 := by rfl
private theorem iPowImag_one : iPowImag 1 = 1 := by rfl
private theorem iPowImag_two : iPowImag 2 = 0 := by rfl

private theorem iPowReal_zero_two (p : Prop) [Decidable p] :
    iPowReal (if p then 0 else 2) = if p then 1 else -1 := by
  by_cases hp : p <;> simp [hp, iPowReal]

private theorem iPowImag_zero_two (p : Prop) [Decidable p] :
    iPowImag (if p then 0 else 2) = 0 := by
  by_cases hp : p <;> simp [hp, iPowImag]

private theorem iPowReal_one_three (p : Prop) [Decidable p] :
    iPowReal (if p then 1 else 3) = 0 := by
  by_cases hp : p <;> simp [hp, iPowReal]

private theorem iPowImag_one_three (p : Prop) [Decidable p] :
    iPowImag (if p then 1 else 3) = if p then 1 else -1 := by
  by_cases hp : p <;> simp [hp, iPowImag]

private theorem iPowReal_grand (p q : Prop) [Decidable p] [Decidable q] :
    iPowReal (if p then 0 else if q then 2 else 4) =
      if p then 1 else if q then -1 else 1 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq, iPowReal]

private theorem iPowImag_grand (p q : Prop) [Decidable p] [Decidable q] :
    iPowImag (if p then 0 else if q then 2 else 4) = 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq, iPowImag]

private theorem depthTwo_real_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (a : ℤ) (y : ι → ℤ) (z : ∀ i, κ i → ℤ) :
    gaussianReal (depthTwoDistance (κ := κ)) (depthTwoCoordinate a y z) =
      (a - ∑ i, ∑ j, z i j) ^ 2 - (∑ i, y i) ^ 2 +
        2 * ((∑ i, y i ^ 2) - (∑ i, (∑ j, z i j) ^ 2)) +
        2 * (∑ i, ∑ j, z i j ^ 2) := by
  classical
  have hchild := signed_double_sum y y
  have hgrand := sigma_block_real_sum
    (fun u : Σ i, κ i => z u.1 u.2)
  simp only [Fintype.sum_sigma] at hgrand
  have hrootLeft :
      (∑ i, ∑ j, a * z i j * (-1)) =
        -a * (∑ i, ∑ j, z i j) := by
    simp only [mul_neg, mul_one, Finset.sum_neg_distrib,
      ← Finset.mul_sum]
    ring
  have hrootRight :
      (∑ i, ∑ j, z i j * a * (-1)) =
        -a * (∑ i, ∑ j, z i j) := by
    simp only [mul_neg, mul_one, Finset.sum_neg_distrib,
      ← Finset.sum_mul]
    ring
  unfold gaussianReal
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_unique,
    depthTwoDistance, depthTwoCoordinate, iPowReal_zero, iPowReal_one,
    iPowReal_two, iPowReal_zero_two, iPowReal_one_three, iPowReal_grand,
    mul_zero, mul_one, zero_add, add_zero,
    Finset.sum_const_zero, Finset.sum_add_distrib]
  rw [hchild, hgrand, hrootLeft, hrootRight]
  simp only [pow_two]
  ring

private theorem depthTwo_imag_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (a : ℤ) (y : ι → ℤ) (z : ∀ i, κ i → ℤ) :
    gaussianImag (depthTwoDistance (κ := κ)) (depthTwoCoordinate a y z) =
      2 * ((a - ∑ i, ∑ j, z i j) * (∑ i, y i) +
        2 * (∑ i, y i * (∑ j, z i j))) := by
  classical
  have hforward := sigma_signed_cross_sum y
    (fun u : Σ i, κ i => z u.1 u.2)
  have hreverse := sigma_signed_cross_sum_rev y
    (fun u : Σ i, κ i => z u.1 u.2)
  simp only [Fintype.sum_sigma] at hforward hreverse
  unfold gaussianImag
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_unique,
    depthTwoDistance, depthTwoCoordinate, iPowImag_zero, iPowImag_one,
    iPowImag_two, iPowImag_zero_two, iPowImag_one_three, iPowImag_grand,
    mul_zero, mul_one, zero_add, add_zero,
    Finset.sum_const_zero, Finset.sum_add_distrib]
  rw [hforward, hreverse]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

private theorem quotient_gaussianReal_eq_realPart
    (w : HighScalarCertificate) :
    gaussianReal w.quotientDistance w.quotientImbalance = w.realPart := by
  have h := depthTwo_real_sum
    (κ := fun b : Fin w.branches.length =>
      Fin (w.branchAt b).grandchildren.length)
    w.root.imbalance
    (fun b => (w.branchAt b).child.imbalance)
    (fun b g => (w.grandAt b g).imbalance)
  have hdist : w.quotientDistance = depthTwoDistance
      (κ := fun b : Fin w.branches.length =>
        Fin (w.branchAt b).grandchildren.length) := by
    funext u v
    rcases u with u | ⟨b, u⟩
    · rcases v with v | ⟨c, v⟩
      · rfl
      · rcases v with v | g <;> rfl
    · rcases u with u | g
      · rcases v with v | ⟨c, v⟩
        · rfl
        · rcases v with v | h <;> rfl
      · rcases v with v | ⟨c, v⟩
        · rfl
        · rcases v with v | h <;> rfl
  have hcoord : w.quotientImbalance = depthTwoCoordinate w.root.imbalance
      (fun b => (w.branchAt b).child.imbalance)
      (fun b g => (w.grandAt b g).imbalance) := by
    funext u
    rcases u with u | ⟨b, u⟩
    · rfl
    · rcases u with u | g <;> rfl
  have hGrand (b : Fin w.branches.length) :
      (∑ g, (w.grandAt b g).imbalance) =
        (w.branchAt b).grandImbalanceSum := by
    unfold HighScalarCertificate.grandAt ScalarBranch.grandImbalanceSum
    exact sum_fin_get_eq_map_sum (M := ℤ) _ _
  have hGrandSq (b : Fin w.branches.length) :
      (∑ g, (w.grandAt b g).imbalance ^ 2) =
        ((w.branchAt b).grandchildren.map fun d => d.imbalance ^ 2).sum := by
    unfold HighScalarCertificate.grandAt
    exact sum_fin_get_eq_map_sum (M := ℤ)
      (w.branchAt b).grandchildren
      (fun d : ScalarDatum => d.imbalance ^ 2)
  have hY : (∑ b, (w.branchAt b).child.imbalance) =
      w.childImbalanceSum := by
    unfold HighScalarCertificate.branchAt
      HighScalarCertificate.childImbalanceSum
    exact sum_fin_get_eq_map_sum (M := ℤ) w.branches
      (fun b : ScalarBranch => b.child.imbalance)
  have hV : (∑ b, (w.branchAt b).child.imbalance ^ 2) =
      w.childSquareSum := by
    unfold HighScalarCertificate.branchAt
      HighScalarCertificate.childSquareSum
    exact sum_fin_get_eq_map_sum (M := ℤ) w.branches
      (fun b : ScalarBranch => b.child.imbalance ^ 2)
  have hS : (∑ b, (w.branchAt b).grandImbalanceSum) =
      w.grandImbalanceSum := by
    unfold HighScalarCertificate.branchAt
      HighScalarCertificate.grandImbalanceSum
    exact sum_fin_get_eq_map_sum (M := ℤ) w.branches
      ScalarBranch.grandImbalanceSum
  have hSS : (∑ b, (w.branchAt b).grandImbalanceSum ^ 2) =
      w.branchGrandSquareSum := by
    unfold HighScalarCertificate.branchAt
      HighScalarCertificate.branchGrandSquareSum
    exact sum_fin_get_eq_map_sum (M := ℤ) w.branches
      (fun b : ScalarBranch => b.grandImbalanceSum ^ 2)
  have hU : (∑ b, ∑ g, (w.grandAt b g).imbalance ^ 2) =
      w.grandSquareSum := by
    simp_rw [hGrandSq]
    unfold HighScalarCertificate.branchAt
      HighScalarCertificate.grandSquareSum
    simpa only [] using sum_fin_get_eq_map_sum (M := ℤ) w.branches
      (fun b => (b.grandchildren.map fun d => d.imbalance ^ 2).sum)
  rw [hdist, hcoord, h]
  simp_rw [hGrand]
  rw [hS, hY, hV, hSS, hU]
  rfl

private theorem quotient_gaussianImag_eq_imagPart
    (w : HighScalarCertificate) :
    gaussianImag w.quotientDistance w.quotientImbalance = w.imagPart := by
  have h := depthTwo_imag_sum
    (κ := fun b : Fin w.branches.length =>
      Fin (w.branchAt b).grandchildren.length)
    w.root.imbalance
    (fun b => (w.branchAt b).child.imbalance)
    (fun b g => (w.grandAt b g).imbalance)
  have hdist : w.quotientDistance = depthTwoDistance
      (κ := fun b : Fin w.branches.length =>
        Fin (w.branchAt b).grandchildren.length) := by
    funext u v
    rcases u with u | ⟨b, u⟩
    · rcases v with v | ⟨c, v⟩
      · rfl
      · rcases v with v | g <;> rfl
    · rcases u with u | g
      · rcases v with v | ⟨c, v⟩
        · rfl
        · rcases v with v | h <;> rfl
      · rcases v with v | ⟨c, v⟩
        · rfl
        · rcases v with v | h <;> rfl
  have hcoord : w.quotientImbalance = depthTwoCoordinate w.root.imbalance
      (fun b => (w.branchAt b).child.imbalance)
      (fun b g => (w.grandAt b g).imbalance) := by
    funext u
    rcases u with u | ⟨b, u⟩
    · rfl
    · rcases u with u | g <;> rfl
  have hGrand (b : Fin w.branches.length) :
      (∑ g, (w.grandAt b g).imbalance) =
        (w.branchAt b).grandImbalanceSum := by
    unfold HighScalarCertificate.grandAt ScalarBranch.grandImbalanceSum
    exact sum_fin_get_eq_map_sum (M := ℤ) _ _
  have hY : (∑ b, (w.branchAt b).child.imbalance) =
      w.childImbalanceSum := by
    unfold HighScalarCertificate.branchAt
      HighScalarCertificate.childImbalanceSum
    simpa only [] using sum_fin_get_eq_map_sum (M := ℤ) w.branches
      (fun b => b.child.imbalance)
  have hS : (∑ b, (w.branchAt b).grandImbalanceSum) =
      w.grandImbalanceSum := by
    unfold HighScalarCertificate.branchAt
      HighScalarCertificate.grandImbalanceSum
    simpa only [] using sum_fin_get_eq_map_sum (M := ℤ) w.branches
      ScalarBranch.grandImbalanceSum
  have hYS :
      (∑ b, (w.branchAt b).child.imbalance *
        (w.branchAt b).grandImbalanceSum) =
        w.childGrandProductSum := by
    unfold HighScalarCertificate.branchAt
      HighScalarCertificate.childGrandProductSum
    simpa only [] using sum_fin_get_eq_map_sum (M := ℤ) w.branches
      (fun b => b.child.imbalance * b.grandImbalanceSum)
  rw [hdist, hcoord, h]
  simp_rw [hGrand]
  rw [hS, hY, hYS]
  rfl

/-- Exact G019 correspondence: the rooted recurrence is the real/imaginary
pair of the literal matrix `K_uv=i^distance(u,v)` on the encoded quotient.
This theorem does not use certificate validity or the target value. -/
theorem depthTwo_quotient_KForm_eq_rootedGaussianForm
    (w : HighScalarCertificate) :
    (gaussianReal w.quotientDistance w.quotientImbalance,
      gaussianImag w.quotientDistance w.quotientImbalance) =
        (w.rootedGaussianForm.re, w.rootedGaussianForm.im) := by
  rw [rootedGaussianForm_eq_scalar_formula]
  exact congrArg₂ Prod.mk
    (quotient_gaussianReal_eq_realPart w)
    (quotient_gaussianImag_eq_imagPart w)

/-- Each of the fifteen explicit rows is now a certificate for an actual
depth-two quotient `xᵀK_Qx=(18,2)`, not merely for a closed scalar formula. -/
theorem high_component_actual_quotient_K_certificates
    (c : ℕ) (hcLower : 4 ≤ c) (hcUpper : c ≤ 18) :
    let w := highScalarCertificate c
    Fintype.card w.QuotientVertex = c ∧
      gaussianReal w.quotientDistance w.quotientImbalance = 18 ∧
      gaussianImag w.quotientDistance w.quotientImbalance = 2 := by
  dsimp only
  have hvalid := high_component_scalar_flexibility c hcLower hcUpper
  have hK := depthTwo_quotient_KForm_eq_rootedGaussianForm
    (highScalarCertificate c)
  have hroot := high_component_rooted_gaussian_certificates c hcLower hcUpper
  refine ⟨?_, ?_, ?_⟩
  · rw [HighScalarCertificate.quotientVertex_card]
    exact hvalid.1
  · have hre := congrArg Prod.fst hK
    rw [hroot] at hre
    exact hre
  · have him := congrArg Prod.snd hK
    rw [hroot] at him
    exact him

/-- At the stated scalar layer, every possible positive component count left
after the analytic `c=1,2,3` exclusions has an explicit passing row. -/
theorem scalar_gaussian_layer_cannot_exclude_any_count_four_to_eighteen :
    ∀ c ∈ Finset.Icc 4 18,
      ∃ w : HighScalarCertificate, w.Valid c := by
  intro c hc
  refine ⟨highScalarCertificate c, ?_⟩
  exact high_component_scalar_flexibility c
    (Finset.mem_Icc.mp hc).1 (Finset.mem_Icc.mp hc).2

/-! ## Four-odd quotient shape equations -/

def p5Real (x : Fin 5 → ℤ) : ℤ :=
  (∑ j, x j ^ 2) -
    2 * (x 0 * x 2 + x 1 * x 3 + x 2 * x 4) +
    2 * x 0 * x 4

def p5ImagHalf (x : Fin 5 → ℤ) : ℤ :=
  x 0 * x 1 + x 1 * x 2 + x 2 * x 3 + x 3 * x 4 -
    x 0 * x 3 - x 1 * x 4

def forkReal (x : Fin 5 → ℤ) : ℤ :=
  (∑ j, x j ^ 2) -
    2 * (x 1 * x 2 + x 1 * x 3 + x 2 * x 3 + x 0 * x 4)

def forkImagHalf (x : Fin 5 → ℤ) : ℤ :=
  x 0 * (x 1 + x 2 + x 3) + x 3 * x 4 - x 4 * (x 1 + x 2)

def starReal (a : ℤ) (y : Fin 4 → ℤ) : ℤ :=
  a ^ 2 + 2 * (∑ j, y j ^ 2) - (∑ j, y j) ^ 2

def starImagHalf (a : ℤ) (y : Fin 4 → ℤ) : ℤ :=
  a * ∑ j, y j

/-- Five-vertex path distance matrix. -/
def p5Distance (u v : Fin 5) : ℕ := Nat.dist u.1 v.1

/-- Fork distance matrix for edges `01,02,03,34`. -/
def forkDistance : Fin 5 → Fin 5 → ℕ :=
  ![![0, 1, 1, 1, 2],
    ![1, 0, 2, 2, 3],
    ![1, 2, 0, 2, 3],
    ![1, 2, 2, 0, 1],
    ![2, 3, 3, 1, 0]]

/-- Star distance matrix, with center zero. -/
def starDistance : Fin 5 → Fin 5 → ℕ :=
  ![![0, 1, 1, 1, 1],
    ![1, 0, 2, 2, 2],
    ![1, 2, 0, 2, 2],
    ![1, 2, 2, 0, 2],
    ![1, 2, 2, 2, 0]]

/-- Direct expansion of the actual `P5` matrix `K_uv=i^distance(u,v)`. -/
theorem p5_KForm_expansion (x : Fin 5 → ℤ) :
    gaussianReal p5Distance x = p5Real x ∧
      gaussianImag p5Distance x = 2 * p5ImagHalf x := by
  constructor <;>
    simp [gaussianReal, gaussianImag, p5Distance, p5Real, p5ImagHalf,
      iPowReal, iPowImag, Nat.dist, Fin.sum_univ_succ] <;> ring

/-- Direct expansion of the actual fork matrix. -/
theorem fork_KForm_expansion (x : Fin 5 → ℤ) :
    gaussianReal forkDistance x = forkReal x ∧
      gaussianImag forkDistance x = 2 * forkImagHalf x := by
  constructor <;>
    simp [gaussianReal, gaussianImag, forkDistance, forkReal, forkImagHalf,
      iPowReal, iPowImag, Fin.sum_univ_succ] <;> ring

/-- Direct expansion of the actual star matrix. -/
theorem star_KForm_expansion (a : ℤ) (y : Fin 4 → ℤ) :
    let x : Fin 5 → ℤ := ![a, y 0, y 1, y 2, y 3]
    gaussianReal starDistance x = starReal a y ∧
      gaussianImag starDistance x = 2 * starImagHalf a y := by
  dsimp only
  constructor <;>
    simp [gaussianReal, gaussianImag, starDistance, starReal, starImagHalf,
      iPowReal, iPowImag, Fin.sum_univ_succ] <;> ring

/-- Actual quotient-variable endpoint.  The two expansion hypotheses are the
path-derived identification of the quotient quadratic form with the exact
target alternating even/odd sums; the conclusion evaluates those sums and
does not assume `18+2i`. -/
theorem fourOdd_gaussian_identity_from_exact_quotient_expansion
    (distance : Fin 5 → Fin 5 → ℕ) (x : Fin 5 → ℤ)
    (realExpansion : gaussianReal distance x =
      18 + 2 * (∑ k ∈ Finset.Icc 1 76, (-1 : ℤ) ^ k))
    (imagExpansion : gaussianImag distance x =
      2 * (∑ k ∈ Finset.Icc 0 76, (-1 : ℤ) ^ k)) :
    gaussianReal distance x = 18 ∧ gaussianImag distance x = 2 := by
  have htarget := order18_target_gaussian_evaluation
  constructor
  · rw [realExpansion]
    exact congrArg Prod.fst htarget
  · rw [imagExpansion]
    exact congrArg Prod.snd htarget

/-- The pair equation `18+2i` is exactly the two displayed P5 equations. -/
theorem p5_gaussian_target_iff (x : Fin 5 → ℤ) :
    (p5Real x, 2 * p5ImagHalf x) = (18, 2) ↔
      p5Real x = 18 ∧ p5ImagHalf x = 1 := by
  constructor <;> intro h
  · constructor
    · exact congrArg Prod.fst h
    · have := congrArg Prod.snd h
      dsimp at this
      omega
  · rcases h with ⟨hr, hi⟩
    simp [hr, hi]

/-- The pair equation `18+2i` is exactly the two displayed fork equations. -/
theorem fork_gaussian_target_iff (x : Fin 5 → ℤ) :
    (forkReal x, 2 * forkImagHalf x) = (18, 2) ↔
      forkReal x = 18 ∧ forkImagHalf x = 1 := by
  constructor <;> intro h
  · constructor
    · exact congrArg Prod.fst h
    · have := congrArg Prod.snd h
      dsimp at this
      omega
  · rcases h with ⟨hr, hi⟩
    simp [hr, hi]

/-- The pair equation `18+2i` is exactly the two displayed star equations. -/
theorem star_gaussian_target_iff (a : ℤ) (y : Fin 4 → ℤ) :
    (starReal a y, 2 * starImagHalf a y) = (18, 2) ↔
      starReal a y = 18 ∧ starImagHalf a y = 1 := by
  constructor <;> intro h
  · constructor
    · exact congrArg Prod.fst h
    · have := congrArg Prod.snd h
      dsimp at this
      omega
  · rcases h with ⟨hr, hi⟩
    simp [hr, hi]

/-- Human star-shape normalization: after the permitted global sign, the
center coordinate and leaf sum are both one, and the leaf square sum is nine. -/
theorem star_gaussian_normalization
    (a Y sumSquares : ℤ)
    (hImag : a * Y = 1)
    (hReal : a ^ 2 + 2 * sumSquares - Y ^ 2 = 18) :
    (a = 1 ∧ Y = 1 ∧ sumSquares = 9) ∨
      (a = -1 ∧ Y = -1 ∧ sumSquares = 9) := by
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hImag with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    norm_num at hReal ⊢
    omega
  · right
    norm_num at hReal ⊢
    omega

/-- Explicit disjunction saying that four ordered entries form the multiset
`{2,-2,1,0}`. -/
def IsStarLeafPattern (a b c d : ℤ) : Prop :=
  [a, b, c, d].Perm [2, -2, 1, 0]

/-- The human, non-census classification of the four star leaf coordinates. -/
theorem star_leaf_pattern
    (a b c d : ℤ)
    (hsum : a + b + c + d = 1)
    (hsq : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 9) :
    IsStarLeafPattern a b c d := by
  have haLower : -3 ≤ a := by nlinarith [sq_nonneg (a + 3)]
  have haUpper : a ≤ 3 := by nlinarith [sq_nonneg (a - 3)]
  have hbLower : -3 ≤ b := by nlinarith [sq_nonneg (b + 3)]
  have hbUpper : b ≤ 3 := by nlinarith [sq_nonneg (b - 3)]
  have hcLower : -3 ≤ c := by nlinarith [sq_nonneg (c + 3)]
  have hcUpper : c ≤ 3 := by nlinarith [sq_nonneg (c - 3)]
  have hd : d = 1 - a - b - c := by omega
  subst d
  interval_cases a
  all_goals interval_cases b
  all_goals interval_cases c
  all_goals norm_num [IsStarLeafPattern] at hsq
  all_goals norm_num [IsStarLeafPattern]
  all_goals rw [List.perm_iff_count]
  all_goals
    intro x
    simp only [List.count_cons, List.count_nil]
    ac_rfl

/-- Compact statement of the audited four-odd scalar domain: five positive
component orders with color budgets 7 and 11 and independently admissible
gauged imbalances.  It deliberately contains no census cardinality. -/
structure FourOddGaussianDomain where
  order : Fin 5 → ℕ
  imbalance : Fin 5 → ℤ
  color : Fin 5 → Bool
  eachValid : ∀ j, ScalarDatum.Valid ⟨imbalance j, order j⟩
  colorSeven : (∑ j, if color j then order j else 0) = 7
  colorEleven : (∑ j, if color j then 0 else order j) = 11

theorem fourOdd_domain_total_order (D : FourOddGaussianDomain) :
    ∑ j, D.order j = 18 := by
  have hsplit : (∑ j, D.order j) =
      (∑ j, if D.color j then D.order j else 0) +
      (∑ j, if D.color j then 0 else D.order j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    cases D.color j <;> simp
  rw [hsplit, D.colorSeven, D.colorEleven]

end LeechTrees.AdditionalBlockLifts
