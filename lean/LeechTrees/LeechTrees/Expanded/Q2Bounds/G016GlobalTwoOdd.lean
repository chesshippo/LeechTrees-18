import LeechTrees.OddEdgesT12Adapter

/-!
# G016: global parity families and the common-middle-port obstruction

The arbitrary-port part of G016 is already a theorem about actual weighted
trees: `T12Adapter.t12_two_odd_physical_edges` says that an actual Leech tree
with exactly two odd physical edges has an even number of odd target ranks.
The first part of this file proves, by source-level arithmetic, that the odd
target count is odd in each of the two audited infinite families and exposes
the resulting graph endpoints.

The common-port proof has one graph adapter that is not present in the current
API.  The audited argument deletes the two odd edges, selects the middle even
component, identifies its two ports, factors the odd-rank polynomial at a
common port, and applies the initial-block/LCA analysis.  The structure
`CommonPortFactorConsequences` records the exact non-final consequences of
that analysis.  Its large-order inconsistency is proved below.  The missing
graph-to-factor extraction is named `CommonPortGraphBridge`; it does not
contain the desired nonexistence conclusion.

No computational search, solver certificate, or finite HOLD is used here.
-/

namespace LeechTrees.G016

open LeechTrees.Foundation
open LeechTrees.OddEdges.GraphAdapter
open LeechTrees.OddEdges.T12Adapter

variable {n : ℕ}

/-! ## The two arbitrary-port parity families -/

/-- In the square family `n = (4k+2)^2`, the odd target count is odd.
Writing `u=2k+1`, the proof identifies it with
`u^2 * (4*u^2-1)`, a product of two explicitly odd numbers. -/
theorem oddTargetCount_squareFamily_odd (k : ℕ) :
    Odd (oddTargetCount ((4 * k + 2) ^ 2)) := by
  let u := 2 * k + 1
  let M := u ^ 2 * (4 * u ^ 2 - 1)
  have hn : (4 * k + 2) ^ 2 = 4 * u ^ 2 := by
    dsimp [u]
    ring
  have htwice :
      2 * targetN ((4 * k + 2) ^ 2) = 4 * M := by
    calc
      2 * targetN ((4 * k + 2) ^ 2) =
          (4 * k + 2) ^ 2 * ((4 * k + 2) ^ 2 - 1) :=
        two_mul_targetN _
      _ = 4 * M := by
        rw [hn]
        dsimp [M]
        ac_rfl
  have htarget : targetN ((4 * k + 2) ^ 2) = 2 * M := by
    omega
  have hcount : oddTargetCount ((4 * k + 2) ^ 2) = M := by
    rw [oddTargetCount_eq, htarget]
    omega

  let a := 2 * k ^ 2 + 2 * k
  let b := 8 * k ^ 2 + 8 * k + 1
  have hu : u ^ 2 = 2 * a + 1 := by
    dsimp [u, a]
    ring
  have hv0 : 4 * u ^ 2 = 2 * b + 2 := by
    dsimp [u, b]
    ring
  have hv : 4 * u ^ 2 - 1 = 2 * b + 1 := by
    omega
  have hM : Odd M := by
    refine ⟨2 * a * b + a + b, ?_⟩
    dsimp [M]
    rw [hv, hu]
    ring
  rw [hcount]
  exact hM

/-- In the square-plus-two family `n = (4k)^2+2`, the target count is
`64*k^4+12*k^2+1`, hence odd. -/
theorem oddTargetCount_squarePlusTwoFamily_odd (k : ℕ) :
    Odd (oddTargetCount ((4 * k) ^ 2 + 2)) := by
  let R := 64 * k ^ 4 + 12 * k ^ 2
  have hn : (4 * k) ^ 2 + 2 = 16 * k ^ 2 + 2 := by ring
  have hpred : (4 * k) ^ 2 + 2 - 1 = 16 * k ^ 2 + 1 := by
    rw [hn]
    omega
  have htwice :
      2 * targetN ((4 * k) ^ 2 + 2) = 2 * (2 * R + 1) := by
    calc
      2 * targetN ((4 * k) ^ 2 + 2) =
          ((4 * k) ^ 2 + 2) * (((4 * k) ^ 2 + 2) - 1) :=
        two_mul_targetN _
      _ = 2 * (2 * R + 1) := by
        rw [hpred, hn]
        dsimp [R]
        ring
  have htarget : targetN ((4 * k) ^ 2 + 2) = 2 * R + 1 := by
    omega
  have hcount : oddTargetCount ((4 * k) ^ 2 + 2) = R + 1 := by
    rw [oddTargetCount_eq, htarget]
    omega
  rw [hcount]
  refine ⟨32 * k ^ 4 + 6 * k ^ 2, ?_⟩
  dsimp [R]
  ring

/-- Generic graph-facing use of T12: an odd target count rules out exactly
two actual odd physical edges, with no port assumption. -/
theorem no_exactlyTwo_of_oddTargetCount_odd
    (T : PosIntTree n) (hL : IsLeech T) (hn : 5 ≤ n)
    (hOdd : Odd (oddTargetCount n)) :
    ¬ ExactlyTwoOddPhysicalEdges T := by
  intro hTwo
  have hEven : Even (oddTargetCount n) :=
    t12_two_odd_physical_edges T hL hn hTwo
  exact (Nat.not_even_iff_odd.mpr hOdd) hEven

/-- Parameterized form of the audited square family
`n=s^2`, `s ≡ 2 (mod 4)`, `s≥6`. -/
theorem no_exactlyTwo_squareFamily
    (k : ℕ) (hk : 1 ≤ k)
    (T : PosIntTree ((4 * k + 2) ^ 2)) (hL : IsLeech T) :
    ¬ ExactlyTwoOddPhysicalEdges T := by
  have hs : 6 ≤ 4 * k + 2 := by omega
  have hsq : 6 * 6 ≤ (4 * k + 2) * (4 * k + 2) :=
    Nat.mul_le_mul hs hs
  have hn : 5 ≤ (4 * k + 2) ^ 2 := by
    rw [pow_two]
    omega
  exact no_exactlyTwo_of_oddTargetCount_odd T hL hn
    (oddTargetCount_squareFamily_odd k)

/-- Exact congruence-facing form of the audited square family. -/
theorem no_exactlyTwo_squareFamily_mod
    (s : ℕ) (hsmod : s % 4 = 2) (hs : 6 ≤ s)
    (T : PosIntTree (s ^ 2)) (hL : IsLeech T) :
    ¬ ExactlyTwoOddPhysicalEdges T := by
  have hdecomp : ∃ k : ℕ, s = 4 * k + 2 ∧ 1 ≤ k := by
    refine ⟨s / 4, ?_, ?_⟩
    · have hdiv := Nat.mod_add_div s 4
      omega
    · have hdiv := Nat.mod_add_div s 4
      omega
  obtain ⟨k, rfl, hk⟩ := hdecomp
  exact no_exactlyTwo_squareFamily k hk T hL

/-- Parameterized form of the audited square-plus-two family
`n=s^2+2`, `s ≡ 0 (mod 4)`, `s≥4`. -/
theorem no_exactlyTwo_squarePlusTwoFamily
    (k : ℕ) (hk : 1 ≤ k)
    (T : PosIntTree ((4 * k) ^ 2 + 2)) (hL : IsLeech T) :
    ¬ ExactlyTwoOddPhysicalEdges T := by
  have hs : 4 ≤ 4 * k := by omega
  have hsq : 4 * 4 ≤ (4 * k) * (4 * k) := Nat.mul_le_mul hs hs
  have hn : 5 ≤ (4 * k) ^ 2 + 2 := by
    rw [pow_two]
    omega
  exact no_exactlyTwo_of_oddTargetCount_odd T hL hn
    (oddTargetCount_squarePlusTwoFamily_odd k)

/-- Exact congruence-facing form of the audited square-plus-two family. -/
theorem no_exactlyTwo_squarePlusTwoFamily_mod
    (s : ℕ) (hsmod : s % 4 = 0) (hs : 4 ≤ s)
    (T : PosIntTree (s ^ 2 + 2)) (hL : IsLeech T) :
    ¬ ExactlyTwoOddPhysicalEdges T := by
  have hdecomp : ∃ k : ℕ, s = 4 * k ∧ 1 ≤ k := by
    refine ⟨s / 4, ?_, ?_⟩
    · have hdiv := Nat.mod_add_div s 4
      omega
    · have hdiv := Nat.mod_add_div s 4
      omega
  obtain ⟨k, rfl, hk⟩ := hdecomp
  exact no_exactlyTwo_squarePlusTwoFamily k hk T hL

/-- The order-18 instance is unconditional and makes no port assumption. -/
theorem no_exactlyTwo_order18
    (T : PosIntTree 18) (hL : IsLeech T) :
    ¬ ExactlyTwoOddPhysicalEdges T := by
  simpa using no_exactlyTwo_squarePlusTwoFamily 1 (by norm_num) T hL

/-- The order-36 instance is unconditional and makes no port assumption. -/
theorem no_exactlyTwo_order36
    (T : PosIntTree 36) (hL : IsLeech T) :
    ¬ ExactlyTwoOddPhysicalEdges T := by
  simpa using no_exactlyTwo_squareFamily 1 (by norm_num) T hL

/-! ## The audited common-port arithmetic after factor extraction -/

/-- Exact large-order numerical consequences of the common-port interval
factor and its initial-block/LCA analysis.

`m0` is the smaller Taylor parity-class size, so its doubled form is recorded
without natural-number division.  The three alternatives in `rankOne` are
the conclusions of the three audited branches:

* rank one in the middle factor forces `m≤4`;
* even first radix in the other factor forces `m≤s`;
* odd first radix gives the middle-distance capacity inequality.

No field states `False` or the desired graph nonexistence conclusion. -/
structure CommonPortFactorConsequences (n : ℕ) where
  s : ℕ
  m : ℕ
  m0 : ℕ
  E : ℕ
  orderLower :
    (n = s ^ 2 ∧ 2 * m0 = s * (s - 1)) ∨
    (n = s ^ 2 + 2 ∧ 2 * m0 = s * (s - 1) + 2)
  middleLower : m0 ≤ m
  evenCapacity : 4 * E ≤ n * (n - 1)
  rankOne :
    m ≤ 4 ∨ m ≤ s ∨ 3 * (m * (m - 1)) ≤ 2 * E

namespace CommonPortFactorConsequences

private theorem square_base_capacity_gap
    {s m0 : ℕ} (hs : 7 ≤ s) (hm0eq : 2 * m0 = s * (s - 1)) :
    s ^ 2 * (s ^ 2 - 1) < 6 * (m0 * (m0 - 1)) := by
  have h42 : 42 ≤ s * (s - 1) := by
    simpa using Nat.mul_le_mul hs (by omega : 6 ≤ s - 1)
  have hm0pos : 1 ≤ m0 := by omega
  have hspredZ : (((s - 1 : ℕ) : ℤ)) = (s : ℤ) - 1 := by
    have hsub := Nat.sub_add_cancel (by omega : 1 ≤ s)
    have hcast : ((s - 1 : ℕ) : ℤ) + 1 = (s : ℤ) := by
      exact_mod_cast hsub
    omega
  have hm0z0 : (2 : ℤ) * (m0 : ℤ) = (s : ℤ) * ((s - 1 : ℕ) : ℤ) := by
    exact_mod_cast hm0eq
  have hm0z : (2 : ℤ) * (m0 : ℤ) = (s : ℤ) * ((s : ℤ) - 1) := by
    rwa [hspredZ] at hm0z0
  have hm0zsq := congrArg (fun z : ℤ => z ^ 2) hm0z
  have hid :
      2 * (6 * ((m0 : ℤ) * ((m0 : ℤ) - 1)) -
          (s : ℤ) ^ 2 * ((s : ℤ) ^ 2 - 1)) =
        (s : ℤ) * ((s : ℤ) ^ 2 - 1) * ((s : ℤ) - 6) := by
    nlinarith [hm0zsq]
  have hsz : (7 : ℤ) ≤ (s : ℤ) := by exact_mod_cast hs
  have hrhs :
      0 < (s : ℤ) * ((s : ℤ) ^ 2 - 1) * ((s : ℤ) - 6) := by
    exact mul_pos (mul_pos (by omega) (by nlinarith)) (by omega)
  have hgapz :
      (s : ℤ) ^ 2 * ((s : ℤ) ^ 2 - 1) <
        6 * ((m0 : ℤ) * ((m0 : ℤ) - 1)) := by
    nlinarith

  have hm0subZ : (((m0 - 1 : ℕ) : ℤ)) = (m0 : ℤ) - 1 := by
    have hsub := Nat.sub_add_cancel hm0pos
    have hcast : ((m0 - 1 : ℕ) : ℤ) + 1 = (m0 : ℤ) := by
      exact_mod_cast hsub
    omega
  have hsquarepos : 1 ≤ s ^ 2 := by nlinarith
  have hsquaresubZ : (((s ^ 2 - 1 : ℕ) : ℤ)) = (s : ℤ) ^ 2 - 1 := by
    have hsub := Nat.sub_add_cancel hsquarepos
    have hcast : ((s ^ 2 - 1 : ℕ) : ℤ) + 1 = (s : ℤ) ^ 2 := by
      exact_mod_cast hsub
    omega
  have hgapz' :
      (s : ℤ) ^ 2 * ((s ^ 2 - 1 : ℕ) : ℤ) <
        6 * ((m0 : ℤ) * ((m0 - 1 : ℕ) : ℤ)) := by
    rw [hsquaresubZ, hm0subZ]
    exact hgapz
  exact_mod_cast hgapz'

private theorem squarePlusTwo_base_capacity_gap
    {s m0 : ℕ} (hs : 6 ≤ s)
    (hm0eq : 2 * m0 = s * (s - 1) + 2) :
    (s ^ 2 + 2) * (s ^ 2 + 2 - 1) < 6 * (m0 * (m0 - 1)) := by
  have h30 : 30 ≤ s * (s - 1) := by
    simpa using Nat.mul_le_mul hs (by omega : 5 ≤ s - 1)
  have hm0pos : 1 ≤ m0 := by omega
  have hspredZ : (((s - 1 : ℕ) : ℤ)) = (s : ℤ) - 1 := by
    have hsub := Nat.sub_add_cancel (by omega : 1 ≤ s)
    have hcast : ((s - 1 : ℕ) : ℤ) + 1 = (s : ℤ) := by
      exact_mod_cast hsub
    omega
  have hm0z0 :
      (2 : ℤ) * (m0 : ℤ) = (s : ℤ) * ((s - 1 : ℕ) : ℤ) + 2 := by
    exact_mod_cast hm0eq
  have hm0z :
      (2 : ℤ) * (m0 : ℤ) = (s : ℤ) * ((s : ℤ) - 1) + 2 := by
    rwa [hspredZ] at hm0z0
  have hm0zsq := congrArg (fun z : ℤ => z ^ 2) hm0z
  have hid :
      2 * (6 * ((m0 : ℤ) * ((m0 : ℤ) - 1)) -
          ((s : ℤ) ^ 2 + 2) * ((s : ℤ) ^ 2 + 1)) =
        (s : ℤ) ^ 3 * ((s : ℤ) - 6) +
          3 * (s : ℤ) * ((s : ℤ) - 2) - 4 := by
    nlinarith [hm0zsq]
  have hsz : (6 : ℤ) ≤ (s : ℤ) := by exact_mod_cast hs
  have hfirst : 0 ≤ (s : ℤ) ^ 3 * ((s : ℤ) - 6) :=
    mul_nonneg (by positivity) (by omega)
  have hprod24 : 24 ≤ (s : ℤ) * ((s : ℤ) - 2) := by
    have hp : 0 ≤ ((s : ℤ) - 6) * ((s : ℤ) + 4) :=
      mul_nonneg (by omega) (by omega)
    nlinarith
  have hrhs :
      0 < (s : ℤ) ^ 3 * ((s : ℤ) - 6) +
        3 * (s : ℤ) * ((s : ℤ) - 2) - 4 := by
    nlinarith
  have hgapz :
      ((s : ℤ) ^ 2 + 2) * ((s : ℤ) ^ 2 + 1) <
        6 * ((m0 : ℤ) * ((m0 : ℤ) - 1)) := by
    nlinarith

  have hm0subZ : (((m0 - 1 : ℕ) : ℤ)) = (m0 : ℤ) - 1 := by
    have hsub := Nat.sub_add_cancel hm0pos
    have hcast : ((m0 - 1 : ℕ) : ℤ) + 1 = (m0 : ℤ) := by
      exact_mod_cast hsub
    omega
  have hnZ : (((s ^ 2 + 2 : ℕ) : ℤ)) = (s : ℤ) ^ 2 + 2 := by
    norm_num
  have hnpos : 1 ≤ s ^ 2 + 2 := by omega
  have hnsubZ : (((s ^ 2 + 2 - 1 : ℕ) : ℤ)) = (s : ℤ) ^ 2 + 1 := by
    have hsub := Nat.sub_add_cancel hnpos
    have hcast :
        ((s ^ 2 + 2 - 1 : ℕ) : ℤ) + 1 = ((s ^ 2 + 2 : ℕ) : ℤ) := by
      exact_mod_cast hsub
    rw [hnZ] at hcast
    nlinarith
  have hgapz' :
      ((s ^ 2 + 2 : ℕ) : ℤ) * ((s ^ 2 + 2 - 1 : ℕ) : ℤ) <
        6 * ((m0 : ℤ) * ((m0 - 1 : ℕ) : ℤ)) := by
    rw [hnZ, hnsubZ, hm0subZ]
    exact hgapz
  exact_mod_cast hgapz'

/-- The elementary large-middle bounds used to contradict each rank-one
branch.  This is proved solely from Taylor's two order forms and `m0≤m`. -/
private theorem large_middle_bounds
    (D : CommonPortFactorConsequences n) (hn : 38 ≤ n) :
    4 < D.m ∧ D.s < D.m ∧
      n * (n - 1) < 6 * (D.m * (D.m - 1)) := by
  rcases D.orderLower with hsq | hsq2
  · have hs : 7 ≤ D.s := by
      by_contra h
      have hsle : D.s ≤ 6 := by omega
      have hsquare : D.s ^ 2 ≤ 6 ^ 2 := by
        simp only [pow_two]
        exact Nat.mul_le_mul hsle hsle
      omega
    have h42 : 42 ≤ D.s * (D.s - 1) := by
      simpa using Nat.mul_le_mul hs (by omega : 6 ≤ D.s - 1)
    have hm04 : 4 < D.m0 := by omega
    have h3s : 3 * D.s ≤ D.s * (D.s - 1) := by
      have h := Nat.mul_le_mul_left D.s (by omega : 3 ≤ D.s - 1)
      simpa [Nat.mul_comm] using h
    have hsm0 : D.s < D.m0 := by omega
    have hbase := square_base_capacity_gap hs hsq.2
    have hbase' :
        n * (n - 1) < 6 * (D.m0 * (D.m0 - 1)) := by
      exact lt_of_eq_of_lt
        (congrArg (fun t : ℕ => t * (t - 1)) hsq.1) hbase
    have hmono :
        D.m0 * (D.m0 - 1) ≤ D.m * (D.m - 1) :=
      Nat.mul_le_mul D.middleLower
        (Nat.sub_le_sub_right D.middleLower 1)
    have hm4 : 4 < D.m := lt_of_lt_of_le hm04 D.middleLower
    have hsm : D.s < D.m := lt_of_lt_of_le hsm0 D.middleLower
    exact ⟨hm4, hsm,
      lt_of_lt_of_le hbase' (Nat.mul_le_mul_left 6 hmono)⟩
  · have hs : 6 ≤ D.s := by
      by_contra h
      have hsle : D.s ≤ 5 := by omega
      have hsquare : D.s ^ 2 ≤ 5 ^ 2 := by
        simp only [pow_two]
        exact Nat.mul_le_mul hsle hsle
      omega
    have h30 : 30 ≤ D.s * (D.s - 1) := by
      simpa using Nat.mul_le_mul hs (by omega : 5 ≤ D.s - 1)
    have hm04 : 4 < D.m0 := by omega
    have h3s : 3 * D.s ≤ D.s * (D.s - 1) := by
      have h := Nat.mul_le_mul_left D.s (by omega : 3 ≤ D.s - 1)
      simpa [Nat.mul_comm] using h
    have hsm0 : D.s < D.m0 := by omega
    have hbase := squarePlusTwo_base_capacity_gap hs hsq2.2
    have hbase' :
        n * (n - 1) < 6 * (D.m0 * (D.m0 - 1)) := by
      exact lt_of_eq_of_lt
        (congrArg (fun t : ℕ => t * (t - 1)) hsq2.1) hbase
    have hmono :
        D.m0 * (D.m0 - 1) ≤ D.m * (D.m - 1) :=
      Nat.mul_le_mul D.middleLower
        (Nat.sub_le_sub_right D.middleLower 1)
    have hm4 : 4 < D.m := lt_of_lt_of_le hm04 D.middleLower
    have hsm : D.s < D.m := lt_of_lt_of_le hsm0 D.middleLower
    exact ⟨hm4, hsm,
      lt_of_lt_of_le hbase' (Nat.mul_le_mul_left 6 hmono)⟩

/-- The audited common-port factor consequences are inconsistent for every
parity-admissible order at least 38. -/
theorem large_order_impossible
    (D : CommonPortFactorConsequences n) (hn : 38 ≤ n) : False := by
  obtain ⟨hm4, hms, hgap⟩ := D.large_middle_bounds hn
  rcases D.rankOne with hm4' | hrest
  · omega
  · rcases hrest with hms' | hcap
    · omega
    · have hcap' : 6 * (D.m * (D.m - 1)) ≤ 4 * D.E := by
        omega
      have hE := D.evenCapacity
      omega

end CommonPortFactorConsequences

/-! ## Actual common port and the explicit missing graph bridge -/

/-- Two actual physical edges share a vertex. -/
def PhysicalEdgesSharePort (T : PosIntTree n) (e f : T.Edge) : Prop :=
  ∃ y : Fin n,
    (y = T.edgeLeft e ∨ y = T.edgeRight e) ∧
    (y = T.edgeLeft f ∨ y = T.edgeRight f)

/-- The two actual odd physical edges share their endpoint in the middle
even-edge component.  Since `twoOddEdges` names the complete two-element odd
edge set, this is the graph-level common-middle-port condition. -/
def CommonMiddlePort (T : PosIntTree n)
    (hTwo : ExactlyTwoOddPhysicalEdges T) : Prop :=
  let d := twoOddEdges T hTwo
  PhysicalEdgesSharePort T d.e d.f

/-- The missing G016 graph adapter.

T12 supplies the even-odd-target premise.  What is still required here is a
construction from the actual two-edge quotient and the shared actual port to
the common rooted interval factor, followed by the audited initial-block/LCA
case split.  The output is `CommonPortFactorConsequences`, not `False` and not
the desired graph theorem. -/
def CommonPortGraphBridge : Prop :=
  ∀ {n : ℕ} (T : PosIntTree n) (_hL : IsLeech T) (_hn : 38 ≤ n)
    (hTwo : ExactlyTwoOddPhysicalEdges T)
    (_hCommon : CommonMiddlePort T hTwo)
    (_hEven : Even (oddTargetCount n)),
    Nonempty (CommonPortFactorConsequences n)

/-- At order 37 there is no Leech tree at all: Taylor's graph-derived order
condition would make 37 a square or two more than a square. -/
theorem no_leech_order37 (T : PosIntTree 37) (hL : IsLeech T) : False := by
  let r : Fin 37 := ⟨0, by decide⟩
  obtain ⟨s, hs⟩ := t3_taylor_order_condition hL r
  have hsle : s ≤ 6 := by
    rcases hs with hs | hs <;> nlinarith
  interval_cases s <;> norm_num at hs

/-- Conditional only on the named common-port quotient/factor bridge: every
actual common-port, exactly-two-odd Leech tree of order at least 38 is
impossible. -/
theorem commonPort_impossible_ge38_of_bridge
    (bridge : CommonPortGraphBridge)
    (T : PosIntTree n) (hL : IsLeech T) (hn : 38 ≤ n)
    (hTwo : ExactlyTwoOddPhysicalEdges T)
    (hCommon : CommonMiddlePort T hTwo) : False := by
  have hEven : Even (oddTargetCount n) :=
    t12_two_odd_physical_edges T hL (by omega) hTwo
  let D := Classical.choice (bridge T hL hn hTwo hCommon hEven)
  exact D.large_order_impossible hn

/-- Audited combined threshold.  Order 36 is excluded unconditionally by the
arbitrary-port square family, order 37 by Taylor parity admissibility, and
orders at least 38 by the explicitly named common-port bridge. -/
theorem commonPort_impossible_ge36_of_bridge
    (bridge : CommonPortGraphBridge)
    (T : PosIntTree n) (hL : IsLeech T) (hn : 36 ≤ n)
    (hTwo : ExactlyTwoOddPhysicalEdges T)
    (hCommon : CommonMiddlePort T hTwo) : False := by
  by_cases h36 : n = 36
  · subst n
    exact (no_exactlyTwo_order36 T hL) hTwo
  by_cases h37 : n = 37
  · subst n
    exact no_leech_order37 T hL
  have hn38 : 38 ≤ n := by omega
  exact commonPort_impossible_ge38_of_bridge bridge T hL hn38 hTwo hCommon

/-- Public negated-existence form of the common-middle-port endpoint. -/
theorem no_commonPort_exactlyTwo_ge36_of_bridge
    (bridge : CommonPortGraphBridge)
    (T : PosIntTree n) (hL : IsLeech T) (hn : 36 ≤ n) :
    ¬ ∃ hTwo : ExactlyTwoOddPhysicalEdges T,
        CommonMiddlePort T hTwo := by
  rintro ⟨hTwo, hCommon⟩
  exact commonPort_impossible_ge36_of_bridge bridge T hL hn hTwo hCommon

end LeechTrees.G016
