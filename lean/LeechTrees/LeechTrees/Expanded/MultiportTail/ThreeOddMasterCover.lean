import Mathlib

/-!
# Exact finite index universe for the order-18 three-odd multiport cover

This file formalizes only the representation index set promoted by the
solve-free audits.  It does not encode or use a solver result.  In particular,
none of the ten master indices is asserted feasible or infeasible.

The old model index is a concrete promoted size row together with one of the
three possible locations of the unique unit odd bridge.  The size rows are
regenerated from the displayed finite equations rather than represented by an
uninterpreted `Fin 86`, `Fin 76`, or `Fin 39` label.
-/

namespace LeechTrees.OddQuotient.ThreeOddMasterCover

/-- The four open quotient/port patterns after the separately closed
common-port cases and the audited quotient symmetries. -/
inductive OpenPattern where
  | p4SD
  | p4DD
  | starEED
  | starDDD
  deriving DecidableEq, Repr, Fintype

/-- One ordered component-size row.  For a path these are `A,B,C,D`; for a
star they are `center,L0,L1,L2`. -/
structure SizeRow where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  deriving DecidableEq, Repr

/-- One signed P4 Gaussian signature. -/
structure P4Signature where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  deriving DecidableEq, Repr

private def signature (a b c d : ℤ) : P4Signature := ⟨a, b, c, d⟩

/-- The complete twenty-element solution set of
`(a-c)^2+(b-d)^2=18` and `ab+bc+cd-ad=1` used by the promoted P4 table. -/
def p4SignedSignatures : List P4Signature :=
  [ signature (-8) (-1) (-5) (-4),
    signature (-7) 1 (-4) 4,
    signature (-5) 2 (-2) 5,
    signature (-4) (-5) (-1) (-8),
    signature (-4) 4 (-1) 7,
    signature (-2) (-4) 1 (-1),
    signature (-2) (-1) (-5) 2,
    signature (-2) 5 1 2,
    signature (-1) (-2) 2 1,
    signature (-1) 1 (-4) (-2),
    signature 1 (-1) 4 2,
    signature 1 2 (-2) (-1),
    signature 2 (-5) (-1) (-2),
    signature 2 1 5 (-2),
    signature 2 4 (-1) 1,
    signature 4 (-4) 1 (-7),
    signature 4 5 1 8,
    signature 5 (-2) 2 (-5),
    signature 7 (-1) 4 (-4),
    signature 8 1 5 4 ]

/-- Kernel-checkable verification that the displayed signature list is exact
at the level of its two defining equations and contains no duplicate. -/
theorem p4SignedSignatures_nodup : p4SignedSignatures.Nodup := by decide

theorem p4SignedSignatures_length : p4SignedSignatures.length = 20 := by decide

theorem p4SignedSignatures_equations (x : P4Signature)
    (hx : x ∈ p4SignedSignatures) :
    (x.a - x.c) ^ 2 + (x.b - x.d) ^ 2 = 18 ∧
      x.a * x.b + x.b * x.c + x.c * x.d - x.a * x.d = 1 := by
  simp only [p4SignedSignatures, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [signature]

/-- Human completeness proof for the twenty signed P4 solutions.  It first
reduces to `u=a-c,v=b-d=±3`, then to the tiny factor equations
`bc=-4` or `bc=5`; it is not a model census. -/
theorem p4SignedSignatures_complete (x : P4Signature)
    (hreal : (x.a - x.c) ^ 2 + (x.b - x.d) ^ 2 = 18)
    (himag : x.a * x.b + x.b * x.c + x.c * x.d - x.a * x.d = 1) :
    x ∈ p4SignedSignatures := by
  rcases x with ⟨a, b, c, d⟩
  let u : ℤ := a - c
  let v : ℤ := b - d
  have huSq : u ^ 2 ≤ 18 := by
    dsimp [u, v] at *
    nlinarith [sq_nonneg (b - d)]
  have hvSq : v ^ 2 ≤ 18 := by
    dsimp [u, v] at *
    nlinarith [sq_nonneg (a - c)]
  have huLower : -4 ≤ u := by nlinarith
  have huUpper : u ≤ 4 := by nlinarith
  have hvLower : -4 ≤ v := by nlinarith
  have hvUpper : v ≤ 4 := by nlinarith
  have huvSq : u ^ 2 + v ^ 2 = 18 := by
    simpa [u, v] using hreal
  have huv :
      (u = -3 ∧ v = -3) ∨ (u = -3 ∧ v = 3) ∨
      (u = 3 ∧ v = -3) ∨ (u = 3 ∧ v = 3) := by
    interval_cases u <;> interval_cases v <;> norm_num at huvSq
    all_goals simp
  have hrewrite : 2 * b * c + u * v = 1 := by
    dsimp [u, v]
    nlinarith [himag]
  have hbc : b * c = -4 ∨ b * c = 5 := by
    rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩
    · left; rw [hu, hv] at hrewrite; nlinarith [hrewrite]
    · right; rw [hu, hv] at hrewrite; nlinarith [hrewrite]
    · right; rw [hu, hv] at hrewrite; nlinarith [hrewrite]
    · left; rw [hu, hv] at hrewrite; nlinarith [hrewrite]
  have hbne : b ≠ 0 := by
    intro hb
    rw [hb] at hbc
    norm_num at hbc
  have hcne : c ≠ 0 := by
    intro hc
    rw [hc] at hbc
    norm_num at hbc
  have hbSign : b ≤ -1 ∨ 1 ≤ b := by omega
  have hcSign : c ≤ -1 ∨ 1 ≤ c := by omega
  have hbLower : -5 ≤ b := by
    rcases hbc with hbc | hbc <;> rcases hcSign with hc | hc <;> nlinarith
  have hbUpper : b ≤ 5 := by
    rcases hbc with hbc | hbc <;> rcases hcSign with hc | hc <;> nlinarith
  have hcLower : -5 ≤ c := by
    rcases hbc with hbc | hbc <;> rcases hbSign with hb | hb <;> nlinarith
  have hcUpper : c ≤ 5 := by
    rcases hbc with hbc | hbc <;> rcases hbSign with hb | hb <;> nlinarith
  have hbcPairs :
      (b = -4 ∧ c = 1) ∨ (b = -2 ∧ c = 2) ∨
      (b = -1 ∧ c = 4) ∨ (b = 1 ∧ c = -4) ∨
      (b = 2 ∧ c = -2) ∨ (b = 4 ∧ c = -1) ∨
      (b = -5 ∧ c = -1) ∨ (b = -1 ∧ c = -5) ∨
      (b = 1 ∧ c = 5) ∨ (b = 5 ∧ c = 1) := by
    interval_cases b <;> interval_cases c
    all_goals norm_num at hbc
    all_goals simp
  rcases huv with huv | huv | huv | huv <;>
    rcases huv with ⟨hu, hv⟩ <;>
    rcases hbcPairs with hp | hp | hp | hp | hp | hp | hp | hp | hp | hp <;>
    rcases hp with ⟨rfl, rfl⟩
  all_goals rw [hu, hv] at hrewrite
  all_goals norm_num at hrewrite
  all_goals dsimp [u, v] at hu hv
  all_goals simp only [p4SignedSignatures, List.mem_cons, List.not_mem_nil,
    or_false, signature, P4Signature.mk.injEq]
  all_goals norm_num
  all_goals omega

def parityCompatible (m : ℕ) (x : ℤ) : Bool :=
  decide (|x| ≤ (m : ℤ) ∧ x % 2 = (m : ℤ) % 2)

def signatureCompatible (r : SizeRow) (x : P4Signature) : Bool :=
  parityCompatible r.a x.a && parityCompatible r.b x.b &&
    parityCompatible r.c x.c && parityCompatible r.d x.d

/-- The 120 oriented positive P4 rows before port and phase filtering.  This is
the literal `(A+C,B+D)=(7,11)` or `(11,7)` generation in the audited source. -/
def rawP4SizeRows : List SizeRow :=
  [(7, 11), (11, 7)].flatMap fun acbd =>
    (List.range (acbd.1 - 1)).flatMap fun ai =>
      (List.range (acbd.2 - 1)).map fun bi =>
        let a := ai + 1
        let b := bi + 1
        ⟨a, b, acbd.1 - a, acbd.2 - b⟩

def p4PortCondition (p : OpenPattern) (r : SizeRow) : Bool :=
  match p with
  | .p4SD => decide (2 ≤ r.c)
  | .p4DD => decide (2 ≤ r.b ∧ 2 ≤ r.c)
  | .starEED | .starDDD => false

def p4PhaseCompatible (r : SizeRow) : Bool :=
  p4SignedSignatures.any (signatureCompatible r)

/-- Exact promoted path size rows: port admissibility and existence of one of
the twenty signed Gaussian phase signatures are both imposed. -/
def p4SizeRows (p : OpenPattern) : List SizeRow :=
  rawP4SizeRows.filter fun r => p4PortCondition p r && p4PhaseCompatible r

theorem rawP4SizeRows_length : rawP4SizeRows.length = 120 := by decide

theorem mem_rawP4SizeRows_iff (r : SizeRow) :
    r ∈ rawP4SizeRows ↔
      0 < r.a ∧ 0 < r.b ∧ 0 < r.c ∧ 0 < r.d ∧
      ((r.a + r.c = 7 ∧ r.b + r.d = 11) ∨
        (r.a + r.c = 11 ∧ r.b + r.d = 7)) := by
  constructor
  · intro hr
    rw [rawP4SizeRows, List.mem_flatMap] at hr
    obtain ⟨acbd, hacbd, hr⟩ := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hacbd
    rcases hacbd with rfl | rfl
    · rw [List.mem_flatMap] at hr
      obtain ⟨ai, hai, hr⟩ := hr
      rw [List.mem_map] at hr
      obtain ⟨bi, hbi, rfl⟩ := hr
      simp only [List.mem_range] at hai hbi
      dsimp
      omega
    · rw [List.mem_flatMap] at hr
      obtain ⟨ai, hai, hr⟩ := hr
      rw [List.mem_map] at hr
      obtain ⟨bi, hbi, rfl⟩ := hr
      simp only [List.mem_range] at hai hbi
      dsimp
      omega
  · rintro ⟨ha, hb, hc, hd, hsum | hsum⟩
    · rw [rawP4SizeRows, List.mem_flatMap]
      refine ⟨(7, 11), by simp, ?_⟩
      rw [List.mem_flatMap]
      refine ⟨r.a - 1, by simp; omega, ?_⟩
      rw [List.mem_map]
      refine ⟨r.b - 1, by simp; omega, ?_⟩
      cases r
      simp only at ha hb hc hd hsum
      simp only [SizeRow.mk.injEq]
      omega
    · rw [rawP4SizeRows, List.mem_flatMap]
      refine ⟨(11, 7), by simp, ?_⟩
      rw [List.mem_flatMap]
      refine ⟨r.a - 1, by simp; omega, ?_⟩
      rw [List.mem_map]
      refine ⟨r.b - 1, by simp; omega, ?_⟩
      cases r
      simp only at ha hb hc hd hsum
      simp only [SizeRow.mk.injEq]
      omega

theorem mem_p4SizeRows_iff (p : OpenPattern) (r : SizeRow) :
    r ∈ p4SizeRows p ↔
      0 < r.a ∧ 0 < r.b ∧ 0 < r.c ∧ 0 < r.d ∧
      ((r.a + r.c = 7 ∧ r.b + r.d = 11) ∨
        (r.a + r.c = 11 ∧ r.b + r.d = 7)) ∧
      p4PortCondition p r = true ∧ p4PhaseCompatible r = true := by
  rw [p4SizeRows, List.mem_filter, mem_rawP4SizeRows_iff]
  simp only [Bool.and_eq_true, and_assoc]

theorem p4SD_sizeRow_count : (p4SizeRows .p4SD).length = 86 := by decide

theorem p4DD_sizeRow_count : (p4SizeRows .p4DD).length = 76 := by decide

def exactlyOneOdd (a b c : ℕ) : Bool :=
  decide (a % 2 + b % 2 + c % 2 = 1)

/-- Exact promoted star size rows.  The leaves are ordered, positive, sum to
the opposite colour-class order, and have parity multiset `(even,even,odd)`. -/
def starSizeRows : List SizeRow :=
  [(7, 11), (11, 7)].flatMap fun co =>
    (List.range (co.2 - 1)).flatMap fun li =>
      (List.range (co.2 - 1)).flatMap fun mi =>
        (List.range (co.2 - 1)).filterMap fun ni =>
          let l0 := li + 1
          let l1 := mi + 1
          let l2 := ni + 1
          if decide (l0 + l1 + l2 = co.2) && exactlyOneOdd l0 l1 l2 then
            some ⟨co.1, l0, l1, l2⟩
          else none

theorem mem_starSizeRows_iff (r : SizeRow) :
    r ∈ starSizeRows ↔
      0 < r.a ∧ 0 < r.b ∧ 0 < r.c ∧ 0 < r.d ∧
      ((r.a = 7 ∧ r.b + r.c + r.d = 11) ∨
        (r.a = 11 ∧ r.b + r.c + r.d = 7)) ∧
      exactlyOneOdd r.b r.c r.d = true := by
  constructor
  · intro hr
    rw [starSizeRows, List.mem_flatMap] at hr
    obtain ⟨co, hco, hr⟩ := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hco
    rcases hco with rfl | rfl
    · rw [List.mem_flatMap] at hr
      obtain ⟨li, hli, hr⟩ := hr
      rw [List.mem_flatMap] at hr
      obtain ⟨mi, hmi, hr⟩ := hr
      rw [List.mem_filterMap] at hr
      obtain ⟨ni, hni, hval⟩ := hr
      simp only [List.mem_range] at hli hmi hni
      dsimp at hval
      split at hval
      · rename_i hcond
        cases hval
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        rcases hcond with ⟨hsum, hodd⟩
        dsimp
        exact ⟨by omega, by omega, by omega, by omega,
          Or.inl ⟨rfl, hsum⟩, hodd⟩
      · simp at hval
    · rw [List.mem_flatMap] at hr
      obtain ⟨li, hli, hr⟩ := hr
      rw [List.mem_flatMap] at hr
      obtain ⟨mi, hmi, hr⟩ := hr
      rw [List.mem_filterMap] at hr
      obtain ⟨ni, hni, hval⟩ := hr
      simp only [List.mem_range] at hli hmi hni
      dsimp at hval
      split at hval
      · rename_i hcond
        cases hval
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        rcases hcond with ⟨hsum, hodd⟩
        dsimp
        exact ⟨by omega, by omega, by omega, by omega,
          Or.inr ⟨rfl, hsum⟩, hodd⟩
      · simp at hval
  · rintro ⟨ha, hb, hc, hd, hsum | hsum, hodd⟩
    · rw [starSizeRows, List.mem_flatMap]
      refine ⟨(7, 11), by simp, ?_⟩
      rw [List.mem_flatMap]
      refine ⟨r.b - 1, by simp; omega, ?_⟩
      rw [List.mem_flatMap]
      refine ⟨r.c - 1, by simp; omega, ?_⟩
      rw [List.mem_filterMap]
      refine ⟨r.d - 1, by simp; omega, ?_⟩
      cases r with
      | mk a b c d =>
          simp only at ha hb hc hd hsum hodd ⊢
          rcases hsum with ⟨rfl, hsum⟩
          have hbEq : b - 1 + 1 = b := Nat.sub_add_cancel (by omega)
          have hcEq : c - 1 + 1 = c := Nat.sub_add_cancel (by omega)
          have hdEq : d - 1 + 1 = d := Nat.sub_add_cancel (by omega)
          simp [hbEq, hcEq, hdEq, hsum, hodd]
    · rw [starSizeRows, List.mem_flatMap]
      refine ⟨(11, 7), by simp, ?_⟩
      rw [List.mem_flatMap]
      refine ⟨r.b - 1, by simp; omega, ?_⟩
      rw [List.mem_flatMap]
      refine ⟨r.c - 1, by simp; omega, ?_⟩
      rw [List.mem_filterMap]
      refine ⟨r.d - 1, by simp; omega, ?_⟩
      cases r with
      | mk a b c d =>
          simp only at ha hb hc hd hsum hodd ⊢
          rcases hsum with ⟨rfl, hsum⟩
          have hbEq : b - 1 + 1 = b := Nat.sub_add_cancel (by omega)
          have hcEq : c - 1 + 1 = c := Nat.sub_add_cancel (by omega)
          have hdEq : d - 1 + 1 = d := Nat.sub_add_cancel (by omega)
          simp [hbEq, hcEq, hdEq, hsum, hodd]

theorem starSizeRows_nodup : starSizeRows.Nodup := by decide

theorem star_sizeRow_count : starSizeRows.length = 39 := by decide

/-- The old promoted model universe.  Each summand retains a concrete row
index and one of the three unit-bridge positions. -/
abbrev LegacyModel :=
  (Fin (p4SizeRows .p4SD).length × Fin 3) ⊕
  ((Fin (p4SizeRows .p4DD).length × Fin 3) ⊕
  ((Fin starSizeRows.length × Fin 3) ⊕
   (Fin starSizeRows.length × Fin 3)))

def LegacyModel.pattern : LegacyModel → OpenPattern
  | .inl _ => .p4SD
  | .inr (.inl _) => .p4DD
  | .inr (.inr (.inl _)) => .starEED
  | .inr (.inr (.inr _)) => .starDDD

/-- Decode the actual promoted size row carried by an old model index. -/
def LegacyModel.sizeRow : LegacyModel → SizeRow
  | .inl (r, _) => (p4SizeRows .p4SD).get r
  | .inr (.inl (r, _)) => (p4SizeRows .p4DD).get r
  | .inr (.inr (.inl (r, _))) => starSizeRows.get r
  | .inr (.inr (.inr (r, _))) => starSizeRows.get r

def LegacyModel.unitBridge : LegacyModel → Fin 3
  | .inl (_, u) => u
  | .inr (.inl (_, u)) => u
  | .inr (.inr (.inl (_, u))) => u
  | .inr (.inr (.inr (_, u))) => u

/-- `258+228+117+117=720`, obtained from the exact regenerated row lists and
three unit-bridge positions, not from four opaque cardinality assumptions. -/
theorem legacyModel_card : Fintype.card LegacyModel = 720 := by
  simp only [LegacyModel, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, p4SD_sizeRow_count, p4DD_sizeRow_count,
    star_sizeRow_count]

/-- The three mutually exclusive low-distance cases used by the optional
parent masters. -/
inductive LowDistanceCase where
  | path3_edge4
  | edge3_nonadj_edge4
  | edge3_adj_path4
  deriving DecidableEq, Repr, Fintype

/-- Case 3 needs two odd bridges incident at one actual component port, hence
is available only in the two mixed port patterns. -/
def caseAdmissible : OpenPattern → LowDistanceCase → Bool
  | _, .path3_edge4 => true
  | _, .edge3_nonadj_edge4 => true
  | .p4SD, .edge3_adj_path4 => true
  | .starEED, .edge3_adj_path4 => true
  | .p4DD, .edge3_adj_path4 => false
  | .starDDD, .edge3_adj_path4 => false

/-- The exact ten optional-parent master indices. -/
def masterList : List (OpenPattern × LowDistanceCase) :=
  [ (.p4SD, .path3_edge4),
    (.p4DD, .path3_edge4),
    (.starEED, .path3_edge4),
    (.starDDD, .path3_edge4),
    (.p4SD, .edge3_nonadj_edge4),
    (.p4DD, .edge3_nonadj_edge4),
    (.starEED, .edge3_nonadj_edge4),
    (.starDDD, .edge3_nonadj_edge4),
    (.p4SD, .edge3_adj_path4),
    (.starEED, .edge3_adj_path4) ]

theorem masterList_nodup : masterList.Nodup := by decide

theorem masterList_length : masterList.length = 10 := by decide

theorem mem_masterList_iff (p : OpenPattern) (c : LowDistanceCase) :
    (p, c) ∈ masterList ↔ caseAdmissible p c := by
  cases p <;> cases c <;> decide

def masterFinset : Finset (OpenPattern × LowDistanceCase) :=
  masterList.toFinset

/-- A master is an element of the explicit ten-row master table. -/
abbrev Master := ↑masterFinset

theorem master_card : Fintype.card Master = 10 := by
  rw [Fintype.card_coe]
  simp [masterFinset, List.toFinset_card_of_nodup masterList_nodup,
    masterList_length]

/-- Every admissible `(pattern,low case)` has exactly one master-table row.
This is the formal union/partition statement at the representation-index
level; it says nothing about whether the corresponding assignment set is
empty. -/
theorem existsUnique_master (p : OpenPattern) (c : LowDistanceCase)
    (h : caseAdmissible p c) :
    ∃! m : Master, m.1 = (p, c) := by
  have hmem : (p, c) ∈ masterFinset := by
    simpa [masterFinset, mem_masterList_iff] using h
  refine ⟨⟨(p, c), hmem⟩, rfl, ?_⟩
  intro y hy
  exact Subtype.ext hy

/-- Each old model pattern is represented in both universal low cases; the
third case is present exactly for `P4-SD` and `star-EED`. -/
theorem legacy_pattern_master_cover (M : LegacyModel) :
    (∃! m : Master, m.1 = (M.pattern, .path3_edge4)) ∧
    (∃! m : Master, m.1 = (M.pattern, .edge3_nonadj_edge4)) ∧
    ((∃! m : Master, m.1 = (M.pattern, .edge3_adj_path4)) ↔
      M.pattern = .p4SD ∨ M.pattern = .starEED) := by
  constructor
  · exact existsUnique_master _ _ (by cases M.pattern <;> decide)
  constructor
  · exact existsUnique_master _ _ (by cases M.pattern <;> decide)
  · have hexact (p : OpenPattern) (c : LowDistanceCase) :
        (∃! m : Master, m.1 = (p, c)) ↔ caseAdmissible p c := by
      constructor
      · rintro ⟨m, hm, _⟩
        have hmemFin : (p, c) ∈ masterFinset := by
          rw [← hm]
          exact m.2
        have hmem : (p, c) ∈ masterList := by
          simpa [masterFinset] using hmemFin
        exact (mem_masterList_iff p c).1 hmem
      · exact existsUnique_master p c
    rw [hexact]
    cases hpat : M.pattern <;> simp [caseAdmissible]

/-- The advertised factor 72 is an index compression only. -/
theorem legacy_to_master_count_ratio : 720 = 72 * 10 := by norm_num

end LeechTrees.OddQuotient.ThreeOddMasterCover
