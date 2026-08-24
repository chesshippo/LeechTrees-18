import LeechTrees.OddEdgesT12Adapter
import LeechTrees.OddEdgesT11Adapter
import LeechTrees.Expanded.Q2Bounds.Q2Bounds

/-!
# G015: the low support-factor obstruction for two odd edges

This file separates two logically different layers of the audited G015
argument and then joins them by an actual unit-bridge adapter.

* `PrefixFactorData` is the exact low-rank algebra used in the proof.  Its
  factors have rooted tree metrics, their Cartesian sum is coefficient-one,
  every rank below `q` occurs, rank `q` is absent, and all internal distances
  in the two factors are globally collision-free.
* `GraphTwoOddWeights` is constructed below from an actual `IsLeech` tree
  with exactly two odd physical edges.  It identifies the physical weights
  as `1` and `2*q+1`, with `q > 0`.
* `prefixFactorDataOfGraph` uses the actual two components incident with the
  unit edge.  `Q2Bounds.lowOddUnitRectanglePoint` supplies every rank below
  `q`; the second physical edge excludes rank `q`.
* The distinct-port section constructs both actual bridge orientations,
  specializes actual target pairs through half-rank 14, and excludes
  `q=8,9,10` by actual internal or odd-pair collisions.  Together with the
  any-order bounds, this gives the graph-level `q ≤ 6` endpoint.

No solver or finite-search result is imported as an axiom.
-/

namespace LeechTrees.G015

open LeechTrees.Foundation
open LeechTrees.OddEdges.GraphAdapter
open LeechTrees.OddEdges.T12Adapter
open LeechTrees.OddQuotient
open LeechTrees.OddQuotient.Q2Bounds

variable {n : ℕ}

/-! ## The audited rooted-support algebra -/

/-- A rooted support with the elementary identities of an integral weighted
tree metric.  Support elements are rooted half-depths.  Coefficient one in
the eventual product makes a depth identify at most one actual vertex, so a
support element itself is a safe vertex label at this algebraic layer.

`gate` is the rooted LCA identity.  `fork` is the sole path-containment
consequence needed to link the three low LCA calculations: an ancestor of
`b` whose branch from `c` meets the root forces the whole `b`--`c` fork to
meet the root.  This narrower field has a direct actual-tree proof.
-/
structure RootedSupportMetric where
  support : Finset ℕ
  zero_mem : 0 ∈ support
  dist : ℕ → ℕ → ℕ
  dist_zero_left : ∀ {a}, a ∈ support → dist 0 a = a
  dist_comm : ∀ {a b}, a ∈ support → b ∈ support → dist a b = dist b a
  gate : ∀ {a b}, a ∈ support → b ∈ support →
    ∃ z ∈ support, z ≤ a ∧ z ≤ b ∧ dist a b + 2 * z = a + b
  fork : ∀ {a b c},
    a ∈ support → b ∈ support → c ∈ support →
    0 < a → a ≤ b → dist a b = b - a → dist a c = a + c →
    dist b c = b + c

/-- The exact first-product information used in the any-order `q ≤ 10`
argument.  `direct` preserves indexed coefficient one, rather than merely
deduplicating a support set.  The three internal-distance fields encode the
global Leech-distance injection on the two actual even components.
-/
structure PrefixFactorData (q : ℕ) where
  P : RootedSupportMetric
  Q : RootedSupportMetric
  direct : ∀ {a b a' b'},
    a ∈ P.support → b ∈ Q.support →
    a' ∈ P.support → b' ∈ Q.support →
    a + b = a' + b' → a = a' ∧ b = b'
  coversBelow : ∀ k, k < q →
    ∃ a ∈ P.support, ∃ b ∈ Q.support, a + b = k
  omitsQ : ∀ {a b}, a ∈ P.support → b ∈ Q.support → a + b ≠ q
  P_internal_injective : ∀ {a b c d},
    a ∈ P.support → b ∈ P.support → c ∈ P.support → d ∈ P.support →
    a ≠ b → c ≠ d → P.dist a b = P.dist c d → s(a, b) = s(c, d)
  Q_internal_injective : ∀ {a b c d},
    a ∈ Q.support → b ∈ Q.support → c ∈ Q.support → d ∈ Q.support →
    a ≠ b → c ≠ d → Q.dist a b = Q.dist c d → s(a, b) = s(c, d)
  internal_disjoint : ∀ {a b c d},
    a ∈ P.support → b ∈ P.support → c ∈ Q.support → d ∈ Q.support →
    a ≠ b → c ≠ d → P.dist a b ≠ Q.dist c d

namespace PrefixFactorData

/-- Swapping the two factors preserves every audited hypothesis. -/
def swap (D : PrefixFactorData q) : PrefixFactorData q where
  P := D.Q
  Q := D.P
  direct := by
    intro a b a' b' ha hb ha' hb' hsum
    have h := D.direct hb ha hb' ha' (by omega)
    exact ⟨h.2, h.1⟩
  coversBelow := by
    intro k hk
    obtain ⟨a, ha, b, hb, hab⟩ := D.coversBelow k hk
    exact ⟨b, hb, a, ha, by omega⟩
  omitsQ := by
    intro a b ha hb
    have h := D.omitsQ hb ha
    omega
  P_internal_injective := D.Q_internal_injective
  Q_internal_injective := D.P_internal_injective
  internal_disjoint := by
    intro a b c d ha hb hc hd hab hcd heq
    exact D.internal_disjoint hc hd ha hb hcd hab heq.symm

private theorem P_not_mem_of_nontrivial_rep
    (D : PrefixFactorData q) {k a b : ℕ}
    (ha : a ∈ D.P.support) (hb : b ∈ D.Q.support)
    (hsum : a + b = k) (hbpos : 0 < b) :
    k ∉ D.P.support := by
  intro hk
  have h := D.direct hk D.Q.zero_mem ha hb (by omega)
  omega

private theorem Q_not_mem_of_nontrivial_rep
    (D : PrefixFactorData q) {k a b : ℕ}
    (ha : a ∈ D.P.support) (hb : b ∈ D.Q.support)
    (hsum : a + b = k) (hapos : 0 < a) :
    k ∉ D.Q.support := by
  intro hk
  have h := D.direct D.P.zero_mem hk ha hb (by omega)
  omega

private theorem P_dist_ne_root
    (D : PrefixFactorData q) {a b k : ℕ}
    (ha : a ∈ D.P.support) (hb : b ∈ D.P.support)
    (hk : k ∈ D.P.support) (hab : a ≠ b) (hkpos : 0 < k)
    (hpairs : s(a, b) ≠ s(0, k)) :
    D.P.dist a b ≠ k := by
  intro hdist
  have hroot := D.P.dist_zero_left hk
  have hp := D.P_internal_injective ha hb D.P.zero_mem hk hab
    (by omega) (hdist.trans hroot.symm)
  exact hpairs hp

private theorem Q_dist_ne_root
    (D : PrefixFactorData q) {a b k : ℕ}
    (ha : a ∈ D.Q.support) (hb : b ∈ D.Q.support)
    (hk : k ∈ D.Q.support) (hab : a ≠ b) (hkpos : 0 < k)
    (hpairs : s(a, b) ≠ s(0, k)) :
    D.Q.dist a b ≠ k := by
  intro hdist
  have hroot := D.Q.dist_zero_left hk
  have hp := D.Q_internal_injective ha hb D.Q.zero_mem hk hab
    (by omega) (hdist.trans hroot.symm)
  exact hpairs hp

/-- Rank one normalizes the two factors: after at most one factor swap,
depth one lies in `P` and not in `Q`. -/
theorem exists_normalized (D : PrefixFactorData q) (hq : 2 ≤ q) :
    ∃ E : PrefixFactorData q,
      1 ∈ E.P.support ∧ 1 ∉ E.Q.support := by
  obtain ⟨a, ha, b, hb, hab⟩ := D.coversBelow 1 (by omega)
  have hcases : (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) := by omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨D, ha, ?_⟩
    exact Q_not_mem_of_nontrivial_rep D ha hb (by omega) (by omega)
  · refine ⟨D.swap, hb, ?_⟩
    exact Q_not_mem_of_nontrivial_rep D.swap hb ha (by omega) (by omega)

/-- The low rooted skeleton forced by ranks below seven.  The final two
fields are useful query endpoints: they say no unlisted factor depth below
eight is being silently discarded. -/
structure BaseSkeleton (D : PrefixFactorData q) where
  P1 : 1 ∈ D.P.support
  Q1_not : 1 ∉ D.Q.support
  Q2 : 2 ∈ D.Q.support
  P4 : 4 ∈ D.P.support
  P5 : 5 ∈ D.P.support
  P_dist_1_4 : D.P.dist 1 4 = 3
  P_dist_1_5 : D.P.dist 1 5 = 6
  P_dist_4_5 : D.P.dist 4 5 = 9
  P_below8 : ∀ {k}, k < 8 → k ∈ D.P.support →
    k = 0 ∨ k = 1 ∨ k = 4 ∨ k = 5
  Q_below8 : ∀ {k}, k < 8 → k ∈ D.Q.support →
    k = 0 ∨ k = 2

/-- Human-audited ranks 1--7, including the LCA/four-point step forcing the
distance nine inside the depth-one factor. -/
theorem baseSkeleton_of_normalized
    (D : PrefixFactorData q) (hq : 7 ≤ q)
    (hP1 : 1 ∈ D.P.support) (hQ1 : 1 ∉ D.Q.support) :
    BaseSkeleton D := by
  /- Rank 2. -/
  obtain ⟨a2, ha2, b2, hb2, hab2⟩ := D.coversBelow 2 (by omega)
  have h2cases :
      (a2 = 0 ∧ b2 = 2) ∨ (a2 = 1 ∧ b2 = 1) ∨
        (a2 = 2 ∧ b2 = 0) := by omega
  have hQ2 : 2 ∈ D.Q.support := by
    rcases h2cases with h02 | h11 | h20
    · simpa [h02.1, h02.2] using hb2
    · exact (hQ1 (h11.2 ▸ hb2)).elim
    · rcases h20 with ⟨rfl, rfl⟩
      have hQ2not : 2 ∉ D.Q.support :=
        Q_not_mem_of_nontrivial_rep D ha2 hb2 (by omega) (by omega)
      obtain ⟨z, hz, hz1, hz2, hgate⟩ := D.P.gate hP1 ha2
      have hz_cases : z = 0 ∨ z = 1 := by omega
      have hd12 : D.P.dist 1 2 = 3 := by
        rcases hz_cases with rfl | rfl
        · omega
        · have hne : D.P.dist 1 2 ≠ 1 := by
            apply P_dist_ne_root D hP1 ha2 hP1 (by omega) (by omega)
            decide
          omega
      obtain ⟨a3, ha3, b3, hb3, hab3⟩ := D.coversBelow 3 (by omega)
      have h3cases :
          (a3 = 0 ∧ b3 = 3) ∨ (a3 = 3 ∧ b3 = 0) := by
        have : b3 ≠ 1 := fun h => hQ1 (h ▸ hb3)
        have : b3 ≠ 2 := fun h => hQ2not (h ▸ hb3)
        omega
      rcases h3cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (D.internal_disjoint hP1 ha2 D.Q.zero_mem hb3
          (by omega) (by omega) <| by
            rw [hd12, D.Q.dist_zero_left hb3]).elim
      · exact (P_dist_ne_root D hP1 ha2 ha3 (by omega) (by omega)
          (by decide) hd12).elim
  have hP2not : 2 ∉ D.P.support :=
    P_not_mem_of_nontrivial_rep D D.P.zero_mem hQ2 (by omega) (by omega)

  /- Rank 3 is already `1+2`, so neither factor may contain depth 3. -/
  have hP3not : 3 ∉ D.P.support :=
    P_not_mem_of_nontrivial_rep D hP1 hQ2 (by omega) (by omega)
  have hQ3not : 3 ∉ D.Q.support :=
    Q_not_mem_of_nontrivial_rep D hP1 hQ2 (by omega) (by omega)

  /- Rank 4. -/
  obtain ⟨a4, ha4, b4, hb4, hab4⟩ := D.coversBelow 4 (by omega)
  have h4cases : (a4 = 4 ∧ b4 = 0) ∨ (a4 = 0 ∧ b4 = 4) := by
    have : a4 ≠ 2 := fun h => hP2not (h ▸ ha4)
    have : a4 ≠ 3 := fun h => hP3not (h ▸ ha4)
    have : b4 ≠ 1 := fun h => hQ1 (h ▸ hb4)
    have : b4 ≠ 3 := fun h => hQ3not (h ▸ hb4)
    omega
  have hP4 : 4 ∈ D.P.support := by
    rcases h4cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ha4
    · have hP4not : 4 ∉ D.P.support :=
        P_not_mem_of_nontrivial_rep D ha4 hb4 (by omega) (by omega)
      obtain ⟨z, hz, hz2, hz4, hgate⟩ := D.Q.gate hQ2 hb4
      have hz_cases : z = 0 ∨ z = 2 := by
        by_cases hz0 : z = 0
        · exact Or.inl hz0
        · have hzpos : 0 < z := Nat.pos_of_ne_zero hz0
          have hz1 : z ≠ 1 := fun h => hQ1 (h ▸ hz)
          exact Or.inr (by omega)
      have hd24 : D.Q.dist 2 4 = 6 := by
        rcases hz_cases with rfl | rfl
        · omega
        · have hne : D.Q.dist 2 4 ≠ 2 := by
            apply Q_dist_ne_root D hQ2 hb4 hQ2 (by omega) (by omega)
            decide
          omega
      have hP5not : 5 ∉ D.P.support :=
        P_not_mem_of_nontrivial_rep D hP1 hb4 (by omega) (by omega)
      have hQ5not : 5 ∉ D.Q.support :=
        Q_not_mem_of_nontrivial_rep D hP1 hb4 (by omega) (by omega)
      obtain ⟨a6, ha6, b6, hb6, hab6⟩ := D.coversBelow 6 (by omega)
      have hP4not' : 4 ∉ D.P.support := hP4not
      have h6cases : (a6 = 6 ∧ b6 = 0) ∨ (a6 = 0 ∧ b6 = 6) := by
        have : a6 ≠ 2 := fun h => hP2not (h ▸ ha6)
        have : a6 ≠ 3 := fun h => hP3not (h ▸ ha6)
        have : a6 ≠ 4 := fun h => hP4not' (h ▸ ha6)
        have : a6 ≠ 5 := fun h => hP5not (h ▸ ha6)
        have : b6 ≠ 1 := fun h => hQ1 (h ▸ hb6)
        have : b6 ≠ 3 := fun h => hQ3not (h ▸ hb6)
        have : b6 ≠ 5 := fun h => hQ5not (h ▸ hb6)
        omega
      rcases h6cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (D.internal_disjoint D.P.zero_mem ha6 hQ2 hb4
          (by omega) (by omega) <| by
            rw [D.P.dist_zero_left ha6, hd24]).elim
      · exact (Q_dist_ne_root D hQ2 hb4 hb6 (by omega) (by omega)
          (by decide) hd24).elim
  have hQ4not : 4 ∉ D.Q.support :=
    Q_not_mem_of_nontrivial_rep D hP4 D.Q.zero_mem (by omega) (by omega)

  /- Rank 5. -/
  obtain ⟨a5, ha5, b5, hb5, hab5⟩ := D.coversBelow 5 (by omega)
  have h5cases : (a5 = 5 ∧ b5 = 0) ∨ (a5 = 0 ∧ b5 = 5) := by
    have : a5 ≠ 2 := fun h => hP2not (h ▸ ha5)
    have : a5 ≠ 3 := fun h => hP3not (h ▸ ha5)
    have : b5 ≠ 1 := fun h => hQ1 (h ▸ hb5)
    have : b5 ≠ 3 := fun h => hQ3not (h ▸ hb5)
    have : b5 ≠ 4 := fun h => hQ4not (h ▸ hb5)
    omega
  have hP5 : 5 ∈ D.P.support := by
    rcases h5cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ha5
    · have hdup := D.direct hP1 hb5 hP4 hQ2 (by omega)
      omega
  have hQ5not : 5 ∉ D.Q.support :=
    Q_not_mem_of_nontrivial_rep D hP5 D.Q.zero_mem (by omega) (by omega)

  /- Forced topology in P. -/
  have hd14 : D.P.dist 1 4 = 3 := by
    obtain ⟨z, hz, hz1, hz4, hgate⟩ := D.P.gate hP1 hP4
    have hz_cases : z = 0 ∨ z = 1 := by omega
    rcases hz_cases with rfl | rfl
    · have hne : D.P.dist 1 4 ≠ 5 := by
        apply P_dist_ne_root D hP1 hP4 hP5 (by omega) (by omega)
        decide
      omega
    · omega
  have hd15 : D.P.dist 1 5 = 6 := by
    obtain ⟨z, hz, hz1, hz5, hgate⟩ := D.P.gate hP1 hP5
    have hz_cases : z = 0 ∨ z = 1 := by omega
    rcases hz_cases with rfl | rfl
    · omega
    · have hne : D.P.dist 1 5 ≠ 4 := by
        apply P_dist_ne_root D hP1 hP5 hP4 (by omega) (by omega)
        decide
      omega
  have hd45 : D.P.dist 4 5 = 9 := by
    exact D.P.fork hP1 hP4 hP5 (by omega) (by omega) hd14 hd15

  have hP6not : 6 ∉ D.P.support :=
    P_not_mem_of_nontrivial_rep D hP4 hQ2 (by omega) (by omega)
  have hQ6not : 6 ∉ D.Q.support :=
    Q_not_mem_of_nontrivial_rep D hP4 hQ2 (by omega) (by omega)
  have hP7not : 7 ∉ D.P.support :=
    P_not_mem_of_nontrivial_rep D hP5 hQ2 (by omega) (by omega)
  have hQ7not : 7 ∉ D.Q.support :=
    Q_not_mem_of_nontrivial_rep D hP5 hQ2 (by omega) (by omega)

  refine {
    P1 := hP1
    Q1_not := hQ1
    Q2 := hQ2
    P4 := hP4
    P5 := hP5
    P_dist_1_4 := hd14
    P_dist_1_5 := hd15
    P_dist_4_5 := hd45
    P_below8 := ?_
    Q_below8 := ?_ }
  · intro k hklt hkmem
    interval_cases k <;> simp_all
  · intro k hklt hkmem
    interval_cases k <;> simp_all

/-- The audited any-order support-factor theorem.  This is the formal core
of `q ≤ 10`; it uses neither order 38 nor distinct ports. -/
theorem q_le_ten (D : PrefixFactorData q) : q ≤ 10 := by
  by_contra hnot
  have hq11 : 11 ≤ q := by omega
  obtain ⟨E, hP1, hQ1⟩ := exists_normalized D (by omega)
  let S := baseSkeleton_of_normalized E (by omega) hP1 hQ1

  obtain ⟨a8, ha8, b8, hb8, hab8⟩ := E.coversBelow 8 (by omega)
  have h8root : (a8 = 8 ∧ b8 = 0) ∨ (a8 = 0 ∧ b8 = 8) := by
    by_cases ha0 : a8 = 0
    · exact Or.inr ⟨ha0, by omega⟩
    by_cases hb0 : b8 = 0
    · exact Or.inl ⟨by omega, hb0⟩
    have haPos : 0 < a8 := Nat.pos_of_ne_zero ha0
    have hbPos : 0 < b8 := Nat.pos_of_ne_zero hb0
    have haLt : a8 < 8 := by omega
    have hbLt : b8 < 8 := by omega
    have haClass := S.P_below8 haLt ha8
    have hbClass := S.Q_below8 hbLt hb8
    omega

  rcases h8root with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · /- `8 ∈ P`. -/
    have hQ8not : 8 ∉ E.Q.support :=
      Q_not_mem_of_nontrivial_rep E ha8 hb8 (by omega) (by omega)
    obtain ⟨a9, ha9, b9, hb9, hab9⟩ := E.coversBelow 9 (by omega)
    have h9root : (a9 = 9 ∧ b9 = 0) ∨ (a9 = 0 ∧ b9 = 9) := by
      by_cases ha0 : a9 = 0
      · exact Or.inr ⟨ha0, by omega⟩
      by_cases hb0 : b9 = 0
      · exact Or.inl ⟨by omega, hb0⟩
      have haPos : 0 < a9 := Nat.pos_of_ne_zero ha0
      have hbPos : 0 < b9 := Nat.pos_of_ne_zero hb0
      have haLt : a9 < 9 := by omega
      have hbLt : b9 < 9 := by omega
      have haClass : a9 = 1 ∨ a9 = 4 ∨ a9 = 5 ∨ a9 = 8 := by
        by_cases h : a9 < 8
        · rcases S.P_below8 h ha9 with h | h | h | h <;> omega
        · omega
      have hbClass : b9 = 2 := by
        have hb8lt : b9 < 8 := by
          by_contra h
          have : b9 = 8 := by omega
          exact hQ8not (this ▸ hb9)
        rcases S.Q_below8 hb8lt hb9 with h | h
        · omega
        · exact h
      omega
    rcases h9root with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (P_dist_ne_root E S.P4 S.P5 ha9 (by omega) (by omega)
        (by decide) S.P_dist_4_5).elim
    · have hdup := E.direct S.P1 hb9 ha8 S.Q2 (by omega)
      omega
  · /- `8 ∈ Q`. -/
    have hP8not : 8 ∉ E.P.support :=
      P_not_mem_of_nontrivial_rep E ha8 hb8 (by omega) (by omega)
    have hP9not : 9 ∉ E.P.support :=
      P_not_mem_of_nontrivial_rep E S.P1 hb8 (by omega) (by omega)
    have hQ9not : 9 ∉ E.Q.support :=
      Q_not_mem_of_nontrivial_rep E S.P1 hb8 (by omega) (by omega)
    obtain ⟨a10, ha10, b10, hb10, hab10⟩ := E.coversBelow 10 (by omega)
    have h10root : (a10 = 10 ∧ b10 = 0) ∨ (a10 = 0 ∧ b10 = 10) := by
      by_cases ha0 : a10 = 0
      · exact Or.inr ⟨ha0, by omega⟩
      by_cases hb0 : b10 = 0
      · exact Or.inl ⟨by omega, hb0⟩
      have haPos : 0 < a10 := Nat.pos_of_ne_zero ha0
      have hbPos : 0 < b10 := Nat.pos_of_ne_zero hb0
      have haLt : a10 < 10 := by omega
      have hbLt : b10 < 10 := by omega
      have haClass : a10 = 1 ∨ a10 = 4 ∨ a10 = 5 := by
        have ha8lt : a10 < 8 := by
          by_contra h
          have : a10 = 8 ∨ a10 = 9 := by omega
          rcases this with h | h
          · exact hP8not (h ▸ ha10)
          · exact hP9not (h ▸ ha10)
        rcases S.P_below8 ha8lt ha10 with h | h | h | h
        · omega
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      have hbClass : b10 = 2 ∨ b10 = 8 := by
        by_cases h : b10 < 8
        · rcases S.Q_below8 h hb10 with h0 | h2
          · omega
          · exact Or.inl h2
        · have : b10 = 8 ∨ b10 = 9 := by omega
          rcases this with h8 | h9
          · exact Or.inr h8
          · exact (hQ9not (h9 ▸ hb10)).elim
      omega
    rcases h10root with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hdup := E.direct ha10 S.Q2 S.P4 hb8 (by omega)
      omega
    · obtain ⟨z, hz, hz2, hz8, hgate⟩ := E.Q.gate S.Q2 hb8
      have hzCases : z = 0 ∨ z = 2 := by
        by_cases hz0 : z = 0
        · exact Or.inl hz0
        · have hzpos : 0 < z := Nat.pos_of_ne_zero hz0
          have hz1 : z ≠ 1 := fun h => S.Q1_not (h ▸ hz)
          exact Or.inr (by omega)
      rcases hzCases with rfl | rfl
      · exact (Q_dist_ne_root E S.Q2 hb8 hb10 (by omega) (by omega)
          (by decide) <| by omega).elim
      · exact (E.internal_disjoint S.P1 S.P5 S.Q2 hb8
          (by omega) (by omega) <| by
            rw [S.P_dist_1_5]
            omega).elim

/-- The sharp common-port-compatible strengthening `q ≠ 7`. -/
theorem q_ne_seven (D : PrefixFactorData q) : q ≠ 7 := by
  intro hq
  subst q
  obtain ⟨E, hP1, hQ1⟩ := exists_normalized D (by omega)
  let S := baseSkeleton_of_normalized E (by omega) hP1 hQ1
  exact E.omitsQ S.P5 S.Q2 (by omega)

/-- Rank one says which of the two *actual* oriented factors is normalized.
Unlike `exists_normalized`, this disjunction retains the identity of both
factors and is therefore suitable for rerooting the middle component. -/
theorem normalized_self_or_swap
    (D : PrefixFactorData q) (hq : 2 ≤ q) :
    (1 ∈ D.P.support ∧ 1 ∉ D.Q.support) ∨
      (1 ∈ D.Q.support ∧ 1 ∉ D.P.support) := by
  obtain ⟨a, ha, b, hb, hab⟩ := D.coversBelow 1 (by omega)
  have hcases : (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) := by omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨ha,
      Q_not_mem_of_nontrivial_rep D ha hb (by omega) (by omega)⟩
  · exact Or.inr ⟨hb,
      P_not_mem_of_nontrivial_rep D ha hb (by omega) (by omega)⟩

structure Q8Skeleton (D : PrefixFactorData q) extends BaseSkeleton D where
  P8_not : 8 ∉ D.P.support
  Q8_not : 8 ∉ D.Q.support
  P9_not : 9 ∉ D.P.support
  Q9_not : 9 ∉ D.Q.support
  no_sum_9 : ∀ {a b}, a ∈ D.P.support → b ∈ D.Q.support → a + b ≠ 9

theorem q8Skeleton_of_normalized
    (D : PrefixFactorData q) (hq : q = 8)
    (hP1 : 1 ∈ D.P.support) (hQ1 : 1 ∉ D.Q.support) :
    Q8Skeleton D := by
  let S := baseSkeleton_of_normalized D (by omega) hP1 hQ1
  have hP8not : 8 ∉ D.P.support := by
    intro h
    exact D.omitsQ h D.Q.zero_mem (by omega)
  have hQ8not : 8 ∉ D.Q.support := by
    intro h
    exact D.omitsQ D.P.zero_mem h (by omega)
  have hP9not : 9 ∉ D.P.support := by
    intro h
    exact (P_dist_ne_root D S.P4 S.P5 h
      (by omega) (by omega)
      (by decide) S.P_dist_4_5).elim
  have hQ9not : 9 ∉ D.Q.support := by
    intro h
    exact (D.internal_disjoint S.P4 S.P5 D.Q.zero_mem h
      (by omega) (by omega) <| by
        rw [S.P_dist_4_5, D.Q.dist_zero_left h]).elim
  have hno9 : ∀ {a b}, a ∈ D.P.support → b ∈ D.Q.support →
      a + b ≠ 9 := by
    intro a b ha hb hab
    by_cases ha0 : a = 0
    · have hb9 : b = 9 := by omega
      exact hQ9not (hb9 ▸ hb)
    by_cases hb0 : b = 0
    · have ha9 : a = 9 := by omega
      exact hP9not (ha9 ▸ ha)
    have halt : a < 9 := by omega
    have hblt : b < 9 := by omega
    have haClass : a = 1 ∨ a = 4 ∨ a = 5 := by
      by_cases h8 : a < 8
      · rcases S.P_below8 h8 ha with h | h | h | h
        · exact (ha0 h).elim
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · have : a = 8 := by omega
        exact (hP8not (this ▸ ha)).elim
    have hbClass : b = 2 := by
      by_cases h8 : b < 8
      · rcases S.Q_below8 h8 hb with h | h
        · exact (hb0 h).elim
        · exact h
      · have : b = 8 := by omega
        exact (hQ8not (this ▸ hb)).elim
    omega
  exact {
    toBaseSkeleton := S
    P8_not := hP8not
    Q8_not := hQ8not
    P9_not := hP9not
    Q9_not := hQ9not
    no_sum_9 := hno9 }

theorem no_first_sum_nine_of_q_eight
    (D : PrefixFactorData q) (hq : q = 8) :
    ∀ {a b}, a ∈ D.P.support → b ∈ D.Q.support → a + b ≠ 9 := by
  rcases normalized_self_or_swap D (by omega) with h | h
  · exact (q8Skeleton_of_normalized D hq h.1 h.2).no_sum_9
  · intro a b ha hb hab
    exact (q8Skeleton_of_normalized D.swap hq h.1 h.2).no_sum_9
      hb ha (by omega)

theorem Q8Skeleton.sum_ten_roots
    {D : PrefixFactorData q} (S : Q8Skeleton D)
    {a b : ℕ} (ha : a ∈ D.P.support) (hb : b ∈ D.Q.support)
    (hab : a + b = 10) :
    (a = 10 ∧ b = 0) ∨ (a = 0 ∧ b = 10) := by
  by_cases ha0 : a = 0
  · exact Or.inr ⟨ha0, by omega⟩
  by_cases hb0 : b = 0
  · exact Or.inl ⟨by omega, hb0⟩
  have halt : a < 10 := by omega
  have hblt : b < 10 := by omega
  have haClass : a = 1 ∨ a = 4 ∨ a = 5 := by
    by_cases h8 : a < 8
    · rcases S.P_below8 h8 ha with h | h | h | h
      · exact (ha0 h).elim
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · have : a = 8 ∨ a = 9 := by omega
      rcases this with h | h
      · exact (S.P8_not (h ▸ ha)).elim
      · exact (S.P9_not (h ▸ ha)).elim
  have hbClass : b = 2 := by
    by_cases h8 : b < 8
    · rcases S.Q_below8 h8 hb with h | h
      · exact (hb0 h).elim
      · exact h
    · have : b = 8 ∨ b = 9 := by omega
      rcases this with h | h
      · exact (S.Q8_not (h ▸ hb)).elim
      · exact (S.Q9_not (h ▸ hb)).elim
  omega

theorem Q8Skeleton.P10_distances
    {D : PrefixFactorData q} (S : Q8Skeleton D)
    (hP10 : 10 ∈ D.P.support) :
    D.P.dist 1 10 = 11 ∧ D.P.dist 4 10 = 14 := by
  have hd110 : D.P.dist 1 10 = 11 := by
    obtain ⟨z, hz, hz1, hz10, hgate⟩ := D.P.gate S.P1 hP10
    have hzCases : z = 0 ∨ z = 1 := by omega
    rcases hzCases with rfl | rfl
    · omega
    · have hp := D.P_internal_injective S.P1 hP10 S.P4 S.P5
          (by omega) (by omega) (by
            rw [S.P_dist_4_5]
            omega)
      simp only [Sym2.eq_iff] at hp
      omega
  have hd410 : D.P.dist 4 10 = 14 := by
    exact D.P.fork S.P1 S.P4 hP10 (by omega) (by omega)
      S.P_dist_1_4 hd110
  exact ⟨hd110, hd410⟩

structure Q9Skeleton (D : PrefixFactorData q) extends BaseSkeleton D where
  P8 : 8 ∈ D.P.support
  Q8_not : 8 ∉ D.Q.support
  P9_not : 9 ∉ D.P.support
  Q9_not : 9 ∉ D.Q.support
  P_dist_1_8 : D.P.dist 1 8 = 7

theorem q9Skeleton_of_normalized
    (D : PrefixFactorData q) (hq : q = 9)
    (hP1 : 1 ∈ D.P.support) (hQ1 : 1 ∉ D.Q.support) :
    Q9Skeleton D := by
  let S := baseSkeleton_of_normalized D (by omega) hP1 hQ1
  obtain ⟨a8, ha8, b8, hb8, hab8⟩ := D.coversBelow 8 (by omega)
  have h8root : (a8 = 8 ∧ b8 = 0) ∨ (a8 = 0 ∧ b8 = 8) := by
    by_cases ha0 : a8 = 0
    · exact Or.inr ⟨ha0, by omega⟩
    by_cases hb0 : b8 = 0
    · exact Or.inl ⟨by omega, hb0⟩
    have haClass := S.P_below8 (by omega) ha8
    have hbClass := S.Q_below8 (by omega) hb8
    omega
  have hP8 : 8 ∈ D.P.support := by
    rcases h8root with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ha8
    · exact (D.omitsQ S.P1 hb8 (by omega)).elim
  have hQ8not : 8 ∉ D.Q.support :=
    Q_not_mem_of_nontrivial_rep D hP8 D.Q.zero_mem (by omega) (by omega)
  have hP9not : 9 ∉ D.P.support := by
    intro h
    exact D.omitsQ h D.Q.zero_mem (by omega)
  have hQ9not : 9 ∉ D.Q.support := by
    intro h
    exact D.omitsQ D.P.zero_mem h (by omega)
  have hd18 : D.P.dist 1 8 = 7 := by
    obtain ⟨z, hz, hz1, hz8, hgate⟩ := D.P.gate S.P1 hP8
    have hzCases : z = 0 ∨ z = 1 := by omega
    rcases hzCases with rfl | rfl
    · have hp := D.P_internal_injective S.P1 hP8 S.P4 S.P5
        (by omega) (by omega) (by
          rw [S.P_dist_4_5]
          omega)
      simp only [Sym2.eq_iff] at hp
      omega
    · omega
  exact {
    toBaseSkeleton := S
    P8 := hP8
    Q8_not := hQ8not
    P9_not := hP9not
    Q9_not := hQ9not
    P_dist_1_8 := hd18 }

/-- Exact normalized first-product information used by the audited `q=10`
linked closure. -/
structure Q10Skeleton (D : PrefixFactorData q) extends BaseSkeleton D where
  Q8 : 8 ∈ D.Q.support
  P8_not : 8 ∉ D.P.support
  P9_not : 9 ∉ D.P.support
  Q9_not : 9 ∉ D.Q.support
  P10_not : 10 ∉ D.P.support
  Q10_not : 10 ∉ D.Q.support
  Q_dist_2_8 : D.Q.dist 2 8 = 10
  no_sum_11 : ∀ {a b}, a ∈ D.P.support → b ∈ D.Q.support → a + b ≠ 11

theorem q10Skeleton_of_normalized
    (D : PrefixFactorData q) (hq : q = 10)
    (hP1 : 1 ∈ D.P.support) (hQ1 : 1 ∉ D.Q.support) :
    Q10Skeleton D := by
  let S := baseSkeleton_of_normalized D (by omega) hP1 hQ1
  obtain ⟨a8, ha8, b8, hb8, hab8⟩ := D.coversBelow 8 (by omega)
  have h8root : (a8 = 8 ∧ b8 = 0) ∨ (a8 = 0 ∧ b8 = 8) := by
    by_cases ha0 : a8 = 0
    · exact Or.inr ⟨ha0, by omega⟩
    by_cases hb0 : b8 = 0
    · exact Or.inl ⟨by omega, hb0⟩
    have haClass := S.P_below8 (by omega) ha8
    have hbClass := S.Q_below8 (by omega) hb8
    omega
  have hQ8 : 8 ∈ D.Q.support := by
    rcases h8root with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (D.omitsQ ha8 S.Q2 (by omega)).elim
    · exact hb8
  have hP8not : 8 ∉ D.P.support :=
    P_not_mem_of_nontrivial_rep D D.P.zero_mem hQ8 (by omega) (by omega)
  have hP9not : 9 ∉ D.P.support :=
    P_not_mem_of_nontrivial_rep D hP1 hQ8 (by omega) (by omega)
  have hQ9not : 9 ∉ D.Q.support :=
    Q_not_mem_of_nontrivial_rep D hP1 hQ8 (by omega) (by omega)
  have hP10not : 10 ∉ D.P.support := by
    intro h
    exact D.omitsQ h D.Q.zero_mem (by omega)
  have hQ10not : 10 ∉ D.Q.support := by
    intro h
    exact D.omitsQ D.P.zero_mem h (by omega)
  have hd28 : D.Q.dist 2 8 = 10 := by
    obtain ⟨z, hz, hz2, hz8, hgate⟩ := D.Q.gate S.Q2 hQ8
    have hzCases : z = 0 ∨ z = 2 := by
      by_cases hz0 : z = 0
      · exact Or.inl hz0
      · have hz1 : z ≠ 1 := fun h => S.Q1_not (h ▸ hz)
        exact Or.inr (by omega)
    rcases hzCases with rfl | rfl
    · omega
    · exact (D.internal_disjoint S.P1 S.P5 S.Q2 hQ8
        (by omega) (by omega) <| by
          rw [S.P_dist_1_5]
          omega).elim
  have hno11 : ∀ {a b}, a ∈ D.P.support → b ∈ D.Q.support →
      a + b ≠ 11 := by
    intro a b ha hb hab
    by_cases ha0 : a = 0
    · have hb11 : b = 11 := by omega
      subst b
      have hdup := D.direct S.P1 hb S.P4 hQ8 (by omega)
      omega
    by_cases hb0 : b = 0
    · have ha11 : a = 11 := by omega
      subst a
      have hdup := D.direct ha S.Q2 S.P5 hQ8 (by omega)
      omega
    have haClass : a = 1 ∨ a = 4 ∨ a = 5 := by
      have halt : a < 11 := by omega
      by_cases h8 : a < 8
      · rcases S.P_below8 h8 ha with h | h | h | h
        · exact (ha0 h).elim
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · have : a = 8 ∨ a = 9 ∨ a = 10 := by omega
        rcases this with h | h | h
        · exact (hP8not (h ▸ ha)).elim
        · exact (hP9not (h ▸ ha)).elim
        · exact (hP10not (h ▸ ha)).elim
    have hbClass : b = 2 ∨ b = 8 := by
      have hblt : b < 11 := by omega
      by_cases h8 : b < 8
      · rcases S.Q_below8 h8 hb with h | h
        · exact (hb0 h).elim
        · exact Or.inl h
      · have : b = 8 ∨ b = 9 ∨ b = 10 := by omega
        rcases this with h | h | h
        · exact Or.inr h
        · exact (hQ9not (h ▸ hb)).elim
        · exact (hQ10not (h ▸ hb)).elim
    omega
  exact {
    toBaseSkeleton := S
    Q8 := hQ8
    P8_not := hP8not
    P9_not := hP9not
    Q9_not := hQ9not
    P10_not := hP10not
    Q10_not := hQ10not
    Q_dist_2_8 := hd28
    no_sum_11 := hno11 }

/-- Orientation-free form of the audited fact that the first product omits
rank 11 when `q=10`. -/
theorem no_first_sum_eleven_of_q_ten
    (D : PrefixFactorData q) (hq : q = 10) :
    ∀ {a b}, a ∈ D.P.support → b ∈ D.Q.support → a + b ≠ 11 := by
  rcases normalized_self_or_swap D (by omega) with h | h
  · exact (q10Skeleton_of_normalized D hq h.1 h.2).no_sum_11
  · intro a b ha hb hab
    have hs := (q10Skeleton_of_normalized D.swap hq h.1 h.2).no_sum_11
      hb ha
    exact hs (by omega)

end PrefixFactorData

/-! ## What the present graph API already constructs -/

/-- Actual graph data for the two odd physical weights.  This is independent
of the support-factor extraction: the unit edge and the second odd edge are
named actual physical edges of the input tree. -/
structure GraphTwoOddWeights (T : PosIntTree n) where
  unit : T.Edge
  second : T.Edge
  ne : unit ≠ second
  unit_weight : T.weight unit = 1
  second_odd : Odd (T.weight second)
  odd_iff : ∀ g : T.Edge, Odd (T.weight g) ↔ g = unit ∨ g = second
  q : ℕ
  second_weight : T.weight second = 2 * q + 1
  q_pos : 0 < q

/-- Existing graph APIs orient the two odd physical weights as `1` and
`2*q+1`, with `q > 0`; the linked rooted factors are constructed below. -/
theorem exists_graphTwoOddWeights
    (T : PosIntTree n) (hL : IsLeech T) (hn : 2 ≤ n)
    (hTwo : ExactlyTwoOddPhysicalEdges T) :
    Nonempty (GraphTwoOddWeights T) := by
  classical
  let d := twoOddEdges T hTwo
  obtain ⟨u, hu1, _huUnique⟩ := t1_existsUnique_weight_one hL hn
  have huOdd : Odd (T.weight u) := by simp [hu1]
  rcases (d.odd_iff u).mp huOdd with hue | huf
  · have hf1 : T.weight d.f ≠ 1 := by
      intro hf
      have hfe : d.f = d.e := t1_edge_weight_injective hL (by
        rw [hue] at hu1
        omega)
      exact d.ne hfe.symm
    let q := T.weight d.f / 2
    have hweight : T.weight d.f = 2 * q + 1 := by
      exact (Nat.two_mul_div_two_add_one_of_odd d.odd_f).symm
    have hqpos : 0 < q := by
      by_contra h
      have : q = 0 := by omega
      rw [this] at hweight
      exact hf1 (by omega)
    refine ⟨{
      unit := u
      second := d.f
      ne := ?_
      unit_weight := hu1
      second_odd := d.odd_f
      odd_iff := ?_
      q := q
      second_weight := hweight
      q_pos := hqpos }⟩
    · intro h
      apply d.ne
      exact hue.symm.trans h
    · intro g
      rw [d.odd_iff]
      constructor
      · rintro (h | h)
        · exact Or.inl (h.trans hue.symm)
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl (h.trans hue)
        · exact Or.inr h
  · have he1 : T.weight d.e ≠ 1 := by
      intro he
      have hef : d.e = d.f := t1_edge_weight_injective hL (by
        rw [huf] at hu1
        omega)
      exact d.ne hef
    let q := T.weight d.e / 2
    have hweight : T.weight d.e = 2 * q + 1 := by
      exact (Nat.two_mul_div_two_add_one_of_odd d.odd_e).symm
    have hqpos : 0 < q := by
      by_contra h
      have : q = 0 := by omega
      rw [this] at hweight
      exact he1 (by omega)
    refine ⟨{
      unit := u
      second := d.e
      ne := ?_
      unit_weight := hu1
      second_odd := d.odd_e
      odd_iff := ?_
      q := q
      second_weight := hweight
      q_pos := hqpos }⟩
    · intro h
      apply d.ne
      exact h.symm.trans huf
    · intro g
      rw [d.odd_iff]
      constructor
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl (h.trans huf.symm)
      · rintro (h | h)
        · exact Or.inr (h.trans huf)
        · exact Or.inl h

/-! ## Actual rooted-component support metrics -/

/-- The first common vertex on two paths to a root, with the firstness
property retained.  `OddEdgesT11Adapter.exists_root_gate` proves the metric
identity but intentionally hides this path-containment witness; G015 needs
it once for the audited `1,4,5` fork. -/
private theorem existsFirstCommon
    {T : PosIntTree n} {u v r : Fin n}
    (p : T.graph.Walk u r) (q : T.graph.Walk v r) :
    ∃ z, ∃ hp : z ∈ p.support, ∃ _hq : z ∈ q.support,
      ∀ x, x ∈ (p.takeUntil z hp).support → x ∈ q.support → x = z := by
  induction p with
  | @nil r0 =>
      refine ⟨r0, by simp, q.end_mem_support, ?_⟩
      intro x hx _
      simpa using hx
  | @cons u w r h p ih =>
      by_cases hu : u ∈ q.support
      · refine ⟨u, by simp, hu, ?_⟩
        intro x hx _
        simpa using hx
      · obtain ⟨z, hzp, hzq, hfirst⟩ := ih q
        have hzu : u ≠ z := by
          intro huz
          apply hu
          simpa [huz] using hzq
        have hzcons : z ∈ (p.cons h).support := by simp [hzp]
        refine ⟨z, hzcons, hzq, ?_⟩
        intro x hx hxq
        rw [p.takeUntil_cons hzp hzu h] at hx
        rcases (by simpa using hx :
            x = u ∨ x ∈ (p.takeUntil z hzp).support) with rfl | hxtail
        · exact (hu hxq).elim
        · exact hfirst x hxtail hxq

/-- A rooted LCA whose first-common path property is still visible. -/
structure StrongRootGate (T : PosIntTree n) (r u v : Fin n) where
  gate : Fin n
  gate_mem_u : gate ∈ (T.path u r).1.support
  gate_mem_v : gate ∈ (T.path v r).1.support
  first_common : ∀ x,
    x ∈ ((T.path u r).1.takeUntil gate gate_mem_u).support →
    x ∈ (T.path v r).1.support → x = gate
  distance_eq :
    T.dist u v + 2 * T.dist gate r = T.dist u r + T.dist v r

private theorem strongRootGate_nonempty
    (T : PosIntTree n) (r u v : Fin n) :
    Nonempty (StrongRootGate T r u v) := by
  classical
  let pu := T.path u r
  let pv := T.path v r
  obtain ⟨z, hzu, hzv, hfirst⟩ := existsFirstCommon pu.1 pv.1
  let a := pu.1.takeUntil z hzu
  let b := pv.1.takeUntil z hzv
  have ha : a.IsPath := pu.2.takeUntil hzu
  have hb : b.IsPath := pv.2.takeUntil hzv
  have hdisjoint : a.support.Disjoint b.reverse.support.tail := by
    rw [List.disjoint_left]
    intro x hxa hxb
    have hxbq : x ∈ pv.1.support := by
      apply pv.1.support_takeUntil_subset hzv
      have : x ∈ b.reverse.support := List.mem_of_mem_tail hxb
      simpa [b] using this
    have hxz : x = z := hfirst x (by simpa [a] using hxa) hxbq
    subst x
    have hnodup : b.reverse.support.Nodup := hb.reverse.support_nodup
    rw [b.reverse.support_eq_cons] at hnodup hxb
    exact (List.nodup_cons.mp hnodup).1 hxb
  let route := a.append b.reverse
  have hroute : route.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append,
      List.nodup_append]
    refine ⟨ha.support_nodup, hb.reverse.support_nodup.tail, ?_⟩
    intro x hx y hy hxy
    subst y
    exact (List.disjoint_left.mp hdisjoint hx) hy
  have huv : T.dist u v = T.dist u z + T.dist v z := by
    have hw : T.walkWeight route = T.dist u v :=
      T.path_walkWeight_eq_dist ⟨route, hroute⟩
    rw [LeechTrees.OddEdges.T11Adapter.PosIntTree.walkWeight_append T,
      LeechTrees.OddEdges.T11Adapter.PosIntTree.walkWeight_reverse T,
      T.path_walkWeight_eq_dist ⟨a, ha⟩,
      T.path_walkWeight_eq_dist ⟨b, hb⟩] at hw
    exact hw.symm
  have hur : T.dist u r = T.dist u z + T.dist z r :=
    LeechTrees.OddEdges.T11Adapter.PosIntTree.dist_split_at_path_vertex T hzu
  have hvr : T.dist v r = T.dist v z + T.dist z r :=
    LeechTrees.OddEdges.T11Adapter.PosIntTree.dist_split_at_path_vertex T hzv
  exact ⟨{
    gate := z
    gate_mem_u := hzu
    gate_mem_v := hzv
    first_common := hfirst
    distance_eq := by omega }⟩

noncomputable def strongRootGate
    (T : PosIntTree n) (r u v : Fin n) : StrongRootGate T r u v :=
  Classical.choice (strongRootGate_nonempty T r u v)

theorem StrongRootGate.common_eq_root
    {T : PosIntTree n} {r u v : Fin n}
    (G : StrongRootGate T r u v) (hgate : G.gate = r)
    {x : Fin n} (hxu : x ∈ (T.path u r).1.support)
    (hxv : x ∈ (T.path v r).1.support) : x = r := by
  have htakePath :
      ((T.path u r).1.takeUntil G.gate G.gate_mem_u).IsPath :=
    (T.path u r).2.takeUntil G.gate_mem_u
  have htakeEq :
      (⟨(T.path u r).1.takeUntil G.gate G.gate_mem_u, htakePath⟩ :
        T.graph.Path u G.gate) =
      T.path u G.gate :=
    T.path_unique _
  have hxTake :
      x ∈ ((T.path u r).1.takeUntil G.gate G.gate_mem_u).support := by
    rw [congrArg (fun p => p.1.support) htakeEq]
    rw [hgate]
    exact hxu
  exact (G.first_common x hxTake hxv).trans hgate

theorem pathSupport_suffix_subset
    (T : PosIntTree n) {u r z : Fin n}
    (hz : z ∈ (T.path u r).1.support) :
    (T.path z r).1.support ⊆ (T.path u r).1.support := by
  let b := (T.path u r).1.dropUntil z hz
  have hb : b.IsPath := (T.path u r).2.dropUntil hz
  have hbeq : (⟨b, hb⟩ : T.graph.Path z r) = T.path z r :=
    T.path_unique _
  intro x hx
  have hxb : x ∈ b.support := by
    rw [congrArg (fun p => p.1.support) hbeq]
    exact hx
  exact (T.path u r).1.support_dropUntil_subset hz hxb

theorem mem_pathSupport_comm
    (T : PosIntTree n) {u v x : Fin n} :
    x ∈ (T.path u v).1.support ↔ x ∈ (T.path v u).1.support := by
  let rp : T.graph.Path v u :=
    ⟨(T.path u v).1.reverse, (T.path u v).2.reverse⟩
  have hrp : rp = T.path v u := T.path_unique rp
  rw [← congrArg (fun p => p.1.support) hrp]
  simp [rp, SimpleGraph.Walk.support_reverse]

/-- Vertices on one path to a root are comparable by rooted path
containment. -/
theorem pathSupport_comparable
    (T : PosIntTree n) {u r x y : Fin n}
    (hx : x ∈ (T.path u r).1.support)
    (hy : y ∈ (T.path u r).1.support) :
    x ∈ (T.path y r).1.support ∨ y ∈ (T.path x r).1.support := by
  let P := (T.path r u).1
  have hxP : x ∈ P.support :=
    (mem_pathSupport_comm T).mp hx
  have hyP : y ∈ P.support :=
    (mem_pathSupport_comm T).mp hy
  let lx := (P.takeUntil x hxP).length
  let ly := (P.takeUntil y hyP).length
  rcases Nat.le_total lx ly with hxy | hyx
  · let q := P.takeUntil y hyP
    have hqpath : q.IsPath := (T.path r u).2.takeUntil hyP
    have hqeq : (⟨q, hqpath⟩ : T.graph.Path r y) = T.path r y :=
      T.path_unique _
    have hxAt : P.getVert lx = x := P.getVert_length_takeUntil hxP
    have hqAt : q.getVert lx = P.getVert lx := P.getVert_takeUntil hyP hxy
    have hxq : x ∈ q.support := by
      rw [← hxAt, ← hqAt]
      exact q.getVert_mem_support lx
    have hxry : x ∈ (T.path r y).1.support := by
      rw [← congrArg (fun p => p.1.support) hqeq]
      exact hxq
    exact Or.inl ((mem_pathSupport_comm T).mpr hxry)
  · let q := P.takeUntil x hxP
    have hqpath : q.IsPath := (T.path r u).2.takeUntil hxP
    have hqeq : (⟨q, hqpath⟩ : T.graph.Path r x) = T.path r x :=
      T.path_unique _
    have hyAt : P.getVert ly = y := P.getVert_length_takeUntil hyP
    have hqAt : q.getVert ly = P.getVert ly := P.getVert_takeUntil hxP hyx
    have hyq : y ∈ q.support := by
      rw [← hyAt, ← hqAt]
      exact q.getVert_mem_support ly
    have hyrx : y ∈ (T.path r x).1.support := by
      rw [← congrArg (fun p => p.1.support) hqeq]
      exact hyq
    exact Or.inr ((mem_pathSupport_comm T).mpr hyrx)

def gateComponentVertex
    (T : PosIntTree n) {C : EvenComponent T}
    (root u v : ComponentVertex T C)
    (G : StrongRootGate T root.1 u.1 v.1) : ComponentVertex T C :=
  ⟨G.gate, by
    have hcomp : componentOf T u.1 = componentOf T root.1 :=
      u.2.trans root.2.symm
    exact (componentOf_eq_of_path_all_even T fun e he =>
      path_edge_even_of_component_eq T hcomp
        (LeechTrees.OddEdges.T11Adapter.pathEdges_suffix_subset
          T G.gate_mem_u he)).trans root.2⟩

@[simp] theorem gateComponentVertex_val
    (T : PosIntTree n) {C : EvenComponent T}
    (root u v : ComponentVertex T C)
    (G : StrongRootGate T root.1 u.1 v.1) :
    (gateComponentVertex T root u v G).1 = G.gate := rfl

/-- The strong actual gate identity after dividing all internal even
distances by two. -/
theorem strongRootGate_rho_identity
    (T : PosIntTree n) {C : EvenComponent T}
    (root u v : ComponentVertex T C)
    (G : StrongRootGate T root.1 u.1 v.1) :
    rho T u v + 2 * rho T (gateComponentVertex T root u v G) root =
      rho T u root + rho T v root := by
  have huv := dist_eq_two_mul_rho T u v
  have hur := dist_eq_two_mul_rho T u root
  have hvr := dist_eq_two_mul_rho T v root
  have hgr := dist_eq_two_mul_rho T
    (gateComponentVertex T root u v G) root
  change T.dist G.gate root.1 =
      2 * rho T (gateComponentVertex T root u v G) root at hgr
  have hgate := G.distance_eq
  omega

theorem rootedGate_eq_of_depth
    (T : PosIntTree n) {C : EvenComponent T}
    (root u v a : ComponentVertex T C)
    (hdepth : Function.Injective (fun x : ComponentVertex T C =>
      rho T x root))
    (G : StrongRootGate T root.1 u.1 v.1)
    (h : rho T (gateComponentVertex T root u v G) root =
      rho T a root) :
    gateComponentVertex T root u v G = a :=
  hdepth h

/-- Equality with the rooted depth difference is the actual ancestor
relation, not merely an arithmetic coincidence. -/
theorem rootedRho_mem_path_of_sub
    (T : PosIntTree n) {C : EvenComponent T}
    (root a b : ComponentVertex T C)
    (hdepth : Function.Injective (fun x : ComponentVertex T C =>
      rho T x root))
    (_hapos : 0 < rho T a root)
    (hale : rho T a root ≤ rho T b root)
    (hab : rho T a b = rho T b root - rho T a root) :
    a.1 ∈ (T.path b.1 root.1).1.support := by
  let G := strongRootGate T root.1 a.1 b.1
  let z := gateComponentVertex T root a b G
  have hz : rho T z root = rho T a root := by
    have hgate := strongRootGate_rho_identity T root a b G
    change rho T a b + 2 * rho T z root =
      rho T a root + rho T b root at hgate
    rw [hab] at hgate
    omega
  have hza : z = a := hdepth hz
  have hval : G.gate = a.1 := by
    exact (gateComponentVertex_val T root a b G).symm.trans
      (congrArg Subtype.val hza)
  simpa [hval] using G.gate_mem_v

/-- Halved internal distance splits at an actual vertex on a rooted path. -/
theorem rootedRho_split_at_path_vertex
    (T : PosIntTree n) {C : EvenComponent T}
    (root x z : ComponentVertex T C)
    (hz : z.1 ∈ (T.path x.1 root.1).1.support) :
    rho T x root = rho T x z + rho T z root := by
  have hsplit :=
    LeechTrees.OddEdges.T11Adapter.PosIntTree.dist_split_at_path_vertex T hz
  have hxr := dist_eq_two_mul_rho T x root
  have hxz := dist_eq_two_mul_rho T x z
  have hzr := dist_eq_two_mul_rho T z root
  omega

/-- If two rooted branches meet only at depth zero, their actual rooted
paths have no other common vertex. -/
theorem rootedPaths_common_eq_root_of_add
    (T : PosIntTree n) {C : EvenComponent T}
    (root a b : ComponentVertex T C)
    (hdepth : Function.Injective (fun x : ComponentVertex T C =>
      rho T x root))
    (hab : rho T a b = rho T a root + rho T b root)
    {x : ComponentVertex T C}
    (hxa : x.1 ∈ (T.path a.1 root.1).1.support)
    (hxb : x.1 ∈ (T.path b.1 root.1).1.support) :
    x = root := by
  let G := strongRootGate T root.1 a.1 b.1
  let z := gateComponentVertex T root a b G
  have hz0 : rho T z root = 0 := by
    have hgate := strongRootGate_rho_identity T root a b G
    change rho T a b + 2 * rho T z root =
      rho T a root + rho T b root at hgate
    rw [hab] at hgate
    omega
  have hzroot : z = root := by
    apply hdepth
    change rho T z root = rho T root root
    exact hz0.trans (rho_self T root).symm
  have hgateRoot : G.gate = root.1 := by
    exact (gateComponentVertex_val T root a b G).symm.trans
      (congrArg Subtype.val hzroot)
  apply Subtype.ext
  exact G.common_eq_root hgateRoot hxa hxb

/-- The exact rooted-tree fork used by G015, derived from actual path
containment rather than assumed as a generic four-point axiom. -/
theorem rootedRho_fork
    (T : PosIntTree n) {C : EvenComponent T}
    (root a b c : ComponentVertex T C)
    (hdepth : Function.Injective (fun x : ComponentVertex T C =>
      rho T x root))
    (hapos : 0 < rho T a root)
    (hale : rho T a root ≤ rho T b root)
    (hab : rho T a b = rho T b root - rho T a root)
    (hac : rho T a c = rho T a root + rho T c root) :
    rho T b c = rho T b root + rho T c root := by
  let Gab := strongRootGate T root.1 a.1 b.1
  let zab := gateComponentVertex T root a b Gab
  have hzab : rho T zab root = rho T a root := by
    have hgate := Gab.distance_eq
    have hdab := dist_eq_two_mul_rho T a b
    have hdar := dist_eq_two_mul_rho T a root
    have hdbr := dist_eq_two_mul_rho T b root
    have hdzr := dist_eq_two_mul_rho T zab root
    change T.dist Gab.gate root.1 = 2 * rho T zab root at hdzr
    rw [hdab, hdar, hdbr, hdzr, hab] at hgate
    omega
  have hzab_eq : zab = a := hdepth hzab
  have ha_mem_b : a.1 ∈ (T.path b.1 root.1).1.support := by
    have hval : Gab.gate = a.1 := congrArg Subtype.val hzab_eq
    have hmem := Gab.gate_mem_v
    rw [hval] at hmem
    exact hmem

  let Gac := strongRootGate T root.1 a.1 c.1
  let zac := gateComponentVertex T root a c Gac
  have hzac : rho T zac root = 0 := by
    have hgate := Gac.distance_eq
    have hdac := dist_eq_two_mul_rho T a c
    have hdar := dist_eq_two_mul_rho T a root
    have hdcr := dist_eq_two_mul_rho T c root
    have hdzr := dist_eq_two_mul_rho T zac root
    change T.dist Gac.gate root.1 = 2 * rho T zac root at hdzr
    rw [hdac, hdar, hdcr, hdzr, hac] at hgate
    omega
  have hrootzero : rho T root root = 0 := rho_self T root
  have hzac_eq : zac = root := hdepth (hzac.trans hrootzero.symm)
  have hgac_root : Gac.gate = root.1 := congrArg Subtype.val hzac_eq

  let Gbc := strongRootGate T root.1 b.1 c.1
  have hgbc_root : Gbc.gate = root.1 := by
    rcases pathSupport_comparable T ha_mem_b Gbc.gate_mem_u with
      ha_suffix | hg_suffix
    · have ha_mem_c : a.1 ∈ (T.path c.1 root.1).1.support :=
        pathSupport_suffix_subset T Gbc.gate_mem_v ha_suffix
      have haroot : a.1 = root.1 :=
        Gac.common_eq_root hgac_root
          (T.path a.1 root.1).1.start_mem_support ha_mem_c
      have haeq : a = root := Subtype.ext haroot
      have hazero : rho T a root = 0 := by
        rw [haeq, rho_self]
      omega
    · exact Gac.common_eq_root hgac_root hg_suffix Gbc.gate_mem_v
  let zbc := gateComponentVertex T root b c Gbc
  have hzbc_eq : zbc = root := by
    apply Subtype.ext
    exact hgbc_root
  have hgate := Gbc.distance_eq
  have hdbc := dist_eq_two_mul_rho T b c
  have hdbr := dist_eq_two_mul_rho T b root
  have hdcr := dist_eq_two_mul_rho T c root
  have hdzr := dist_eq_two_mul_rho T zbc root
  change T.dist Gbc.gate root.1 = 2 * rho T zbc root at hdzr
  rw [hdbc, hdbr, hdcr, hdzr, hzbc_eq, rho_self] at hgate
  omega

/-- All rooted half-depths in one actual even component. -/
noncomputable def rootedDepthSupport
    (T : PosIntTree n) {C : EvenComponent T}
    (root : ComponentVertex T C) : Finset ℕ :=
  Finset.univ.image (fun x : ComponentVertex T C => rho T x root)

noncomputable def vertexAtDepth
    (T : PosIntTree n) {C : EvenComponent T}
    (root : ComponentVertex T C) (a : ℕ) : ComponentVertex T C :=
  if h : ∃ x : ComponentVertex T C, rho T x root = a then
    Classical.choose h
  else root

theorem vertexAtDepth_spec
    (T : PosIntTree n) {C : EvenComponent T}
    (root : ComponentVertex T C) {a : ℕ}
    (ha : a ∈ rootedDepthSupport T root) :
    rho T (vertexAtDepth T root a) root = a := by
  have hex : ∃ x : ComponentVertex T C, rho T x root = a := by
    rw [rootedDepthSupport, Finset.mem_image] at ha
    obtain ⟨x, _, hx⟩ := ha
    exact ⟨x, hx⟩
  simp only [vertexAtDepth, dif_pos hex]
  exact Classical.choose_spec hex

/-- Convert one actual rooted component into the abstract support metric.
Depth injectivity is supplied below from the unit-edge rooted direct sum. -/
noncomputable def rootedComponentMetric
    (T : PosIntTree n) {C : EvenComponent T}
    (root : ComponentVertex T C)
    (hdepth : Function.Injective (fun x : ComponentVertex T C =>
      rho T x root)) : RootedSupportMetric where
  support := rootedDepthSupport T root
  zero_mem := by
    rw [rootedDepthSupport, Finset.mem_image]
    exact ⟨root, Finset.mem_univ _, rho_self T root⟩
  dist a b := rho T (vertexAtDepth T root a) (vertexAtDepth T root b)
  dist_zero_left := by
    intro a ha
    have h0 : vertexAtDepth T root 0 = root := by
      apply hdepth
      change rho T (vertexAtDepth T root 0) root = rho T root root
      rw [vertexAtDepth_spec T root (by
        rw [rootedDepthSupport, Finset.mem_image]
        exact ⟨root, Finset.mem_univ _, rho_self T root⟩), rho_self]
    rw [h0, rho_comm]
    exact vertexAtDepth_spec T root ha
  dist_comm := by
    intro a b _ _
    exact rho_comm T _ _
  gate := by
    intro a b ha hb
    let u := vertexAtDepth T root a
    let v := vertexAtDepth T root b
    let G := strongRootGate T root.1 u.1 v.1
    let z := gateComponentVertex T root u v G
    have hzmem : rho T z root ∈ rootedDepthSupport T root := by
      rw [rootedDepthSupport, Finset.mem_image]
      exact ⟨z, Finset.mem_univ _, rfl⟩
    refine ⟨rho T z root, hzmem, ?_, ?_, ?_⟩
    · have hsplit := rootedRho_split_at_path_vertex T root u z (by
        exact G.gate_mem_u)
      rw [vertexAtDepth_spec T root ha] at hsplit
      omega
    · have hsplit := rootedRho_split_at_path_vertex T root v z (by
        exact G.gate_mem_v)
      rw [vertexAtDepth_spec T root hb] at hsplit
      omega
    · have hgate := strongRootGate_rho_identity T root u v G
      change rho T u v + 2 * rho T z root =
        rho T u root + rho T v root at hgate
      simpa [u, v, vertexAtDepth_spec T root ha,
        vertexAtDepth_spec T root hb] using hgate
  fork := by
    intro a b c ha hb hc hapos hale hab hac
    let va := vertexAtDepth T root a
    let vb := vertexAtDepth T root b
    let vc := vertexAtDepth T root c
    have hfork := rootedRho_fork T root va vb vc hdepth
      (by simpa [va, vertexAtDepth_spec T root ha] using hapos)
      (by simpa [va, vb, vertexAtDepth_spec T root ha,
          vertexAtDepth_spec T root hb] using hale)
      (by simpa [va, vb, vertexAtDepth_spec T root ha,
          vertexAtDepth_spec T root hb] using hab)
      (by simpa [va, vc, vertexAtDepth_spec T root ha,
          vertexAtDepth_spec T root hc] using hac)
    simpa [vb, vc, vertexAtDepth_spec T root hb,
      vertexAtDepth_spec T root hc] using hfork

/-! ## The unit-rectangle to prefix-factor adapter -/

def unitOddBridge {T : PosIntTree n} (W : GraphTwoOddWeights T) :
    OddBridge T :=
  ⟨W.unit, by simp [W.unit_weight]⟩

/-- `Q2Bounds` data specialized to the two named actual odd edges.  Under
`odd_iff`, every non-unit odd bridge is literally `second`, so the lower
bound in this record is an equality. -/
def graphSecondOddBridgeData
    {T : PosIntTree n} (hL : IsLeech T) (W : GraphTwoOddWeights T) :
    SecondOddBridgeData T where
  unit := unitOddBridge W
  q₂ := 2 * W.q + 1
  t := W.q
  q₂_eq := rfl
  t_pos := W.q_pos
  unit_weight := W.unit_weight
  other_weight_lower := by
    intro e hne
    rcases (W.odd_iff e.1).mp e.2 with he | he
    · exact (hne (Subtype.ext he)).elim
    · rw [he, W.second_weight]
  q₂_le_target := by
    have hmem := t1_edge_weight_mem_target hL W.second
    rw [W.second_weight] at hmem
    exact (Finset.mem_Icc.mp hmem).2

abbrev GraphUnitLeftVertex
    {T : PosIntTree n} (hL : IsLeech T) (W : GraphTwoOddWeights T) :=
  UnitLeftComponentVertex (graphSecondOddBridgeData hL W)

abbrev GraphUnitRightVertex
    {T : PosIntTree n} (hL : IsLeech T) (W : GraphTwoOddWeights T) :=
  UnitRightComponentVertex (graphSecondOddBridgeData hL W)

def graphUnitLeftRoot
    {T : PosIntTree n} (hL : IsLeech T) (W : GraphTwoOddWeights T) :
    GraphUnitLeftVertex hL W :=
  ⟨T.edgeLeft W.unit, rfl⟩

def graphUnitRightRoot
    {T : PosIntTree n} (hL : IsLeech T) (W : GraphTwoOddWeights T) :
    GraphUnitRightVertex hL W :=
  ⟨T.edgeRight W.unit, rfl⟩

/-- A vertex of the even component incident on the left is in the actual
left deletion side of the unit edge. -/
def graphUnitLeftCutVertex
    {T : PosIntTree n} (hL : IsLeech T) (W : GraphTwoOddWeights T)
    (x : GraphUnitLeftVertex hL W) : T.LeftVertex W.unit :=
  ⟨x.1, by
    unfold PosIntTree.LeftCut
    rw [T.cut_reachable_iff_not_mem_pathEdges]
    intro hmem
    have heven := path_edge_even_of_component_eq T x.2 hmem
    have hunitEven : Even (T.weight W.unit) := by simpa using heven
    exact (Nat.not_odd_iff_even.mpr hunitEven) (by
      simp [W.unit_weight])⟩

/-- Right-hand analogue of `graphUnitLeftCutVertex`. -/
def graphUnitRightCutVertex
    {T : PosIntTree n} (hL : IsLeech T) (W : GraphTwoOddWeights T)
    (x : GraphUnitRightVertex hL W) : T.RightVertex W.unit :=
  ⟨x.1, by
    unfold PosIntTree.RightCut
    rw [T.cut_reachable_iff_not_mem_pathEdges]
    intro hmem
    have heven := path_edge_even_of_component_eq T x.2 hmem
    have hunitEven : Even (T.weight W.unit) := by simpa using heven
    exact (Nat.not_odd_iff_even.mpr hunitEven) (by
      simp [W.unit_weight])⟩

theorem graphUnitLeftDepth_injective
    {T : PosIntTree n} (hL : IsLeech T) (W : GraphTwoOddWeights T) :
    Function.Injective (fun x : GraphUnitLeftVertex hL W =>
      rho T x (graphUnitLeftRoot hL W)) := by
  intro x y hxy
  apply Subtype.ext
  have hcut : graphUnitLeftCutVertex hL W x =
      graphUnitLeftCutVertex hL W y :=
    T.leftDepth_injective hL W.unit (by
      change T.dist x.1 (T.edgeLeft W.unit) =
        T.dist y.1 (T.edgeLeft W.unit)
      have hx := dist_eq_two_mul_rho T x (graphUnitLeftRoot hL W)
      have hy := dist_eq_two_mul_rho T y (graphUnitLeftRoot hL W)
      change T.dist x.1 (T.edgeLeft W.unit) = 2 *
        rho T x (graphUnitLeftRoot hL W) at hx
      change T.dist y.1 (T.edgeLeft W.unit) = 2 *
        rho T y (graphUnitLeftRoot hL W) at hy
      change rho T x (graphUnitLeftRoot hL W) =
        rho T y (graphUnitLeftRoot hL W) at hxy
      omega)
  exact congrArg (fun z : T.LeftVertex W.unit => z.1) hcut

theorem graphUnitRightDepth_injective
    {T : PosIntTree n} (hL : IsLeech T) (W : GraphTwoOddWeights T) :
    Function.Injective (fun x : GraphUnitRightVertex hL W =>
      rho T x (graphUnitRightRoot hL W)) := by
  intro x y hxy
  apply Subtype.ext
  have hcut : graphUnitRightCutVertex hL W x =
      graphUnitRightCutVertex hL W y :=
    T.rightDepth_injective hL W.unit (by
      change T.dist (T.edgeRight W.unit) x.1 =
        T.dist (T.edgeRight W.unit) y.1
      have hx := dist_eq_two_mul_rho T x (graphUnitRightRoot hL W)
      have hy := dist_eq_two_mul_rho T y (graphUnitRightRoot hL W)
      change T.dist x.1 (T.edgeRight W.unit) = 2 *
        rho T x (graphUnitRightRoot hL W) at hx
      change T.dist y.1 (T.edgeRight W.unit) = 2 *
        rho T y (graphUnitRightRoot hL W) at hy
      change rho T x (graphUnitRightRoot hL W) =
        rho T y (graphUnitRightRoot hL W) at hxy
      rw [T.dist_comm x.1 (T.edgeRight W.unit)] at hx
      rw [T.dist_comm y.1 (T.edgeRight W.unit)] at hy
      calc
        T.dist (T.edgeRight W.unit) x.1 =
            2 * rho T x (graphUnitRightRoot hL W) := hx
        _ = 2 * rho T y (graphUnitRightRoot hL W) :=
          congrArg (fun z => 2 * z) hxy
        _ = T.dist (T.edgeRight W.unit) y.1 := hy.symm)
  exact congrArg (fun z : T.RightVertex W.unit => z.1) hcut

private theorem vertexPair_ofDistinct_sym2
    {u v : Fin n} (huv : u ≠ v) :
    s((VertexPair.ofDistinct u v huv).left,
      (VertexPair.ofDistinct u v huv).right) = s(u, v) := by
  by_cases h : u < v
  · simp [VertexPair.ofDistinct, h, VertexPair.left, VertexPair.right]
  · simp [VertexPair.ofDistinct, h, VertexPair.left, VertexPair.right,
      Sym2.eq_swap]

private theorem pathEdges_ofDistinct
    (T : PosIntTree n) {u v : Fin n} (huv : u ≠ v) :
    T.pathEdges (VertexPair.ofDistinct u v huv).left
      (VertexPair.ofDistinct u v huv).right = T.pathEdges u v := by
  by_cases h : u < v
  · simp [VertexPair.ofDistinct, h, VertexPair.left, VertexPair.right]
  · simp [VertexPair.ofDistinct, h, VertexPair.left, VertexPair.right,
      T.pathEdges_comm]

/-- Equality of actual internal half-distances in one component is equality
of the corresponding unordered depth labels. -/
theorem rootedMetric_internal_injective
    (T : PosIntTree n) (hL : IsLeech T) {C : EvenComponent T}
    (root : ComponentVertex T C)
    {a b c d : ℕ}
    (ha : a ∈ rootedDepthSupport T root)
    (hb : b ∈ rootedDepthSupport T root)
    (hc : c ∈ rootedDepthSupport T root)
    (hd : d ∈ rootedDepthSupport T root)
    (hab : a ≠ b) (hcd : c ≠ d)
    (heq : rho T (vertexAtDepth T root a) (vertexAtDepth T root b) =
      rho T (vertexAtDepth T root c) (vertexAtDepth T root d)) :
    s(a, b) = s(c, d) := by
  let xa := vertexAtDepth T root a
  let xb := vertexAtDepth T root b
  let xc := vertexAtDepth T root c
  let xd := vertexAtDepth T root d
  have hxab : xa.1 ≠ xb.1 := by
    intro h
    apply hab
    have hsub : xa = xb := Subtype.ext h
    calc
      a = rho T xa root := (vertexAtDepth_spec T root ha).symm
      _ = rho T xb root := by rw [hsub]
      _ = b := vertexAtDepth_spec T root hb
  have hxcd : xc.1 ≠ xd.1 := by
    intro h
    apply hcd
    have hsub : xc = xd := Subtype.ext h
    calc
      c = rho T xc root := (vertexAtDepth_spec T root hc).symm
      _ = rho T xd root := by rw [hsub]
      _ = d := vertexAtDepth_spec T root hd
  let p := VertexPair.ofDistinct xa.1 xb.1 hxab
  let q := VertexPair.ofDistinct xc.1 xd.1 hxcd
  have hpdist : T.pairDist p = T.pairDist q := by
    dsimp only [p, q]
    rw [T.pairDist_pairOfDistinct, T.pairDist_pairOfDistinct]
    have hp := dist_eq_two_mul_rho T xa xb
    have hq := dist_eq_two_mul_rho T xc xd
    exact hp.trans ((congrArg (fun z => 2 * z) heq).trans hq.symm)
  have hpq : p = q := hL.pairDist_injective hpdist
  have hs : s(xa.1, xb.1) = s(xc.1, xd.1) := by
    have := congrArg (fun z : VertexPair n => s(z.left, z.right)) hpq
    simpa [p, q, vertexPair_ofDistinct_sym2] using this
  rcases Sym2.eq_iff.mp hs with h | h
  · apply Sym2.eq_iff.mpr
    exact Or.inl ⟨by
      calc
        a = rho T xa root := (vertexAtDepth_spec T root ha).symm
        _ = rho T xc root := by rw [Subtype.ext h.1]
        _ = c := vertexAtDepth_spec T root hc, by
      calc
        b = rho T xb root := (vertexAtDepth_spec T root hb).symm
        _ = rho T xd root := by rw [Subtype.ext h.2]
        _ = d := vertexAtDepth_spec T root hd⟩
  · apply Sym2.eq_iff.mpr
    exact Or.inr ⟨by
      calc
        a = rho T xa root := (vertexAtDepth_spec T root ha).symm
        _ = rho T xd root := by rw [Subtype.ext h.1]
        _ = d := vertexAtDepth_spec T root hd, by
      calc
        b = rho T xb root := (vertexAtDepth_spec T root hb).symm
        _ = rho T xc root := by rw [Subtype.ext h.2]
        _ = c := vertexAtDepth_spec T root hc⟩

/-- The two incident even components have disjoint nonzero internal
half-distance spectra, because equality would identify a global pair across
the two distinct components. -/
private theorem unitComponents_internal_disjoint
    {T : PosIntTree n} (hL : IsLeech T) (W : GraphTwoOddWeights T)
    {a b c d : ℕ}
    (ha : a ∈ rootedDepthSupport T (graphUnitLeftRoot hL W))
    (hb : b ∈ rootedDepthSupport T (graphUnitLeftRoot hL W))
    (hc : c ∈ rootedDepthSupport T (graphUnitRightRoot hL W))
    (hd : d ∈ rootedDepthSupport T (graphUnitRightRoot hL W))
    (hab : a ≠ b) (hcd : c ≠ d) :
    rho T
        (vertexAtDepth T (graphUnitLeftRoot hL W) a)
        (vertexAtDepth T (graphUnitLeftRoot hL W) b) ≠
      rho T
        (vertexAtDepth T (graphUnitRightRoot hL W) c)
        (vertexAtDepth T (graphUnitRightRoot hL W) d) := by
  intro heq
  let xa := vertexAtDepth T (graphUnitLeftRoot hL W) a
  let xb := vertexAtDepth T (graphUnitLeftRoot hL W) b
  let xc := vertexAtDepth T (graphUnitRightRoot hL W) c
  let xd := vertexAtDepth T (graphUnitRightRoot hL W) d
  have hxab : xa.1 ≠ xb.1 := by
    intro h
    apply hab
    have hsub : xa = xb := Subtype.ext h
    calc
      a = rho T xa (graphUnitLeftRoot hL W) :=
        (vertexAtDepth_spec T (graphUnitLeftRoot hL W) ha).symm
      _ = rho T xb (graphUnitLeftRoot hL W) := by rw [hsub]
      _ = b := vertexAtDepth_spec T (graphUnitLeftRoot hL W) hb
  have hxcd : xc.1 ≠ xd.1 := by
    intro h
    apply hcd
    have hsub : xc = xd := Subtype.ext h
    calc
      c = rho T xc (graphUnitRightRoot hL W) :=
        (vertexAtDepth_spec T (graphUnitRightRoot hL W) hc).symm
      _ = rho T xd (graphUnitRightRoot hL W) := by rw [hsub]
      _ = d := vertexAtDepth_spec T (graphUnitRightRoot hL W) hd
  let p := VertexPair.ofDistinct xa.1 xb.1 hxab
  let q := VertexPair.ofDistinct xc.1 xd.1 hxcd
  have hpdist : T.pairDist p = T.pairDist q := by
    dsimp only [p, q]
    rw [T.pairDist_pairOfDistinct, T.pairDist_pairOfDistinct]
    have hp := dist_eq_two_mul_rho T xa xb
    have hq := dist_eq_two_mul_rho T xc xd
    exact hp.trans ((congrArg (fun z => 2 * z) heq).trans hq.symm)
  have hpq : p = q := hL.pairDist_injective hpdist
  have hs : s(xa.1, xb.1) = s(xc.1, xd.1) := by
    have := congrArg (fun z : VertexPair n => s(z.left, z.right)) hpq
    simpa [p, q, vertexPair_ofDistinct_sym2] using this
  rcases Sym2.eq_iff.mp hs with h | h
  · apply oddBridge_components_ne T (unitOddBridge W)
    calc
      componentOf T (T.edgeLeft W.unit) = componentOf T xa.1 := xa.2.symm
      _ = componentOf T xc.1 := congrArg (componentOf T) h.1
      _ = componentOf T (T.edgeRight W.unit) := xc.2
  · apply oddBridge_components_ne T (unitOddBridge W)
    calc
      componentOf T (T.edgeLeft W.unit) = componentOf T xa.1 := xa.2.symm
      _ = componentOf T xd.1 := congrArg (componentOf T) h.1
      _ = componentOf T (T.edgeRight W.unit) := xd.2

/-- The promised source-only quotient/unit-rectangle adapter.  Its support
fields are actual component vertices; no coefficient or collision hypothesis
is assumed. -/
noncomputable def prefixFactorDataOfGraph
    {T : PosIntTree n} (hL : IsLeech T) (W : GraphTwoOddWeights T) :
    PrefixFactorData W.q := by
  let D := graphSecondOddBridgeData hL W
  let rL := graphUnitLeftRoot hL W
  let rR := graphUnitRightRoot hL W
  let hLdepth := graphUnitLeftDepth_injective hL W
  let hRdepth := graphUnitRightDepth_injective hL W
  let P := rootedComponentMetric T rL hLdepth
  let Q := rootedComponentMetric T rR hRdepth
  refine {
    P := P
    Q := Q
    direct := ?_
    coversBelow := ?_
    omitsQ := ?_
    P_internal_injective := ?_
    Q_internal_injective := ?_
    internal_disjoint := ?_ }
  · intro a b a' b' ha hb ha' hb' hsum
    let x := vertexAtDepth T rL a
    let y := vertexAtDepth T rR b
    let x' := vertexAtDepth T rL a'
    let y' := vertexAtDepth T rR b'
    let z : T.LeftVertex W.unit × T.RightVertex W.unit :=
      (graphUnitLeftCutVertex hL W x, graphUnitRightCutVertex hL W y)
    let z' : T.LeftVertex W.unit × T.RightVertex W.unit :=
      (graphUnitLeftCutVertex hL W x', graphUnitRightCutVertex hL W y')
    have hrooted : T.rootedCrossSum W.unit z =
        T.rootedCrossSum W.unit z' := by
      have hxa := dist_eq_two_mul_rho T x rL
      have hyb := dist_eq_two_mul_rho T y rR
      have hxa' := dist_eq_two_mul_rho T x' rL
      have hyb' := dist_eq_two_mul_rho T y' rR
      change T.dist x.1 (T.edgeLeft W.unit) = 2 * rho T x rL at hxa
      change T.dist y.1 (T.edgeRight W.unit) = 2 * rho T y rR at hyb
      change T.dist x'.1 (T.edgeLeft W.unit) = 2 * rho T x' rL at hxa'
      change T.dist y'.1 (T.edgeRight W.unit) = 2 * rho T y' rR at hyb'
      rw [T.dist_comm y.1 (T.edgeRight W.unit)] at hyb
      rw [T.dist_comm y'.1 (T.edgeRight W.unit)] at hyb'
      change T.dist x.1 (T.edgeLeft W.unit) + T.weight W.unit +
          T.dist (T.edgeRight W.unit) y.1 =
        T.dist x'.1 (T.edgeLeft W.unit) + T.weight W.unit +
          T.dist (T.edgeRight W.unit) y'.1
      rw [hxa, hyb, hxa', hyb',
        vertexAtDepth_spec T rL ha, vertexAtDepth_spec T rR hb,
        vertexAtDepth_spec T rL ha', vertexAtDepth_spec T rR hb']
      omega
    have hzz := T.rootedCrossSum_injective hL W.unit hrooted
    have hxx : x = x' := Subtype.ext
      (congrArg (fun z : T.LeftVertex W.unit => z.1)
        (congrArg Prod.fst hzz))
    have hyy : y = y' := Subtype.ext
      (congrArg (fun z : T.RightVertex W.unit => z.1)
        (congrArg Prod.snd hzz))
    constructor
    · calc
        a = rho T x rL := (vertexAtDepth_spec T rL ha).symm
        _ = rho T x' rL := by rw [hxx]
        _ = a' := vertexAtDepth_spec T rL ha'
    · calc
        b = rho T y rR := (vertexAtDepth_spec T rR hb).symm
        _ = rho T y' rR := by rw [hyy]
        _ = b' := vertexAtDepth_spec T rR hb'
  · intro k hk
    let i : Fin D.t := ⟨k, by simpa [D] using hk⟩
    let z := lowOddUnitRectanglePoint hL D i
    let a := rho T z.1 rL
    let b := rho T z.2 rR
    have ha : a ∈ P.support := by
      change a ∈ rootedDepthSupport T rL
      rw [rootedDepthSupport, Finset.mem_image]
      exact ⟨z.1, Finset.mem_univ _, rfl⟩
    have hb : b ∈ Q.support := by
      change b ∈ rootedDepthSupport T rR
      rw [rootedDepthSupport, Finset.mem_image]
      exact ⟨z.2, Finset.mem_univ _, rfl⟩
    refine ⟨a, ha, b, hb, ?_⟩
    have hcross := T.cross_distance_decomposition W.unit
      (graphUnitLeftCutVertex hL W z.1).2
      (graphUnitRightCutVertex hL W z.2).2
    have hleft := dist_eq_two_mul_rho T z.1 rL
    have hright := dist_eq_two_mul_rho T z.2 rR
    change T.dist z.1.1 (T.edgeLeft W.unit) = 2 * rho T z.1 rL at hleft
    change T.dist z.2.1 (T.edgeRight W.unit) = 2 * rho T z.2 rR at hright
    rw [T.dist_comm z.2.1 (T.edgeRight W.unit)] at hright
    have hpair : T.pairDist (unitRectanglePair D z) =
        T.dist z.1.1 z.2.1 := by
      rw [unitRectanglePair, T.pairDist_pairOfDistinct]
    have hlow := lowOddPair_dist hL D i
    rw [lowOddUnitRectanglePoint_spec hL D i] at hpair
    rw [hlow] at hpair
    change T.dist z.1.1 z.2.1 =
      T.dist z.1.1 (T.edgeLeft W.unit) + T.weight W.unit +
        T.dist (T.edgeRight W.unit) z.2.1 at hcross
    rw [hleft, hright, W.unit_weight] at hcross
    dsimp only [a, b, i] at hpair hcross ⊢
    omega
  · intro a b ha hb hsum
    let x := vertexAtDepth T rL a
    let y := vertexAtDepth T rR b
    let z : GraphUnitLeftVertex hL W × GraphUnitRightVertex hL W := (x, y)
    have hcross := T.cross_distance_decomposition W.unit
      (graphUnitLeftCutVertex hL W x).2
      (graphUnitRightCutVertex hL W y).2
    have hleft := dist_eq_two_mul_rho T x rL
    have hright := dist_eq_two_mul_rho T y rR
    change T.dist x.1 (T.edgeLeft W.unit) = 2 * rho T x rL at hleft
    change T.dist y.1 (T.edgeRight W.unit) = 2 * rho T y rR at hright
    rw [T.dist_comm y.1 (T.edgeRight W.unit)] at hright
    have hrect : T.pairDist (unitRectanglePair D z) = 2 * W.q + 1 := by
      have hp : T.pairDist (unitRectanglePair D z) = T.dist x.1 y.1 := by
        rw [unitRectanglePair, T.pairDist_pairOfDistinct]
      rw [hp]
      change T.dist x.1 y.1 =
        T.dist x.1 (T.edgeLeft W.unit) + T.weight W.unit +
          T.dist (T.edgeRight W.unit) y.1 at hcross
      rw [hcross, hleft, hright, W.unit_weight,
        vertexAtDepth_spec T rL ha, vertexAtDepth_spec T rR hb]
      omega
    have hedge : T.pairDist (T.edgePair W.second) = 2 * W.q + 1 := by
      rw [T.edgePair_dist, W.second_weight]
    have hpairs : unitRectanglePair D z = T.edgePair W.second :=
      hL.pairDist_injective (hrect.trans hedge.symm)
    have hunitRaw : W.unit.1 ∈ T.pathEdges x.1 y.1 :=
      (T.mem_pathEdges_iff_opposite_cuts W.unit x.1 y.1).2
        (Or.inl ⟨(graphUnitLeftCutVertex hL W x).2,
          (graphUnitRightCutVertex hL W y).2⟩)
    have hunitRect : W.unit.1 ∈
        T.pathEdges (unitRectanglePair D z).left
          (unitRectanglePair D z).right := by
      rw [unitRectanglePair, pathEdges_ofDistinct T]
      exact hunitRaw
    rw [hpairs, T.edgePair_left, T.edgePair_right,
      T.pathEdges_edge] at hunitRect
    apply W.ne
    exact Subtype.ext (Finset.mem_singleton.mp hunitRect)
  · intro a b c d ha hb hc hd hab hcd heq
    exact rootedMetric_internal_injective T hL rL
      ha hb hc hd hab hcd heq
  · intro a b c d ha hb hc hd hab hcd heq
    exact rootedMetric_internal_injective T hL rR
      ha hb hc hd hab hcd heq
  · intro a b c d ha hb hc hd hab hcd
    exact unitComponents_internal_disjoint hL W
      ha hb hc hd hab hcd

/-! ## Unconditional graph-facing endpoints -/

/-- The audited any-order bound for the actual second odd physical edge. -/
theorem graph_second_odd_q_le_ten
    {T : PosIntTree n} (hL : IsLeech T) (W : GraphTwoOddWeights T) :
    W.q ≤ 10 :=
  PrefixFactorData.q_le_ten (prefixFactorDataOfGraph hL W)

/-- The sharp common-port-compatible exclusion of `q=7`. -/
theorem graph_second_odd_q_ne_seven
    {T : PosIntTree n} (hL : IsLeech T) (W : GraphTwoOddWeights T) :
    W.q ≠ 7 :=
  PrefixFactorData.q_ne_seven (prefixFactorDataOfGraph hL W)

/-- Directly quantified actual-tree endpoint, with the two actual physical
edges and their exact weights retained in the witness. -/
theorem actual_two_odd_q_bounds
    (T : PosIntTree n) (hL : IsLeech T) (hn : 2 ≤ n)
    (hTwo : ExactlyTwoOddPhysicalEdges T) :
    ∃ W : GraphTwoOddWeights T, W.q ≤ 10 ∧ W.q ≠ 7 := by
  let W := Classical.choice (exists_graphTwoOddWeights T hL hn hTwo)
  exact ⟨W, graph_second_odd_q_le_ten hL W,
    graph_second_odd_q_ne_seven hL W⟩

/-! ## Actual linked ports for the distinct-port strengthening -/

/-- Two actual physical edges share an actual vertex. -/
def PhysicalEdgesSharePort
    (T : PosIntTree n) (e f : T.Edge) : Prop :=
  ∃ y : Fin n,
    (y = T.edgeLeft e ∨ y = T.edgeRight e) ∧
    (y = T.edgeLeft f ∨ y = T.edgeRight f)

/-- The audited distinct-middle-port hypothesis, stated without a quotient
label: the complete two-edge odd set has no common physical endpoint. -/
def DistinctMiddlePorts
    {T : PosIntTree n} (W : GraphTwoOddWeights T) : Prop :=
  ¬ PhysicalEdgesSharePort T W.unit W.second

/-- Orientation-free hypothesis for a tree whose actual odd physical edges
are pairwise endpoint-disjoint. -/
def OddPhysicalEdgesPairwisePortDisjoint (T : PosIntTree n) : Prop :=
  ∀ e f : T.Edge, Odd (T.weight e) → Odd (T.weight f) → e ≠ f →
    ¬ PhysicalEdgesSharePort T e f

theorem distinctMiddlePorts_of_pairwise
    {T : PosIntTree n} (W : GraphTwoOddWeights T)
    (h : OddPhysicalEdgesPairwisePortDisjoint T) :
    DistinctMiddlePorts W :=
  h W.unit W.second (by simp [W.unit_weight]) W.second_odd W.ne

private theorem otherEdge_endpoints_sameCut
    (T : PosIntTree n) {e f : T.Edge} (hne : e ≠ f) :
    (T.LeftCut e (T.edgeLeft f) ∧ T.LeftCut e (T.edgeRight f)) ∨
    (T.RightCut e (T.edgeLeft f) ∧ T.RightCut e (T.edgeRight f)) := by
  have havoid : e.1 ∉ T.pathEdges (T.edgeLeft f) (T.edgeRight f) := by
    rw [T.pathEdges_edge f]
    intro hmem
    apply hne
    exact Subtype.ext (Finset.mem_singleton.mp hmem)
  rcases T.cut_cover e (T.edgeLeft f) with hll | hlr <;>
    rcases T.cut_cover e (T.edgeRight f) with hrl | hrr
  · exact Or.inl ⟨hll, hrl⟩
  · exact (havoid ((T.mem_pathEdges_iff_opposite_cuts e _ _).2
      (Or.inl ⟨hll, hrr⟩))).elim
  · exact (havoid ((T.mem_pathEdges_iff_opposite_cuts e _ _).2
      (Or.inr ⟨hlr, hrl⟩))).elim
  · exact Or.inr ⟨hlr, hrr⟩

private theorem component_eq_of_avoids_twoOdd
    {T : PosIntTree n} (W : GraphTwoOddWeights T) {u v : Fin n}
    (hu : W.unit.1 ∉ T.pathEdges u v)
    (hs : W.second.1 ∉ T.pathEdges u v) :
    componentOf T u = componentOf T v := by
  apply componentOf_eq_of_path_all_even T
  intro e he
  rw [← Nat.not_odd_iff_even]
  intro hodd
  let g : T.Edge := T.edgeOfPathMem e he
  rcases (W.odd_iff g).mp (by simpa [g] using hodd) with hg | hg
  · apply hu
    have : e = W.unit.1 := by
      simpa [g] using congrArg Subtype.val hg
    simpa [this] using he
  · apply hs
    have : e = W.second.1 := by
      simpa [g] using congrArg Subtype.val hg
    simpa [this] using he

/-- The actual three-component orientation of the two named odd bridges.
Both oriented bridges retain their actual physical indices and ports. -/
structure TwoBridgeOrientation
    {T : PosIntTree n} (W : GraphTwoOddWeights T) where
  unitOuter : EvenComponent T
  middle : EvenComponent T
  secondOuter : EvenComponent T
  unitBridge : OrientedBridge T unitOuter middle
  secondBridge : OrientedBridge T middle secondOuter
  unitBridge_eq : unitBridge.bridge.1 = W.unit
  secondBridge_eq : secondBridge.bridge.1 = W.second
  ports_ne : unitBridge.targetPort ≠ secondBridge.sourcePort

/-- Construct the linked quotient path and its two distinct actual middle
ports.  This is the orientation lemma absent from the public quotient API;
the proof works directly with the two physical cuts. -/
theorem twoBridgeOrientation_nonempty
    {T : PosIntTree n} (W : GraphTwoOddWeights T)
    (hDistinct : DistinctMiddlePorts W) :
    Nonempty (TwoBridgeOrientation W) := by
  classical
  have hsame := otherEdge_endpoints_sameCut T W.ne
  rcases hsame with hsecondLeft | hsecondRight
  · let p := T.edgeLeft W.unit
    rcases T.cut_cover W.second p with hpLeft | hpRight
    · have hunitAvoid : W.unit.1 ∉
          T.pathEdges p (T.edgeLeft W.second) :=
        (T.cut_reachable_iff_not_mem_pathEdges W.unit _ _).1
          hsecondLeft.1.symm
      have hsecondAvoid : W.second.1 ∉
          T.pathEdges p (T.edgeLeft W.second) :=
        (T.cut_reachable_iff_not_mem_pathEdges W.second _ _).1 hpLeft
      have hmiddle : componentOf T (T.edgeLeft W.second) =
          componentOf T p :=
        (component_eq_of_avoids_twoOdd W hunitAvoid hsecondAvoid).symm
      let ub : OrientedBridge T
          (componentOf T (T.edgeRight W.unit)) (componentOf T p) := {
        bridge := unitOddBridge W
        sourcePortVertex := T.edgeRight W.unit
        targetPortVertex := p
        edge_eq_ports := by
          change W.unit.1 = s(T.edgeRight W.unit, p)
          rw [T.edge_eq_mk_endpoints, Sym2.eq_swap]
        source_component := rfl
        target_component := rfl
        component_pair := by
          rw [quotientEdgePair_eq]
          change s(componentOf T (T.edgeLeft W.unit),
            componentOf T (T.edgeRight W.unit)) =
            s(componentOf T (T.edgeRight W.unit), componentOf T p)
          rw [show p = T.edgeLeft W.unit from rfl, Sym2.eq_swap] }
      let sb : OrientedBridge T
          (componentOf T p) (componentOf T (T.edgeRight W.second)) := {
        bridge := ⟨W.second, W.second_odd⟩
        sourcePortVertex := T.edgeLeft W.second
        targetPortVertex := T.edgeRight W.second
        edge_eq_ports := T.edge_eq_mk_endpoints W.second
        source_component := hmiddle
        target_component := rfl
        component_pair := by
          rw [quotientEdgePair_eq, hmiddle] }
      refine ⟨{
        unitOuter := componentOf T (T.edgeRight W.unit)
        middle := componentOf T p
        secondOuter := componentOf T (T.edgeRight W.second)
        unitBridge := ub
        secondBridge := sb
        unitBridge_eq := rfl
        secondBridge_eq := rfl
        ports_ne := ?_ }⟩
      intro hports
      apply hDistinct
      refine ⟨p, Or.inl rfl, Or.inl ?_⟩
      exact congrArg Subtype.val hports
    · have hunitAvoid : W.unit.1 ∉
          T.pathEdges p (T.edgeRight W.second) :=
        (T.cut_reachable_iff_not_mem_pathEdges W.unit _ _).1
          hsecondLeft.2.symm
      have hsecondAvoid : W.second.1 ∉
          T.pathEdges p (T.edgeRight W.second) :=
        (T.cut_reachable_iff_not_mem_pathEdges W.second _ _).1 hpRight
      have hmiddle : componentOf T (T.edgeRight W.second) =
          componentOf T p :=
        (component_eq_of_avoids_twoOdd W hunitAvoid hsecondAvoid).symm
      let ub : OrientedBridge T
          (componentOf T (T.edgeRight W.unit)) (componentOf T p) := {
        bridge := unitOddBridge W
        sourcePortVertex := T.edgeRight W.unit
        targetPortVertex := p
        edge_eq_ports := by
          change W.unit.1 = s(T.edgeRight W.unit, p)
          rw [T.edge_eq_mk_endpoints, Sym2.eq_swap]
        source_component := rfl
        target_component := rfl
        component_pair := by
          rw [quotientEdgePair_eq]
          change s(componentOf T (T.edgeLeft W.unit),
            componentOf T (T.edgeRight W.unit)) =
            s(componentOf T (T.edgeRight W.unit), componentOf T p)
          rw [show p = T.edgeLeft W.unit from rfl, Sym2.eq_swap] }
      let sb : OrientedBridge T
          (componentOf T p) (componentOf T (T.edgeLeft W.second)) := {
        bridge := ⟨W.second, W.second_odd⟩
        sourcePortVertex := T.edgeRight W.second
        targetPortVertex := T.edgeLeft W.second
        edge_eq_ports := by
          rw [T.edge_eq_mk_endpoints, Sym2.eq_swap]
        source_component := hmiddle
        target_component := rfl
        component_pair := by
          rw [quotientEdgePair_eq, hmiddle]
          exact Sym2.eq_swap }
      refine ⟨{
        unitOuter := componentOf T (T.edgeRight W.unit)
        middle := componentOf T p
        secondOuter := componentOf T (T.edgeLeft W.second)
        unitBridge := ub
        secondBridge := sb
        unitBridge_eq := rfl
        secondBridge_eq := rfl
        ports_ne := ?_ }⟩
      intro hports
      apply hDistinct
      refine ⟨p, Or.inl rfl, Or.inr ?_⟩
      exact congrArg Subtype.val hports
  · let p := T.edgeRight W.unit
    rcases T.cut_cover W.second p with hpLeft | hpRight
    · have hunitAvoid : W.unit.1 ∉
          T.pathEdges p (T.edgeLeft W.second) :=
        (T.cut_reachable_iff_not_mem_pathEdges W.unit _ _).1
          hsecondRight.1.symm
      have hsecondAvoid : W.second.1 ∉
          T.pathEdges p (T.edgeLeft W.second) :=
        (T.cut_reachable_iff_not_mem_pathEdges W.second _ _).1 hpLeft
      have hmiddle : componentOf T (T.edgeLeft W.second) =
          componentOf T p :=
        (component_eq_of_avoids_twoOdd W hunitAvoid hsecondAvoid).symm
      let ub : OrientedBridge T
          (componentOf T (T.edgeLeft W.unit)) (componentOf T p) := {
        bridge := unitOddBridge W
        sourcePortVertex := T.edgeLeft W.unit
        targetPortVertex := p
        edge_eq_ports := T.edge_eq_mk_endpoints W.unit
        source_component := rfl
        target_component := rfl
        component_pair := by
          rw [quotientEdgePair_eq]
          change s(componentOf T (T.edgeLeft W.unit),
            componentOf T (T.edgeRight W.unit)) =
            s(componentOf T (T.edgeLeft W.unit), componentOf T p)
          rw [show p = T.edgeRight W.unit from rfl] }
      let sb : OrientedBridge T
          (componentOf T p) (componentOf T (T.edgeRight W.second)) := {
        bridge := ⟨W.second, W.second_odd⟩
        sourcePortVertex := T.edgeLeft W.second
        targetPortVertex := T.edgeRight W.second
        edge_eq_ports := T.edge_eq_mk_endpoints W.second
        source_component := hmiddle
        target_component := rfl
        component_pair := by
          rw [quotientEdgePair_eq, hmiddle] }
      refine ⟨{
        unitOuter := componentOf T (T.edgeLeft W.unit)
        middle := componentOf T p
        secondOuter := componentOf T (T.edgeRight W.second)
        unitBridge := ub
        secondBridge := sb
        unitBridge_eq := rfl
        secondBridge_eq := rfl
        ports_ne := ?_ }⟩
      intro hports
      apply hDistinct
      refine ⟨p, Or.inr rfl, Or.inl ?_⟩
      exact congrArg Subtype.val hports
    · have hunitAvoid : W.unit.1 ∉
          T.pathEdges p (T.edgeRight W.second) :=
        (T.cut_reachable_iff_not_mem_pathEdges W.unit _ _).1
          hsecondRight.2.symm
      have hsecondAvoid : W.second.1 ∉
          T.pathEdges p (T.edgeRight W.second) :=
        (T.cut_reachable_iff_not_mem_pathEdges W.second _ _).1 hpRight
      have hmiddle : componentOf T (T.edgeRight W.second) =
          componentOf T p :=
        (component_eq_of_avoids_twoOdd W hunitAvoid hsecondAvoid).symm
      let ub : OrientedBridge T
          (componentOf T (T.edgeLeft W.unit)) (componentOf T p) := {
        bridge := unitOddBridge W
        sourcePortVertex := T.edgeLeft W.unit
        targetPortVertex := p
        edge_eq_ports := T.edge_eq_mk_endpoints W.unit
        source_component := rfl
        target_component := rfl
        component_pair := by
          rw [quotientEdgePair_eq]
          change s(componentOf T (T.edgeLeft W.unit),
            componentOf T (T.edgeRight W.unit)) =
            s(componentOf T (T.edgeLeft W.unit), componentOf T p)
          rw [show p = T.edgeRight W.unit from rfl] }
      let sb : OrientedBridge T
          (componentOf T p) (componentOf T (T.edgeLeft W.second)) := {
        bridge := ⟨W.second, W.second_odd⟩
        sourcePortVertex := T.edgeRight W.second
        targetPortVertex := T.edgeLeft W.second
        edge_eq_ports := by
          rw [T.edge_eq_mk_endpoints, Sym2.eq_swap]
        source_component := hmiddle
        target_component := rfl
        component_pair := by
          rw [quotientEdgePair_eq, hmiddle]
          exact Sym2.eq_swap }
      refine ⟨{
        unitOuter := componentOf T (T.edgeLeft W.unit)
        middle := componentOf T p
        secondOuter := componentOf T (T.edgeLeft W.second)
        unitBridge := ub
        secondBridge := sb
        unitBridge_eq := rfl
        secondBridge_eq := rfl
        ports_ne := ?_ }⟩
      intro hports
      apply hDistinct
      refine ⟨p, Or.inr rfl, Or.inr ?_⟩
      exact congrArg Subtype.val hports

noncomputable def twoBridgeOrientation
    {T : PosIntTree n} (W : GraphTwoOddWeights T)
    (hDistinct : DistinctMiddlePorts W) : TwoBridgeOrientation W :=
  Classical.choice (twoBridgeOrientation_nonempty W hDistinct)

theorem TwoBridgeOrientation.unitOuter_ne_middle
    {T : PosIntTree n} {W : GraphTwoOddWeights T}
    (O : TwoBridgeOrientation W) : O.unitOuter ≠ O.middle := by
  intro h
  apply quotientEdgePair_not_isDiag T O.unitBridge.bridge
  rw [O.unitBridge.component_pair, h, Sym2.mk_isDiag_iff]

theorem TwoBridgeOrientation.middle_ne_secondOuter
    {T : PosIntTree n} {W : GraphTwoOddWeights T}
    (O : TwoBridgeOrientation W) : O.middle ≠ O.secondOuter := by
  intro h
  apply quotientEdgePair_not_isDiag T O.secondBridge.bridge
  rw [O.secondBridge.component_pair, h, Sym2.mk_isDiag_iff]

theorem TwoBridgeOrientation.unitOuter_ne_secondOuter
    {T : PosIntTree n} {W : GraphTwoOddWeights T}
    (O : TwoBridgeOrientation W) : O.unitOuter ≠ O.secondOuter := by
  intro h
  have hpairs : quotientEdgePair T O.unitBridge.bridge =
      quotientEdgePair T O.secondBridge.bridge := by
    rw [O.unitBridge.component_pair, O.secondBridge.component_pair, h,
      Sym2.eq_swap]
  have hbridges := quotientEdgePair_injective T hpairs
  apply W.ne
  exact O.unitBridge_eq.symm.trans
    ((congrArg Subtype.val hbridges).trans O.secondBridge_eq)

private theorem orientedBridge_endpoints_ne
    {T : PosIntTree n} {C D : EvenComponent T}
    (b : OrientedBridge T C D)
    (x : ComponentVertex T C) (y : ComponentVertex T D) : x.1 ≠ y.1 := by
  intro h
  have hCD : C = D :=
    x.2.symm.trans ((congrArg (componentOf T) h).trans y.2)
  apply quotientEdgePair_not_isDiag T b.bridge
  rw [b.component_pair, hCD, Sym2.mk_isDiag_iff]

noncomputable def orientedBridgePair
    {T : PosIntTree n} {C D : EvenComponent T}
    (b : OrientedBridge T C D)
    (x : ComponentVertex T C) (y : ComponentVertex T D) : VertexPair n :=
  VertexPair.ofDistinct x.1 y.1 (orientedBridge_endpoints_ne b x y)

theorem orientedBridgePair_dist
    {T : PosIntTree n} {C D : EvenComponent T}
    (b : OrientedBridge T C D)
    (x : ComponentVertex T C) (y : ComponentVertex T D) :
    T.pairDist (orientedBridgePair b x y) =
      2 * rho T x b.sourcePort + T.weight b.bridge.1 +
        2 * rho T b.targetPort y := by
  rw [orientedBridgePair, T.pairDist_pairOfDistinct]
  have hroute := orientedBridge_distance_decomposition T b
    (oddCut_reachable_of_component_eq T b.bridge
      (x.2.trans b.source_component.symm))
    (oddCut_reachable_of_component_eq T b.bridge
      (y.2.trans b.target_component.symm))
  have hx := dist_eq_two_mul_rho T x b.sourcePort
  have hy := dist_eq_two_mul_rho T b.targetPort y
  change T.dist x.1 b.sourcePortVertex = 2 * rho T x b.sourcePort at hx
  change T.dist b.targetPortVertex y.1 = 2 * rho T b.targetPort y at hy
  rw [hroute, hx, hy]

/-- The unordered global pair remembers its ordered component endpoints:
the apparent swapped case would identify the two distinct quotient
components joined by the odd bridge. -/
theorem orientedBridgePair_injective
    {T : PosIntTree n} {C D : EvenComponent T}
    (b : OrientedBridge T C D) :
    Function.Injective (fun z : ComponentVertex T C × ComponentVertex T D =>
      orientedBridgePair b z.1 z.2) := by
  intro z z' hzz
  have hs : s(z.1.1, z.2.1) = s(z'.1.1, z'.2.1) := by
    have h := congrArg
      (fun p : VertexPair n => s(p.left, p.right)) hzz
    simpa [orientedBridgePair, vertexPair_ofDistinct_sym2] using h
  rcases Sym2.eq_iff.mp hs with hdirect | hswap
  · apply Prod.ext
    · exact Subtype.ext hdirect.1
    · exact Subtype.ext hdirect.2
  · have hCD : C = D :=
      z.1.2.symm.trans ((congrArg (componentOf T) hswap.1).trans z'.2.2)
    exfalso
    apply quotientEdgePair_not_isDiag T b.bridge
    rw [b.component_pair, hCD, Sym2.mk_isDiag_iff]

/-- Rooted half-depth is injective at either actual port of an oriented odd
bridge.  Fixing the opposite port turns an equality of depths into an
equality of actual crossing pairs. -/
theorem orientedSourceDepth_injective
    {T : PosIntTree n} (hL : IsLeech T)
    {C D : EvenComponent T} (b : OrientedBridge T C D) :
    Function.Injective (fun x : ComponentVertex T C =>
      rho T x b.sourcePort) := by
  intro x x' hxx
  have hp : orientedBridgePair b x b.targetPort =
      orientedBridgePair b x' b.targetPort := by
    apply hL.pairDist_injective
    rw [orientedBridgePair_dist, orientedBridgePair_dist]
    change rho T x b.sourcePort = rho T x' b.sourcePort at hxx
    rw [hxx]
  have hpair : (x, b.targetPort) = (x', b.targetPort) :=
    orientedBridgePair_injective b (a₁ := (x, b.targetPort))
      (a₂ := (x', b.targetPort)) hp
  exact congrArg Prod.fst hpair

theorem orientedTargetDepth_injective
    {T : PosIntTree n} (hL : IsLeech T)
    {C D : EvenComponent T} (b : OrientedBridge T C D) :
    Function.Injective (fun y : ComponentVertex T D =>
      rho T b.targetPort y) := by
  intro y y' hyy
  have hp : orientedBridgePair b b.sourcePort y =
      orientedBridgePair b b.sourcePort y' := by
    apply hL.pairDist_injective
    rw [orientedBridgePair_dist, orientedBridgePair_dist]
    change rho T b.targetPort y = rho T b.targetPort y' at hyy
    rw [hyy]
  have hpair : (b.sourcePort, y) = (b.sourcePort, y') :=
    orientedBridgePair_injective b (a₁ := (b.sourcePort, y))
      (a₂ := (b.sourcePort, y')) hp
  exact congrArg Prod.snd hpair

/-- Internal half-distance spectra of two different actual even components
are disjoint.  This version is independent of a preferred physical
orientation and is reusable for the rerooted middle component. -/
theorem rootedMetrics_internal_disjoint
    (T : PosIntTree n) (hL : IsLeech T)
    {C D : EvenComponent T} (hCD : C ≠ D)
    (rC : ComponentVertex T C) (rD : ComponentVertex T D)
    {a b c d : ℕ}
    (ha : a ∈ rootedDepthSupport T rC)
    (hb : b ∈ rootedDepthSupport T rC)
    (hc : c ∈ rootedDepthSupport T rD)
    (hd : d ∈ rootedDepthSupport T rD)
    (hab : a ≠ b) (hcd : c ≠ d) :
    rho T (vertexAtDepth T rC a) (vertexAtDepth T rC b) ≠
      rho T (vertexAtDepth T rD c) (vertexAtDepth T rD d) := by
  intro heq
  let xa := vertexAtDepth T rC a
  let xb := vertexAtDepth T rC b
  let xc := vertexAtDepth T rD c
  let xd := vertexAtDepth T rD d
  have hxab : xa.1 ≠ xb.1 := by
    intro h
    apply hab
    have hsub : xa = xb := Subtype.ext h
    calc
      a = rho T xa rC := (vertexAtDepth_spec T rC ha).symm
      _ = rho T xb rC := by rw [hsub]
      _ = b := vertexAtDepth_spec T rC hb
  have hxcd : xc.1 ≠ xd.1 := by
    intro h
    apply hcd
    have hsub : xc = xd := Subtype.ext h
    calc
      c = rho T xc rD := (vertexAtDepth_spec T rD hc).symm
      _ = rho T xd rD := by rw [hsub]
      _ = d := vertexAtDepth_spec T rD hd
  let p := VertexPair.ofDistinct xa.1 xb.1 hxab
  let q := VertexPair.ofDistinct xc.1 xd.1 hxcd
  have hpq : p = q := by
    apply hL.pairDist_injective
    dsimp only [p, q]
    rw [T.pairDist_pairOfDistinct, T.pairDist_pairOfDistinct]
    have hp := dist_eq_two_mul_rho T xa xb
    have hq := dist_eq_two_mul_rho T xc xd
    exact hp.trans ((congrArg (fun z => 2 * z) heq).trans hq.symm)
  have hs : s(xa.1, xb.1) = s(xc.1, xd.1) := by
    have h := congrArg (fun z : VertexPair n => s(z.left, z.right)) hpq
    simpa [p, q, vertexPair_ofDistinct_sym2] using h
  rcases Sym2.eq_iff.mp hs with h | h
  · apply hCD
    exact xa.2.symm.trans ((congrArg (componentOf T) h.1).trans xc.2)
  · apply hCD
    exact xa.2.symm.trans ((congrArg (componentOf T) h.1).trans xd.2)

/-- Pointwise form of cross-component internal-spectrum disjointness. -/
theorem componentInternalRho_ne
    (T : PosIntTree n) (hL : IsLeech T)
    {C D : EvenComponent T} (hCD : C ≠ D)
    {x x' : ComponentVertex T C} {y y' : ComponentVertex T D}
    (hxx : x ≠ x') (hyy : y ≠ y') :
    rho T x x' ≠ rho T y y' := by
  intro heq
  have hrawXX : x.1 ≠ x'.1 := fun h => hxx (Subtype.ext h)
  have hrawYY : y.1 ≠ y'.1 := fun h => hyy (Subtype.ext h)
  let p := VertexPair.ofDistinct x.1 x'.1 hrawXX
  let q := VertexPair.ofDistinct y.1 y'.1 hrawYY
  have hpq : p = q := by
    apply hL.pairDist_injective
    dsimp only [p, q]
    rw [T.pairDist_pairOfDistinct, T.pairDist_pairOfDistinct]
    have hp := dist_eq_two_mul_rho T x x'
    have hq := dist_eq_two_mul_rho T y y'
    omega
  have hs : s(x.1, x'.1) = s(y.1, y'.1) := by
    have h := congrArg (fun z : VertexPair n => s(z.left, z.right)) hpq
    simpa [p, q, vertexPair_ofDistinct_sym2] using h
  rcases Sym2.eq_iff.mp hs with h | h
  · apply hCD
    exact x.2.symm.trans ((congrArg (componentOf T) h.1).trans y.2)
  · apply hCD
    exact x.2.symm.trans ((congrArg (componentOf T) h.1).trans y'.2)

/-- Equality of two nontrivial actual internal half-distances identifies the
underlying unordered physical vertex pairs. -/
theorem internalRho_eq_implies_sym2
    (T : PosIntTree n) (hL : IsLeech T)
    {C D : EvenComponent T}
    {x x' : ComponentVertex T C} {y y' : ComponentVertex T D}
    (hxx : x ≠ x') (hyy : y ≠ y')
    (heq : rho T x x' = rho T y y') :
    s(x.1, x'.1) = s(y.1, y'.1) := by
  have hrawXX : x.1 ≠ x'.1 := fun h => hxx (Subtype.ext h)
  have hrawYY : y.1 ≠ y'.1 := fun h => hyy (Subtype.ext h)
  let p := VertexPair.ofDistinct x.1 x'.1 hrawXX
  let q := VertexPair.ofDistinct y.1 y'.1 hrawYY
  have hpq : p = q := by
    apply hL.pairDist_injective
    dsimp only [p, q]
    rw [T.pairDist_pairOfDistinct, T.pairDist_pairOfDistinct]
    have hp := dist_eq_two_mul_rho T x x'
    have hq := dist_eq_two_mul_rho T y y'
    omega
  have h := congrArg (fun z : VertexPair n => s(z.left, z.right)) hpq
  simpa [p, q, vertexPair_ofDistinct_sym2] using h

/-- In the forced q=8 middle skeleton, a new old-root depth-ten vertex is a
new root branch.  Its half-distances from the old depth 1, 4, and 5 vertices
are respectively 11, 14, and 15.  The last value uses actual gate identity;
the erased arithmetic gate in `RootedSupportMetric` is not enough. -/
theorem q8_depthTen_actual_topology
    (T : PosIntTree n) (hL : IsLeech T)
    {C : EvenComponent T}
    (root u1 u4 u5 u10 : ComponentVertex T C)
    (hdepth : Function.Injective (fun x : ComponentVertex T C =>
      rho T x root))
    (hu1 : rho T u1 root = 1)
    (hu4 : rho T u4 root = 4)
    (hu5 : rho T u5 root = 5)
    (hu10 : rho T u10 root = 10)
    (h14 : rho T u1 u4 = 3)
    (h15 : rho T u1 u5 = 6)
    (h45 : rho T u4 u5 = 9)
    (hbelow8 : ∀ x : ComponentVertex T C, rho T x root < 8 →
      rho T x root = 0 ∨ rho T x root = 1 ∨
        rho T x root = 4 ∨ rho T x root = 5) :
    rho T u1 u10 = 11 ∧
      rho T u4 u10 = 14 ∧ rho T u5 u10 = 15 := by
  have hu1ne10 : u1 ≠ u10 := by
    intro h
    have := congrArg (fun x : ComponentVertex T C => rho T x root) h
    change rho T u1 root = rho T u10 root at this
    omega
  have hu4ne5 : u4 ≠ u5 := by
    intro h
    have := congrArg (fun x : ComponentVertex T C => rho T x root) h
    change rho T u4 root = rho T u5 root at this
    omega
  have hrootne5 : root ≠ u5 := by
    intro h
    rw [← h, rho_self] at hu5
    omega
  have hu5ne10 : u5 ≠ u10 := by
    intro h
    have := congrArg (fun x : ComponentVertex T C => rho T x root) h
    change rho T u5 root = rho T u10 root at this
    omega

  have hd1_10 : rho T u1 u10 = 11 := by
    let G := strongRootGate T root.1 u1.1 u10.1
    let z := gateComponentVertex T root u1 u10 G
    have hzPath : z.1 ∈ (T.path u1.1 root.1).1.support := by
      simpa [z] using G.gate_mem_u
    have hsplit := rootedRho_split_at_path_vertex T root u1 z hzPath
    have hzle : rho T z root ≤ 1 := by
      rw [hu1] at hsplit
      omega
    have hzClass := hbelow8 z (by omega)
    have hgate := strongRootGate_rho_identity T root u1 u10 G
    rcases hzClass with hz0 | hz1 | hz4 | hz5
    · rw [hz0, hu1, hu10] at hgate
      omega
    · have hd9 : rho T u1 u10 = 9 := by
        rw [hz1, hu1, hu10] at hgate
        omega
      have hs := internalRho_eq_implies_sym2 T hL hu1ne10 hu4ne5
        (hd9.trans h45.symm)
      rcases Sym2.eq_iff.mp hs with h | h
      · have hu1eq4 : u1 = u4 := Subtype.ext h.1
        have hdepthEq := congrArg
          (fun x : ComponentVertex T C => rho T x root) hu1eq4
        change rho T u1 root = rho T u4 root at hdepthEq
        omega
      · have hu1eq5 : u1 = u5 := Subtype.ext h.1
        have hdepthEq := congrArg
          (fun x : ComponentVertex T C => rho T x root) hu1eq5
        change rho T u1 root = rho T u5 root at hdepthEq
        omega
    · omega
    · omega

  have hd4_10 : rho T u4 u10 = 14 := by
    have h := rootedRho_fork T root u1 u4 u10 hdepth
      (by omega) (by omega) (by omega) (by omega)
    omega

  have hu1Path4 : u1.1 ∈ (T.path u4.1 root.1).1.support := by
    apply rootedRho_mem_path_of_sub T root u1 u4 hdepth
    · omega
    · omega
    · omega

  have hd5_10 : rho T u5 u10 = 15 := by
    let G := strongRootGate T root.1 u5.1 u10.1
    let z := gateComponentVertex T root u5 u10 G
    have hzPath5 : z.1 ∈ (T.path u5.1 root.1).1.support := by
      simpa [z] using G.gate_mem_u
    have hsplit := rootedRho_split_at_path_vertex T root u5 z hzPath5
    have hzle : rho T z root ≤ 5 := by
      rw [hu5] at hsplit
      omega
    have hzClass := hbelow8 z (by omega)
    have hgate := strongRootGate_rho_identity T root u5 u10 G
    rcases hzClass with hz0 | hz1 | hz4 | hz5
    · rw [hz0, hu5, hu10] at hgate
      omega
    · have hzEq : z = u1 := hdepth (hz1.trans hu1.symm)
      have hu1Path5 : u1.1 ∈ (T.path u5.1 root.1).1.support := by
        simpa [hzEq] using hzPath5
      have hu1Self : u1.1 ∈ (T.path u1.1 root.1).1.support :=
        (T.path u1.1 root.1).1.start_mem_support
      have hu1Root := rootedPaths_common_eq_root_of_add
        T root u1 u5 hdepth (by omega) hu1Self hu1Path5
      rw [hu1Root, rho_self] at hu1
      omega
    · have hzEq : z = u4 := hdepth (hz4.trans hu4.symm)
      have hu4Path5 : u4.1 ∈ (T.path u5.1 root.1).1.support := by
        simpa [hzEq] using hzPath5
      have hu1Path5 : u1.1 ∈ (T.path u5.1 root.1).1.support :=
        pathSupport_suffix_subset T hu4Path5 hu1Path4
      have hu1Self : u1.1 ∈ (T.path u1.1 root.1).1.support :=
        (T.path u1.1 root.1).1.start_mem_support
      have hu1Root := rootedPaths_common_eq_root_of_add
        T root u1 u5 hdepth (by omega) hu1Self hu1Path5
      rw [hu1Root, rho_self] at hu1
      omega
    · have hd5 : rho T u5 u10 = 5 := by
        rw [hz5, hu5, hu10] at hgate
        omega
      have hs := internalRho_eq_implies_sym2 T hL hu5ne10 hrootne5
        (by rw [hd5, rho_comm T root u5, hu5])
      rcases Sym2.eq_iff.mp hs with h | h
      · have hu5root : u5 = root := Subtype.ext h.1
        rw [hu5root, rho_self] at hu5
        omega
      · have hu10root : u10 = root := Subtype.ext h.2
        rw [hu10root, rho_self] at hu10
        omega

  exact ⟨hd1_10, hd4_10, hd5_10⟩

/-! ## The actual topology hidden behind the normalized q=9 skeleton -/

/-- In an actual rooted component realizing the normalized `q=9` factor,
the forced vertices at depths `4` and `8` have half-distance `10`, and those
at depths `5` and `8` have half-distance `13`. -/
private theorem q9_actual_dist_four_eight_and_five_eight
    (T : PosIntTree n) {C : EvenComponent T}
    (root : ComponentVertex T C)
    (hdepth : Function.Injective (fun x : ComponentVertex T C =>
      rho T x root))
    (D : PrefixFactorData q)
    (hSupport : D.P.support = rootedDepthSupport T root)
    (hDist : ∀ a b,
      D.P.dist a b =
        rho T (vertexAtDepth T root a) (vertexAtDepth T root b))
    (S : PrefixFactorData.Q9Skeleton D) :
    rho T (vertexAtDepth T root 4) (vertexAtDepth T root 8) = 10 ∧
      rho T (vertexAtDepth T root 5) (vertexAtDepth T root 8) = 13 := by
  let u1 := vertexAtDepth T root 1
  let u4 := vertexAtDepth T root 4
  let u5 := vertexAtDepth T root 5
  let u8 := vertexAtDepth T root 8
  have h1mem : 1 ∈ rootedDepthSupport T root := by
    rw [← hSupport]
    exact S.P1
  have h4mem : 4 ∈ rootedDepthSupport T root := by
    rw [← hSupport]
    exact S.P4
  have h5mem : 5 ∈ rootedDepthSupport T root := by
    rw [← hSupport]
    exact S.P5
  have h8mem : 8 ∈ rootedDepthSupport T root := by
    rw [← hSupport]
    exact S.P8
  have hu1 : rho T u1 root = 1 :=
    vertexAtDepth_spec T root h1mem
  have hu4 : rho T u4 root = 4 :=
    vertexAtDepth_spec T root h4mem
  have hu5 : rho T u5 root = 5 :=
    vertexAtDepth_spec T root h5mem
  have hu8 : rho T u8 root = 8 :=
    vertexAtDepth_spec T root h8mem
  have h14 : rho T u1 u4 = 3 := by
    calc
      rho T u1 u4 = D.P.dist 1 4 := by
        simpa [u1, u4] using (hDist 1 4).symm
      _ = 3 := S.P_dist_1_4
  have h15 : rho T u1 u5 = 6 := by
    calc
      rho T u1 u5 = D.P.dist 1 5 := by
        simpa [u1, u5] using (hDist 1 5).symm
      _ = 6 := S.P_dist_1_5
  have h18 : rho T u1 u8 = 7 := by
    calc
      rho T u1 u8 = D.P.dist 1 8 := by
        simpa [u1, u8] using (hDist 1 8).symm
      _ = 7 := S.P_dist_1_8
  have hu1path4 : u1.1 ∈ (T.path u4.1 root.1).1.support := by
    apply rootedRho_mem_path_of_sub T root u1 u4 hdepth
    · omega
    · omega
    · omega
  have hu1path8 : u1.1 ∈ (T.path u8.1 root.1).1.support := by
    apply rootedRho_mem_path_of_sub T root u1 u8 hdepth
    · omega
    · omega
    · omega
  let G := strongRootGate T root.1 u4.1 u8.1
  let g := gateComponentVertex T root u4 u8 G
  have hsplit : rho T u4 root = rho T u4 g + rho T g root := by
    apply rootedRho_split_at_path_vertex T root u4 g
    simpa [g] using G.gate_mem_u
  have hgle : rho T g root ≤ 4 := by omega
  have hgmemRoot : rho T g root ∈ rootedDepthSupport T root := by
    rw [rootedDepthSupport, Finset.mem_image]
    exact ⟨g, Finset.mem_univ _, rfl⟩
  have hgmem : rho T g root ∈ D.P.support := by
    rw [hSupport]
    exact hgmemRoot
  have hgClass := S.P_below8 (show rho T g root < 8 by omega) hgmem
  have hgCases : rho T g root = 0 ∨ rho T g root = 1 ∨
      rho T g root = 4 := by
    rcases hgClass with h | h | h | h <;> omega
  have h48 : rho T u4 u8 = 10 := by
    rcases hgCases with hg0 | hg1 | hg4
    · have hgr : g = root := by
        apply hdepth
        simpa [rho_self] using hg0
      have hgate : G.gate = root.1 := by
        have hval := congrArg Subtype.val hgr
        simpa [g, gateComponentVertex_val] using hval
      have hu1root : u1.1 = root.1 :=
        G.common_eq_root hgate hu1path4 hu1path8
      have : u1 = root := Subtype.ext hu1root
      rw [this, rho_self] at hu1
      omega
    · have hgateIdentity := strongRootGate_rho_identity T root u4 u8 G
      change rho T u4 u8 + 2 * rho T g root =
        rho T u4 root + rho T u8 root at hgateIdentity
      omega
    · have hgateIdentity := strongRootGate_rho_identity T root u4 u8 G
      change rho T u4 u8 + 2 * rho T g root =
        rho T u4 root + rho T u8 root at hgateIdentity
      have hd48four : rho T u4 u8 = 4 := by omega
      have hdup : D.P.dist 4 8 = D.P.dist 0 4 := by
        calc
          D.P.dist 4 8 = rho T u4 u8 := by
            simpa [u4, u8] using hDist 4 8
          _ = 4 := hd48four
          _ = D.P.dist 0 4 := (D.P.dist_zero_left S.P4).symm
      have hpairs := D.P_internal_injective S.P4 S.P8
        D.P.zero_mem S.P4 (by omega) (by omega) hdup
      simp only [Sym2.eq_iff] at hpairs
      omega
  have h85 : rho T u8 u5 = 13 := by
    have hfork := rootedRho_fork T root u1 u8 u5 hdepth
      (by omega) (by omega) (by omega) (by omega)
    omega
  exact ⟨by simpa [u4, u8] using h48,
    by simpa [u5, u8, rho_comm] using h85⟩

/-! ## Pure q=9 support classifiers used by the actual rank split -/

private theorem q9_P10_not
    (D : PrefixFactorData q) (S : PrefixFactorData.Q9Skeleton D) :
    10 ∉ D.P.support := by
  intro h10
  have hdup := D.direct h10 D.Q.zero_mem S.P8 S.Q2 (by omega)
  omega

private theorem q9_Q10_not
    (D : PrefixFactorData q) (S : PrefixFactorData.Q9Skeleton D) :
    10 ∉ D.Q.support := by
  intro h10
  have hdup := D.direct D.P.zero_mem h10 S.P8 S.Q2 (by omega)
  omega

private theorem q9_Q11_not
    (D : PrefixFactorData q) (S : PrefixFactorData.Q9Skeleton D)
    (hP58 : D.P.dist 5 8 = 13) :
    11 ∉ D.Q.support := by
  intro h11
  obtain ⟨z, hz, hz2, hz11, hgate⟩ := D.Q.gate S.Q2 h11
  have hzCases : z = 0 ∨ z = 2 := by
    have hzClass := S.Q_below8 (by omega) hz
    rcases hzClass with h | h <;> omega
  rcases hzCases with rfl | rfl
  · have hQdist : D.Q.dist 2 11 = 13 := by omega
    exact (D.internal_disjoint S.P5 S.P8 S.Q2 h11
      (by omega) (by omega) (by rw [hP58, hQdist])).elim
  · have hQdist : D.Q.dist 2 11 = 9 := by omega
    exact (D.internal_disjoint S.P4 S.P5 S.Q2 h11
      (by omega) (by omega) (by rw [S.P_dist_4_5, hQdist])).elim

private theorem q9_sum_eleven_roots
    (D : PrefixFactorData q) (S : PrefixFactorData.Q9Skeleton D)
    {a b : ℕ} (ha : a ∈ D.P.support) (hb : b ∈ D.Q.support)
    (hsum : a + b = 11) :
    (a = 11 ∧ b = 0) ∨ (a = 0 ∧ b = 11) := by
  have hP10 := q9_P10_not D S
  have hQ10 := q9_Q10_not D S
  by_cases ha0 : a = 0
  · exact Or.inr ⟨ha0, by omega⟩
  by_cases hb0 : b = 0
  · exact Or.inl ⟨by omega, hb0⟩
  have haClass : a = 1 ∨ a = 4 ∨ a = 5 ∨ a = 8 := by
    by_cases h8 : a < 8
    · rcases S.P_below8 h8 ha with h | h | h | h
      · exact (ha0 h).elim
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · have : a = 8 ∨ a = 9 ∨ a = 10 := by omega
      rcases this with h | h | h
      · exact Or.inr (Or.inr (Or.inr h))
      · exact (S.P9_not (h ▸ ha)).elim
      · exact (hP10 (h ▸ ha)).elim
  have hbClass : b = 2 := by
    by_cases h8 : b < 8
    · rcases S.Q_below8 h8 hb with h | h
      · exact (hb0 h).elim
      · exact h
    · have : b = 8 ∨ b = 9 ∨ b = 10 := by omega
      rcases this with h | h | h
      · exact (S.Q8_not (h ▸ hb)).elim
      · exact (S.Q9_not (h ▸ hb)).elim
      · exact (hQ10 (h ▸ hb)).elim
  omega

private theorem q9_sum_twelve_roots
    (D : PrefixFactorData q) (S : PrefixFactorData.Q9Skeleton D)
    (hQ11 : 11 ∉ D.Q.support)
    {a b : ℕ} (ha : a ∈ D.P.support) (hb : b ∈ D.Q.support)
    (hsum : a + b = 12) :
    (a = 12 ∧ b = 0) ∨ (a = 0 ∧ b = 12) := by
  have hP10 := q9_P10_not D S
  have hQ10 := q9_Q10_not D S
  by_cases ha0 : a = 0
  · exact Or.inr ⟨ha0, by omega⟩
  by_cases hb0 : b = 0
  · exact Or.inl ⟨by omega, hb0⟩
  have haClass : a = 1 ∨ a = 4 ∨ a = 5 ∨ a = 8 ∨ a = 11 := by
    by_cases h8 : a < 8
    · rcases S.P_below8 h8 ha with h | h | h | h
      · exact (ha0 h).elim
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · have : a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 := by omega
      rcases this with h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact (S.P9_not (h ▸ ha)).elim
      · exact (hP10 (h ▸ ha)).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  have hbClass : b = 2 := by
    by_cases h8 : b < 8
    · rcases S.Q_below8 h8 hb with h | h
      · exact (hb0 h).elim
      · exact h
    · have : b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 := by omega
      rcases this with h | h | h | h
      · exact (S.Q8_not (h ▸ hb)).elim
      · exact (S.Q9_not (h ▸ hb)).elim
      · exact (hQ10 (h ▸ hb)).elim
      · exact (hQ11 (h ▸ hb)).elim
  omega

private theorem q9_sum_thirteen_roots_of_P12
    (D : PrefixFactorData q) (S : PrefixFactorData.Q9Skeleton D)
    (hP11 : 11 ∉ D.P.support) (hQ11 : 11 ∉ D.Q.support)
    (_hP12 : 12 ∈ D.P.support) (hQ12 : 12 ∉ D.Q.support)
    {a b : ℕ} (ha : a ∈ D.P.support) (hb : b ∈ D.Q.support)
    (hsum : a + b = 13) :
    (a = 13 ∧ b = 0) ∨ (a = 0 ∧ b = 13) := by
  have hP10 := q9_P10_not D S
  have hQ10 := q9_Q10_not D S
  by_cases ha0 : a = 0
  · exact Or.inr ⟨ha0, by omega⟩
  by_cases hb0 : b = 0
  · exact Or.inl ⟨by omega, hb0⟩
  have haClass : a = 1 ∨ a = 4 ∨ a = 5 ∨ a = 8 ∨ a = 12 := by
    by_cases h8 : a < 8
    · rcases S.P_below8 h8 ha with h | h | h | h
      · exact (ha0 h).elim
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · have : a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 ∨ a = 12 := by omega
      rcases this with h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact (S.P9_not (h ▸ ha)).elim
      · exact (hP10 (h ▸ ha)).elim
      · exact (hP11 (h ▸ ha)).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  have hbClass : b = 2 := by
    by_cases h8 : b < 8
    · rcases S.Q_below8 h8 hb with h | h
      · exact (hb0 h).elim
      · exact h
    · have : b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 ∨ b = 12 := by omega
      rcases this with h | h | h | h | h
      · exact (S.Q8_not (h ▸ hb)).elim
      · exact (S.Q9_not (h ▸ hb)).elim
      · exact (hQ10 (h ▸ hb)).elim
      · exact (hQ11 (h ▸ hb)).elim
      · exact (hQ12 (h ▸ hb)).elim
  omega

private theorem q9_sum_fourteen_roots_of_Q12
    (D : PrefixFactorData q) (S : PrefixFactorData.Q9Skeleton D)
    (hQ11 : 11 ∉ D.Q.support)
    (hP12 : 12 ∉ D.P.support) (_hQ12 : 12 ∈ D.Q.support)
    (hQ13 : 13 ∉ D.Q.support)
    {a b : ℕ} (ha : a ∈ D.P.support) (hb : b ∈ D.Q.support)
    (hsum : a + b = 14) :
    (a = 14 ∧ b = 0) ∨ (a = 0 ∧ b = 14) := by
  have hP10 := q9_P10_not D S
  have hQ10 := q9_Q10_not D S
  by_cases ha0 : a = 0
  · exact Or.inr ⟨ha0, by omega⟩
  by_cases hb0 : b = 0
  · exact Or.inl ⟨by omega, hb0⟩
  have haClass : a = 1 ∨ a = 4 ∨ a = 5 ∨ a = 8 ∨
      a = 11 ∨ a = 13 := by
    by_cases h8 : a < 8
    · rcases S.P_below8 h8 ha with h | h | h | h
      · exact (ha0 h).elim
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · have : a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 ∨ a = 12 ∨ a = 13 := by
        omega
      rcases this with h | h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact (S.P9_not (h ▸ ha)).elim
      · exact (hP10 (h ▸ ha)).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact (hP12 (h ▸ ha)).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  have hbClass : b = 2 ∨ b = 12 := by
    by_cases h8 : b < 8
    · rcases S.Q_below8 h8 hb with h | h
      · exact (hb0 h).elim
      · exact Or.inl h
    · have : b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 ∨ b = 12 ∨ b = 13 := by
        omega
      rcases this with h | h | h | h | h | h
      · exact (S.Q8_not (h ▸ hb)).elim
      · exact (S.Q9_not (h ▸ hb)).elim
      · exact (hQ10 (h ▸ hb)).elim
      · exact (hQ11 (h ▸ hb)).elim
      · exact Or.inr h
      · exact (hQ13 (h ▸ hb)).elim
  omega

private theorem pathEdges_start_segment_subset
    (T : PosIntTree n) {u v z : Fin n}
    (hz : z ∈ (T.path u v).1.support) :
    T.pathEdges u z ⊆ T.pathEdges u v := by
  let q := (T.path u v).1.takeUntil z hz
  have hqpath : q.IsPath := (T.path u v).2.takeUntil hz
  have hqeq : (⟨q, hqpath⟩ : T.graph.Path u z) = T.path u z :=
    T.path_unique _
  intro e he
  have heq : e ∈ q.edges := by
    rw [congrArg (fun p => p.1.edges) hqeq]
    simpa [PosIntTree.pathEdges] using he
  have hefull : e ∈ (T.path u v).1.edges :=
    (T.path u v).1.edges_takeUntil_subset hz heq
  simpa [PosIntTree.pathEdges] using hefull

private theorem orientedBridge_ports_cut_orientation
    {T : PosIntTree n} {C D : EvenComponent T}
    (b : OrientedBridge T C D) :
    (T.LeftCut b.bridge.1 b.sourcePortVertex ∧
      T.RightCut b.bridge.1 b.targetPortVertex) ∨
    (T.RightCut b.bridge.1 b.sourcePortVertex ∧
      T.LeftCut b.bridge.1 b.targetPortVertex) := by
  have hend :
      s(T.edgeLeft b.bridge.1, T.edgeRight b.bridge.1) =
        s(b.sourcePortVertex, b.targetPortVertex) :=
    (T.edge_eq_mk_endpoints b.bridge.1).symm.trans b.edge_eq_ports
  rcases Sym2.eq_iff.mp hend with h | h
  · left
    exact ⟨by simpa [h.1] using T.edgeLeft_mem_LeftCut b.bridge.1,
      by simpa [h.2] using T.edgeRight_mem_RightCut b.bridge.1⟩
  · right
    exact ⟨by simpa [h.2] using T.edgeRight_mem_RightCut b.bridge.1,
      by simpa [h.1] using T.edgeLeft_mem_LeftCut b.bridge.1⟩

private theorem orientedBridge_sourcePort_mem_pathSupport
    {T : PosIntTree n} {C D : EvenComponent T}
    (b : OrientedBridge T C D) {u v : Fin n}
    (h : b.bridge.1.1 ∈ T.pathEdges u v) :
    b.sourcePortVertex ∈ (T.path u v).1.support := by
  have he : b.bridge.1.1 ∈ (T.path u v).1.edges := by
    simpa [PosIntTree.pathEdges] using h
  rw [b.edge_eq_ports] at he
  exact (T.path u v).1.fst_mem_support_of_mem_edges he

private theorem orientedBridge_targetPort_mem_pathSupport
    {T : PosIntTree n} {C D : EvenComponent T}
    (b : OrientedBridge T C D) {u v : Fin n}
    (h : b.bridge.1.1 ∈ T.pathEdges u v) :
    b.targetPortVertex ∈ (T.path u v).1.support := by
  have he : b.bridge.1.1 ∈ (T.path u v).1.edges := by
    simpa [PosIntTree.pathEdges] using h
  rw [b.edge_eq_ports] at he
  exact (T.path u v).1.snd_mem_support_of_mem_edges he

/-- A pair crossing one oriented odd bridge and avoiding a second named edge
is an actual point of the oriented component rectangle, provided avoiding
those two edges is known to identify an even component. -/
private theorem orientedRectangle_of_cross_avoids
    {T : PosIntTree n} {C D : EvenComponent T}
    (b : OrientedBridge T C D) (other : T.Edge)
    (hsame : ∀ {u v : Fin n},
      b.bridge.1.1 ∉ T.pathEdges u v →
      other.1 ∉ T.pathEdges u v → componentOf T u = componentOf T v)
    (p : VertexPair n)
    (hcross : b.bridge.1.1 ∈ T.pathEdges p.left p.right)
    (hother : other.1 ∉ T.pathEdges p.left p.right) :
    ∃ x : ComponentVertex T C, ∃ y : ComponentVertex T D,
      orientedBridgePair b x y = p := by
  have hsupp := orientedBridge_sourcePort_mem_pathSupport b hcross
  have htsupp := orientedBridge_targetPort_mem_pathSupport b hcross
  have hsuppRev : b.sourcePortVertex ∈
      (T.path p.right p.left).1.support :=
    (mem_pathSupport_comm T).mp hsupp
  have htsuppRev : b.targetPortVertex ∈
      (T.path p.right p.left).1.support :=
    (mem_pathSupport_comm T).mp htsupp
  have hsLeft := pathEdges_start_segment_subset T hsupp
  have htLeft := pathEdges_start_segment_subset T htsupp
  have hsRight := pathEdges_start_segment_subset T hsuppRev
  have htRight := pathEdges_start_segment_subset T htsuppRev
  rw [T.pathEdges_comm p.right p.left] at hsRight htRight
  have hotherSL : other.1 ∉ T.pathEdges p.left b.sourcePortVertex :=
    fun h => hother (hsLeft h)
  have hotherTL : other.1 ∉ T.pathEdges p.left b.targetPortVertex :=
    fun h => hother (htLeft h)
  have hotherSR : other.1 ∉ T.pathEdges p.right b.sourcePortVertex :=
    fun h => hother (hsRight h)
  have hotherTR : other.1 ∉ T.pathEdges p.right b.targetPortVertex :=
    fun h => hother (htRight h)
  rcases orientedBridge_ports_cut_orientation b with hp | hp <;>
    rcases (T.mem_pathEdges_iff_opposite_cuts b.bridge.1
      p.left p.right).mp hcross with he | he
  · have hsavoid : b.bridge.1.1 ∉
        T.pathEdges p.left b.sourcePortVertex :=
      (T.cut_reachable_iff_not_mem_pathEdges b.bridge.1 _ _).1
        (he.1.trans hp.1.symm)
    have htavoid : b.bridge.1.1 ∉
        T.pathEdges p.right b.targetPortVertex :=
      (T.cut_reachable_iff_not_mem_pathEdges b.bridge.1 _ _).1
        (he.2.trans hp.2.symm)
    let x : ComponentVertex T C :=
      ⟨p.left, (hsame hsavoid hotherSL).trans b.source_component⟩
    let y : ComponentVertex T D :=
      ⟨p.right, (hsame htavoid hotherTR).trans b.target_component⟩
    refine ⟨x, y, ?_⟩
    change VertexPair.ofDistinct p.left p.right _ = p
    rw [VertexPair.ofDistinct_eq_of_lt _ p.left_lt_right]
    apply Subtype.ext
    rfl
  · have hsavoid : b.bridge.1.1 ∉
        T.pathEdges p.right b.sourcePortVertex :=
      (T.cut_reachable_iff_not_mem_pathEdges b.bridge.1 _ _).1
        (he.2.trans hp.1.symm)
    have htavoid : b.bridge.1.1 ∉
        T.pathEdges p.left b.targetPortVertex :=
      (T.cut_reachable_iff_not_mem_pathEdges b.bridge.1 _ _).1
        (he.1.trans hp.2.symm)
    let x : ComponentVertex T C :=
      ⟨p.right, (hsame hsavoid hotherSR).trans b.source_component⟩
    let y : ComponentVertex T D :=
      ⟨p.left, (hsame htavoid hotherTL).trans b.target_component⟩
    refine ⟨x, y, ?_⟩
    change VertexPair.ofDistinct p.right p.left _ = p
    rw [VertexPair.ofDistinct]
    split
    · rename_i hlt
      exact (not_lt_of_ge p.left_lt_right.le hlt).elim
    · rfl
  · have hsavoid : b.bridge.1.1 ∉
        T.pathEdges p.right b.sourcePortVertex :=
      (T.cut_reachable_iff_not_mem_pathEdges b.bridge.1 _ _).1
        (he.2.trans hp.1.symm)
    have htavoid : b.bridge.1.1 ∉
        T.pathEdges p.left b.targetPortVertex :=
      (T.cut_reachable_iff_not_mem_pathEdges b.bridge.1 _ _).1
        (he.1.trans hp.2.symm)
    let x : ComponentVertex T C :=
      ⟨p.right, (hsame hsavoid hotherSR).trans b.source_component⟩
    let y : ComponentVertex T D :=
      ⟨p.left, (hsame htavoid hotherTL).trans b.target_component⟩
    refine ⟨x, y, ?_⟩
    change VertexPair.ofDistinct p.right p.left _ = p
    rw [VertexPair.ofDistinct]
    split
    · rename_i hlt
      exact (not_lt_of_ge p.left_lt_right.le hlt).elim
    · rfl
  · have hsavoid : b.bridge.1.1 ∉
        T.pathEdges p.left b.sourcePortVertex :=
      (T.cut_reachable_iff_not_mem_pathEdges b.bridge.1 _ _).1
        (he.1.trans hp.1.symm)
    have htavoid : b.bridge.1.1 ∉
        T.pathEdges p.right b.targetPortVertex :=
      (T.cut_reachable_iff_not_mem_pathEdges b.bridge.1 _ _).1
        (he.2.trans hp.2.symm)
    let x : ComponentVertex T C :=
      ⟨p.left, (hsame hsavoid hotherSL).trans b.source_component⟩
    let y : ComponentVertex T D :=
      ⟨p.right, (hsame htavoid hotherTR).trans b.target_component⟩
    refine ⟨x, y, ?_⟩
    change VertexPair.ofDistinct p.left p.right _ = p
    rw [VertexPair.ofDistinct_eq_of_lt _ p.left_lt_right]
    apply Subtype.ext
    rfl

theorem unitOnlyPair_exists_orientedRectangle
    {T : PosIntTree n} (W : GraphTwoOddWeights T)
    (O : TwoBridgeOrientation W) (p : VertexPair n)
    (hunit : W.unit.1 ∈ T.pathEdges p.left p.right)
    (hsecond : W.second.1 ∉ T.pathEdges p.left p.right) :
    ∃ x : ComponentVertex T O.unitOuter,
      ∃ y : ComponentVertex T O.middle,
        orientedBridgePair O.unitBridge x y = p := by
  apply orientedRectangle_of_cross_avoids O.unitBridge W.second
  · intro u v hu hs
    apply component_eq_of_avoids_twoOdd W
    · simpa [O.unitBridge_eq] using hu
    · exact hs
  · simpa [O.unitBridge_eq] using hunit
  · exact hsecond

theorem secondOnlyPair_exists_orientedRectangle
    {T : PosIntTree n} (W : GraphTwoOddWeights T)
    (O : TwoBridgeOrientation W) (p : VertexPair n)
    (hunit : W.unit.1 ∉ T.pathEdges p.left p.right)
    (hsecond : W.second.1 ∈ T.pathEdges p.left p.right) :
    ∃ x : ComponentVertex T O.middle,
      ∃ y : ComponentVertex T O.secondOuter,
        orientedBridgePair O.secondBridge x y = p := by
  apply orientedRectangle_of_cross_avoids O.secondBridge W.unit
  · intro u v hs hu
    apply component_eq_of_avoids_twoOdd W hu
    simpa [O.secondBridge_eq] using hs
  · simpa [O.secondBridge_eq] using hsecond
  · exact hunit

/-- The complete named two-edge datum associated with `GraphTwoOddWeights`.
This lets the T12 parity relation be used without returning to an arbitrary
choice of the two odd edges. -/
noncomputable def graphTwoOddEdges
    {T : PosIntTree n} (W : GraphTwoOddWeights T) : TwoOddEdges T where
  e := W.unit
  f := W.second
  ne := W.ne
  oddSet := by
    classical
    ext g
    simp only [actualOddPhysicalEdges, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    exact W.odd_iff g

/-- Every actual odd pair crosses exactly one of the two named physical odd
edges.  This is the coefficient partition behind the linked two-product
identity, proved here directly from T12's exact incidence relation. -/
theorem oddPair_exactlyOne_namedBridge
    {T : PosIntTree n} (W : GraphTwoOddWeights T)
    (p : OddVertexPair T) :
    (W.unit.1 ∈ T.pathEdges p.1.left p.1.right ∧
      W.second.1 ∉ T.pathEdges p.1.left p.1.right) ∨
    (W.unit.1 ∉ T.pathEdges p.1.left p.1.right ∧
      W.second.1 ∈ T.pathEdges p.1.left p.1.right) := by
  let d := graphTwoOddEdges W
  have hrel := ceilHalf_pairDist_relation_fixed T d p.1
  dsimp [d, graphTwoOddEdges] at hrel
  have hodd := p.2
  by_cases hu : W.unit.1 ∈ T.pathEdges p.1.left p.1.right
  · by_cases hs : W.second.1 ∈ T.pathEdges p.1.left p.1.right
    · change 2 * (ceilHalfTree T).pairDist p.1 =
          T.pairDist p.1 +
            (if W.unit.1 ∈ T.pathEdges p.1.left p.1.right then 1 else 0) +
            (if W.second.1 ∈ T.pathEdges p.1.left p.1.right then 1 else 0)
        at hrel
      simp [hu, hs] at hrel
      omega
    · exact Or.inl ⟨hu, hs⟩
  · by_cases hs : W.second.1 ∈ T.pathEdges p.1.left p.1.right
    · exact Or.inr ⟨hu, hs⟩
    · change 2 * (ceilHalfTree T).pairDist p.1 =
          T.pairDist p.1 +
            (if W.unit.1 ∈ T.pathEdges p.1.left p.1.right then 1 else 0) +
            (if W.second.1 ∈ T.pathEdges p.1.left p.1.right then 1 else 0)
        at hrel
      simp [hu, hs] at hrel
      omega

/-- An oriented bridge rectangle point really crosses its named physical
bridge. -/
theorem orientedBridgePair_mem_path
    {T : PosIntTree n} {C D : EvenComponent T}
    (b : OrientedBridge T C D)
    (x : ComponentVertex T C) (y : ComponentVertex T D) :
    b.bridge.1.1 ∈ T.pathEdges
      (orientedBridgePair b x y).left
      (orientedBridgePair b x y).right := by
  have hx : (T.cutGraph b.bridge.1).Reachable x.1 b.sourcePortVertex :=
    oddCut_reachable_of_component_eq T b.bridge
      (x.2.trans b.source_component.symm)
  have hy : (T.cutGraph b.bridge.1).Reachable y.1 b.targetPortVertex :=
    oddCut_reachable_of_component_eq T b.bridge
      (y.2.trans b.target_component.symm)
  have hraw : b.bridge.1.1 ∈ T.pathEdges x.1 y.1 := by
    rcases orientedBridge_ports_cut_orientation b with h | h
    · apply (T.mem_pathEdges_iff_opposite_cuts b.bridge.1 x.1 y.1).2
      exact Or.inl ⟨hx.trans h.1, hy.trans h.2⟩
    · apply (T.mem_pathEdges_iff_opposite_cuts b.bridge.1 x.1 y.1).2
      exact Or.inr ⟨hx.trans h.1, hy.trans h.2⟩
  rw [orientedBridgePair, pathEdges_ofDistinct]
  exact hraw

theorem orientedBridgePair_odd
    {T : PosIntTree n} {C D : EvenComponent T}
    (b : OrientedBridge T C D)
    (x : ComponentVertex T C) (y : ComponentVertex T D) :
    T.pairDist (orientedBridgePair b x y) % 2 = 1 := by
  have hw : T.weight b.bridge.1 % 2 = 1 :=
    (Nat.odd_iff (n := T.weight b.bridge.1)).mp b.bridge.2
  rw [orientedBridgePair_dist]
  omega

noncomputable def orientedOddPair
    {T : PosIntTree n} {C D : EvenComponent T}
    (b : OrientedBridge T C D)
    (x : ComponentVertex T C) (y : ComponentVertex T D) :
    OddVertexPair T :=
  ⟨orientedBridgePair b x y, orientedBridgePair_odd b x y⟩

/-- Half-rank of a point in the first, weight-one bridge rectangle. -/
theorem unitBridgePair_halfRank
    {T : PosIntTree n} (W : GraphTwoOddWeights T)
    (O : TwoBridgeOrientation W)
    (x : ComponentVertex T O.unitOuter)
    (y : ComponentVertex T O.middle) :
    T.pairDist (orientedBridgePair O.unitBridge x y) / 2 =
      rho T x O.unitBridge.sourcePort +
        rho T O.unitBridge.targetPort y := by
  rw [orientedBridgePair_dist, O.unitBridge_eq, W.unit_weight]
  omega

/-- The first-product factors with their orientation aligned to
`unitOuter -> middle`.  Unlike the earlier left/right adapter, this record
retains the identity of the quotient-middle factor after normalization. -/
noncomputable def prefixFactorDataOfOrientation
    {T : PosIntTree n} (hL : IsLeech T) (W : GraphTwoOddWeights T)
    (O : TwoBridgeOrientation W) : PrefixFactorData W.q := by
  let rP := O.unitBridge.sourcePort
  let rQ := O.unitBridge.targetPort
  let hPdepth := orientedSourceDepth_injective hL O.unitBridge
  let hQdepth : Function.Injective
      (fun y : ComponentVertex T O.middle => rho T y rQ) := by
    intro y y' h
    apply orientedTargetDepth_injective hL O.unitBridge
    simpa [rho_comm] using h
  let P := rootedComponentMetric T rP hPdepth
  let Q := rootedComponentMetric T rQ hQdepth
  refine {
    P := P
    Q := Q
    direct := ?_
    coversBelow := ?_
    omitsQ := ?_
    P_internal_injective := ?_
    Q_internal_injective := ?_
    internal_disjoint := ?_ }
  · intro a b a' b' ha hb ha' hb' hsum
    let x := vertexAtDepth T rP a
    let y := vertexAtDepth T rQ b
    let x' := vertexAtDepth T rP a'
    let y' := vertexAtDepth T rQ b'
    have hp : orientedBridgePair O.unitBridge x y =
        orientedBridgePair O.unitBridge x' y' := by
      apply hL.pairDist_injective
      rw [orientedBridgePair_dist, orientedBridgePair_dist,
        O.unitBridge_eq, W.unit_weight,
        rho_comm T rQ y, rho_comm T rQ y',
        vertexAtDepth_spec T rP ha, vertexAtDepth_spec T rQ hb,
        vertexAtDepth_spec T rP ha', vertexAtDepth_spec T rQ hb']
      omega
    have hxy : (x, y) = (x', y') :=
      orientedBridgePair_injective O.unitBridge
        (a₁ := (x, y)) (a₂ := (x', y')) hp
    have hxx : x = x' := by simpa using congrArg Prod.fst hxy
    have hyy : y = y' := by simpa using congrArg Prod.snd hxy
    constructor
    · calc
        a = rho T x rP := (vertexAtDepth_spec T rP ha).symm
        _ = rho T x' rP := by rw [hxx]
        _ = a' := vertexAtDepth_spec T rP ha'
    · calc
        b = rho T y rQ := (vertexAtDepth_spec T rQ hb).symm
        _ = rho T y' rQ := by rw [hyy]
        _ = b' := vertexAtDepth_spec T rQ hb'
  · intro k hk
    let D := graphSecondOddBridgeData hL W
    let i : Fin D.t := ⟨k, by simpa [D] using hk⟩
    let p := (lowOddPair hL D i).1
    have hunit : W.unit.1 ∈ T.pathEdges p.left p.right := by
      simpa [D, p] using unit_mem_lowOddPair_path hL D i
    have hsecond : W.second.1 ∉ T.pathEdges p.left p.right := by
      intro hs
      have hle := T.weightOfPair_le_dist_of_mem hs
      have hdist := lowOddPair_dist hL D i
      rw [T.weightOfPair_edge, W.second_weight] at hle
      have hpdist : T.dist p.left p.right = 2 * k + 1 := by
        simpa [p, PosIntTree.pairDist] using hdist
      omega
    obtain ⟨x, y, hpair⟩ :=
      unitOnlyPair_exists_orientedRectangle W O p hunit hsecond
    let a := rho T x rP
    let b := rho T rQ y
    have ha : a ∈ P.support := by
      change a ∈ rootedDepthSupport T rP
      rw [rootedDepthSupport, Finset.mem_image]
      exact ⟨x, Finset.mem_univ _, rfl⟩
    have hb : b ∈ Q.support := by
      change b ∈ rootedDepthSupport T rQ
      rw [rootedDepthSupport, Finset.mem_image]
      exact ⟨y, Finset.mem_univ _, rho_comm T y rQ⟩
    refine ⟨a, ha, b, hb, ?_⟩
    have hpdist := congrArg T.pairDist hpair
    have hlow := lowOddPair_dist hL D i
    rw [orientedBridgePair_dist, O.unitBridge_eq, W.unit_weight] at hpdist
    change T.pairDist (lowOddPair hL D i).1 = _ at hlow
    dsimp only [p, a, b, i, rP, rQ] at hpdist hlow ⊢
    omega
  · intro a b ha hb hsum
    let x := vertexAtDepth T rP a
    let y := vertexAtDepth T rQ b
    have hrect : T.pairDist (orientedBridgePair O.unitBridge x y) =
        2 * W.q + 1 := by
      rw [orientedBridgePair_dist, O.unitBridge_eq, W.unit_weight,
        rho_comm T rQ y,
        vertexAtDepth_spec T rP ha, vertexAtDepth_spec T rQ hb]
      omega
    have hedge : T.pairDist (T.edgePair W.second) = 2 * W.q + 1 := by
      rw [T.edgePair_dist, W.second_weight]
    have hpairs : orientedBridgePair O.unitBridge x y =
        T.edgePair W.second :=
      hL.pairDist_injective (hrect.trans hedge.symm)
    have hunit : W.unit.1 ∈ T.pathEdges
        (orientedBridgePair O.unitBridge x y).left
        (orientedBridgePair O.unitBridge x y).right := by
      simpa [O.unitBridge_eq] using
        orientedBridgePair_mem_path O.unitBridge x y
    rw [hpairs, T.edgePair_left, T.edgePair_right,
      T.pathEdges_edge] at hunit
    apply W.ne
    exact Subtype.ext (Finset.mem_singleton.mp hunit)
  · intro a b c d ha hb hc hd hab hcd heq
    exact rootedMetric_internal_injective T hL rP
      ha hb hc hd hab hcd heq
  · intro a b c d ha hb hc hd hab hcd heq
    exact rootedMetric_internal_injective T hL rQ
      ha hb hc hd hab hcd heq
  · intro a b c d ha hb hc hd hab hcd
    have hcomponents : O.unitOuter ≠ O.middle := by
      intro h
      apply quotientEdgePair_not_isDiag T O.unitBridge.bridge
      rw [O.unitBridge.component_pair, h, Sym2.mk_isDiag_iff]
    exact rootedMetrics_internal_disjoint T hL hcomponents rP rQ
      ha hb hc hd hab hcd

@[simp] theorem prefixFactorDataOfOrientation_P_support
    {T : PosIntTree n} (hL : IsLeech T) (W : GraphTwoOddWeights T)
    (O : TwoBridgeOrientation W) :
    (prefixFactorDataOfOrientation hL W O).P.support =
      rootedDepthSupport T O.unitBridge.sourcePort := rfl

@[simp] theorem prefixFactorDataOfOrientation_Q_support
    {T : PosIntTree n} (hL : IsLeech T) (W : GraphTwoOddWeights T)
    (O : TwoBridgeOrientation W) :
    (prefixFactorDataOfOrientation hL W O).Q.support =
      rootedDepthSupport T O.unitBridge.targetPort := rfl

@[simp] theorem prefixFactorDataOfOrientation_P_dist
    {T : PosIntTree n} (hL : IsLeech T) (W : GraphTwoOddWeights T)
    (O : TwoBridgeOrientation W) (a b : ℕ) :
    (prefixFactorDataOfOrientation hL W O).P.dist a b =
      rho T
        (vertexAtDepth T O.unitBridge.sourcePort a)
        (vertexAtDepth T O.unitBridge.sourcePort b) := rfl

@[simp] theorem prefixFactorDataOfOrientation_Q_dist
    {T : PosIntTree n} (hL : IsLeech T) (W : GraphTwoOddWeights T)
    (O : TwoBridgeOrientation W) (a b : ℕ) :
    (prefixFactorDataOfOrientation hL W O).Q.dist a b =
      rho T
        (vertexAtDepth T O.unitBridge.targetPort a)
        (vertexAtDepth T O.unitBridge.targetPort b) := rfl

theorem orientationSourceDepth_mem
    {T : PosIntTree n} (hL : IsLeech T) (W : GraphTwoOddWeights T)
    (O : TwoBridgeOrientation W) (x : ComponentVertex T O.unitOuter) :
    rho T x O.unitBridge.sourcePort ∈
      (prefixFactorDataOfOrientation hL W O).P.support := by
  rw [prefixFactorDataOfOrientation_P_support,
    rootedDepthSupport, Finset.mem_image]
  exact ⟨x, Finset.mem_univ _, rfl⟩

theorem orientationTargetDepth_mem
    {T : PosIntTree n} (hL : IsLeech T) (W : GraphTwoOddWeights T)
    (O : TwoBridgeOrientation W) (y : ComponentVertex T O.middle) :
    rho T O.unitBridge.targetPort y ∈
      (prefixFactorDataOfOrientation hL W O).Q.support := by
  rw [prefixFactorDataOfOrientation_Q_support,
    rootedDepthSupport, Finset.mem_image]
  exact ⟨y, Finset.mem_univ _, rho_comm T y O.unitBridge.targetPort⟩

/-- Exact half-rank of an actual pair crossing the second bridge in the
linked orientation. -/
theorem secondBridgePair_halfRank
    {T : PosIntTree n} (W : GraphTwoOddWeights T)
    (O : TwoBridgeOrientation W)
    (x : ComponentVertex T O.middle)
    (y : ComponentVertex T O.secondOuter) :
    T.pairDist (orientedBridgePair O.secondBridge x y) / 2 =
      W.q + rho T x O.secondBridge.sourcePort +
        rho T O.secondBridge.targetPort y := by
  rw [orientedBridgePair_dist, O.secondBridge_eq, W.second_weight]
  omega

/-- Exact target-length hypothesis used by the distinct-port audit: odd
half-ranks `0,...,14` all occur. -/
def OddTargetThrough14 (n : ℕ) : Prop :=
  15 ≤ (targetN n + 1) / 2

theorem oddTargetThrough14_of_nine_le {n : ℕ} (hn : 9 ≤ n) :
    OddTargetThrough14 n := by
  have hc : Nat.choose 9 2 ≤ Nat.choose n 2 :=
    Nat.choose_le_choose 2 hn
  have h9 : Nat.choose 9 2 = 36 := by norm_num [Nat.choose]
  unfold OddTargetThrough14 targetN
  omega

/-- The unique actual odd pair at a requested rank `0,...,14`. -/
noncomputable def oddTargetPairThrough14
    {T : PosIntTree n} (hL : IsLeech T) (hTarget : OddTargetThrough14 n)
    (k : Fin 15) : OddVertexPair T :=
  (LeechTrees.OddQuotient.IsLeech.oddHalfRankEquiv hL).symm
    ⟨k.1, k.2.trans_le hTarget⟩

@[simp] theorem oddTargetPairThrough14_halfRank
    {T : PosIntTree n} (hL : IsLeech T) (hTarget : OddTargetThrough14 n)
    (k : Fin 15) :
    T.pairDist (oddTargetPairThrough14 hL hTarget k).1 / 2 = k.1 := by
  have h := congrArg Fin.val
    ((LeechTrees.OddQuotient.IsLeech.oddHalfRankEquiv hL).apply_symm_apply
      (⟨k.1, k.2.trans_le hTarget⟩ :
        Fin ((targetN n + 1) / 2)))
  simpa only [oddTargetPairThrough14,
    LeechTrees.OddQuotient.IsLeech.oddHalfRankEquiv_val] using h

/-- Actual linked factorization of every target rank through 14.  The
returned equalities keep both the indexed global pair and the exact rooted
sum, so later collision arguments cannot confuse a support label with an
actual source. -/
theorem oddTargetThrough14_linked_factorization
    {T : PosIntTree n} (hL : IsLeech T) (W : GraphTwoOddWeights T)
    (O : TwoBridgeOrientation W) (hTarget : OddTargetThrough14 n)
    (k : Fin 15) :
    (∃ x : ComponentVertex T O.unitOuter,
      ∃ y : ComponentVertex T O.middle,
        orientedBridgePair O.unitBridge x y =
          (oddTargetPairThrough14 hL hTarget k).1 ∧
        rho T x O.unitBridge.sourcePort +
          rho T O.unitBridge.targetPort y = k.1) ∨
    (∃ x : ComponentVertex T O.middle,
      ∃ y : ComponentVertex T O.secondOuter,
        orientedBridgePair O.secondBridge x y =
          (oddTargetPairThrough14 hL hTarget k).1 ∧
        W.q + rho T x O.secondBridge.sourcePort +
          rho T O.secondBridge.targetPort y = k.1) := by
  let p := oddTargetPairThrough14 hL hTarget k
  rcases oddPair_exactlyOne_namedBridge W p with hfirst | hsecond
  · obtain ⟨x, y, hp⟩ :=
      unitOnlyPair_exists_orientedRectangle W O p.1 hfirst.1 hfirst.2
    left
    refine ⟨x, y, hp, ?_⟩
    have hrank := unitBridgePair_halfRank W O x y
    have htarget := oddTargetPairThrough14_halfRank hL hTarget k
    rw [hp] at hrank
    simpa [p] using hrank.symm.trans htarget
  · obtain ⟨x, y, hp⟩ :=
      secondOnlyPair_exists_orientedRectangle W O p.1 hsecond.1 hsecond.2
    right
    refine ⟨x, y, hp, ?_⟩
    have hrank := secondBridgePair_halfRank W O x y
    have htarget := oddTargetPairThrough14_halfRank hL hTarget k
    rw [hp] at hrank
    simpa [p] using hrank.symm.trans htarget

/-- The collision source demanded by the audit is the actual indexed odd-pair
type, not an anonymous proposition about `q`. -/
def ActualOddHalfRankCollision (T : PosIntTree n) : Prop :=
  ∃ x y : OddVertexPair T, x ≠ y ∧
    T.pairDist x.1 / 2 = T.pairDist y.1 / 2

/-- Equal half-ranks in the two different bridge rectangles are an actual
indexed collision.  Distinctness is proved by path incidence, not assumed. -/
theorem actualCollision_of_unit_second
    {T : PosIntTree n} (W : GraphTwoOddWeights T)
    (O : TwoBridgeOrientation W)
    (x : ComponentVertex T O.unitOuter)
    (y : ComponentVertex T O.middle)
    (u : ComponentVertex T O.middle)
    (v : ComponentVertex T O.secondOuter)
    (hrank : T.pairDist (orientedBridgePair O.unitBridge x y) / 2 =
      T.pairDist (orientedBridgePair O.secondBridge u v) / 2) :
    ActualOddHalfRankCollision T := by
  let p := orientedOddPair O.unitBridge x y
  let q := orientedOddPair O.secondBridge u v
  have hunit : W.unit.1 ∈ T.pathEdges p.1.left p.1.right := by
    simpa [p, orientedOddPair, O.unitBridge_eq] using
      orientedBridgePair_mem_path O.unitBridge x y
  have hsecond : W.second.1 ∈ T.pathEdges q.1.left q.1.right := by
    simpa [q, orientedOddPair, O.secondBridge_eq] using
      orientedBridgePair_mem_path O.secondBridge u v
  have hsecondAvoid : W.second.1 ∉ T.pathEdges p.1.left p.1.right := by
    rcases oddPair_exactlyOne_namedBridge W p with h | h
    · exact h.2
    · exact (h.1 hunit).elim
  have hpq : p ≠ q := by
    intro heq
    apply hsecondAvoid
    have hval : p.1 = q.1 := congrArg Subtype.val heq
    rw [hval]
    exact hsecond
  exact ⟨p, q, hpq, by simpa [p, q, orientedOddPair] using hrank⟩

/-- The complete audited distinct-port collision in the `q=10` case.  Rank
11 locates the second port; rank 13 is then represented by two different
actual bridge rectangles. -/
theorem actualCollision_of_q_ten
    {T : PosIntTree n} (hL : IsLeech T) (W : GraphTwoOddWeights T)
    (O : TwoBridgeOrientation W) (hTarget : OddTargetThrough14 n)
    (hq : W.q = 10) : ActualOddHalfRankCollision T := by
  let D := prefixFactorDataOfOrientation hL W O
  let k11 : Fin 15 := ⟨11, by omega⟩
  have hfactor := oddTargetThrough14_linked_factorization
    hL W O hTarget k11
  have hnoFirst : ∀ {a b}, a ∈ D.P.support → b ∈ D.Q.support →
      a + b ≠ 11 :=
    PrefixFactorData.no_first_sum_eleven_of_q_ten D hq
  rcases hfactor with hfirst | hsecond
  · obtain ⟨x, y, _hpair, hsum⟩ := hfirst
    have hxmem : rho T x O.unitBridge.sourcePort ∈ D.P.support := by
      change rho T x O.unitBridge.sourcePort ∈
        (prefixFactorDataOfOrientation hL W O).P.support
      rw [prefixFactorDataOfOrientation_P_support,
        rootedDepthSupport, Finset.mem_image]
      exact ⟨x, Finset.mem_univ _, rfl⟩
    have hymem : rho T O.unitBridge.targetPort y ∈ D.Q.support := by
      change rho T O.unitBridge.targetPort y ∈
        (prefixFactorDataOfOrientation hL W O).Q.support
      rw [prefixFactorDataOfOrientation_Q_support,
        rootedDepthSupport, Finset.mem_image]
      exact ⟨y, Finset.mem_univ _, rho_comm T y O.unitBridge.targetPort⟩
    exact (hnoFirst hxmem hymem (by simpa [k11] using hsum)).elim
  · obtain ⟨x, y, _hpair, hsum⟩ := hsecond
    have hab : rho T x O.secondBridge.sourcePort +
        rho T O.secondBridge.targetPort y = 1 := by
      dsimp only [k11] at hsum
      omega
    rcases PrefixFactorData.normalized_self_or_swap D (by omega) with
        hOuterP | hMiddleP
    · /- The normalized depth-one factor is `unitOuter`.  Either positive
         summand of the shifted unrank one repeats its internal distance. -/
      let p1 := vertexAtDepth T O.unitBridge.sourcePort 1
      have hp1mem : 1 ∈ rootedDepthSupport T O.unitBridge.sourcePort := by
        simpa [D] using hOuterP.1
      have hp1depth : rho T p1 O.unitBridge.sourcePort = 1 :=
        vertexAtDepth_spec T O.unitBridge.sourcePort hp1mem
      have hp1ne : O.unitBridge.sourcePort ≠ p1 := by
        intro heq
        rw [← heq, rho_self] at hp1depth
        omega
      rcases (show
          rho T x O.secondBridge.sourcePort = 1 ∧
              rho T O.secondBridge.targetPort y = 0 ∨
            rho T x O.secondBridge.sourcePort = 0 ∧
              rho T O.secondBridge.targetPort y = 1 by omega) with h | h
      · have hxne : x ≠ O.secondBridge.sourcePort := by
          intro heq
          rw [heq, rho_self] at h
          omega
        exfalso
        apply componentInternalRho_ne T hL
          O.unitOuter_ne_middle.symm hxne hp1ne
        rw [h.1, rho_comm T O.unitBridge.sourcePort p1, hp1depth]
      · have hyne : O.secondBridge.targetPort ≠ y := by
          intro heq
          rw [← heq, rho_self] at h
          omega
        exfalso
        apply componentInternalRho_ne T hL
          O.unitOuter_ne_secondOuter hp1ne hyne
        rw [rho_comm T O.unitBridge.sourcePort p1, hp1depth, h.2]
    · /- The normalized depth-one factor is the actual middle component. -/
      let S := PrefixFactorData.q10Skeleton_of_normalized
        D.swap hq hMiddleP.1 hMiddleP.2
      have hMiddle1 : 1 ∈ rootedDepthSupport T O.unitBridge.targetPort := by
        simpa [D, PrefixFactorData.swap] using S.P1
      have hMiddle4 : 4 ∈ rootedDepthSupport T O.unitBridge.targetPort := by
        simpa [D, PrefixFactorData.swap] using S.P4
      have hMiddle5 : 5 ∈ rootedDepthSupport T O.unitBridge.targetPort := by
        simpa [D, PrefixFactorData.swap] using S.P5
      have hOuter8 : 8 ∈ rootedDepthSupport T O.unitBridge.sourcePort := by
        simpa [D, PrefixFactorData.swap] using S.Q8
      let u1 := vertexAtDepth T O.unitBridge.targetPort 1
      let u4 := vertexAtDepth T O.unitBridge.targetPort 4
      let u5 := vertexAtDepth T O.unitBridge.targetPort 5
      let z8 := vertexAtDepth T O.unitBridge.sourcePort 8
      have hu1 : rho T u1 O.unitBridge.targetPort = 1 :=
        vertexAtDepth_spec T O.unitBridge.targetPort hMiddle1
      have hu4 : rho T u4 O.unitBridge.targetPort = 4 :=
        vertexAtDepth_spec T O.unitBridge.targetPort hMiddle4
      have hu5 : rho T u5 O.unitBridge.targetPort = 5 :=
        vertexAtDepth_spec T O.unitBridge.targetPort hMiddle5
      have hz8 : rho T z8 O.unitBridge.sourcePort = 8 :=
        vertexAtDepth_spec T O.unitBridge.sourcePort hOuter8
      have hu1ne : u1 ≠ O.unitBridge.targetPort := by
        intro heq
        rw [heq, rho_self] at hu1
        omega
      have hthirdZero : rho T O.secondBridge.targetPort y = 0 := by
        by_contra hne
        have hpos : 0 < rho T O.secondBridge.targetPort y :=
          Nat.pos_of_ne_zero hne
        have hyone : rho T O.secondBridge.targetPort y = 1 := by omega
        have hyne : O.secondBridge.targetPort ≠ y := by
          intro heq
          rw [← heq, rho_self] at hyone
          omega
        exfalso
        apply componentInternalRho_ne T hL
          O.middle_ne_secondOuter hu1ne hyne
        rw [hu1, hyone]
      have hxone : rho T x O.secondBridge.sourcePort = 1 := by omega
      have hxne : x ≠ O.secondBridge.sourcePort := by
        intro heq
        rw [heq, rho_self] at hxone
        omega
      have hsym :
          s(x.1, O.secondBridge.sourcePort.1) =
            s(u1.1, O.unitBridge.targetPort.1) := by
        apply internalRho_eq_implies_sym2 T hL hxne hu1ne
        rw [hxone, hu1]
      have hport : O.secondBridge.sourcePort = u1 := by
        rcases Sym2.eq_iff.mp hsym with h | h
        · exfalso
          apply O.ports_ne
          exact Subtype.ext h.2.symm
        · exact Subtype.ext h.2
      have h14 : rho T u1 u4 = 3 := by
        simpa [D, PrefixFactorData.swap, u1, u4] using
          S.P_dist_1_4
      have hsecondDepth : rho T u4 O.secondBridge.sourcePort = 3 := by
        rw [hport, rho_comm]
        exact h14
      apply actualCollision_of_unit_second W O z8 u5 u4
        O.secondBridge.targetPort
      rw [unitBridgePair_halfRank W O,
        secondBridgePair_halfRank W O, rho_self,
        rho_comm T O.unitBridge.targetPort u5, hu5,
        hz8, hsecondDepth, hq]

/-- Leech injectivity forbids an actual indexed odd-half-rank collision. -/
theorem no_actualOddHalfRankCollision
    {T : PosIntTree n} (hL : IsLeech T) :
    ¬ ActualOddHalfRankCollision T := by
  rintro ⟨x, y, hxy, hrank⟩
  apply hxy
  apply Subtype.ext
  apply hL.pairDist_injective
  have hxodd := x.2
  have hyodd := y.2
  omega

/-- Distinct actual middle ports exclude the audited q=8 case. -/
theorem graph_distinctPort_second_odd_q_ne_eight
    {T : PosIntTree n} (hL : IsLeech T) (W : GraphTwoOddWeights T)
    (hDistinct : DistinctMiddlePorts W)
    (hTarget : OddTargetThrough14 n) : W.q ≠ 8 := by
  intro hq
  let O := twoBridgeOrientation W hDistinct
  let D := prefixFactorDataOfOrientation hL W O
  let k9 : Fin 15 := ⟨9, by omega⟩
  have hfactor9 := oddTargetThrough14_linked_factorization
    hL W O hTarget k9
  have hnoFirst9 : ∀ {a b}, a ∈ D.P.support → b ∈ D.Q.support →
      a + b ≠ 9 :=
    PrefixFactorData.no_first_sum_nine_of_q_eight D hq
  rcases hfactor9 with hfirst9 | hsecond9
  · obtain ⟨x, y, _hpair, hsum⟩ := hfirst9
    have hxmem : rho T x O.unitBridge.sourcePort ∈ D.P.support := by
      change rho T x O.unitBridge.sourcePort ∈
        (prefixFactorDataOfOrientation hL W O).P.support
      rw [prefixFactorDataOfOrientation_P_support,
        rootedDepthSupport, Finset.mem_image]
      exact ⟨x, Finset.mem_univ _, rfl⟩
    have hymem : rho T O.unitBridge.targetPort y ∈ D.Q.support := by
      change rho T O.unitBridge.targetPort y ∈
        (prefixFactorDataOfOrientation hL W O).Q.support
      rw [prefixFactorDataOfOrientation_Q_support,
        rootedDepthSupport, Finset.mem_image]
      exact ⟨y, Finset.mem_univ _, rho_comm T y O.unitBridge.targetPort⟩
    exact hnoFirst9 hxmem hymem (by simpa [k9] using hsum)
  · obtain ⟨x9, y9, _hpair9, hsum9⟩ := hsecond9
    have hshift1 : rho T x9 O.secondBridge.sourcePort +
        rho T O.secondBridge.targetPort y9 = 1 := by
      dsimp only [k9] at hsum9
      omega
    rcases PrefixFactorData.normalized_self_or_swap D (by omega) with
        hOuterP | hMiddleP
    · /- If normalized P is unitOuter, either shifted summand one
         repeats its actual internal depth one. -/
      let z1 := vertexAtDepth T O.unitBridge.sourcePort 1
      have hz1mem : 1 ∈ rootedDepthSupport T O.unitBridge.sourcePort := by
        simpa [D] using hOuterP.1
      have hz1 : rho T z1 O.unitBridge.sourcePort = 1 :=
        vertexAtDepth_spec T O.unitBridge.sourcePort hz1mem
      have hz1ne : O.unitBridge.sourcePort ≠ z1 := by
        intro heq
        rw [← heq, rho_self] at hz1
        omega
      rcases (show
          rho T x9 O.secondBridge.sourcePort = 1 ∧
              rho T O.secondBridge.targetPort y9 = 0 ∨
            rho T x9 O.secondBridge.sourcePort = 0 ∧
              rho T O.secondBridge.targetPort y9 = 1 by omega) with h | h
      · have hxne : x9 ≠ O.secondBridge.sourcePort := by
          intro heq
          rw [heq, rho_self] at h
          omega
        apply componentInternalRho_ne T hL
          O.unitOuter_ne_middle.symm hxne hz1ne
        rw [h.1, rho_comm T O.unitBridge.sourcePort z1, hz1]
      · have hyne : O.secondBridge.targetPort ≠ y9 := by
          intro heq
          rw [← heq, rho_self] at h
          omega
        apply componentInternalRho_ne T hL
          O.unitOuter_ne_secondOuter hz1ne hyne
        rw [rho_comm T O.unitBridge.sourcePort z1, hz1, h.2]
    · /- Normalized P is the actual middle component. -/
      let S := PrefixFactorData.q8Skeleton_of_normalized
        D.swap hq hMiddleP.1 hMiddleP.2
      have hMiddle1 : 1 ∈ rootedDepthSupport T O.unitBridge.targetPort := by
        simpa [D, PrefixFactorData.swap] using S.P1
      have hMiddle4 : 4 ∈ rootedDepthSupport T O.unitBridge.targetPort := by
        simpa [D, PrefixFactorData.swap] using S.P4
      have hMiddle5 : 5 ∈ rootedDepthSupport T O.unitBridge.targetPort := by
        simpa [D, PrefixFactorData.swap] using S.P5
      have hOuter2 : 2 ∈ rootedDepthSupport T O.unitBridge.sourcePort := by
        simpa [D, PrefixFactorData.swap] using S.Q2
      let u1 := vertexAtDepth T O.unitBridge.targetPort 1
      let u4 := vertexAtDepth T O.unitBridge.targetPort 4
      let u5 := vertexAtDepth T O.unitBridge.targetPort 5
      let z2 := vertexAtDepth T O.unitBridge.sourcePort 2
      have hu1 : rho T u1 O.unitBridge.targetPort = 1 :=
        vertexAtDepth_spec T O.unitBridge.targetPort hMiddle1
      have hu4 : rho T u4 O.unitBridge.targetPort = 4 :=
        vertexAtDepth_spec T O.unitBridge.targetPort hMiddle4
      have hu5 : rho T u5 O.unitBridge.targetPort = 5 :=
        vertexAtDepth_spec T O.unitBridge.targetPort hMiddle5
      have hz2 : rho T z2 O.unitBridge.sourcePort = 2 :=
        vertexAtDepth_spec T O.unitBridge.sourcePort hOuter2
      have hu1neRoot : u1 ≠ O.unitBridge.targetPort := by
        intro heq
        rw [heq, rho_self] at hu1
        omega
      have hu4neRoot : O.unitBridge.targetPort ≠ u4 := by
        intro heq
        rw [← heq, rho_self] at hu4
        omega
      have hu5neRoot : O.unitBridge.targetPort ≠ u5 := by
        intro heq
        rw [← heq, rho_self] at hu5
        omega
      have hu1ne4 : u1 ≠ u4 := by
        intro heq
        have := congrArg (fun v : ComponentVertex T O.middle =>
          rho T v O.unitBridge.targetPort) heq
        change rho T u1 O.unitBridge.targetPort =
          rho T u4 O.unitBridge.targetPort at this
        omega
      have hu1ne5 : u1 ≠ u5 := by
        intro heq
        have := congrArg (fun v : ComponentVertex T O.middle =>
          rho T v O.unitBridge.targetPort) heq
        change rho T u1 O.unitBridge.targetPort =
          rho T u5 O.unitBridge.targetPort at this
        omega
      have hu4ne5 : u4 ≠ u5 := by
        intro heq
        have := congrArg (fun v : ComponentVertex T O.middle =>
          rho T v O.unitBridge.targetPort) heq
        change rho T u4 O.unitBridge.targetPort =
          rho T u5 O.unitBridge.targetPort at this
        omega
      have hz2neRoot : O.unitBridge.sourcePort ≠ z2 := by
        intro heq
        rw [← heq, rho_self] at hz2
        omega
      have hMiddleDepth : Function.Injective
          (fun v : ComponentVertex T O.middle =>
            rho T v O.unitBridge.targetPort) := by
        intro v v' hvv
        apply orientedTargetDepth_injective hL O.unitBridge
        simpa [rho_comm] using hvv

      /- Shifted unrank one identifies the actual second port with u1. -/
      have hthird0 : rho T O.secondBridge.targetPort y9 = 0 := by
        by_contra hne
        have hy1 : rho T O.secondBridge.targetPort y9 = 1 := by
          have hpos := Nat.pos_of_ne_zero hne
          omega
        have hyne : O.secondBridge.targetPort ≠ y9 := by
          intro heq
          rw [← heq, rho_self] at hy1
          omega
        apply componentInternalRho_ne T hL
          O.middle_ne_secondOuter hu1neRoot hyne
        rw [hu1, hy1]
      have hx9one : rho T x9 O.secondBridge.sourcePort = 1 := by omega
      have hx9ne : x9 ≠ O.secondBridge.sourcePort := by
        intro heq
        rw [heq, rho_self] at hx9one
        omega
      have hportSym :
          s(x9.1, O.secondBridge.sourcePort.1) =
            s(u1.1, O.unitBridge.targetPort.1) := by
        apply internalRho_eq_implies_sym2 T hL hx9ne hu1neRoot
        rw [hx9one, hu1]
      have hport : O.secondBridge.sourcePort = u1 := by
        rcases Sym2.eq_iff.mp hportSym with h | h
        · exfalso
          apply O.ports_ne
          exact Subtype.ext h.2.symm
        · exact Subtype.ext h.2
      have h14 : rho T u1 u4 = 3 := by
        simpa [D, PrefixFactorData.swap, u1, u4] using S.P_dist_1_4
      have h15 : rho T u1 u5 = 6 := by
        simpa [D, PrefixFactorData.swap, u1, u5] using S.P_dist_1_5
      have h45 : rho T u4 u5 = 9 := by
        simpa [D, PrefixFactorData.swap, u4, u5] using S.P_dist_4_5
      have hnew4 : rho T u4 O.secondBridge.sourcePort = 3 := by
        rw [hport, rho_comm]
        exact h14

      /- Rank ten cannot come from shifted unrank two. -/
      let k10 : Fin 15 := ⟨10, by omega⟩
      have hfactor10 := oddTargetThrough14_linked_factorization
        hL W O hTarget k10
      rcases hfactor10 with hfirst10 | hsecond10
      · obtain ⟨x10, y10, _hpair10, hsum10⟩ := hfirst10
        let a10 := rho T x10 O.unitBridge.sourcePort
        let b10 := rho T O.unitBridge.targetPort y10
        have hab10 : a10 + b10 = 10 := by
          simpa [k10, a10, b10] using hsum10
        have haD : a10 ∈ D.P.support := by
          change rho T x10 O.unitBridge.sourcePort ∈
            (prefixFactorDataOfOrientation hL W O).P.support
          rw [prefixFactorDataOfOrientation_P_support,
            rootedDepthSupport, Finset.mem_image]
          exact ⟨x10, Finset.mem_univ _, rfl⟩
        have hbD : b10 ∈ D.Q.support := by
          change rho T O.unitBridge.targetPort y10 ∈
            (prefixFactorDataOfOrientation hL W O).Q.support
          rw [prefixFactorDataOfOrientation_Q_support,
            rootedDepthSupport, Finset.mem_image]
          exact ⟨y10, Finset.mem_univ _,
            rho_comm T y10 O.unitBridge.targetPort⟩
        have haS : a10 ∈ (D.swap).Q.support := by
          simpa [PrefixFactorData.swap] using haD
        have hbS : b10 ∈ (D.swap).P.support := by
          simpa [PrefixFactorData.swap] using hbD
        have hroot10 :
            (a10 = 10 ∧ b10 = 0) ∨ (a10 = 0 ∧ b10 = 10) := by
          by_cases ha0 : a10 = 0
          · exact Or.inr ⟨ha0, by omega⟩
          by_cases hb0 : b10 = 0
          · exact Or.inl ⟨by omega, hb0⟩
          have haClass : a10 = 2 := by
            by_cases ha8 : a10 < 8
            · rcases S.Q_below8 ha8 haS with h0 | h2
              · exact (ha0 h0).elim
              · exact h2
            · have h89 : a10 = 8 ∨ a10 = 9 := by omega
              rcases h89 with h8 | h9
              · exact (S.Q8_not (h8 ▸ haS)).elim
              · exact (S.Q9_not (h9 ▸ haS)).elim
          have hbClass : b10 = 1 ∨ b10 = 4 ∨ b10 = 5 := by
            by_cases hb8 : b10 < 8
            · rcases S.P_below8 hb8 hbS with h0 | h1 | h4 | h5
              · exact (hb0 h0).elim
              · exact Or.inl h1
              · exact Or.inr (Or.inl h4)
              · exact Or.inr (Or.inr h5)
            · have h89 : b10 = 8 ∨ b10 = 9 := by omega
              rcases h89 with h8 | h9
              · exact (S.P8_not (h8 ▸ hbS)).elim
              · exact (S.P9_not (h9 ▸ hbS)).elim
          omega
        rcases hroot10 with hOuter10 | hMiddle10
        · /- An outer depth ten gives an explicit rank-eleven collision. -/
          have hcoll := actualCollision_of_unit_second W O x10 u1 u4
            O.secondBridge.targetPort (by
              rw [unitBridgePair_halfRank W O,
                secondBridgePair_halfRank W O, rho_self,
                rho_comm T O.unitBridge.targetPort u1, hu1,
                hnew4, hq]
              dsimp only [a10] at hOuter10
              omega)
          exact no_actualOddHalfRankCollision hL hcoll
        · /- The surviving placement is an actual middle depth ten. -/
          have hu10 : rho T y10 O.unitBridge.targetPort = 10 := by
            rw [rho_comm]
            dsimp only [b10] at hMiddle10
            exact hMiddle10.2
          have hbelow8 : ∀ v : ComponentVertex T O.middle,
              rho T v O.unitBridge.targetPort < 8 →
              rho T v O.unitBridge.targetPort = 0 ∨
                rho T v O.unitBridge.targetPort = 1 ∨
                rho T v O.unitBridge.targetPort = 4 ∨
                rho T v O.unitBridge.targetPort = 5 := by
            intro v hv
            have hmem : rho T v O.unitBridge.targetPort ∈
                rootedDepthSupport T O.unitBridge.targetPort := by
              rw [rootedDepthSupport, Finset.mem_image]
              exact ⟨v, Finset.mem_univ _, rfl⟩
            apply S.P_below8 hv
            simpa [D, PrefixFactorData.swap] using hmem
          obtain ⟨hd1_10, hd4_10, hd5_10⟩ :=
            q8_depthTen_actual_topology T hL
              O.unitBridge.targetPort u1 u4 u5 y10 hMiddleDepth
              hu1 hu4 hu5 hu10 h14 h15 h45 hbelow8
          have hy10ne1 : u1 ≠ y10 := by
            intro heq
            have := congrArg (fun v : ComponentVertex T O.middle =>
              rho T v O.unitBridge.targetPort) heq
            change rho T u1 O.unitBridge.targetPort =
              rho T y10 O.unitBridge.targetPort at this
            omega
          have hy10ne4 : u4 ≠ y10 := by
            intro heq
            have := congrArg (fun v : ComponentVertex T O.middle =>
              rho T v O.unitBridge.targetPort) heq
            change rho T u4 O.unitBridge.targetPort =
              rho T y10 O.unitBridge.targetPort at this
            omega
          have hy10ne5 : u5 ≠ y10 := by
            intro heq
            have := congrArg (fun v : ComponentVertex T O.middle =>
              rho T v O.unitBridge.targetPort) heq
            change rho T u5 O.unitBridge.targetPort =
              rho T y10 O.unitBridge.targetPort at this
            omega

          /- Rank thirteen has neither a shifted nor a first-product source. -/
          let k13 : Fin 15 := ⟨13, by omega⟩
          have hfactor13 := oddTargetThrough14_linked_factorization
            hL W O hTarget k13
          rcases hfactor13 with hfirst13 | hsecond13
          · obtain ⟨x13, y13, _hpair13, hsum13⟩ := hfirst13
            let a13 := rho T x13 O.unitBridge.sourcePort
            let b13 := rho T O.unitBridge.targetPort y13
            have hab13 : a13 + b13 = 13 := by
              simpa [k13, a13, b13] using hsum13
            have haD13 : a13 ∈ D.P.support := by
              change rho T x13 O.unitBridge.sourcePort ∈
                (prefixFactorDataOfOrientation hL W O).P.support
              rw [prefixFactorDataOfOrientation_P_support,
                rootedDepthSupport, Finset.mem_image]
              exact ⟨x13, Finset.mem_univ _, rfl⟩
            have hbD13 : b13 ∈ D.Q.support := by
              change rho T O.unitBridge.targetPort y13 ∈
                (prefixFactorDataOfOrientation hL W O).Q.support
              rw [prefixFactorDataOfOrientation_Q_support,
                rootedDepthSupport, Finset.mem_image]
              exact ⟨y13, Finset.mem_univ _,
                rho_comm T y13 O.unitBridge.targetPort⟩
            have haS13 : a13 ∈ (D.swap).Q.support := by
              simpa [PrefixFactorData.swap] using haD13
            have hbS13 : b13 ∈ (D.swap).P.support := by
              simpa [PrefixFactorData.swap] using hbD13
            have hMiddle10rooted : 10 ∈ rootedDepthSupport T
                O.unitBridge.targetPort := by
              rw [rootedDepthSupport, Finset.mem_image]
              exact ⟨y10, Finset.mem_univ _, hu10⟩
            have hMiddle10mem : 10 ∈ (D.swap).P.support := by
              simpa [D, PrefixFactorData.swap] using hMiddle10rooted
            have hcanonical10 :
                vertexAtDepth T O.unitBridge.targetPort 10 = y10 := by
              apply hMiddleDepth
              change rho T (vertexAtDepth T O.unitBridge.targetPort 10)
                O.unitBridge.targetPort =
                rho T y10 O.unitBridge.targetPort
              rw [vertexAtDepth_spec T O.unitBridge.targetPort
                hMiddle10rooted, hu10]
            have hroot13 :
                (a13 = 13 ∧ b13 = 0) ∨
                  (a13 = 0 ∧ b13 = 13) := by
              by_cases ha0 : a13 = 0
              · exact Or.inr ⟨ha0, by omega⟩
              by_cases hb0 : b13 = 0
              · exact Or.inl ⟨by omega, hb0⟩
              by_cases ha8 : a13 < 8
              · have ha2 : a13 = 2 := by
                  rcases S.Q_below8 ha8 haS13 with h0 | h2
                  · exact (ha0 h0).elim
                  · exact h2
                have hb11 : b13 = 11 := by omega
                have hdist0 : (D.swap).P.dist 0 b13 = 11 := by
                  rw [(D.swap).P.dist_zero_left hbS13]
                  omega
                have hdist110 : (D.swap).P.dist 1 10 = 11 := by
                  simp [D, PrefixFactorData.swap, hcanonical10]
                  exact hd1_10
                have hp := (D.swap).P_internal_injective
                  (D.swap).P.zero_mem hbS13 S.P1 hMiddle10mem
                  (by omega) (by omega) (hdist0.trans hdist110.symm)
                simp only [Sym2.eq_iff] at hp
                omega
              · have hb8 : b13 < 8 := by omega
                rcases S.P_below8 hb8 hbS13 with h0 | h1 | h4 | h5
                · exact (hb0 h0).elim
                · have ha12 : a13 = 12 := by omega
                  have hdup := (D.swap).direct
                    (D.swap).P.zero_mem haS13 hMiddle10mem S.Q2 (by omega)
                  omega
                · have ha9 : a13 = 9 := by omega
                  exact (S.Q9_not (ha9 ▸ haS13)).elim
                · have ha8eq : a13 = 8 := by omega
                  exact (S.Q8_not (ha8eq ▸ haS13)).elim
            rcases hroot13 with hOuter13 | hMiddle13
            · /- Outer depth 13: gate with outer depth 2 gives 15 or 11. -/
              have hx13depth : rho T x13 O.unitBridge.sourcePort = 13 := by
                dsimp only [a13] at hOuter13
                exact hOuter13.1
              have hx13ne2 : z2 ≠ x13 := by
                intro heq
                have := congrArg (fun v : ComponentVertex T O.unitOuter =>
                  rho T v O.unitBridge.sourcePort) heq
                change rho T z2 O.unitBridge.sourcePort =
                  rho T x13 O.unitBridge.sourcePort at this
                omega
              let G := strongRootGate T O.unitBridge.sourcePort.1 z2.1 x13.1
              let z := gateComponentVertex T O.unitBridge.sourcePort z2 x13 G
              have hzPath : z.1 ∈
                  (T.path z2.1 O.unitBridge.sourcePort.1).1.support := by
                simpa [z] using G.gate_mem_u
              have hsplit := rootedRho_split_at_path_vertex T
                O.unitBridge.sourcePort z2 z hzPath
              have hzle : rho T z O.unitBridge.sourcePort ≤ 2 := by
                rw [hz2] at hsplit
                omega
              have hzmem : rho T z O.unitBridge.sourcePort ∈
                  rootedDepthSupport T O.unitBridge.sourcePort := by
                rw [rootedDepthSupport, Finset.mem_image]
                exact ⟨z, Finset.mem_univ _, rfl⟩
              have hzClass := S.Q_below8
                (show rho T z O.unitBridge.sourcePort < 8 by omega) (by
                simpa [D, PrefixFactorData.swap] using hzmem)
              have hgate := strongRootGate_rho_identity T
                O.unitBridge.sourcePort z2 x13 G
              rcases hzClass with hz0 | hz2gate
              · have hd15 : rho T z2 x13 = 15 := by
                  rw [hz0, hz2, hx13depth] at hgate
                  omega
                apply componentInternalRho_ne T hL
                  O.unitOuter_ne_middle hx13ne2.symm hy10ne5
                rw [rho_comm T x13 z2, hd15, hd5_10]
              · have hd11 : rho T z2 x13 = 11 := by
                  rw [hz2gate, hz2, hx13depth] at hgate
                  omega
                apply componentInternalRho_ne T hL
                  O.unitOuter_ne_middle hx13ne2.symm hy10ne1
                rw [rho_comm T x13 z2, hd11, hd1_10]
            · /- Middle depth 13: two actual gates give 14, or 15/9. -/
              have hy13depth : rho T y13 O.unitBridge.targetPort = 13 := by
                rw [rho_comm]
                dsimp only [b13] at hMiddle13
                exact hMiddle13.2
              have hu1ne13 : u1 ≠ y13 := by
                intro heq
                have := congrArg (fun v : ComponentVertex T O.middle =>
                  rho T v O.unitBridge.targetPort) heq
                change rho T u1 O.unitBridge.targetPort =
                  rho T y13 O.unitBridge.targetPort at this
                omega
              have hu4ne13 : u4 ≠ y13 := by
                intro heq
                have := congrArg (fun v : ComponentVertex T O.middle =>
                  rho T v O.unitBridge.targetPort) heq
                change rho T u4 O.unitBridge.targetPort =
                  rho T y13 O.unitBridge.targetPort at this
                omega
              let G1 := strongRootGate T O.unitBridge.targetPort.1
                u1.1 y13.1
              let z1g := gateComponentVertex T O.unitBridge.targetPort
                u1 y13 G1
              have hz1Path : z1g.1 ∈
                  (T.path u1.1 O.unitBridge.targetPort.1).1.support := by
                simpa [z1g] using G1.gate_mem_u
              have hsplit1 := rootedRho_split_at_path_vertex T
                O.unitBridge.targetPort u1 z1g hz1Path
              have hz1le : rho T z1g O.unitBridge.targetPort ≤ 1 := by
                rw [hu1] at hsplit1
                omega
              have hz1Class := hbelow8 z1g (by omega)
              have hgate1 := strongRootGate_rho_identity T
                O.unitBridge.targetPort u1 y13 G1
              rcases hz1Class with hz0 | hz1 | hz4 | hz5
              · have hd14 : rho T u1 y13 = 14 := by
                  rw [hz0, hu1, hy13depth] at hgate1
                  omega
                have hs := internalRho_eq_implies_sym2 T hL
                  hu1ne13 hy10ne4 (hd14.trans hd4_10.symm)
                rcases Sym2.eq_iff.mp hs with h | h
                · have hu1eq4 : u1 = u4 := Subtype.ext h.1
                  exact hu1ne4 hu1eq4
                · have hu1eq10 : u1 = y10 := Subtype.ext h.1
                  exact hy10ne1 hu1eq10
              · have hd12 : rho T u1 y13 = 12 := by
                  rw [hz1, hu1, hy13depth] at hgate1
                  omega
                have hu1Path13 : u1.1 ∈
                    (T.path y13.1 O.unitBridge.targetPort.1).1.support := by
                  apply rootedRho_mem_path_of_sub T
                    O.unitBridge.targetPort u1 y13 hMiddleDepth
                  · omega
                  · omega
                  · omega
                have hu1Path4 : u1.1 ∈
                    (T.path u4.1 O.unitBridge.targetPort.1).1.support := by
                  apply rootedRho_mem_path_of_sub T
                    O.unitBridge.targetPort u1 u4 hMiddleDepth
                  · omega
                  · omega
                  · omega
                let G4 := strongRootGate T O.unitBridge.targetPort.1
                  u4.1 y13.1
                let z4g := gateComponentVertex T O.unitBridge.targetPort
                  u4 y13 G4
                have hz4Path : z4g.1 ∈
                    (T.path u4.1 O.unitBridge.targetPort.1).1.support := by
                  simpa [z4g] using G4.gate_mem_u
                have hsplit4 := rootedRho_split_at_path_vertex T
                  O.unitBridge.targetPort u4 z4g hz4Path
                have hz4le : rho T z4g O.unitBridge.targetPort ≤ 4 := by
                  rw [hu4] at hsplit4
                  omega
                have hz4Class := hbelow8 z4g (by omega)
                have hgate4 := strongRootGate_rho_identity T
                  O.unitBridge.targetPort u4 y13 G4
                rcases hz4Class with hz40 | hz41 | hz44 | hz45
                · have hzRoot : z4g = O.unitBridge.targetPort := by
                    apply hMiddleDepth
                    change rho T z4g O.unitBridge.targetPort =
                      rho T O.unitBridge.targetPort O.unitBridge.targetPort
                    rw [hz40, rho_self]
                  have hgateRoot : G4.gate = O.unitBridge.targetPort.1 := by
                    exact (gateComponentVertex_val T
                      O.unitBridge.targetPort u4 y13 G4).symm.trans
                      (congrArg Subtype.val hzRoot)
                  have hu1Root : u1 = O.unitBridge.targetPort := by
                    apply Subtype.ext
                    exact G4.common_eq_root hgateRoot hu1Path4 hu1Path13
                  exact hu1neRoot hu1Root
                · have hd15 : rho T u4 y13 = 15 := by
                    rw [hz41, hu4, hy13depth] at hgate4
                    omega
                  have hs := internalRho_eq_implies_sym2 T hL
                    hu4ne13 hy10ne5 (hd15.trans hd5_10.symm)
                  rcases Sym2.eq_iff.mp hs with h | h
                  · have hu4eq5 : u4 = u5 := Subtype.ext h.1
                    have := congrArg (fun v : ComponentVertex T O.middle =>
                      rho T v O.unitBridge.targetPort) hu4eq5
                    change rho T u4 O.unitBridge.targetPort =
                      rho T u5 O.unitBridge.targetPort at this
                    omega
                  · have hu4eq10 : u4 = y10 := Subtype.ext h.1
                    exact hy10ne4 hu4eq10
                · have hd9 : rho T u4 y13 = 9 := by
                    rw [hz44, hu4, hy13depth] at hgate4
                    omega
                  have hs := internalRho_eq_implies_sym2 T hL
                    hu4ne13 hu4ne5 (hd9.trans h45.symm)
                  rcases Sym2.eq_iff.mp hs with h | h
                  · have hy13eq5 : y13 = u5 := Subtype.ext h.2
                    have := congrArg (fun v : ComponentVertex T O.middle =>
                      rho T v O.unitBridge.targetPort) hy13eq5
                    change rho T y13 O.unitBridge.targetPort =
                      rho T u5 O.unitBridge.targetPort at this
                    omega
                  · have hu4eq5 : u4 = u5 := Subtype.ext h.1
                    have := congrArg (fun v : ComponentVertex T O.middle =>
                      rho T v O.unitBridge.targetPort) hu4eq5
                    change rho T u4 O.unitBridge.targetPort =
                      rho T u5 O.unitBridge.targetPort at this
                    omega
                · omega
              · omega
              · omega
          · obtain ⟨x13, y13, _hpair13, hsum13⟩ := hsecond13
            have hshift5 : rho T x13 O.secondBridge.sourcePort +
                rho T O.secondBridge.targetPort y13 = 5 := by
              dsimp only [k13] at hsum13
              omega
            let b := rho T O.secondBridge.targetPort y13
            by_cases hb0 : b = 0
            · have ha5 : rho T x13 O.secondBridge.sourcePort = 5 := by
                dsimp only [b] at hb0
                omega
              have hxne : x13 ≠ O.secondBridge.sourcePort := by
                intro heq
                rw [heq, rho_self] at ha5
                omega
              have hs : s(x13.1, O.secondBridge.sourcePort.1) =
                  s(O.unitBridge.targetPort.1, u5.1) := by
                apply internalRho_eq_implies_sym2 T hL hxne hu5neRoot
                rw [ha5, rho_comm T O.unitBridge.targetPort u5, hu5]
              rcases Sym2.eq_iff.mp hs with h | h
              · have hru5 : O.secondBridge.sourcePort = u5 :=
                  Subtype.ext h.2
                rw [hport] at hru5
                exact hu1ne5 hru5
              · apply O.ports_ne
                exact (Subtype.ext h.2).symm
            · have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
              have hble : b ≤ 5 := by omega
              have hyne : O.secondBridge.targetPort ≠ y13 := by
                intro heq
                have : b = 0 := by
                  dsimp only [b]
                  rw [← heq, rho_self]
                exact hb0 this
              have hbcases : b = 1 ∨ b = 2 ∨ b = 3 ∨
                  b = 4 ∨ b = 5 := by omega
              rcases hbcases with hb1 | hb2 | hb3 | hb4 | hb5
              · apply componentInternalRho_ne T hL
                  O.middle_ne_secondOuter hu1neRoot hyne
                rw [hu1]
                simpa [b] using hb1.symm
              · apply componentInternalRho_ne T hL
                  O.unitOuter_ne_secondOuter hz2neRoot hyne
                rw [rho_comm T O.unitBridge.sourcePort z2, hz2]
                simpa [b] using hb2.symm
              · apply componentInternalRho_ne T hL
                  O.middle_ne_secondOuter hu1ne4 hyne
                rw [h14]
                simpa [b] using hb3.symm
              · apply componentInternalRho_ne T hL
                  O.middle_ne_secondOuter hu4neRoot hyne
                rw [rho_comm T O.unitBridge.targetPort u4, hu4]
                simpa [b] using hb4.symm
              · apply componentInternalRho_ne T hL
                  O.middle_ne_secondOuter hu5neRoot hyne
                rw [rho_comm T O.unitBridge.targetPort u5, hu5]
                simpa [b] using hb5.symm
      · obtain ⟨x10, y10, _hpair10, hsum10⟩ := hsecond10
        have hshift2 : rho T x10 O.secondBridge.sourcePort +
            rho T O.secondBridge.targetPort y10 = 2 := by
          dsimp only [k10] at hsum10
          omega
        have hcases :
            (rho T x10 O.secondBridge.sourcePort = 2 ∧
              rho T O.secondBridge.targetPort y10 = 0) ∨
            (rho T x10 O.secondBridge.sourcePort = 1 ∧
              rho T O.secondBridge.targetPort y10 = 1) ∨
            (rho T x10 O.secondBridge.sourcePort = 0 ∧
              rho T O.secondBridge.targetPort y10 = 2) := by omega
        rcases hcases with h20 | h11 | h02
        · have hxne : x10 ≠ O.secondBridge.sourcePort := by
            intro heq
            rw [heq, rho_self] at h20
            omega
          apply componentInternalRho_ne T hL
            O.unitOuter_ne_middle.symm hxne hz2neRoot
          rw [h20.1, rho_comm T O.unitBridge.sourcePort z2, hz2]
        · have hxne : x10 ≠ O.secondBridge.sourcePort := by
            intro heq
            rw [heq, rho_self] at h11
            omega
          have hyne : O.secondBridge.targetPort ≠ y10 := by
            intro heq
            rw [← heq, rho_self] at h11
            omega
          apply componentInternalRho_ne T hL
            O.middle_ne_secondOuter hxne hyne
          rw [h11.1, h11.2]
        · have hyne : O.secondBridge.targetPort ≠ y10 := by
            intro heq
            rw [← heq, rho_self] at h02
            omega
          apply componentInternalRho_ne T hL
            O.unitOuter_ne_secondOuter hz2neRoot hyne
          rw [rho_comm T O.unitBridge.sourcePort z2, hz2, h02.2]

/-! ## Actual q=9 shifted-product and normalized-role closure -/

private theorem componentVertex_ne_of_rho_pos
    (T : PosIntTree n) {C : EvenComponent T}
    {x y : ComponentVertex T C} (h : 0 < rho T x y) : x ≠ y := by
  intro hxy
  subst y
  rw [rho_self] at h
  omega

/-- When the normalized q=9 component is the unit-outer component, shifted
unrank three has no source.  Every split repeats an already realized internal
distance in a different actual even component. -/
private theorem q9_outer_no_shifted_three
    {T : PosIntTree n} (hL : IsLeech T) {W : GraphTwoOddWeights T}
    (O : TwoBridgeOrientation W)
    (r p1 p4 : ComponentVertex T O.unitOuter)
    (h1 : rho T p1 r = 1) (h4 : rho T p4 r = 4)
    (h14 : rho T p1 p4 = 3)
    (x : ComponentVertex T O.middle)
    (y : ComponentVertex T O.secondOuter)
    (hsum : rho T x O.secondBridge.sourcePort +
      rho T O.secondBridge.targetPort y = 3) : False := by
  have hr1 : rho T r p1 = 1 := by simpa [rho_comm] using h1
  have hr4 : rho T r p4 = 4 := by simpa [rho_comm] using h4
  have hrp1 : r ≠ p1 := componentVertex_ne_of_rho_pos T (by omega)
  have hp14 : p1 ≠ p4 := componentVertex_ne_of_rho_pos T (by omega)
  rcases (show
      (rho T x O.secondBridge.sourcePort = 0 ∧
          rho T O.secondBridge.targetPort y = 3) ∨
      (rho T x O.secondBridge.sourcePort = 1 ∧
          rho T O.secondBridge.targetPort y = 2) ∨
      (rho T x O.secondBridge.sourcePort = 2 ∧
          rho T O.secondBridge.targetPort y = 1) ∨
      (rho T x O.secondBridge.sourcePort = 3 ∧
          rho T O.secondBridge.targetPort y = 0) by omega) with
      h | h | h | h
  · have hty : O.secondBridge.targetPort ≠ y :=
      componentVertex_ne_of_rho_pos T (by omega)
    apply componentInternalRho_ne T hL O.unitOuter_ne_secondOuter hp14 hty
    omega
  · have hxs : x ≠ O.secondBridge.sourcePort :=
      componentVertex_ne_of_rho_pos T (by omega)
    apply componentInternalRho_ne T hL O.unitOuter_ne_middle hrp1 hxs
    omega
  · have hty : O.secondBridge.targetPort ≠ y :=
      componentVertex_ne_of_rho_pos T (by omega)
    apply componentInternalRho_ne T hL O.unitOuter_ne_secondOuter hrp1 hty
    omega
  · have hxs : x ≠ O.secondBridge.sourcePort :=
      componentVertex_ne_of_rho_pos T (by omega)
    apply componentInternalRho_ne T hL O.unitOuter_ne_middle hp14 hxs
    omega

private theorem q9_outer_no_shifted_four
    {T : PosIntTree n} (hL : IsLeech T) {W : GraphTwoOddWeights T}
    (O : TwoBridgeOrientation W)
    (r p1 p4 : ComponentVertex T O.unitOuter)
    (h1 : rho T p1 r = 1) (h4 : rho T p4 r = 4)
    (x : ComponentVertex T O.middle)
    (y : ComponentVertex T O.secondOuter)
    (hsum : rho T x O.secondBridge.sourcePort +
      rho T O.secondBridge.targetPort y = 4) : False := by
  have hr1 : rho T r p1 = 1 := by simpa [rho_comm] using h1
  have hr4 : rho T r p4 = 4 := by simpa [rho_comm] using h4
  have hrp1 : r ≠ p1 := componentVertex_ne_of_rho_pos T (by omega)
  have hrp4 : r ≠ p4 := componentVertex_ne_of_rho_pos T (by omega)
  rcases (show
      (rho T x O.secondBridge.sourcePort = 0 ∧
          rho T O.secondBridge.targetPort y = 4) ∨
      (rho T x O.secondBridge.sourcePort = 1 ∧
          rho T O.secondBridge.targetPort y = 3) ∨
      (rho T x O.secondBridge.sourcePort = 2 ∧
          rho T O.secondBridge.targetPort y = 2) ∨
      (rho T x O.secondBridge.sourcePort = 3 ∧
          rho T O.secondBridge.targetPort y = 1) ∨
      (rho T x O.secondBridge.sourcePort = 4 ∧
          rho T O.secondBridge.targetPort y = 0) by omega) with
      h | h | h | h | h
  · have hty : O.secondBridge.targetPort ≠ y :=
      componentVertex_ne_of_rho_pos T (by omega)
    apply componentInternalRho_ne T hL O.unitOuter_ne_secondOuter hrp4 hty
    omega
  · have hxs : x ≠ O.secondBridge.sourcePort :=
      componentVertex_ne_of_rho_pos T (by omega)
    apply componentInternalRho_ne T hL O.unitOuter_ne_middle hrp1 hxs
    omega
  · have hxs : x ≠ O.secondBridge.sourcePort :=
      componentVertex_ne_of_rho_pos T (by omega)
    have hty : O.secondBridge.targetPort ≠ y :=
      componentVertex_ne_of_rho_pos T (by omega)
    apply componentInternalRho_ne T hL O.middle_ne_secondOuter hxs hty
    omega
  · have hty : O.secondBridge.targetPort ≠ y :=
      componentVertex_ne_of_rho_pos T (by omega)
    apply componentInternalRho_ne T hL O.unitOuter_ne_secondOuter hrp1 hty
    omega
  · have hxs : x ≠ O.secondBridge.sourcePort :=
      componentVertex_ne_of_rho_pos T (by omega)
    apply componentInternalRho_ne T hL O.unitOuter_ne_middle hrp4 hxs
    omega

private theorem q9_outer_no_shifted_five
    {T : PosIntTree n} (hL : IsLeech T) {W : GraphTwoOddWeights T}
    (O : TwoBridgeOrientation W)
    (r p1 p4 p5 : ComponentVertex T O.unitOuter)
    (h1 : rho T p1 r = 1) (h5 : rho T p5 r = 5)
    (h14 : rho T p1 p4 = 3)
    (x : ComponentVertex T O.middle)
    (y : ComponentVertex T O.secondOuter)
    (hsum : rho T x O.secondBridge.sourcePort +
      rho T O.secondBridge.targetPort y = 5) : False := by
  have hr1 : rho T r p1 = 1 := by simpa [rho_comm] using h1
  have hr5 : rho T r p5 = 5 := by simpa [rho_comm] using h5
  have hrp1 : r ≠ p1 := componentVertex_ne_of_rho_pos T (by omega)
  have hrp5 : r ≠ p5 := componentVertex_ne_of_rho_pos T (by omega)
  have hp14 : p1 ≠ p4 := componentVertex_ne_of_rho_pos T (by omega)
  rcases (show
      (rho T x O.secondBridge.sourcePort = 0 ∧
          rho T O.secondBridge.targetPort y = 5) ∨
      (rho T x O.secondBridge.sourcePort = 1 ∧
          rho T O.secondBridge.targetPort y = 4) ∨
      (rho T x O.secondBridge.sourcePort = 2 ∧
          rho T O.secondBridge.targetPort y = 3) ∨
      (rho T x O.secondBridge.sourcePort = 3 ∧
          rho T O.secondBridge.targetPort y = 2) ∨
      (rho T x O.secondBridge.sourcePort = 4 ∧
          rho T O.secondBridge.targetPort y = 1) ∨
      (rho T x O.secondBridge.sourcePort = 5 ∧
          rho T O.secondBridge.targetPort y = 0) by omega) with
      h | h | h | h | h | h
  · have hty : O.secondBridge.targetPort ≠ y :=
      componentVertex_ne_of_rho_pos T (by omega)
    apply componentInternalRho_ne T hL O.unitOuter_ne_secondOuter hrp5 hty
    omega
  · have hxs : x ≠ O.secondBridge.sourcePort :=
      componentVertex_ne_of_rho_pos T (by omega)
    apply componentInternalRho_ne T hL O.unitOuter_ne_middle hrp1 hxs
    omega
  · have hty : O.secondBridge.targetPort ≠ y :=
      componentVertex_ne_of_rho_pos T (by omega)
    apply componentInternalRho_ne T hL O.unitOuter_ne_secondOuter hp14 hty
    omega
  · have hxs : x ≠ O.secondBridge.sourcePort :=
      componentVertex_ne_of_rho_pos T (by omega)
    apply componentInternalRho_ne T hL O.unitOuter_ne_middle hp14 hxs
    omega
  · have hty : O.secondBridge.targetPort ≠ y :=
      componentVertex_ne_of_rho_pos T (by omega)
    apply componentInternalRho_ne T hL O.unitOuter_ne_secondOuter hrp1 hty
    omega
  · have hxs : x ≠ O.secondBridge.sourcePort :=
      componentVertex_ne_of_rho_pos T (by omega)
    apply componentInternalRho_ne T hL O.unitOuter_ne_middle hrp5 hxs
    omega

/-- In the outer-normalized role, shifted unrank two forces the second middle
port to be the already forced depth-two middle vertex. -/
private theorem q9_outer_shifted_two_forces_port
    {T : PosIntTree n} (hL : IsLeech T) {W : GraphTwoOddWeights T}
    (O : TwoBridgeOrientation W)
    (u2 : ComponentVertex T O.middle)
    (h2 : rho T u2 O.unitBridge.targetPort = 2)
    (x : ComponentVertex T O.middle)
    (y : ComponentVertex T O.secondOuter)
    (hsum : rho T x O.secondBridge.sourcePort +
      rho T O.secondBridge.targetPort y = 2) :
    O.secondBridge.sourcePort = u2 := by
  have hru2 : O.unitBridge.targetPort ≠ u2 := by
    intro h
    rw [← h, rho_self] at h2
    omega
  rcases (show
      (rho T x O.secondBridge.sourcePort = 0 ∧
          rho T O.secondBridge.targetPort y = 2) ∨
      (rho T x O.secondBridge.sourcePort = 1 ∧
          rho T O.secondBridge.targetPort y = 1) ∨
      (rho T x O.secondBridge.sourcePort = 2 ∧
          rho T O.secondBridge.targetPort y = 0) by omega) with h | h | h
  · have hty : O.secondBridge.targetPort ≠ y :=
      componentVertex_ne_of_rho_pos T (by omega)
    exfalso
    apply componentInternalRho_ne T hL O.middle_ne_secondOuter hru2 hty
    rw [rho_comm T O.unitBridge.targetPort u2, h2]
    omega
  · have hxs : x ≠ O.secondBridge.sourcePort :=
      componentVertex_ne_of_rho_pos T (by omega)
    have hty : O.secondBridge.targetPort ≠ y :=
      componentVertex_ne_of_rho_pos T (by omega)
    exfalso
    apply componentInternalRho_ne T hL O.middle_ne_secondOuter hxs hty
    omega
  · have hxs : x ≠ O.secondBridge.sourcePort :=
      componentVertex_ne_of_rho_pos T (by omega)
    have hsym :
        s(x.1, O.secondBridge.sourcePort.1) =
          s(O.unitBridge.targetPort.1, u2.1) := by
      apply internalRho_eq_implies_sym2 T hL hxs hru2
      rw [rho_comm T O.unitBridge.targetPort u2, h2]
      omega
    rcases Sym2.eq_iff.mp hsym with hpair | hpair
    · exact Subtype.ext hpair.2
    · exfalso
      apply O.ports_ne
      exact Subtype.ext hpair.2.symm

/-- In the middle-normalized role, shifted unrank two is impossible because
the other unit-edge factor already realizes internal half-distance two. -/
private theorem q9_middle_no_shifted_two
    {T : PosIntTree n} (hL : IsLeech T) {W : GraphTwoOddWeights T}
    (O : TwoBridgeOrientation W)
    (rO z2 : ComponentVertex T O.unitOuter)
    (h2 : rho T z2 rO = 2)
    (x : ComponentVertex T O.middle)
    (y : ComponentVertex T O.secondOuter)
    (hsum : rho T x O.secondBridge.sourcePort +
      rho T O.secondBridge.targetPort y = 2) : False := by
  have hO2 : rO ≠ z2 := by
    intro h
    rw [← h, rho_self] at h2
    omega
  rcases (show
      (rho T x O.secondBridge.sourcePort = 0 ∧
          rho T O.secondBridge.targetPort y = 2) ∨
      (rho T x O.secondBridge.sourcePort = 1 ∧
          rho T O.secondBridge.targetPort y = 1) ∨
      (rho T x O.secondBridge.sourcePort = 2 ∧
          rho T O.secondBridge.targetPort y = 0) by omega) with h | h | h
  · have hty : O.secondBridge.targetPort ≠ y :=
      componentVertex_ne_of_rho_pos T (by omega)
    apply componentInternalRho_ne T hL O.unitOuter_ne_secondOuter hO2 hty
    rw [rho_comm T rO z2, h2]
    omega
  · have hxs : x ≠ O.secondBridge.sourcePort :=
      componentVertex_ne_of_rho_pos T (by omega)
    have hty : O.secondBridge.targetPort ≠ y :=
      componentVertex_ne_of_rho_pos T (by omega)
    apply componentInternalRho_ne T hL O.middle_ne_secondOuter hxs hty
    omega
  · have hxs : x ≠ O.secondBridge.sourcePort :=
      componentVertex_ne_of_rho_pos T (by omega)
    apply componentInternalRho_ne T hL O.unitOuter_ne_middle hO2 hxs
    rw [rho_comm T rO z2, h2]
    omega

/-- In the middle-normalized role, shifted unrank three identifies the second
middle port with one of the two endpoints of the unique internal distance
three, namely the old depth-one or depth-four vertex. -/
private theorem q9_middle_shifted_three_port_cases
    {T : PosIntTree n} (hL : IsLeech T) {W : GraphTwoOddWeights T}
    (O : TwoBridgeOrientation W)
    (u1 u4 : ComponentVertex T O.middle)
    (rO z2 : ComponentVertex T O.unitOuter)
    (h2 : rho T z2 rO = 2)
    (h14 : rho T u1 u4 = 3)
    (x : ComponentVertex T O.middle)
    (y : ComponentVertex T O.secondOuter)
    (hsum : rho T x O.secondBridge.sourcePort +
      rho T O.secondBridge.targetPort y = 3) :
    O.secondBridge.sourcePort = u1 ∨ O.secondBridge.sourcePort = u4 := by
  have hO2 : rO ≠ z2 := by
    intro h
    rw [← h, rho_self] at h2
    omega
  have h14ne : u1 ≠ u4 := componentVertex_ne_of_rho_pos T (by omega)
  rcases (show
      (rho T x O.secondBridge.sourcePort = 0 ∧
          rho T O.secondBridge.targetPort y = 3) ∨
      (rho T x O.secondBridge.sourcePort = 1 ∧
          rho T O.secondBridge.targetPort y = 2) ∨
      (rho T x O.secondBridge.sourcePort = 2 ∧
          rho T O.secondBridge.targetPort y = 1) ∨
      (rho T x O.secondBridge.sourcePort = 3 ∧
          rho T O.secondBridge.targetPort y = 0) by omega) with
      h | h | h | h
  · have hty : O.secondBridge.targetPort ≠ y :=
      componentVertex_ne_of_rho_pos T (by omega)
    exfalso
    apply componentInternalRho_ne T hL O.middle_ne_secondOuter h14ne hty
    omega
  · have hxs : x ≠ O.secondBridge.sourcePort :=
      componentVertex_ne_of_rho_pos T (by omega)
    have hty : O.secondBridge.targetPort ≠ y :=
      componentVertex_ne_of_rho_pos T (by omega)
    exfalso
    apply componentInternalRho_ne T hL O.unitOuter_ne_secondOuter hO2 hty
    rw [rho_comm T rO z2, h2]
    omega
  · have hxs : x ≠ O.secondBridge.sourcePort :=
      componentVertex_ne_of_rho_pos T (by omega)
    exfalso
    apply componentInternalRho_ne T hL O.unitOuter_ne_middle hO2 hxs
    rw [rho_comm T rO z2, h2]
    omega
  · have hxs : x ≠ O.secondBridge.sourcePort :=
      componentVertex_ne_of_rho_pos T (by omega)
    have hsym :
        s(x.1, O.secondBridge.sourcePort.1) = s(u1.1, u4.1) := by
      apply internalRho_eq_implies_sym2 T hL hxs h14ne
      omega
    rcases Sym2.eq_iff.mp hsym with hp | hp
    · exact Or.inr (Subtype.ext hp.2)
    · exact Or.inl (Subtype.ext hp.2)

/-! ## The two actual normalized roles -/

private theorem q9_outer_normalized_false
    {T : PosIntTree n} (hL : IsLeech T) (W : GraphTwoOddWeights T)
    (O : TwoBridgeOrientation W) (hTarget : OddTargetThrough14 n)
    (hq : W.q = 9)
    (hNorm :
      1 ∈ (prefixFactorDataOfOrientation hL W O).P.support ∧
      1 ∉ (prefixFactorDataOfOrientation hL W O).Q.support) : False := by
  let D := prefixFactorDataOfOrientation hL W O
  let S := PrefixFactorData.q9Skeleton_of_normalized D hq hNorm.1 hNorm.2
  let rP := O.unitBridge.sourcePort
  let rQ := O.unitBridge.targetPort
  let p1 := vertexAtDepth T rP 1
  let p4 := vertexAtDepth T rP 4
  let p5 := vertexAtDepth T rP 5
  let p8 := vertexAtDepth T rP 8
  let q2 := vertexAtDepth T rQ 2
  have hPdepth : Function.Injective
      (fun x : ComponentVertex T O.unitOuter => rho T x rP) := by
    simpa [rP] using orientedSourceDepth_injective hL O.unitBridge
  have htop := q9_actual_dist_four_eight_and_five_eight T rP hPdepth D
    (by
      simp [D, rP])
    (fun a b => by
      simp [D, rP])
    S
  have hp1mem : 1 ∈ rootedDepthSupport T rP := by
    simpa [D, rP] using S.P1
  have hp4mem : 4 ∈ rootedDepthSupport T rP := by
    simpa [D, rP] using S.P4
  have hp5mem : 5 ∈ rootedDepthSupport T rP := by
    simpa [D, rP] using S.P5
  have hp8mem : 8 ∈ rootedDepthSupport T rP := by
    simpa [D, rP] using S.P8
  have hq2mem : 2 ∈ rootedDepthSupport T rQ := by
    simpa [D, rQ] using S.Q2
  have hp1 : rho T p1 rP = 1 := vertexAtDepth_spec T rP hp1mem
  have hp4 : rho T p4 rP = 4 := vertexAtDepth_spec T rP hp4mem
  have hp5 : rho T p5 rP = 5 := vertexAtDepth_spec T rP hp5mem
  have hp8 : rho T p8 rP = 8 := vertexAtDepth_spec T rP hp8mem
  have hq2 : rho T q2 rQ = 2 := vertexAtDepth_spec T rQ hq2mem
  have hp14 : rho T p1 p4 = 3 := by
    simpa [D, rP, p1, p4] using S.P_dist_1_4
  have hp48 : rho T p4 p8 = 10 := by
    simpa [rP, p4, p8] using htop.1
  have hp58 : rho T p5 p8 = 13 := by
    simpa [rP, p5, p8] using htop.2
  have hDP48 : D.P.dist 4 8 = 10 := by
    calc
      D.P.dist 4 8 = rho T p4 p8 := by
        simp [D, rP, p4, p8]
      _ = 10 := hp48
  have hDP58 : D.P.dist 5 8 = 13 := by
    calc
      D.P.dist 5 8 = rho T p5 p8 := by
        simp [D, rP, p5, p8]
      _ = 13 := hp58
  have hQ11 : 11 ∉ D.Q.support := q9_Q11_not D S hDP58
  have memP (x : ComponentVertex T O.unitOuter) :
      rho T x rP ∈ D.P.support := by
    change rho T x rP ∈
      (prefixFactorDataOfOrientation hL W O).P.support
    rw [prefixFactorDataOfOrientation_P_support,
      rootedDepthSupport, Finset.mem_image]
    exact ⟨x, Finset.mem_univ _, rfl⟩
  have memQ (x : ComponentVertex T O.middle) :
      rho T rQ x ∈ D.Q.support := by
    change rho T rQ x ∈
      (prefixFactorDataOfOrientation hL W O).Q.support
    rw [prefixFactorDataOfOrientation_Q_support,
      rootedDepthSupport, Finset.mem_image]
    exact ⟨x, Finset.mem_univ _, rho_comm T x rQ⟩

  let k11 : Fin 15 := ⟨11, by omega⟩
  have hfactor11 := oddTargetThrough14_linked_factorization
    hL W O hTarget k11
  rcases hfactor11 with hfirst11 | hsecond11
  · obtain ⟨x11, y11, _hpair11, hsum11⟩ := hfirst11
    have hx11 := memP x11
    have hy11 := memQ y11
    have hroots := q9_sum_eleven_roots D S hx11 hy11
      (by simpa [k11, rP, rQ] using hsum11)
    rcases hroots with hPcase | hQcase
    · have hP11 : 11 ∈ D.P.support := by simpa [hPcase.1] using hx11
      obtain ⟨z, hz, hz1, hz11, hgate⟩ := D.P.gate S.P1 hP11
      have hzCases : z = 0 ∨ z = 1 := by
        have hzClass := S.P_below8 (by omega) hz
        rcases hzClass with h | h | h | h <;> omega
      have hP1_11 : D.P.dist 1 11 = 12 := by
        rcases hzCases with rfl | rfl
        · omega
        · have hbad : D.P.dist 1 11 = 10 := by omega
          have hpairs := D.P_internal_injective S.P1 hP11 S.P4 S.P8
            (by omega) (by omega) (by rw [hbad, hDP48])
          simp only [Sym2.eq_iff] at hpairs
          omega
      let k12 : Fin 15 := ⟨12, by omega⟩
      have hfactor12 := oddTargetThrough14_linked_factorization
        hL W O hTarget k12
      rcases hfactor12 with hfirst12 | hsecond12
      · obtain ⟨x12, y12, _hpair12, hsum12⟩ := hfirst12
        have hx12 := memP x12
        have hy12 := memQ y12
        have hroots12 := q9_sum_twelve_roots D S hQ11 hx12 hy12
          (by simpa [k12, rP, rQ] using hsum12)
        rcases hroots12 with hP12case | hQ12case
        · have hP12 : 12 ∈ D.P.support := by
            simpa [hP12case.1] using hx12
          have hdup := D.P_internal_injective D.P.zero_mem hP12
            S.P1 hP11 (by omega) (by omega) (by
              rw [D.P.dist_zero_left hP12, hP1_11])
          simp only [Sym2.eq_iff] at hdup
          omega
        · have hQ12 : 12 ∈ D.Q.support := by
            simpa [hQ12case.2] using hy12
          exact (D.internal_disjoint S.P1 hP11 D.Q.zero_mem hQ12
            (by omega) (by omega) (by
              rw [hP1_11, D.Q.dist_zero_left hQ12])).elim
      · obtain ⟨x12, y12, _hpair12, hsum12⟩ := hsecond12
        apply q9_outer_no_shifted_three hL O rP p1 p4 hp1 hp4 hp14
          x12 y12
        dsimp only [k12] at hsum12
        omega
    · have : 11 ∈ D.Q.support := by simpa [hQcase.2] using hy11
      exact hQ11 this
  · obtain ⟨x11, y11, _hpair11, hsum11⟩ := hsecond11
    have hshift11 : rho T x11 O.secondBridge.sourcePort +
        rho T O.secondBridge.targetPort y11 = 2 := by
      dsimp only [k11] at hsum11
      omega
    have hport : O.secondBridge.sourcePort = q2 :=
      q9_outer_shifted_two_forces_port hL O q2 hq2 x11 y11 hshift11
    let k12 : Fin 15 := ⟨12, by omega⟩
    have hfactor12 := oddTargetThrough14_linked_factorization
      hL W O hTarget k12
    rcases hfactor12 with hfirst12 | hsecond12
    · obtain ⟨x12, y12, _hpair12, hsum12⟩ := hfirst12
      have hx12 := memP x12
      have hy12 := memQ y12
      have hroots12 := q9_sum_twelve_roots D S hQ11 hx12 hy12
        (by simpa [k12, rP, rQ] using hsum12)
      rcases hroots12 with hP12case | hQ12case
      · have hP12 : 12 ∈ D.P.support := by
          simpa [hP12case.1] using hx12
        have hQ12 : 12 ∉ D.Q.support := by
          intro h
          have hdup := D.direct hP12 D.Q.zero_mem D.P.zero_mem h (by omega)
          omega
        have hP11 : 11 ∉ D.P.support := by
          intro h
          let p11 := vertexAtDepth T rP 11
          have hp11mem : 11 ∈ rootedDepthSupport T rP := by
            simpa [D, rP] using h
          have hp11 : rho T p11 rP = 11 :=
            vertexAtDepth_spec T rP hp11mem
          apply no_actualOddHalfRankCollision hL
          apply actualCollision_of_unit_second W O p11 rQ x11 y11
          rw [unitBridgePair_halfRank W O,
            secondBridgePair_halfRank W O, rho_self, hp11]
          dsimp only [k11] at hsum11
          omega
        let k13 : Fin 15 := ⟨13, by omega⟩
        have hfactor13 := oddTargetThrough14_linked_factorization
          hL W O hTarget k13
        rcases hfactor13 with hfirst13 | hsecond13
        · obtain ⟨x13, y13, _hpair13, hsum13⟩ := hfirst13
          have hx13 := memP x13
          have hy13 := memQ y13
          have hroots13 := q9_sum_thirteen_roots_of_P12
            D S hP11 hQ11 hP12 hQ12 hx13 hy13
            (by simpa [k13, rP, rQ] using hsum13)
          rcases hroots13 with hP13case | hQ13case
          · have hP13 : 13 ∈ D.P.support := by
              simpa [hP13case.1] using hx13
            have hdup := D.P_internal_injective D.P.zero_mem hP13
              S.P5 S.P8 (by omega) (by omega) (by
                rw [D.P.dist_zero_left hP13, hDP58])
            simp only [Sym2.eq_iff] at hdup
            omega
          · have hQ13 : 13 ∈ D.Q.support := by
              simpa [hQ13case.2] using hy13
            exact (D.internal_disjoint S.P5 S.P8 D.Q.zero_mem hQ13
              (by omega) (by omega) (by
                rw [hDP58, D.Q.dist_zero_left hQ13])).elim
        · obtain ⟨x13, y13, _hpair13, hsum13⟩ := hsecond13
          apply q9_outer_no_shifted_four hL O rP p1 p4 hp1 hp4
            x13 y13
          dsimp only [k13] at hsum13
          omega
      · have hQ12 : 12 ∈ D.Q.support := by
          simpa [hQ12case.2] using hy12
        have hP12 : 12 ∉ D.P.support := by
          intro h
          have hdup := D.direct h D.Q.zero_mem D.P.zero_mem hQ12 (by omega)
          omega
        have hQ13 : 13 ∉ D.Q.support := by
          intro h
          have hdup := D.direct S.P1 hQ12 D.P.zero_mem h (by omega)
          omega
        obtain ⟨z, hz, hz2, hz12, hgate⟩ := D.Q.gate S.Q2 hQ12
        have hzCases : z = 0 ∨ z = 2 := by
          have hzClass := S.Q_below8 (by omega) hz
          rcases hzClass with h | h <;> omega
        have hQ2_12 : D.Q.dist 2 12 = 14 := by
          rcases hzCases with rfl | rfl
          · omega
          · have hbad : D.Q.dist 2 12 = 10 := by omega
            exact (D.internal_disjoint S.P4 S.P8 S.Q2 hQ12
              (by omega) (by omega) (by rw [hDP48, hbad])).elim
        let k14 : Fin 15 := ⟨14, by omega⟩
        have hfactor14 := oddTargetThrough14_linked_factorization
          hL W O hTarget k14
        rcases hfactor14 with hfirst14 | hsecond14
        · obtain ⟨x14, y14, _hpair14, hsum14⟩ := hfirst14
          have hx14 := memP x14
          have hy14 := memQ y14
          have hroots14 := q9_sum_fourteen_roots_of_Q12
            D S hQ11 hP12 hQ12 hQ13 hx14 hy14
            (by simpa [k14, rP, rQ] using hsum14)
          rcases hroots14 with hP14case | hQ14case
          · have hP14 : 14 ∈ D.P.support := by
              simpa [hP14case.1] using hx14
            exact (D.internal_disjoint D.P.zero_mem hP14 S.Q2 hQ12
              (by omega) (by omega) (by
                rw [D.P.dist_zero_left hP14, hQ2_12])).elim
          · have hQ14 : 14 ∈ D.Q.support := by
              simpa [hQ14case.2] using hy14
            have hdup := D.Q_internal_injective D.Q.zero_mem hQ14
              S.Q2 hQ12 (by omega) (by omega) (by
                rw [D.Q.dist_zero_left hQ14, hQ2_12])
            simp only [Sym2.eq_iff] at hdup
            omega
        · obtain ⟨x14, y14, _hpair14, hsum14⟩ := hsecond14
          apply q9_outer_no_shifted_five hL O rP p1 p4 p5
            hp1 hp5 hp14 x14 y14
          dsimp only [k14] at hsum14
          omega
    · obtain ⟨x12, y12, _hpair12, hsum12⟩ := hsecond12
      apply q9_outer_no_shifted_three hL O rP p1 p4 hp1 hp4 hp14
        x12 y12
      dsimp only [k12] at hsum12
      omega

private theorem q9_middle_normalized_false
    {T : PosIntTree n} (hL : IsLeech T) (W : GraphTwoOddWeights T)
    (O : TwoBridgeOrientation W) (hTarget : OddTargetThrough14 n)
    (hq : W.q = 9)
    (hNorm :
      1 ∈ (prefixFactorDataOfOrientation hL W O).Q.support ∧
      1 ∉ (prefixFactorDataOfOrientation hL W O).P.support) : False := by
  let D := prefixFactorDataOfOrientation hL W O
  let E := D.swap
  have hNormE : 1 ∈ E.P.support ∧ 1 ∉ E.Q.support := by
    simpa [E, PrefixFactorData.swap] using hNorm
  let S := PrefixFactorData.q9Skeleton_of_normalized E hq hNormE.1 hNormE.2
  let rP := O.unitBridge.sourcePort
  let rQ := O.unitBridge.targetPort
  let u1 := vertexAtDepth T rQ 1
  let u4 := vertexAtDepth T rQ 4
  let u5 := vertexAtDepth T rQ 5
  let u8 := vertexAtDepth T rQ 8
  let z2 := vertexAtDepth T rP 2
  have hQdepth : Function.Injective
      (fun x : ComponentVertex T O.middle => rho T x rQ) := by
    intro x y hxy
    apply orientedTargetDepth_injective hL O.unitBridge
    simpa [rQ, rho_comm] using hxy
  have htop := q9_actual_dist_four_eight_and_five_eight T rQ hQdepth E
    (by
      simp [E, D, PrefixFactorData.swap, rQ])
    (fun a b => by
      simp [E, D, PrefixFactorData.swap, rQ])
    S
  have hu1mem : 1 ∈ rootedDepthSupport T rQ := by
    simpa [E, D, PrefixFactorData.swap, rQ] using S.P1
  have hu4mem : 4 ∈ rootedDepthSupport T rQ := by
    simpa [E, D, PrefixFactorData.swap, rQ] using S.P4
  have hu5mem : 5 ∈ rootedDepthSupport T rQ := by
    simpa [E, D, PrefixFactorData.swap, rQ] using S.P5
  have hu8mem : 8 ∈ rootedDepthSupport T rQ := by
    simpa [E, D, PrefixFactorData.swap, rQ] using S.P8
  have hz2mem : 2 ∈ rootedDepthSupport T rP := by
    simpa [E, D, PrefixFactorData.swap, rP] using S.Q2
  have hu1 : rho T u1 rQ = 1 := vertexAtDepth_spec T rQ hu1mem
  have hu4 : rho T u4 rQ = 4 := vertexAtDepth_spec T rQ hu4mem
  have hu5 : rho T u5 rQ = 5 := vertexAtDepth_spec T rQ hu5mem
  have hu8 : rho T u8 rQ = 8 := vertexAtDepth_spec T rQ hu8mem
  have hz2 : rho T z2 rP = 2 := vertexAtDepth_spec T rP hz2mem
  have hu14 : rho T u1 u4 = 3 := by
    simpa [E, D, PrefixFactorData.swap, rQ, u1, u4] using S.P_dist_1_4
  have hu48 : rho T u4 u8 = 10 := by
    simpa [rQ, u4, u8] using htop.1
  have hu58 : rho T u5 u8 = 13 := by
    simpa [rQ, u5, u8] using htop.2
  have hEP48 : E.P.dist 4 8 = 10 := by
    calc
      E.P.dist 4 8 = rho T u4 u8 := by
        simp [E, D, PrefixFactorData.swap, rQ, u4, u8]
      _ = 10 := hu48
  have hEP58 : E.P.dist 5 8 = 13 := by
    calc
      E.P.dist 5 8 = rho T u5 u8 := by
        simp [E, D, PrefixFactorData.swap, rQ, u5, u8]
      _ = 13 := hu58
  have hEQ11 : 11 ∉ E.Q.support := q9_Q11_not E S hEP58
  have memEP (x : ComponentVertex T O.middle) :
      rho T rQ x ∈ E.P.support := by
    change rho T rQ x ∈
      (prefixFactorDataOfOrientation hL W O).Q.support
    rw [prefixFactorDataOfOrientation_Q_support,
      rootedDepthSupport, Finset.mem_image]
    exact ⟨x, Finset.mem_univ _, rho_comm T x rQ⟩
  have memEQ (x : ComponentVertex T O.unitOuter) :
      rho T x rP ∈ E.Q.support := by
    change rho T x rP ∈
      (prefixFactorDataOfOrientation hL W O).P.support
    rw [prefixFactorDataOfOrientation_P_support,
      rootedDepthSupport, Finset.mem_image]
    exact ⟨x, Finset.mem_univ _, rfl⟩

  let k11 : Fin 15 := ⟨11, by omega⟩
  have hfactor11 := oddTargetThrough14_linked_factorization
    hL W O hTarget k11
  rcases hfactor11 with hfirst11 | hsecond11
  · obtain ⟨x11, y11, _hpair11, hsum11⟩ := hfirst11
    have hx11 := memEQ x11
    have hy11 := memEP y11
    change rho T x11 rP + rho T rQ y11 = 11 at hsum11
    have hroots := q9_sum_eleven_roots E S hy11 hx11
      (by omega)
    rcases hroots with hPcase | hQcase
    · have hEP11 : 11 ∈ E.P.support := by
        simpa [hPcase.1] using hy11
      obtain ⟨z, hz, hz1, hz11, hgate⟩ := E.P.gate S.P1 hEP11
      have hzCases : z = 0 ∨ z = 1 := by
        have hzClass := S.P_below8 (by omega) hz
        rcases hzClass with h | h | h | h <;> omega
      have hEP1_11 : E.P.dist 1 11 = 12 := by
        rcases hzCases with rfl | rfl
        · omega
        · have hbad : E.P.dist 1 11 = 10 := by omega
          have hpairs := E.P_internal_injective S.P1 hEP11 S.P4 S.P8
            (by omega) (by omega) (by rw [hbad, hEP48])
          simp only [Sym2.eq_iff] at hpairs
          omega
      let k12 : Fin 15 := ⟨12, by omega⟩
      have hfactor12 := oddTargetThrough14_linked_factorization
        hL W O hTarget k12
      rcases hfactor12 with hfirst12 | hsecond12
      · obtain ⟨x12, y12, _hpair12, hsum12⟩ := hfirst12
        have hx12 := memEQ x12
        have hy12 := memEP y12
        change rho T x12 rP + rho T rQ y12 = 12 at hsum12
        have hroots12 := q9_sum_twelve_roots E S hEQ11 hy12 hx12
          (by omega)
        rcases hroots12 with hP12case | hQ12case
        · have hEP12 : 12 ∈ E.P.support := by
            simpa [hP12case.1] using hy12
          have hdup := E.P_internal_injective E.P.zero_mem hEP12
            S.P1 hEP11 (by omega) (by omega) (by
              rw [E.P.dist_zero_left hEP12, hEP1_11])
          simp only [Sym2.eq_iff] at hdup
          omega
        · have hEQ12 : 12 ∈ E.Q.support := by
            simpa [hQ12case.2] using hx12
          exact (E.internal_disjoint S.P1 hEP11 E.Q.zero_mem hEQ12
            (by omega) (by omega) (by
              rw [hEP1_11, E.Q.dist_zero_left hEQ12])).elim
      · obtain ⟨x12, y12, _hpair12, hsum12⟩ := hsecond12
        have hshift12 : rho T x12 O.secondBridge.sourcePort +
            rho T O.secondBridge.targetPort y12 = 3 := by
          dsimp only [k12] at hsum12
          omega
        have hports := q9_middle_shifted_three_port_cases hL O
          u1 u4 rP z2 hz2 hu14 x12 y12 hshift12
        let u11 := vertexAtDepth T rQ 11
        have hu11mem : 11 ∈ rootedDepthSupport T rQ := by
          simpa [E, D, PrefixFactorData.swap, rQ] using hEP11
        have hu11 : rho T u11 rQ = 11 :=
          vertexAtDepth_spec T rQ hu11mem
        rcases hports with hport1 | hport4
        · apply no_actualOddHalfRankCollision hL
          apply actualCollision_of_unit_second W O z2 u8 rQ
            O.secondBridge.targetPort
          rw [unitBridgePair_halfRank W O,
            secondBridgePair_halfRank W O, rho_self,
            hz2, hport1, hq,
            rho_comm T rQ u8, hu8,
            rho_comm T rQ u1, hu1]
        · apply no_actualOddHalfRankCollision hL
          apply actualCollision_of_unit_second W O z2 u11 rQ
            O.secondBridge.targetPort
          rw [unitBridgePair_halfRank W O,
            secondBridgePair_halfRank W O, rho_self,
            hz2, hport4, hq,
            rho_comm T rQ u11, hu11,
            rho_comm T rQ u4, hu4]
    · have : 11 ∈ E.Q.support := by simpa [hQcase.2] using hx11
      exact hEQ11 this
  · obtain ⟨x11, y11, _hpair11, hsum11⟩ := hsecond11
    have hshift11 : rho T x11 O.secondBridge.sourcePort +
        rho T O.secondBridge.targetPort y11 = 2 := by
      dsimp only [k11] at hsum11
      omega
    exact q9_middle_no_shifted_two hL O rP z2 hz2
      x11 y11 hshift11

/-- Oriented actual-tree exclusion of the distinct-port `q=9` case.  Its
only premises are the actual Leech tree, actual named physical bridges with
distinct middle ports retained by `O`, and the actual odd target through
rank 14. -/
theorem oriented_distinctPort_second_odd_q_ne_nine
    {T : PosIntTree n} (hL : IsLeech T) (W : GraphTwoOddWeights T)
    (O : TwoBridgeOrientation W) (hTarget : OddTargetThrough14 n) :
    W.q ≠ 9 := by
  intro hq
  let D := prefixFactorDataOfOrientation hL W O
  rcases PrefixFactorData.normalized_self_or_swap D (by omega) with
      hOuter | hMiddle
  · apply q9_outer_normalized_false hL W O hTarget hq
    simpa [D] using hOuter
  · apply q9_middle_normalized_false hL W O hTarget hq
    simpa [D] using hMiddle

/-- Graph-facing actual-tree exclusion.  The orientation and its distinct
actual middle ports are constructed from the physical distinct-port
hypothesis; no collision ledger or factor-extraction premise occurs. -/
theorem graph_distinctPort_second_odd_q_ne_nine
    {T : PosIntTree n} (hL : IsLeech T) (W : GraphTwoOddWeights T)
    (hDistinct : DistinctMiddlePorts W)
    (hTarget : OddTargetThrough14 n) : W.q ≠ 9 := by
  let O := twoBridgeOrientation W hDistinct
  exact oriented_distinctPort_second_odd_q_ne_nine hL W O hTarget

/-- Public graph-facing exclusion of the audited distinct-port `q=10`
case. -/
theorem graph_distinctPort_second_odd_q_ne_ten
    {T : PosIntTree n} (hL : IsLeech T) (W : GraphTwoOddWeights T)
    (hDistinct : DistinctMiddlePorts W)
    (hTarget : OddTargetThrough14 n) : W.q ≠ 10 := by
  intro hq
  let O := twoBridgeOrientation W hDistinct
  exact no_actualOddHalfRankCollision hL
    (actualCollision_of_q_ten hL W O hTarget hq)

/-- Distinct actual middle ports improve the unconditional second-odd bound
from `q ≤ 10`, `q ≠ 7` to the audited `q ≤ 6`, provided the actual odd target
is available through half-rank 14.  The exclusions of 8, 9, and 10 above are
all graph-derived and use no collision-ledger premise. -/
theorem graph_distinctPort_second_odd_q_le_six
    {T : PosIntTree n} (hL : IsLeech T) (W : GraphTwoOddWeights T)
    (hDistinct : DistinctMiddlePorts W)
    (hTarget : OddTargetThrough14 n) : W.q ≤ 6 := by
  have hle := graph_second_odd_q_le_ten hL W
  have h7 := graph_second_odd_q_ne_seven hL W
  have h8 := graph_distinctPort_second_odd_q_ne_eight
    hL W hDistinct hTarget
  have h9 := graph_distinctPort_second_odd_q_ne_nine
    hL W hDistinct hTarget
  have h10 := graph_distinctPort_second_odd_q_ne_ten
    hL W hDistinct hTarget
  omega

/-- At every order at least nine, the target-through-14 premise follows from
the Leech target length. -/
theorem graph_distinctPort_second_odd_q_le_six_of_nine_le
    {T : PosIntTree n} (hL : IsLeech T) (W : GraphTwoOddWeights T)
    (hDistinct : DistinctMiddlePorts W) (hn : 9 ≤ n) : W.q ≤ 6 :=
  graph_distinctPort_second_odd_q_le_six hL W hDistinct
    (oddTargetThrough14_of_nine_le hn)

/-- Direct exactly-two-odd endpoint.  The witness retains the two actual
physical edges, their weights `1` and `2*q+1`, and the proved bound `q ≤ 6`.
The orientation-free port hypothesis is stated for the actual odd physical
edges, not for quotient labels. -/
theorem actual_two_odd_distinctPort_q_le_six
    (T : PosIntTree n) (hL : IsLeech T) (hn : 2 ≤ n)
    (hTwo : ExactlyTwoOddPhysicalEdges T)
    (hPorts : OddPhysicalEdgesPairwisePortDisjoint T)
    (hTarget : OddTargetThrough14 n) :
    ∃ W : GraphTwoOddWeights T, W.q ≤ 6 := by
  let W := Classical.choice (exists_graphTwoOddWeights T hL hn hTwo)
  exact ⟨W, graph_distinctPort_second_odd_q_le_six hL W
    (distinctMiddlePorts_of_pairwise W hPorts) hTarget⟩

/-- Order-at-least-nine specialization of the direct exactly-two-odd
endpoint; the rank-through-14 guard is discharged internally. -/
theorem actual_two_odd_distinctPort_q_le_six_of_nine_le
    (T : PosIntTree n) (hL : IsLeech T) (hn : 9 ≤ n)
    (hTwo : ExactlyTwoOddPhysicalEdges T)
    (hPorts : OddPhysicalEdgesPairwisePortDisjoint T) :
    ∃ W : GraphTwoOddWeights T, W.q ≤ 6 :=
  actual_two_odd_distinctPort_q_le_six T hL (by omega) hTwo hPorts
    (oddTargetThrough14_of_nine_le hn)

end LeechTrees.G015
