import LeechTrees.Foundations
import LeechTrees.OddEdges
import LeechTrees.OddEdgesGraphAdapter
import LeechTrees.OddEdgesT12CutLemma
import LeechTrees.OddEdgesT12OrderField
import LeechTrees.OddEdgesT12PairSums
import LeechTrees.OddEdgesT12TargetChars

/-!
# Concrete T12 adapter

This module derives the signed Gaussian data from an actual positive-integral
tree with exactly two odd physical edges.  It uses a ceil-half reweighting and
the compatibility of the two actual edge cuts; no Gaussian identity is taken
as a hypothesis.
-/

open scoped BigOperators

namespace LeechTrees.OddEdges.T12Adapter

open LeechTrees.Foundation
open LeechTrees.OddEdges.GraphAdapter
open LeechTrees.OddEdges.T12Adapter.PairSums

variable {n : ℕ}

/-- Replace each positive physical weight `w` by `ceil(w/2)`. -/
noncomputable def ceilHalfTree (T : PosIntTree n) : PosIntTree n where
  graph := T.graph
  isTree := T.isTree
  weight e := (T.weight e + 1) / 2
  weight_pos e := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
    have := T.weight_pos e
    omega

@[simp] theorem ceilHalfTree_graph (T : PosIntTree n) :
    (ceilHalfTree T).graph = T.graph := rfl

@[simp] theorem ceilHalfTree_weight (T : PosIntTree n)
    (e : T.Edge) :
    (ceilHalfTree T).weight e = (T.weight e + 1) / 2 := rfl

theorem ceilHalfTree_path (T : PosIntTree n) (u v : Fin n) :
    (ceilHalfTree T).path u v = T.path u v :=
  T.path_unique _

theorem ceilHalfTree_pathEdges (T : PosIntTree n) (u v : Fin n) :
    (ceilHalfTree T).pathEdges u v = T.pathEdges u v := by
  unfold PosIntTree.pathEdges
  rw [ceilHalfTree_path]

theorem two_mul_ceilHalf (w : ℕ) :
    2 * ((w + 1) / 2) = w + if Odd w then 1 else 0 := by
  by_cases hw : Even w
  · have hnot : ¬ Odd w := by
      intro hodd
      exact (Nat.not_even_iff_odd.mpr hodd) hw
    rcases hw with ⟨q, hq⟩
    rw [if_neg hnot, hq]
    omega
  · have hodd := Nat.not_even_iff_odd.mp hw
    rcases hodd with ⟨q, hq⟩
    rw [if_pos]
    · rw [hq]
      omega
    · exact ⟨q, hq⟩

theorem ceilHalfTree_pathIncidence
    (T : PosIntTree n) (p : VertexPair n) (e : T.Edge) :
    (ceilHalfTree T).pathIncidence p e = T.pathIncidence p e := by
  unfold PosIntTree.pathIncidence
  rw [ceilHalfTree_pathEdges]

private theorem oddIndicatorSum_eq_two
    (T : PosIntTree n) (hTwo : ExactlyTwoOddPhysicalEdges T)
    (p : VertexPair n) :
    ∃ e f : T.Edge, e ≠ f ∧ Odd (T.weight e) ∧ Odd (T.weight f) ∧
      (∑ g : T.Edge, if Odd (T.weight g) then T.pathIncidence p g else 0) =
        T.pathIncidence p e + T.pathIncidence p f := by
  classical
  rcases Finset.card_eq_two.mp hTwo with ⟨e, f, hef, hset⟩
  have he : Odd (T.weight e) := by
    have : e ∈ actualOddPhysicalEdges T := by simp [hset]
    simpa using this
  have hf : Odd (T.weight f) := by
    have : f ∈ actualOddPhysicalEdges T := by simp [hset]
    simpa using this
  refine ⟨e, f, hef, he, hf, ?_⟩
  calc
    (∑ g : T.Edge, if Odd (T.weight g) then T.pathIncidence p g else 0) =
        ∑ g ∈ actualOddPhysicalEdges T, T.pathIncidence p g := by
          unfold actualOddPhysicalEdges
          rw [Finset.sum_filter]
    _ = T.pathIncidence p e + T.pathIncidence p f := by
      rw [hset]
      simp [hef]

theorem ceilHalf_pairDist_relation
    (T : PosIntTree n) (hTwo : ExactlyTwoOddPhysicalEdges T)
    (p : VertexPair n) :
    ∃ e f : T.Edge, e ≠ f ∧ Odd (T.weight e) ∧ Odd (T.weight f) ∧
      2 * (ceilHalfTree T).pairDist p = T.pairDist p +
        T.pathIncidence p e + T.pathIncidence p f := by
  classical
  rcases oddIndicatorSum_eq_two T hTwo p with ⟨e, f, hef, he, hf, hsum⟩
  refine ⟨e, f, hef, he, hf, ?_⟩
  rw [← (ceilHalfTree T).pathIncidence_row p, ← T.pathIncidence_row p]
  unfold LeechTrees.weightedRow
  rw [Finset.mul_sum]
  calc
    (∑ g : (ceilHalfTree T).Edge,
        2 * ((ceilHalfTree T).pathIncidence p g * (ceilHalfTree T).weight g)) =
        ∑ g : T.Edge, T.pathIncidence p g *
          (T.weight g + if Odd (T.weight g) then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro g _
            rw [ceilHalfTree_weight]
            calc
              2 * (T.pathIncidence p g * ((T.weight g + 1) / 2)) =
                  T.pathIncidence p g * (2 * ((T.weight g + 1) / 2)) := by
                    ac_rfl
              _ = T.pathIncidence p g *
                  (T.weight g + if Odd (T.weight g) then 1 else 0) := by
                    rw [two_mul_ceilHalf]
    _ = (∑ g : T.Edge, T.pathIncidence p g * T.weight g) +
        ∑ g : T.Edge,
          if Odd (T.weight g) then T.pathIncidence p g else 0 := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro g _
            by_cases hg : Odd (T.weight g) <;> simp [hg, mul_add]
    _ = (∑ g : T.Edge, T.pathIncidence p g * T.weight g) +
        (T.pathIncidence p e + T.pathIncidence p f) := by rw [hsum]
    _ = (∑ g : T.Edge, T.pathIncidence p g * T.weight g) +
        T.pathIncidence p e + T.pathIncidence p f := by omega

/-- A fixed choice of the two odd physical edges.  The final field records the
entire odd-edge set, rather than merely recording that the chosen edges are
odd. -/
structure TwoOddEdges (T : PosIntTree n) where
  e : T.Edge
  f : T.Edge
  ne : e ≠ f
  oddSet : actualOddPhysicalEdges T = {e, f}

private theorem nonempty_twoOddEdges (T : PosIntTree n)
    (hTwo : ExactlyTwoOddPhysicalEdges T) : Nonempty (TwoOddEdges T) := by
  classical
  rcases Finset.card_eq_two.mp hTwo with ⟨e, f, hef, hset⟩
  exact ⟨⟨e, f, hef, hset⟩⟩

noncomputable def twoOddEdges (T : PosIntTree n)
    (hTwo : ExactlyTwoOddPhysicalEdges T) : TwoOddEdges T :=
  Classical.choice (nonempty_twoOddEdges T hTwo)

theorem TwoOddEdges.odd_e (d : TwoOddEdges T) : Odd (T.weight d.e) := by
  have : d.e ∈ actualOddPhysicalEdges T := by simp [d.oddSet]
  simpa [actualOddPhysicalEdges] using this

theorem TwoOddEdges.odd_f (d : TwoOddEdges T) : Odd (T.weight d.f) := by
  have : d.f ∈ actualOddPhysicalEdges T := by simp [d.oddSet]
  simpa [actualOddPhysicalEdges] using this

theorem TwoOddEdges.odd_iff (d : TwoOddEdges T) (g : T.Edge) :
    Odd (T.weight g) ↔ g = d.e ∨ g = d.f := by
  have hm : g ∈ actualOddPhysicalEdges T ↔ Odd (T.weight g) := by
    simp [actualOddPhysicalEdges]
  rw [← hm, d.oddSet]
  simp

theorem ceilHalf_pairDist_relation_fixed
    (T : PosIntTree n) (d : TwoOddEdges T) (p : VertexPair n) :
    2 * (ceilHalfTree T).pairDist p = T.pairDist p +
      T.pathIncidence p d.e + T.pathIncidence p d.f := by
  classical
  rw [← (ceilHalfTree T).pathIncidence_row p, ← T.pathIncidence_row p]
  unfold LeechTrees.weightedRow
  rw [Finset.mul_sum]
  calc
    (∑ g : (ceilHalfTree T).Edge,
        2 * ((ceilHalfTree T).pathIncidence p g * (ceilHalfTree T).weight g)) =
        ∑ g : T.Edge, T.pathIncidence p g *
          (T.weight g + if Odd (T.weight g) then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro g _
            rw [ceilHalfTree_weight]
            calc
              2 * (T.pathIncidence p g * ((T.weight g + 1) / 2)) =
                  T.pathIncidence p g * (2 * ((T.weight g + 1) / 2)) := by
                    ac_rfl
              _ = T.pathIncidence p g *
                  (T.weight g + if Odd (T.weight g) then 1 else 0) := by
                    rw [two_mul_ceilHalf]
    _ = (∑ g : T.Edge, T.pathIncidence p g * T.weight g) +
        ∑ g : T.Edge,
          if Odd (T.weight g) then T.pathIncidence p g else 0 := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro g _
            by_cases hg : Odd (T.weight g) <;> simp [hg, mul_add]
    _ = (∑ g : T.Edge, T.pathIncidence p g * T.weight g) +
        (T.pathIncidence p d.e + T.pathIncidence p d.f) := by
          congr 1
          calc
            (∑ g : T.Edge,
                if Odd (T.weight g) then T.pathIncidence p g else 0) =
                ∑ g ∈ actualOddPhysicalEdges T, T.pathIncidence p g := by
                  unfold actualOddPhysicalEdges
                  rw [Finset.sum_filter]
            _ = T.pathIncidence p d.e + T.pathIncidence p d.f := by
              rw [d.oddSet]
              simp [d.ne]
    _ = (∑ g : T.Edge, T.pathIncidence p g * T.weight g) +
        T.pathIncidence p d.e + T.pathIncidence p d.f := by omega

/-- The root sign in the ceil-half tree. -/
noncomputable def vertexSign (T : PosIntTree n) (r v : Fin n) : ℤ :=
  (-1 : ℤ) ^ (ceilHalfTree T).dist r v

@[simp] theorem vertexSign_sq (T : PosIntTree n) (r v : Fin n) :
    vertexSign T r v ^ 2 = 1 := by
  rw [pow_two]
  unfold vertexSign
  rw [← pow_add]
  apply Even.neg_one_pow
  exact ⟨(ceilHalfTree T).dist r v, by omega⟩

theorem vertexSign_mul (T : PosIntTree n) (r u v : Fin n) :
    vertexSign T r u * vertexSign T r v =
      (-1 : ℤ) ^ (ceilHalfTree T).dist u v := by
  have he := (ceilHalfTree T).root_path_even r u v
  have hp : (-1 : ℤ) ^ ((ceilHalfTree T).dist r u +
      (ceilHalfTree T).dist u v + (ceilHalfTree T).dist r v) = 1 :=
    he.neg_one_pow
  have hsq : (((-1 : ℤ) ^ (ceilHalfTree T).dist u v) ^ 2) = 1 := by
    rw [pow_two, ← pow_add]
    apply Even.neg_one_pow
    exact ⟨(ceilHalfTree T).dist u v, by omega⟩
  simp only [pow_add] at hp
  calc
    vertexSign T r u * vertexSign T r v =
        vertexSign T r u * vertexSign T r v *
          (((-1 : ℤ) ^ (ceilHalfTree T).dist u v) ^ 2) := by rw [hsq]; simp
    _ = (((-1 : ℤ) ^ (ceilHalfTree T).dist r u) *
          ((-1 : ℤ) ^ (ceilHalfTree T).dist u v) *
          ((-1 : ℤ) ^ (ceilHalfTree T).dist r v)) *
          ((-1 : ℤ) ^ (ceilHalfTree T).dist u v) := by
            simp only [vertexSign]
            ring
    _ = (-1 : ℤ) ^ (ceilHalfTree T).dist u v := by rw [hp]; simp

theorem mem_pathEdges_iff_root_xor (T : PosIntTree n) (r u v : Fin n)
    (e : T.Edge) :
    e.1 ∈ T.pathEdges u v ↔
      (e.1 ∈ T.pathEdges r u ∧ e.1 ∉ T.pathEdges r v) ∨
      (e.1 ∉ T.pathEdges r u ∧ e.1 ∈ T.pathEdges r v) := by
  rw [T.mem_pathEdges_iff_opposite_cuts,
    T.mem_pathEdges_iff_opposite_cuts,
    T.mem_pathEdges_iff_opposite_cuts]
  simp only [T.rightCut_iff_not_leftCut]
  tauto

/-- Signed half-rank character on odd distances. -/
noncomputable def oddPairTerm (T : PosIntTree n) (p : VertexPair n) : ℤ :=
  if Odd (T.pairDist p) then (-1 : ℤ) ^ ((T.pairDist p - 1) / 2) else 0

/-- Signed half-rank character on even distances. -/
noncomputable def evenPairTerm (T : PosIntTree n) (p : VertexPair n) : ℤ :=
  if Even (T.pairDist p) then (-1 : ℤ) ^ (T.pairDist p / 2) else 0

theorem neg_one_pow_pred {m : ℕ} (hm : 0 < m) :
    (-1 : ℤ) ^ (m - 1) = -((-1 : ℤ) ^ m) := by
  have heq : m = (m - 1) + 1 := by omega
  conv_rhs => rw [heq]
  rw [pow_succ]
  ring

theorem pairTerms_neither
    (T : PosIntTree n) (d : TwoOddEdges T) (r : Fin n) (p : VertexPair n)
    (he : d.e.1 ∉ T.pathEdges p.left p.right)
    (hf : d.f.1 ∉ T.pathEdges p.left p.right) :
    oddPairTerm T p = 0 ∧
    evenPairTerm T p = vertexSign T r p.left * vertexSign T r p.right := by
  have hrel := ceilHalf_pairDist_relation_fixed T d p
  simp [PosIntTree.pathIncidence, he, hf] at hrel
  have hev : Even (T.pairDist p) :=
    ⟨(ceilHalfTree T).pairDist p, by omega⟩
  have hodd : ¬ Odd (T.pairDist p) := by
    intro ho
    exact (Nat.not_even_iff_odd.mpr ho) hev
  have hhalf : T.pairDist p / 2 = (ceilHalfTree T).pairDist p := by omega
  constructor
  · simp [oddPairTerm, hodd]
  · rw [evenPairTerm, if_pos hev, hhalf]
    unfold PosIntTree.pairDist
    exact (vertexSign_mul T r p.left p.right).symm

theorem pairTerms_e_only
    (T : PosIntTree n) (d : TwoOddEdges T) (r : Fin n) (p : VertexPair n)
    (he : d.e.1 ∈ T.pathEdges p.left p.right)
    (hf : d.f.1 ∉ T.pathEdges p.left p.right) :
    oddPairTerm T p = -(vertexSign T r p.left * vertexSign T r p.right) ∧
    evenPairTerm T p = 0 := by
  have hrel := ceilHalf_pairDist_relation_fixed T d p
  simp [PosIntTree.pathIncidence, he, hf] at hrel
  have hpos : 0 < (ceilHalfTree T).pairDist p := by omega
  have hodd : Odd (T.pairDist p) :=
    ⟨(ceilHalfTree T).pairDist p - 1, by omega⟩
  have hnot : ¬ Even (T.pairDist p) := Nat.not_even_iff_odd.mpr hodd
  have hhalf : (T.pairDist p - 1) / 2 =
      (ceilHalfTree T).pairDist p - 1 := by omega
  constructor
  · rw [oddPairTerm, if_pos hodd, hhalf, neg_one_pow_pred hpos]
    unfold PosIntTree.pairDist
    rw [← vertexSign_mul]
  · simp [evenPairTerm, hnot]

theorem pairTerms_f_only
    (T : PosIntTree n) (d : TwoOddEdges T) (r : Fin n) (p : VertexPair n)
    (he : d.e.1 ∉ T.pathEdges p.left p.right)
    (hf : d.f.1 ∈ T.pathEdges p.left p.right) :
    oddPairTerm T p = -(vertexSign T r p.left * vertexSign T r p.right) ∧
    evenPairTerm T p = 0 := by
  have hrel := ceilHalf_pairDist_relation_fixed T d p
  simp [PosIntTree.pathIncidence, he, hf] at hrel
  have hpos : 0 < (ceilHalfTree T).pairDist p := by omega
  have hodd : Odd (T.pairDist p) :=
    ⟨(ceilHalfTree T).pairDist p - 1, by omega⟩
  have hnot : ¬ Even (T.pairDist p) := Nat.not_even_iff_odd.mpr hodd
  have hhalf : (T.pairDist p - 1) / 2 =
      (ceilHalfTree T).pairDist p - 1 := by omega
  constructor
  · rw [oddPairTerm, if_pos hodd, hhalf, neg_one_pow_pred hpos]
    unfold PosIntTree.pairDist
    rw [← vertexSign_mul]
  · simp [evenPairTerm, hnot]

theorem pairTerms_both
    (T : PosIntTree n) (d : TwoOddEdges T) (r : Fin n) (p : VertexPair n)
    (he : d.e.1 ∈ T.pathEdges p.left p.right)
    (hf : d.f.1 ∈ T.pathEdges p.left p.right) :
    oddPairTerm T p = 0 ∧
    evenPairTerm T p = -(vertexSign T r p.left * vertexSign T r p.right) := by
  have hrel := ceilHalf_pairDist_relation_fixed T d p
  simp [PosIntTree.pathIncidence, he, hf] at hrel
  have hpos : 0 < (ceilHalfTree T).pairDist p := by omega
  have hev : Even (T.pairDist p) :=
    ⟨(ceilHalfTree T).pairDist p - 1, by omega⟩
  have hodd : ¬ Odd (T.pairDist p) := by
    intro ho
    exact (Nat.not_even_iff_odd.mpr ho) hev
  have hhalf : T.pairDist p / 2 =
      (ceilHalfTree T).pairDist p - 1 := by omega
  constructor
  · simp [oddPairTerm, hodd]
  · rw [evenPairTerm, if_pos hev, hhalf, neg_one_pow_pred hpos]
    unfold PosIntTree.pairDist
    rw [← vertexSign_mul]

/-- Whether the rooted path to a vertex uses a specified edge. -/
def rootUses (T : PosIntTree n) (r : Fin n) (e : T.Edge) (v : Fin n) : Prop :=
  e.1 ∈ T.pathEdges r v

theorem cutDiff_rootUses_iff (T : PosIntTree n) (r u v : Fin n) (e : T.Edge) :
    cutDiff (rootUses T r e) u v ↔ e.1 ∈ T.pathEdges u v := by
  unfold cutDiff rootUses
  exact (mem_pathEdges_iff_root_xor T r u v e).symm

noncomputable def oddCutKernel (T : PosIntTree n) (d : TwoOddEdges T)
    (r u v : Fin n) : ℤ :=
  -(exactlyOneCutTerm (rootUses T r d.e) (rootUses T r d.f)
      (vertexSign T r) u v)

noncomputable def evenCutKernel (T : PosIntTree n) (d : TwoOddEdges T)
    (r u v : Fin n) : ℤ :=
  evenCutSignTerm (rootUses T r d.e) (rootUses T r d.f)
    (vertexSign T r) u v

theorem exactlyOneCutTerm_comm {P Q : Fin n → Prop}
    (w : Fin n → ℤ) (u v : Fin n) :
    exactlyOneCutTerm P Q w u v = exactlyOneCutTerm P Q w v u := by
  classical
  by_cases hPu : P u <;> by_cases hQu : Q u <;>
    by_cases hPv : P v <;> by_cases hQv : Q v <;>
      simp [exactlyOneCutTerm, exactlyOne, cutDiff,
        hPu, hQu, hPv, hQv, mul_comm]

theorem evenCutSignTerm_comm {P Q : Fin n → Prop}
    (w : Fin n → ℤ) (u v : Fin n) :
    evenCutSignTerm P Q w u v = evenCutSignTerm P Q w v u := by
  classical
  by_cases hPu : P u <;> by_cases hQu : Q u <;>
    by_cases hPv : P v <;> by_cases hQv : Q v <;>
      simp [evenCutSignTerm, cutDiff, hPu, hQu, hPv, hQv, mul_comm]

theorem oddCutKernel_comm (T : PosIntTree n) (d : TwoOddEdges T)
    (r u v : Fin n) : oddCutKernel T d r u v = oddCutKernel T d r v u := by
  unfold oddCutKernel
  rw [exactlyOneCutTerm_comm]

theorem evenCutKernel_comm (T : PosIntTree n) (d : TwoOddEdges T)
    (r u v : Fin n) : evenCutKernel T d r u v = evenCutKernel T d r v u := by
  unfold evenCutKernel
  rw [evenCutSignTerm_comm]

theorem oddPairTerm_eq_kernel (T : PosIntTree n) (d : TwoOddEdges T)
    (r : Fin n) (p : VertexPair n) :
    oddPairTerm T p = oddCutKernel T d r p.left p.right := by
  have heqE := cutDiff_rootUses_iff T r p.left p.right d.e
  have heqF := cutDiff_rootUses_iff T r p.left p.right d.f
  by_cases he : d.e.1 ∈ T.pathEdges p.left p.right <;>
    by_cases hf : d.f.1 ∈ T.pathEdges p.left p.right
  · have h := (pairTerms_both T d r p he hf).1
    rw [h]
    simp [oddCutKernel, exactlyOneCutTerm, exactlyOne, heqE, heqF, he, hf]
  · have h := (pairTerms_e_only T d r p he hf).1
    rw [h]
    simp [oddCutKernel, exactlyOneCutTerm, exactlyOne, heqE, heqF, he, hf]
  · have h := (pairTerms_f_only T d r p he hf).1
    rw [h]
    simp [oddCutKernel, exactlyOneCutTerm, exactlyOne, heqE, heqF, he, hf]
  · have h := (pairTerms_neither T d r p he hf).1
    rw [h]
    simp [oddCutKernel, exactlyOneCutTerm, exactlyOne, heqE, heqF, he, hf]

theorem evenPairTerm_eq_kernel (T : PosIntTree n) (d : TwoOddEdges T)
    (r : Fin n) (p : VertexPair n) :
    evenPairTerm T p = evenCutKernel T d r p.left p.right := by
  have heqE := cutDiff_rootUses_iff T r p.left p.right d.e
  have heqF := cutDiff_rootUses_iff T r p.left p.right d.f
  by_cases he : d.e.1 ∈ T.pathEdges p.left p.right <;>
    by_cases hf : d.f.1 ∈ T.pathEdges p.left p.right
  · have h := (pairTerms_both T d r p he hf).2
    rw [h]
    simp [evenCutKernel, evenCutSignTerm, heqE, heqF, he, hf]
  · have h := (pairTerms_e_only T d r p he hf).2
    rw [h]
    simp [evenCutKernel, evenCutSignTerm, heqE, heqF, he, hf]
  · have h := (pairTerms_f_only T d r p he hf).2
    rw [h]
    simp [evenCutKernel, evenCutSignTerm, heqE, heqF, he, hf]
  · have h := (pairTerms_neither T d r p he hf).2
    rw [h]
    simp [evenCutKernel, evenCutSignTerm, heqE, heqF, he, hf]

noncomputable def massTT (T : PosIntTree n) (d : TwoOddEdges T)
    (r : Fin n) : ℤ := by
  classical
  exact cellTT (rootUses T r d.e) (rootUses T r d.f) (vertexSign T r)

noncomputable def massTF (T : PosIntTree n) (d : TwoOddEdges T)
    (r : Fin n) : ℤ := by
  classical
  exact cellTF (rootUses T r d.e) (rootUses T r d.f) (vertexSign T r)

noncomputable def massFT (T : PosIntTree n) (d : TwoOddEdges T)
    (r : Fin n) : ℤ := by
  classical
  exact cellFT (rootUses T r d.e) (rootUses T r d.f) (vertexSign T r)

noncomputable def massFF (T : PosIntTree n) (d : TwoOddEdges T)
    (r : Fin n) : ℤ := by
  classical
  exact cellFF (rootUses T r d.e) (rootUses T r d.f) (vertexSign T r)

theorem odd_character_factorization
    (T : PosIntTree n) (d : TwoOddEdges T) (r : Fin n) :
    (∑ p : VertexPair n, oddPairTerm T p) =
      -(massTT T d r + massFF T d r) *
        (massTF T d r + massFT T d r) := by
  classical
  have hsum : (∑ p : VertexPair n, oddPairTerm T p) =
      ∑ p : VertexPair n, oddCutKernel T d r p.left p.right := by
    apply Finset.sum_congr rfl
    intro p _
    exact oddPairTerm_eq_kernel T d r p
  have hpair :
      2 * (∑ p : VertexPair n, oddPairTerm T p) =
        ∑ u : Fin n, ∑ v : Fin n,
          if u = v then 0 else oddCutKernel T d r u v := by
    calc
      2 * (∑ p : VertexPair n, oddPairTerm T p) =
          2 * (∑ p : VertexPair n, oddCutKernel T d r p.left p.right) := by
            rw [hsum]
      _ = ∑ u : Fin n, ∑ v : Fin n,
          if u = v then 0 else oddCutKernel T d r u v :=
        two_mul_sum_vertexPair (oddCutKernel T d r)
          (oddCutKernel_comm T d r)
  have hoffdiag :
      (∑ u : Fin n, ∑ v : Fin n,
          if u = v then 0 else oddCutKernel T d r u v) =
        ∑ u : Fin n, ∑ v : Fin n, oddCutKernel T d r u v := by
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    by_cases huv : u = v
    · subst v
      simp [oddCutKernel, exactlyOneCutTerm, exactlyOne, cutDiff]
    · simp [huv]
  have htotal :
      (∑ u : Fin n, ∑ v : Fin n, oddCutKernel T d r u v) =
        -(2 * (massTT T d r + massFF T d r) *
          (massTF T d r + massFT T d r)) := by
    calc
      (∑ u : Fin n, ∑ v : Fin n, oddCutKernel T d r u v) =
          -(∑ u : Fin n, ∑ v : Fin n,
            exactlyOneCutTerm (rootUses T r d.e) (rootUses T r d.f)
              (vertexSign T r) u v) := by
                unfold oddCutKernel
                simp_rw [Finset.sum_neg_distrib]
      _ = -(2 * (massTT T d r + massFF T d r) *
          (massTF T d r + massFT T d r)) := by
            rw [sum_exactlyOne_cutDiff]
            simp only [massTT, massTF, massFT, massFF]
  rw [hoffdiag, htotal] at hpair
  linarith

theorem even_character_factorization
    (T : PosIntTree n) (d : TwoOddEdges T) (r : Fin n) :
    2 * (∑ p : VertexPair n, evenPairTerm T p) =
      (massTT T d r - massFF T d r) ^ 2 +
        (massTF T d r - massFT T d r) ^ 2 - n := by
  classical
  have hsum : (∑ p : VertexPair n, evenPairTerm T p) =
      ∑ p : VertexPair n, evenCutKernel T d r p.left p.right := by
    apply Finset.sum_congr rfl
    intro p _
    exact evenPairTerm_eq_kernel T d r p
  have hpair :
      2 * (∑ p : VertexPair n, evenPairTerm T p) =
        ∑ u : Fin n, ∑ v : Fin n,
          if u = v then 0 else evenCutKernel T d r u v := by
    calc
      2 * (∑ p : VertexPair n, evenPairTerm T p) =
          2 * (∑ p : VertexPair n, evenCutKernel T d r p.left p.right) := by
            rw [hsum]
      _ = ∑ u : Fin n, ∑ v : Fin n,
          if u = v then 0 else evenCutKernel T d r u v :=
        two_mul_sum_vertexPair (evenCutKernel T d r)
          (evenCutKernel_comm T d r)
  have hdiag :
      (∑ u : Fin n, evenCutKernel T d r u u) = (n : ℤ) := by
    calc
      (∑ u : Fin n, evenCutKernel T d r u u) = ∑ _u : Fin n, (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro u _
        simp [evenCutKernel, evenCutSignTerm, cutDiff]
        rw [← pow_two]
        exact vertexSign_sq T r u
      _ = (n : ℤ) := by simp
  have hoffdiag :
      (∑ u : Fin n, ∑ v : Fin n,
          if u = v then 0 else evenCutKernel T d r u v) =
        (∑ u : Fin n, ∑ v : Fin n, evenCutKernel T d r u v) - n := by
    calc
      (∑ u : Fin n, ∑ v : Fin n,
          if u = v then 0 else evenCutKernel T d r u v) =
          ∑ u : Fin n, ∑ v : Fin n,
            (evenCutKernel T d r u v -
              if u = v then evenCutKernel T d r u v else 0) := by
                apply Finset.sum_congr rfl
                intro u _
                apply Finset.sum_congr rfl
                intro v _
                by_cases huv : u = v <;> simp [huv]
      _ = (∑ u : Fin n, ∑ v : Fin n, evenCutKernel T d r u v) -
          ∑ u : Fin n, evenCutKernel T d r u u := by
            simp_rw [Finset.sum_sub_distrib]
            congr 1
            apply Finset.sum_congr rfl
            intro u _
            simp
      _ = (∑ u : Fin n, ∑ v : Fin n, evenCutKernel T d r u v) - n := by
        rw [hdiag]
  have htotal :
      (∑ u : Fin n, ∑ v : Fin n, evenCutKernel T d r u v) =
        (massTT T d r - massFF T d r) ^ 2 +
          (massTF T d r - massFT T d r) ^ 2 := by
    unfold evenCutKernel massTT massTF massFT massFF
    exact sum_evenCutSign (rootUses T r d.e) (rootUses T r d.f)
      (vertexSign T r)
  rw [hoffdiag, htotal] at hpair
  exact hpair

theorem odd_character_target (T : PosIntTree n) (hL : IsLeech T) :
    (∑ p : VertexPair n, oddPairTerm T p) =
      if Even (oddTargetCount n) then 0 else 1 := by
  unfold oddPairTerm
  rw [oddTargetCount_eq]
  exact LeechTrees.OddEdges.TargetChars.leech_odd_half_character hL

theorem evenTargetCount_eq_half (n : ℕ) :
    evenTargetCount n = targetN n / 2 := by
  unfold evenTargetCount
  rw [oddTargetCount_eq]
  omega

theorem even_character_target (T : PosIntTree n) (hL : IsLeech T) :
    (∑ p : VertexPair n, evenPairTerm T p) =
      if Even (evenTargetCount n) then 0 else -1 := by
  unfold evenPairTerm
  rw [evenTargetCount_eq_half]
  exact LeechTrees.OddEdges.TargetChars.leech_even_half_character hL

theorem massTF_eq_zero_of_empty
    (T : PosIntTree n) (d : TwoOddEdges T) (r : Fin n)
    (h : ∀ v, ¬(rootUses T r d.e v ∧ ¬rootUses T r d.f v)) :
    massTF T d r = 0 := by
  classical
  unfold massTF cellTF
  apply Finset.sum_eq_zero
  intro v _
  rw [if_neg (h v)]

theorem massFT_eq_zero_of_empty
    (T : PosIntTree n) (d : TwoOddEdges T) (r : Fin n)
    (h : ∀ v, ¬(¬rootUses T r d.e v ∧ rootUses T r d.f v)) :
    massFT T d r = 0 := by
  classical
  unfold massFT cellFT
  apply Finset.sum_eq_zero
  intro v _
  rw [if_neg (h v)]

theorem massTT_eq_zero_of_empty
    (T : PosIntTree n) (d : TwoOddEdges T) (r : Fin n)
    (h : ∀ v, ¬(rootUses T r d.e v ∧ rootUses T r d.f v)) :
    massTT T d r = 0 := by
  classical
  unfold massTT cellTT
  apply Finset.sum_eq_zero
  intro v _
  rw [if_neg (h v)]

private noncomputable def gaussianData_of_coordinates
    (T : PosIntTree n) (hL : IsLeech T) (d : TwoOddEdges T) (r : Fin n)
    (s xi eta chi : ℤ)
    (horder :
      ((n : ℤ) = s ^ 2 ∧ oddTargetCount n = evenTargetCount n) ∨
      ((n : ℤ) = s ^ 2 + 2 ∧
        oddTargetCount n = evenTargetCount n + 1))
    (hoddCoordinate :
      eta * (xi + chi) =
        -(massTT T d r + massFF T d r) *
          (massTF T d r + massFT T d r))
    (hevenCoordinate :
      (xi - chi) ^ 2 + eta ^ 2 =
        (massTT T d r - massFF T d r) ^ 2 +
          (massTF T d r - massFT T d r) ^ 2) :
    TwoOddGaussianData n (oddTargetCount n) (evenTargetCount n) := by
  refine
    { s := s
      xi := xi
      eta := eta
      chi := chi
      order_case := horder
      odd_eval := ?_
      gaussian_even := ?_
      gaussian_odd := ?_ }
  · intro hOodd
    have hnot : ¬Even (oddTargetCount n) := Nat.not_even_iff_odd.mpr hOodd
    have ht := odd_character_target T hL
    rw [if_neg hnot] at ht
    calc
      eta * (xi + chi) =
          -(massTT T d r + massFF T d r) *
            (massTF T d r + massFT T d r) := hoddCoordinate
      _ = ∑ p : VertexPair n, oddPairTerm T p :=
        (odd_character_factorization T d r).symm
      _ = 1 := ht
  · intro hEeven
    have ht := even_character_target T hL
    rw [if_pos hEeven] at ht
    have hf := even_character_factorization T d r
    rw [ht] at hf
    calc
      (xi - chi) ^ 2 + eta ^ 2 =
          (massTT T d r - massFF T d r) ^ 2 +
            (massTF T d r - massFT T d r) ^ 2 := hevenCoordinate
      _ = (n : ℤ) := by linarith
  · intro hEodd
    have hnot : ¬Even (evenTargetCount n) := Nat.not_even_iff_odd.mpr hEodd
    have ht := even_character_target T hL
    rw [if_neg hnot] at ht
    have hf := even_character_factorization T d r
    rw [ht] at hf
    calc
      (xi - chi) ^ 2 + eta ^ 2 =
          (massTT T d r - massFF T d r) ^ 2 +
            (massTF T d r - massFT T d r) ^ 2 := hevenCoordinate
      _ = (n : ℤ) - 2 := by linarith

/-- Concrete construction of all Gaussian data from an actual Leech tree and
its two actual odd physical edges. -/
theorem concreteTwoOddGaussianData
    (T : PosIntTree n) (hL : IsLeech T) (hn : 5 ≤ n)
    (hTwo : ExactlyTwoOddPhysicalEdges T) :
    Nonempty (TwoOddGaussianData n (oddTargetCount n) (evenTargetCount n)) := by
  classical
  let d := twoOddEdges T hTwo
  let r : Fin n := ⟨0, by omega⟩
  obtain ⟨s, horder⟩ :=
    LeechTrees.OddEdges.T12Adapter.OrderField.coupled_order_case T hL r
  rcases LeechTrees.OddEdges.T12Adapter.CutLemma.one_of_three_root_path_cells_empty
      T d.e d.f d.ne r with hTF | hFT | hTT
  · have hz : massTF T d r = 0 :=
      massTF_eq_zero_of_empty T d r (by simpa [rootUses] using hTF)
    refine ⟨gaussianData_of_coordinates T hL d r s
      (massTT T d r) (-(massFT T d r)) (massFF T d r) horder ?_ ?_⟩
    · rw [hz]
      ring
    · rw [hz]
      ring
  · have hz : massFT T d r = 0 :=
      massFT_eq_zero_of_empty T d r (by simpa [rootUses] using hFT)
    refine ⟨gaussianData_of_coordinates T hL d r s
      (massTT T d r) (-(massTF T d r)) (massFF T d r) horder ?_ ?_⟩
    · rw [hz]
      ring
    · rw [hz]
      ring
  · have hz : massTT T d r = 0 :=
      massTT_eq_zero_of_empty T d r (by simpa [rootUses] using hTT)
    refine ⟨gaussianData_of_coordinates T hL d r s
      (massTF T d r) (-(massFF T d r)) (massFT T d r) horder ?_ ?_⟩
    · rw [hz]
      ring
    · rw [hz]
      ring

/-- Graph-level T12: an actual Leech tree with exactly two odd physical edges
has an even number of odd target ranks. -/
theorem t12_two_odd_physical_edges
    (T : PosIntTree n) (hL : IsLeech T) (hn : 5 ≤ n)
    (hTwo : ExactlyTwoOddPhysicalEdges T) :
    Even (oddTargetCount n) := by
  exact twoOdd_oddTargetCount_even hn
    (Classical.choice (concreteTwoOddGaussianData T hL hn hTwo))

end LeechTrees.OddEdges.T12Adapter
