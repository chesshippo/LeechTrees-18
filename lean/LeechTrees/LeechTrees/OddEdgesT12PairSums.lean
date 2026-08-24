import LeechTrees.Foundations

open scoped BigOperators

namespace LeechTrees.OddEdges.T12Adapter.PairSums

open LeechTrees.Foundation

/-- Ordered pairs of distinct vertices. -/
abbrev OrientedPair (n : ℕ) := {q : Fin n × Fin n // q.1 ≠ q.2}

/-- Every ordered distinct pair is either the increasing representative of
an unordered pair or the reverse of one. -/
noncomputable def orientedPairEquiv (n : ℕ) :
    OrientedPair n ≃ VertexPair n ⊕ VertexPair n := by
  classical
  let toFun : OrientedPair n → VertexPair n ⊕ VertexPair n := fun q =>
    if h : q.1.1 < q.1.2 then
      Sum.inl ⟨q.1, h⟩
    else
      Sum.inr ⟨(q.1.2, q.1.1), lt_of_le_of_ne (le_of_not_gt h) q.2.symm⟩
  let invFun : VertexPair n ⊕ VertexPair n → OrientedPair n
    | Sum.inl p => ⟨(p.left, p.right), ne_of_lt p.left_lt_right⟩
    | Sum.inr p => ⟨(p.right, p.left), (ne_of_lt p.left_lt_right).symm⟩
  exact
    { toFun := toFun
      invFun := invFun
      left_inv := by
        intro q
        rcases q with ⟨⟨u, v⟩, huv⟩
        by_cases hlt : u < v
        · simp [toFun, invFun, hlt, VertexPair.left, VertexPair.right]
        · simp [toFun, invFun, hlt, VertexPair.left, VertexPair.right]
      right_inv := by
        intro q
        rcases q with p | p
        · dsimp only [invFun, toFun]
          rw [dif_pos p.left_lt_right]
          congr 1
        · have hnot : ¬ p.right < p.left := not_lt_of_ge p.left_lt_right.le
          dsimp only [invFun, toFun]
          rw [dif_neg hnot]
          congr 1 }

private theorem sum_oriented_eq_sum_ite_ne {n : ℕ} (F : Fin n → Fin n → ℤ) :
    (∑ q : OrientedPair n, F q.1.1 q.1.2) =
      ∑ q : Fin n × Fin n, if q.1 ≠ q.2 then F q.1 q.2 else 0 := by
  classical
  symm
  calc
    (∑ q : Fin n × Fin n, if q.1 ≠ q.2 then F q.1 q.2 else 0) =
        ∑ q ∈ (Finset.univ.filter fun q : Fin n × Fin n => q.1 ≠ q.2),
          F q.1 q.2 := by
            rw [Finset.sum_filter]
    _ = ∑ q : OrientedPair n, F q.1.1 q.1.2 := by
      exact Finset.sum_subtype _ (fun _ => by simp) _

/-- The ordered off-diagonal sum of a symmetric function is twice its sum
over the canonical increasing representatives. -/
theorem two_mul_sum_vertexPair {n : ℕ} (F : Fin n → Fin n → ℤ)
    (hsymm : ∀ u v, F u v = F v u) :
    2 * (∑ p : VertexPair n, F p.left p.right) =
      ∑ u : Fin n, ∑ v : Fin n, if u = v then 0 else F u v := by
  classical
  let G : VertexPair n ⊕ VertexPair n → ℤ
    | Sum.inl p => F p.left p.right
    | Sum.inr p => F p.right p.left
  have horiented :
      (∑ q : OrientedPair n, F q.1.1 q.1.2) =
        (∑ p : VertexPair n, F p.left p.right) +
          ∑ p : VertexPair n, F p.right p.left := by
    calc
      (∑ q : OrientedPair n, F q.1.1 q.1.2) =
          ∑ s : VertexPair n ⊕ VertexPair n, G s := by
            apply Fintype.sum_equiv (orientedPairEquiv n)
            intro q
            by_cases hlt : q.1.1 < q.1.2
            · simp [orientedPairEquiv, G, hlt, VertexPair.left, VertexPair.right]
            · simp [orientedPairEquiv, G, hlt, VertexPair.left, VertexPair.right]
      _ = (∑ p : VertexPair n, F p.left p.right) +
            ∑ p : VertexPair n, F p.right p.left := by
          rw [Fintype.sum_sum_type]
  have hordered :
      (∑ u : Fin n, ∑ v : Fin n, if u = v then 0 else F u v) =
        ∑ q : OrientedPair n, F q.1.1 q.1.2 := by
    rw [sum_oriented_eq_sum_ite_ne]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    by_cases h : u = v <;> simp [h]
  rw [hordered, horiented]
  simp_rw [hsymm]
  ring

/-! Four-cell algebra for two predicates. -/

def cutDiff {α : Type*} (P : α → Prop) (u v : α) : Prop :=
  (P u ∧ ¬ P v) ∨ (¬ P u ∧ P v)

def exactlyOne (A B : Prop) : Prop :=
  (A ∧ ¬ B) ∨ (¬ A ∧ B)

noncomputable def cellTT {α : Type*} [Fintype α]
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (w : α → ℤ) : ℤ :=
  ∑ x, if P x ∧ Q x then w x else 0

noncomputable def cellTF {α : Type*} [Fintype α]
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (w : α → ℤ) : ℤ :=
  ∑ x, if P x ∧ ¬ Q x then w x else 0

noncomputable def cellFT {α : Type*} [Fintype α]
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (w : α → ℤ) : ℤ :=
  ∑ x, if ¬ P x ∧ Q x then w x else 0

noncomputable def cellFF {α : Type*} [Fintype α]
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (w : α → ℤ) : ℤ :=
  ∑ x, if ¬ P x ∧ ¬ Q x then w x else 0

private theorem fintype_sum_mul_sum {α : Type*} [Fintype α]
    (f g : α → ℤ) :
    (∑ x, f x) * (∑ y, g y) = ∑ x, ∑ y, f x * g y := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]

noncomputable def exactlyOneCutTerm {α : Type*}
    (P Q : α → Prop) (w : α → ℤ) (u v : α) : ℤ := by
  classical
  exact if exactlyOne (cutDiff P u v) (cutDiff Q u v)
    then w u * w v else 0

noncomputable def evenCutSignTerm {α : Type*}
    (P Q : α → Prop) (w : α → ℤ) (u v : α) : ℤ := by
  classical
  exact if ¬ cutDiff P u v ∧ ¬ cutDiff Q u v then w u * w v
    else if cutDiff P u v ∧ cutDiff Q u v then -(w u * w v)
    else 0

/-- The ordered weighted sum over pairs on which exactly one of two
predicates changes is twice the product of the two checkerboard-class
masses. -/
theorem sum_exactlyOne_cutDiff {α : Type*} [Fintype α]
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (w : α → ℤ) :
    (∑ u, ∑ v, exactlyOneCutTerm P Q w u v) =
      2 * (cellTT P Q w + cellFF P Q w) *
        (cellTF P Q w + cellFT P Q w) := by
  classical
  let D : α → ℤ := fun x =>
    if (P x ∧ Q x) ∨ (¬ P x ∧ ¬ Q x) then w x else 0
  let O : α → ℤ := fun x =>
    if (P x ∧ ¬ Q x) ∨ (¬ P x ∧ Q x) then w x else 0
  have hD : (∑ x, D x) = cellTT P Q w + cellFF P Q w := by
    unfold D cellTT cellFF
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hP : P x <;> by_cases hQ : Q x <;> simp [hP, hQ]
  have hO : (∑ x, O x) = cellTF P Q w + cellFT P Q w := by
    unfold O cellTF cellFT
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hP : P x <;> by_cases hQ : Q x <;> simp [hP, hQ]
  calc
    (∑ u, ∑ v, exactlyOneCutTerm P Q w u v) =
        (∑ u, ∑ v, D u * O v) + ∑ u, ∑ v, O u * D v := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro u hu
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro v hv
          by_cases hPu : P u <;> by_cases hQu : Q u <;>
            by_cases hPv : P v <;> by_cases hQv : Q v <;>
              simp [D, O, exactlyOneCutTerm, exactlyOne, cutDiff,
                hPu, hQu, hPv, hQv]
    _ = (∑ u, D u) * (∑ v, O v) + (∑ u, O u) * (∑ v, D v) := by
      rw [fintype_sum_mul_sum, fintype_sum_mul_sum]
    _ = 2 * (cellTT P Q w + cellFF P Q w) *
          (cellTF P Q w + cellFT P Q w) := by
      rw [hD, hO]
      ring

/-- With zero cut changes counted positively and two cut changes negatively,
the all-ordered-pairs sum is the sum of two squares of opposite-cell mass
differences.  Removing the diagonal later subtracts `∑ x, w x ^ 2`. -/
theorem sum_evenCutSign {α : Type*} [Fintype α]
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (w : α → ℤ) :
    (∑ u, ∑ v, evenCutSignTerm P Q w u v) =
      (cellTT P Q w - cellFF P Q w) ^ 2 +
        (cellTF P Q w - cellFT P Q w) ^ 2 := by
  classical
  let A : α → ℤ := fun x =>
    if P x ∧ Q x then w x
    else if ¬ P x ∧ ¬ Q x then -w x else 0
  let B : α → ℤ := fun x =>
    if P x ∧ ¬ Q x then w x
    else if ¬ P x ∧ Q x then -w x else 0
  have hA : (∑ x, A x) = cellTT P Q w - cellFF P Q w := by
    unfold A cellTT cellFF
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hP : P x <;> by_cases hQ : Q x <;> simp [hP, hQ]
  have hB : (∑ x, B x) = cellTF P Q w - cellFT P Q w := by
    unfold B cellTF cellFT
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hP : P x <;> by_cases hQ : Q x <;> simp [hP, hQ]
  calc
    (∑ u, ∑ v, evenCutSignTerm P Q w u v) =
        (∑ u, ∑ v, A u * A v) + ∑ u, ∑ v, B u * B v := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro u hu
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro v hv
          by_cases hPu : P u <;> by_cases hQu : Q u <;>
            by_cases hPv : P v <;> by_cases hQv : Q v <;>
              simp [A, B, evenCutSignTerm, cutDiff, hPu, hQu, hPv, hQv]
    _ = (∑ u, A u) ^ 2 + (∑ u, B u) ^ 2 := by
      rw [pow_two, pow_two, fintype_sum_mul_sum, fintype_sum_mul_sum]
    _ = (cellTT P Q w - cellFF P Q w) ^ 2 +
          (cellTF P Q w - cellFT P Q w) ^ 2 := by
      rw [hA, hB]

end LeechTrees.OddEdges.T12Adapter.PairSums
