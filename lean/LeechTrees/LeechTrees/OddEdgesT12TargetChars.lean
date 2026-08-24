import LeechTrees.Foundations
import LeechTrees.OddEdges

open scoped BigOperators

namespace LeechTrees.OddEdges.TargetChars

open LeechTrees.Foundation

private theorem odd_filtered_half_sum_eq_range (N : ℕ) :
    (∑ k ∈ (Finset.Icc 1 N).filter Odd,
        (-1 : ℤ) ^ ((k - 1) / 2)) =
      ∑ j ∈ Finset.range ((N + 1) / 2), (-1 : ℤ) ^ j := by
  classical
  refine Finset.sum_bij'
      (s := (Finset.Icc 1 N).filter Odd)
      (t := Finset.range ((N + 1) / 2))
      (f := fun k => (-1 : ℤ) ^ ((k - 1) / 2))
      (g := fun j => (-1 : ℤ) ^ j)
      (fun k _ => (k - 1) / 2)
      (fun j _ => 2 * j + 1)
      ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk
    rcases hk.2 with ⟨a, ha⟩
    simp only [Finset.mem_range]
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    exact ⟨j, by omega⟩
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk
    rcases hk.2 with ⟨a, ha⟩
    change 2 * ((k - 1) / 2) + 1 = k
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    change (2 * j + 1 - 1) / 2 = j
    omega
  · intro k hk
    rfl

theorem odd_half_sum_Icc (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N,
        if Odd k then (-1 : ℤ) ^ ((k - 1) / 2) else 0) =
      if Even ((N + 1) / 2) then 0 else 1 := by
  classical
  rw [← Finset.sum_filter]
  rw [odd_filtered_half_sum_eq_range]
  exact alternating_sum_range ((N + 1) / 2)

private theorem even_filtered_half_sum_eq_neg_range (N : ℕ) :
    (∑ k ∈ (Finset.Icc 1 N).filter Even,
        (-1 : ℤ) ^ (k / 2)) =
      ∑ j ∈ Finset.range (N / 2), -((-1 : ℤ) ^ j) := by
  classical
  refine Finset.sum_bij'
      (s := (Finset.Icc 1 N).filter Even)
      (t := Finset.range (N / 2))
      (f := fun k => (-1 : ℤ) ^ (k / 2))
      (g := fun j => -((-1 : ℤ) ^ j))
      (fun k _ => k / 2 - 1)
      (fun j _ => 2 * (j + 1))
      ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk
    rcases hk.2 with ⟨a, ha⟩
    simp only [Finset.mem_range]
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    exact ⟨j + 1, by omega⟩
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk
    rcases hk.2 with ⟨a, ha⟩
    change 2 * (k / 2 - 1 + 1) = k
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    change 2 * (j + 1) / 2 - 1 = j
    omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk
    rcases hk.2 with ⟨a, ha⟩
    have hhalf : k / 2 = (k / 2 - 1) + 1 := by omega
    change (-1 : ℤ) ^ (k / 2) = -((-1 : ℤ) ^ (k / 2 - 1))
    calc
      (-1 : ℤ) ^ (k / 2) =
          (-1 : ℤ) ^ ((k / 2 - 1) + 1) :=
        congrArg (fun m : ℕ => (-1 : ℤ) ^ m) hhalf
      _ = -((-1 : ℤ) ^ (k / 2 - 1)) := by
        rw [pow_succ]
        ring

theorem even_half_sum_Icc (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N,
        if Even k then (-1 : ℤ) ^ (k / 2) else 0) =
      if Even (N / 2) then 0 else -1 := by
  classical
  rw [← Finset.sum_filter]
  rw [even_filtered_half_sum_eq_neg_range]
  calc
    (∑ j ∈ Finset.range (N / 2), -((-1 : ℤ) ^ j)) =
        -(∑ j ∈ Finset.range (N / 2), (-1 : ℤ) ^ j) := by
      rw [Finset.sum_neg_distrib]
    _ = -(if Even (N / 2) then 0 else 1) := by
      rw [alternating_sum_range]
    _ = if Even (N / 2) then 0 else -1 := by
      by_cases h : Even (N / 2) <;> simp [h]

theorem leech_odd_half_character {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) :
    (∑ p : VertexPair n,
        if Odd (T.pairDist p) then
          (-1 : ℤ) ^ ((T.pairDist p - 1) / 2)
        else 0) =
      if Even ((targetN n + 1) / 2) then 0 else 1 := by
  classical
  calc
    (∑ p : VertexPair n,
        if Odd (T.pairDist p) then
          (-1 : ℤ) ^ ((T.pairDist p - 1) / 2)
        else 0) =
        ∑ k : {k : ℕ // k ∈ Finset.Icc 1 (targetN n)},
          if Odd k.1 then (-1 : ℤ) ^ ((k.1 - 1) / 2) else 0 := by
      apply Fintype.sum_equiv hL.spectrumEquiv
      intro p
      rfl
    _ = ∑ k ∈ Finset.Icc 1 (targetN n),
          if Odd k then (-1 : ℤ) ^ ((k - 1) / 2) else 0 := by
      symm
      exact Finset.sum_subtype _ (fun _ => Iff.rfl) _
    _ = if Even ((targetN n + 1) / 2) then 0 else 1 :=
      odd_half_sum_Icc (targetN n)

theorem leech_even_half_character {n : ℕ} {T : PosIntTree n}
    (hL : IsLeech T) :
    (∑ p : VertexPair n,
        if Even (T.pairDist p) then
          (-1 : ℤ) ^ (T.pairDist p / 2)
        else 0) =
      if Even (targetN n / 2) then 0 else -1 := by
  classical
  calc
    (∑ p : VertexPair n,
        if Even (T.pairDist p) then
          (-1 : ℤ) ^ (T.pairDist p / 2)
        else 0) =
        ∑ k : {k : ℕ // k ∈ Finset.Icc 1 (targetN n)},
          if Even k.1 then (-1 : ℤ) ^ (k.1 / 2) else 0 := by
      apply Fintype.sum_equiv hL.spectrumEquiv
      intro p
      rfl
    _ = ∑ k ∈ Finset.Icc 1 (targetN n),
          if Even k then (-1 : ℤ) ^ (k / 2) else 0 := by
      symm
      exact Finset.sum_subtype _ (fun _ => Iff.rfl) _
    _ = if Even (targetN n / 2) then 0 else -1 :=
      even_half_sum_Icc (targetN n)

end LeechTrees.OddEdges.TargetChars
