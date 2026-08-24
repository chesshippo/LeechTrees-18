import LeechTrees.Expanded.Q2Bounds.G016GlobalTwoOdd
import LeechTrees.OddEdgesT11Adapter
import LeechTrees.OddQuotient.F9Endpoints

/-!
# The actual common-port interval factor

This module removes the first half of the former `CommonPortGraphBridge`.
Starting with the two actual odd physical edges and their common actual
endpoint, it proves that the two rooted descendant branches are disjoint,
identifies the middle and outer parity classes, and constructs the indexed
direct sum of the rooted half-depth supports with the full odd target
interval.  No polynomial support equality is accepted as input.
-/

namespace LeechTrees.G016.CommonPortAdapter

open LeechTrees.Foundation
open LeechTrees.OddEdges
open LeechTrees.OddEdges.GraphAdapter
open LeechTrees.OddEdges.T11Adapter
open LeechTrees.OddEdges.T12Adapter
open LeechTrees.OddQuotient

variable {n : ℕ}

/-- The two fixed actual odd edges together with their common actual port. -/
structure CommonPortFrame (T : PosIntTree n) (d : TwoOddEdges T) where
  port : Fin n
  port_e : port = T.edgeLeft d.e ∨ port = T.edgeRight d.e
  port_f : port = T.edgeLeft d.f ∨ port = T.edgeRight d.f

theorem frame_of_commonMiddlePort
    (T : PosIntTree n) (hTwo : ExactlyTwoOddPhysicalEdges T)
    (hCommon : LeechTrees.G016.CommonMiddlePort T hTwo) :
    Nonempty (CommonPortFrame T (twoOddEdges T hTwo)) := by
  dsimp only [LeechTrees.G016.CommonMiddlePort] at hCommon
  rcases hCommon with ⟨y, he, hf⟩
  exact ⟨⟨y, he, hf⟩⟩

namespace CommonPortFrame

variable {T : PosIntTree n} {d : TwoOddEdges T} (F : CommonPortFrame T d)

def IsMiddle (v : Fin n) : Prop :=
  ¬ rootUses T F.port d.e v ∧ ¬ rootUses T F.port d.f v

def IsOuter (v : Fin n) : Prop :=
  (rootUses T F.port d.e v ∧ ¬ rootUses T F.port d.f v) ∨
  (¬ rootUses T F.port d.e v ∧ rootUses T F.port d.f v)

abbrev MiddleVertex := {v : Fin n // F.IsMiddle v}
abbrev OuterVertex := {v : Fin n // F.IsOuter v}

private theorem e_only_nonempty :
    ∃ v : Fin n,
      rootUses T F.port d.e v ∧ ¬ rootUses T F.port d.f v := by
  rcases F.port_e with he | he
  · refine ⟨T.edgeRight d.e, ?_, ?_⟩
    · simp [rootUses, he, T.pathEdges_edge d.e]
    · simp only [rootUses, he, T.pathEdges_edge d.e,
        Finset.mem_singleton]
      exact fun h => d.ne (Subtype.ext h.symm)
  · refine ⟨T.edgeLeft d.e, ?_, ?_⟩
    · rw [rootUses, he, T.pathEdges_comm, T.pathEdges_edge d.e]
      simp
    · rw [rootUses, he, T.pathEdges_comm, T.pathEdges_edge d.e]
      simp only [Finset.mem_singleton]
      exact fun h => d.ne (Subtype.ext h.symm)

private theorem f_only_nonempty :
    ∃ v : Fin n,
      ¬ rootUses T F.port d.e v ∧ rootUses T F.port d.f v := by
  rcases F.port_f with hf | hf
  · refine ⟨T.edgeRight d.f, ?_, ?_⟩
    · simp only [rootUses, hf, T.pathEdges_edge d.f,
        Finset.mem_singleton]
      exact fun h => d.ne (Subtype.ext h)
    · simp [rootUses, hf, T.pathEdges_edge d.f]
  · refine ⟨T.edgeLeft d.f, ?_, ?_⟩
    · rw [rootUses, hf, T.pathEdges_comm, T.pathEdges_edge d.f]
      simp only [Finset.mem_singleton]
      exact fun h => d.ne (Subtype.ext h)
    · rw [rootUses, hf, T.pathEdges_comm, T.pathEdges_edge d.f]
      simp

private theorem e_only_at_edge_distance :
    ∃ v : Fin n,
      rootUses T F.port d.e v ∧ ¬ rootUses T F.port d.f v ∧
        T.dist F.port v = T.weight d.e := by
  rcases F.port_e with he | he
  · refine ⟨T.edgeRight d.e, ?_, ?_, ?_⟩
    · simp [rootUses, he, T.pathEdges_edge d.e]
    · simp only [rootUses, he, T.pathEdges_edge d.e,
        Finset.mem_singleton]
      exact fun h => d.ne (Subtype.ext h.symm)
    · rw [he, ← T.edgePair_dist d.e]
      rfl
  · refine ⟨T.edgeLeft d.e, ?_, ?_, ?_⟩
    · rw [rootUses, he, T.pathEdges_comm, T.pathEdges_edge d.e]
      simp
    · rw [rootUses, he, T.pathEdges_comm, T.pathEdges_edge d.e]
      simp only [Finset.mem_singleton]
      exact fun h => d.ne (Subtype.ext h.symm)
    · rw [he, T.dist_comm, ← T.edgePair_dist d.e]
      rfl

private theorem f_only_at_edge_distance :
    ∃ v : Fin n,
      ¬ rootUses T F.port d.e v ∧ rootUses T F.port d.f v ∧
        T.dist F.port v = T.weight d.f := by
  rcases F.port_f with hf | hf
  · refine ⟨T.edgeRight d.f, ?_, ?_, ?_⟩
    · simp only [rootUses, hf, T.pathEdges_edge d.f,
        Finset.mem_singleton]
      exact fun h => d.ne (Subtype.ext h)
    · simp [rootUses, hf, T.pathEdges_edge d.f]
    · rw [hf, ← T.edgePair_dist d.f]
      rfl
  · refine ⟨T.edgeLeft d.f, ?_, ?_, ?_⟩
    · rw [rootUses, hf, T.pathEdges_comm, T.pathEdges_edge d.f]
      simp only [Finset.mem_singleton]
      exact fun h => d.ne (Subtype.ext h)
    · rw [rootUses, hf, T.pathEdges_comm, T.pathEdges_edge d.f]
      simp
    · rw [hf, T.dist_comm, ← T.edgePair_dist d.f]
      rfl

/-- A rooted path from a common endpoint cannot use both distinct incident
edges.  This is derived from the general laminar-cut theorem by exhibiting
an actual vertex in each of the two one-edge cells. -/
theorem no_both (v : Fin n) :
    ¬(rootUses T F.port d.e v ∧ rootUses T F.port d.f v) := by
  rcases LeechTrees.OddEdges.T12Adapter.CutLemma.one_of_three_root_path_cells_empty
      T d.e d.f d.ne F.port with he | hf | hboth
  · obtain ⟨x, hxe, hxf⟩ := F.e_only_nonempty
    exact (he x ⟨hxe, hxf⟩).elim
  · obtain ⟨x, hxe, hxf⟩ := F.f_only_nonempty
    exact (hf x ⟨hxe, hxf⟩).elim
  · simpa [rootUses] using hboth v

theorem middle_or_outer (v : Fin n) : F.IsMiddle v ∨ F.IsOuter v := by
  by_cases he : rootUses T F.port d.e v <;>
    by_cases hf : rootUses T F.port d.f v
  · exact (F.no_both v ⟨he, hf⟩).elim
  · exact Or.inr (Or.inl ⟨he, hf⟩)
  · exact Or.inr (Or.inr ⟨he, hf⟩)
  · exact Or.inl ⟨he, hf⟩

theorem outer_iff_not_middle (v : Fin n) :
    F.IsOuter v ↔ ¬F.IsMiddle v := by
  constructor
  · rintro (h | h) hm
    · exact hm.1 h.1
    · exact hm.2 h.2
  · intro hnot
    rcases F.middle_or_outer v with hm | ho
    · exact (hnot hm).elim
    · exact ho

theorem port_middle : F.IsMiddle F.port := by
  simp [IsMiddle, rootUses, T.pathEdges_self]

noncomputable instance : Fintype F.MiddleVertex := Fintype.ofFinite _
noncomputable instance : Fintype F.OuterVertex := Fintype.ofFinite _

theorem middle_nonempty : Nonempty F.MiddleVertex :=
  ⟨⟨F.port, F.port_middle⟩⟩

theorem outer_nonempty : Nonempty F.OuterVertex := by
  obtain ⟨v, he, hf⟩ := F.e_only_nonempty
  exact ⟨⟨v, Or.inl ⟨he, hf⟩⟩⟩

private noncomputable def rootUseBit (P : Prop) : ℕ := by
  classical
  exact if P then 1 else 0

private theorem rootDist_mod_two (v : Fin n) :
    T.dist F.port v % 2 =
      (rootUseBit (rootUses T F.port d.e v) +
        rootUseBit (rootUses T F.port d.f v)) % 2 := by
  classical
  by_cases hv : F.port = v
  · subst v
    rw [T.dist_self F.port]
    unfold rootUses
    rw [T.pathEdges_self F.port]
    simp [rootUseBit]
  · let p := VertexPair.ofDistinct F.port v hv
    have hpdist : T.pairDist p = T.dist F.port v :=
      T.pairDist_pairOfDistinct F.port v hv
    have hpaths : T.pathEdges p.left p.right = T.pathEdges F.port v := by
      dsimp only [p]
      by_cases hlt : F.port < v
      · simp [VertexPair.ofDistinct, hlt, VertexPair.left, VertexPair.right]
      · simp [VertexPair.ofDistinct, hlt, VertexPair.left, VertexPair.right,
          T.pathEdges_comm v F.port]
    have hrel := ceilHalf_pairDist_relation_fixed T d p
    rw [hpdist] at hrel
    unfold PosIntTree.pathIncidence at hrel
    rw [hpaths] at hrel
    unfold rootUseBit
    simp only [rootUses]
    split_ifs at hrel ⊢ <;> omega

theorem middle_iff_root_even (v : Fin n) :
    F.IsMiddle v ↔ T.dist F.port v % 2 = 0 := by
  have hpar := F.rootDist_mod_two v
  by_cases he : rootUses T F.port d.e v <;>
    by_cases hf : rootUses T F.port d.f v
  · exact (F.no_both v ⟨he, hf⟩).elim
  · simp [rootUseBit, IsMiddle, he, hf] at hpar ⊢
    exact hpar
  · simp [rootUseBit, IsMiddle, he, hf] at hpar ⊢
    exact hpar
  · simp [rootUseBit, IsMiddle, he, hf] at hpar ⊢
    exact hpar

theorem outer_iff_root_odd (v : Fin n) :
    F.IsOuter v ↔ T.dist F.port v % 2 = 1 := by
  rw [F.outer_iff_not_middle, F.middle_iff_root_even]
  have hlt := Nat.mod_lt (T.dist F.port v) (by omega : 0 < 2)
  omega

/-- The common port lies on every path from the middle class to the outer
class. -/
private theorem dist_add_of_incident_edge
    (e : T.Edge)
    (hy : F.port = T.edgeLeft e ∨ F.port = T.edgeRight e)
    {u v : Fin n}
    (hu : e.1 ∉ T.pathEdges F.port u)
    (hv : e.1 ∈ T.pathEdges F.port v) :
    T.dist u v = T.dist u F.port + T.dist F.port v := by
  rcases hy with hy | hy
  · rw [hy] at hu hv ⊢
    have huL : T.LeftCut e u := by
      have hreach := (T.cut_reachable_iff_not_mem_pathEdges e
        (T.edgeLeft e) u).2 hu
      exact hreach.symm.trans (T.edgeLeft_mem_LeftCut e)
    have hvR : T.RightCut e v := by
      rcases (T.mem_pathEdges_iff_opposite_cuts e (T.edgeLeft e) v).1 hv with
        h | h
      · exact h.2
      · exact (T.LeftCut_disjoint_RightCut e (T.edgeLeft e)
          ⟨T.edgeLeft_mem_LeftCut e, h.1⟩).elim
    have huv := T.cross_distance_decomposition e huL hvR
    have hyv := T.cross_distance_decomposition e
      (T.edgeLeft_mem_LeftCut e) hvR
    rw [T.dist_self] at hyv
    omega
  · rw [hy] at hu hv ⊢
    have huR : T.RightCut e u := by
      have hreach := (T.cut_reachable_iff_not_mem_pathEdges e
        (T.edgeRight e) u).2 hu
      exact hreach.symm.trans (T.edgeRight_mem_RightCut e)
    have hvL : T.LeftCut e v := by
      rcases (T.mem_pathEdges_iff_opposite_cuts e (T.edgeRight e) v).1 hv with
        h | h
      · exact (T.LeftCut_disjoint_RightCut e (T.edgeRight e)
          ⟨h.1, T.edgeRight_mem_RightCut e⟩).elim
      · exact h.2
    have hvu := T.cross_distance_decomposition e hvL huR
    have hvy := T.cross_distance_decomposition e hvL
      (T.edgeRight_mem_RightCut e)
    rw [T.dist_self] at hvy
    rw [T.dist_comm u v, T.dist_comm u (T.edgeRight e),
      T.dist_comm (T.edgeRight e) v]
    omega

theorem middle_outer_dist_add (u : F.MiddleVertex) (v : F.OuterVertex) :
    T.dist u.1 v.1 = T.dist u.1 F.port + T.dist F.port v.1 := by
  rcases v.2 with h | h
  · exact F.dist_add_of_incident_edge d.e F.port_e u.2.1 h.1
  · exact F.dist_add_of_incident_edge d.f F.port_f u.2.2 h.2

noncomputable def middleDepth (u : F.MiddleVertex) : ℕ :=
  T.dist F.port u.1 / 2

noncomputable def outerDepth (v : F.OuterVertex) : ℕ :=
  T.dist F.port v.1 / 2

theorem middleDepth_twice (u : F.MiddleVertex) :
    2 * F.middleDepth u = T.dist F.port u.1 := by
  have h := (F.middle_iff_root_even u.1).1 u.2
  unfold middleDepth
  omega

theorem outerDepth_twice_add_one (v : F.OuterVertex) :
    2 * F.outerDepth v + 1 = T.dist F.port v.1 := by
  have h := (F.outer_iff_root_odd v.1).1 v.2
  unfold outerDepth
  omega

private theorem middle_outer_ne (u : F.MiddleVertex) (v : F.OuterVertex) :
    u.1 ≠ v.1 := by
  intro h
  have : F.IsOuter u.1 := by simpa [h] using v.2
  exact (F.outer_iff_not_middle u.1).1 this u.2

noncomputable def middleOuterPair
    (z : F.MiddleVertex × F.OuterVertex) : VertexPair n :=
  VertexPair.ofDistinct z.1.1 z.2.1 (F.middle_outer_ne z.1 z.2)

theorem middleOuterPair_dist (z : F.MiddleVertex × F.OuterVertex) :
    T.pairDist (F.middleOuterPair z) = T.dist z.1.1 z.2.1 :=
  T.pairDist_pairOfDistinct _ _ _

theorem middleOuterPair_odd (z : F.MiddleVertex × F.OuterVertex) :
    T.pairDist (F.middleOuterPair z) % 2 = 1 := by
  rw [F.middleOuterPair_dist, F.middle_outer_dist_add]
  have hm := F.middleDepth_twice z.1
  have ho := F.outerDepth_twice_add_one z.2
  rw [T.dist_comm z.1.1 F.port]
  omega

theorem middleOuterPair_halfRank (z : F.MiddleVertex × F.OuterVertex) :
    T.pairDist (F.middleOuterPair z) / 2 =
      F.middleDepth z.1 + F.outerDepth z.2 := by
  rw [F.middleOuterPair_dist, F.middle_outer_dist_add,
    T.dist_comm z.1.1 F.port]
  have hm := F.middleDepth_twice z.1
  have ho := F.outerDepth_twice_add_one z.2
  omega

noncomputable def outerEquivComplement :
    F.OuterVertex ≃ {v : Fin n // ¬F.IsMiddle v} :=
  Equiv.subtypeEquivProp <| funext fun v => propext (F.outer_iff_not_middle v)

theorem pair_odd_iff_opposite_middle (p : VertexPair n) :
    T.pairDist p % 2 = 1 ↔
      (F.IsMiddle p.left ∧ ¬F.IsMiddle p.right) ∨
      (¬F.IsMiddle p.left ∧ F.IsMiddle p.right) := by
  rw [T.pairDist_odd_iff_root_opposite F.port p,
    F.middle_iff_root_even p.left, F.middle_iff_root_even p.right]
  have hl := Nat.mod_lt (T.dist F.port p.left) (by omega : 0 < 2)
  have hr := Nat.mod_lt (T.dist F.port p.right) (by omega : 0 < 2)
  constructor
  · rintro (⟨hl0, hr1⟩ | ⟨hl1, hr0⟩)
    · exact Or.inl ⟨hl0, by omega⟩
    · exact Or.inr ⟨by omega, hr0⟩
  · rintro (⟨hl0, hr0⟩ | ⟨hl0, hr0⟩)
    · exact Or.inl ⟨hl0, by omega⟩
    · exact Or.inr ⟨by omega, hr0⟩

/-- Exact reindexing of every odd pair by one middle and one outer vertex. -/
noncomputable def middleOuterOddPairEquiv :
    (F.MiddleVertex × F.OuterVertex) ≃ OddVertexPair T :=
  (Equiv.prodCongr (Equiv.refl _) F.outerEquivComplement).trans <|
    (oppositePairEquiv F.IsMiddle).trans <|
      Equiv.subtypeEquivProp <| funext fun p =>
        propext (F.pair_odd_iff_opposite_middle p).symm

theorem middleOuterOddPairEquiv_val
    (z : F.MiddleVertex × F.OuterVertex) :
    (F.middleOuterOddPairEquiv z).1 = F.middleOuterPair z := by
  rfl

/-- The actual common-port odd-rank bijection. -/
noncomputable def middleOuterRankEquiv (hL : IsLeech T) :
    (F.MiddleVertex × F.OuterVertex) ≃
      Fin ((targetN n + 1) / 2) :=
  F.middleOuterOddPairEquiv.trans
    (LeechTrees.OddQuotient.IsLeech.oddHalfRankEquiv hL)

theorem middleOuterRankEquiv_val
    (hL : IsLeech T) (z : F.MiddleVertex × F.OuterVertex) :
    (F.middleOuterRankEquiv hL z : ℕ) =
      F.middleDepth z.1 + F.outerDepth z.2 := by
  rw [middleOuterRankEquiv, Equiv.trans_apply,
    LeechTrees.OddQuotient.IsLeech.oddHalfRankEquiv_val,
    F.middleOuterOddPairEquiv_val,
    F.middleOuterPair_halfRank]

theorem middleDepth_injective (hL : IsLeech T) :
    Function.Injective F.middleDepth := by
  let v₀ : F.OuterVertex := Classical.choice F.outer_nonempty
  intro u u' huu'
  have hpair : (u, v₀) = (u', v₀) :=
    (F.middleOuterRankEquiv hL).injective <| Fin.ext <| by
      rw [F.middleOuterRankEquiv_val, F.middleOuterRankEquiv_val, huu']
  exact congrArg Prod.fst hpair

theorem outerDepth_injective (hL : IsLeech T) :
    Function.Injective F.outerDepth := by
  let u₀ : F.MiddleVertex := Classical.choice F.middle_nonempty
  intro v v' hvv'
  have hpair : (u₀, v) = (u₀, v') :=
    (F.middleOuterRankEquiv hL).injective <| Fin.ext <| by
      rw [F.middleOuterRankEquiv_val, F.middleOuterRankEquiv_val, hvv']
  exact congrArg Prod.snd hpair

noncomputable def middleDepthSet : Finset ℕ :=
  Finset.univ.image F.middleDepth

noncomputable def outerDepthSet : Finset ℕ :=
  Finset.univ.image F.outerDepth

theorem zero_mem_middleDepthSet : 0 ∈ F.middleDepthSet := by
  rw [middleDepthSet, Finset.mem_image]
  refine ⟨⟨F.port, F.port_middle⟩, Finset.mem_univ _, ?_⟩
  simp [middleDepth]

theorem zero_mem_outerDepthSet (hL : IsLeech T) (hn : 2 ≤ n) :
    0 ∈ F.outerDepthSet := by
  obtain ⟨u, hu, _⟩ := t1_existsUnique_weight_one hL hn
  have huOdd : Odd (T.weight u) := by simp [hu]
  rcases (d.odd_iff u).mp huOdd with hue | huf
  · obtain ⟨v, he, hf, hd⟩ := F.e_only_at_edge_distance
    let x : F.OuterVertex := ⟨v, Or.inl ⟨he, hf⟩⟩
    rw [outerDepthSet, Finset.mem_image]
    refine ⟨x, Finset.mem_univ _, ?_⟩
    unfold outerDepth
    rw [hd, ← hue, hu]
  · obtain ⟨v, he, hf, hd⟩ := F.f_only_at_edge_distance
    let x : F.OuterVertex := ⟨v, Or.inr ⟨he, hf⟩⟩
    rw [outerDepthSet, Finset.mem_image]
    refine ⟨x, Finset.mem_univ _, ?_⟩
    unfold outerDepth
    rw [hd, ← huf, hu]

noncomputable def middleDepthEquiv (hL : IsLeech T) :
    F.MiddleVertex ≃ ↑F.middleDepthSet := by
  let f : F.MiddleVertex → ↑F.middleDepthSet := fun u =>
    ⟨F.middleDepth u, by simp [middleDepthSet]⟩
  apply Equiv.ofBijective f
  constructor
  · intro u v h
    apply F.middleDepth_injective hL
    exact congrArg Subtype.val h
  · intro x
    rcases Finset.mem_image.mp x.2 with ⟨u, _, hu⟩
    exact ⟨u, Subtype.ext hu⟩

noncomputable def outerDepthEquiv (hL : IsLeech T) :
    F.OuterVertex ≃ ↑F.outerDepthSet := by
  let f : F.OuterVertex → ↑F.outerDepthSet := fun v =>
    ⟨F.outerDepth v, by simp [outerDepthSet]⟩
  apply Equiv.ofBijective f
  constructor
  · intro u v h
    apply F.outerDepth_injective hL
    exact congrArg Subtype.val h
  · intro x
    rcases Finset.mem_image.mp x.2 with ⟨v, _, hv⟩
    exact ⟨v, Subtype.ext hv⟩

theorem middleDepthSet_card (hL : IsLeech T) :
    F.middleDepthSet.card = Fintype.card F.MiddleVertex := by
  rw [← Fintype.card_coe,
    ← Fintype.card_congr (F.middleDepthEquiv hL)]

theorem outerDepthSet_card (hL : IsLeech T) :
    F.outerDepthSet.card = Fintype.card F.OuterVertex := by
  rw [← Fintype.card_coe,
    ← Fintype.card_congr (F.outerDepthEquiv hL)]

/-- The full graph-derived interval factor.  Its equivalence is the composite
of the actual middle/outer pair partition and the exact Leech odd-spectrum
equivalence, so uniqueness and coverage are indexed rather than inferred
from a deduplicated support identity. -/
noncomputable def intervalDirectSum
    (hL : IsLeech T) :
    IntervalDirectSum F.middleDepthSet F.outerDepthSet
      ((targetN n + 1) / 2) where
  equiv :=
    (Equiv.prodCongr (F.middleDepthEquiv hL).symm
      (F.outerDepthEquiv hL).symm).trans
        (F.middleOuterRankEquiv hL)
  sum_eq := by
    intro p
    let u := (F.middleDepthEquiv hL).symm p.1
    let v := (F.outerDepthEquiv hL).symm p.2
    change (F.middleOuterRankEquiv hL (u, v) : ℕ) =
      (p.1 : ℕ) + (p.2 : ℕ)
    rw [F.middleOuterRankEquiv_val]
    have hu := congrArg Subtype.val
      ((F.middleDepthEquiv hL).apply_symm_apply p.1)
    have hv := congrArg Subtype.val
      ((F.outerDepthEquiv hL).apply_symm_apply p.2)
    change F.middleDepth u = (p.1 : ℕ) at hu
    change F.outerDepth v = (p.2 : ℕ) at hv
    change F.middleDepth u + F.outerDepth v =
      (p.1 : ℕ) + (p.2 : ℕ)
    rw [hu, hv]

theorem interval_card_product (hL : IsLeech T) :
    Fintype.card F.MiddleVertex * Fintype.card F.OuterVertex =
      (targetN n + 1) / 2 := by
  rw [← F.middleDepthSet_card hL, ← F.outerDepthSet_card hL]
  exact (F.intervalDirectSum hL).card_mul

end CommonPortFrame

/-- Public actual-graph construction replacing the factor-extraction clause
of `CommonPortGraphBridge`. -/
theorem actual_commonPort_intervalFactor
    (T : PosIntTree n) (hL : IsLeech T) (hn : 2 ≤ n)
    (hTwo : ExactlyTwoOddPhysicalEdges T)
    (hCommon : LeechTrees.G016.CommonMiddlePort T hTwo) :
    ∃ F : CommonPortFrame T (twoOddEdges T hTwo),
      Nonempty (IntervalDirectSum F.middleDepthSet F.outerDepthSet
          ((targetN n + 1) / 2)) ∧
        0 ∈ F.middleDepthSet ∧ 0 ∈ F.outerDepthSet ∧
        Fintype.card F.MiddleVertex * Fintype.card F.OuterVertex =
          (targetN n + 1) / 2 := by
  let F := Classical.choice (frame_of_commonMiddlePort T hTwo hCommon)
  exact ⟨F, ⟨F.intervalDirectSum hL⟩, F.zero_mem_middleDepthSet,
    F.zero_mem_outerDepthSet hL hn, F.interval_card_product hL⟩

end LeechTrees.G016.CommonPortAdapter
