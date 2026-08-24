import LeechTrees.ParityTail
import LeechTrees.QHop.CoreCountAdapter

/-!
# Joint signed-cut flow

This module formalizes G009 and the G024(b) marginal false positive.  The
generic model is an exact finite rooted-tree interface: its fields are only
the parent/child incidence, rooted depths, descendant-set decomposition, and
the two structural induction principles.  No residual sign, flow equation,
or realizability conclusion is assumed.
-/

open scoped BigOperators

namespace LeechTrees.SignedCutFlow

open LeechTrees.ParityTail

noncomputable section

/-- Exact finite rooted-tree interface used by the flow theorem. -/
structure Model (V : Type*) [Fintype V] [DecidableEq V] where
  root : V
  parent : V → V
  weightToParent : V → ℕ
  children : V → Finset V
  child_ne_root : ∀ {v u}, u ∈ children v → u ≠ root
  child_parent : ∀ {v u}, u ∈ children v → parent u = v
  depth : V → ℕ
  depth_root : depth root = 0
  depth_parent_add_weight : ∀ v, v ≠ root →
    depth v = depth (parent v) + weightToParent v
  subtree : V → Finset V
  root_subtree : subtree root = Finset.univ
  subtree_sum_decomp : ∀ (f : V → ℤ) v,
    (∑ z ∈ subtree v, f z) =
      f v + ∑ u ∈ children v, ∑ z ∈ subtree u, f z
  bottomUp : ∀ (P : V → Prop),
    (∀ v, (∀ u ∈ children v, P u) → P v) → ∀ v, P v
  topDown : ∀ (P : V → Prop), P root →
    (∀ v, v ≠ root → P (parent v) → P v) → ∀ v, P v

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Model

variable (R : Model V)

/-- Residual vertex sign reconstructed from a family of oriented cut sums. -/
def residual (delta : ℤ) (x : V → ℤ) (v : V) : ℤ :=
  if v = R.root then delta - ∑ u ∈ R.children v, x u
  else x v - ∑ u ∈ R.children v, x u

def IsPlusMinusOne (_R : Model V) (sigma : V → ℤ) : Prop :=
  ∀ v, sigma v = 1 ∨ sigma v = -1

def SatisfiesEdgeParity (sigma : V → ℤ) : Prop :=
  ∀ v, v ≠ R.root →
    sigma (R.parent v) * sigma v = paritySign (R.weightToParent v)

/-- Weighted-depth parity character, allowing the audited global sign. -/
def IsWeightedDepthCharacter (sigma : V → ℤ) : Prop :=
  ∃ g : ℤ, (g = 1 ∨ g = -1) ∧
    ∀ v, sigma v = g * paritySign (R.depth v)

/-- One common character realizes all oriented descendant cut sums. -/
def Realizes (delta : ℤ) (x sigma : V → ℤ) : Prop :=
  R.IsWeightedDepthCharacter sigma ∧
  (∑ v : V, sigma v) = delta ∧
  ∀ v, v ≠ R.root → x v = ∑ z ∈ R.subtree v, sigma z

theorem paritySign_pm (d : ℕ) : paritySign d = 1 ∨ paritySign d = -1 := by
  unfold paritySign
  rw [neg_one_pow_eq_pow_mod_two]
  have hlt : d % 2 < 2 := Nat.mod_lt _ (by omega)
  interval_cases h : d % 2 <;> norm_num [h]

theorem weightedDepthCharacter_pm
    {sigma : V → ℤ} (h : R.IsWeightedDepthCharacter sigma) :
    R.IsPlusMinusOne sigma := by
  rcases h with ⟨g, hg, hsig⟩
  intro v
  rcases hg with rfl | rfl <;>
    rcases paritySign_pm (R.depth v) with hp | hp <;>
    simp [hsig v, hp]

theorem weightedDepthCharacter_edgeParity
    {sigma : V → ℤ} (h : R.IsWeightedDepthCharacter sigma) :
    R.SatisfiesEdgeParity sigma := by
  rcases h with ⟨g, hg, hsig⟩
  intro v hv
  have hdepth := R.depth_parent_add_weight v hv
  have hp := paritySign_pm (R.depth (R.parent v))
  rw [hsig, hsig, hdepth, ← paritySign_add]
  rcases hg with rfl | rfl <;> rcases hp with hp | hp <;>
    rw [hp] <;> norm_num

theorem weightedDepthCharacter_iff_pm_and_edgeParity (sigma : V → ℤ) :
    R.IsWeightedDepthCharacter sigma ↔
      R.IsPlusMinusOne sigma ∧ R.SatisfiesEdgeParity sigma := by
  constructor
  · intro h
    exact ⟨R.weightedDepthCharacter_pm h,
      R.weightedDepthCharacter_edgeParity h⟩
  · rintro ⟨hpm, hedge⟩
    refine ⟨sigma R.root, hpm R.root, ?_⟩
    apply R.topDown (fun v => sigma v = sigma R.root * paritySign (R.depth v))
    · rw [R.depth_root]
      simp [paritySign]
    · intro v hv ih
      have hp := hpm (R.parent v)
      have he := hedge v hv
      have hdepth := R.depth_parent_add_weight v hv
      rw [hdepth, ← paritySign_add, ← mul_assoc, ← ih]
      rcases hp with hp | hp <;> rw [hp] at he ⊢ <;> norm_num at he ⊢
      · exact he
      · linarith

private theorem residual_eq_of_realizes
    {delta : ℤ} {x sigma : V → ℤ}
    (hreal : R.Realizes delta x sigma) :
    ∀ v, R.residual delta x v = sigma v := by
  intro v
  rcases hreal with ⟨hchar, htotal, hcuts⟩
  by_cases hv : v = R.root
  · subst v
    rw [residual, if_pos rfl]
    have hroot := R.subtree_sum_decomp sigma R.root
    rw [R.root_subtree] at hroot
    have hchildren :
        (∑ u ∈ R.children R.root, x u) =
          ∑ u ∈ R.children R.root,
            ∑ z ∈ R.subtree u, sigma z := by
      apply Finset.sum_congr rfl
      intro u hu
      exact hcuts u (R.child_ne_root hu)
    rw [hchildren]
    rw [← htotal, hroot]
    ring
  · rw [residual, if_neg hv, hcuts v hv,
      R.subtree_sum_decomp sigma v]
    have hchildren :
        (∑ u ∈ R.children v, x u) =
          ∑ u ∈ R.children v,
            ∑ z ∈ R.subtree u, sigma z := by
      apply Finset.sum_congr rfl
      intro u hu
      exact hcuts u (R.child_ne_root hu)
    rw [hchildren]
    ring

/-- The exact joint signed-cut-flow iff. -/
theorem joint_signed_cut_flow_iff (delta : ℤ) (x : V → ℤ) :
    (∃ sigma : V → ℤ, R.Realizes delta x sigma) ↔
      (∀ v, R.residual delta x v = 1 ∨
        R.residual delta x v = -1) ∧
      ∀ v, v ≠ R.root →
        R.residual delta x (R.parent v) * R.residual delta x v =
          paritySign (R.weightToParent v) := by
  constructor
  · rintro ⟨sigma, hreal⟩
    have hres := R.residual_eq_of_realizes hreal
    have hpm := R.weightedDepthCharacter_pm hreal.1
    have hedge := R.weightedDepthCharacter_edgeParity hreal.1
    constructor
    · intro v
      rw [hres v]
      exact hpm v
    · intro v hv
      rw [hres, hres]
      exact hedge v hv
  · rintro ⟨hpm, hedge⟩
    let b : V → ℤ := R.residual delta x
    have hbchar : R.IsWeightedDepthCharacter b :=
      (R.weightedDepthCharacter_iff_pm_and_edgeParity b).2
        ⟨hpm, hedge⟩
    have hrecover : ∀ v,
        if v = R.root then delta = ∑ z ∈ R.subtree v, b z
        else x v = ∑ z ∈ R.subtree v, b z := by
      apply R.bottomUp
      intro v ih
      by_cases hv : v = R.root
      · subst v
        rw [if_pos rfl, R.subtree_sum_decomp]
        have hchildren :
            (∑ u ∈ R.children R.root,
              ∑ z ∈ R.subtree u, b z) =
              ∑ u ∈ R.children R.root, x u := by
          apply Finset.sum_congr rfl
          intro u hu
          have hu' := ih u hu
          rw [if_neg (R.child_ne_root hu)] at hu'
          exact hu'.symm
        rw [hchildren]
        simp [b, residual]
      · rw [if_neg hv, R.subtree_sum_decomp]
        have hchildren :
            (∑ u ∈ R.children v,
              ∑ z ∈ R.subtree u, b z) =
              ∑ u ∈ R.children v, x u := by
          apply Finset.sum_congr rfl
          intro u hu
          have hu' := ih u hu
          rw [if_neg (R.child_ne_root hu)] at hu'
          exact hu'.symm
        rw [hchildren]
        simp [b, residual, hv]
    refine ⟨b, hbchar, ?_, ?_⟩
    · have hroot := hrecover R.root
      rw [if_pos rfl, R.root_subtree] at hroot
      simpa using hroot.symm
    · intro v hv
      have hv' := hrecover v
      rw [if_neg hv] at hv'
      exact hv'

/-- Opposite global normalization is the same theorem with `delta=-4`. -/
theorem joint_signed_cut_flow_iff_neg_four (x : V → ℤ) :
    (∃ sigma : V → ℤ, R.Realizes (-4) x sigma) ↔
      (∀ v, R.residual (-4) x v = 1 ∨
        R.residual (-4) x v = -1) ∧
      ∀ v, v ≠ R.root →
        R.residual (-4) x (R.parent v) * R.residual (-4) x v =
          paritySign (R.weightToParent v) :=
  R.joint_signed_cut_flow_iff (-4) x

end Model

/-! ## Construction from an honest finite parent relation

`Model` is convenient for the algebra above, but its decomposition and
induction fields must not be treated as extra hypotheses at a graph-level
endpoint.  The following smaller structure contains only a root, a parent
map which decreases an integer level, and the actual edge weights/depths.
Children, descendant sets, their disjoint decomposition, and both induction
principles are proved below.
-/

/-- Minimal data for a finite rooted parent tree.  In particular, no cut
sum, residual-sign, flow, subtree decomposition, or induction conclusion is
a field of this structure. -/
structure ParentData (V : Type*) [Fintype V] [DecidableEq V] where
  root : V
  parent : V → V
  level : V → ℕ
  level_root : level root = 0
  level_parent_add_one : ∀ v, v ≠ root →
    level v = level (parent v) + 1
  weightToParent : V → ℕ
  depth : V → ℕ
  depth_root : depth root = 0
  depth_parent_add_weight : ∀ v, v ≠ root →
    depth v = depth (parent v) + weightToParent v

namespace ParentData

variable (D : ParentData V)

/-- One step towards the root. -/
def Step (E : ParentData V) (u v : V) : Prop :=
  u ≠ E.root ∧ E.parent u = v

/-- `z` is a descendant of `v` when repeated parent steps take `z` to `v`. -/
def Descendant (E : ParentData V) (v z : V) : Prop :=
  Relation.ReflTransGen E.Step z v

noncomputable def children (E : ParentData V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun u => E.Step u v)

noncomputable def subtree (E : ParentData V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun z => E.Descendant v z)

@[simp] theorem mem_children (v u : V) :
    u ∈ D.children v ↔ D.Step u v := by
  classical
  simp [children]

@[simp] theorem mem_subtree (v z : V) :
    z ∈ D.subtree v ↔ D.Descendant v z := by
  classical
  simp [subtree]

theorem step_rightUnique : Relator.RightUnique D.Step := by
  rintro u v w ⟨_, huv⟩ ⟨_, huw⟩
  exact huv.symm.trans huw

/-- Levels can only decrease while following parent steps. -/
theorem level_le_of_descendant {v z : V} (h : D.Descendant v z) :
    D.level v ≤ D.level z := by
  induction h with
  | refl => exact Nat.le_refl _
  | @tail u v _ huv ih =>
      rcases huv with ⟨hu, rfl⟩
      have hdrop : D.level (D.parent u) < D.level u := by
        rw [D.level_parent_add_one u hu]
        omega
      exact (Nat.le_of_lt hdrop).trans ih

/-- A descendant at the same level is the vertex itself. -/
theorem eq_of_descendant_of_level_eq {v z : V}
    (h : D.Descendant v z) (hlevel : D.level z = D.level v) : z = v := by
  rcases Relation.ReflTransGen.cases_tail h with hv | ⟨u, hzu, huv⟩
  · exact hv.symm
  · have huv_lt : D.level v < D.level u := by
      rcases huv with ⟨hu, rfl⟩
      rw [D.level_parent_add_one u hu]
      omega
    have huz_le : D.level u ≤ D.level z :=
      D.level_le_of_descendant hzu
    omega

/-- Every vertex reaches the root.  This is derived by strong induction on
the strictly decreasing level, not stored in `ParentData`. -/
theorem descendant_root (v : V) : D.Descendant D.root v := by
  generalize hk : D.level v = k
  induction k using Nat.strong_induction_on generalizing v with
  | h k ih =>
      by_cases hv : v = D.root
      · subst v
        exact Relation.ReflTransGen.refl
      · have hp_lt : D.level (D.parent v) < k := by
          have hstep := D.level_parent_add_one v hv
          omega
        have hp : D.Descendant D.root (D.parent v) :=
          ih _ hp_lt (D.parent v) rfl
        exact hp.head ⟨hv, rfl⟩

theorem descendant_iff_self_or_child (v z : V) :
    D.Descendant v z ↔
      z = v ∨ ∃ u, D.Step u v ∧ D.Descendant u z := by
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_tail h with hv | ⟨u, hzu, huv⟩
    · exact Or.inl hv.symm
    · exact Or.inr ⟨u, huv, hzu⟩
  · rintro (rfl | ⟨u, huv, hzu⟩)
    · exact Relation.ReflTransGen.refl
    · exact hzu.tail huv

theorem subtree_pairwiseDisjoint (v : V) :
    (↑(D.children v) : Set V).PairwiseDisjoint D.subtree := by
  classical
  intro u hu w hw huw
  change Disjoint (D.subtree u) (D.subtree w)
  rw [Finset.disjoint_left]
  intro z hzu hzw
  have hdu : D.Descendant u z := (D.mem_subtree u z).1 hzu
  have hdw : D.Descendant w z := (D.mem_subtree w z).1 hzw
  have hlevels : D.level u = D.level w := by
    have huStep : D.Step u v := (D.mem_children v u).1 hu
    have hwStep : D.Step w v := (D.mem_children v w).1 hw
    rcases huStep with ⟨hune, hup⟩
    rcases hwStep with ⟨hwne, hwp⟩
    have hlu := D.level_parent_add_one u hune
    have hlw := D.level_parent_add_one w hwne
    rw [hup] at hlu
    rw [hwp] at hlw
    omega
  rcases Relation.ReflTransGen.total_of_right_unique
      D.step_rightUnique hdu hdw with hud | hwu
  · exact huw (D.eq_of_descendant_of_level_eq hud hlevels)
  · exact huw (D.eq_of_descendant_of_level_eq hwu hlevels.symm).symm

theorem subtree_eq_insert_child_union (v : V) :
    D.subtree v =
      insert v ((D.children v).biUnion fun u => D.subtree u) := by
  classical
  ext z
  simp only [D.mem_subtree, Finset.mem_insert, Finset.mem_biUnion,
    D.mem_children]
  exact D.descendant_iff_self_or_child v z

theorem self_not_mem_child_union (v : V) :
    v ∉ (D.children v).biUnion fun u => D.subtree u := by
  classical
  intro hv
  rcases Finset.mem_biUnion.mp hv with ⟨u, hu, hvu⟩
  have huStep : D.Step u v := (D.mem_children v u).1 hu
  have hdesc : D.Descendant u v := (D.mem_subtree u v).1 hvu
  have hle : D.level u ≤ D.level v := D.level_le_of_descendant hdesc
  rcases huStep with ⟨hune, hup⟩
  have hlevel := D.level_parent_add_one u hune
  rw [hup] at hlevel
  omega

/-- Exact disjoint descendant decomposition, derived from the parent map. -/
theorem subtree_sum_decomp (f : V → ℤ) (v : V) :
    (∑ z ∈ D.subtree v, f z) =
      f v + ∑ u ∈ D.children v, ∑ z ∈ D.subtree u, f z := by
  classical
  rw [D.subtree_eq_insert_child_union v,
    Finset.sum_insert (D.self_not_mem_child_union v),
    Finset.sum_biUnion (D.subtree_pairwiseDisjoint v)]

/-- Bottom-up induction, derived from finiteness and maximum level. -/
theorem bottomUp (P : V → Prop)
    (hstep : ∀ v, (∀ u ∈ D.children v, P u) → P v) : ∀ v, P v := by
  classical
  intro v
  by_contra hv
  let bad : Finset V := Finset.univ.filter (fun z => ¬P z)
  have hbad : bad.Nonempty := ⟨v, by simp [bad, hv]⟩
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image bad D.level hbad
  have hmnot : ¬P m := (Finset.mem_filter.mp hm).2
  apply hmnot
  apply hstep m
  intro u hu
  by_contra huP
  have huBad : u ∈ bad := by simp [bad, huP]
  have hle := hmax u huBad
  have huStep : D.Step u m := (D.mem_children m u).1 hu
  rcases huStep with ⟨hune, hup⟩
  have hlevel := D.level_parent_add_one u hune
  rw [hup] at hlevel
  omega

/-- Top-down induction, derived from finiteness and minimum level. -/
theorem topDown (P : V → Prop) (hroot : P D.root)
    (hstep : ∀ v, v ≠ D.root → P (D.parent v) → P v) : ∀ v, P v := by
  classical
  intro v
  by_contra hv
  let bad : Finset V := Finset.univ.filter (fun z => ¬P z)
  have hbad : bad.Nonempty := ⟨v, by simp [bad, hv]⟩
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image bad D.level hbad
  have hmnot : ¬P m := (Finset.mem_filter.mp hm).2
  have hmne : m ≠ D.root := by
    intro h
    exact hmnot (h ▸ hroot)
  have hp : P (D.parent m) := by
    by_contra hp
    have hpBad : D.parent m ∈ bad := by simp [bad, hp]
    have hle := hmin (D.parent m) hpBad
    have hlevel := D.level_parent_add_one m hmne
    omega
  exact hmnot (hstep m hmne hp)

/-- The exact `Model` generated by a finite parent map. -/
noncomputable def toModel : Model V where
  root := D.root
  parent := D.parent
  weightToParent := D.weightToParent
  children := D.children
  child_ne_root := by
    intro v u hu
    exact ((D.mem_children v u).1 hu).1
  child_parent := by
    intro v u hu
    exact ((D.mem_children v u).1 hu).2
  depth := D.depth
  depth_root := D.depth_root
  depth_parent_add_weight := D.depth_parent_add_weight
  subtree := D.subtree
  root_subtree := by
    ext z
    simp [D.descendant_root z]
  subtree_sum_decomp := D.subtree_sum_decomp
  bottomUp := D.bottomUp
  topDown := D.topDown

end ParentData

/-! ## Actual `PosIntTree` adapter

For each non-root vertex the unique incoming physical edge is obtained from
the injective child-endpoint map and the exact `n-1` physical-edge count.
Thus every field of `rootedParentData` is computed from the supplied graph,
its canonical paths, and its physical weights.
-/

namespace PosIntTreeAdapter

open LeechTrees.Foundation
open LeechTrees.QHop

variable {n : ℕ}

noncomputable def childEquiv (T : PosIntTree n) (r : Fin n) :
    T.Edge ≃ {v : Fin n // v ≠ r} := by
  classical
  let f : T.Edge → {v : Fin n // v ≠ r} := fun e =>
    ⟨RootedCut.child T r e, by
      intro h
      have hc := RootedCut.child_away T r e
      rw [h] at hc
      exact RootedCut.root_not_away T r e hc⟩
  apply Equiv.ofBijective f
  apply (Fintype.bijective_iff_injective_and_card f).2
  constructor
  · intro e g heg
    apply RootedCut.child_injective T r
    exact congrArg Subtype.val heg
  · have hedge : Fintype.card T.Edge + 1 = n := by
      simpa only [SimpleGraph.edgeFinset_card, Fintype.card_fin] using
        T.isTree.card_edgeFinset
    have hne : Fintype.card {v : Fin n // v ≠ r} = n - 1 := by
      calc
        Fintype.card {v : Fin n // v ≠ r} = Fintype.card (Fin n) - 1 :=
          Set.card_ne_eq r
        _ = n - 1 := by rw [Fintype.card_fin]
    omega

noncomputable def incomingEdge (T : PosIntTree n) (r : Fin n)
    (v : {x : Fin n // x ≠ r}) : T.Edge :=
  (childEquiv T r).symm v

@[simp] theorem child_incomingEdge (T : PosIntTree n) (r : Fin n)
    (v : {x : Fin n // x ≠ r}) :
    RootedCut.child T r (incomingEdge T r v) = v.1 := by
  exact congrArg Subtype.val ((childEquiv T r).apply_symm_apply v)

noncomputable def rootedParent (T : PosIntTree n) (r v : Fin n) : Fin n :=
  if hv : v = r then r
  else RootedCut.parent T r (incomingEdge T r ⟨v, hv⟩)

noncomputable def rootedWeightToParent
    (T : PosIntTree n) (r v : Fin n) : ℕ :=
  if hv : v = r then 0 else T.weight (incomingEdge T r ⟨v, hv⟩)

/-- Actual graph-derived parent data.  The level recurrence is the canonical
path-length recurrence, and the depth recurrence is its weighted analogue. -/
noncomputable def rootedParentData (T : PosIntTree n) (r : Fin n) :
    ParentData (Fin n) where
  root := r
  parent := rootedParent T r
  level := fun v => (T.path r v).1.length
  level_root := by
    simpa using congrArg (fun p : T.graph.Path r r => p.1.length)
      (SimpleGraph.Path.loop_eq (T.path r r))
  level_parent_add_one := by
    intro v hv
    let e := incomingEdge T r ⟨v, hv⟩
    have hc : RootedCut.child T r e = v := by
      dsimp only [e]
      exact child_incomingEdge T r ⟨v, hv⟩
    have hpath := RootedCut.root_child_path_eq_concat T r e
    have hlength := congrArg (fun p => p.1.length) hpath
    have hp : rootedParent T r v = RootedCut.parent T r e := by
      unfold rootedParent
      split
      · contradiction
      · rfl
    rw [hp]
    rw [← hc]
    simp at hlength
    exact hlength
  weightToParent := rootedWeightToParent T r
  depth := T.dist r
  depth_root := T.dist_self r
  depth_parent_add_weight := by
    intro v hv
    let e := incomingEdge T r ⟨v, hv⟩
    have hc : RootedCut.child T r e = v := by
      dsimp only [e]
      exact child_incomingEdge T r ⟨v, hv⟩
    calc
      T.dist r v = T.dist r (RootedCut.child T r e) := by rw [hc]
      _ = T.walkWeight (T.path r (RootedCut.child T r e)).1 :=
        T.dist_eq_walkWeight_path _ _
      _ = T.walkWeight
          ((T.path r (RootedCut.parent T r e)).1.concat
            (RootedCut.parent_adj_child T r e)) := by
        rw [RootedCut.root_child_path_eq_concat T r e]
      _ = T.walkWeight (T.path r (RootedCut.parent T r e)).1 + T.weight e := by
        simp [PosIntTree.walkWeight, RootedCut.parent_child_edge T r e,
          T.weightOfPair_edge]
      _ = T.dist r (RootedCut.parent T r e) + T.weight e := by
        rw [T.path_walkWeight_eq_dist (T.path r (RootedCut.parent T r e))]
      _ = T.dist r (rootedParent T r v) + rootedWeightToParent T r v := by
        simp [rootedParent, rootedWeightToParent, hv, e]

/-- The signed-cut-flow model computed from an actual weighted tree. -/
noncomputable def rootedModel (T : PosIntTree n) (r : Fin n) : Model (Fin n) :=
  (rootedParentData T r).toModel

/-- G009, actual graph endpoint: joint feasibility for all oriented
descendant cuts of a supplied positive-integer tree is equivalent to the
local residual-sign and edge-parity conditions. -/
theorem joint_signed_cut_flow_iff (T : PosIntTree n) (r : Fin n)
    (delta : ℤ) (x : Fin n → ℤ) :
    (∃ sigma : Fin n → ℤ, (rootedModel T r).Realizes delta x sigma) ↔
      (∀ v, (rootedModel T r).residual delta x v = 1 ∨
        (rootedModel T r).residual delta x v = -1) ∧
      ∀ v, v ≠ (rootedModel T r).root →
        (rootedModel T r).residual delta x
            ((rootedModel T r).parent v) *
          (rootedModel T r).residual delta x v =
            paritySign ((rootedModel T r).weightToParent v) :=
  (rootedModel T r).joint_signed_cut_flow_iff delta x

/-- Audited order-18 Leech specialization with total signed mass `-4`. -/
theorem leech_order18_joint_signed_cut_flow_iff
    (T : PosIntTree 18) (_hL : IsLeech T) (r : Fin 18)
    (x : Fin 18 → ℤ) :
    (∃ sigma : Fin 18 → ℤ, (rootedModel T r).Realizes (-4) x sigma) ↔
      (∀ v, (rootedModel T r).residual (-4) x v = 1 ∨
        (rootedModel T r).residual (-4) x v = -1) ∧
      ∀ v, v ≠ (rootedModel T r).root →
        (rootedModel T r).residual (-4) x
            ((rootedModel T r).parent v) *
          (rootedModel T r).residual (-4) x v =
            paritySign ((rootedModel T r).weightToParent v) :=
  (rootedModel T r).joint_signed_cut_flow_iff_neg_four x

end PosIntTreeAdapter

/-! ## G024(b): the rooted-star marginal false positive -/

def badStarWeights : Finset ℕ := {5, 14, 15, 16, 17}

def badStarImbalance (w : ℕ) : ℤ :=
  if w ∈ badStarWeights then -1 else 1

theorem badStarImbalance_pm (w : ℕ) :
    badStarImbalance w = 1 ∨ badStarImbalance w = -1 := by
  classical
  by_cases h : w ∈ badStarWeights <;> simp [badStarImbalance, h]

/-- Every spoke marginal is admissible and the signed first moment is exact,
but the common root residual is `-3`, not a sign. -/
theorem rooted_eighteen_star_marginal_false_positive :
    (∀ w ∈ (Finset.Icc 1 17 : Finset ℕ),
      badStarImbalance w = 1 ∨ badStarImbalance w = -1) ∧
    (∑ w ∈ (Finset.Icc 1 17 : Finset ℕ),
      (w : ℤ) * badStarImbalance w * (badStarImbalance w - 4)) = 77 ∧
    (∑ w ∈ (Finset.Icc 1 17 : Finset ℕ), badStarImbalance w) = 7 ∧
    4 - (∑ w ∈ (Finset.Icc 1 17 : Finset ℕ), badStarImbalance w) = -3 ∧
    ¬(4 - (∑ w ∈ (Finset.Icc 1 17 : Finset ℕ), badStarImbalance w) = 1 ∨
      4 - (∑ w ∈ (Finset.Icc 1 17 : Finset ℕ), badStarImbalance w) = -1) := by
  decide

end

end LeechTrees.SignedCutFlow
