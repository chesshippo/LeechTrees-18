import LeechTrees.ParityTailGraphAdapter

/-!
# T8 arbitrary-collinear outer-component construction

This isolated module attempts the one graph-geometric obligation left by
`GraphAdapterV1`: construct its `OuterCertificate` from an actual nonempty
edge set contained in one canonical tree path.
-/

namespace LeechTrees.ParityTail.T8Collinear

open LeechTrees.Foundation
open LeechTrees.ParityTail.GraphAdapterV1
open SimpleGraph

noncomputable section

namespace OrientedCut

variable {n : ℕ} (T : PosIntTree n) (r : Fin n)

noncomputable local instance propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The component of `T - e` opposite the chosen root. -/
def Away (e : T.Edge) (x : Fin n) : Prop :=
  if T.LeftCut e r then T.RightCut e x else T.LeftCut e x

/-- The endpoint of `e` in its away-from-root component. -/
def child (e : T.Edge) : Fin n :=
  if T.LeftCut e r then T.edgeRight e else T.edgeLeft e

/-- The endpoint of `e` in its root component. -/
def parent (e : T.Edge) : Fin n :=
  if T.LeftCut e r then T.edgeLeft e else T.edgeRight e

theorem root_not_away (e : T.Edge) : ¬Away T r e r := by
  unfold Away
  by_cases h : T.LeftCut e r
  · simp [h, (T.leftCut_iff_not_rightCut e r).mp h]
  · simp [h]

theorem child_away (e : T.Edge) : Away T r e (child T r e) := by
  unfold Away child
  by_cases h : T.LeftCut e r
  · simp [h, T.edgeRight_mem_RightCut e]
  · simp [h, T.edgeLeft_mem_LeftCut e]

theorem parent_not_away (e : T.Edge) : ¬Away T r e (parent T r e) := by
  unfold Away parent
  by_cases h : T.LeftCut e r
  · simp [h, (T.leftCut_iff_not_rightCut e (T.edgeLeft e)).mp
      (T.edgeLeft_mem_LeftCut e)]
  · have hp : ¬T.LeftCut e (T.edgeRight e) :=
      (T.rightCut_iff_not_leftCut e (T.edgeRight e)).mp
        (T.edgeRight_mem_RightCut e)
    simp [h, hp]

theorem parent_child_edge (e : T.Edge) :
    s(parent T r e, child T r e) = e.1 := by
  unfold parent child
  by_cases h : T.LeftCut e r
  · simp [h, T.edge_eq_mk_endpoints e]
  · simp [h, Sym2.eq_swap, T.edge_eq_mk_endpoints e]

theorem parent_adj_child (e : T.Edge) :
    T.graph.Adj (parent T r e) (child T r e) := by
  rw [← SimpleGraph.mem_edgeSet, parent_child_edge]
  exact e.2

theorem away_iff_mem_pathEdges (e : T.Edge) (x : Fin n) :
    Away T r e x ↔ e.1 ∈ T.pathEdges r x := by
  unfold Away
  rw [T.mem_pathEdges_iff_opposite_cuts]
  by_cases h : T.LeftCut e r
  · have hnr : ¬T.RightCut e r :=
      (T.leftCut_iff_not_rightCut e r).mp h
    simp [h, hnr]
  · have hr : T.RightCut e r :=
      (T.rightCut_iff_not_leftCut e r).2 h
    simp [h, hr]

theorem mem_pathEdges_iff_opposite_away (e : T.Edge) (u v : Fin n) :
    e.1 ∈ T.pathEdges u v ↔
      (Away T r e u ∧ ¬Away T r e v) ∨
        (¬Away T r e u ∧ Away T r e v) := by
  rw [T.mem_pathEdges_iff_opposite_cuts]
  unfold Away
  by_cases h : T.LeftCut e r
  · simp only [if_pos h]
    rw [T.leftCut_iff_not_rightCut e u,
      T.leftCut_iff_not_rightCut e v]
    tauto
  · simp only [if_neg h]
    rw [T.rightCut_iff_not_leftCut e u,
      T.rightCut_iff_not_leftCut e v]

theorem child_mem_root_path_support_of_away (e : T.Edge) {x : Fin n}
    (hx : Away T r e x) : child T r e ∈ (T.path r x).1.support := by
  have hefin := (away_iff_mem_pathEdges T r e x).mp hx
  have he : e.1 ∈ (T.path r x).1.edges := by
    simpa [PosIntTree.pathEdges] using hefin
  rw [← parent_child_edge T r e] at he
  exact (T.path r x).1.snd_mem_support_of_mem_edges he

theorem pathEdges_subset_of_mem_support {x z : Fin n}
    (hz : z ∈ (T.path r x).1.support) :
    T.pathEdges r z ⊆ T.pathEdges r x := by
  let q := (T.path r x).1.takeUntil z hz
  have hqpath : q.IsPath := (T.path r x).2.takeUntil hz
  have hqeq : (⟨q, hqpath⟩ : T.graph.Path r z) = T.path r z :=
    T.path_unique _
  intro e he
  have heq : e ∈ q.edges := by
    have : e ∈ (T.path r z).1.edges := by
      simpa [PosIntTree.pathEdges] using he
    rwa [← congrArg (fun p : T.graph.Path r z ↦ p.1.edges) hqeq] at this
  have := (T.path r x).1.edges_takeUntil_subset hz heq
  simpa [PosIntTree.pathEdges] using this

theorem away_mono_of_child_away (e f : T.Edge)
    (hchild : Away T r e (child T r f)) :
    ∀ x : Fin n, Away T r f x → Away T r e x := by
  intro x hx
  have hc : child T r f ∈ (T.path r x).1.support :=
    child_mem_root_path_support_of_away T r f hx
  have hsub := pathEdges_subset_of_mem_support T r hc
  apply (away_iff_mem_pathEdges T r e x).mpr
  exact hsub ((away_iff_mem_pathEdges T r e (child T r f)).mp hchild)

theorem child_not_mem_parent_path (e : T.Edge) :
    child T r e ∉ (T.path r (parent T r e)).1.support := by
  intro hc
  have hsub := pathEdges_subset_of_mem_support T r hc
  have hechild : e.1 ∈ T.pathEdges r (child T r e) :=
    (away_iff_mem_pathEdges T r e (child T r e)).mp (child_away T r e)
  have heparent := hsub hechild
  exact parent_not_away T r e
    ((away_iff_mem_pathEdges T r e (parent T r e)).mpr heparent)

theorem root_child_path_eq_concat (e : T.Edge) :
    T.path r (child T r e) =
      ⟨(T.path r (parent T r e)).1.concat (parent_adj_child T r e),
        (T.path r (parent T r e)).2.concat
          (child_not_mem_parent_path T r e) (parent_adj_child T r e)⟩ := by
  exact (T.path_unique _).symm

theorem child_injective : Function.Injective (child T r) := by
  intro e f hchild
  have heq := congrArg (fun p ↦ p.1.edges) (root_child_path_eq_concat T r e)
  have hfq := congrArg (fun p ↦ p.1.edges) (root_child_path_eq_concat T r f)
  have hcanon : (T.path r (child T r e)).1.edges =
      (T.path r (child T r f)).1.edges := by rw [hchild]
  have hedges :
      (T.path r (parent T r e)).1.edges ++ [e.1] =
        (T.path r (parent T r f)).1.edges ++ [f.1] := by
    calc
      (T.path r (parent T r e)).1.edges ++ [e.1] =
          (T.path r (child T r e)).1.edges := by
        simpa [SimpleGraph.Walk.edges_concat, parent_child_edge T r e]
          using heq.symm
      _ = (T.path r (child T r f)).1.edges := hcanon
      _ = (T.path r (parent T r f)).1.edges ++ [f.1] := by
        simpa [SimpleGraph.Walk.edges_concat, parent_child_edge T r f]
          using hfq
  have hlast := congrArg List.getLast? hedges
  have hef : e.1 = f.1 := by simpa using hlast
  exact Subtype.ext hef

theorem child_away_of_takeUntil_length_le (e f : T.Edge) {x : Fin n}
    (he : Away T r e x) (hf : Away T r f x)
    (hlen :
      ((T.path r x).1.takeUntil (child T r e)
          (child_mem_root_path_support_of_away T r e he)).length ≤
      ((T.path r x).1.takeUntil (child T r f)
          (child_mem_root_path_support_of_away T r f hf)).length) :
    Away T r e (child T r f) := by
  let P := (T.path r x).1
  let hce : child T r e ∈ P.support :=
    child_mem_root_path_support_of_away T r e he
  let hcf : child T r f ∈ P.support :=
    child_mem_root_path_support_of_away T r f hf
  let qe := P.takeUntil (child T r e) hce
  let qf := P.takeUntil (child T r f) hcf
  have hceAt : P.getVert qe.length = child T r e :=
    P.getVert_length_takeUntil hce
  have hqfAt : qf.getVert qe.length = P.getVert qe.length :=
    P.getVert_takeUntil hcf hlen
  have hceqf : child T r e ∈ qf.support := by
    rw [← hceAt, ← hqfAt]
    exact qf.getVert_mem_support qe.length
  have hqfpath : qf.IsPath := (T.path r x).2.takeUntil hcf
  have hqfeq : (⟨qf, hqfpath⟩ : T.graph.Path r (child T r f)) =
      T.path r (child T r f) := T.path_unique _
  have hcecanon : child T r e ∈ (T.path r (child T r f)).1.support := by
    rw [← congrArg (fun p ↦ p.1.support) hqfeq]
    exact hceqf
  have hsub := pathEdges_subset_of_mem_support T r hcecanon
  apply (away_iff_mem_pathEdges T r e (child T r f)).mpr
  exact hsub
    ((away_iff_mem_pathEdges T r e (child T r e)).mp (child_away T r e))

theorem child_away_comparable_of_common (e f : T.Edge) {x : Fin n}
    (he : Away T r e x) (hf : Away T r f x) :
    Away T r e (child T r f) ∨ Away T r f (child T r e) := by
  let le := ((T.path r x).1.takeUntil (child T r e)
    (child_mem_root_path_support_of_away T r e he)).length
  let lf := ((T.path r x).1.takeUntil (child T r f)
    (child_mem_root_path_support_of_away T r f hf)).length
  rcases Nat.le_total le lf with h | h
  · exact Or.inl (child_away_of_takeUntil_length_le T r e f he hf h)
  · exact Or.inr (child_away_of_takeUntil_length_le T r f e hf he h)

theorem away_comparable_of_common (e f : T.Edge) {x : Fin n}
    (he : Away T r e x) (hf : Away T r f x) :
    (∀ y, Away T r e y → Away T r f y) ∨
      (∀ y, Away T r f y → Away T r e y) := by
  rcases child_away_comparable_of_common T r e f he hf with hef | hfe
  · exact Or.inr (away_mono_of_child_away T r e f hef)
  · exact Or.inl (away_mono_of_child_away T r f e hfe)

/-- Distance from the root to the away endpoint, used only to select the two
extreme edges of a finite collinear family. -/
def depth (e : T.Edge) : ℕ :=
  (T.path r (child T r e)).1.length

theorem depth_lt_of_child_away_of_ne (e f : T.Edge)
    (haway : Away T r e (child T r f)) (hne : e ≠ f) :
    depth T r e < depth T r f := by
  let P := (T.path r (child T r f)).1
  have hc : child T r e ∈ P.support :=
    child_mem_root_path_support_of_away T r e haway
  let q := P.takeUntil (child T r e) hc
  have hqpath : q.IsPath := (T.path r (child T r f)).2.takeUntil hc
  have hqeq : (⟨q, hqpath⟩ : T.graph.Path r (child T r e)) =
      T.path r (child T r e) := T.path_unique _
  have hchildren : child T r e ≠ child T r f := by
    intro h
    exact hne (child_injective T r h)
  have hlt : q.length < P.length := P.length_takeUntil_lt hc hchildren
  have hlen : q.length = depth T r e := by
    exact congrArg (fun p ↦ p.1.length) hqeq
  simpa [depth, P, hlen] using hlt

/-- Along a common root path, numeric depth order is reverse inclusion of
away components. -/
theorem away_mono_of_depth_le_of_common (e f : T.Edge) {x : Fin n}
    (he : Away T r e x) (hf : Away T r f x)
    (hdepth : depth T r e ≤ depth T r f) :
    ∀ y, Away T r f y → Away T r e y := by
  rcases away_comparable_of_common T r e f he hf with hef | hfe
  · by_cases hsame : e = f
    · subst f
      exact fun y hy => hy
    · have hchild : Away T r f (child T r e) :=
        hef _ (child_away T r e)
      have hlt := depth_lt_of_child_away_of_ne T r f e hchild (Ne.symm hsame)
      exact (Nat.not_lt_of_ge hdepth hlt).elim
  · exact hfe

end OrientedCut

/-! ## The base-edge crossing equivalence, oriented by the witness root -/

abbrev RootVertex {n : ℕ} (T : PosIntTree n) (r : Fin n) (e : T.Edge) :=
  {x : Fin n // ¬OrientedCut.Away T r e x}

abbrev AwayVertex {n : ℕ} (T : PosIntTree n) (r : Fin n) (e : T.Edge) :=
  {x : Fin n // OrientedCut.Away T r e x}

/-- The foundation crossing-pair equivalence, with its two factors oriented
as the root component and the away component. -/
def orientedCrossingPairEquiv {n : ℕ} (T : PosIntTree n) (r : Fin n)
    (e : T.Edge) :
    RootVertex T r e × AwayVertex T r e ≃ T.CrossingPair e := by
  classical
  let ec : OppositePair (OrientedCut.Away T r e) ≃ T.CrossingPair e :=
    Equiv.subtypeEquivProp <| funext fun q => propext <| by
      exact (OrientedCut.mem_pathEdges_iff_opposite_away
        T r e q.left q.right).symm
  exact (Equiv.prodComm _ _).trans
    ((oppositePairEquiv (OrientedCut.Away T r e)).trans ec)

theorem pathEdges_ofDistinct {n : ℕ} (T : PosIntTree n)
    (u v : Fin n) (huv : u ≠ v) :
    T.pathEdges (VertexPair.ofDistinct u v huv).left
        (VertexPair.ofDistinct u v huv).right = T.pathEdges u v := by
  by_cases h : u < v
  · simp [VertexPair.ofDistinct, h, VertexPair.left, VertexPair.right]
  · simp [VertexPair.ofDistinct, h, VertexPair.left, VertexPair.right,
      T.pathEdges_comm]

theorem sign_product_ofDistinct {n : ℕ} (sign : Fin n → ℤ)
    (u v : Fin n) (huv : u ≠ v) :
    sign (VertexPair.ofDistinct u v huv).left *
        sign (VertexPair.ofDistinct u v huv).right = sign u * sign v := by
  by_cases h : u < v
  · simp [VertexPair.ofDistinct, h, VertexPair.left, VertexPair.right]
  · simp [VertexPair.ofDistinct, h, VertexPair.left, VertexPair.right,
      mul_comm]

theorem orientedCrossingPairEquiv_apply_val {n : ℕ}
    (T : PosIntTree n) (r : Fin n) (e : T.Edge)
    (z : RootVertex T r e × AwayVertex T r e) :
    (orientedCrossingPairEquiv T r e z).1 =
      VertexPair.ofDistinct z.2.1 z.1.1
        (fun h => z.1.2 (h ▸ z.2.2)) := by
  rfl

theorem oriented_pair_mem_pathSupport_iff {n : ℕ}
    (T : PosIntTree n) (r : Fin n) (F : Finset T.Edge)
    (near far : T.Edge) (_hnear : near ∈ F) (hfar : far ∈ F)
    (toNear : ∀ f ∈ F, ∀ x,
      OrientedCut.Away T r f x → OrientedCut.Away T r near x)
    (fromFar : ∀ f ∈ F, ∀ x,
      OrientedCut.Away T r far x → OrientedCut.Away T r f x)
    (z : RootVertex T r near × AwayVertex T r near) :
    (orientedCrossingPairEquiv T r near z).1 ∈ pathSupport T F ↔
      OrientedCut.Away T r far z.2.1 := by
  constructor
  · intro hs
    have hcross : far.1 ∈ T.pathEdges
        (orientedCrossingPairEquiv T r near z).1.left
        (orientedCrossingPairEquiv T r near z).1.right :=
      (Finset.mem_filter.mp hs).2 far hfar
    rw [orientedCrossingPairEquiv_apply_val,
      pathEdges_ofDistinct] at hcross
    have hop := (OrientedCut.mem_pathEdges_iff_opposite_away
      T r far z.2.1 z.1.1).1 hcross
    have hrootNot : ¬OrientedCut.Away T r far z.1.1 := by
      intro hf
      exact z.1.2 (toNear far hfar z.1.1 hf)
    rcases hop with h | h
    · exact h.1
    · exact (hrootNot h.2).elim
  · intro hfarAway
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro f hf
    have haway : OrientedCut.Away T r f z.2.1 :=
      fromFar f hf z.2.1 hfarAway
    have hroot : ¬OrientedCut.Away T r f z.1.1 := by
      intro h
      exact z.1.2 (toNear f hf z.1.1 h)
    rw [orientedCrossingPairEquiv_apply_val, pathEdges_ofDistinct]
    exact (OrientedCut.mem_pathEdges_iff_opposite_away
      T r f z.2.1 z.1.1).2 (Or.inl ⟨haway, hroot⟩)

def rootOuterSet {n : ℕ} (T : PosIntTree n) (r : Fin n)
    (near : T.Edge) : Finset (Fin n) :=
  by
    classical
    exact Finset.univ.filter fun x => ¬OrientedCut.Away T r near x

def awayOuterSet {n : ℕ} (T : PosIntTree n) (r : Fin n)
    (far : T.Edge) : Finset (Fin n) :=
  by
    classical
    exact Finset.univ.filter fun x => OrientedCut.Away T r far x

def rootOuterSetEquiv {n : ℕ} (T : PosIntTree n) (r : Fin n)
    (near : T.Edge) :
    {x : Fin n // x ∈ rootOuterSet T r near} ≃ RootVertex T r near :=
  Equiv.subtypeEquivProp <| funext fun x => propext <| by
    simp [rootOuterSet]

def awayOuterSetEquiv {n : ℕ} (T : PosIntTree n) (r : Fin n)
    (far : T.Edge) :
    {x : Fin n // x ∈ awayOuterSet T r far} ≃ AwayVertex T r far :=
  Equiv.subtypeEquivProp <| funext fun x => propext <| by
    simp [awayOuterSet]

def supportCrossingEquiv {n : ℕ} (T : PosIntTree n)
    (F : Finset T.Edge) (near : T.Edge) (hnear : near ∈ F) :
    {q : VertexPair n // q ∈ pathSupport T F} ≃
      {c : T.CrossingPair near // c.1 ∈ pathSupport T F} where
  toFun q :=
    ⟨⟨q.1, (Finset.mem_filter.mp q.2).2 near hnear⟩, q.2⟩
  invFun c := ⟨c.1.1, c.2⟩
  left_inv _q := rfl
  right_inv _c := rfl

def restrictedExtremeProductEquiv {n : ℕ} (T : PosIntTree n)
    (r : Fin n) (near far : T.Edge)
    (far_sub_near : ∀ x, OrientedCut.Away T r far x →
      OrientedCut.Away T r near x) :
    {z : RootVertex T r near × AwayVertex T r near //
      OrientedCut.Away T r far z.2.1} ≃
      RootVertex T r near × AwayVertex T r far where
  toFun z := ⟨z.1.1, ⟨z.1.2.1, z.2⟩⟩
  invFun z :=
    ⟨⟨z.1, ⟨z.2.1, far_sub_near z.2.1 z.2.2⟩⟩, z.2.2⟩
  left_inv _z := rfl
  right_inv _z := rfl

/-- The actual support is the product of the root-side component of the
nearest selected edge and the away-side component of the farthest selected
edge. -/
def supportExtremeProductEquiv {n : ℕ} (T : PosIntTree n) (r : Fin n)
    (F : Finset T.Edge) (near far : T.Edge)
    (hnear : near ∈ F) (hfar : far ∈ F)
    (toNear : ∀ f ∈ F, ∀ x,
      OrientedCut.Away T r f x → OrientedCut.Away T r near x)
    (fromFar : ∀ f ∈ F, ∀ x,
      OrientedCut.Away T r far x → OrientedCut.Away T r f x) :
    {q : VertexPair n // q ∈ pathSupport T F} ≃
      RootVertex T r near × AwayVertex T r far := by
  let E := orientedCrossingPairEquiv T r near
  let restricted :
      {z : RootVertex T r near × AwayVertex T r near //
        OrientedCut.Away T r far z.2.1} ≃
        {c : T.CrossingPair near // c.1 ∈ pathSupport T F} :=
    E.subtypeEquiv fun z =>
      (oriented_pair_mem_pathSupport_iff T r F near far hnear hfar
        toNear fromFar z).symm
  exact (supportCrossingEquiv T F near hnear).trans <|
    restricted.symm |>.trans <|
      restrictedExtremeProductEquiv T r near far
        (fromFar near hnear)

/-- A finite nonempty family on one canonical path has nearest and farthest
selected edges, whose root-oriented components bound every selected cut. -/
theorem exists_extreme_edges {n : ℕ} (T : PosIntTree n)
    (F : Finset T.Edge) (hF : F.Nonempty)
    (q₀ : VertexPair n) (hq₀ : q₀ ∈ pathSupport T F) :
    ∃ near far : T.Edge,
      near ∈ F ∧ far ∈ F ∧
      (∀ f ∈ F, ∀ x,
        OrientedCut.Away T q₀.left f x →
          OrientedCut.Away T q₀.left near x) ∧
      (∀ f ∈ F, ∀ x,
        OrientedCut.Away T q₀.left far x →
          OrientedCut.Away T q₀.left f x) := by
  obtain ⟨near, hnear, hmin⟩ :=
    Finset.exists_min_image F (OrientedCut.depth T q₀.left) hF
  obtain ⟨far, hfar, hmax⟩ :=
    Finset.exists_max_image F (OrientedCut.depth T q₀.left) hF
  have hpath : ∀ f ∈ F,
      f.1 ∈ T.pathEdges q₀.left q₀.right :=
    (Finset.mem_filter.mp hq₀).2
  have hcommon : ∀ f ∈ F,
      OrientedCut.Away T q₀.left f q₀.right := by
    intro f hf
    exact (OrientedCut.away_iff_mem_pathEdges T q₀.left f q₀.right).2
      (hpath f hf)
  refine ⟨near, far, hnear, hfar, ?_, ?_⟩
  · intro f hf x hx
    exact OrientedCut.away_mono_of_depth_le_of_common
      T q₀.left near f (hcommon near hnear) (hcommon f hf)
        (hmin f hf) x hx
  · intro f hf x hx
    exact OrientedCut.away_mono_of_depth_le_of_common
      T q₀.left f far (hcommon f hf) (hcommon far hfar)
        (hmax f hf) x hx

def liftExtremeProduct {n : ℕ} (T : PosIntTree n) (r : Fin n)
    (near far : T.Edge)
    (far_sub_near : ∀ x, OrientedCut.Away T r far x →
      OrientedCut.Away T r near x)
    (z : RootVertex T r near × AwayVertex T r far) :
    RootVertex T r near × AwayVertex T r near :=
  ⟨z.1, ⟨z.2.1, far_sub_near z.2.1 z.2.2⟩⟩

theorem supportExtremeProductEquiv_recovers_pair {n : ℕ}
    (T : PosIntTree n) (r : Fin n) (F : Finset T.Edge)
    (near far : T.Edge) (hnear : near ∈ F) (hfar : far ∈ F)
    (toNear : ∀ f ∈ F, ∀ x,
      OrientedCut.Away T r f x → OrientedCut.Away T r near x)
    (fromFar : ∀ f ∈ F, ∀ x,
      OrientedCut.Away T r far x → OrientedCut.Away T r f x)
    (q : {q : VertexPair n // q ∈ pathSupport T F}) :
    (orientedCrossingPairEquiv T r near
      (liftExtremeProduct T r near far (fromFar near hnear)
        (supportExtremeProductEquiv T r F near far hnear hfar
          toNear fromFar q))).1 = q.1 := by
  simp [supportExtremeProductEquiv, supportCrossingEquiv,
    restrictedExtremeProductEquiv, liftExtremeProduct]

def supportOuterFinsetEquiv {n : ℕ}
    (T : PosIntTree n) (r : Fin n) (F : Finset T.Edge)
    (near far : T.Edge) (hnear : near ∈ F) (hfar : far ∈ F)
    (toNear : ∀ f ∈ F, ∀ x,
      OrientedCut.Away T r f x → OrientedCut.Away T r near x)
    (fromFar : ∀ f ∈ F, ∀ x,
      OrientedCut.Away T r far x → OrientedCut.Away T r f x) :
    {q : VertexPair n // q ∈ pathSupport T F} ≃
      ({u : Fin n // u ∈ rootOuterSet T r near} ×
        {v : Fin n // v ∈ awayOuterSet T r far}) :=
  (supportExtremeProductEquiv T r F near far hnear hfar
    toNear fromFar).trans <|
      Equiv.prodCongr (rootOuterSetEquiv T r near).symm
        (awayOuterSetEquiv T r far).symm

theorem supportOuterFinsetEquiv_sign_product {n : ℕ}
    (T : PosIntTree n) (r : Fin n) (F : Finset T.Edge)
    (near far : T.Edge) (hnear : near ∈ F) (hfar : far ∈ F)
    (toNear : ∀ f ∈ F, ∀ x,
      OrientedCut.Away T r f x → OrientedCut.Away T r near x)
    (fromFar : ∀ f ∈ F, ∀ x,
      OrientedCut.Away T r far x → OrientedCut.Away T r f x)
    (sign : Fin n → ℤ)
    (q : {q : VertexPair n // q ∈ pathSupport T F}) :
    sign q.1.left * sign q.1.right =
      sign (supportOuterFinsetEquiv T r F near far hnear hfar
        toNear fromFar q).1.1 *
      sign (supportOuterFinsetEquiv T r F near far hnear hfar
        toNear fromFar q).2.1 := by
  let z := supportExtremeProductEquiv T r F near far hnear hfar
    toNear fromFar q
  have hrecover := supportExtremeProductEquiv_recovers_pair
    T r F near far hnear hfar toNear fromFar q
  calc
    sign q.1.left * sign q.1.right =
        sign (orientedCrossingPairEquiv T r near
          (liftExtremeProduct T r near far (fromFar near hnear) z)).1.left *
        sign (orientedCrossingPairEquiv T r near
          (liftExtremeProduct T r near far (fromFar near hnear) z)).1.right := by
      rw [hrecover]
    _ = sign z.2.1 * sign z.1.1 := by
      rw [orientedCrossingPairEquiv_apply_val, sign_product_ofDistinct]
      change sign z.2.1 * sign z.1.1 = sign z.2.1 * sign z.1.1
      rfl
    _ = sign (supportOuterFinsetEquiv T r F near far hnear hfar
          toNear fromFar q).1.1 *
        sign (supportOuterFinsetEquiv T r F near far hnear hfar
          toNear fromFar q).2.1 := by
      change sign z.2.1 * sign z.1.1 = sign z.1.1 * sign z.2.1
      exact mul_comm _ _

/-- The missing arbitrary-collinear certificate, constructed from the
nearest and farthest selected edges on an actual witness path. -/
theorem outerCertificate_of_nonempty_collinear {n : ℕ}
    (T : PosIntTree n) (sign : Fin n → ℤ) (F : Finset T.Edge)
    (hF : F.Nonempty) (hcol : (pathSupport T F).Nonempty) :
    Nonempty (OuterCertificate T sign F) := by
  obtain ⟨q₀, hq₀⟩ := hcol
  obtain ⟨near, far, hnear, hfar, toNear, fromFar⟩ :=
    exists_extreme_edges T F hF q₀ hq₀
  exact ⟨{
    left := rootOuterSet T q₀.left near
    right := awayOuterSet T q₀.left far
    equiv := supportOuterFinsetEquiv T q₀.left F near far
      hnear hfar toNear fromFar
    sign_product := supportOuterFinsetEquiv_sign_product
      T q₀.left F near far hnear hfar toNear fromFar sign }⟩

/-- Full discharge of the exact named blocker exported by
`GraphAdapterV1`. -/
theorem T8CollinearOuterCertificateRequired_proved {n : ℕ}
    (T : PosIntTree n) : T8CollinearOuterCertificateRequired T := by
  intro sign F hF hcol
  exact outerCertificate_of_nonempty_collinear T sign F hF hcol

/-- Certificate-free actual-tree T8 collinear factorization. -/
theorem T8_actual_collinear_outer_factorization_closed {n : ℕ}
    (T : PosIntTree n) (sign : Fin n → ℤ) (F : Finset T.Edge)
    (hF : F.Nonempty) (hcol : (pathSupport T F).Nonempty) :
    ∃ left right : Finset (Fin n),
      actualPathCoefficient T F = left.card * right.card ∧
      actualSignedPathCoefficient T sign F =
        signedMass sign left * signedMass sign right := by
  obtain ⟨cert⟩ := outerCertificate_of_nonempty_collinear
    T sign F hF hcol
  exact ⟨cert.left, cert.right,
    (T8_actual_collinear_outer_factorization T sign F cert).1,
    (T8_actual_collinear_outer_factorization T sign F cert).2⟩

end

end LeechTrees.ParityTail.T8Collinear
