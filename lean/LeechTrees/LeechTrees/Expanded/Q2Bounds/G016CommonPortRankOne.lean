import LeechTrees.Expanded.Q2Bounds.G016CommonPortAdapter
import LeechTrees.Expanded.Q2Bounds.G015SupportFactor

/-!
# The common-port rank-one obstruction

This module supplies the second half of the graph bridge left open in
`G016CommonPortAdapter`.  The interval factor there is fed into the repaired
initial-block theorem.  When rank one belongs to the common middle factor,
actual rooted-tree gates (including the `r = 2` crossed-pair fork) force that
factor to have at most four vertices.  When rank one belongs to the other
factor, an even first radix is handled by the actual T12 signed cell masses,
and an odd first radix injects all actual middle-component pairs into the
available positive multiples.

No factor consequence, LCA identity, signed mass, or distance capacity is
accepted as an input at the graph endpoint.
-/

open scoped BigOperators

open LeechTrees.Foundation
open LeechTrees.OddEdges
open LeechTrees.OddEdges.GraphAdapter
open LeechTrees.OddEdges.T11Adapter
open LeechTrees.OddEdges.T12Adapter
open LeechTrees.OddEdges.T12Adapter.PairSums
open LeechTrees.OddQuotient
open LeechTrees.G015
open LeechTrees.G016.CommonPortAdapter

namespace LeechTrees.G016.CommonPortRankOne

open LeechTrees.Foundation
open LeechTrees.OddEdges
open LeechTrees.OddEdges.GraphAdapter
open LeechTrees.OddEdges.T11Adapter
open LeechTrees.OddEdges.T12Adapter
open LeechTrees.OddEdges.T12Adapter.PairSums
open LeechTrees.OddQuotient
open LeechTrees.G015
open LeechTrees.G016.CommonPortAdapter

variable {n : ℕ}

/-! ## A hostile, abstract audit of the `1 ∈ middle` branch -/

private theorem sym2_ne_of_coordinates
    {a b c d : ℕ}
    (hdirect : ¬(a = c ∧ b = d))
    (hswap : ¬(a = d ∧ b = c)) :
    s(a, b) ≠ s(c, d) := by
  intro h
  rcases Sym2.eq_iff.mp h with h | h
  · exact hdirect h
  · exact hswap h

private theorem no_root_distance_collision
    (P : RootedSupportMetric)
    (hinj : ∀ {a b c d : ℕ},
      a ∈ P.support → b ∈ P.support →
      c ∈ P.support → d ∈ P.support →
      a ≠ b → c ≠ d →
      P.dist a b = P.dist c d → s(a, b) = s(c, d))
    {a b k : ℕ}
    (ha : a ∈ P.support) (hb : b ∈ P.support)
    (hk : k ∈ P.support) (hab : a ≠ b) (hk0 : 0 ≠ k)
    (hpairs : s(a, b) ≠ s(0, k)) :
    P.dist a b ≠ k := by
  intro hdist
  apply hpairs
  apply hinj ha hb P.zero_mem hk hab hk0
  rw [P.dist_zero_left hk]
  exact hdist

private theorem card_pair_insert_bound (H : ℕ) :
    ({0, 1, H, H + 1} : Finset ℕ).card ≤ 4 := by
  calc
    ({0, 1, H, H + 1} : Finset ℕ).card ≤
        ({1, H, H + 1} : Finset ℕ).card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ (({H, H + 1} : Finset ℕ).card + 1) + 1 := by
      exact Nat.add_le_add_right (Finset.card_insert_le _ _) 1
    _ ≤ ((({H + 1} : Finset ℕ).card + 1) + 1) + 1 := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_right (Finset.card_insert_le _ _) 1) 1
    _ = 4 := by simp

/-- The full initial-block/LCA conclusion for the factor containing rank one.

The proof deliberately retains all three first-radix cases.  In the binary
case, each positive block has an even-depth vertex forced below the depth-one
vertex and an odd-depth vertex forced outside it.  Two positive blocks then
give the two distinct crossed pairs of the same distance. -/
theorem rankOne_middle_card_le_four
    (P : RootedSupportMetric) (Y : Finset ℕ) (C : ℕ)
    (hsum : IntervalDirectSum P.support Y C)
    (h0Y : 0 ∈ Y) (h1 : 1 ∈ P.support)
    (hYpos : ∃ y ∈ Y, 0 < y)
    (hinj : ∀ {a b c d : ℕ},
      a ∈ P.support → b ∈ P.support →
      c ∈ P.support → d ∈ P.support →
      a ≠ b → c ≠ d →
      P.dist a b = P.dist c d → s(a, b) = s(c, d)) :
    P.support.card ≤ 4 := by
  obtain ⟨r, hr2, hbelow, hrnot⟩ :=
    hsum.exists_firstRadix P.zero_mem h0Y h1 hYpos
  have hrpos : 0 < r := by omega
  have hclass := hsum.block_classification P.zero_mem h0Y
    hrpos hbelow hrnot hYpos
  have hrC := hsum.firstRadix_dvd_length P.zero_mem h0Y
    hrpos hbelow hrnot hYpos

  by_cases hr4 : 4 ≤ r
  · have h1m : 1 ∈ P.support := hbelow 1 (by omega)
    have h2m : 2 ∈ P.support := hbelow 2 (by omega)
    have h3m : 3 ∈ P.support := hbelow 3 (by omega)
    obtain ⟨z, hz, hz1, hz2, hgate⟩ := P.gate h1m h2m
    have hzcase : z = 0 ∨ z = 1 := by omega
    rcases hzcase with rfl | rfl
    · have hne : P.dist 1 2 ≠ 3 :=
        no_root_distance_collision P hinj h1m h2m h3m
          (by omega) (by omega)
          (sym2_ne_of_coordinates (by omega) (by omega))
      omega
    · have hne : P.dist 1 2 ≠ 1 :=
        no_root_distance_collision P hinj h1m h2m h1m
          (by omega) (by omega)
          (sym2_ne_of_coordinates (by omega) (by omega))
      omega

  · have hrle3 : r ≤ 3 := by omega
    by_cases hr3 : r = 3
    · by_cases hcard : P.support.card ≤ 3
      · omega
      · have hx : ∃ x ∈ P.support, 3 ≤ x := by
          by_contra h
          push_neg at h
          have hsub : P.support ⊆ Finset.range 3 := by
            intro x hxmem
            exact Finset.mem_range.mpr (h x hxmem)
          have hle := Finset.card_le_card hsub
          simp at hle
          omega
        obtain ⟨x, hxmem, hx3⟩ := hx
        let H := r * (x / r)
        have hxC : x < C := hsum.sum_lt hxmem h0Y
        have hH : H ∈ P.support := (hclass x hxC).1.mp hxmem
        have hHpos : 0 < H := by
          dsimp only [H]
          rw [hr3]
          have : 0 < x / 3 := Nat.div_pos (by omega) (by omega)
          omega
        have hHC : H < C := hsum.sum_lt hH h0Y
        rcases hrC with ⟨qC, hqC⟩
        have hH2C : H + 2 < C := by
          dsimp only [H] at hHC ⊢
          rw [hr3] at hHC hqC ⊢
          omega
        have hboundary1 : r * ((H + 1) / r) = H := by
          dsimp only [H]
          rw [Nat.mul_add_div hrpos]
          have : 1 / r = 0 := Nat.div_eq_of_lt (by omega)
          rw [this]
          simp
        have hboundary2 : r * ((H + 2) / r) = H := by
          dsimp only [H]
          rw [Nat.mul_add_div hrpos]
          have : 2 / r = 0 := Nat.div_eq_of_lt (by omega)
          rw [this]
          simp
        have hH1 : H + 1 ∈ P.support := by
          apply (hclass (H + 1) (by omega)).1.mpr
          rwa [hboundary1]
        have hH2 : H + 2 ∈ P.support := by
          apply (hclass (H + 2) hH2C).1.mpr
          rwa [hboundary2]
        have h1m : 1 ∈ P.support := hbelow 1 (by omega)
        obtain ⟨z, hz, hz1, hzH, hgate⟩ := P.gate h1m hH1
        have hzcase : z = 0 ∨ z = 1 := by omega
        rcases hzcase with rfl | rfl
        · have hne : P.dist 1 (H + 1) ≠ H + 2 :=
            no_root_distance_collision P hinj h1m hH1 hH2
              (by omega) (by omega)
              (sym2_ne_of_coordinates (by omega) (by omega))
          omega
        · have hne : P.dist 1 (H + 1) ≠ H :=
            no_root_distance_collision P hinj h1m hH1 hH
              (by omega) (by omega)
              (sym2_ne_of_coordinates (by omega) (by omega))
          omega

    · have hr2eq : r = 2 := by omega
      have h1m : 1 ∈ P.support := hbelow 1 (by omega)
      have hblockData : ∀ {H : ℕ},
          H ∈ P.support → 0 < H → r ∣ H →
          H + 1 ∈ P.support ∧
            P.dist 1 H = H - 1 ∧
            P.dist 1 (H + 1) = H + 2 := by
        intro H hH hHpos hHdiv
        have hHC : H < C := hsum.sum_lt hH h0Y
        rcases hrC with ⟨qC, hqC⟩
        rcases hHdiv with ⟨qH, hqH⟩
        have hH1C : H + 1 < C := by
          rw [hr2eq] at hqC hqH
          omega
        have hHge2 : 2 ≤ H := by
          rw [hr2eq] at hqH
          omega
        have hboundary : r * ((H + 1) / r) = H := by
          rw [hqH, Nat.mul_add_div hrpos]
          have : 1 / r = 0 := Nat.div_eq_of_lt (by omega)
          rw [this]
          simp
        have hH1 : H + 1 ∈ P.support := by
          apply (hclass (H + 1) hH1C).1.mpr
          rwa [hboundary]
        refine ⟨hH1, ?_, ?_⟩
        · obtain ⟨z, hz, hz1, hzH, hgate⟩ := P.gate h1m hH
          have hzcase : z = 0 ∨ z = 1 := by omega
          rcases hzcase with rfl | rfl
          · have hne : P.dist 1 H ≠ H + 1 :=
              no_root_distance_collision P hinj h1m hH hH1
                (by omega)
                (by omega)
                (sym2_ne_of_coordinates (by omega) (by omega))
            omega
          · omega
        · obtain ⟨z, hz, hz1, hzH, hgate⟩ := P.gate h1m hH1
          have hzcase : z = 0 ∨ z = 1 := by omega
          rcases hzcase with rfl | rfl
          · omega
          · have hne : P.dist 1 (H + 1) ≠ H :=
              no_root_distance_collision P hinj h1m hH1 hH
                (by omega) (by omega)
                (sym2_ne_of_coordinates (by omega) (by omega))
            omega

      by_cases hlarge : ∃ x ∈ P.support, 2 ≤ x
      · obtain ⟨x, hxmem, hx2⟩ := hlarge
        let H := r * (x / r)
        have hxC : x < C := hsum.sum_lt hxmem h0Y
        have hH : H ∈ P.support := (hclass x hxC).1.mp hxmem
        have hHdiv : r ∣ H := ⟨x / r, by simp [H]⟩
        have hHpos : 0 < H := by
          dsimp only [H]
          rw [hr2eq]
          have : 0 < x / 2 := Nat.div_pos hx2 (by omega)
          omega
        obtain ⟨hH1, hdH, hdH1⟩ := hblockData hH hHpos hHdiv

        have hboundary_unique : ∀ {K : ℕ},
            K ∈ P.support → 0 < K → r ∣ K → K = H := by
          intro K hK hKpos hKdiv
          by_contra hKH
          obtain ⟨hK1, hdK, hdK1⟩ := hblockData hK hKpos hKdiv
          have hrEven : Even r := by
            rw [hr2eq]
            exact ⟨1, by omega⟩
          have hHEven : Even H := by
            rcases hrEven with ⟨a, ha⟩
            rcases hHdiv with ⟨b, hb⟩
            refine ⟨a * b, ?_⟩
            rw [hb, ha]
            ring
          have hKEven : Even K := by
            rcases hrEven with ⟨a, ha⟩
            rcases hKdiv with ⟨b, hb⟩
            refine ⟨a * b, ?_⟩
            rw [hb, ha]
            ring
          have hHK1 : H ≠ K + 1 := by
            rcases hHEven with ⟨a, ha⟩
            rcases hKEven with ⟨b, hb⟩
            omega
          have hKH1 : K ≠ H + 1 := by
            rcases hHEven with ⟨a, ha⟩
            rcases hKEven with ⟨b, hb⟩
            omega
          have hcross1 : P.dist H (K + 1) = H + K + 1 := by
            have houtside : P.dist 1 (K + 1) = 1 + (K + 1) := by
              omega
            have := P.fork h1m hH hK1 (by omega) (by omega) hdH houtside
            omega
          have hcross2 : P.dist K (H + 1) = H + K + 1 := by
            have houtside : P.dist 1 (H + 1) = 1 + (H + 1) := by
              omega
            have := P.fork h1m hK hH1 (by omega) (by omega) hdK houtside
            omega
          have hs := hinj hH hK1 hK hH1 hHK1 hKH1
            (hcross1.trans hcross2.symm)
          rcases Sym2.eq_iff.mp hs with hs | hs
          · exact hKH hs.1.symm
          · omega

        have hsub : P.support ⊆ {0, 1, H, H + 1} := by
          intro y hy
          have hyC : y < C := hsum.sum_lt hy h0Y
          let K := r * (y / r)
          have hK : K ∈ P.support := (hclass y hyC).1.mp hy
          have hKdiv : r ∣ K := ⟨y / r, by simp [K]⟩
          have hydecomp := Nat.div_add_mod y r
          have hymod := Nat.mod_lt y hrpos
          by_cases hK0 : K = 0
          · have : y = 0 ∨ y = 1 := by
              dsimp only [K] at hK0
              rw [hr2eq] at hK0 hydecomp hymod
              omega
            simp only [Finset.mem_insert, Finset.mem_singleton]
            tauto
          · have hKpos : 0 < K := by omega
            have hKH := hboundary_unique hK hKpos hKdiv
            have : y = H ∨ y = H + 1 := by
              dsimp only [K] at hKH
              rw [hr2eq] at hKH hydecomp hymod
              omega
            simp only [Finset.mem_insert, Finset.mem_singleton]
            tauto
        exact (Finset.card_le_card hsub).trans (card_pair_insert_bound H)
      · push_neg at hlarge
        have hsub : P.support ⊆ {0, 1} := by
          intro x hx
          have hxlt : x < 2 := hlarge x hx
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega
        have hcard2 : ({0, 1} : Finset ℕ).card ≤ 2 := by simp
        exact (Finset.card_le_card hsub).trans (hcard2.trans (by omega))

/-! ## The actual common middle component -/

end LeechTrees.G016.CommonPortRankOne

namespace LeechTrees.G016.CommonPortAdapter.CommonPortFrame

open LeechTrees.G016.CommonPortRankOne

variable {T : PosIntTree n} {d : TwoOddEdges T}

theorem middle_component
    (F : CommonPortFrame T d) (u : F.MiddleVertex) :
    componentOf T u.1 = componentOf T F.port := by
  apply componentOf_eq_of_path_all_even T
  intro e he
  rw [T.pathEdges_comm] at he
  rw [← Nat.not_odd_iff_even]
  intro hodd
  let g : T.Edge := T.edgeOfPathMem e he
  rcases (d.odd_iff g).mp (by simpa [g] using hodd) with hg | hg
  · apply u.2.1
    change d.e.1 ∈ T.pathEdges F.port u.1
    have heq : e = d.e.1 := by
      simpa [g] using congrArg Subtype.val hg
    simpa [heq] using he
  · apply u.2.2
    change d.f.1 ∈ T.pathEdges F.port u.1
    have heq : e = d.f.1 := by
      simpa [g] using congrArg Subtype.val hg
    simpa [heq] using he

theorem component_isMiddle
    (F : CommonPortFrame T d)
    (x : ComponentVertex T (componentOf T F.port)) :
    F.IsMiddle x.1 := by
  constructor
  · intro he
    have hev := path_edge_even_of_component_eq T x.2.symm he
    have hev' : Even (T.weight d.e) := by simpa using hev
    exact (Nat.not_odd_iff_even.mpr hev') d.odd_e
  · intro hf
    have hev := path_edge_even_of_component_eq T x.2.symm hf
    have hev' : Even (T.weight d.f) := by simpa using hev
    exact (Nat.not_odd_iff_even.mpr hev') d.odd_f

noncomputable def middleComponentEquiv (F : CommonPortFrame T d) :
    F.MiddleVertex ≃ ComponentVertex T (componentOf T F.port) where
  toFun u := ⟨u.1, F.middle_component u⟩
  invFun x := ⟨x.1, F.component_isMiddle x⟩
  left_inv _ := rfl
  right_inv _ := rfl

def middleRoot (F : CommonPortFrame T d) :
    ComponentVertex T (componentOf T F.port) :=
  ⟨F.port, rfl⟩

theorem rho_middleComponentEquiv
    (F : CommonPortFrame T d) (u : F.MiddleVertex) :
    rho T (F.middleComponentEquiv u) F.middleRoot = F.middleDepth u := by
  unfold rho middleDepth middleComponentEquiv middleRoot
  change T.dist u.1 F.port / 2 = T.dist F.port u.1 / 2
  rw [T.dist_comm u.1 F.port]

theorem middleDepth_symm_middleComponentEquiv
    (F : CommonPortFrame T d)
    (x : ComponentVertex T (componentOf T F.port)) :
    F.middleDepth (F.middleComponentEquiv.symm x) =
      rho T x F.middleRoot := by
  rw [← F.rho_middleComponentEquiv (F.middleComponentEquiv.symm x)]
  simp

theorem middleRho_injective
    (F : CommonPortFrame T d) (hL : IsLeech T) :
    Function.Injective (fun x : ComponentVertex T (componentOf T F.port) =>
      rho T x F.middleRoot) := by
  intro x y hxy
  apply F.middleComponentEquiv.symm.injective
  apply F.middleDepth_injective hL
  rw [F.middleDepth_symm_middleComponentEquiv,
    F.middleDepth_symm_middleComponentEquiv]
  exact hxy

theorem rootedDepthSupport_middleRoot
    (F : CommonPortFrame T d) (_hL : IsLeech T) :
    rootedDepthSupport T F.middleRoot = F.middleDepthSet := by
  ext a
  constructor
  · intro ha
    rw [rootedDepthSupport, Finset.mem_image] at ha
    obtain ⟨x, _, hx⟩ := ha
    rw [middleDepthSet, Finset.mem_image]
    refine ⟨F.middleComponentEquiv.symm x, Finset.mem_univ _, ?_⟩
    rw [F.middleDepth_symm_middleComponentEquiv]
    exact hx
  · intro ha
    rw [middleDepthSet, Finset.mem_image] at ha
    obtain ⟨u, _, hu⟩ := ha
    rw [rootedDepthSupport, Finset.mem_image]
    refine ⟨F.middleComponentEquiv u, Finset.mem_univ _, ?_⟩
    rw [F.rho_middleComponentEquiv]
    exact hu

noncomputable def middleMetric
    (F : CommonPortFrame T d) (hL : IsLeech T) : RootedSupportMetric :=
  rootedComponentMetric T F.middleRoot (F.middleRho_injective hL)

theorem middleMetric_support
    (F : CommonPortFrame T d) (hL : IsLeech T) :
    (F.middleMetric hL).support = F.middleDepthSet := by
  exact F.rootedDepthSupport_middleRoot hL

theorem middleMetric_internal_injective
    (F : CommonPortFrame T d) (hL : IsLeech T) :
    ∀ {a b c e : ℕ},
      a ∈ (F.middleMetric hL).support →
      b ∈ (F.middleMetric hL).support →
      c ∈ (F.middleMetric hL).support →
      e ∈ (F.middleMetric hL).support →
      a ≠ b → c ≠ e →
      (F.middleMetric hL).dist a b =
        (F.middleMetric hL).dist c e →
      s(a, b) = s(c, e) := by
  intro a b c e ha hb hc he hab hce hdist
  exact rootedMetric_internal_injective T hL F.middleRoot
    ha hb hc he hab hce hdist

/-! ## Actual internal-pair ranks and the odd-radix capacity -/

noncomputable def middleVertexEmbedding
    (F : CommonPortFrame T d) (hL : IsLeech T) :
    ↑F.middleDepthSet ↪ Fin n where
  toFun a := ((F.middleDepthEquiv hL).symm a).1
  inj' := by
    intro a b hab
    apply (F.middleDepthEquiv hL).symm.injective
    exact Subtype.ext hab

noncomputable def middleInternalPair
    (F : CommonPortFrame T d) (hL : IsLeech T)
    (e : DepthEdge F.middleDepthSet) : VertexPair n :=
  internalPairOfDepthEdge (F.middleVertexEmbedding hL) e

noncomputable def middleInternalHalfRank
    (F : CommonPortFrame T d) (hL : IsLeech T)
    (e : DepthEdge F.middleDepthSet) : ℕ :=
  T.pairDist (F.middleInternalPair hL e) / 2

theorem middleInternalPair_even
    (F : CommonPortFrame T d) (hL : IsLeech T)
    (e : DepthEdge F.middleDepthSet) :
    Even (T.pairDist (F.middleInternalPair hL e)) := by
  rw [middleInternalPair, pairDist_internalPairOfDepthEdge]
  let u := (F.middleDepthEquiv hL).symm e.1.inf
  let v := (F.middleDepthEquiv hL).symm e.1.sup
  have hcomp : componentOf T u.1 = componentOf T v.1 :=
    (F.middle_component u).trans (F.middle_component v).symm
  simpa [middleVertexEmbedding, u, v] using
    dist_even_of_component_eq T hcomp

theorem two_mul_middleInternalHalfRank
    (F : CommonPortFrame T d) (hL : IsLeech T)
    (e : DepthEdge F.middleDepthSet) :
    2 * F.middleInternalHalfRank hL e =
      T.pairDist (F.middleInternalPair hL e) :=
  Nat.two_mul_div_two_of_even (F.middleInternalPair_even hL e)

theorem middleInternalHalfRank_pos
    (F : CommonPortFrame T d) (hL : IsLeech T)
    (e : DepthEdge F.middleDepthSet) :
    0 < F.middleInternalHalfRank hL e := by
  have hp := hL.pairDist_pos (F.middleInternalPair hL e)
  have hd := F.two_mul_middleInternalHalfRank hL e
  omega

theorem middleInternalHalfRank_le
    (F : CommonPortFrame T d) (hL : IsLeech T)
    (e : DepthEdge F.middleDepthSet) :
    F.middleInternalHalfRank hL e ≤ evenTargetCount n := by
  rw [LeechTrees.OddEdges.T11Adapter.evenTargetCount_eq_half]
  rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
  calc
    F.middleInternalHalfRank hL e * 2 =
        T.pairDist (F.middleInternalPair hL e) := by
      rw [Nat.mul_comm, F.two_mul_middleInternalHalfRank]
    _ ≤ targetN n := hL.pairDist_le_target _

private theorem middleDepthEquiv_symm_depth
    (F : CommonPortFrame T d) (hL : IsLeech T)
    (a : ↑F.middleDepthSet) :
    F.middleDepth ((F.middleDepthEquiv hL).symm a) = (a : ℕ) := by
  have h := congrArg Subtype.val
    ((F.middleDepthEquiv hL).apply_symm_apply a)
  exact h

private theorem depthEdge_inf_ne_sup
    {X : Finset ℕ} (e : DepthEdge X) : e.1.inf ≠ e.1.sup := by
  intro h
  apply (⊤ : SimpleGraph ↑X).not_isDiag_of_mem_edgeSet e.2
  rw [(Sym2.sortEquiv.symm_apply_apply e.1).symm]
  exact Sym2.mk_isDiag_iff.mpr h

theorem middleInternalHalfRank_realizes
    (F : CommonPortFrame T d) (hL : IsLeech T)
    (e : DepthEdge F.middleDepthSet) :
    RealizesInternalRank F.middleDepthSet
      (F.middleInternalHalfRank hL e) := by
  let a : ↑F.middleDepthSet := e.1.inf
  let b : ↑F.middleDepthSet := e.1.sup
  let u : F.MiddleVertex := (F.middleDepthEquiv hL).symm a
  let v : F.MiddleVertex := (F.middleDepthEquiv hL).symm b
  obtain ⟨z, hzu, hzv, hgate, hzuLe, hzvLe⟩ :=
    PosIntTree.exists_root_gate T F.port u.1 v.1
  have hzcomp : componentOf T z = componentOf T F.port := by
    apply componentOf_eq_of_path_all_even T
    intro g hg
    have hsub := pathEdges_suffix_subset T hzu hg
    exact path_edge_even_of_component_eq T (F.middle_component u) hsub
  let zc : ComponentVertex T (componentOf T F.port) := ⟨z, hzcomp⟩
  let zm : F.MiddleVertex := F.middleComponentEquiv.symm zc
  let c := F.middleDepth zm
  have hc : c ∈ F.middleDepthSet := by
    rw [middleDepthSet, Finset.mem_image]
    exact ⟨zm, Finset.mem_univ _, rfl⟩
  have haDepth : F.middleDepth u = (a : ℕ) :=
    F.middleDepthEquiv_symm_depth hL a
  have hbDepth : F.middleDepth v = (b : ℕ) :=
    F.middleDepthEquiv_symm_depth hL b
  have hzc : zm.1 = z := by rfl
  have hctwice : 2 * c = T.dist F.port z := by
    simpa [c, hzc] using F.middleDepth_twice zm
  have hatwice : 2 * (a : ℕ) = T.dist F.port u.1 := by
    rw [← haDepth]
    exact F.middleDepth_twice u
  have hbtwice : 2 * (b : ℕ) = T.dist F.port v.1 := by
    rw [← hbDepth]
    exact F.middleDepth_twice v
  have hranktwice :
      2 * F.middleInternalHalfRank hL e = T.dist u.1 v.1 := by
    rw [F.two_mul_middleInternalHalfRank,
      middleInternalPair, pairDist_internalPairOfDepthEdge]
    rfl
  have hgate' := hgate
  rw [T.dist_comm u.1 F.port, T.dist_comm v.1 F.port,
    T.dist_comm z F.port] at hgate'
  rw [T.dist_comm z F.port, T.dist_comm u.1 F.port] at hzuLe
  rw [T.dist_comm z F.port, T.dist_comm v.1 F.port] at hzvLe
  refine ⟨a, a.2, b, b.2, ?_, c, hc, ?_, ?_, ?_⟩
  · exact fun hab => depthEdge_inf_ne_sup e (Subtype.ext hab)
  · omega
  · omega
  · omega

theorem middleInternalHalfRank_dvd
    (F : CommonPortFrame T d) (hL : IsLeech T)
    {r : ℕ} (hall : ∀ x ∈ F.middleDepthSet, r ∣ x)
    (e : DepthEdge F.middleDepthSet) :
    r ∣ F.middleInternalHalfRank hL e :=
  realizedInternalRank_dvd hall (F.middleInternalHalfRank_realizes hL e)

theorem middleInternalHalfRank_injective
    (F : CommonPortFrame T d) (hL : IsLeech T) :
    Function.Injective (F.middleInternalHalfRank hL) := by
  intro e f hef
  have hpairs : F.middleInternalPair hL e = F.middleInternalPair hL f := by
    apply hL.pairDist_injective
    have he := F.two_mul_middleInternalHalfRank hL e
    have hf := F.two_mul_middleInternalHalfRank hL f
    omega
  exact internalPairOfDepthEdge_injective (F.middleVertexEmbedding hL) hpairs

noncomputable def middleMultipleIndex
    (F : CommonPortFrame T d) (hL : IsLeech T)
    (r : ℕ) (hr : 0 < r)
    (hall : ∀ x ∈ F.middleDepthSet, r ∣ x)
    (e : DepthEdge F.middleDepthSet) :
    Fin (evenTargetCount n / r) := by
  let k := F.middleInternalHalfRank hL e
  have hkpos : 0 < k := F.middleInternalHalfRank_pos hL e
  have hkle : k ≤ evenTargetCount n := F.middleInternalHalfRank_le hL e
  have hkdvd : r ∣ k := F.middleInternalHalfRank_dvd hL hall e
  let q := k / r
  have hqpos : 0 < q := by
    dsimp only [q]
    exact Nat.div_pos (Nat.le_of_dvd hkpos hkdvd) hr
  have hqle : q ≤ evenTargetCount n / r := by
    dsimp only [q]
    exact Nat.div_le_div_right hkle
  exact ⟨q - 1, by omega⟩

theorem middleMultipleIndex_injective
    (F : CommonPortFrame T d) (hL : IsLeech T)
    (r : ℕ) (hr : 0 < r)
    (hall : ∀ x ∈ F.middleDepthSet, r ∣ x) :
    Function.Injective (F.middleMultipleIndex hL r hr hall) := by
  intro e f hef
  have hval := congrArg
    (fun q : Fin (evenTargetCount n / r) => (q : ℕ)) hef
  let ke := F.middleInternalHalfRank hL e
  let kf := F.middleInternalHalfRank hL f
  have hediv : r ∣ ke := F.middleInternalHalfRank_dvd hL hall e
  have hfdiv : r ∣ kf := F.middleInternalHalfRank_dvd hL hall f
  rcases hediv with ⟨qe, hqe⟩
  rcases hfdiv with ⟨qf, hqf⟩
  have hqepos : 0 < qe := by
    have hp := F.middleInternalHalfRank_pos hL e
    change 0 < ke at hp
    rw [hqe] at hp
    by_contra h
    have : qe = 0 := by omega
    simp [this] at hp
  have hqfpos : 0 < qf := by
    have hp := F.middleInternalHalfRank_pos hL f
    change 0 < kf at hp
    rw [hqf] at hp
    by_contra h
    have : qf = 0 := by omega
    simp [this] at hp
  simp only [middleMultipleIndex] at hval
  change ke / r - 1 = kf / r - 1 at hval
  rw [hqe, hqf, Nat.mul_div_right qe hr,
    Nat.mul_div_right qf hr] at hval
  have hqeq : qe = qf := by omega
  apply F.middleInternalHalfRank_injective hL
  change ke = kf
  rw [hqe, hqf, hqeq]

theorem middle_internal_multiple_capacity
    (F : CommonPortFrame T d) (hL : IsLeech T)
    (r : ℕ) (hr : 0 < r)
    (hall : ∀ x ∈ F.middleDepthSet, r ∣ x) :
    F.middleDepthSet.card.choose 2 ≤ evenTargetCount n / r := by
  have hle := Fintype.card_le_of_injective
    (F.middleMultipleIndex hL r hr hall)
    (F.middleMultipleIndex_injective hL r hr hall)
  rw [card_depthEdge] at hle
  simpa using hle

end LeechTrees.G016.CommonPortAdapter.CommonPortFrame

namespace LeechTrees.G016.CommonPortRankOne

/-! ## Taylor data and nontriviality of both factors -/

private theorem odd_half_count_gt_order
    (hn : 38 ≤ n) : n < (targetN n + 1) / 2 := by
  have htwice := two_mul_targetN n
  have hdouble : n + 1 ≤ 2 * n := by omega
  have h8 : 8 ≤ n - 1 := by omega
  have hquad : 4 * (n + 1) ≤ n * (n - 1) := by
    calc
      4 * (n + 1) ≤ 4 * (2 * n) := Nat.mul_le_mul_left 4 hdouble
      _ = n * 8 := by ring
      _ ≤ n * (n - 1) := Nat.mul_le_mul_left n h8
  have hlow : 2 * (n + 1) ≤ targetN n := by omega
  omega

private theorem subtype_fin_card_le
    (P : Fin n → Prop) [DecidablePred P] :
    Fintype.card {v : Fin n // P v} ≤ n := by
  simpa using Fintype.card_le_of_injective
    (fun v : {v : Fin n // P v} => v.1)
    (fun _ _ h => Subtype.ext h)

end LeechTrees.G016.CommonPortRankOne

namespace LeechTrees.G016.CommonPortAdapter.CommonPortFrame

open LeechTrees.G016.CommonPortRankOne

variable {T : PosIntTree n} {d : TwoOddEdges T}

theorem middleCard_eq_parityClassSize
    (F : CommonPortFrame T d) :
    Fintype.card F.MiddleVertex = T.parityClassSize F.port := by
  classical
  unfold PosIntTree.parityClassSize
  exact Fintype.card_congr
    (Equiv.subtypeEquivProp <| funext fun v =>
      propext (F.middle_iff_root_even v))

theorem middleCard_le_order (F : CommonPortFrame T d) :
    Fintype.card F.MiddleVertex ≤ n := by
  rw [F.middleCard_eq_parityClassSize]
  exact T.parityClassSize_le_order F.port

theorem outerCard_le_order (F : CommonPortFrame T d) :
    Fintype.card F.OuterVertex ≤ n := by
  simpa using Fintype.card_le_of_injective
    (fun v : F.OuterVertex => v.1)
    (fun _ _ h => Subtype.ext h)

theorem depthSupports_positive
    (F : CommonPortFrame T d) (hL : IsLeech T) (hn : 38 ≤ n) :
    (∃ x ∈ F.middleDepthSet, 0 < x) ∧
      (∃ y ∈ F.outerDepthSet, 0 < y) := by
  have h0M := F.zero_mem_middleDepthSet
  have h0O := F.zero_mem_outerDepthSet hL (by omega)
  have hprod := (F.intervalDirectSum hL).card_mul
  have hMbound : F.middleDepthSet.card ≤ n := by
    rw [F.middleDepthSet_card hL]
    exact F.middleCard_le_order
  have hObound : F.outerDepthSet.card ≤ n := by
    rw [F.outerDepthSet_card hL]
    exact F.outerCard_le_order
  have hCgt := odd_half_count_gt_order hn
  have hMcard : 1 < F.middleDepthSet.card := by
    have hpos : 0 < F.middleDepthSet.card :=
      Finset.card_pos.mpr ⟨0, h0M⟩
    by_contra h
    have heq : F.middleDepthSet.card = 1 := by omega
    rw [heq, one_mul] at hprod
    omega
  have hOcard : 1 < F.outerDepthSet.card := by
    have hpos : 0 < F.outerDepthSet.card :=
      Finset.card_pos.mpr ⟨0, h0O⟩
    by_contra h
    have heq : F.outerDepthSet.card = 1 := by omega
    rw [heq, mul_one] at hprod
    omega
  exact ⟨Finset.exists_pos_of_one_lt_card hMcard,
    Finset.exists_pos_of_one_lt_card hOcard⟩

/-- Taylor's two natural order forms, with the smaller parity-class order
recorded in exactly the doubled form used by G016. -/
theorem naturalTaylorData
    (F : CommonPortFrame T d) (hL : IsLeech T) (hn : 38 ≤ n) :
    ∃ s m0 : ℕ,
      ((n = s ^ 2 ∧ 2 * m0 = s * (s - 1)) ∨
        (n = s ^ 2 + 2 ∧ 2 * m0 = s * (s - 1) + 2)) ∧
      m0 ≤ Fintype.card F.MiddleVertex := by
  let m := T.parityClassSize F.port
  let m0 := min m (n - m)
  let s := if 2 * m ≤ n then n - 2 * m else 2 * m - n
  have hm : m ≤ n := T.parityClassSize_le_order F.port
  have hpar : m * (n - m) = (targetN n + 1) / 2 :=
    t3_parity_equation hL F.port
  have hhalf :
      2 * (m * (n - m)) = targetN n ∨
        2 * (m * (n - m)) = targetN n + 1 := by
    omega
  have htwice := two_mul_targetN n
  have hclear :
      4 * m * (n - m) = n * (n - 1) ∨
        4 * m * (n - m) = n * (n - 1) + 2 := by
    rcases hhalf with h | h
    · left
      calc
        4 * m * (n - m) = 2 * (2 * (m * (n - m))) := by ring
        _ = 2 * targetN n := by rw [h]
        _ = n * (n - 1) := htwice
    · right
      calc
        4 * m * (n - m) = 2 * (2 * (m * (n - m))) := by ring
        _ = 2 * (targetN n + 1) := by rw [h]
        _ = 2 * targetN n + 2 := by ring
        _ = n * (n - 1) + 2 := by rw [htwice]
  have horderZ :
      (n : ℤ) = (2 * (m : ℤ) - (n : ℤ)) ^ 2 ∨
        (n : ℤ) = (2 * (m : ℤ) - (n : ℤ)) ^ 2 + 2 := by
    rcases hclear with h | h
    · left
      have hn1 : 1 ≤ n := by omega
      have hz :
          4 * (m : ℤ) * ((n : ℤ) - (m : ℤ)) =
            (n : ℤ) * ((n : ℤ) - 1) := by
        have hz0 := congrArg (fun t : ℕ => (t : ℤ)) h
        norm_num [Nat.cast_sub hm, Nat.cast_sub hn1] at hz0
        exact hz0
      nlinarith
    · right
      have hn1 : 1 ≤ n := by omega
      have hz :
          4 * (m : ℤ) * ((n : ℤ) - (m : ℤ)) =
            (n : ℤ) * ((n : ℤ) - 1) + 2 := by
        have hz0 := congrArg (fun t : ℕ => (t : ℤ)) h
        norm_num [Nat.cast_sub hm, Nat.cast_sub hn1] at hz0
        exact hz0
      nlinarith
  have hsquare :
      ((s : ℕ) : ℤ) ^ 2 =
        (2 * (m : ℤ) - (n : ℤ)) ^ 2 := by
    dsimp only [s]
    split_ifs with h
    · rw [Nat.cast_sub h]
      push_cast
      ring
    · have hnm : n ≤ 2 * m := by omega
      rw [Nat.cast_sub hnm]
      push_cast
      ring
  have horder : n = s ^ 2 ∨ n = s ^ 2 + 2 := by
    rcases horderZ with h | h
    · left
      exact_mod_cast h.trans hsquare.symm
    · right
      exact_mod_cast h.trans (congrArg (fun z : ℤ => z + 2) hsquare).symm
  have htwomin : 2 * m0 = n - s := by
    dsimp only [m0, s]
    split_ifs with h
    · rw [Nat.min_eq_left (by omega)]
      omega
    · rw [Nat.min_eq_right (by omega)]
      omega
  have hspos : 1 ≤ s := by
    rcases horder with h | h <;> nlinarith
  have hsdecomp : s ^ 2 = s * (s - 1) + s := by
    calc
      s ^ 2 = s * s := by rw [pow_two]
      _ = s * ((s - 1) + 1) := by rw [Nat.sub_add_cancel hspos]
      _ = s * (s - 1) + s := by ring
  refine ⟨s, m0, ?_, ?_⟩
  · rcases horder with h | h
    · left
      refine ⟨h, ?_⟩
      omega
    · right
      refine ⟨h, ?_⟩
      omega
  · have hm0m : m0 ≤ m := Nat.min_le_left _ _
    rw [F.middleCard_eq_parityClassSize]
    exact hm0m

end LeechTrees.G016.CommonPortAdapter.CommonPortFrame

namespace LeechTrees.G016.CommonPortRankOne

/-! ## The actual T12 signed-mass branch -/

end LeechTrees.G016.CommonPortRankOne

namespace LeechTrees.G016.CommonPortAdapter.CommonPortFrame

open LeechTrees.G016.CommonPortRankOne

variable {T : PosIntTree n} {d : TwoOddEdges T}

private theorem ceilHalfDist_middle
    (F : CommonPortFrame T d) (u : F.MiddleVertex) :
    (ceilHalfTree T).dist F.port u.1 = F.middleDepth u := by
  by_cases hu : F.port = u.1
  · simp [middleDepth, hu]
  · let p := VertexPair.ofDistinct F.port u.1 hu
    have hpRaw : T.pairDist p = T.dist F.port u.1 :=
      T.pairDist_pairOfDistinct F.port u.1 hu
    have hpCeil : (ceilHalfTree T).pairDist p =
        (ceilHalfTree T).dist F.port u.1 :=
      (ceilHalfTree T).pairDist_pairOfDistinct F.port u.1 hu
    have hpaths : T.pathEdges p.left p.right =
        T.pathEdges F.port u.1 := by
      dsimp only [p]
      by_cases hlt : F.port < u.1
      · simp [VertexPair.ofDistinct, hlt, VertexPair.left, VertexPair.right]
      · simp [VertexPair.ofDistinct, hlt, VertexPair.left, VertexPair.right,
          T.pathEdges_comm u.1 F.port]
    have hrel := ceilHalf_pairDist_relation_fixed T d p
    rw [hpRaw, hpCeil] at hrel
    unfold PosIntTree.pathIncidence at hrel
    rw [hpaths] at hrel
    have he : d.e.1 ∉ T.pathEdges F.port u.1 := u.2.1
    have hf : d.f.1 ∉ T.pathEdges F.port u.1 := u.2.2
    simp [he, hf] at hrel
    have htwice := F.middleDepth_twice u
    omega

theorem vertexSign_middle_eq_one
    (F : CommonPortFrame T d)
    (hallEven : ∀ x ∈ F.middleDepthSet, Even x)
    (u : F.MiddleVertex) :
    vertexSign T F.port u.1 = 1 := by
  have hmem : F.middleDepth u ∈ F.middleDepthSet := by
    rw [middleDepthSet, Finset.mem_image]
    exact ⟨u, Finset.mem_univ _, rfl⟩
  have heven := hallEven (F.middleDepth u) hmem
  unfold vertexSign
  rw [F.ceilHalfDist_middle u, heven.neg_one_pow]

theorem massFF_eq_middleCard_of_evenDepths
    (F : CommonPortFrame T d)
    (hallEven : ∀ x ∈ F.middleDepthSet, Even x) :
    massFF T d F.port = (Fintype.card F.MiddleVertex : ℤ) := by
  classical
  unfold massFF cellFF
  calc
    (∑ x : Fin n,
        if ¬rootUses T F.port d.e x ∧ ¬rootUses T F.port d.f x then
          vertexSign T F.port x else 0) =
        ∑ u : F.MiddleVertex, vertexSign T F.port u.1 := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (fun _ => by simp [CommonPortFrame.IsMiddle]) _
    _ = ∑ _u : F.MiddleVertex, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro u _
      exact F.vertexSign_middle_eq_one hallEven u
    _ = (Fintype.card F.MiddleVertex : ℤ) := by simp

theorem middleCard_sq_le_order_of_evenDepths
    (F : CommonPortFrame T d) (hL : IsLeech T)
    (hallEven : ∀ x ∈ F.middleDepthSet, Even x) :
    (Fintype.card F.MiddleVertex : ℤ) ^ 2 ≤ (n : ℤ) := by
  have hTT : massTT T d F.port = 0 :=
    massTT_eq_zero_of_empty T d F.port (fun v => F.no_both v)
  have hFF := F.massFF_eq_middleCard_of_evenDepths hallEven
  have hfactor := even_character_factorization T d F.port
  have htarget := even_character_target T hL
  by_cases hE : Even (evenTargetCount n)
  · rw [if_pos hE] at htarget
    rw [htarget, hTT, hFF] at hfactor
    nlinarith [sq_nonneg (massTF T d F.port - massFT T d F.port)]
  · rw [if_neg hE] at htarget
    rw [htarget, hTT, hFF] at hfactor
    nlinarith [sq_nonneg (massTF T d F.port - massFT T d F.port)]

end LeechTrees.G016.CommonPortAdapter.CommonPortFrame

namespace LeechTrees.G016.CommonPortRankOne

/-! ## Exhaustion of the rank-one alternatives -/

private theorem two_mul_choose_two (m : ℕ) :
    2 * m.choose 2 = m * (m - 1) := by
  rw [Nat.choose_two_right]
  apply Nat.mul_div_cancel'
  by_cases hm : Even m
  · rcases hm with ⟨q, hq⟩
    refine ⟨q * (m - 1), ?_⟩
    rw [hq]
    ring
  · rcases Nat.not_even_iff_odd.mp hm with ⟨q, hq⟩
    have hmpos : 0 < m := by omega
    have hm1 : m - 1 = q + q := by omega
    refine ⟨m * q, ?_⟩
    rw [hm1]
    ring

end LeechTrees.G016.CommonPortRankOne

namespace LeechTrees.G016.CommonPortAdapter.CommonPortFrame

open LeechTrees.G016.CommonPortRankOne

variable {T : PosIntTree n} {d : TwoOddEdges T}

/-- The three conclusions of the common-port rank-one analysis, now derived
from the actual tree, the actual common port, and the actual indexed interval
factor. -/
theorem rankOneConsequences
    (F : CommonPortFrame T d) (hL : IsLeech T) (hn : 38 ≤ n)
    (_hEven : Even (oddTargetCount n))
    (s : ℕ) (horder : n = s ^ 2 ∨ n = s ^ 2 + 2) :
    Fintype.card F.MiddleVertex ≤ 4 ∨
      Fintype.card F.MiddleVertex ≤ s ∨
      3 * (Fintype.card F.MiddleVertex *
        (Fintype.card F.MiddleVertex - 1)) ≤
          2 * evenTargetCount n := by
  let C := (targetN n + 1) / 2
  have hsum : IntervalDirectSum F.middleDepthSet F.outerDepthSet C :=
    F.intervalDirectSum hL
  have h0M := F.zero_mem_middleDepthSet
  have h0O := F.zero_mem_outerDepthSet hL (by omega)
  obtain ⟨hMpos, hOpos⟩ := F.depthSupports_positive hL hn
  have hC1 : 1 < C := by
    have := odd_half_count_gt_order hn
    omega
  obtain ⟨a, haM, b, hbO, hab⟩ := hsum.exists_repr hC1
  have hrankOne :
      (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) := by
    omega
  rcases hrankOne with hMone | hOone
  · have h1M : 1 ∈ F.middleDepthSet := by simpa [hMone.1] using haM
    let P := F.middleMetric hL
    have hsumP : IntervalDirectSum P.support F.outerDepthSet C := by
      rw [F.middleMetric_support]
      exact hsum
    have h1P : 1 ∈ P.support := by
      rw [F.middleMetric_support]
      exact h1M
    have hcard := rankOne_middle_card_le_four P F.outerDepthSet C
      hsumP h0O h1P hOpos (F.middleMetric_internal_injective hL)
    left
    dsimp only [P] at hcard
    rw [F.middleMetric_support, F.middleDepthSet_card hL] at hcard
    exact hcard
  · have h1O : 1 ∈ F.outerDepthSet := by simpa [hOone.2] using hbO
    let hswap : IntervalDirectSum F.outerDepthSet F.middleDepthSet C :=
      hsum.comm
    obtain ⟨r, hr2, hbelow, hrnot⟩ :=
      hswap.exists_firstRadix h0O h0M h1O hMpos
    have hrpos : 0 < r := by omega
    have hclass := hswap.block_classification h0O h0M
      hrpos hbelow hrnot hMpos
    have hall : ∀ x ∈ F.middleDepthSet, r ∣ x := by
      intro x hx
      have hxC := hswap.sum_lt h0O hx
      exact (hclass x (by simpa using hxC)).2 hx
    by_cases hrEven : Even r
    · have hallEven : ∀ x ∈ F.middleDepthSet, Even x := by
        intro x hx
        rcases hrEven with ⟨q, hq⟩
        rcases hall x hx with ⟨k, hk⟩
        refine ⟨q * k, ?_⟩
        rw [hk, hq]
        ring
      have hsqZ := F.middleCard_sq_le_order_of_evenDepths hL hallEven
      have hsq : (Fintype.card F.MiddleVertex) ^ 2 ≤ n := by
        exact_mod_cast hsqZ
      right
      left
      rcases horder with h | h
      · nlinarith
      · have hspos : 1 ≤ s := by nlinarith
        by_contra hms
        have : s + 1 ≤ Fintype.card F.MiddleVertex := by omega
        nlinarith
    · have hrOdd : Odd r := Nat.not_even_iff_odd.mp hrEven
      have hr3 : 3 ≤ r := by
        rcases hrOdd with ⟨q, hq⟩
        omega
      have hcap := F.middle_internal_multiple_capacity hL r hrpos hall
      have hmuldiv :
          3 * (evenTargetCount n / r) ≤ evenTargetCount n := by
        calc
          3 * (evenTargetCount n / r) ≤
              r * (evenTargetCount n / r) :=
            Nat.mul_le_mul_right (evenTargetCount n / r) hr3
          _ ≤ evenTargetCount n := Nat.mul_div_le _ _
      have hchoose :
          3 * F.middleDepthSet.card.choose 2 ≤ evenTargetCount n :=
        calc
          3 * F.middleDepthSet.card.choose 2 ≤
              3 * (evenTargetCount n / r) :=
            Nat.mul_le_mul_left 3 hcap
          _ ≤ evenTargetCount n := hmuldiv
      have hid := two_mul_choose_two F.middleDepthSet.card
      have hfinal :
          3 * (F.middleDepthSet.card *
            (F.middleDepthSet.card - 1)) ≤
              2 * evenTargetCount n := by
        calc
          3 * (F.middleDepthSet.card *
              (F.middleDepthSet.card - 1)) =
              2 * (3 * F.middleDepthSet.card.choose 2) := by
            rw [← hid]
            ring
          _ ≤ 2 * evenTargetCount n := Nat.mul_le_mul_left 2 hchoose
      right
      right
      rw [F.middleDepthSet_card hL] at hfinal
      exact hfinal

end LeechTrees.G016.CommonPortAdapter.CommonPortFrame

namespace LeechTrees.G016.CommonPortRankOne

/-! ## Actual factor consequences and unconditional graph endpoints -/

private theorem actual_even_capacity (n : ℕ) :
    4 * evenTargetCount n ≤ n * (n - 1) := by
  have hhalf : 2 * evenTargetCount n ≤ targetN n := by
    rw [LeechTrees.OddEdges.T11Adapter.evenTargetCount_eq_half]
    omega
  have htwice := two_mul_targetN n
  omega

/-- The former `CommonPortGraphBridge` output, constructed from the actual
graph with no bridge hypothesis remaining. -/
theorem actual_commonPort_factorConsequences_ge38
    (T : PosIntTree n) (hL : IsLeech T) (hn : 38 ≤ n)
    (hTwo : ExactlyTwoOddPhysicalEdges T)
    (hCommon : LeechTrees.G016.CommonMiddlePort T hTwo) :
    Nonempty (LeechTrees.G016.CommonPortFactorConsequences n) := by
  let d := twoOddEdges T hTwo
  let F : CommonPortFrame T d :=
    Classical.choice (frame_of_commonMiddlePort T hTwo hCommon)
  obtain ⟨s, m0, hTaylor, hm0⟩ := F.naturalTaylorData hL hn
  let m := Fintype.card F.MiddleVertex
  let E := evenTargetCount n
  have hEven : Even (oddTargetCount n) :=
    t12_two_odd_physical_edges T hL (by omega) hTwo
  have horder : n = s ^ 2 ∨ n = s ^ 2 + 2 := by
    rcases hTaylor with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hrank := F.rankOneConsequences hL hn hEven s horder
  refine ⟨{
    s := s
    m := m
    m0 := m0
    E := E
    orderLower := hTaylor
    middleLower := ?_
    evenCapacity := ?_
    rankOne := ?_ }⟩
  · simpa only [m] using hm0
  · simpa only [E] using actual_even_capacity n
  · simpa only [m, E] using hrank

/-- The explicitly constructed value of the old bridge proposition.  This is
kept as a compatibility endpoint; the public nonexistence theorems below do
not ask callers to supply it. -/
theorem actual_commonPortGraphBridge :
    LeechTrees.G016.CommonPortGraphBridge := by
  intro n T hL hn hTwo hCommon hEven
  exact actual_commonPort_factorConsequences_ge38 T hL hn hTwo hCommon

/-- No actual common-middle-port, exactly-two-odd Leech tree has order at
least 38. -/
theorem commonPort_impossible_ge38
    (T : PosIntTree n) (hL : IsLeech T) (hn : 38 ≤ n)
    (hTwo : ExactlyTwoOddPhysicalEdges T)
    (hCommon : LeechTrees.G016.CommonMiddlePort T hTwo) : False := by
  let D := Classical.choice
    (actual_commonPort_factorConsequences_ge38 T hL hn hTwo hCommon)
  exact D.large_order_impossible hn

/-- The audited combined threshold: order 36 is removed by the arbitrary-port
parity theorem, order 37 by Taylor admissibility, and every order at least 38
by the actual common-port rank-one analysis above. -/
theorem commonPort_impossible_ge36
    (T : PosIntTree n) (hL : IsLeech T) (hn : 36 ≤ n)
    (hTwo : ExactlyTwoOddPhysicalEdges T)
    (hCommon : LeechTrees.G016.CommonMiddlePort T hTwo) : False := by
  by_cases h36 : n = 36
  · subst n
    exact (LeechTrees.G016.no_exactlyTwo_order36 T hL) hTwo
  by_cases h37 : n = 37
  · subst n
    exact LeechTrees.G016.no_leech_order37 T hL
  have hn38 : 38 ≤ n := by omega
  exact commonPort_impossible_ge38 T hL hn38 hTwo hCommon

/-- Public negated-existence form of the unconditional common-port endpoint. -/
theorem no_commonPort_exactlyTwo_ge36
    (T : PosIntTree n) (hL : IsLeech T) (hn : 36 ≤ n) :
    ¬ ∃ hTwo : ExactlyTwoOddPhysicalEdges T,
        LeechTrees.G016.CommonMiddlePort T hTwo := by
  rintro ⟨hTwo, hCommon⟩
  exact commonPort_impossible_ge36 T hL hn hTwo hCommon

end LeechTrees.G016.CommonPortRankOne
