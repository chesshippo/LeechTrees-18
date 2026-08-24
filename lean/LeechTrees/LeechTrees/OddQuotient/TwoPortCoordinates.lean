import LeechTrees.OddQuotient.Components
import LeechTrees.OddEdgesT11Adapter

/-!
# Forward two-port coordinates inside one even component

This module records only the forward metric consequence for three actual
named vertices in one even component.  The two ports may coincide: repeated
port roles are part of the intended odd-quotient representation.

The coordinate equations are stored with natural witnesses `c` and `h` and
the guard `c <= delta`.  Signed recovery is stated over `Int`, so no theorem
uses a prematurely truncated natural expression such as
`(a - b + delta) / 2`.  There is no converse, port injectivity hypothesis,
profile reconstruction, or tree-realization claim here.
-/

namespace LeechTrees.OddQuotient

open LeechTrees.Foundation

variable {n : ℕ}

/-- Division-free two-port projection coordinates.  The intended values are
`a = rho(p,u)`, `b = rho(q,u)`, and `delta = rho(p,q)`. -/
structure TwoPortCoord (a b delta : ℕ) where
  c : ℕ
  h : ℕ
  c_le_delta : c ≤ delta
  left_eq : a = h + c
  right_eq : b = h + (delta - c)

namespace TwoPortCoord

variable {a b delta : ℕ} (x : TwoPortCoord a b delta)

/-- A subtraction-free recovery equation for the projection coordinate. -/
theorem balance_c : b + 2 * x.c = a + delta := by
  have hc := x.c_le_delta
  have ha := x.left_eq
  have hb := x.right_eq
  omega

/-- A subtraction-free recovery equation for the off-path height. -/
theorem balance_h : delta + 2 * x.h = a + b := by
  have hc := x.c_le_delta
  have ha := x.left_eq
  have hb := x.right_eq
  omega

/-- Signed, division-free recovery of `c`.  Moving subtraction to `Int`
prevents natural-number truncation from entering the statement. -/
theorem int_c_equation :
    2 * (x.c : ℤ) = (a : ℤ) - (b : ℤ) + (delta : ℤ) := by
  have hc := x.c_le_delta
  have ha := x.left_eq
  have hb := x.right_eq
  omega

/-- Signed, division-free recovery of `h`. -/
theorem int_h_equation :
    2 * (x.h : ℤ) = (a : ℤ) + (b : ℤ) - (delta : ℤ) := by
  have hc := x.c_le_delta
  have ha := x.left_eq
  have hb := x.right_eq
  omega

theorem c_int_nonnegative : (0 : ℤ) ≤ (x.c : ℤ) := by
  omega

theorem h_int_nonnegative : (0 : ℤ) ≤ (x.h : ℤ) := by
  omega

/-- The signed numerator defining twice `c` is nonnegative. -/
theorem int_c_numerator_nonnegative
    (x : TwoPortCoord a b delta) :
    (0 : ℤ) ≤ (a : ℤ) - (b : ℤ) + (delta : ℤ) := by
  have heq :=
    LeechTrees.OddQuotient.TwoPortCoord.int_c_equation x
  have hc :=
    LeechTrees.OddQuotient.TwoPortCoord.c_int_nonnegative x
  omega

/-- The signed numerator defining twice `h` is nonnegative. -/
theorem int_h_numerator_nonnegative
    (x : TwoPortCoord a b delta) :
    (0 : ℤ) ≤ (a : ℤ) + (b : ℤ) - (delta : ℤ) := by
  have heq :=
    LeechTrees.OddQuotient.TwoPortCoord.int_h_equation x
  have hh :=
    LeechTrees.OddQuotient.TwoPortCoord.h_int_nonnegative x
  omega

end TwoPortCoord

/-- The coordinate witness together with its actual named gate.  The gate
lies on both paths to the first port `p`, and `gate_split_q_u` certifies the
third metric split.  Thus the whole bundle, rather than the two memberships
alone, records the median of `p`, `q`, and `u`.  Membership in `C` is part of
the type, not an unproved assertion about an arbitrary vertex of `Fin n`. -/
structure TwoPortGate (T : PosIntTree n) (C : EvenComponent T)
    (p q u : ComponentVertex T C) where
  gate : ComponentVertex T C
  gate_mem_q_to_p : gate.1 ∈ (T.path q.1 p.1).1.support
  gate_mem_u_to_p : gate.1 ∈ (T.path u.1 p.1).1.support
  gate_split_q_u : rho T q u = rho T q gate + rho T gate u
  coord : TwoPortCoord (rho T p u) (rho T q u) (rho T p q)
  c_eq_gate : coord.c = rho T p gate
  h_eq_gate : coord.h = rho T gate u

/-- Every three actual named vertices in one even component have a named
two-port gate and integral coordinates.  No Leech-spectrum assumption,
distinct-port assumption, or realization converse is used. -/
theorem exists_twoPortGate (T : PosIntTree n) {C : EvenComponent T}
    (p q u : ComponentVertex T C) :
    Nonempty (TwoPortGate T C p q u) := by
  obtain ⟨z, hzq, hzu, hgate, _, _⟩ :=
    LeechTrees.OddEdges.T11Adapter.PosIntTree.exists_root_gate
      T p.1 q.1 u.1

  have hqp_component : componentOf T q.1 = componentOf T p.1 :=
    q.2.trans p.2.symm
  have hzp_component : componentOf T z = componentOf T p.1 := by
    apply componentOf_eq_of_path_all_even T
    intro e he
    exact path_edge_even_of_component_eq T hqp_component
      (LeechTrees.OddEdges.T11Adapter.pathEdges_suffix_subset T hzq he)
  let zC : ComponentVertex T C := ⟨z, hzp_component.trans p.2⟩

  have hqp_split :
      T.dist q.1 p.1 = T.dist q.1 z + T.dist z p.1 :=
    LeechTrees.OddEdges.T11Adapter.PosIntTree.dist_split_at_path_vertex T hzq
  have hup_split :
      T.dist u.1 p.1 = T.dist u.1 z + T.dist z p.1 :=
    LeechTrees.OddEdges.T11Adapter.PosIntTree.dist_split_at_path_vertex T hzu
  have hqu_split :
      T.dist q.1 u.1 = T.dist q.1 z + T.dist z u.1 := by
    rw [T.dist_comm z u.1]
    omega

  have hqp_half := dist_eq_two_mul_rho T q p
  have hqz_half := dist_eq_two_mul_rho T q zC
  have hzp_half := dist_eq_two_mul_rho T zC p
  have hup_half := dist_eq_two_mul_rho T u p
  have huz_half := dist_eq_two_mul_rho T u zC
  have hqu_half := dist_eq_two_mul_rho T q u
  have hzu_half := dist_eq_two_mul_rho T zC u

  have hdelta_raw :
      rho T q p = rho T q zC + rho T zC p := by
    have h := hqp_split
    rw [hqp_half, hqz_half, hzp_half] at h
    omega
  have ha_raw :
      rho T u p = rho T u zC + rho T zC p := by
    have h := hup_split
    rw [hup_half, huz_half, hzp_half] at h
    omega
  have hb_raw :
      rho T q u = rho T q zC + rho T zC u := by
    have h := hqu_split
    rw [hqu_half, hqz_half, hzu_half] at h
    omega

  have hdelta :
      rho T p q = rho T p zC + rho T zC q := by
    calc
      rho T p q = rho T q p := rho_comm T p q
      _ = rho T q zC + rho T zC p := hdelta_raw
      _ = rho T p zC + rho T zC q := by
        rw [rho_comm T p zC, rho_comm T zC q]
        omega
  have ha :
      rho T p u = rho T zC u + rho T p zC := by
    calc
      rho T p u = rho T u p := rho_comm T p u
      _ = rho T u zC + rho T zC p := ha_raw
      _ = rho T zC u + rho T p zC := by
        rw [rho_comm T u zC, rho_comm T zC p]
  have hc_le : rho T p zC ≤ rho T p q := by
    omega
  have hdelta_sub : rho T p q - rho T p zC = rho T zC q := by
    omega
  have hb :
      rho T q u = rho T zC u + (rho T p q - rho T p zC) := by
    rw [hdelta_sub]
    rw [← rho_comm T q zC]
    omega

  let coordinate : TwoPortCoord (rho T p u) (rho T q u) (rho T p q) :=
    { c := rho T p zC
      h := rho T zC u
      c_le_delta := hc_le
      left_eq := ha
      right_eq := hb }
  exact ⟨{
    gate := zC
    gate_mem_q_to_p := hzq
    gate_mem_u_to_p := hzu
    gate_split_q_u := hb_raw
    coord := coordinate
    c_eq_gate := rfl
    h_eq_gate := rfl }⟩

/-- Coordinate-only corollary for consumers that do not need to retain the
named gate witness. -/
theorem exists_twoPortCoord (T : PosIntTree n) {C : EvenComponent T}
    (p q u : ComponentVertex T C) :
    Nonempty (TwoPortCoord (rho T p u) (rho T q u) (rho T p q)) := by
  obtain ⟨g⟩ := exists_twoPortGate T p q u
  exact ⟨g.coord⟩

end LeechTrees.OddQuotient
