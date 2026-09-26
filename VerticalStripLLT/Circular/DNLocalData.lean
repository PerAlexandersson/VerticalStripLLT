import VerticalStripLLT.Circular.HRVStepComparison
import VerticalStripLLT.Circular.SecondBounceGeometry
import VerticalStripLLT.Circular.CornerBoundary
import VerticalStripLLT.Circular.PeriodicSwapResidue

set_option backward.isDefEq.respectTransparency false

-- NEW MODULE VerticalStripLLT.Circular.DNLocalData

/-! Local data of a DN single contact: the strict edges `e : a → i`, `f : i → z`,
the successor `y` of `i`, the two local normal edges `i → y`, `y → z`, and the
exterior boundary of the diagram with `e` deleted. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

namespace Diagram

variable {n : ℕ} (D : Diagram n)

section DN

variable (e f : Edge D.area) (he : e ∈ D.strict) (hf : f ∈ D.strict)
  (hcontact : f.tail = e.head)
  (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
  (hb : D.area.area e.head + 1 < n)
  (hns : ∀ g ∈ D.strict, g.head ≠ D.area.next e.head)
  (hlen : 2 ≤ f.length.val)
  (hgap : D.area.area (D.area.next f.head) < D.area.area f.head)

include he in
theorem dn_Le : e.length.val = D.area.area e.head := (D.strict_corner e he).1

include hf in
theorem dn_Lf : f.length.val = D.area.area f.head := (D.strict_corner f hf).1

include he hb in
theorem dn_three_le : 3 ≤ n := by
  have := e.length_pos
  have := D.dn_Le e he
  lia

include he hb in
theorem dn_two_le : (2 : ℤ) ≤ n := by
  have := D.dn_three_le e he hb
  lia

theorem dn_res_p : D.residue (e.head.val : ℤ) = e.head := Orientation.residue_intCast_eq _

theorem dn_res_p1 : D.residue ((e.head.val : ℤ) + 1) = D.area.next e.head := by
  rw [D.residue_succ, dn_res_p]

theorem dn_e_lift : D.naturalLift e ((e.head.val : ℤ) - e.length.val) e.head.val :=
  D.naturalLift_of_head_length (D.dn_res_p e).symm (by ring)

theorem dn_res_a : D.residue ((e.head.val : ℤ) - e.length.val) = e.tail :=
  (D.dn_e_lift e).1

include hcontact in
theorem dn_f_lift : D.naturalLift f e.head.val ((e.head.val : ℤ) + f.length.val) := by
  have := D.naturalLift_base f
  rw [hcontact] at this
  exact this

include hcontact in
theorem dn_res_T : D.residue ((e.head.val : ℤ) + f.length.val) = f.head :=
  (D.naturalLift_head (D.dn_f_lift e f hcontact)).symm

include he hb in
theorem dn_Y_ne_I : D.area.next e.head ≠ e.head := by
  intro h
  apply D.residue_p_ne_succ (D.dn_three_le e he hb |>.trans' (by lia)) (e.head.val : ℤ)
  rw [dn_res_p, dn_res_p1, h]

include he hb in
theorem dn_A_ne_Y : e.tail ≠ D.area.next e.head := by
  intro h
  rw [← D.dn_res_a e, ← D.dn_res_p1 e] at h
  have hL := e.length_pos
  have := D.dn_Le e he
  have := D.eq_of_residue_eq_of_bounds h.symm (by lia) (by lia)
  lia

include hcontact in
theorem dn_Z_ne_I : f.head ≠ e.head := by
  rw [← hcontact]
  exact fun h => f.tail_ne_head h.symm

include hf hns in
theorem dn_Z_ne_Y : f.head ≠ D.area.next e.head := hns f hf

include he heq in
theorem dn_g_valid :
    D.boundaryNaturalLift (e.head.val : ℤ) ((e.head.val : ℤ) + 1) := by
  refine ⟨?_, by lia⟩
  rw [boundary, dn_res_p1, heq]
  have := e.length_pos
  have := D.dn_Le e he
  lia

/-- The local normal edge `i → y`. -/
noncomputable def dnG : Edge D.area := D.edgeFromLift _ _ (D.dn_g_valid e he heq)

theorem dnG_lift : D.naturalLift (D.dnG e he heq) (e.head.val : ℤ) ((e.head.val : ℤ) + 1) :=
  D.edgeFromLift_naturalLift _

theorem dnG_tail : (D.dnG e he heq).tail = e.head := by
  rw [dnG, edgeFromLift_tail, dn_res_p]

theorem dnG_head : (D.dnG e he heq).head = D.area.next e.head := by
  rw [dnG, edgeFromLift_head, dn_res_p1]

include hns in
theorem dnG_not_strict : D.dnG e he heq ∉ D.strict := fun h =>
  hns _ h (D.dnG_head e he heq)

include hf hcontact hlen in
theorem dn_h_valid :
    D.boundaryNaturalLift ((e.head.val : ℤ) + 1) ((e.head.val : ℤ) + f.length.val) := by
  refine ⟨?_, by lia⟩
  rw [boundary, D.dn_res_T e f hcontact, ← D.dn_Lf f hf]
  lia

/-- The local normal edge `y → z`. -/
noncomputable def dnH : Edge D.area := D.edgeFromLift _ _ (D.dn_h_valid e f hf hcontact hlen)

theorem dnH_lift : D.naturalLift (D.dnH e f hf hcontact hlen) ((e.head.val : ℤ) + 1)
    ((e.head.val : ℤ) + f.length.val) :=
  D.edgeFromLift_naturalLift _

theorem dnH_tail : (D.dnH e f hf hcontact hlen).tail = D.area.next e.head := by
  rw [dnH, edgeFromLift_tail, dn_res_p1]

theorem dnH_head : (D.dnH e f hf hcontact hlen).head = f.head := by
  rw [dnH, edgeFromLift_head, D.dn_res_T e f hcontact]

theorem dnH_length : ((D.dnH e f hf hcontact hlen).length.val : ℤ) = f.length.val - 1 := by
  rw [dnH, edgeFromLift_length]
  ring

theorem dnH_not_strict : D.dnH e f hf hcontact hlen ∉ D.strict := by
  intro h
  have hc := (D.strict_corner _ h).1
  have hl := D.dnH_length e f hf hcontact hlen
  rw [D.dnH_head e f hf hcontact hlen, ← D.dn_Lf f hf] at hc
  lia

/-- The boundary of the diagram with the first strict edge deleted. -/
theorem dn_R_boundary (z : ℤ) :
    (D.deleteCorner e (D.strict_corner e he)).boundary z =
      D.boundary z + if D.residue z = e.head then 1 else 0 := by
  exact D.deleteCorner_boundary e (D.strict_corner e he) z

include he in
theorem dn_boundary_le_R (z : ℤ) :
    D.boundary z ≤ (D.deleteCorner e (D.strict_corner e he)).boundary z := by
  rw [D.dn_R_boundary e he]
  split_ifs <;> lia

include heq hb in
theorem dn_R_same :
    (D.deleteCorner e (D.strict_corner e he)).boundary ((e.head.val : ℤ) + 1) =
      (D.deleteCorner e (D.strict_corner e he)).boundary (e.head.val : ℤ) := by
  rw [D.dn_R_boundary e he, D.dn_R_boundary e he, dn_res_p, dn_res_p1,
    ite_eq_right (D.dn_Y_ne_I e he hb), ite_eq_left rfl, boundary, boundary,
    dn_res_p, dn_res_p1, heq]
  ring

include hf hcontact hgap in
theorem dn_R_avoid (z k : ℤ) :
    (D.deleteCorner e (D.strict_corner e he)).boundary z ≠
      (e.head.val : ℤ) + 1 + n * k := by
  have hT : (D.deleteCorner e (D.strict_corner e he)).boundary
      ((e.head.val : ℤ) + f.length.val) = e.head.val := by
    rw [D.dn_R_boundary e he, D.dn_res_T e f hcontact, ite_eq_right (D.dn_Z_ne_I e f hcontact),
      boundary, D.dn_res_T e f hcontact, ← D.dn_Lf f hf]
    ring
  have hT1 : (e.head.val : ℤ) + 2 ≤ (D.deleteCorner e (D.strict_corner e he)).boundary
      ((e.head.val : ℤ) + f.length.val + 1) := by
    have h1 := D.dn_boundary_le_R e he ((e.head.val : ℤ) + f.length.val + 1)
    have h0 : D.boundary ((e.head.val : ℤ) + f.length.val + 1) =
        (e.head.val : ℤ) + f.length.val + 1 - D.area.area (D.area.next f.head) := by
      rw [boundary, D.residue_succ, D.dn_res_T e f hcontact]
    rw [h0] at h1
    have h2 := D.dn_Lf f hf
    have h3 : (D.area.area (D.area.next f.head) : ℤ) + 1 ≤ f.length.val := by
      rw [h2]; exact_mod_cast hgap
    lia
  intro h
  apply (D.deleteCorner e (D.strict_corner e he)).no_boundary_gap _ _ hT hT1 (z + n * (-k))
  rw [(D.deleteCorner e (D.strict_corner e he)).boundary_add_period, h]
  ring

end DN

end Diagram

end VerticalStripLLT.Circular

