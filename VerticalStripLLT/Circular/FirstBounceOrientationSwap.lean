import VerticalStripLLT.Circular.FirstBounceOrientationData
import VerticalStripLLT.Circular.PeriodicBoundarySwap

set_option backward.isDefEq.respectTransparency false

/-! The periodic swap acting on natural edges. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

namespace Diagram

variable {n : ℕ} (D : Diagram n)

/-- The edge whose lift is the periodic swap of the lift of `ε` (when valid). -/
noncomputable def swapEdge (P : ℤ) (ε : Edge D.area) : Edge D.area :=
  if h : D.boundaryNaturalLift (periodicSwap n P (ε.tail.val : ℤ))
      (periodicSwap n P ((ε.tail.val : ℤ) + ε.length.val)) then
    D.edgeFromLift _ _ h else ε

theorem naturalLift_head {ε : Edge D.area} {x y : ℤ} (h : D.naturalLift ε x y) :
    ε.head = D.residue y := by
  rw [h.2, D.residue_add_length ε x h.1]

theorem naturalLift_base (ε : Edge D.area) :
    D.naturalLift ε (ε.tail.val : ℤ) ((ε.tail.val : ℤ) + ε.length.val) :=
  ⟨Orientation.residue_intCast_eq _, rfl⟩

theorem naturalLift_translate {ε : Edge D.area} {x y : ℤ} (h : D.naturalLift ε x y) (k : ℤ) :
    D.naturalLift ε (x + n * k) (y + n * k) :=
  ⟨by rw [D.residue_add_period]; exact h.1, by rw [h.2]; ring⟩

theorem naturalLift_boundary {ε : Edge D.area} {x y : ℤ} (h : D.naturalLift ε x y) :
    D.boundary y ≤ x ∧ x < y :=
  D.boundaryNaturalLift_of_edge (D.naturalLift_head h) (by rw [h.2]; ring)

section NN

variable (e : Edge D.area) (he : e ∈ D.strict) (hlen : 2 ≤ e.length.val)
  (hgap : D.area.area (D.area.next e.head) < D.area.area e.head)
  (hsame : D.boundary ((e.tail.val : ℤ) + 1) = D.boundary (e.tail.val : ℤ))
  (hleft : ¬ D.strictAt (e.tail.val : ℤ))
  (hright : ¬ D.strictAt ((e.tail.val : ℤ) + 1))

include hlen in
theorem nn_two_le : (2 : ℤ) ≤ n := by
  have := D.nn_three_le e hlen
  lia

include he hgap in
theorem nn_havoid (z k : ℤ) : D.boundary z ≠ (e.tail.val : ℤ) + 1 + n * k := by
  intro h
  apply D.nn_boundary_ne e he hgap (z + n * (-k))
  rw [D.boundary_add_period, h]
  ring

include hlen in
theorem nn_ps_fix (z : ℤ) (h1 : D.residue z ≠ D.residue (e.tail.val : ℤ))
    (h2 : D.residue z ≠ D.residue ((e.tail.val : ℤ) + 1)) :
    periodicSwap n (e.tail.val : ℤ) z = z := by
  have hn := D.nn_two_le e hlen
  unfold periodicSwap
  rw [ite_eq_right, ite_eq_right]
  · intro h
    apply h2
    apply (D.residue_eq_iff_mod_sub_zero).mpr
    have h1n : (1 : ℤ) % n = 1 := Int.emod_eq_of_lt (by lia) (by lia)
    rw [show z - ((e.tail.val : ℤ) + 1) = (z - e.tail.val) - 1 by ring, Int.sub_emod, h, h1n]
    simp
  · intro h
    exact h1 ((D.residue_eq_iff_mod_sub_zero).mpr h)

include hsame in
theorem nn_not_periodicBridge (ε : Edge D.area) (hε : ε ≠ D.bridgeEdge e) {x y : ℤ}
    (h : D.naturalLift ε x y) : ¬ periodicBridge n (e.tail.val : ℤ) x y := by
  rintro ⟨k, hx, hy⟩
  apply hε
  apply D.nn_eq_bridge e hsame
  · rw [← h.1, hx, D.residue_add_period]
  · have := h.2
    lia

include he hlen hgap hsame in
theorem nn_swap_valid (ε : Edge D.area) (hε : ε ≠ D.bridgeEdge e) :
    D.boundaryNaturalLift (periodicSwap n (e.tail.val : ℤ) (ε.tail.val : ℤ))
      (periodicSwap n (e.tail.val : ℤ) ((ε.tail.val : ℤ) + ε.length.val)) := by
  have hb := D.naturalLift_boundary (D.naturalLift_base ε)
  have := periodicSwap_boundary_forward n (e.tail.val : ℤ) (D.nn_two_le e hlen) D.boundary
    D.boundary_add_period hsame (D.nn_havoid e he hgap) _ _
    ⟨hb.1, hb.2, D.nn_not_periodicBridge e hsame ε hε (D.naturalLift_base ε)⟩
  exact ⟨this.1, this.2.1⟩

include he hlen hgap hsame in
theorem nn_swapEdge_eq (ε : Edge D.area) (hε : ε ≠ D.bridgeEdge e) :
    D.swapEdge (e.tail.val : ℤ) ε =
      D.edgeFromLift _ _ (D.nn_swap_valid e he hlen hgap hsame ε hε) := by
  unfold swapEdge
  rw [dite_eq_left (D.nn_swap_valid e he hlen hgap hsame ε hε)]

include he hlen hgap hsame in
theorem nn_swapEdge_naturalLift (ε : Edge D.area) (hε : ε ≠ D.bridgeEdge e) {x y : ℤ}
    (h : D.naturalLift ε x y) :
    D.naturalLift (D.swapEdge (e.tail.val : ℤ) ε)
      (periodicSwap n (e.tail.val : ℤ) x) (periodicSwap n (e.tail.val : ℤ) y) := by
  have hn := D.nn_two_le e hlen
  obtain ⟨k, hk⟩ := D.residue_eq_exists_period (h.1.trans (Orientation.residue_intCast_eq _).symm)
  have hy : y = ((ε.tail.val : ℤ) + ε.length.val) + n * k := by rw [h.2, hk]; ring
  rw [hk, hy, periodicSwap_translate _ _ _ _ hn, periodicSwap_translate _ _ _ _ hn]
  apply naturalLift_translate
  rw [D.nn_swapEdge_eq e he hlen hgap hsame ε hε]
  exact D.edgeFromLift_naturalLift _

include he hlen hgap hsame in
theorem nn_swapEdge_ne_bridge (ε : Edge D.area) (hε : ε ≠ D.bridgeEdge e) :
    D.swapEdge (e.tail.val : ℤ) ε ≠ D.bridgeEdge e := by
  intro heq
  have hb := D.naturalLift_boundary (D.naturalLift_base ε)
  have hf := periodicSwap_boundary_forward n (e.tail.val : ℤ) (D.nn_two_le e hlen) D.boundary
    D.boundary_add_period hsame (D.nn_havoid e he hgap) _ _
    ⟨hb.1, hb.2, D.nn_not_periodicBridge e hsame ε hε (D.naturalLift_base ε)⟩
  have hl := D.nn_swapEdge_naturalLift e he hlen hgap hsame ε hε (D.naturalLift_base ε)
  rw [heq] at hl
  apply hf.2.2
  have h1 := hl.1
  rw [D.nn_bridge_tail e hsame] at h1
  obtain ⟨k, hk⟩ := D.residue_eq_exists_period h1
  refine ⟨k, hk, ?_⟩
  rw [hl.2, D.nn_bridge_length e hsame, hk]
  ring

include he hlen hgap hsame in
theorem nn_swapEdge_swapEdge (ε : Edge D.area) (hε : ε ≠ D.bridgeEdge e) :
    D.swapEdge (e.tail.val : ℤ) (D.swapEdge (e.tail.val : ℤ) ε) = ε := by
  have hi := periodicSwap_involutive n (e.tail.val : ℤ) (D.nn_two_le e hlen)
  have h1 := D.nn_swapEdge_naturalLift e he hlen hgap hsame ε hε (D.naturalLift_base ε)
  have h2 := D.nn_swapEdge_naturalLift e he hlen hgap hsame _
    (D.nn_swapEdge_ne_bridge e he hlen hgap hsame ε hε) h1
  rw [hi, hi] at h2
  exact D.naturalLift_injective h2 (D.naturalLift_base ε)

include he hsame hright in
theorem nn_e_ne_bridge : e ≠ D.bridgeEdge e := by
  intro h
  exact D.nn_bridge_not_strict e hsame hright (h ▸ he)

include he hlen hgap hsame hright in
theorem nn_swapEdge_e :
    D.swapEdge (e.tail.val : ℤ) e = D.shortenedOldEdge e he hlen := by
  have hn := D.nn_two_le e hlen
  have h1 := D.nn_swapEdge_naturalLift e he hlen hgap hsame e
    (D.nn_e_ne_bridge e he hsame hright) (D.naturalLift_base e)
  have hP : periodicSwap n (e.tail.val : ℤ) (e.tail.val : ℤ) = (e.tail.val : ℤ) + 1 := by
    simpa using (periodicSwap_base n (e.tail.val : ℤ) 0 hn).1
  have hT : periodicSwap n (e.tail.val : ℤ) ((e.tail.val : ℤ) + e.length.val) =
      (e.tail.val : ℤ) + e.length.val := by
    apply D.nn_ps_fix e hlen
    · rw [nn_residue_T]; exact D.nn_head_ne_P e hlen
    · rw [nn_residue_T]; exact D.nn_head_ne_P1 e hlen
  rw [hP, hT] at h1
  apply D.naturalLift_injective h1
  refine ⟨(D.nn_fE_tail e he hlen).symm, ?_⟩
  rw [D.nn_fE_length e he hlen]
  ring

include he hlen hgap hsame hleft hright in
theorem nn_swapEdge_fix (ε : Edge D.area) (hε : ε ∈ D.strict) (hne : ε ≠ e) :
    D.swapEdge (e.tail.val : ℤ) ε = ε := by
  have hends := D.nn_strict_endpoints e he hgap hleft hright ε hε hne
  have hεb : ε ≠ D.bridgeEdge e := fun h => D.nn_bridge_not_strict e hsame hright (h ▸ hε)
  have h1 := D.nn_swapEdge_naturalLift e he hlen hgap hsame ε hεb (D.naturalLift_base ε)
  have hx : periodicSwap n (e.tail.val : ℤ) (ε.tail.val : ℤ) = ε.tail.val := by
    apply D.nn_ps_fix e hlen <;> rw [Orientation.residue_intCast_eq]
    · exact hends.2.2.1
    · exact hends.2.2.2
  have hy : periodicSwap n (e.tail.val : ℤ) ((ε.tail.val : ℤ) + ε.length.val) =
      (ε.tail.val : ℤ) + ε.length.val := by
    apply D.nn_ps_fix e hlen <;>
      rw [D.residue_add_length ε _ (Orientation.residue_intCast_eq _)]
    · exact hends.1
    · exact hends.2.1
  rw [hx, hy] at h1
  exact D.naturalLift_injective h1 (D.naturalLift_base ε)

end NN

end Diagram

end VerticalStripLLT.Circular

