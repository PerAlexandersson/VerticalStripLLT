import VerticalStripLLT.Circular.HRVPotential
import VerticalStripLLT.Circular.BoundaryEdges
import VerticalStripLLT.Circular.ShortenStrictPairs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


/-! Local data of the NN configuration: bridge edge, boundary facts, strict edges. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

namespace Diagram

variable {n : ℕ} (D : Diagram n)

theorem eq_of_residue_eq_of_bounds {a b : ℤ} (h : D.residue a = D.residue b)
    (h1 : b ≤ a) (h2 : a < b + n) : a = b := by
  obtain ⟨k, hk⟩ := D.residue_eq_exists_period h
  have hn : (0 : ℤ) < n := by exact_mod_cast D.area.positive
  rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
  · have : (n : ℤ) * k ≤ -n := by nlinarith
    lia
  · subst hk0; simpa using hk
  · have : (n : ℤ) ≤ n * k := by nlinarith
    lia

theorem edge_eq_of_endpoints {a b : Edge D.area} (ht : a.tail = b.tail) (hh : a.head = b.head) :
    a = b :=
  D.endpointEmbedding.injective (Prod.ext ht hh)

/-- The bridge edge from the tail of `e` to its successor. -/
noncomputable def bridgeEdge (e : Edge D.area) : Edge D.area :=
  if h : D.boundaryNaturalLift (e.tail.val : ℤ) ((e.tail.val : ℤ) + 1) then
    D.edgeFromLift _ _ h else e

section NN

variable (e : Edge D.area) (he : e ∈ D.strict) (hlen : 2 ≤ e.length.val)
  (hgap : D.area.area (D.area.next e.head) < D.area.area e.head)
  (hsame : D.boundary ((e.tail.val : ℤ) + 1) = D.boundary (e.tail.val : ℤ))
  (hleft : ¬ D.strictAt (e.tail.val : ℤ))
  (hright : ¬ D.strictAt ((e.tail.val : ℤ) + 1))

theorem nn_residue_P : D.residue (e.tail.val : ℤ) = e.tail :=
  Orientation.residue_intCast_eq e.tail

theorem nn_residue_P1 : D.residue ((e.tail.val : ℤ) + 1) = D.area.next e.tail := by
  rw [D.residue_succ, nn_residue_P]

theorem nn_residue_T :
    D.residue ((e.tail.val : ℤ) + e.length.val) = e.head :=
  D.residue_add_length e _ (D.nn_residue_P e)

include hlen in
theorem nn_three_le : 3 ≤ n := by
  have := e.length_lt_n
  lia

include he in
theorem nn_boundary_T :
    D.boundary ((e.tail.val : ℤ) + e.length.val) = (e.tail.val : ℤ) := by
  rw [boundary, nn_residue_T, ← (D.strict_corner e he).1]
  ring

include he hgap in
theorem nn_boundary_T1 :
    (e.tail.val : ℤ) + 2 ≤ D.boundary ((e.tail.val : ℤ) + e.length.val + 1) := by
  rw [boundary, D.residue_succ, nn_residue_T]
  have hc := (D.strict_corner e he).1
  have : (D.area.area (D.area.next e.head) : ℤ) + 1 ≤ e.length.val := by
    rw [hc]; exact_mod_cast hgap
  lia

include he hgap in
theorem nn_boundary_ne (w : ℤ) : D.boundary w ≠ (e.tail.val : ℤ) + 1 :=
  D.no_boundary_gap _ _ (D.nn_boundary_T e he) (D.nn_boundary_T1 e he hgap) w

include he hgap in
theorem nn_residue_boundary_ne (w : ℤ) :
    D.residue (D.boundary w) ≠ D.residue ((e.tail.val : ℤ) + 1) := by
  intro h
  obtain ⟨k, hk⟩ := D.residue_eq_exists_period h
  apply D.nn_boundary_ne e he hgap (w + (n : ℤ) * (-k))
  rw [D.boundary_add_period, hk]
  ring

include hsame in
theorem nn_boundary_succ (z : ℤ) (hz : D.residue z = D.residue (e.tail.val : ℤ)) :
    D.boundary (z + 1) = D.boundary z := by
  obtain ⟨k, hk⟩ := D.residue_eq_exists_period hz
  subst hk
  rw [show (e.tail.val : ℤ) + n * k + 1 = ((e.tail.val : ℤ) + 1) + n * k by ring,
    D.boundary_add_period, D.boundary_add_period, hsame]

include hlen in
theorem nn_head_ne_P : e.head ≠ D.residue (e.tail.val : ℤ) := by
  intro h
  rw [← D.nn_residue_T] at h
  have := e.length_lt_n
  have := D.eq_of_residue_eq_of_bounds h (by lia) (by lia)
  lia

include hlen in
theorem nn_head_ne_P1 : e.head ≠ D.residue ((e.tail.val : ℤ) + 1) := by
  intro h
  rw [← D.nn_residue_T] at h
  have := e.length_lt_n
  have := D.eq_of_residue_eq_of_bounds h (by lia) (by lia)
  lia

include he hgap hleft hright in
theorem nn_strict_endpoints (ε : Edge D.area) (hε : ε ∈ D.strict) (hne : ε ≠ e) :
    ε.head ≠ D.residue (e.tail.val : ℤ) ∧ ε.head ≠ D.residue ((e.tail.val : ℤ) + 1) ∧
      ε.tail ≠ D.residue (e.tail.val : ℤ) ∧
        ε.tail ≠ D.residue ((e.tail.val : ℤ) + 1) := by
  have hc := D.strict_corner ε hε
  refine ⟨fun h => hleft ⟨ε, hε, h⟩, fun h => hright ⟨ε, hε, h⟩, ?_, ?_⟩
  · intro ht
    have hrP : D.residue (e.tail.val : ℤ) = ε.tail := ht.symm
    have hhead := D.residue_add_length ε _ hrP
    have hb : D.boundary ((e.tail.val : ℤ) + ε.length.val) = (e.tail.val : ℤ) := by
      rw [boundary, hhead, ← hc.1]; ring
    have hb1 : (e.tail.val : ℤ) + 1 ≤ D.boundary ((e.tail.val : ℤ) + ε.length.val + 1) := by
      rw [boundary, D.residue_succ, hhead]
      have : (D.area.area (D.area.next ε.head) : ℤ) ≤ ε.length.val := by
        rw [hc.1]; exact_mod_cast hc.2
      lia
    have hT := D.nn_boundary_T e he
    have hT1 := D.nn_boundary_T1 e he hgap
    have hlen_eq : (ε.length.val : ℤ) = e.length.val := by
      rcases lt_trichotomy (ε.length.val : ℤ) e.length.val with h | h | h
      · have := D.boundary_monotone
          (show (e.tail.val : ℤ) + ε.length.val + 1 ≤
            (e.tail.val : ℤ) + e.length.val by lia)
        lia
      · exact h
      · have := D.boundary_monotone
          (show (e.tail.val : ℤ) + e.length.val + 1 ≤
            (e.tail.val : ℤ) + ε.length.val by lia)
        lia
    apply hne
    apply D.edge_eq_of_endpoints
    · rw [ht, nn_residue_P]
    · rw [← hhead, hlen_eq, nn_residue_T]
  · intro ht
    have hx := D.nn_residue_P ε
    have hb : D.boundary ((ε.tail.val : ℤ) + ε.length.val) = ε.tail.val := by
      rw [boundary, D.residue_add_length ε _ hx, ← hc.1]; ring
    apply D.nn_residue_boundary_ne e he hgap ((ε.tail.val : ℤ) + ε.length.val)
    rw [hb, hx, ht]

include hsame in
theorem nn_bridge_valid :
    D.boundaryNaturalLift (e.tail.val : ℤ) ((e.tail.val : ℤ) + 1) :=
  ⟨by rw [hsame]; exact D.boundary_le_self _, by lia⟩

include hsame in
theorem nn_bridge_eq : D.bridgeEdge e = D.edgeFromLift _ _ (D.nn_bridge_valid e hsame) := by
  unfold bridgeEdge
  rw [dite_eq_left (D.nn_bridge_valid e hsame)]

include hsame in
theorem nn_bridge_tail : (D.bridgeEdge e).tail = D.residue (e.tail.val : ℤ) := by
  rw [D.nn_bridge_eq e hsame, D.edgeFromLift_tail]

include hsame in
theorem nn_bridge_head : (D.bridgeEdge e).head = D.residue ((e.tail.val : ℤ) + 1) := by
  rw [D.nn_bridge_eq e hsame, D.edgeFromLift_head]

include hsame in
theorem nn_bridge_length : ((D.bridgeEdge e).length.val : ℤ) = 1 := by
  rw [D.nn_bridge_eq e hsame, D.edgeFromLift_length]
  ring

include hsame hright in
theorem nn_bridge_not_strict : D.bridgeEdge e ∉ D.strict := by
  intro h
  exact hright ⟨_, h, D.nn_bridge_head e hsame⟩

include hsame in
theorem nn_eq_bridge (ε : Edge D.area) (ht : ε.tail = D.residue (e.tail.val : ℤ))
    (hl : (ε.length.val : ℤ) = 1) : ε = D.bridgeEdge e := by
  apply D.edge_eq_of_endpoints
  · rw [ht, D.nn_bridge_tail e hsame]
  · rw [D.nn_bridge_head e hsame, ← D.residue_add_length ε _ ht.symm, hl]

theorem nn_fE_tail : (D.shortenedOldEdge e he hlen).tail =
    D.residue ((e.tail.val : ℤ) + 1) := by
  rw [D.shortenedOldEdge_tail, nn_residue_P1]

theorem nn_fE_head : (D.shortenedOldEdge e he hlen).head = e.head := rfl

theorem nn_fE_length : ((D.shortenedOldEdge e he hlen).length.val : ℤ) =
    (e.length.val : ℤ) - 1 := by
  have := D.shortenStrict_edge_length e he hlen
  have h2 : (D.shortenedOldEdge e he hlen).length.val =
    (D.shortenedEdge e he hlen).length.val := rfl
  lia

theorem nn_fE_not_strict : D.shortenedOldEdge e he hlen ∉ D.strict :=
  D.shortened_old_edge_not_strict e he hlen

include hsame in
theorem nn_fE_ne_bridge : D.shortenedOldEdge e he hlen ≠ D.bridgeEdge e := by
  intro h
  have := congrArg Edge.head h
  rw [nn_fE_head, D.nn_bridge_head e hsame] at this
  exact D.nn_head_ne_P1 e hlen this

end NN

end Diagram

end VerticalStripLLT.Circular
