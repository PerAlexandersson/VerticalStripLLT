import VerticalStripLLT.Circular.CornerPairs
import VerticalStripLLT.Circular.StrictEdgeInjectivity
import VerticalStripLLT.Circular.FirstBounceOrientationData

/-! Removing the first strict corner exposes NN boundary geometry in a DN move. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ} (D : Diagram n)

theorem deleteCorner_boundary (e : Edge D.area) (he : IsCorner e) (z : ℤ) :
    (D.deleteCorner e he).boundary z =
      D.boundary z + if D.residue z = e.head then 1 else 0 := by
  have hp := corner_area_pos he
  change z - (Function.update D.area.area e.head (D.area.area e.head - 1)
      (D.residue z) : ℤ) = _
  by_cases hz : D.residue z = e.head
  · rw [ite_eq_left hz, hz, Function.update_self, boundary, hz]
    lia
  · rw [Function.update_of_ne hz, ite_eq_right hz, boundary]
    ring

theorem deleteStrictCorner_not_strictAt (e : Edge D.area) (he : e ∈ D.strict)
    (z : ℤ) (hz : D.residue z = e.head) :
    ¬ (D.deleteCorner e (D.strict_corner e he)).strictAt z := by
  rintro ⟨f, hf, hh⟩
  have hf' := (D.mem_deleteCorner_strict e (D.strict_corner e he) f).mp hf
  have hh' : (D.cornerIncl e (D.strict_corner e he) f).head = e.head := hh.trans hz
  exact D.cornerIncl_ne e (D.strict_corner e he) f (D.strict_edge_eq_of_head_eq hf' he hh')

theorem deleteCorner_not_strictAt (e : Edge D.area) (he : IsCorner e) (z : ℤ)
    (h : ¬ D.strictAt z) : ¬ (D.deleteCorner e he).strictAt z := by
  rintro ⟨f, hf, hh⟩
  exact h ⟨D.cornerIncl e he f, (D.mem_deleteCorner_strict e he f).mp hf, hh⟩

theorem deleteStrictCorner_surviving_gap (e f : Edge D.area)
    (he : e ∈ D.strict) (hf : f ∈ D.strict) (hne : f ≠ e)
    (hgap : D.area.area (D.area.next f.head) < D.area.area f.head) :
    (D.deleteCorner e (D.strict_corner e he)).area.area (D.area.next f.head) <
      (D.deleteCorner e (D.strict_corner e he)).area.area f.head := by
  have hh : f.head ≠ e.head := fun h => hne (D.strict_edge_eq_of_head_eq hf he h)
  change (D.area.lowerAt e.head (corner_area_pos (D.strict_corner e he))
      (D.strict_corner e he).2).area (D.area.next f.head) <
    (D.area.lowerAt e.head (corner_area_pos (D.strict_corner e he))
      (D.strict_corner e he).2).area f.head
  rw [CircularArea.lowerAt_area_of_ne _ _ _ _ hh]
  exact (CircularArea.lowerAt_area_le _ _ _ _ _).trans_lt hgap

theorem dn_deleted_boundary_same (e f : Edge D.area) (he : e ∈ D.strict)
    (hcontact : f.tail = e.head) (hlen : 2 ≤ f.length.val)
    (heq : D.area.area (D.area.next e.head) = D.area.area e.head) :
    (D.deleteCorner e (D.strict_corner e he)).boundary ((f.tail.val : ℤ) + 1) =
      (D.deleteCorner e (D.strict_corner e he)).boundary (f.tail.val : ℤ) := by
  have hn : 2 ≤ n := by have := f.length_lt_n; lia
  have hr : D.residue (f.tail.val : ℤ) = e.head :=
    (Orientation.residue_intCast_eq f.tail).trans hcontact
  have hr1 : D.residue ((f.tail.val : ℤ) + 1) = D.area.next e.head := by
    rw [D.residue_succ, hr]
  have hne : D.residue ((f.tail.val : ℤ) + 1) ≠ e.head := by
    rw [← hr]
    exact (D.residue_p_ne_succ hn _).symm
  rw [D.deleteCorner_boundary, D.deleteCorner_boundary, ite_eq_right hne,
    ite_eq_left hr, boundary, boundary, hr1, hr, heq]
  ring

end VerticalStripLLT.Circular.Diagram
