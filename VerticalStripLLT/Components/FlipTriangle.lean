import VerticalStripLLT.Circular.Flip
import VerticalStripLLT.Circular.HRVPotential

/-! The retained long edge and length identities of an actual circular flip. -/

namespace VerticalStripLLT.Circular.DirectedFlipWitness

open Classical

variable {n : ℕ} {D : Diagram n} {θ η : Orientation D}

/-- The selected edge realizing the source's long lifted cover. -/
noncomputable def longEdge (w : DirectedFlipWitness D θ η) : Edge D.area :=
  (D.liftCover_liftStep w.source_ac).choose

theorem longEdge_mem (w : DirectedFlipWitness D θ η) :
    w.longEdge ∈ D.strict ∪ θ.val :=
  (D.liftCover_liftStep w.source_ac).choose_spec.1

theorem longEdge_lift (w : DirectedFlipWitness D θ η) :
    D.naturalLift w.longEdge w.a w.c :=
  (D.liftCover_liftStep w.source_ac).choose_spec.2

theorem longEdge_target_mem (w : DirectedFlipWitness D θ η) :
    w.longEdge ∈ D.strict ∪ η.val :=
  D.mem_selected_of_naturalLift_of_liftCover w.longEdge_lift w.target_ac

theorem longEdge_tail (w : DirectedFlipWitness D θ η) :
    w.eab.tail = w.longEdge.tail := w.ab_lift.1.symm.trans w.longEdge_lift.1

theorem short_head_tail (w : DirectedFlipWitness D θ η) :
    w.eab.head = w.ebc.tail := by
  have hb : D.residue w.b = w.eab.head := by
    rw [w.ab_lift.2]
    exact D.residue_add_length w.eab w.a w.ab_lift.1
  exact hb.symm.trans w.bc_lift.1

theorem longEdge_head (w : DirectedFlipWitness D θ η) :
    w.ebc.head = w.longEdge.head := by
  have hc : D.residue w.c = w.ebc.head := by
    rw [w.bc_lift.2]
    exact D.residue_add_length w.ebc w.b w.bc_lift.1
  have hc' : D.residue w.c = w.longEdge.head := by
    rw [w.longEdge_lift.2]
    exact D.residue_add_length w.longEdge w.a w.longEdge_lift.1
  exact hc.symm.trans hc'

theorem longEdge_length (w : DirectedFlipWitness D θ η) :
    (w.longEdge.length.val : ℤ) = w.eab.length.val + w.ebc.length.val := by
  have hab := w.ab_lift.2
  have hbc := w.bc_lift.2
  have hac := w.longEdge_lift.2
  lia

theorem longEdge_ne_ab (w : DirectedFlipWitness D θ η) : w.longEdge ≠ w.eab := by
  intro heq
  have hab := w.ab_lift.2
  have hac := w.longEdge_lift.2
  rw [heq] at hac
  have hbc := w.cyclicWindow.2.1
  lia

theorem longEdge_ne_bc (w : DirectedFlipWitness D θ η) : w.longEdge ≠ w.ebc := by
  intro heq
  have hbc := w.bc_lift.2
  have hac := w.longEdge_lift.2
  rw [heq] at hac
  have hab := w.cyclicWindow.1
  lia

/-- The swap also has the expected form on full selected sets, including strict edges. -/
theorem full_target_eq_source_swap (w : DirectedFlipWitness D θ η) :
    D.strict ∪ η.val = insert w.ebc ((D.strict ∪ θ.val).erase w.eab) := by
  have hab : w.eab ∉ D.strict := (Finset.mem_sdiff.mp w.eab_normal).2
  rw [w.target_eq_source_swap]
  ext e
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
  grind

end VerticalStripLLT.Circular.DirectedFlipWitness
