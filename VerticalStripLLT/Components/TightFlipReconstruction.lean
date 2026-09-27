import VerticalStripLLT.Components.FlipTriangle
import VerticalStripLLT.Components.CircularTightPaths

/-! Reconstructing actual circular flips from tight selected subgraphs. -/

namespace VerticalStripLLT.Circular.DirectedFlipWitness

open Classical

variable {n : ℕ} {D : Diagram n} {θ η : Orientation D}

/-- Transfer every full integer cover test, including the two excluded covers. -/
def of_tightSelections (w : DirectedFlipWitness D θ η)
    (α β : Orientation D) (hθα : θ.val ⊆ α.val) (hηβ : η.val ⊆ β.val)
    (hswap : β.val = insert w.ebc (α.val.erase w.eab))
    (M : ℤ) (z : Fin n → ℤ)
    (hweakα : ∀ e ∈ D.strict ∪ α.val,
      M * (e.length.val : ℤ) ≤ z e.head - z e.tail)
    (hweakβ : ∀ e ∈ D.strict ∪ β.val,
      M * (e.length.val : ℤ) ≤ z e.head - z e.tail)
    (htightα : ∀ e ∈ D.strict ∪ α.val,
      z e.head - z e.tail = M * (e.length.val : ℤ) → e ∈ D.strict ∪ θ.val)
    (htightβ : ∀ e ∈ D.strict ∪ β.val,
      z e.head - z e.tail = M * (e.length.val : ℤ) → e ∈ D.strict ∪ η.val)
    (heqθ : ∀ e ∈ D.strict ∪ θ.val,
      z e.head - z e.tail = M * (e.length.val : ℤ)) : DirectedFlipWitness D α β := by
  have hab := D.liftScore_eq_of_naturalLift w.ab_lift
    (heqθ w.eab (Finset.mem_union_right _ w.source_ab_mem))
  have hac := D.liftScore_eq_of_naturalLift w.longEdge_lift (heqθ _ w.longEdge_mem)
  have hbc := hab.symm.trans hac
  refine {
    a := w.a, b := w.b, c := w.c
    cyclicWindow := w.cyclicWindow
    eab := w.eab, ebc := w.ebc
    eab_normal := w.eab_normal, ebc_normal := w.ebc_normal
    ab_lift := w.ab_lift, bc_lift := w.bc_lift
    source_ab := (D.liftCover_tight_iff hθα hweakα htightα hab).mpr w.source_ab
    source_ac := (D.liftCover_tight_iff hθα hweakα htightα hac).mpr w.source_ac
    source_not_bc := fun h =>
      w.source_not_bc ((D.liftCover_tight_iff hθα hweakα htightα hbc).mp h)
    target_ac := (D.liftCover_tight_iff hηβ hweakβ htightβ hac).mpr w.target_ac
    target_bc := (D.liftCover_tight_iff hηβ hweakβ htightβ hbc).mpr w.target_bc
    target_not_ab := fun h =>
      w.target_not_ab ((D.liftCover_tight_iff hηβ hweakβ htightβ hab).mp h)
    agree_elsewhere := ?_
  }
  intro e hab hbc
  rw [hswap]
  simp [hab, hbc]

end VerticalStripLLT.Circular.DirectedFlipWitness
