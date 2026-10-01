import VerticalStripLLT.Components.DiagramProof.InitialVertex.Restriction
import Mathlib.SetTheory.Cardinal.Finite

/-! Initial-vertex restriction preserves the number of corner-chain terminals. -/

namespace VerticalStripLLT.Circular.DiagramProof

noncomputable section

namespace CornerFamily

variable {k : ℕ} {D : Diagram (k + 2)}

/-- Fixed chain terminals are carried bijectively by the successor embedding. -/
def initialVertex_fixedTerminalEquiv (F : CornerFamily D) (hD : Forward D)
    (f : Edge D.area) (hf : f ∈ F.edges) (hft : f.tail = 0) :
    {u : Fin (k + 1) //
      (F.induced hD (Fin.succOrderEmb (k + 1))).terminal
        (inducedDiagram_forward hD (Fin.succOrderEmb (k + 1))) u = u} ≃
      {v : Fin (k + 2) // F.terminal hD v = v} := by
  let G := F.induced hD (Fin.succOrderEmb (k + 1))
  let hE := inducedDiagram_forward hD (Fin.succOrderEmb (k + 1))
  let map : {u : Fin (k + 1) // G.terminal hE u = u} →
      {v : Fin (k + 2) // F.terminal hD v = v} := fun u =>
    ⟨u.val.succ, by
      rw [← F.initialVertex_terminal hD u.val]
      exact congrArg Fin.succ u.property⟩
  apply Equiv.ofBijective map
  constructor
  · rintro ⟨u, hu⟩ ⟨v, hv⟩ huv
    apply Subtype.ext
    exact Fin.succ_inj.mp (congrArg Subtype.val huv)
  · rintro ⟨v, hv⟩
    have hstep : F.step 0 f.head := (F.step_iff _ _).mpr ⟨f, hf, hft, rfl⟩
    have hpos : 0 < F.terminal hD 0 := by
      rw [F.terminal_eq_of_step hD hstep]
      have hfpos : 0 < f.head := by simpa only [hft] using hD f
      exact hfpos.trans_le (F.le_terminal hD f.head)
    have hvzero : v ≠ 0 := by
      intro hz
      rw [hz] at hv
      exact hpos.ne' hv
    obtain ⟨u, hu⟩ := Fin.eq_succ_of_ne_zero hvzero
    refine ⟨⟨u, ?_⟩, ?_⟩
    · apply Fin.succ_inj.mp
      rw [F.initialVertex_terminal hD u]
      simpa only [hu] using hv
    · apply Subtype.ext
      exact hu.symm

/-- Deleting the initial vertex, the tail of a retained corner, keeps the number of
corner-chain terminals. -/
theorem initialVertex_fixedTerminal_card (F : CornerFamily D) (hD : Forward D)
    (f : Edge D.area) (hf : f ∈ F.edges) (hft : f.tail = 0) :
    Nat.card {u : Fin (k + 1) //
      (F.induced hD (Fin.succOrderEmb (k + 1))).terminal
        (inducedDiagram_forward hD (Fin.succOrderEmb (k + 1))) u = u} =
      Nat.card {v : Fin (k + 2) // F.terminal hD v = v} :=
  Nat.card_congr (F.initialVertex_fixedTerminalEquiv hD f hf hft)

end CornerFamily

end

end VerticalStripLLT.Circular.DiagramProof
