import VerticalStripLLT.Components.DiagramProof.CornerChains

/-! Transporting corner-chain terminals through a closed induced vertex set. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {k n : ℕ} {E : Diagram k} {D : Diagram n}

namespace CornerFamily

theorem induced_terminal_eq (F : CornerFamily D) (G : CornerFamily E)
    (hD : Forward D) (hE : Forward E) (ι : Fin k ↪o Fin n)
    (hstep : ∀ u v, G.step u v ↔ F.step (ι u) (ι v))
    (hclosed : ∀ u v, F.step (ι u) v → ∃ w, ι w = v)
    (u : Fin k) :
    ι (G.terminal hE u) = F.terminal hD (ι u) := by
  have hpath : Relation.ReflTransGen F.step (ι u) (ι (G.terminal hE u)) :=
    (G.reachable_terminal hE u).lift ι (fun x y hxy => (hstep x y).mp hxy)
  have hsink : ∀ v, ¬ F.step (ι (G.terminal hE u)) v := by
    intro v htv
    obtain ⟨w, hw⟩ := hclosed (G.terminal hE u) v htv
    have htw : G.step (G.terminal hE u) w :=
      (hstep _ _).mpr (by simpa only [hw] using htv)
    exact G.terminal_sink hE u w htw
  have hterminal : ι (G.terminal hE u) = F.terminal hD (ι (G.terminal hE u)) := by
    by_contra hne
    obtain ⟨v, htv⟩ := F.exists_successor hD hne
    exact hsink v htv
  exact hterminal.trans (F.terminal_eq_of_reachable hD hpath).symm

end CornerFamily

end VerticalStripLLT.Circular.DiagramProof
