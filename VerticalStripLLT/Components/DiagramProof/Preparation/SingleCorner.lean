import VerticalStripLLT.Components.DiagramProof.Preparation.Preparation
import VerticalStripLLT.Components.DiagramProof.Relations.FiniteCoverPaths

/-!
# A single retained corner

For a corner family with one retained edge, the corner-chain terminal map is
explicit.  This is the interface used when the complete diagram has only its
extreme maximal corner retained.
-/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

namespace CornerFamily

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hforward : Forward D)

/-- A vertex other than the tail of the sole retained corner is a chain sink. -/
theorem terminal_eq_self_of_singleton {e : Edge D.area} {z : Fin n}
    (hedges : F.edges = {e}) (hetail : e.tail = z) (v : Fin n) (hv : v ≠ z) :
    F.terminal hforward v = v := by
  have hsink : ∀ w, ¬ F.step v w := by
    intro w hvw
    obtain ⟨f, hf, hfv, hfw⟩ := (F.step_iff v w).mp hvw
    rw [hedges] at hf
    have hfe : f = e := Finset.mem_singleton.mp hf
    have htail : e.tail = v := hfe ▸ hfv
    exact hv (htail.symm.trans hetail)
  exact reachable_eq_of_sink hsink (F.reachable_terminal hforward v)

/-- The sole retained corner has the terminal at its head. -/
theorem terminal_eq_head_of_singleton {e : Edge D.area} {z t : Fin n}
    (hedges : F.edges = {e}) (hetail : e.tail = z) (head : e.head = t)
    (htop : ∀ v, v ≤ t) :
    F.terminal hforward z = t := by
  have he_mem : e ∈ F.edges := by
    rw [hedges]
    simp
  have hstep : F.step z t := (F.step_iff z t).mpr ⟨e, he_mem, hetail, head⟩
  have hterminal_t : F.terminal hforward t = t :=
    le_antisymm (htop _) (F.le_terminal hforward t)
  exact (F.terminal_eq_of_step hforward hstep).trans hterminal_t

/-- In an anchor, the sole retained corner is the only selected edge out of its tail. -/
theorem anchor_selected_iff_of_singleton {e : Edge D.area} {z t : Fin n}
    (hedges : F.edges = {e}) (hetail : e.tail = z) (head : e.head = t)
    (htop : ∀ v, v ≤ t) {θ : Orientation D} (hθ : F.Anchor hforward θ)
    (v : Fin n) :
    D.edgeData.selected θ.val z v ↔ v = t := by
  have hterminal_z : F.terminal hforward z = t :=
    F.terminal_eq_head_of_singleton hforward hedges hetail head htop
  have he_mem : e ∈ F.edges := by
    rw [hedges]
    simp
  constructor
  · intro hselected
    obtain ⟨f, hf, hfv, hfw⟩ := hselected
    rcases hθ.2 f hf with hfe | hgood
    · rw [hedges] at hfe
      have hfe' : f = e := Finset.mem_singleton.mp hfe
      have hhead : e.head = v := hfe' ▸ hfw
      exact hhead.symm.trans head
    · have hlt : F.terminal hforward f.tail < F.terminal hforward f.head := hgood
      have htail : f.tail = z := hfv
      have hhead : f.head = v := hfw
      rw [htail, hhead, hterminal_z] at hlt
      exact ((not_lt_of_ge (htop _)) hlt).elim
  · intro hv
    subst v
    have hselected : e ∈ fullSelection θ := hθ.1 he_mem
    have := (mem_fullSelection_iff_selected θ e).mp hselected
    simpa [hetail, head] using this

/-- A common-cover state reaches an anchor with the singleton-corner endpoint property. -/
theorem exists_preparation_of_singleton {e : Edge D.area} {z t : Fin n}
    (hedges : F.edges = {e}) (hetail : e.tail = z) (head : e.head = t)
    (htop : ∀ v, v ≤ t) (θ : Orientation D) (hC : F.CommonCover θ) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧
      F.Anchor hforward η ∧
      (∀ v, D.edgeData.selected η.val z v ↔ v = t) := by
  obtain ⟨η, hpath, hanchor, _⟩ := F.exists_preparation hforward θ hC
  exact ⟨η, hpath, hanchor,
    F.anchor_selected_iff_of_singleton hforward hedges hetail head htop hanchor⟩

end CornerFamily

end

end VerticalStripLLT.Circular.DiagramProof
