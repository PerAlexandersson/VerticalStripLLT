import VerticalStripLLT.Components.DiagramProof.InitialVertexCounts

/-! The finite initial-row extras and their count decomposition. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

open Classical

noncomputable section

variable {k : ℕ} {D : Diagram (k + 2)}

def initialVertexExtras (F : CornerFamily D) (hD : Forward D) (f : Edge D.area) :
    Finset (Edge D.area) :=
  (F.goodEdges hD).filter (fun e => e.tail = 0 ∧ e ≠ f)

def selectedInitialVertexExtras (θ : Orientation D) (f : Edge D.area) :
    Finset (Edge D.area) :=
  ((fullSelection θ).filter (fun e => e.tail = 0)).erase f

theorem row_eq_insert_selectedInitialVertexExtras
    (F : CornerFamily D) (hD : Forward D) (θ : Orientation D)
    (hθ : F.Anchor hD θ) (f : Edge D.area) (hf : f ∈ F.edges)
    (hft : f.tail = 0) :
    (fullSelection θ).filter (fun e => e.tail = 0) =
      insert f (selectedInitialVertexExtras θ f) := by
  have hfm : f ∈ (fullSelection θ).filter (fun e => e.tail = 0) :=
    Finset.mem_filter.mpr ⟨hθ.1 hf, hft⟩
  exact (Finset.insert_erase hfm).symm

theorem selectedInitialVertexExtras_subset
    (F : CornerFamily D) (hD : Forward D) (θ : Orientation D)
    (hθ : F.Anchor hD θ) (f : Edge D.area) :
    selectedInitialVertexExtras θ f ⊆ F.initialVertexExtras hD f := by
  intro e he
  have he' := Finset.mem_erase.mp he
  have hsel := Finset.mem_filter.mp he'.2
  apply Finset.mem_filter.mpr
  exact ⟨(F.mem_goodEdges hD e).mpr (hθ.2 e hsel.1), hsel.2, he'.1⟩

theorem totalSelected_eq_initialVertex_core_add_one_add_extras
    (F : CornerFamily D) (hD : Forward D) (θ : Orientation D)
    (hθ : F.Anchor hD θ) (f : Edge D.area) (hf : f ∈ F.edges)
    (hft : f.tail = 0) :
    totalSelected θ = totalSelected (initialVertexRestrict hD θ) + 1 +
      (selectedInitialVertexExtras θ f).card := by
  have htotal := initialVertex_totalSelected hD θ
  have hfm : f ∈ (fullSelection θ).filter (fun e => e.tail = 0) :=
    Finset.mem_filter.mpr ⟨hθ.1 hf, hft⟩
  have hcard := Finset.card_erase_add_one hfm
  unfold selectedInitialVertexExtras
  lia

end

end VerticalStripLLT.Circular.DiagramProof.CornerFamily
