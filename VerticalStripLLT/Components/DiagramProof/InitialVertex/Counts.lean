import VerticalStripLLT.Components.DiagramProof.InitialVertex.Restriction
import VerticalStripLLT.Components.DiagramProof.Restriction.InducedCounts

/-! Separating the selected core edges from the selected edges at the initial vertex. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

variable {k : ℕ} {D : Diagram (k + 2)}

/-- The only natural edges lost on deletion of zero are those starting at zero. -/
theorem initialVertex_edge_retained_iff (hD : Forward D) (e : Edge D.area) :
    (∃ u v : Fin (k + 1), u.succ = e.tail ∧ v.succ = e.head) ↔ e.tail ≠ 0 := by
  constructor
  · rintro ⟨u, v, hu, _⟩
    exact hu ▸ Fin.succ_ne_zero u
  · intro ht
    have hh : e.head ≠ 0 := ne_of_gt ((Fin.pos_iff_ne_zero.mpr ht).trans (hD e))
    obtain ⟨u, hu⟩ := Fin.eq_succ_of_ne_zero ht
    obtain ⟨v, hv⟩ := Fin.eq_succ_of_ne_zero hh
    exact ⟨u, v, hu.symm, hv.symm⟩

/-- Exactly the corner starting at zero is lost among the ambient corners. -/
theorem initialVertex_corner_retained_iff (hD : Forward D) (f : Edge D.area)
    (hf : IsCorner f) (hft : f.tail = 0) (e : Edge D.area) (he : IsCorner e) :
    (∃ u v : Fin (k + 1), u.succ = e.tail ∧ v.succ = e.head) ↔ e ≠ f := by
  rw [initialVertex_edge_retained_iff hD]
  constructor
  · intro ht hef
    exact ht (hef ▸ hft)
  · intro hne ht
    apply hne
    have htail : e.tail = f.tail := ht.trans hft.symm
    apply D.endpointEmbedding.injective
    apply Prod.ext htail
    exact le_antisymm (((isCorner_iff_extremal hD f).mp hf).2 e htail)
      (((isCorner_iff_extremal hD e).mp he).2 f htail.symm)

theorem initialVertex_totalSelected (hD : Forward D) (θ : Orientation D) :
    totalSelected θ = totalSelected (initialVertexRestrict hD θ) +
      ((fullSelection θ).filter (fun e => e.tail = 0)).card := by
  have h := totalSelected_eq_inducedRestrict_add_outside hD (Fin.succOrderEmb (k + 1)) θ
  have hout : ((fullSelection θ).filter (fun e : Edge D.area =>
      ¬ ∃ u v, (Fin.succOrderEmb (k + 1)) u = e.tail ∧
        (Fin.succOrderEmb (k + 1)) v = e.head)) =
      (fullSelection θ).filter (fun e => e.tail = 0) := by
    ext e
    simp only [Finset.mem_filter, Fin.coe_succOrderEmb,
      initialVertex_edge_retained_iff hD, not_not]
  rw [hout] at h
  exact h

/-- Identical initial rows and total counts give identical core counts. -/
theorem initialVertex_core_count_eq (hD : Forward D) (θ τ : Orientation D)
    (htotal : totalSelected θ = totalSelected τ)
    (hrow : ∀ v, D.edgeData.selected θ.val 0 v ↔ D.edgeData.selected τ.val 0 v) :
    totalSelected (initialVertexRestrict hD θ) = totalSelected (initialVertexRestrict hD τ) := by
  have hout : (fullSelection θ).filter (fun e => e.tail = 0) =
      (fullSelection τ).filter (fun e => e.tail = 0) := by
    ext e
    simp only [Finset.mem_filter]
    by_cases he : e.tail = 0
    · simp only [he, and_true, mem_fullSelection_iff_selected, hrow]
    · simp only [he, and_false]
  have hθ := initialVertex_totalSelected hD θ
  have hτ := initialVertex_totalSelected hD τ
  rw [hout] at hθ
  lia

end VerticalStripLLT.Circular.DiagramProof
