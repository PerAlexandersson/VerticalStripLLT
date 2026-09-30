import VerticalStripLLT.Components.DiagramProof.InducedRestriction
import VerticalStripLLT.Components.DiagramProof.LastCliquePaths

/-! Lifting core paths after the exterior edges into the final vertex have been swept. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {k n : ℕ} {E : Diagram k} {D : Diagram n}
  (hE : Forward E) (hD : Forward D) (ι : Fin k ↪o Fin n)
  (hnatural : ∀ u v,
    (∃ f : Edge E.area, f.tail = u ∧ f.head = v) ↔
      ∃ f : Edge D.area, f.tail = ι u ∧ f.head = ι v)
  (hstrict : ∀ u v,
    (∃ f ∈ E.strict, f.tail = u ∧ f.head = v) ↔
      ∃ f ∈ D.strict, f.tail = ι u ∧ f.head = ι v)

/-- Changing only the core cannot introduce an edge from an omitted vertex into `e`.
Consequently all core cover tests agree, including those at intermediate states. -/
theorem inducedExtend_cover_iff_of_last_gap (θ : Orientation D) (c e : Fin n)
    (himage : ∀ z, (∃ w, ι w = z) ↔ z ≤ c ∨ z = e)
    (hno : ∀ x, c < x → x < e → ¬ D.edgeData.selected θ.val x e)
    (α : Orientation E) (u v : Fin k) :
    Cover (inducedExtend hD ι hnatural hstrict θ α) (ι u) (ι v) ↔ Cover α u v := by
  apply relationCover_iff_of_last_gap ι c e himage
    (fun {_ _} h => (inducedExtend hD ι hnatural hstrict θ α).selected_lt_of_forward hD h)
  · intro x hcx hxe hsel
    have hout : ¬ ∃ a b, ι a = x ∧ ι b = e := by
      rintro ⟨a, _, ha, _⟩
      rcases (himage x).mp ⟨a, ha⟩ with hxc | hxeq
      · exact (not_le_of_gt hcx) hxc
      · exact hxe.ne hxeq
    exact hno x hcx hxe
      ((inducedExtend_outside hD ι hnatural hstrict θ α x e hout).mp hsel)
  · intro a b
    exact (inducedExtend_inside hD ι hnatural hstrict θ α a b).symm

/-- The swept exterior stays fixed along any actual core path. The induced natural
and strict edge correspondences are explicit hypotheses, not conclusions. -/
theorem induced_lift_reachable_of_last_gap (θ : Orientation D) (c e : Fin n)
    (himage : ∀ z, (∃ w, ι w = z) ↔ z ≤ c ∨ z = e)
    (hno : ∀ x, c < x → x < e → ¬ D.edgeData.selected θ.val x e)
    {α : Orientation E}
    (hp : Relation.ReflTransGen (Flip E) (inducedRestrict hE ι hnatural hstrict θ) α) :
    Relation.ReflTransGen (Flip D) θ (inducedExtend hD ι hnatural hstrict θ α) :=
  induced_lift_reachable hE hD ι hnatural hstrict θ
    (inducedExtend_cover_iff_of_last_gap hD ι hnatural hstrict θ c e himage hno) hp

end VerticalStripLLT.Circular.DiagramProof
