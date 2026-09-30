import Mathlib.Logic.Relation

/-! Transport of weak components when only an image block is replaced. -/

namespace VerticalStripLLT.Circular.DiagramProof

theorem eqvGen_iff_of_block_replacement
    {V W : Type*} (ι : V → W) (R S : W → W → Prop)
    (hR : ∀ u v, Relation.EqvGen R (ι u) (ι v))
    (hS : ∀ u v, Relation.EqvGen S (ι u) (ι v))
    (hout : ∀ x y, (¬ ∃ u v, ι u = x ∧ ι v = y) → (R x y ↔ S x y))
    (x y : W) :
    Relation.EqvGen R x y ↔ Relation.EqvGen S x y := by
  have hRS : ∀ {x y}, R x y → Relation.EqvGen S x y := by
    intro x y hxy
    by_cases him : ∃ u v, ι u = x ∧ ι v = y
    · obtain ⟨u, v, hu, hv⟩ := him
      simpa only [hu, hv] using hS u v
    · exact Relation.EqvGen.rel _ _ ((hout x y him).mp hxy)
  have hSR : ∀ {x y}, S x y → Relation.EqvGen R x y := by
    intro x y hxy
    by_cases him : ∃ u v, ι u = x ∧ ι v = y
    · obtain ⟨u, v, hu, hv⟩ := him
      simpa only [hu, hv] using hR u v
    · exact Relation.EqvGen.rel _ _ ((hout x y him).mpr hxy)
  constructor
  · intro h
    exact Relation.EqvGen.eqvGen_le (fun a b hxy => hRS (x := a) (y := b) hxy) x y h
  · intro h
    exact Relation.EqvGen.eqvGen_le (fun a b hxy => hSR (x := a) (y := b) hxy) x y h

end VerticalStripLLT.Circular.DiagramProof
