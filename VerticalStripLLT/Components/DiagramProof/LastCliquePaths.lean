import VerticalStripLLT.Components.DiagramProof.PathRestriction

/-! Restricting forward paths to a prefix together with the final vertex. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {k n : ℕ} {R : Fin k → Fin k → Prop} {S : Fin n → Fin n → Prop}

/-- The image consisting of a prefix together with one final vertex is path-closed
when no vertex in the omitted gap has a selected edge to that final vertex. -/
theorem pathImage_closed_of_last_gap (ι : Fin k ↪o Fin n) (c e : Fin n)
    (himage : ∀ z, (∃ w, ι w = z) ↔ z ≤ c ∨ z = e)
    (hforward : ∀ ⦃x y⦄, S x y → x < y)
    (hno : ∀ x, c < x → x < e → ¬ S x e)
    (u v : Fin k) (z : Fin n) :
    Relation.ReflTransGen S (ι u) z → Relation.ReflTransGen S z (ι v) →
      ∃ w, ι w = z := by
  intro _ hzv
  rcases (himage (ι v)).mp ⟨v, rfl⟩ with hv | hv
  · apply (himage z).mpr
    left
    exact (reachable_le hforward hzv).trans hv
  · rw [hv] at hzv
    rcases hzv.cases_tail with hze | ⟨y, hzy, hye⟩
    · exact (himage z).mpr (Or.inr hze.symm)
    · by_cases hcy : c < y
      · exact (hno y hcy (hforward hye) hye).elim
      · apply (himage z).mpr
        left
        exact (reachable_le hforward hzy).trans (le_of_not_gt hcy)

/-- Forward reachability between vertices of a last-gap core is exactly its induced
reachability, provided the core image is the prefix plus the final vertex. -/
theorem reachable_iff_of_last_gap (ι : Fin k ↪o Fin n) (c e : Fin n)
    (himage : ∀ z, (∃ w, ι w = z) ↔ z ≤ c ∨ z = e)
    (hforward : ∀ ⦃x y⦄, S x y → x < y)
    (hno : ∀ x, c < x → x < e → ¬ S x e)
    (hrel : ∀ u v, R u v ↔ S (ι u) (ι v)) (u v : Fin k) :
    Relation.ReflTransGen S (ι u) (ι v) ↔ Relation.ReflTransGen R u v := by
  apply reachable_iff_of_pathImage ι
  · exact pathImage_closed_of_last_gap ι c e himage hforward hno
  · exact hrel

/-- Cover tests between vertices of a last-gap core are exactly the induced cover tests. -/
theorem relationCover_iff_of_last_gap (ι : Fin k ↪o Fin n) (c e : Fin n)
    (himage : ∀ z, (∃ w, ι w = z) ↔ z ≤ c ∨ z = e)
    (hforward : ∀ ⦃x y⦄, S x y → x < y)
    (hno : ∀ x, c < x → x < e → ¬ S x e)
    (hrel : ∀ u v, R u v ↔ S (ι u) (ι v)) (u v : Fin k) :
    RelationCover S (ι u) (ι v) ↔ RelationCover R u v := by
  apply relationCover_iff_of_pathImage ι
  · exact pathImage_closed_of_last_gap ι c e himage hforward hno
  · exact hrel

end VerticalStripLLT.Circular.DiagramProof
