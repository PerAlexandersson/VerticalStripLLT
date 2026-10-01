import VerticalStripLLT.Components.DiagramProof.Relations.RelationPaths
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Hom.Basic

/-! Restriction of paths and covers to images closed under ambient paths. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {V W : Type*} [LinearOrder V] [LinearOrder W]
  {R : V → V → Prop} {S : W → W → Prop}

/-- An ambient path with endpoints in a path-closed image restricts to a core path. -/
theorem reachable_iff_of_pathImage (ι : V ↪o W)
    (hclosed : ∀ u v z, Relation.ReflTransGen S (ι u) z →
      Relation.ReflTransGen S z (ι v) → ∃ w, ι w = z)
    (hrel : ∀ u v, R u v ↔ S (ι u) (ι v)) (u v : V) :
    Relation.ReflTransGen S (ι u) (ι v) ↔ Relation.ReflTransGen R u v := by
  constructor
  · intro h
    have restrict {x : W} (hp : Relation.ReflTransGen S x (ι v)) :
        ∀ w, x = ι w → Relation.ReflTransGen R w v := by
      induction hp using Relation.ReflTransGen.head_induction_on with
      | refl =>
        intro w hw
        have hweq : w = v := ι.injective hw.symm
        subst w
        exact Relation.ReflTransGen.refl
      | @head x y hxy hyv ih =>
        intro w hw
        obtain ⟨z, hz⟩ := hclosed w v y
          (by simpa only [← hw] using Relation.ReflTransGen.single hxy) hyv
        apply (ih z hz.symm).head
        apply (hrel w z).mpr
        simpa only [← hw, hz] using hxy
    exact restrict h u rfl
  · intro h
    exact h.lift ι (fun u v hs => (hrel u v).mp hs)

/-- Path-closed image restriction preserves the full reachability-cover test. -/
theorem relationCover_iff_of_pathImage (ι : V ↪o W)
    (hclosed : ∀ u v z, Relation.ReflTransGen S (ι u) z →
      Relation.ReflTransGen S z (ι v) → ∃ w, ι w = z)
    (hrel : ∀ u v, R u v ↔ S (ι u) (ι v)) (u v : V) :
    RelationCover S (ι u) (ι v) ↔ RelationCover R u v := by
  have paths := reachable_iff_of_pathImage ι hclosed hrel
  constructor
  · rintro ⟨hlt, hreach, hcover⟩
    refine ⟨ι.lt_iff_lt.mp hlt, (paths u v).mp hreach, ?_⟩
    intro w huw hwv hw
    exact hcover (ι w) (ι.strictMono huw) (ι.strictMono hwv)
      ⟨(paths u w).mpr hw.1, (paths w v).mpr hw.2⟩
  · rintro ⟨hlt, hreach, hcover⟩
    refine ⟨ι.strictMono hlt, (paths u v).mpr hreach, ?_⟩
    intro z huz hzv hz
    obtain ⟨w, rfl⟩ := hclosed u v z hz.1 hz.2
    exact hcover w (ι.lt_iff_lt.mp huz) (ι.lt_iff_lt.mp hzv)
      ⟨(paths u w).mp hz.1, (paths w v).mp hz.2⟩

/-- The image `{0} ∪ [a,b]` is path-closed when the zero row has no head below `a`. -/
theorem pathImage_closed_of_zero_interval
    {N : ℕ} {S : Fin (N + 1) → Fin (N + 1) → Prop} (ι : V ↪o Fin (N + 1))
    {a b : ℕ}
    (himage : ∀ z, (∃ w, ι w = z) ↔ z = 0 ∨ a ≤ z.val ∧ z.val ≤ b)
    (hforward : ∀ ⦃x y⦄, S x y → x < y) (ha : 0 < a) (_hab : a ≤ b)
    (hzero : ∀ z, 0 < z.val → z.val < a → ¬ S 0 z)
    (u v : V) (z : Fin (N + 1)) :
    Relation.ReflTransGen S (ι u) z → Relation.ReflTransGen S z (ι v) →
      ∃ w, ι w = z := by
  intro huz hzv
  have hlow : z = 0 ∨ a ≤ z.val := by
    rcases (himage (ι u)).mp ⟨u, rfl⟩ with hu | hu
    · have hzeroz : Relation.ReflTransGen S 0 z := by simpa only [hu] using huz
      rcases hzeroz.cases_head with hzz | ⟨y, h0y, hyz⟩
      · exact Or.inl hzz.symm
      · refine Or.inr ?_
        have hya : a ≤ y.val := by
          by_contra hnot
          exact (hzero y (hforward h0y) (lt_of_not_ge hnot) h0y).elim
        have hyz' : y.val ≤ z.val := reachable_le hforward hyz
        exact hya.trans hyz'
    · have huz' : (ι u).val ≤ z.val := reachable_le hforward huz
      exact Or.inr (hu.1.trans huz')
  rcases hlow with hzeroz | haz
  · exact (himage z).mpr (Or.inl hzeroz)
  · have hzv' : z.val ≤ (ι v).val := reachable_le hforward hzv
    rcases (himage (ι v)).mp ⟨v, rfl⟩ with hv | hv
    · rw [hv] at hzv'
      exact ((not_le_of_gt ha) (haz.trans hzv')).elim
    · exact (himage z).mpr (Or.inr ⟨haz, hzv'.trans hv.2⟩)

end VerticalStripLLT.Circular.DiagramProof
