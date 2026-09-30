import VerticalStripLLT.Components.DiagramProof.PathRestriction

/-! Path and weak-reachability restriction along selected complete blocks. -/

namespace VerticalStripLLT.Circular.DiagramProof

/-- An updated forward relation cannot leave and return to a bounded image when
every exterior updated edge agrees with the source relation. -/
theorem pathImage_closed_of_forward_update {k n : ℕ}
    (ι : Fin (k + 1) ↪o Fin n) {R T : Fin n → Fin n → Prop}
    (hforward : ∀ ⦃x y⦄, T x y → x < y) {lo hi : Fin n}
    (hbounds : ∀ i, lo ≤ ι i ∧ ι i ≤ hi)
    (hclosed : ∀ x y, lo ≤ x → y ≤ hi → R x y →
      (∃ i, ι i = x) → ∃ j, ι j = y)
    (hexterior : ∀ x y, (¬ ∃ a b, ι a = x ∧ ι b = y) → (T x y ↔ R x y))
    (u v : Fin (k + 1)) (z : Fin n) :
    Relation.ReflTransGen T (ι u) z → Relation.ReflTransGen T z (ι v) →
      ∃ w, ι w = z := by
  intro huz hzv
  have pathImage : ∀ {x : Fin n}, Relation.ReflTransGen T (ι u) x →
      Relation.ReflTransGen T x (ι v) → ∃ i, ι i = x := by
    intro x hux
    induction hux with
    | refl =>
      intro _
      exact ⟨u, rfl⟩
    | @tail x y hux hxy ih =>
      intro hyv
      obtain ⟨i, hix⟩ := ih ((Relation.ReflTransGen.single hxy).trans hyv)
      by_cases hyimage : ∃ j, ι j = y
      · exact hyimage
      · have hxyR : R (ι i) y := by
          apply (hexterior (ι i) y ?_).mp
          simpa only [hix] using hxy
          rintro ⟨a, b, ha, hb⟩
          exact hyimage ⟨b, hb⟩
        have hyhi : y ≤ hi :=
          (reachable_le hforward hyv).trans (hbounds v).2
        exact hclosed (ι i) y (hbounds i).1 hyhi hxyR ⟨i, rfl⟩
  exact pathImage huz hzv

/-- Weak reachability restricts along an injective image closed under both
ends of every ambient relation edge. -/
theorem eqvGen_iff_of_image_closed {V W : Type*} (ι : V ↪ W)
    {R : W → W → Prop} {S : V → V → Prop}
    (himageclosed : ∀ x y, R x y →
      ((∃ a, ι a = x) ↔ ∃ b, ι b = y))
    (hrel : ∀ a b, S a b ↔ R (ι a) (ι b)) (u v : V) :
    Relation.EqvGen R (ι u) (ι v) ↔ Relation.EqvGen S u v := by
  have image_iff_of_eqvGen : ∀ {x y : W}, Relation.EqvGen R x y →
      ((∃ a, ι a = x) ↔ ∃ b, ι b = y) := by
    intro x y hxy
    induction hxy with
    | rel x y hxy => exact himageclosed x y hxy
    | refl => exact Iff.rfl
    | symm x y hxy ih => exact ih.symm
    | trans x y z hxy hyz ihxy ihyz =>
      exact ihxy.trans ihyz
  have image_of_eqvGen : ∀ {x y : W}, Relation.EqvGen R x y →
      (∃ a, ι a = x) → ∃ b, ι b = y := by
    intro x y hxy hx
    exact (image_iff_of_eqvGen hxy).mp hx
  let P : W → W → Prop := fun x y =>
    (∃ a, ι a = x) ∧ (∃ b, ι b = y) ∧ R x y
  have within : ∀ {x y : W}, Relation.EqvGen R x y →
      (∃ a, ι a = x) → (∃ b, ι b = y) → Relation.EqvGen P x y := by
    intro x y hxy
    induction hxy with
    | rel x y hxy =>
      intro hx hy
      exact Relation.EqvGen.rel _ _ ⟨hx, hy, hxy⟩
    | refl =>
      intro _ _
      exact Relation.EqvGen.refl _
    | symm x y hxy ih =>
      intro hy hx
      exact Relation.EqvGen.symm _ _ (ih hx hy)
    | trans x y z hxy hyz ihxy ihyz =>
      intro hx hz
      have hy := image_of_eqvGen hxy hx
      exact Relation.EqvGen.trans _ _ _ (ihxy hx hy) (ihyz hy hz)
  have ambient : ∀ {x y : W}, Relation.EqvGen P x y → Relation.EqvGen R x y := by
    intro x y hxy
    induction hxy with
    | rel x y hxy => exact Relation.EqvGen.rel _ _ hxy.2.2
    | refl => exact Relation.EqvGen.refl _
    | symm x y hxy ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z hxy hyz ihxy ihyz =>
      exact Relation.EqvGen.trans _ _ _ ihxy ihyz
  have restrict : ∀ {x y : W}, Relation.EqvGen P x y → ∀ a b,
      ι a = x → ι b = y → Relation.EqvGen S a b := by
    intro x y hxy
    induction hxy with
    | rel x y hxy =>
      intro a b ha hb
      apply Relation.EqvGen.rel
      apply (hrel a b).mpr
      simpa only [← ha, ← hb] using hxy.2.2
    | refl x =>
      intro a b ha hb
      have hab : a = b := ι.injective (ha.trans hb.symm)
      subst b
      exact Relation.EqvGen.refl _
    | symm x y hxy ih =>
      intro a b ha hb
      exact Relation.EqvGen.symm _ _ (ih b a hb ha)
    | trans x y z hxy hyz ihxy ihyz =>
      intro a c ha hc
      obtain ⟨b, hb⟩ := image_of_eqvGen (ambient hxy) ⟨a, ha⟩
      exact Relation.EqvGen.trans _ _ _ (ihxy a b ha hb) (ihyz b c hb hc)
  constructor
  · intro huv
    exact restrict (within huv ⟨u, rfl⟩ ⟨v, rfl⟩) u v rfl rfl
  · intro huv
    induction huv with
    | rel x y hxy => exact Relation.EqvGen.rel _ _ ((hrel x y).mp hxy)
    | refl => exact Relation.EqvGen.refl _
    | symm x y hxy ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z hxy hyz ihxy ihyz =>
      exact Relation.EqvGen.trans _ _ _ ihxy ihyz

end VerticalStripLLT.Circular.DiagramProof
