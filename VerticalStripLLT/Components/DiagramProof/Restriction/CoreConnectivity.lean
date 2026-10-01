import Mathlib.Logic.Relation

/-! Gluing connected core intersections of ambient selected blocks. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

/-- Connected core intersections glue to global core connectivity. -/
theorem coreConnected_of_block_gluing {V W : Type*}
    {ι : V → W} {R : V → V → Prop} {S L : W → W → Prop}
    (hinside : ∀ u v, S (ι u) (ι v) → R u v)
    (hout : ∀ x y, S x y → L x y ∨ ∃ u v, ι u = x ∧ ι v = y)
    (hmeet : ∀ x, ∃ u, Relation.EqvGen L x (ι u))
    (hblock : ∀ u v, Relation.EqvGen L (ι u) (ι v) →
      Relation.EqvGen R u v)
    (hconn : ∀ x y, Relation.EqvGen S x y) :
    ∀ u v, Relation.EqvGen R u v := by
  let rep : W → V := fun x => Classical.choose (hmeet x)
  have hrep (x : W) : Relation.EqvGen L x (ι (rep x)) :=
    Classical.choose_spec (hmeet x)
  have hstep : ∀ x y, S x y →
      Relation.EqvGen R (rep x) (rep y) := by
    intro x y hxy
    rcases hout x y hxy with hL | ⟨u, v, hux, hvy⟩
    · apply hblock
      exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hrep x))
        (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ hL) (hrep y))
    · have hR : R u v := hinside u v (by simpa only [hux, hvy] using hxy)
      have hleft : Relation.EqvGen L (ι u) (ι (rep x)) := by
        simpa only [hux] using hrep x
      have hright : Relation.EqvGen L (ι v) (ι (rep y)) := by
        simpa only [hvy] using hrep y
      exact Relation.EqvGen.trans _ _ _
        (Relation.EqvGen.symm _ _ (hblock u (rep x) hleft))
        (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ hR)
          (hblock v (rep y) hright))
  have hmap : ∀ x y, Relation.EqvGen S x y →
      Relation.EqvGen R (rep x) (rep y) := by
    intro x y hxy
    induction hxy with
    | rel x y hxy => exact hstep x y hxy
    | refl => exact Relation.EqvGen.refl _
    | symm x y hxy ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z hxy hyz ihxy ihyz =>
        exact Relation.EqvGen.trans _ _ _ ihxy ihyz
  intro u v
  have hpath : Relation.EqvGen R (rep (ι u)) (rep (ι v)) :=
    hmap (ι u) (ι v) (hconn (ι u) (ι v))
  exact Relation.EqvGen.trans _ _ _
    (hblock u (rep (ι u)) (hrep (ι u)))
    (Relation.EqvGen.trans _ _ _ hpath
      (Relation.EqvGen.symm _ _ (hblock v (rep (ι v)) (hrep (ι v)))))

/-- Every ambient vertex reaches the core in the block relation when the
ambient selected relation is connected and every selected edge is either a
block edge or has both endpoints in the core image. -/
theorem coreRepresentative_exists_of_connected {V W : Type*}
    {ι : V → W} {S L : W → W → Prop}
    (u0 : V)
    (hout : ∀ x y, S x y → L x y ∨ ∃ u v, ι u = x ∧ ι v = y)
    (hconn : ∀ x y, Relation.EqvGen S x y) :
    ∀ x, ∃ u, Relation.EqvGen L x (ι u) := by
  let C : W → Prop := fun x => ∃ u, Relation.EqvGen L x (ι u)
  have hstep : ∀ x y, S x y → (C x ↔ C y) := by
    intro x y hxy
    rcases hout x y hxy with hL | ⟨u, v, hux, hvy⟩
    · constructor
      · rintro ⟨w, hw⟩
        exact ⟨w, Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hL)) hw⟩
      · rintro ⟨w, hw⟩
        exact ⟨w, Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.rel _ _ hL) hw⟩
    · constructor
      · rintro ⟨_, _⟩
        exact ⟨v, by rw [← hvy]; exact Relation.EqvGen.refl _⟩
      · rintro ⟨_, _⟩
        exact ⟨u, by rw [← hux]; exact Relation.EqvGen.refl _⟩
  have hpath : ∀ x y, Relation.EqvGen S x y → (C x ↔ C y) := by
    intro x y hxy
    induction hxy with
    | rel x y hxy => exact hstep x y hxy
    | refl => exact Iff.rfl
    | symm x y hxy ih => exact ih.symm
    | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz
  intro x
  have hcore : C (ι u0) := ⟨u0, Relation.EqvGen.refl _⟩
  exact (hpath x (ι u0) (hconn x (ι u0))).mpr hcore

/-- The block-gluing theorem with the core-meeting condition derived from
ambient connectedness. -/
theorem coreConnected_of_block_gluing_of_connected {V W : Type*}
    {ι : V → W} {R : V → V → Prop} {S L : W → W → Prop}
    (u0 : V)
    (hinside : ∀ u v, S (ι u) (ι v) → R u v)
    (hout : ∀ x y, S x y → L x y ∨ ∃ u v, ι u = x ∧ ι v = y)
    (hblock : ∀ u v, Relation.EqvGen L (ι u) (ι v) →
      Relation.EqvGen R u v)
    (hconn : ∀ x y, Relation.EqvGen S x y) :
    ∀ u v, Relation.EqvGen R u v := by
  exact coreConnected_of_block_gluing hinside hout
    (coreRepresentative_exists_of_connected u0 hout hconn) hblock hconn

end VerticalStripLLT.Circular.DiagramProof
