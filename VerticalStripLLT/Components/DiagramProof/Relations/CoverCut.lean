import VerticalStripLLT.Components.DiagramProof.Relations.RelationPaths

/-! An edge that alone crosses a forward-closed cut is a cover. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {V : Type*} [LinearOrder V]

/-- A directed edge crossing a forward-closed cut is a cover when it is the
only edge allowed to cross that cut. -/
theorem relationCover_of_cut {R : V → V → Prop} {a b : V}
    (hforward : ∀ ⦃u v⦄, R u v → u < v)
    (hab : R a b) (P : V → Prop) (hPa : P a) (hPb : ¬ P b)
    (hcut : ∀ ⦃u v⦄, R u v → (u = a ∧ v = b) ∨ (P u → P v)) :
    RelationCover R a b := by
  let S : V → V → Prop := fun u v => R u v ∧ (P u → P v)
  have hpreserves {u v : V} (h : Relation.ReflTransGen S u v)
      (hu : P u) : P v := by
    induction h with
    | refl => exact hu
    | tail _ hstep ih => exact hstep.2 ih
  refine ⟨hforward hab, Relation.ReflTransGen.single hab, ?_⟩
  intro w haw hwb hw
  rcases hw with ⟨hl, hr⟩
  have hl' : Relation.ReflTransGen S a w := by
    apply reachable_mono_on_interval hforward (S := S) (lo := a) (hi := w) ?_
      hl le_rfl le_rfl
    intro u v hau hvw huv
    refine ⟨huv, ?_⟩
    rcases hcut huv with hab' | hmono
    · rcases hab' with ⟨_, rfl⟩
      exact (not_le_of_gt hwb hvw).elim
    · exact hmono
  have hr' : Relation.ReflTransGen S w b := by
    apply reachable_mono_on_interval hforward (S := S) (lo := w) (hi := b) ?_
      hr le_rfl le_rfl
    intro u v hwu hvb huv
    refine ⟨huv, ?_⟩
    rcases hcut huv with hab' | hmono
    · exact (not_le_of_gt haw (hab'.1 ▸ hwu)).elim
    · exact hmono
  exact hPb (hpreserves hr' (hpreserves hl' hPa))

end VerticalStripLLT.Circular.DiagramProof
