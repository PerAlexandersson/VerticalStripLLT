import Mathlib.Logic.Relation
import Mathlib.Order.Basic

/-! Restricting a path to tight steps of a monotone score. -/

namespace VerticalStripLLT.Components

variable {V W : Type*} [PartialOrder W]

theorem score_le_of_reachable (R : V → V → Prop) (score : V → W)
    (hmono : ∀ ⦃u v⦄, R u v → score u ≤ score v)
    {u v : V} (h : Relation.ReflTransGen R u v) : score u ≤ score v := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact ih.trans (hmono hstep)

/-- Equal endpoint scores force every step to belong to the tight subrelation. -/
theorem reachable_of_tight_score (R S : V → V → Prop) (score : V → W)
    (hmono : ∀ ⦃u v⦄, R u v → score u ≤ score v)
    (htight : ∀ ⦃u v⦄, R u v → score u = score v → S u v)
    {u v : V} (h : Relation.ReflTransGen R u v) (heq : score u = score v) :
    Relation.ReflTransGen S u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail v w hpath hstep ih =>
    have hprefix := score_le_of_reachable R score hmono hpath
    have hlast := hmono hstep
    have huv : score u = score v := le_antisymm hprefix (by simpa [heq] using hlast)
    exact (ih huv).tail (htight hstep (huv.symm.trans heq))

end VerticalStripLLT.Components
