import VerticalStripLLT.CyclicHessenberg.CycleDisplayDeletion
import Mathlib.Data.Fintype.Sigma

/-! Finiteness follows from the actual maximal-cycle deletion equivalence. -/

namespace VerticalStripLLT.CyclicHessenberg

variable {V : Type*} [LinearOrder V]

namespace CycleDisplay

@[simp] theorem blocks_empty (D : CycleDisplay (∅ : Finset V)) : D.blocks = [] := by
  have hc := D.count_le_card
  exact List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hc)

instance emptyUnique : Unique (CycleDisplay (∅ : Finset V)) where
  default := empty
  uniq D := CycleDisplay.ext (blocks_empty D)

theorem finite (S : Finset V) : Finite (CycleDisplay S) := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hS : S.Nonempty
    · let r := S.max' hS
      have hr : r ∈ S := S.max'_mem hS
      have hmax : ∀ a ∈ S, a ≤ r := fun a ha => Finset.le_max' S a ha
      letI (U : RootSet S r) : Finite (CycleDisplay (S \ U.val)) :=
        ih _ (Finset.sdiff_ssubset U.property.1 ⟨r, U.property.2⟩)
      exact Finite.of_surjective (assemble S r hmax) (assemble_surjective S r hr hmax)
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      infer_instance

noncomputable instance fintype (S : Finset V) : Fintype (CycleDisplay S) :=
  @Fintype.ofFinite _ (finite S)

end CycleDisplay

end VerticalStripLLT.CyclicHessenberg
