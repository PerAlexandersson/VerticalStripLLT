import VerticalStripLLT.CyclicHessenberg.CycleDisplay
import Mathlib.GroupTheory.Perm.List
import Mathlib.Data.List.Cycle

set_option autoImplicit false

/-! Translate cyclic block equations into pointwise list actions. -/

namespace VerticalStripLLT.CyclicHessenberg

variable {V : Type*} [LinearOrder V]

/-- A cyclic list action is exactly the form-permutation action on its support. -/
theorem map_cons_eq_rotated_iff_formPerm_action (f : V → V) (r : V)
    (t : List V) (hnd : (r :: t).Nodup) :
    List.map f (r :: t) = t ++ [r] ↔
      ∀ x ∈ r :: t, f x = (r :: t).formPerm x := by
  let l := r :: t
  have hrot : t ++ [r] = l.rotate 1 := by
    simp [l, List.rotate_cons_succ]
  constructor
  · intro hmap x hx
    have hx' : x ∈ l := by simpa [l] using hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx'
    have hmap' : List.map f l = l.rotate 1 := by
      exact hmap.trans hrot
    have hopt := congrArg (fun w : List V => w[i]?) hmap'
    have hval : f l[i] = l[(i + 1) % l.length]'_ := by
      apply Option.some.inj
      simpa [List.getElem?_map, List.getElem?_rotate, hi] using hopt
    exact hval.trans (List.formPerm_apply_getElem l hnd i hi).symm
  · intro hact
    have hrotMap : List.map f l = l.rotate 1 := by
      apply List.ext_getElem
      · simp
      · intro i hi₁ hi₂
        have hi : i < l.length := by simpa using hi₁
        rw [List.getElem_map, hact _ (List.getElem_mem hi),
          List.formPerm_apply_getElem l hnd i hi, List.getElem_rotate]
    simpa [l, List.rotate_cons_succ] using hrotMap

/-- A cycle-source/target equality holds exactly when each block has its cyclic action. -/
theorem map_cycleSourceWord_eq_cycleTargetWord_iff (f : V → V)
    (B : List (V × List V)) :
    List.map f (cycleSourceWord B) = cycleTargetWord B ↔
      ∀ b ∈ B, List.map f (b.1 :: b.2) = b.2 ++ [b.1] := by
  induction B with
  | nil => simp [cycleSourceWord, cycleTargetWord]
  | cons b B ih =>
    change List.map f ((b.1 :: b.2) ++ cycleSourceWord B) =
        (b.2 ++ [b.1]) ++ cycleTargetWord B ↔ _
    rw [List.map_append]
    have hsplit :
        (List.map f (b.1 :: b.2) ++ List.map f (cycleSourceWord B) =
          (b.2 ++ [b.1]) ++ cycleTargetWord B) ↔
          (List.map f (b.1 :: b.2) = b.2 ++ [b.1] ∧
            List.map f (cycleSourceWord B) = cycleTargetWord B) := by
      constructor
      · intro h
        exact List.append_inj h (by simp)
      · rintro ⟨hblock, hrest⟩
        rw [hblock, hrest]
    rw [hsplit, ih]
    simp only [List.mem_cons, forall_eq_or_imp]

end VerticalStripLLT.CyclicHessenberg
