import VerticalStripLLT.Circular.IntegerChain
import VerticalStripLLT.Circular.ContactEndpoints
import VerticalStripLLT.Circular.NeutralContacts
import VerticalStripLLT.Circular.ParallelPathsGeneral
import Mathlib.Tactic.Linarith

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular
namespace Diagram

variable {n : ℕ} (D : Diagram n)

structure RawBounceContacts (t x : ℤ) where
  k : ℕ
  main : Fin (k + 2) → Fin n
  parallel : Fin (k + 1) → Fin n
  main_steps : ∀ i : Fin (k + 1),
    D.edgeData.selected ∅ (main i.castSucc) (main i.succ)
  parallel_steps : ∀ i : Fin k,
    D.edgeData.selected ∅ (parallel i.castSucc) (parallel i.succ)
  parallel_next : ∀ i : Fin (k + 1),
    parallel i = D.area.next (main i.castSucc)
  main_zero : main 0 = D.residue x
  main_last : main (Fin.last (k + 1)) = D.residue t
  inner_last : main (Fin.last k).castSucc = D.residue (D.boundary t)
  parallel_zero : parallel 0 = D.residue (x + 1)
  parallel_last : parallel (Fin.last k) = D.residue (D.boundary t + 1)

theorem ReverseBounce.exists_raw_contacts {t x : ℤ}
    (h : ReverseBounce D t x) (hroot : D.strictAt t) :
    Nonempty (D.RawBounceContacts t x) := by
  rcases ReverseBounce.exists_contacts D h hroot with
    ⟨inner, hne, hstarts, hends, hmain, hparallel⟩
  let mainList : List ℤ := inner ++ [t]
  let parallelList : List ℤ := inner.map (fun z : ℤ => z + 1)
  let k : ℕ := inner.length - 1
  have hlen : 1 ≤ inner.length := by
    cases inner with
    | nil => exact False.elim (hne rfl)
    | cons a as => simp
  have hk : inner.length = k + 1 := by dsimp [k]; lia
  have hmainlen : mainList.length = k + 2 := by
    simp only [mainList, List.length_append, List.length_singleton, hk]
  have hparlen : parallelList.length = k + 1 := by
    simpa only [parallelList, List.length_map] using hk
  let main : Fin (k + 2) → Fin n := fun j =>
    D.residue (mainList.get ⟨j.val, by rw [hmainlen]; exact j.isLt⟩)
  let parallel : Fin (k + 1) → Fin n := fun j =>
    D.residue (parallelList.get ⟨j.val, by rw [hparlen]; exact j.isLt⟩)
  refine ⟨⟨k, main, parallel, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro j
    have hj : j.val + 1 < mainList.length := by rw [hmainlen]; lia
    have hs := List.isChain_iff_getElem.mp hmain.isChain j.val hj
    simpa [main, integerSelected] using hs
  · intro j
    have hj : j.val + 1 < parallelList.length := by rw [hparlen]; lia
    have hs := List.isChain_iff_getElem.mp hparallel.isChain j.val hj
    simpa [parallel, parallelList, integerSelected] using hs
  · intro j
    dsimp [parallel, main, mainList, parallelList]
    simp only [List.getElem_map]
    rw [List.getElem_append_left (by rw [hk]; exact j.isLt)]
    exact D.residue_succ _
  · rcases hstarts with ⟨rest, hrest⟩
    simp [main, mainList, hrest]
  · simp [main, mainList, ← hk]
  · rcases hends with ⟨init, hinit⟩
    have hinitlen : init.length = k := by
      have hh := congrArg List.length hinit
      simp only [List.length_append, List.length_singleton] at hh
      lia
    simp [main, mainList, hinit, ← hinitlen]
  · rcases hstarts with ⟨rest, hrest⟩
    simp [parallel, parallelList, hrest]
  · rcases hends with ⟨init, hinit⟩
    have hinitlen : init.length = k := by
      have hh := congrArg List.length hinit
      simp only [List.length_append, List.length_singleton] at hh
      lia
    simp [parallel, parallelList, hinit, ← hinitlen]

namespace RawBounceContacts

variable {D} {t x : ℤ} (B : D.RawBounceContacts t x)

include B

theorem main_injective (ha : D.edgeData.Admissible ∅) : Function.Injective B.main :=
  acyclic_walk_injective _ ha B.main B.main_steps

theorem main_parallel_disjoint (ha : D.edgeData.Admissible ∅)
    (ht : D.EligibleDE t) (hx : ¬ D.strictAt (x + 1)) :
    ∀ i j, B.main i ≠ B.parallel j := by
  apply parallel_paths_disjoint_general _ D.strict_selected_leftUnique
    D.strict_selected_rightUnique B.main B.parallel (B.main_injective ha)
    B.main_steps B.parallel_steps
  · intro v
    rw [B.parallel_zero]
    exact D.not_selected_to_of_not_strictAt hx v
  · intro v
    rw [B.parallel_last]
    exact ht.parallel_end_free D v
  · exact Nat.lt_succ_self _

theorem next_residue_ne (ha : D.edgeData.Admissible ∅)
    (ht : D.EligibleDE t) (hx : ¬ D.strictAt (x + 1)) :
    D.residue (x + 1) ≠ D.residue t := by
  have hh := B.main_parallel_disjoint ha ht hx (Fin.last (B.k + 1)) 0
  rw [B.main_last, B.parallel_zero] at hh
  exact hh.symm

end RawBounceContacts
end Diagram
end VerticalStripLLT.Circular
