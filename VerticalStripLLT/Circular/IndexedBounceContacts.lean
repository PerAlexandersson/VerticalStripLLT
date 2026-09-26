import VerticalStripLLT.Circular.IntegerChain
import Mathlib.Data.List.Chain
import Mathlib.Tactic.Linarith

/-! Fin-indexed paths obtained from reverse-bounce contact lists. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular

namespace Diagram

variable {n : ℕ} (D : Diagram n)

structure IndexedBounceContacts (t x : ℤ) where
  k : ℕ
  main : Fin (k + 3) → Fin n
  parallel : Fin (k + 1) → Fin n
  main_steps : ∀ i : Fin (k + 2),
    D.edgeData.selected ∅ (main i.castSucc) (main i.succ)
  parallel_steps : ∀ i : Fin k,
    D.edgeData.selected ∅ (parallel i.castSucc) (parallel i.succ)
  parallel_next : ∀ i : Fin (k + 1),
    parallel i = D.area.next (main i.succ.castSucc)
  main_zero : main 0 = D.residue (D.boundary x)
  main_one : main 1 = D.residue x
  main_last : main (Fin.last (k + 2)) = D.residue t
  inner_last : main (Fin.last (k + 1)).castSucc = D.residue (D.boundary t)
  parallel_zero : parallel 0 = D.residue (x + 1)
  parallel_last : parallel (Fin.last k) = D.residue (D.boundary t + 1)

theorem ReverseBounce.exists_indexed_contacts {t x : ℤ}
    (h : ReverseBounce D t x) (hroot : D.strictAt t)
    (hterminal : D.strictAt x) : Nonempty (D.IndexedBounceContacts t x) := by
  rcases ReverseBounce.exists_contacts D h hroot with
    ⟨inner, hne, hstarts, hends, hmain, hparallel⟩
  let mainList : List ℤ := D.boundary x :: (inner ++ [t])
  let parallelList : List ℤ := inner.map (fun z : ℤ => z + 1)
  let k : ℕ := inner.length - 1
  have hlen : 1 ≤ inner.length := by
    cases inner with
    | nil => exact False.elim (hne rfl)
    | cons a as => simp
  have hk : inner.length = k + 1 := by dsimp [k]; lia
  have hmainlen : mainList.length = k + 3 := by
    simp only [mainList, List.length_cons, List.length_append, List.length_nil, hk]
  have hparlen : parallelList.length = k + 1 := by
    simpa only [parallelList, List.length_map] using hk
  let main : Fin (k + 3) → Fin n := fun i =>
    D.residue (mainList.get ⟨i.val, by rw [hmainlen]; exact i.isLt⟩)
  let parallel : Fin (k + 1) → Fin n := fun i =>
    D.residue (parallelList.get ⟨i.val, by rw [hparlen]; exact i.isLt⟩)
  have hmainchain : List.IsChain D.integerSelected mainList := by
    apply List.IsChain.cons hmain.isChain
    rcases hstarts with ⟨rest, hrest⟩
    simpa [integerSelected, mainList, hrest] using D.selected_of_strictAt hterminal
  refine ⟨⟨k, main, parallel, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i
    have hi : i.val + 1 < mainList.length := by
      rw [hmainlen]
      have := i.isLt
      lia
    have hs := List.isChain_iff_getElem.mp hmainchain i.val hi
    simpa [main, integerSelected] using hs
  · intro i
    have hi : i.val + 1 < parallelList.length := by
      rw [hparlen]
      have := i.isLt
      lia
    have hs := List.isChain_iff_getElem.mp hparallel.isChain i.val hi
    simpa [parallel, parallelList, integerSelected] using hs
  · intro i
    dsimp [parallel, main, mainList, parallelList]
    simp only [List.getElem_map]
    rw [List.getElem_append_left (by have := i.isLt; lia)]
    exact D.residue_succ _
  · simp [main, mainList]
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

end Diagram
end VerticalStripLLT.Circular
