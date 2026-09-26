import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Relator
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Linarith

namespace VerticalStripLLT.Circular

theorem parallel_paths_disjoint_general
    {V : Type*} {a b : ℕ} (R : V → V → Prop)
    (hleft : Relator.LeftUnique R) (hright : Relator.RightUnique R)
    (p : Fin (a + 1) → V) (q : Fin (b + 1) → V)
    (hp_inj : Function.Injective p)
    (hp : ∀ i : Fin a, R (p i.castSucc) (p i.succ))
    (hq : ∀ i : Fin b, R (q i.castSucc) (q i.succ))
    (hq0 : ∀ v, ¬ R v (q 0))
    (hqlast : ∀ v, ¬ R (q (Fin.last b)) v)
    (hab : b < a) :
    ∀ i j, p i ≠ q j := by
  classical
  let P : V → Prop := fun v => ∃ j, v = q j
  have forward {u v : V} (hu : P u) (h : R u v) : P v := by
    obtain ⟨i, rfl⟩ := hu
    by_cases hi : i.val < b
    · let j : Fin b := ⟨i.val, hi⟩
      have hj : j.castSucc = i := Fin.ext rfl
      exact ⟨j.succ, hright h (hj ▸ hq j)⟩
    · have hi' : i = Fin.last b := Fin.ext (by change i.val = b; lia)
      exact (hqlast v (hi' ▸ h)).elim
  have backward {u v : V} (hv : P v) (h : R u v) : P u := by
    obtain ⟨i, rfl⟩ := hv
    by_cases hi : i.val = 0
    · have hi' : i = 0 := Fin.ext hi
      exact (hq0 u (hi' ▸ h)).elim
    · let j : Fin b := ⟨i.val - 1, by lia⟩
      have hj : j.succ = i := Fin.ext (by dsimp [j]; lia)
      exact ⟨j.castSucc, hleft h (hj ▸ hq j)⟩
  have adjacent (i : Fin a) : P (p i.castSucc) ↔ P (p i.succ) :=
    ⟨fun h => forward h (hp i), fun h => backward h (hp i)⟩
  have all_eq (i : Fin (a + 1)) : P (p i) ↔ P (p 0) := by
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih => exact (adjacent i).symm.trans ih
  intro i j hij
  have hzero : P (p 0) := (all_eq i).mp ⟨j, hij⟩
  have hall (r : Fin (a + 1)) : ∃ s, p r = q s := (all_eq r).mpr hzero
  let f (r : Fin (a + 1)) : Fin (b + 1) := Classical.choose (hall r)
  have hf (r) : p r = q (f r) := Classical.choose_spec (hall r)
  have hinj : Function.Injective f := by
    intro c d hcd
    apply hp_inj
    rw [hf c, hf d, hcd]
  have hc := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hc
  lia

end VerticalStripLLT.Circular
