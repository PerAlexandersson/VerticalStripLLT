import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Relator
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Linarith

/-! A saturated path cannot meet a longer injective path in a partial injection. -/

namespace VerticalStripLLT.Circular

theorem parallel_paths_disjoint
    {V : Type*} {k : ℕ} (R : V → V → Prop)
    (hleft : Relator.LeftUnique R) (hright : Relator.RightUnique R)
    (p : Fin (k + 3) → V) (q : Fin (k + 1) → V)
    (hp_inj : Function.Injective p) (_hq_inj : Function.Injective q)
    (hp : ∀ i : Fin (k + 2), R (p i.castSucc) (p i.succ))
    (hq : ∀ i : Fin k, R (q i.castSucc) (q i.succ))
    (hq0 : ∀ v, ¬ R v (q 0))
    (hqlast : ∀ v, ¬ R (q (Fin.last k)) v) :
    ∀ i j, p i ≠ q j := by
  classical
  let P : V → Prop := fun v => ∃ j, v = q j
  have forward {u v : V} (hu : P u) (h : R u v) : P v := by
    obtain ⟨i, rfl⟩ := hu
    by_cases hi : i.val < k
    · let j : Fin k := ⟨i.val, hi⟩
      have hj : j.castSucc = i := Fin.ext rfl
      exact ⟨j.succ, hright h (hj ▸ hq j)⟩
    · have hi' : i = Fin.last k := Fin.ext (by change i.val = k; lia)
      exact (hqlast v (hi' ▸ h)).elim
  have backward {u v : V} (hv : P v) (h : R u v) : P u := by
    obtain ⟨i, rfl⟩ := hv
    by_cases hi : i.val = 0
    · have hi' : i = 0 := Fin.ext hi
      exact (hq0 u (hi' ▸ h)).elim
    · let j : Fin k := ⟨i.val - 1, by lia⟩
      have hj : j.succ = i := Fin.ext (by dsimp [j]; lia)
      exact ⟨j.castSucc, hleft h (hj ▸ hq j)⟩
  have adjacent (i : Fin (k + 2)) : P (p i.castSucc) ↔ P (p i.succ) :=
    ⟨fun h => forward h (hp i), fun h => backward h (hp i)⟩
  have all_eq (i : Fin (k + 3)) : P (p i) ↔ P (p 0) := by
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih => exact (adjacent i).symm.trans ih
  intro i j hij
  have hzero : P (p 0) := (all_eq i).mp ⟨j, hij⟩
  have hall (r : Fin (k + 3)) : ∃ s, p r = q s := (all_eq r).mpr hzero
  let f (r : Fin (k + 3)) : Fin (k + 1) := Classical.choose (hall r)
  have hf (r) : p r = q (f r) := Classical.choose_spec (hall r)
  have hinj : Function.Injective f := by
    intro a b hab
    apply hp_inj
    rw [hf a, hf b, hab]
  have hc := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hc
  lia

end VerticalStripLLT.Circular
