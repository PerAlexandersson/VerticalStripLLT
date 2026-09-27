import VerticalStripLLT.Components.BlockExtractor
import Mathlib.Data.List.Pairwise

/-! Index inequalities forced by compatible words. -/

namespace VerticalStripLLT.Components

variable {V : Type*} [DecidableEq V]

theorem wordCompatible_idxOf_lt (R : V → V → Prop) (w : List V)
    (hirr : ∀ u, ¬R u u) (hw : wordCompatible R w) {u v : V}
    (hu : u ∈ w) (hv : v ∈ w)
    (huv : R u v) : w.idxOf u < w.idxOf v := by
  by_cases huv_eq : u = v
  · subst v
    exact (hirr u huv).elim
  have hiu : w.idxOf u < w.length := List.idxOf_lt_length_iff.mpr hu
  have hiv : w.idxOf v < w.length := List.idxOf_lt_length_iff.mpr hv
  have hwu : w[w.idxOf u] = u := List.getElem_idxOf hiu
  have hwv : w[w.idxOf v] = v := List.getElem_idxOf hiv
  have hidx_ne : w.idxOf v ≠ w.idxOf u := by
    intro h
    apply huv_eq
    exact (List.idxOf_inj hu).mp h.symm
  by_contra hlt
  have hle : w.idxOf v < w.idxOf u :=
    Nat.lt_of_le_of_ne (Nat.not_lt.mp hlt) hidx_ne
  have hp := (List.pairwise_iff_getElem.mp hw) (w.idxOf v) (w.idxOf u) hiv hiu hle
  exact hp (by simpa [hwu, hwv] using huv)

theorem idxOf_middle (ρ σ : List V) {a : V} (ha : a ∉ ρ) :
    (ρ ++ [a] ++ σ).idxOf a = ρ.length := by
  rw [show ρ ++ [a] ++ σ = ρ ++ ([a] ++ σ) by simp [List.append_assoc],
    List.idxOf_append_of_notMem ha]
  simp

end VerticalStripLLT.Components
