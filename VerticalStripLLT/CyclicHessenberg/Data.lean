import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi

set_option autoImplicit false

/-! Foundational finite data for cyclic Hessenberg functions. -/

namespace VerticalStripLLT.CyclicHessenberg

/-- A weakly increasing, extensive self-map of a finite chain. -/
structure Hessenberg (k : ℕ) where
  toFun : Fin k → Fin k
  monotone' : Monotone toFun
  le_apply' : ∀ i, i ≤ toFun i
  deriving DecidableEq

instance {k : ℕ} : CoeFun (Hessenberg k) (fun _ => Fin k → Fin k) :=
  ⟨Hessenberg.toFun⟩

namespace Hessenberg

/-- Equality of Hessenberg functions is determined by their evaluations. -/
@[ext]
theorem ext {k : ℕ} {f g : Hessenberg k} (h : ∀ i, f i = g i) : f = g := by
  cases f with
  | mk f hf₁ hf₂ =>
    cases g with
    | mk g hg₁ hg₂ =>
      have hfg : f = g := funext h
      cases hfg
      rfl

instance {k : ℕ} : Finite (Hessenberg k) :=
  Finite.of_injective Hessenberg.toFun fun f g h => ext fun i => congrFun h i

noncomputable instance {k : ℕ} : Fintype (Hessenberg k) := Fintype.ofFinite _

/-- The identity Hessenberg function. -/
def identity (k : ℕ) : Hessenberg k where
  toFun := id
  monotone' := by
    intro a b hab
    exact hab
  le_apply' := by
    intro i
    exact le_rfl

@[simp]
theorem identity_apply {k : ℕ} (i : Fin k) : identity k i = i := rfl

/-- The constant function with the largest value of a nonempty finite chain. -/
def complete {k : ℕ} (hk : 0 < k) : Hessenberg k where
  toFun := fun _ => ⟨k - 1, Nat.sub_lt hk Nat.zero_lt_one⟩
  monotone' := by
    intro a b hab
    exact le_rfl
  le_apply' := by
    intro i
    apply Fin.le_iff_val_le_val.mpr
    exact Nat.le_pred_of_lt i.isLt

@[simp]
theorem complete_apply {k : ℕ} (hk : 0 < k) (i : Fin k) :
    complete hk i = ⟨k - 1, Nat.sub_lt hk Nat.zero_lt_one⟩ := rfl

/-- The monotonicity condition, exposed as a theorem on coerced functions. -/
theorem monotone {k : ℕ} (h : Hessenberg k) : Monotone h := h.monotone'

/-- Every Hessenberg function is extensive. -/
theorem le_apply {k : ℕ} (h : Hessenberg k) (i : Fin k) : i ≤ h i :=
  h.le_apply' i

/-- Translation of the extensive condition to the source's one-based labels. -/
theorem oneBased_iff {k : ℕ} (h : Hessenberg k) (i : Fin k) :
    i ≤ h i ↔ i.val + 1 ≤ (h i).val + 1 := by
  rw [Fin.le_iff_val_le_val]
  constructor
  · intro hi
    exact Nat.succ_le_succ hi
  · intro hi
    exact Nat.le_of_succ_le_succ hi

end Hessenberg

/-- A layer-indexed tuple of Hessenberg functions. -/
abbrev Tuple (k n : ℕ) := Fin n → Hessenberg k

end VerticalStripLLT.CyclicHessenberg
