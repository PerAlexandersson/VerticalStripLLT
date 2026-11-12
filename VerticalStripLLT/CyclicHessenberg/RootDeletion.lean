import VerticalStripLLT.CyclicHessenberg.Kernel
import Mathlib.Data.Finset.Powerset

/-! Positive residual kernels and the simultaneous minimum slide. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {V R : Type*} [LinearOrder V]

section Semiring

variable [CommSemiring R]

/-- The positive residual is a sum of crossed entries, defined before its signed identity.
Applications require `r ∈ U` and that `r` is the largest remaining vertex. -/
noncomputable def rootDeletion (q : R) (Z : List V → List V → R)
    (U : Finset V) (r : V) (π τ : List V) : R :=
  q ^ (U.card - 1) * ∑ σ : Order (U.erase r),
    Z ((r :: σ.val) ++ π) ((σ.val ++ [r]) ++ τ)

/-- Every crossed summand fixes prefixes of equal length, although their orders differ. -/
theorem rootDeletion_exchangeCompatible {q : R} {Z : List V → List V → R}
    (hZ : ListExchangeCompatible q Z) (U : Finset V) (r : V) :
    ListExchangeCompatible q (rootDeletion q Z U r) := by
  classical
  apply ListExchangeCompatible.smul
  apply ListExchangeCompatible.sum
  intro σ hσ
  exact hZ.prefixLists (r :: σ.val) (σ.val ++ [r]) (by simp [Nat.add_comm])

theorem rootDeletion_map {T : Type*} [CommSemiring T] (f : R →+* T)
    (q : R) (Z : List V → List V → R) (U : Finset V) (r : V) (π τ : List V) :
    f (rootDeletion q Z U r π τ) =
      rootDeletion (f q) (fun l t => f (Z l t)) U r π τ := by
  classical
  simp [rootDeletion]

/-- The crossed entries encountered while moving `a` simultaneously along both lists. -/
def minimumSlideSum (Z : List V → List V → R) (a : V) (π τ : List V) :
    List V → List V → List V → List V → R
  | ρ, ρ', x :: xs, y :: ys =>
    Z (ρ ++ x :: a :: xs ++ π) (ρ' ++ a :: y :: ys ++ τ) +
      minimumSlideSum Z a π τ (ρ ++ [x]) (ρ' ++ [y]) xs ys
  | _, _, _, _ => 0

/-- Each step is the second exchange law. The fixed row and column suffixes are arbitrary. -/
theorem minimumSlide {q : R} {Z : List V → List V → R}
    (hZ : ListExchangeCompatible q Z) (a : V) (π τ ρ ρ' xs ys : List V)
    (hρ : ρ.length = ρ'.length) (hlen : xs.length = ys.length)
    (hxs : ∀ x ∈ xs, a < x) (hys : ∀ y ∈ ys, a < y) :
    Z (ρ ++ a :: xs ++ π) (ρ' ++ a :: ys ++ τ) =
      Z (ρ ++ xs ++ [a] ++ π) (ρ' ++ ys ++ [a] ++ τ) +
        q * minimumSlideSum Z a π τ ρ ρ' xs ys := by
  induction xs generalizing ys ρ ρ' with
  | nil =>
    have hy : ys = [] := List.length_eq_zero_iff.mp hlen.symm
    subst ys
    simp [minimumSlideSum]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have hax := hxs x (by simp)
      have hay := hys y (by simp)
      have hstep := (hZ ρ (xs ++ π) ρ' (ys ++ τ) a x a y hρ hax hay).2
      have htail := ih (ys := ys) (ρ := ρ ++ [x]) (ρ' := ρ' ++ [y])
        (by simp [hρ]) (by simpa using hlen)
        (fun z hz => hxs z (by simp [hz])) (fun z hz => hys z (by simp [hz]))
      simp only [List.append_assoc, List.cons_append, List.nil_append] at hstep htail ⊢
      rw [hstep, htail]
      simp only [minimumSlideSum]
      ring

end Semiring

section Ring

variable [CommRing R]

/-- A mountain lists the unmarked vertices increasingly, then the root, then marks decreasingly. -/
def mountainList (U T : Finset V) (r : V) : List V :=
  ((U.erase r) \ T).sort ++ [r] ++ T.sort (· ≥ ·)

/-- The signed prefix functional before the positive root-deletion theorem. -/
noncomputable def signedRootDeletion (Z : List V → List V → R)
    (U : Finset V) (r : V) (π τ : List V) : R :=
  ∑ T ∈ (U.erase r).powerset,
    (-1 : R) ^ T.card * Z (mountainList U T r ++ π) (mountainList U T r ++ τ)

end Ring

end VerticalStripLLT.CyclicHessenberg
