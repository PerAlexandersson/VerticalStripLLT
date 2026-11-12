import VerticalStripLLT.CyclicHessenberg.Data
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.GroupTheory.Perm.Basic

/-! Feasible layer matchings and their successive-composition monodromy. -/

namespace VerticalStripLLT.CyclicHessenberg

variable {k n : ℕ}

/-- Each layer is an actual perfect matching with the original edge inequalities. -/
def IsMatchingTuple (h : Tuple k n) (φ : Fin n → Equiv.Perm (Fin k)) : Prop :=
  ∀ (ℓ : Fin n) (x : Fin k), x ≤ h ℓ (φ ℓ x)

abbrev MatchingTuple (h : Tuple k n) :=
  {φ : Fin n → Equiv.Perm (Fin k) // IsMatchingTuple h φ}

noncomputable instance matchingTupleFintype (h : Tuple k n) : Fintype (MatchingTuple h) :=
  Fintype.ofFinite _

/-- Follow the first `i` matchings in order. Inversion reverses Mathlib's product convention. -/
def matchingTransport (φ : Fin n → Equiv.Perm (Fin k)) (i : Fin (n + 1)) :
    Equiv.Perm (Fin k) :=
  (Fin.partialProd (fun ℓ => (φ ℓ)⁻¹) i)⁻¹

@[simp] theorem matchingTransport_zero (φ : Fin n → Equiv.Perm (Fin k)) :
    matchingTransport φ 0 = 1 := by
  simp [matchingTransport]

theorem matchingTransport_succ (φ : Fin n → Equiv.Perm (Fin k)) (ℓ : Fin n) :
    matchingTransport φ ℓ.succ = φ ℓ * matchingTransport φ ℓ.castSucc := by
  simp only [matchingTransport, Fin.partialProd_succ, mul_inv_rev, inv_inv]

theorem matchingTransport_succ_apply (φ : Fin n → Equiv.Perm (Fin k))
    (ℓ : Fin n) (x : Fin k) :
    matchingTransport φ ℓ.succ x = φ ℓ (matchingTransport φ ℓ.castSucc x) := by
  rw [matchingTransport_succ, Equiv.Perm.mul_apply]

/-- The last matching acts last: `φ_(n-1) ∘ ... ∘ φ_0`. -/
def matchingMonodromy (φ : Fin n → Equiv.Perm (Fin k)) : Equiv.Perm (Fin k) :=
  matchingTransport φ (Fin.last n)

/-- Recover the individual matching between two successive transported boundaries. -/
theorem matchingTransport_recover (φ : Fin n → Equiv.Perm (Fin k)) (ℓ : Fin n) :
    (matchingTransport φ ℓ.castSucc).symm.trans (matchingTransport φ ℓ.succ) = φ ℓ := by
  apply Equiv.ext
  intro x
  simp only [Equiv.trans_apply, matchingTransport_succ_apply, Equiv.apply_symm_apply]

/-- Successive ratios reconstruct a boundary path with identity starting boundary. -/
theorem matchingTransport_of_boundaries (P : Fin (n + 1) → Equiv.Perm (Fin k))
    (hP : P 0 = 1) (i : Fin (n + 1)) :
    matchingTransport (fun ℓ => (P ℓ.castSucc).symm.trans (P ℓ.succ)) i = P i := by
  induction i using Fin.inductionOn with
  | zero => exact matchingTransport_zero _ |>.trans hP.symm
  | succ i ih =>
    rw [matchingTransport_succ, ih]
    apply Equiv.ext
    intro x
    simp only [Equiv.Perm.mul_apply, Equiv.trans_apply, Equiv.symm_apply_apply]

theorem matchingTransport_of_arbitrary_boundaries
    (P : Fin (n + 1) → Equiv.Perm (Fin k)) (i : Fin (n + 1)) :
    matchingTransport (fun ℓ => (P ℓ.castSucc).symm.trans (P ℓ.succ)) i =
      (P 0).symm.trans (P i) := by
  let Q := fun ℓ => (P 0).symm.trans (P ℓ)
  have hQ : Q 0 = 1 := by ext x; simp [Q]
  have hh := matchingTransport_of_boundaries Q hQ i
  have hratio : (fun ℓ : Fin n => (Q ℓ.castSucc).symm.trans (Q ℓ.succ)) =
      (fun ℓ : Fin n => (P ℓ.castSucc).symm.trans (P ℓ.succ)) := by
    funext ℓ
    ext x
    simp [Q]
  rw [hratio] at hh
  exact hh

end VerticalStripLLT.CyclicHessenberg
