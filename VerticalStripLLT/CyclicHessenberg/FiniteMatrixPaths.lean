import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false

/-! Finite fixed-endpoint paths and their matrix-product expansion. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

/-- Paths of `n` steps with specified initial and terminal states. -/
def FixedBoundaryPath (I : Type*) (n : ℕ) (a b : I) :=
  {p : Fin (n + 1) → I // p 0 = a ∧ p (Fin.last n) = b}

noncomputable instance fixedBoundaryPathFintype {I : Type*} [Fintype I]
    (n : ℕ) (a b : I) : Fintype (FixedBoundaryPath I n a b) := by
  unfold FixedBoundaryPath
  exact Fintype.ofFinite _

/-- Split a nonempty path into its first step and the remaining path. -/
def fixedBoundaryPathSplit {I : Type*} (n : ℕ) (a b : I) :
    FixedBoundaryPath I (n + 1) a b ≃
      Σ c : I, FixedBoundaryPath I n c b where
  toFun p :=
    ⟨p.val (Fin.succ 0),
      ⟨fun i => p.val i.succ, by
        constructor
        · rfl
        · simpa using p.property.2⟩⟩
  invFun q :=
    ⟨Fin.cons a q.2.val, by
      constructor
      · simp
      · simpa using q.2.property.2⟩
  left_inv p := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ ?_ i
    · simp [p.property.1]
    · intro j
      rfl
  right_inv q := by
    rcases q with ⟨c, p, hfirst, hlast⟩
    subst c
    rfl

private def fixedBoundaryPathWeight {I R : Type*} [Fintype I]
    [CommSemiring R] {n : ℕ} {a b : I}
    (M : Fin n → Matrix I I R) (p : FixedBoundaryPath I n a b) : R :=
  ∏ ℓ : Fin n, M ℓ (p.val ℓ.castSucc) (p.val ℓ.succ)

/-- The product of a list of matrices is the sum over paths with fixed endpoints. -/
theorem list_prod_eq_sum_fixedBoundaryPath {I R : Type*} [Fintype I] [DecidableEq I]
    [CommSemiring R] {n : ℕ} (M : Fin n → Matrix I I R) (a b : I) :
    (List.ofFn M).prod a b =
      ∑ p : FixedBoundaryPath I n a b,
        ∏ ℓ : Fin n, M ℓ (p.val ℓ.castSucc) (p.val ℓ.succ) := by
  classical
  induction n generalizing a b with
  | zero =>
    by_cases hab : a = b
    · subst b
      let p₀ : FixedBoundaryPath I 0 a a := ⟨fun _ => a, by simp⟩
      letI : Subsingleton (FixedBoundaryPath I 0 a a) := ⟨by
        intro p q
        apply Subtype.ext
        funext i
        have hi : i = 0 := Fin.ext (by have := i.isLt; simp only [Fin.val_zero]; lia)
        subst i
        exact p.property.1.trans q.property.1.symm⟩
      let : Unique (FixedBoundaryPath I 0 a a) :=
        ⟨⟨p₀⟩, fun p => Subsingleton.elim p p₀⟩
      simp [Matrix.one_apply]
    · letI : IsEmpty (FixedBoundaryPath I 0 a b) := ⟨fun p =>
        hab (by simpa using p.property.1.symm.trans p.property.2)⟩
      simp [List.ofFn_zero, Matrix.one_apply, fixedBoundaryPathWeight, hab]
  | succ n ih =>
    let tailM : Fin n → Matrix I I R := fun i => M i.succ
    let e := fixedBoundaryPathSplit n a b
    have hweight (c : I) (p : FixedBoundaryPath I n c b) :
        fixedBoundaryPathWeight M (e.symm ⟨c, p⟩) =
          M 0 a c * fixedBoundaryPathWeight tailM p := by
      change (∏ ℓ : Fin (n + 1),
        M ℓ (Fin.cons a p.val ℓ.castSucc) (Fin.cons a p.val ℓ.succ)) = _
      rw [Fin.prod_univ_succ]
      simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ,
        Fin.castSucc_succ, p.property.1]
      rfl
    calc
      (List.ofFn M).prod a b =
          ∑ c : I, M 0 a c * (List.ofFn tailM).prod c b := by
        simp [List.ofFn_succ, List.prod_cons, Matrix.mul_apply, tailM]
      _ = ∑ c : I, M 0 a c *
            ∑ p : FixedBoundaryPath I n c b, fixedBoundaryPathWeight tailM p := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [ih tailM c b]
        rfl
      _ = ∑ q : Σ c : I, FixedBoundaryPath I n c b,
            M 0 a q.1 * fixedBoundaryPathWeight tailM q.2 := by
        rw [Fintype.sum_sigma]
        simp only [Finset.mul_sum]
      _ = ∑ p : FixedBoundaryPath I (n + 1) a b,
            fixedBoundaryPathWeight M p := by
        calc
          (∑ q : Σ c : I, FixedBoundaryPath I n c b,
              M 0 a q.1 * fixedBoundaryPathWeight tailM q.2) =
              ∑ q : Σ c : I, FixedBoundaryPath I n c b,
                fixedBoundaryPathWeight M (e.symm q) := by
            apply Finset.sum_congr rfl
            intro q hq
            rcases q with ⟨c, p⟩
            exact (hweight c p).symm
          _ = ∑ p : FixedBoundaryPath I (n + 1) a b,
                fixedBoundaryPathWeight M p := by
            simpa [e] using
              (Equiv.sum_comp e (fun q => fixedBoundaryPathWeight M (e.symm q))).symm

end VerticalStripLLT.CyclicHessenberg
