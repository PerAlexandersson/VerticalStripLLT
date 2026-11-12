import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-! A sparse matrix for an involution and its scalar commutation criterion. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {I R : Type*} [Fintype I] [DecidableEq I]

section Semiring

variable [CommSemiring R]

/-- The sparse exchange matrix associated with an involution. -/
def involutionExchange (s : I → I) (up : I → Prop) [DecidablePred up] (q : R) :
    Matrix I I R := fun x y =>
  (if y = x then if up x then q else 0 else 0) +
    (if y = s x then if up x then 1 + q else 1 else 0)

private theorem sum_pick (b : I) (f : I → R) :
    (∑ i : I, if i = b then f i else 0) = f b := by
  classical
  simp

private theorem sum_diag_mul (f c : I → R) (b : I) :
    (∑ i : I, f i * (if b = i then c i else 0)) = f b * c b := by
  classical
  simp_rw [mul_ite]
  simpa [eq_comm] using sum_pick b (fun i => f i * c i)

private theorem sum_shift_mul (s : I → I) (hs : ∀ i, s (s i) = i)
    (f c : I → R) (b : I) :
    (∑ i : I, f i * (if b = s i then c i else 0)) = f (s b) * c (s b) := by
  classical
  have hcond (i : I) : (b = s i) ↔ (i = s b) := by
    constructor
    · intro h
      calc
        i = s (s i) := (hs i).symm
        _ = s b := congrArg s h.symm
    · intro h
      calc
        b = s (s b) := (hs b).symm
        _ = s i := (congrArg s h).symm
  simp_rw [mul_ite, hcond]
  simpa using sum_pick (s b) (fun i => f i * c i)

private theorem sum_pick_mul (b : I) (c : R) (f : I → R) :
    (∑ i : I, (if i = b then c else 0) * f i) = c * f b := by
  classical
  simp

/-- Entry formula for right multiplication by the exchange matrix. -/
theorem mul_involutionExchange_entry (s : I → I) (up : I → Prop)
    [DecidablePred up] (q : R) (Z : Matrix I I R) (x y : I)
    (hs : ∀ i, s (s i) = i) (hup : ∀ i, up (s i) ↔ ¬ up i) :
    (Z * involutionExchange s up q) x y =
      (if up y then q else 0) * Z x y +
        (if up y then 1 else 1 + q) * Z x (s y) := by
  classical
  simp only [Matrix.mul_apply, involutionExchange, mul_add, Finset.sum_add_distrib]
  rw [sum_diag_mul, sum_shift_mul s hs]
  simp [hup y]
  ring

/-- Entry formula for left multiplication by the exchange matrix. -/
theorem involutionExchange_mul_entry (s : I → I) (up : I → Prop)
    [DecidablePred up] (q : R) (Z : Matrix I I R) (x y : I)
    (hs : ∀ i, s (s i) = i) (hup : ∀ i, up (s i) ↔ ¬ up i) :
    (involutionExchange s up q * Z) x y =
      (if up x then q else 0) * Z x y +
        (if up x then 1 + q else 1) * Z (s x) y := by
  classical
  simp only [Matrix.mul_apply, involutionExchange, mul_add, Finset.sum_add_distrib]
  rw [sum_pick_mul, sum_pick_mul]

/-- Scalar form of the two exchange relations for an involution. -/
def InvolutionExchangeCompatible (s : I → I) (up : I → Prop) [DecidablePred up]
    (q : R) (Z : Matrix I I R) : Prop :=
  ∀ x y, up x → up y →
    Z x (s y) = (1 + q) * Z (s x) y ∧
      Z x y = Z (s x) (s y) + q * Z (s x) y

/-- The scalar exchange relations are equivalent to commuting with the sparse matrix. -/
theorem involutionExchangeCompatible_iff_commute (s : I → I) (up : I → Prop)
    [DecidablePred up] (q : R) (Z : Matrix I I R)
    (hs : ∀ i, s (s i) = i) (hup : ∀ i, up (s i) ↔ ¬ up i) :
    InvolutionExchangeCompatible s up q Z ↔
      Z * involutionExchange s up q = involutionExchange s up q * Z := by
  constructor
  · intro h
    ext x y
    rw [mul_involutionExchange_entry s up q Z x y hs hup,
      involutionExchange_mul_entry s up q Z x y hs hup]
    by_cases hx : up x <;> by_cases hy : up y
    · obtain ⟨hxy, _⟩ := h x y hx hy
      simp [hx, hy, hxy]
    · have hsy : up (s y) := (hup y).mpr hy
      obtain ⟨hxy, hxy'⟩ := h x (s y) hx hsy
      have hxy'' : Z x y = (1 + q) * Z (s x) (s y) := by
        simpa [hs y] using hxy
      have hxy''' : Z x (s y) = Z (s x) y + q * Z (s x) (s y) := by
        simpa [hs y] using hxy'
      simp [hx, hy, hxy'', hxy''']
      ring
    · have hsx : up (s x) := (hup x).mpr hx
      obtain ⟨_, hxy⟩ := h (s x) y hsx hy
      have hxy' : Z (s x) y = Z x (s y) + q * Z x y := by
        simpa [hs x] using hxy
      simp [hx, hy, hxy']
      ring
    · have hsx : up (s x) := (hup x).mpr hx
      have hsy : up (s y) := (hup y).mpr hy
      obtain ⟨hxy, _⟩ := h (s x) (s y) hsx hsy
      have hxy' : Z (s x) y = (1 + q) * Z x (s y) := by
        simpa [hs x, hs y] using hxy
      simp [hx, hy, hxy']
  · intro h x y hx hy
    have hnsx : ¬ up (s x) := fun h' => (hup x).mp h' hx
    have hnsy : ¬ up (s y) := fun h' => (hup y).mp h' hy
    have h₁ := congrArg (fun M : Matrix I I R => M (s x) y) h
    rw [mul_involutionExchange_entry s up q Z (s x) y hs hup,
      involutionExchange_mul_entry s up q Z (s x) y hs hup] at h₁
    have h₂ := congrArg (fun M : Matrix I I R => M (s x) (s y)) h
    rw [mul_involutionExchange_entry s up q Z (s x) (s y) hs hup,
      involutionExchange_mul_entry s up q Z (s x) (s y) hs hup] at h₂
    constructor
    · simpa [hnsx, hnsy, hx, hy, hs x, hs y] using h₂.symm
    · simpa [hnsx, hx, hy, hs x, hs y, add_comm, add_left_comm, add_assoc] using h₁.symm

/-- Products of scalar-compatible matrices remain scalar-compatible. -/
theorem InvolutionExchangeCompatible.mul (s : I → I) (up : I → Prop)
    [DecidablePred up] (q : R) (Z W : Matrix I I R)
    (hs : ∀ i, s (s i) = i) (hup : ∀ i, up (s i) ↔ ¬ up i)
    (hZ : InvolutionExchangeCompatible s up q Z)
    (hW : InvolutionExchangeCompatible s up q W) :
    InvolutionExchangeCompatible s up q (Z * W) := by
  apply (involutionExchangeCompatible_iff_commute s up q (Z * W) hs hup).2
  have hZ' := (involutionExchangeCompatible_iff_commute s up q Z hs hup).1 hZ
  have hW' := (involutionExchangeCompatible_iff_commute s up q W hs hup).1 hW
  calc
    (Z * W) * involutionExchange s up q = Z * (W * involutionExchange s up q) :=
      Matrix.mul_assoc _ _ _
    _ = Z * (involutionExchange s up q * W) := by rw [hW']
    _ = (Z * involutionExchange s up q) * W := (Matrix.mul_assoc _ _ _).symm
    _ = (involutionExchange s up q * Z) * W := by rw [hZ']
    _ = involutionExchange s up q * (Z * W) := Matrix.mul_assoc _ _ _

end Semiring

end VerticalStripLLT.CyclicHessenberg
