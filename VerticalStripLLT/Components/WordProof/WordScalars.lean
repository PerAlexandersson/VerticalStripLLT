import VerticalStripLLT.Components.WordProof.WordGenerators
import Mathlib.RingTheory.TensorProduct.Basic

/-! Scalar extension of the contextual word algebra. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace VerticalStripLLT.Components

open scoped TensorProduct

noncomputable section

variable {V : Type*} [LinearOrder V]

local instance scalarWordTensorRing (K : Type*) [CommRing K] : Ring (K ⊗[ℤ] WordAlgebra V) :=
  Algebra.TensorProduct.instRing

/-- The image of a word in the scalar extension of the word algebra. -/
def scalarWord (K : Type*) [CommRing K] (w : List V) :
    K ⊗[ℤ] WordAlgebra V :=
  (1 : K) ⊗ₜ[ℤ] algebraWord w

@[simp]
theorem scalarWord_append (K : Type*) [CommRing K] (w v : List V) :
    scalarWord K (w ++ v) = scalarWord K w * scalarWord K v := by
  simp [scalarWord, algebraWord_append, Algebra.TensorProduct.tmul_mul_tmul]

theorem scalarWord_repeated (K : Type*) [CommRing K] (w : List V)
    (hw : ¬w.Nodup) : scalarWord K w = 0 := by
  simp [scalarWord, algebraWord_repeated w hw]

theorem scalarWord_sandwich (K : Type*) [CommRing K] (a : V)
    (Y : K ⊗[ℤ] WordAlgebra V) :
    scalarWord K [a] * Y * scalarWord K [a] = 0 := by
  induction Y using TensorProduct.inductionOn with
  | tmul k y =>
    simp [scalarWord, Algebra.TensorProduct.tmul_mul_tmul,
      algebraWord_sandwich]
  | add x y hx hy =>
    rw [mul_add, add_mul, hx, hy, add_zero]

theorem scalarWord_triple (K : Type*) [CommRing K] (a b c : V)
    (hab : a < b) (hbc : b < c) :
    scalarWord K [b] * (scalarWord K [a] * scalarWord K [c] -
        scalarWord K [c] * scalarWord K [a]) -
      (scalarWord K [a] * scalarWord K [c] -
        scalarWord K [c] * scalarWord K [a]) * scalarWord K [b] = 0 := by
  simpa only [scalarWord, ← TensorProduct.tmul_sub,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.tmul_zero] using
    congrArg (fun z : WordAlgebra V => (1 : K) ⊗ₜ[ℤ] z)
      (algebraWord_triple a b c hab hbc)

theorem scalarWord_algebraMap_commutes (K : Type*) [CommRing K] (k : K)
    (x : K ⊗[ℤ] WordAlgebra V) :
    Commute (algebraMap K (K ⊗[ℤ] WordAlgebra V) k) x := by
  exact Algebra.commutes k x

/-- Extend an integer-linear word functional to the scalar tensor algebra. -/
def scalarWordFunctional (K : Type*) [CommRing K]
    (f : WordQuotient V →ₗ[ℤ] ℤ) :
    K ⊗[ℤ] WordAlgebra V →ₗ[K] K :=
  LinearMap.liftBaseChange K
    ((Algebra.linearMap ℤ K).comp
      (f.comp wordAlgebraEquiv.toLinearMap))

@[simp]
theorem scalarWordFunctional_tmul (K : Type*) [CommRing K]
    (f : WordQuotient V →ₗ[ℤ] ℤ) (a : K) (x : WordAlgebra V) :
    scalarWordFunctional K f (a ⊗ₜ[ℤ] x) =
      a * algebraMap ℤ K (f (wordAlgebraEquiv x)) := by
  simp [scalarWordFunctional]

@[simp]
theorem scalarWordFunctional_tmul_algebraWord (K : Type*) [CommRing K]
    (f : WordQuotient V →ₗ[ℤ] ℤ) (a : K) (w : List V) :
    scalarWordFunctional K f (a ⊗ₜ[ℤ] algebraWord w) =
      a * algebraMap ℤ K (f (wordAlgebraEquiv (algebraWord w))) := by
  exact scalarWordFunctional_tmul K f a (algebraWord w)

end

end VerticalStripLLT.Components
