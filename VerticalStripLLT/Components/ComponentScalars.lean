import VerticalStripLLT.Components.WordScalars
import VerticalStripLLT.Components.ComponentFunctional
import VerticalStripLLT.Circular.EdgeColoring

/-! Scalar extension of the actual component word functional. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace VerticalStripLLT.Components

open Circular
open scoped TensorProduct

noncomputable section

variable {n : ℕ} {D : Diagram n}

local instance componentTensorRing (K : Type*) [CommRing K] :
    Ring (K ⊗[ℤ] WordAlgebra (Fin n)) :=
  Algebra.TensorProduct.instRing

/- The quotient representative of a concrete word is useful when applying
the scalar extension to the component functional. -/
theorem wordAlgebraEquiv_algebraWord {V : Type*} [LinearOrder V]
    (w : List V) :
    wordAlgebraEquiv (V := V) (algebraWord w) =
      (wordRelations (V := V)).mkQ (basisWord w) := by
  change algebraCoefficients (wordProjection (wordMonomial w)) = _
  rw [algebraCoefficients_projection, wordCoefficients_wordMonomial]

/-! The component functional after extension of scalars. -/
def componentScalarEval (K : Type*) [CommRing K]
    (θ : Circular.Orientation D)
    (hforward : ∀ e : Edge D.area, e.tail < e.head) :
    K ⊗[ℤ] WordAlgebra (Fin n) →ₗ[K] K :=
  scalarWordFunctional (V := Fin n) K
    (componentWordFunctional θ hforward)

@[simp]
theorem componentScalarEval_tmul_algebraWord (K : Type*) [CommRing K]
    (θ : Circular.Orientation D)
    (hforward : ∀ e : Edge D.area, e.tail < e.head)
    (a : K) (w : List (Fin n)) :
    componentScalarEval K θ hforward
        (a ⊗ₜ[ℤ] algebraWord w) =
      a * algebraMap ℤ K (componentWordCount D θ w) := by
  rw [componentScalarEval, scalarWordFunctional_tmul_algebraWord,
    wordAlgebraEquiv_algebraWord,
    componentWordFunctional_mk_basisWord]

@[simp]
theorem componentScalarEval_scalarWord (K : Type*) [CommRing K]
    (θ : Circular.Orientation D)
    (hforward : ∀ e : Edge D.area, e.tail < e.head)
    (w : List (Fin n)) :
    componentScalarEval K θ hforward (scalarWord (V := Fin n) K w) =
      algebraMap ℤ K (componentWordCount D θ w) := by
  rw [scalarWord, componentScalarEval_tmul_algebraWord]
  simp

end

end VerticalStripLLT.Components

namespace VerticalStripLLT.Circular.EdgeData

open scoped BigOperators Classical

variable {V E : Type*}

/-! Rewrite strict admissibility using the selected relation rather than edge
representatives. -/
theorem strictOrderEnumerator_eq_selected_sum
    [Fintype V] [DecidableEq V] [DecidableEq E]
    (G : EdgeData V E) (A : Finset E) (m : ℕ) :
    G.strictOrderEnumerator A m =
      ∑ c : V → Fin m,
        if ∀ u v, G.selected A u v → c u < c v then
          monomial c else 0 := by
  classical
  unfold EdgeData.strictOrderEnumerator
  apply Finset.sum_congr rfl
  intro c hc
  have hiff :
      (∀ e ∈ G.strict ∪ A, c (G.tail e) < c (G.head e)) ↔
        ∀ u v, G.selected A u v → c u < c v := by
    constructor
    · intro he u v huv
      exact G.lt_of_selected A c he huv
    · intro he e he_mem
      exact he (G.tail e) (G.head e) ⟨e, he_mem, rfl, rfl⟩
  exact ite_congr (propext hiff) (fun _ => rfl) (fun _ => rfl)

end VerticalStripLLT.Circular.EdgeData
