import VerticalStripLLT.CyclicHessenberg.LayerListBridge
import VerticalStripLLT.CyclicHessenberg.SmallOrders
import VerticalStripLLT.CyclicHessenberg.CycleExpansion
import VerticalStripLLT.CyclicHessenberg.MatchingExpansion

set_option autoImplicit false

/-! Complete two-vertex layers and their repeated open transfer kernel. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

def completeTwo : Hessenberg 2 := Hessenberg.complete (by decide)

def completeTwoTuple (n : ℕ) : Tuple 2 n := fun _ => completeTwo

def fullOrderForwardTwo : FullOrder 2 :=
  ⟨[0, 1], by
    constructor
    · simp
    · ext x
      fin_cases x <;> simp⟩

def fullOrderReverseTwo : FullOrder 2 :=
  ⟨[1, 0], by
    constructor
    · simp
    · ext x
      fin_cases x <;> simp⟩

@[simp] private theorem fullOrderForwardTwo_val :
    fullOrderForwardTwo.val = [0, 1] := rfl

@[simp] private theorem fullOrderReverseTwo_val :
    fullOrderReverseTwo.val = [1, 0] := rfl

private theorem fullOrder_two_cases (π : FullOrder 2) :
    π = fullOrderForwardTwo ∨ π = fullOrderReverseTwo := by
  have hlen : π.val.length = 2 := by simpa using π.property.length
  obtain ⟨x, y, hxy⟩ := List.length_eq_two.mp hlen
  have hmem (z : Fin 2) (hz : z ∈ π.val) : z = 0 ∨ z = 1 := by
    fin_cases z <;> simp_all
  have hx : x ∈ π.val := by rw [hxy]; simp
  have hy : y ∈ π.val := by rw [hxy]; simp
  rcases hmem x hx with hx | hx
  · subst x
    rcases hmem y hy with hy | hy
    · subst y
      have hnodup := π.property.1
      rw [hxy] at hnodup
      simp at hnodup
      exact hnodup.elim
    · subst y
      left
      apply Subtype.ext
      exact hxy
  · subst x
    rcases hmem y hy with hy | hy
    · subst y
      right
      apply Subtype.ext
      exact hxy
    · subst y
      have hnodup := π.property.1
      rw [hxy] at hnodup
      simp at hnodup
      exact hnodup.elim

def completeTwoLayerKernel : Kernel (Polynomial ℕ) (Finset.univ : Finset (Fin 2)) :=
  naturalLayerKernel completeTwo

theorem completeTwoLayerKernel_forward_row (τ : FullOrder 2) :
    completeTwoLayerKernel fullOrderForwardTwo τ = 1 + Polynomial.X := by
  rw [← layerListWeight_eq completeTwo Polynomial.X fullOrderForwardTwo τ]
  rcases fullOrder_two_cases τ with hτ | hτ <;> subst τ
    <;> simp [completeTwoLayerKernel, layerListWeight, layerListFeasible,
      layerListAscentCount, spectatorCount, completeTwo, Hessenberg.complete]

theorem completeTwoLayerKernel_reverse_row (τ : FullOrder 2) :
    completeTwoLayerKernel fullOrderReverseTwo τ = 1 := by
  rw [← layerListWeight_eq completeTwo Polynomial.X fullOrderReverseTwo τ]
  rcases fullOrder_two_cases τ with hτ | hτ <;> subst τ
    <;> simp [completeTwoLayerKernel, layerListWeight, layerListFeasible,
      layerListAscentCount, spectatorCount, completeTwo, Hessenberg.complete]

theorem completeTwoLayerKernel_entry (π τ : FullOrder 2) :
    completeTwoLayerKernel π τ =
      if π = fullOrderForwardTwo then 1 + Polynomial.X else 1 := by
  rcases fullOrder_two_cases π with hπ | hπ
  · subst π
    simp [completeTwoLayerKernel_forward_row]
  · subst π
    have hne : fullOrderReverseTwo ≠ fullOrderForwardTwo := by
      intro h
      have := congrArg Subtype.val h
      simp at this
    simp [completeTwoLayerKernel_reverse_row, hne]

private def fullOrderTwoEquivBool : FullOrder 2 ≃ Bool where
  toFun π := if π.val = [0, 1] then false else true
  invFun b := if b then fullOrderReverseTwo else fullOrderForwardTwo
  left_inv π := by
    rcases fullOrder_two_cases π with h | h
    · apply Subtype.ext
      simpa [h]
    · have hrev : [1, 0] ≠ [0, 1] := by
        intro heq
        have h10 : (1 : Fin 2) = 0 := (List.cons.inj heq).1
        have hne : (1 : Fin 2) ≠ 0 := by decide
        exact hne h10
      apply Subtype.ext
      simp [h, hrev]
  right_inv b := by
    cases b <;> simp [fullOrderForwardTwo_val, fullOrderReverseTwo_val,
      fullOrderForwardTwo, fullOrderReverseTwo]

private theorem sum_fullOrder_two {R : Type*} [AddCommMonoid R]
    (F : FullOrder 2 → R) :
    (∑ π : FullOrder 2, F π) =
      F fullOrderForwardTwo + F fullOrderReverseTwo := by
  classical
  calc
    (∑ π : FullOrder 2, F π) = ∑ b : Bool, F (fullOrderTwoEquivBool.symm b) :=
      (Equiv.sum_comp fullOrderTwoEquivBool.symm F).symm
    _ = F fullOrderForwardTwo + F fullOrderReverseTwo := by
      simp [fullOrderTwoEquivBool]

private theorem completeTwoLayerKernel_mul_self :
    completeTwoLayerKernel * completeTwoLayerKernel =
      (Polynomial.X + 2) • completeTwoLayerKernel := by
  classical
  ext π τ
  rw [Matrix.mul_apply, sum_fullOrder_two]
  by_cases hπ : π = fullOrderForwardTwo
  · subst π
    simp [completeTwoLayerKernel_entry]
    ring
  · simp [completeTwoLayerKernel_entry, hπ]
    ring

theorem completeTwoLayerKernel_pow_succ (n : ℕ) :
    completeTwoLayerKernel ^ (n + 1) =
      (Polynomial.X + 2) ^ n • completeTwoLayerKernel := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, Matrix.smul_mul, completeTwoLayerKernel_mul_self,
        smul_smul]
      simp only [pow_succ]
      congr 1
      ring

theorem completeTwoOpenKernel_eq (n : ℕ) :
    naturalOpenKernel (completeTwoTuple (n + 1)) =
      (Polynomial.X + 2) ^ n • completeTwoLayerKernel := by
  classical
  change (List.ofFn (fun i : Fin (n + 1) =>
    naturalLayerKernel (completeTwoTuple (n + 1) i))).prod = _
  rw [List.ofFn_const, List.prod_replicate, completeTwoLayerKernel_pow_succ]

theorem completeTwoOpenKernel_entry (n : ℕ) (π τ : FullOrder 2) :
    naturalOpenKernel (completeTwoTuple (n + 1)) π τ =
      (Polynomial.X + 2) ^ n * completeTwoLayerKernel π τ := by
  rw [completeTwoOpenKernel_eq]
  rfl

end VerticalStripLLT.CyclicHessenberg
