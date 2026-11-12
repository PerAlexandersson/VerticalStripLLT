import VerticalStripLLT.CyclicHessenberg.ExpansionRootSum
import VerticalStripLLT.CyclicHessenberg.ColorRecurrence
import VerticalStripLLT.CyclicHessenberg.ColorElementaryWeights

set_option autoImplicit false

/-! Identify the natural deletion expansion with the actual weighted coloring sum. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

/-- Evaluating the natural deletion expression gives the independently defined
weighted coloring sum. -/
theorem naturalKernelExpansion_eval_eq_weightedKernelColoring
    {V R : Type*} [LinearOrder V] [CommRing R]
    (S : Finset V) (Z : List V → List V → Polynomial ℕ)
    (hZ : ListExchangeCompatible Polynomial.X Z) (hs : SupportedKernel S Z)
    {m : ℕ} (weight : Fin m → R) (φ : Polynomial ℕ →+* R) :
    MvPolynomial.eval₂Hom φ
        (fun d : ℕ+ => elementaryWeights (List.ofFn weight) d.val)
        (naturalKernelExpansion S Z) =
      weightedKernelColoring S (fun l t => φ (Z l t)) weight := by
  classical
  let eval : NEExpansion →+* R := MvPolynomial.eval₂Hom φ
    (fun d : ℕ+ => elementaryWeights (List.ofFn weight) d.val)
  have hStrong : ∀ S : Finset V,
      ∀ Z : List V → List V → Polynomial ℕ,
        ListExchangeCompatible Polynomial.X Z → SupportedKernel S Z →
          eval (naturalKernelExpansion S Z) =
            weightedKernelColoring S (fun l t => φ (Z l t)) weight := by
    intro S
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      intro Z hZ hs
      by_cases hS : S.Nonempty
      · let r := S.max' hS
        let T := S.erase r
        have hrS : r ∈ S := by
          exact Finset.max'_mem S hS
        have hST : insert r T = S := Finset.insert_erase hrS
        have hrT : ∀ a ∈ T, a < r := by
          intro a ha
          rcases Finset.mem_erase.mp ha with ⟨hne, haS⟩
          exact lt_of_le_of_ne (Finset.le_max' S a haS) hne
        have hsInsert : SupportedKernel (insert r T) Z := by
          rw [hST]
          exact hs
        have hcolorRec := weightedKernelColoring_insert_max T r hrT
          (φ Polynomial.X) (fun l t => φ (Z l t)) (hZ.map φ) (hsInsert.map φ) weight
        have hnatRec := naturalKernelExpansion_insert_max T r hrT Z
        have hEvalRec :
            eval (naturalKernelExpansion (insert r T) Z) =
              ∑ U ∈ T.powerset, elementaryWeights (List.ofFn weight) (U.card + 1) *
                weightedKernelColoring ((insert r T) \ (insert r U))
                  (fun l t => φ (rootDeletion Polynomial.X Z (insert r U) r l t))
                  weight := by
          rw [hnatRec]
          simp only [map_sum, map_mul]
          apply Finset.sum_congr rfl
          intro U hU
          have hUsub : U ⊆ T := Finset.mem_powerset.mp hU
          have hfull : insert r U ⊆ insert r T := Finset.insert_subset_insert r hUsub
          have hstrict : (insert r T) \ (insert r U) ⊂ insert r T :=
            Finset.sdiff_ssubset hfull ⟨r, Finset.mem_insert_self _ _⟩
          have hstrictS : (insert r T) \ (insert r U) ⊂ S := by
            rw [← hST]
            exact hstrict
          have hZ' := rootDeletion_exchangeCompatible hZ (insert r U) r
          have hs' := hsInsert.rootDeletion Polynomial.X (insert r U) hfull r
            (Finset.mem_insert_self _ _)
          rw [ih ((insert r T) \ (insert r U)) hstrictS
            (rootDeletion Polynomial.X Z (insert r U) r) hZ' hs']
          simp only [eval, natElementary, MvPolynomial.eval₂Hom_X']
        have hrootMap (U : Finset V) :
            (fun l t => φ (rootDeletion Polynomial.X Z (insert r U) r l t)) =
              rootDeletion (φ Polynomial.X) (fun l t => φ (Z l t))
                (insert r U) r := by
          funext l t
          exact rootDeletion_map φ Polynomial.X Z (insert r U) r l t
        have hEvalRec' :
            eval (naturalKernelExpansion (insert r T) Z) =
              ∑ U ∈ T.powerset, elementaryWeights (List.ofFn weight) (U.card + 1) *
                weightedKernelColoring ((insert r T) \ (insert r U))
                  (rootDeletion (φ Polynomial.X) (fun l t => φ (Z l t))
                    (insert r U) r) weight := by
          rw [hEvalRec]
          apply Finset.sum_congr rfl
          intro U hU
          rw [hrootMap U]
        calc
          eval (naturalKernelExpansion S Z) =
              eval (naturalKernelExpansion (insert r T) Z) := by rw [hST]
          _ = weightedKernelColoring (insert r T) (fun l t => φ (Z l t)) weight :=
            hEvalRec'.trans hcolorRec.symm
          _ = weightedKernelColoring S (fun l t => φ (Z l t)) weight := by rw [hST]
      · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
        subst S
        simp [eval, naturalKernelExpansion_empty, weightedKernelColoring_empty]
  simpa only [eval] using hStrong S Z hZ hs

end VerticalStripLLT.CyclicHessenberg
