import VerticalStripLLT.CyclicHessenberg.ColorDeletion
import VerticalStripLLT.CyclicHessenberg.ColorEvaluation
import VerticalStripLLT.CyclicHessenberg.KernelSupport

/-! Evaluate a colored suffix after fixing a valid prefix. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

private theorem wordEval_prefix_shift {V R : Type*} [CommRing R]
    (f : List V → R) (p : List V) (A : WordSum R V) :
    wordEval f p [] A = wordEval (fun w => f (p ++ w)) [] [] A := by
  induction A using MonoidAlgebra.induction_on with
  | of w =>
    change wordEval f p [] (wordTerm (R := R) w.toList) =
      wordEval (fun w => f (p ++ w)) [] [] (wordTerm (R := R) w.toList)
    simp [wordEval_term]
  | add A B hA hB => simp only [map_add, hA, hB]
  | smul c A hA => simp only [map_smul, hA]

/-- A valid fixed prefix leaves the residual colorings of the complementary support. -/
theorem colorClassProduct_prefix_eval {V R : Type*} [LinearOrder V] [CommRing R]
    (S U T : Finset V) (hUS : U ⊆ S) (p : Order U) (hUT : S \ U ⊆ T)
    {m : ℕ} (weight : Fin m → R) (f : List V → R)
    (hf : ∀ w, ¬ IsOrder S w → f w = 0) :
    wordEval f [] [] (wordTerm p.val * colorClassProduct T.sort (List.ofFn weight)) =
      ∑ κ : ↥(S \ U) → Fin m, (∏ v, weight (κ v)) *
        f (p.val ++ (sortColorOrder κ).val) := by
  classical
  let f' : List V → R := fun w => f (p.val ++ w)
  have hf' : ∀ w, ¬ IsOrder (S \ U) w → f' w = 0 :=
    supported_prefix S U hUS p f hf
  have heval := colorClassProduct_eval_of_subset (S \ U) T hUT weight f' hf'
  generalize hG : colorClassProduct T.sort (List.ofFn weight) = G at heval ⊢
  calc
    wordEval f [] [] (wordTerm p.val * G) = wordEval f p.val [] G := by
      simpa only [List.nil_append] using
        (wordEval_term_mul f [] [] p.val G)
    _ = wordEval f' [] [] G :=
      wordEval_prefix_shift f p.val _
    _ = ∑ κ : ↥(S \ U) → Fin m, (∏ v, weight (κ v)) *
          f (p.val ++ (sortColorOrder κ).val) := by
      exact heval

/-- A mountain block followed by a color product evaluates as a signed
root-deletion coloring sum. -/
theorem mountainWordSum_mul_eval {V R : Type*} [LinearOrder V] [CommRing R]
    {S : Finset V} (Z : List V → List V → R) (hZ : SupportedKernel S Z)
    (U : Finset V) (r : V) (hr : r ∉ U) (hU : insert r U ⊆ S)
    (T : Finset V) (hAT : S \ insert r U ⊆ T) {m : ℕ}
    (weight : Fin m → R) :
    wordEval (fun w => Z w w) [] []
        (mountainWordSum U r * colorClassProduct T.sort (List.ofFn weight)) =
      ∑ κ : ↥(S \ insert r U) → Fin m, (∏ a, weight (κ a)) *
        signedRootDeletion Z (insert r U) r (sortColorOrder κ).val
          (sortColorOrder κ).val := by
  classical
  let A : Finset V := S \ insert r U
  let f : List V → R := fun w => Z w w
  have hf : ∀ w, ¬ IsOrder S w → f w = 0 := by
    intro w hw
    exact hZ w w (Or.inl hw)
  let mountain (B : Finset V) : List V :=
    (U \ B).sort ++ [r] ++ B.sort (· ≥ ·)
  have hterm (B : Finset V) (hB : B ⊆ U) :
      wordEval f [] []
          (wordTerm (R := R) (mountain B) *
            colorClassProduct T.sort (List.ofFn weight)) =
        ∑ κ : A → Fin m, (∏ a : A, weight (κ a)) *
          Z (mountain B ++ (sortColorOrder κ).val)
            (mountain B ++ (sortColorOrder κ).val) := by
    have horder : IsOrder (insert r U) (mountain B) := by
      simpa only [mountain] using (mountain_isOrder U B r hr hB)
    have heval := colorClassProduct_prefix_eval S (insert r U) T hU
      ⟨mountain B, horder⟩ hAT weight f hf
    simpa only [f] using heval
  have hdelete (w : List V) :
      (∑ B ∈ U.powerset, (-1 : R) ^ B.card *
        Z (mountain B ++ w) (mountain B ++ w)) =
        signedRootDeletion Z (insert r U) r w w := by
    have heval := mountainWordSum_eval Z U r hr w w
    simpa only [mountainWordSum, mountain, map_sum, map_smul, wordEval_term,
      List.nil_append, List.append_nil, smul_eq_mul] using heval
  have hexpand :
      wordEval f [] []
          (mountainWordSum U r * colorClassProduct T.sort (List.ofFn weight)) =
        ∑ B ∈ U.powerset, (-1 : R) ^ B.card •
          ∑ κ : A → Fin m, (∏ a : A, weight (κ a)) *
            Z (mountain B ++ (sortColorOrder κ).val)
              (mountain B ++ (sortColorOrder κ).val) := by
    simp only [mountainWordSum, mountain, Finset.sum_mul, map_sum, map_smul,
      smul_mul_assoc]
    apply Finset.sum_congr rfl
    intro B hB
    rw [hterm B (Finset.mem_powerset.mp hB)]
  have hswap :
      (∑ B ∈ U.powerset, (-1 : R) ^ B.card •
        ∑ κ : A → Fin m, (∏ a : A, weight (κ a)) *
          Z (mountain B ++ (sortColorOrder κ).val)
            (mountain B ++ (sortColorOrder κ).val)) =
      ∑ κ : A → Fin m, (∏ a : A, weight (κ a)) *
        ∑ B ∈ U.powerset, (-1 : R) ^ B.card *
          Z (mountain B ++ (sortColorOrder κ).val)
            (mountain B ++ (sortColorOrder κ).val) := by
    simp only [Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro κ hκ
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B hB
    simp only [smul_eq_mul]
    ring
  calc
    wordEval f [] []
        (mountainWordSum U r * colorClassProduct T.sort (List.ofFn weight)) =
        ∑ κ : A → Fin m, (∏ a : A, weight (κ a)) *
          ∑ B ∈ U.powerset, (-1 : R) ^ B.card *
            Z (mountain B ++ (sortColorOrder κ).val)
              (mountain B ++ (sortColorOrder κ).val) := hexpand.trans hswap
    _ = ∑ κ : A → Fin m, (∏ a : A, weight (κ a)) *
          signedRootDeletion Z (insert r U) r (sortColorOrder κ).val
            (sortColorOrder κ).val := by
      apply Finset.sum_congr rfl
      intro κ hκ
      rw [hdelete (sortColorOrder κ).val]

end VerticalStripLLT.CyclicHessenberg
