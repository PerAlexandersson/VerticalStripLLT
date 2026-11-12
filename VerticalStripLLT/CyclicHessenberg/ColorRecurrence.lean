import VerticalStripLLT.CyclicHessenberg.WeightedColoring
import VerticalStripLLT.CyclicHessenberg.ColorMissing
import VerticalStripLLT.CyclicHessenberg.ColorPrefixEvaluation

/-! The positive deletion recurrence for the independently defined finite coloring sum. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {V R : Type*} [LinearOrder V] [CommRing R]

/-- Delete a subset together with the largest root. All color sums retain their direct semantics. -/
theorem weightedKernelColoring_insert_max (S : Finset V) (r : V)
    (hr : ∀ a ∈ S, a < r) (q : R) (Z : List V → List V → R)
    (hZ : ListExchangeCompatible q Z) (hs : SupportedKernel (insert r S) Z)
    {m : ℕ} (weight : Fin m → R) :
    weightedKernelColoring (insert r S) Z weight =
      ∑ U ∈ S.powerset, elementaryWeights (List.ofFn weight) (U.card + 1) *
        weightedKernelColoring ((insert r S) \ (insert r U))
          (rootDeletion q Z (insert r U) r) weight := by
  classical
  have hrS : r ∉ S := fun h => (lt_irrefl r) (hr r h)
  let f : List V → R := fun w => Z w w
  let Y := List.ofFn weight
  let G := colorClassProduct S.sort Y
  have hf : ∀ w, ¬ IsOrder (insert r S) w → f w = 0 :=
    fun w hw => hs w w (Or.inl hw)
  have hrep : ∀ w, ¬ w.Nodup → f w = 0 := hs.diagonal_repeated
  have hdegree : ∀ w : List V, S.card + 1 < w.length → f w = 0 := by
    intro w hw
    apply hs.diagonal_degree
    simpa only [Finset.card_insert_of_notMem hrS] using hw
  have hbalance : ContextualBalance f := hZ.diagonal_contextualBalance
  have hmissing : wordEval f [] [] G = 0 :=
    colorClassProduct_eval_missing (insert r S) S r (Finset.mem_insert_self _ _)
      hrS weight f hf
  have hfactor := (colorClassProduct_insert_root f hrep S.sort r Y).eval
  have hinsertion := ((colorInsertion_eq_mountainSum f hbalance hrep S r hr hdegree Y)
    .mul_right G).eval
  calc
    weightedKernelColoring (insert r S) Z weight =
        wordEval f [] [] (colorClassProduct (S.sort ++ [r]) Y) := by
      rw [weightedKernelColoring_eq_classProduct _ _ hs, sort_insert_max S r hr]
    _ = wordEval f [] [] (colorInsertion S.sort r Y * G) := by
      rw [hfactor]
      simp only [add_mul, one_mul, map_add, hmissing, zero_add]
    _ = ∑ U ∈ S.powerset, elementaryWeights Y (U.card + 1) *
          wordEval f [] [] (mountainWordSum U r * G) := by
      simpa only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, smul_eq_mul]
        using hinsertion
    _ = _ := by
      apply Finset.sum_congr rfl
      intro U hU
      have hUS : U ⊆ S := Finset.mem_powerset.mp hU
      have hrU : r ∉ U := fun h => hrS (hUS h)
      have hfull : insert r U ⊆ insert r S := Finset.insert_subset_insert hUS
      have hremaining : (insert r S) \ (insert r U) ⊆ S := by
        intro a ha
        obtain ⟨haS, haU⟩ := Finset.mem_sdiff.mp ha
        rcases Finset.mem_insert.mp haS with rfl | haS
        · exact False.elim (haU (Finset.mem_insert_self _ _))
        · exact haS
      congr 1
      rw [mountainWordSum_mul_eval Z hs U r hrU hfull S hremaining weight]
      unfold weightedKernelColoring
      apply Finset.sum_congr rfl
      intro κ hκ
      rw [signedRootDeletion_eq_rootDeletion hZ (insert r U) r
        (Finset.mem_insert_self _ _)]
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact le_rfl
      · exact (hr a (hUS ha)).le

end VerticalStripLLT.CyclicHessenberg
