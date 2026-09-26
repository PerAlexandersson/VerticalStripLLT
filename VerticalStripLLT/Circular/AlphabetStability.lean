import VerticalStripLLT.Circular.ColoringAlphabet
import VerticalStripLLT.Circular.Coloring

/-! Alphabet specialization directly from the coloring sum, without an expansion theorem. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators

namespace EdgeData

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Setting the last alphabet variable to zero removes precisely the colorings using it. -/
theorem specializeLast_coloringLLT (G : EdgeData V E) (m : ℕ) :
    specializeLast m (G.coloringLLT (m + 1)) = G.coloringLLT m := by
  classical
  let lift : (V → Fin m) → (V → Fin (m + 1)) := fun c v => (c v).castSucc
  have hinj : Function.Injective lift := by
    intro c d h
    funext v
    exact Fin.castSucc_inj.mp (congrFun h v)
  have hzero (c : V → Fin (m + 1))
      (hc : c ∉ (Finset.univ : Finset (V → Fin m)).image lift) :
      specializeLast m (G.coloringWeight c) = 0 := by
    have hlast : ∃ v, c v = Fin.last m := by
      by_contra h
      push Not at h
      let d : V → Fin m := fun v => ⟨(c v).val, Fin.lt_last_iff_ne_last.mpr (h v)⟩
      apply hc
      refine Finset.mem_image.mpr ⟨d, Finset.mem_univ _, ?_⟩
      funext v
      exact Fin.ext rfl
    obtain ⟨v, hv⟩ := hlast
    exact G.specializeLast_coloringWeight_eq_zero_of_last m c v hv
  unfold coloringLLT
  rw [map_sum]
  calc
    (∑ c : V → Fin (m + 1), specializeLast m (G.coloringWeight c)) =
        ∑ c ∈ (Finset.univ : Finset (V → Fin m)).image lift,
          specializeLast m (G.coloringWeight c) := by
      symm
      exact Finset.sum_subset (Finset.subset_univ _) (fun c _ hc => hzero c hc)
    _ = ∑ c : V → Fin m, specializeLast m (G.coloringWeight (lift c)) :=
      Finset.sum_image hinj.injOn
    _ = ∑ c : V → Fin m, G.coloringWeight c := by
      apply Finset.sum_congr rfl
      intro c _
      exact G.specializeLast_coloringWeight_castSucc m c

end EdgeData

namespace Diagram

/-- Every circular coloring polynomial is compatible with removing the last variable. -/
theorem specializeLast_coloringLLT {n : ℕ} (D : Diagram n) (m : ℕ) :
    specializeLast m (D.coloringLLT (m + 1)) = D.coloringLLT m :=
  D.edgeData.specializeLast_coloringLLT m

end Diagram

end VerticalStripLLT.Circular
