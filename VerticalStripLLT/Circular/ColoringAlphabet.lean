import VerticalStripLLT.AlphabetStability
import VerticalStripLLT.Circular.EdgeColoring

/-! Specializing the final color preserves circular edge-coloring weights. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators

namespace EdgeData

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]

theorem specializeLast_monomial_castSucc (m : ℕ) (c : V → Fin m) :
    specializeLast m (monomial (fun v => (c v).castSucc)) = monomial c := by
  unfold monomial
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro v _
  exact specializeLast_X_castSucc m (c v)

theorem specializeLast_coloringWeight_castSucc (G : EdgeData V E) (m : ℕ)
    (c : V → Fin m) :
    specializeLast m (G.coloringWeight (fun v => (c v).castSucc)) = G.coloringWeight c := by
  classical
  unfold coloringWeight
  have hadm : admissibleColoring G (fun v => (c v).castSucc) ↔
      admissibleColoring G c := by simp [admissibleColoring]
  have hasc : (G.ascentEdges (fun v => (c v).castSucc)).card =
      (G.ascentEdges c).card := rfl
  have hC (p : Q) : specializeLast m (MvPolynomial.C p) = MvPolynomial.C p := by
    simp [specializeLast]
  rw [hadm, hasc]
  split_ifs <;> simp [map_mul, hC, specializeLast_monomial_castSucc]

theorem specializeLast_coloringWeight_eq_zero_of_last (G : EdgeData V E) (m : ℕ)
    (c : V → Fin (m + 1)) (v : V) (hv : c v = Fin.last m) :
    specializeLast m (G.coloringWeight c) = 0 := by
  classical
  unfold coloringWeight
  split_ifs with hadm
  · rw [map_mul, monomial, map_prod]
    have hprod : ∏ x, specializeLast m (MvPolynomial.X (c x)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ v)
      rw [hv, specializeLast_X_last]
    rw [hprod, mul_zero]
  · rfl

end EdgeData
end VerticalStripLLT.Circular
