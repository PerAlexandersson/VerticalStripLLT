import VerticalStripLLT.Coloring
import Mathlib.Tactic.Ring

/-! The local weight identity under explicit normal/strict edge insertion hypotheses. -/

namespace VerticalStripLLT

open scoped BigOperators

theorem coloringWeight_unicellular_of_edges {n m : ℕ}
    (P Q R : SchroderPath n) (e : Fin n × Fin n) (c : Fin n → Fin m)
    (hPn : P.normalEdges = insert e Q.normalEdges)
    (hRn : R.normalEdges = Q.normalEdges)
    (hPs : P.strictEdges = Q.strictEdges)
    (hRs : R.strictEdges = insert e Q.strictEdges)
    (he : e ∉ Q.normalEdges) :
    coloringWeight P c - coloringWeight Q c =
      MvPolynomial.C (Polynomial.X - 1) * coloringWeight R c := by
  classical
  let t : Prop := c e.1 < c e.2
  have hP_adm : admissible P c ↔ admissible Q c := by
    simp [admissible, hPs]
  have hR_adm : admissible R c ↔ admissible Q c ∧ t := by
    simp [admissible, hRs, t, and_comm]
  have hA_R : ascentCount R c = ascentCount Q c := by
    simp [ascentCount, hRn]
  have hA_P_false : ¬t → ascentCount P c = ascentCount Q c := by
    intro ht
    change ¬c e.1 < c e.2 at ht
    simp [ascentCount, hPn, Finset.filter_insert, ht]
  have hA_P_true : t → ascentCount P c = ascentCount Q c + 1 := by
    intro ht
    change c e.1 < c e.2 at ht
    simp [ascentCount, hPn, Finset.filter_insert, he, ht]
  by_cases hQ : admissible Q c
  · by_cases ht : t
    · have hP : admissible P c := hP_adm.mpr hQ
      have hR : admissible R c := hR_adm.mpr ⟨hQ, ht⟩
      have hAP := hA_P_true ht
      have hAR := hA_R
      simp only [coloringWeight, hP, hQ, hR, ↓reduceIte, hAP, hAR]
      rw [pow_succ]
      simp only [map_sub, map_one, map_mul]
      ring
    · have hP : admissible P c := hP_adm.mpr hQ
      have hR : ¬admissible R c := by
        intro hR
        exact ht (hR_adm.mp hR).2
      have hAP := hA_P_false ht
      simp only [coloringWeight, hP, hQ, hR, ↓reduceIte, hAP]
      ring
  · have hP : ¬admissible P c := fun h => hQ (hP_adm.mp h)
    have hR : ¬admissible R c := fun h => hQ (hR_adm.mp h).1
    simp [coloringWeight, hP, hQ, hR]

end VerticalStripLLT
