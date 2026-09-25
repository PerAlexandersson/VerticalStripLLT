import VerticalStripLLT.SwapSum
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace VerticalStripLLT

theorem coloringWeight_insert_edges {n m : ℕ} (P B : SchroderPath n)
    (en es : Fin n × Fin n)
    (hPn : P.normalEdges = insert en B.normalEdges)
    (hPs : P.strictEdges = insert es B.strictEdges)
    (hfresh : en ∉ B.normalEdges) (c : Fin n → Fin m) :
    coloringWeight P c =
      if c es.1 < c es.2 then
        (if c en.1 < c en.2 then MvPolynomial.C Polynomial.X * coloringWeight B c
          else coloringWeight B c)
      else 0 := by
  classical
  have hadm : admissible P c ↔ c es.1 < c es.2 ∧ admissible B c := by
    simp [admissible, hPs]
  by_cases hs : c es.1 < c es.2
  · rw [ite_eq_left hs]
    by_cases hn : c en.1 < c en.2
    · have hA : ascentCount P c = ascentCount B c + 1 := by
        simp [ascentCount, hPn, Finset.filter_insert, hn, hfresh]
      rw [ite_eq_left hn]
      unfold coloringWeight
      by_cases hB : admissible B c
      · rw [ite_eq_left (hadm.2 ⟨hs, hB⟩), ite_eq_left hB, hA, pow_succ, MvPolynomial.C_mul]
        ring
      · rw [ite_eq_right (fun h => hB (hadm.1 h).2), ite_eq_right hB, mul_zero]
    · have hA : ascentCount P c = ascentCount B c := by
        simp [ascentCount, hPn, Finset.filter_insert, hn]
      rw [ite_eq_right hn]
      unfold coloringWeight
      by_cases hB : admissible B c
      · rw [ite_eq_left (hadm.2 ⟨hs, hB⟩), ite_eq_left hB, hA]
      · rw [ite_eq_right (fun h => hB (hadm.1 h).2), ite_eq_right hB]
  · rw [ite_eq_right hs]
    unfold coloringWeight
    rw [ite_eq_right (fun h => hs (hadm.1 h).1)]

theorem coloringWeight_insert_strict {n m : ℕ} (P B : SchroderPath n)
    (es : Fin n × Fin n)
    (hPn : P.normalEdges = B.normalEdges)
    (hPs : P.strictEdges = insert es B.strictEdges) (c : Fin n → Fin m) :
    coloringWeight P c = if c es.1 < c es.2 then coloringWeight B c else 0 := by
  classical
  have hadm : admissible P c ↔ c es.1 < c es.2 ∧ admissible B c := by
    simp [admissible, hPs]
  have hA : ascentCount P c = ascentCount B c := by simp [ascentCount, hPn]
  unfold coloringWeight
  by_cases hs : c es.1 < c es.2
  · rw [ite_eq_left hs]
    by_cases hB : admissible B c
    · rw [ite_eq_left (hadm.2 ⟨hs, hB⟩), ite_eq_left hB, hA]
    · rw [ite_eq_right (fun h => hB (hadm.1 h).2), ite_eq_right hB]
  · rw [ite_eq_right hs, ite_eq_right (fun h => hs (hadm.1 h).1)]

theorem coloringLLT_eq_C_X_mul_of_edges {n m : ℕ} (P Q B : SchroderPath n) (i y z : Fin n)
    (hPn : P.normalEdges = insert (y, z) B.normalEdges)
    (hPs : P.strictEdges = insert (i, z) B.strictEdges)
    (hQn : Q.normalEdges = B.normalEdges)
    (hQs : Q.strictEdges = insert (y, z) B.strictEdges)
    (hfresh : (y, z) ∉ B.normalEdges)
    (hiy : (i, y) ∈ B.normalEdges)
    (hs : B.strictEdges.map (swapVertexPair i y) = B.strictEdges)
    (hn : (B.normalEdges.erase (i, y)).map (swapVertexPair i y) =
      B.normalEdges.erase (i, y))
    (hzi : z ≠ i) (hzy : z ≠ y) :
    coloringLLT P m = MvPolynomial.C Polynomial.X * coloringLLT Q m := by
  classical
  -- `T c = c` when both `c i, c y` lie below `c z`, and the swapped coloring otherwise.
  let T : (Fin n → Fin m) → (Fin n → Fin m) := fun c =>
    if c i < c z ∧ c y < c z then c else swapColors i y c
  have hswz : ∀ c : Fin n → Fin m, swapColors i y c z = c z := fun c =>
    swapColors_apply_of_ne_of_ne i y z c hzi hzy
  have hT : Function.Involutive T := by
    intro c
    by_cases hc : c i < c z ∧ c y < c z
    · simp only [T, ite_eq_left hc]
    · have hc' : ¬ (swapColors i y c i < swapColors i y c z ∧
          swapColors i y c y < swapColors i y c z) := by
        rw [swapColors_apply_left, swapColors_apply_right, hswz]
        exact fun h => hc ⟨h.2, h.1⟩
      simp only [T, ite_eq_right hc, ite_eq_right hc', swapColors_involutive]
  have hQw : ∀ d : Fin n → Fin m, coloringWeight Q d =
      if d y < d z then coloringWeight B d else 0 :=
    coloringWeight_insert_strict Q B (y, z) hQn hQs
  have hpt : ∀ c : Fin n → Fin m,
      coloringWeight P c = MvPolynomial.C Polynomial.X * coloringWeight Q (T c) := by
    intro c
    rw [coloringWeight_insert_edges P B (y, z) (i, z) hPn hPs hfresh c]
    dsimp only
    by_cases h1 : c i < c z
    · rw [ite_eq_left h1]
      by_cases h2 : c y < c z
      · rw [ite_eq_left h2]
        simp only [T, ite_eq_left (And.intro h1 h2), hQw, ite_eq_left h2]
      · rw [ite_eq_right h2]
        have hT' : T c = swapColors i y c := ite_eq_right (fun h : c i < c z ∧ c y < c z => h2 h.2)
        rw [hT', hQw, swapColors_apply_right, hswz, ite_eq_left h1]
        exact coloringWeight_eq_C_X_mul_swapColors B i y hiy hs hn c
          (lt_of_lt_of_le h1 (not_lt.mp h2))
    · rw [ite_eq_right h1]
      have hT' : T c = swapColors i y c := ite_eq_right (fun h : c i < c z ∧ c y < c z => h1 h.1)
      rw [hT', hQw, swapColors_apply_right, hswz, ite_eq_right h1, mul_zero]
  unfold coloringLLT
  rw [Finset.mul_sum]
  rw [← Equiv.sum_comp (Function.Involutive.toPerm T hT)
    (fun d => MvPolynomial.C Polynomial.X * coloringWeight Q d)]
  exact Finset.sum_congr rfl fun c _ => hpt c

end VerticalStripLLT
