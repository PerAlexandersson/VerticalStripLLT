import VerticalStripLLT.Recursion
import VerticalStripLLT.PathSplit
import VerticalStripLLT.NonemptyPath
import VerticalStripLLT.PrefixScanners

namespace VerticalStripLLT

namespace Step

/-- East count of a concatenation. -/
theorem eastCount_append (U V : List Step) :
    eastCount (U ++ V) = eastCount U + eastCount V := by
  simp [eastCount, List.count_append]

/-- East count of a word beginning with an east step. -/
theorem eastCount_cons_east (W : List Step) :
    eastCount (east :: W) = eastCount W + 1 := by
  simp [eastCount]

/-- A word with no east step has east count zero. -/
theorem eastCount_eq_zero_of_not_mem {U : List Step} (hU : east ∉ U) :
    eastCount U = 0 := by
  simpa only [eastCount] using List.count_eq_zero_of_not_mem hU

/-- A word with positive east count contains an east step. -/
theorem east_mem_of_eastCount_pos {W : List Step} (hW : 0 < eastCount W) :
    east ∈ W := by
  unfold eastCount at hW
  exact List.count_pos_iff.mp hW

/-- If the prefix ends one unit above the diagonal, appending an east step
returns to the diagonal. -/
theorem endpointFrom_append_east_of_gap (x y : ℕ) (U : List Step)
    (hgap : (endpointFrom x y U).2 = (endpointFrom x y U).1 + 1) :
    endpointFrom x y (U ++ [east]) =
      ((endpointFrom x y U).1 + 1, (endpointFrom x y U).1 + 1) := by
  rw [endpointFrom_append]
  simp only [endpointFrom]
  rw [hgap]

end Step

namespace SchroderPath

/-- Congruence for an arbitrary path invariant: paths with equal size indices
and equal step words have equal values.  The size equality is transported
honestly by substitution. -/
theorem invariant_congr {A : Sort*} (F : ∀ n, SchroderPath n → A)
    {m m' : ℕ} (P : SchroderPath m) (P' : SchroderPath m')
    (hm : m = m') (hs : P.steps = P'.steps) : F m P = F m' P' := by
  subst hm
  cases P
  cases P'
  cases hs
  rfl

/-- A path with a nonempty word has positive size. -/
theorem pos_of_steps_ne_nil {n : ℕ} (P : SchroderPath n) (hP : P.steps ≠ []) :
    0 < n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact absurd ((steps_eq_nil_iff P).mpr hn) hP
  · exact hn

end SchroderPath

/-- The product branch at the first east step gives two strictly smaller positive paths. -/
theorem firstEast_product_reduction {A : Type*} [CommRing A]
    (q : A) (e : ℕ → A) (F : ∀ n, SchroderPath n → A)
    (hF : SatisfiesRecursion q e F)
    {n : ℕ} (U W : List Step)
    (h : Step.validFrom n 0 0 (U ++ Step.east :: W) = true)
    (hU : Step.east ∉ U)
    (hgap : (Step.endpointFrom 0 0 U).2 = (Step.endpointFrom 0 0 U).1 + 1)
    (hcount : 2 ≤ Step.eastCount (U ++ Step.east :: W)) :
    ∃ (k l : ℕ) (P : SchroderPath k) (Q : SchroderPath l),
      0 < k ∧ 0 < l ∧ k < n ∧ l < n ∧ k + l = n ∧
      P.steps = U ++ [Step.east] ∧ Q.steps = W ∧
      F n ⟨U ++ Step.east :: W, h⟩ = F k P * F l Q := by
  set a := (Step.endpointFrom 0 0 U).1
  have hend : Step.endpointFrom 0 0 (U ++ [Step.east]) = (a + 1, a + 1) :=
    Step.endpointFrom_append_east_of_gap 0 0 U hgap
  have h' : Step.validFrom n 0 0 ((U ++ [Step.east]) ++ W) = true := by
    simpa only [List.append_assoc, List.singleton_append] using h
  let P : SchroderPath (a + 1) := SchroderPath.prefixAtReturn _ _ h' hend
  let Q : SchroderPath (n - (a + 1)) := SchroderPath.suffixAtReturn _ _ h' hend
  have hsuf := Step.validFrom_suffix_at_endpoint (U ++ [Step.east]) W h' hend
  have hkn : a + 1 ≤ n := (Step.validFrom_bounds n (a + 1) (a + 1) hsuf).2
  have hWcount : 0 < Step.eastCount W := by
    rw [Step.eastCount_append, Step.eastCount_cons_east,
      Step.eastCount_eq_zero_of_not_mem hU] at hcount
    lia
  have hWne : W ≠ [] :=
    List.ne_nil_of_mem (Step.east_mem_of_eastCount_pos hWcount)
  have hl : 0 < n - (a + 1) := SchroderPath.pos_of_steps_ne_nil Q hWne
  refine ⟨a + 1, n - (a + 1), P, Q, Nat.succ_pos a, hl, by lia, by lia,
    by lia, rfl, rfl, ?_⟩
  rw [← hF.concat P Q]
  exact SchroderPath.invariant_congr F _ _ (by lia)
    (by simp [P, Q, SchroderPath.concat_steps])

end VerticalStripLLT
