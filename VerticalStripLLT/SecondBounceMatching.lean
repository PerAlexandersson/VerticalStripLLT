import VerticalStripLLT.SecondBounceOrder
-- Local helper module: VerticalStripLLT.SecondBounceMatching

/-! ## The ascent-preserving, fibre-preserving bijection between source and successor

A source orientation is `(b, θ)` with `b` the orientation of `(y,t)`; a successor
orientation is `(c, θ')` with `c` the orientation of `(a,i)`.  With `β = bitOf θ` and the
background values `A, C, H`, the map `secondMatch` is:
* `b = β = true`: `(true, θ)` (identity);
* `b = β = false`: `(false, swap θ)` with bit `false`;
* `b ≠ β`, case `A ≤ H ∧ C ≤ H`: `b = true ↦ (false, θ with bit true)`,
  `b = false ↦ (true, swap θ with bit false)`;
* `b ≠ β`, otherwise, `b = true`: identity if `C ≤ A`, else `(false, swap θ with bit true)`;
* `b ≠ β`, otherwise, `b = false`: identity if `A ≤ C`, else `(true, swap θ with bit false)`.
-/

namespace VerticalStripLLT
namespace BounceHRV

open scoped BigOperators

variable {n : ℕ}

section SecondMatching

variable {B : SchroderPath n} {a i y t : Fin n} (hy : y.val = i.val + 1) (hyt : y < t)
  (hai : a < i) (hiy : (i, y) ∈ B.normalEdges)
  (hSinv : B.strictEdges.map (swapVertexPair i y) = B.strictEdges)
  (hNinv : (B.normalEdges.erase (i, y)).map (swapVertexPair i y) =
    B.normalEdges.erase (i, y))

/-- The source-to-successor matching for the second bounce. -/
noncomputable def secondMatch (i y t : Fin n) (hiy : (i, y) ∈ B.normalEdges)
    (hNinv : (B.normalEdges.erase (i, y)).map (swapVertexPair i y) =
      B.normalEdges.erase (i, y)) (p : Bool × Orientation B) : Bool × Orientation B :=
  if p.1 = bitOf hiy p.2 then
    (if p.1 then (true, p.2) else (false, setBit i y false (swapO hNinv p.2)))
  else if gh (r0 i y p.2) i ≤ gh (r0 i y p.2) t ∧ gh (r0 i y p.2) y ≤ gh (r0 i y p.2) t then
    (if p.1 then (false, setBit i y true p.2) else (true, setBit i y false (swapO hNinv p.2)))
  else if p.1 then
    (if gh (r0 i y p.2) y ≤ gh (r0 i y p.2) i then (true, p.2)
      else (false, setBit i y true (swapO hNinv p.2)))
  else
    (if gh (r0 i y p.2) i ≤ gh (r0 i y p.2) y then (false, p.2)
      else (true, setBit i y false (swapO hNinv p.2)))

/-- An explicit left inverse of `secondMatch`. -/
noncomputable def secondUnmatch (i y t : Fin n) (hiy : (i, y) ∈ B.normalEdges)
    (hNinv : (B.normalEdges.erase (i, y)).map (swapVertexPair i y) =
      B.normalEdges.erase (i, y)) (q : Bool × Orientation B) : Bool × Orientation B :=
  if q.1 = bitOf hiy q.2 then
    (if q.1 then (true, q.2) else (false, setBit i y false (swapO hNinv q.2)))
  else if gh (r0 i y q.2) i ≤ gh (r0 i y q.2) t ∧ gh (r0 i y q.2) y ≤ gh (r0 i y q.2) t then
    (if q.1 then (false, setBit i y true (swapO hNinv q.2)) else (true, setBit i y false q.2))
  else if q.1 then
    (if gh (r0 i y q.2) y ≤ gh (r0 i y q.2) i then (true, q.2)
      else (false, setBit i y true (swapO hNinv q.2)))
  else
    (if gh (r0 i y q.2) i ≤ gh (r0 i y q.2) y then (false, q.2)
      else (true, setBit i y false (swapO hNinv q.2)))

include hy hyt hSinv in
theorem secondUnmatch_secondMatch (p : Bool × Orientation B) :
    secondUnmatch i y t hiy hNinv (secondMatch i y t hiy hNinv p) = p := by
  obtain ⟨b, θ⟩ := p
  have hHt : y < gh (r0 i y θ) t := lt_of_lt_of_le hyt (le_gh _ t)
  have hA := A_cases hy θ
  have hC := C_cases (i := i) (y := y) θ
  have hSS : ∀ β β' : Bool, setBit i y β' (swapO hNinv (setBit i y β (swapO hNinv θ))) =
      setBit i y β' θ := by
    intro β β'
    rw [swapO_setBit, swapO_swapO, setBit_setBit]
  have hvi : ∀ β : Bool, gh (r0 i y (setBit i y β (swapO hNinv θ))) i =
      Equiv.swap i y (gh (r0 i y θ) y) := fun β => by
    rw [gh_r0_setBit, gh_r0_swapO_i hy hSinv]
  have hvy : ∀ β : Bool, gh (r0 i y (setBit i y β (swapO hNinv θ))) y =
      Equiv.swap i y (gh (r0 i y θ) i) := fun β => by
    rw [gh_r0_setBit, gh_r0_swapO_y hy hSinv]
  have hvt : ∀ β : Bool, gh (r0 i y (setBit i y β (swapO hNinv θ))) t = gh (r0 i y θ) t :=
    fun β => by rw [gh_r0_setBit, gh_r0_swapO_t hy hyt hSinv]
  have hIsw := ord_caseI_swap (C := gh (r0 i y θ) y) hy hA hHt
  cases b <;> cases hβ : bitOf hiy θ
  · -- `b = β = false`
    have hm : secondMatch i y t hiy hNinv (false, θ) =
        (false, setBit i y false (swapO hNinv θ)) := by
      simp [secondMatch, hβ]
    rw [hm]
    simp only [secondUnmatch, bitOf_setBit, ite_true, Bool.false_eq_true, ite_false, hSS]
    rw [← hβ, setBit_bitOf]
  · -- `b = false`, `β = true`
    by_cases hI : gh (r0 i y θ) i ≤ gh (r0 i y θ) t ∧ gh (r0 i y θ) y ≤ gh (r0 i y θ) t
    · have hm : secondMatch i y t hiy hNinv (false, θ) =
          (true, setBit i y false (swapO hNinv θ)) := by
        simp [secondMatch, hβ, hI]
      rw [hm]
      simp only [secondUnmatch, bitOf_setBit, Bool.true_eq_false, ite_false, ite_true, hvi, hvy,
        hvt, hSS]
      rw [ite_eq_left (hIsw.2 hI), ← hβ, setBit_bitOf]
    · by_cases hAC : gh (r0 i y θ) i ≤ gh (r0 i y θ) y
      · have hm : secondMatch i y t hiy hNinv (false, θ) = (false, θ) := by
          simp [secondMatch, hβ, hI, hAC]
        rw [hm]
        simp [secondUnmatch, hβ, hI, hAC]
      · have hm : secondMatch i y t hiy hNinv (false, θ) =
            (true, setBit i y false (swapO hNinv θ)) := by
          simp [secondMatch, hβ, hI, hAC]
        rw [hm]
        simp only [secondUnmatch, bitOf_setBit, Bool.true_eq_false, ite_false, ite_true, hvi,
          hvy, hvt, hSS]
        rw [ite_eq_right (fun h => hI (hIsw.1 h)),
          ite_eq_right (fun h => hAC ((ord_swap_AC hy hA hC hHt hI).1 h)), ← hβ, setBit_bitOf]
  · -- `b = true`, `β = false`
    by_cases hI : gh (r0 i y θ) i ≤ gh (r0 i y θ) t ∧ gh (r0 i y θ) y ≤ gh (r0 i y θ) t
    · have hm : secondMatch i y t hiy hNinv (true, θ) = (false, setBit i y true θ) := by
        simp [secondMatch, hβ, hI]
      rw [hm]
      simp only [secondUnmatch, bitOf_setBit, Bool.false_eq_true, ite_false, gh_r0_setBit,
        setBit_setBit]
      rw [ite_eq_left hI, ← hβ, setBit_bitOf]
    · by_cases hCA : gh (r0 i y θ) y ≤ gh (r0 i y θ) i
      · have hm : secondMatch i y t hiy hNinv (true, θ) = (true, θ) := by
          simp [secondMatch, hβ, hI, hCA]
        rw [hm]
        simp [secondUnmatch, hβ, hI, hCA]
      · have hm : secondMatch i y t hiy hNinv (true, θ) =
            (false, setBit i y true (swapO hNinv θ)) := by
          simp [secondMatch, hβ, hI, hCA]
        rw [hm]
        simp only [secondUnmatch, bitOf_setBit, Bool.false_eq_true, ite_false, hvi, hvy, hvt,
          hSS]
        rw [ite_eq_right (fun h => hI (hIsw.1 h)),
          ite_eq_right (fun h => hCA ((ord_swap_CA hy hA hC hHt hI).1 h)), ← hβ, setBit_bitOf]
  · -- `b = β = true`
    have hm : secondMatch i y t hiy hNinv (true, θ) = (true, θ) := by
      simp [secondMatch, hβ]
    rw [hm]
    simp [secondUnmatch, hβ]

include hy hyt hSinv in
theorem secondMatch_bijective : Function.Bijective (secondMatch i y t hiy hNinv) :=
  (Function.LeftInverse.injective
    (secondUnmatch_secondMatch hy hyt hiy hSinv hNinv)).bijective_of_finite

end SecondMatching

end BounceHRV
end VerticalStripLLT
