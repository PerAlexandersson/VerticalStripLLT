import VerticalStripLLT.SecondBounceMatching
-- Local helper module: VerticalStripLLT.SecondBounceSpec

/-! ## Ascent and fibre-monomial bookkeeping for each matched pair -/

namespace VerticalStripLLT
namespace BounceHRV

open scoped BigOperators

variable {n : ℕ}

section SecondSpec

variable {B : SchroderPath n} {a i y t : Fin n} (hy : y.val = i.val + 1) (hyt : y < t)
  (hai : a < i) (hiy : (i, y) ∈ B.normalEdges)
  (hSinv : B.strictEdges.map (swapVertexPair i y) = B.strictEdges)
  (hNinv : (B.normalEdges.erase (i, y)).map (swapVertexPair i y) =
    B.normalEdges.erase (i, y))

include hy hyt hai hSinv in
theorem secondMatch_spec (p : Bool × Orientation B) :
    orientationAsc B p.2 + (if p.1 then 1 else 0) =
      orientationAsc B (secondMatch i y t hiy hNinv p).2 +
        (if (secondMatch i y t hiy hNinv p).1 then 1 else 0) ∧
    fiberMono (gh (RT2 a i y t (secondMatch i y t hiy hNinv p).1
        (secondMatch i y t hiy hNinv p).2)) =
      fiberMono (gh (RP2 a i y t p.1 p.2)) := by
  obtain ⟨b, θ⟩ := p
  have hHt : y < gh (r0 i y θ) t := lt_of_lt_of_le hyt (le_gh _ t)
  have hA := A_cases hy θ
  have hswap_r0 : ∀ β : Bool, ∀ u w, r0 i y (setBit i y β (swapO hNinv θ)) u w ↔
      r0 i y θ (Equiv.swap i y u) (Equiv.swap i y w) := fun β u w =>
    (r0_setBit β _ u w).trans (r0_swapO hy hSinv hNinv θ u w)
  have hswap_asc : ∀ β : Bool, orientationAsc B (setBit i y β (swapO hNinv θ)) +
      (if bitOf hiy θ then 1 else 0) = orientationAsc B θ + (if β then 1 else 0) := by
    intro β
    have := orientationAsc_setBit hiy β (swapO hNinv θ)
    rwa [bitOf_swapO hiy hNinv, orientationAsc_swapO] at this
  have hvi : ∀ β : Bool, gh (r0 i y (setBit i y β (swapO hNinv θ))) i =
      Equiv.swap i y (gh (r0 i y θ) y) := fun β => by
    rw [gh_r0_setBit, gh_r0_swapO_i hy hSinv]
  have hvy : ∀ β : Bool, gh (r0 i y (setBit i y β (swapO hNinv θ))) y =
      Equiv.swap i y (gh (r0 i y θ) i) := fun β => by
    rw [gh_r0_setBit, gh_r0_swapO_y hy hSinv]
  have hvt : ∀ β : Bool, gh (r0 i y (setBit i y β (swapO hNinv θ))) t = gh (r0 i y θ) t :=
    fun β => by rw [gh_r0_setBit, gh_r0_swapO_t hy hyt hSinv]
  cases b <;> cases hβ : bitOf hiy θ
  · -- `b = β = false`: swap, successor bit `false`
    have hm : secondMatch i y t hiy hNinv (false, θ) =
        (false, setBit i y false (swapO hNinv θ)) := by
      simp [secondMatch, hβ]
    rw [hm]
    refine ⟨?_, fiberMono2_of_swap hy hyt hai hiy false false θ _ (hswap_r0 false) ?_ ?_
      (fun h => absurd h Bool.false_ne_true)⟩
    · have := hswap_asc false
      rw [hβ] at this
      simpa using this.symm
    · rw [gh_RT2_i hy hyt hai hiy, bitOf_setBit, hvi, gh_RP2_y hy hyt hai hiy]
      simp only [Bool.false_eq_true, ite_false]
    · rw [gh_RT2_y hy hyt hai hiy, hvy, hvt, gh_RP2_i hy hyt hai hiy, hβ]
      simp only [Bool.false_eq_true, ite_false]
      exact ord_max_swapA hy hA hHt
  · -- `b = false`, `β = true`
    by_cases hI : gh (r0 i y θ) i ≤ gh (r0 i y θ) t ∧ gh (r0 i y θ) y ≤ gh (r0 i y θ) t
    · have hm : secondMatch i y t hiy hNinv (false, θ) =
          (true, setBit i y false (swapO hNinv θ)) := by
        simp [secondMatch, hβ, hI]
      rw [hm]
      refine ⟨?_, fiberMono2_of_swap hy hyt hai hiy false true θ _ (hswap_r0 false) ?_ ?_
        (fun _ => ?_)⟩
      · have := hswap_asc false
        rw [hβ] at this
        simpa using this.symm
      · rw [gh_RT2_i hy hyt hai hiy, bitOf_setBit, hvi, gh_RP2_y hy hyt hai hiy]
        simp only [Bool.false_eq_true, ite_false]
      · rw [gh_RT2_y hy hyt hai hiy, hvy, hvt, gh_RP2_i hy hyt hai hiy, hβ]
        simp only [ite_true]
        exact ord_I_swap_i hy hA hHt hI
      · rw [gh_RT2_i hy hyt hai hiy, bitOf_setBit, hvi, gh_RP2_i hy hyt hai hiy, hβ]
        simp only [Bool.false_eq_true, ite_false, ite_true]
        exact ord_swapC_le hy hHt
    · by_cases hAC : gh (r0 i y θ) i ≤ gh (r0 i y θ) y
      · have hm : secondMatch i y t hiy hNinv (false, θ) = (false, θ) := by
          simp [secondMatch, hβ, hI, hAC]
        rw [hm]
        refine ⟨rfl, fiberMono2_of_same hy hyt hai hiy false false θ θ (fun _ _ => Iff.rfl)
          ?_ (by rw [gh_RT2_i hy hyt hai hiy, gh_RP2_i hy hyt hai hiy, hβ]; simp only [ite_true])
          ?_ (Or.inl ?_)⟩
        · rw [gh_RT2_y hy hyt hai hiy, gh_RP2_y hy hyt hai hiy]
          simp only [Bool.false_eq_true, ite_false]
          exact ord_AC_y hI hAC
        · rw [gh_RT2_y hy hyt hai hiy, gh_RP2_i hy hyt hai hiy, hβ]
          simp only [ite_true]
          exact le_max_right _ _
        · rw [gh_RT2_y hy hyt hai hiy, gh_RP2_i hy hyt hai hiy, hβ]
          simp only [ite_true]
          exact ord_AC_i hI hAC
      · have hm : secondMatch i y t hiy hNinv (false, θ) =
            (true, setBit i y false (swapO hNinv θ)) := by
          simp [secondMatch, hβ, hI, hAC]
        rw [hm]
        refine ⟨?_, fiberMono2_of_swap hy hyt hai hiy false true θ _ (hswap_r0 false) ?_ ?_
          (fun _ => ?_)⟩
        · have := hswap_asc false
          rw [hβ] at this
          simpa using this.symm
        · rw [gh_RT2_i hy hyt hai hiy, bitOf_setBit, hvi, gh_RP2_y hy hyt hai hiy]
          simp only [Bool.false_eq_true, ite_false]
        · rw [gh_RT2_y hy hyt hai hiy, hvy, hvt, gh_RP2_i hy hyt hai hiy, hβ]
          simp only [ite_true]
          exact ord_IIb_swap_i hy hA hHt hI hAC
        · rw [gh_RT2_i hy hyt hai hiy, bitOf_setBit, hvi, gh_RP2_i hy hyt hai hiy, hβ]
          simp only [Bool.false_eq_true, ite_false, ite_true]
          exact ord_swapC_le hy hHt
  · -- `b = true`, `β = false`
    by_cases hI : gh (r0 i y θ) i ≤ gh (r0 i y θ) t ∧ gh (r0 i y θ) y ≤ gh (r0 i y θ) t
    · have hm : secondMatch i y t hiy hNinv (true, θ) = (false, setBit i y true θ) := by
        simp [secondMatch, hβ, hI]
      rw [hm]
      refine ⟨?_, fiberMono2_of_same hy hyt hai hiy true false θ _ (r0_setBit true θ)
        ?_ ?_ ?_ (Or.inl ?_)⟩
      · have := orientationAsc_setBit hiy true θ
        rw [hβ] at this
        simpa using this.symm
      · rw [gh_RT2_y hy hyt hai hiy, gh_r0_setBit, gh_RP2_y hy hyt hai hiy]
        simp only [ite_true]
      · rw [gh_RT2_i hy hyt hai hiy, bitOf_setBit, gh_r0_setBit, gh_RP2_i hy hyt hai hiy, hβ]
        simp only [Bool.false_eq_true, ite_false, ite_true]
        exact ord_I_i hI
      · rw [gh_RT2_y hy hyt hai hiy, gh_r0_setBit, gh_RP2_i hy hyt hai hiy, hβ]
        simp only [Bool.false_eq_true, ite_false]
        exact (ord_I_y hI).le
      · rw [gh_RT2_y hy hyt hai hiy, gh_r0_setBit, gh_RP2_i hy hyt hai hiy, hβ]
        simp only [Bool.false_eq_true, ite_false]
        exact ord_I_y hI
    · by_cases hCA : gh (r0 i y θ) y ≤ gh (r0 i y θ) i
      · have hm : secondMatch i y t hiy hNinv (true, θ) = (true, θ) := by
          simp [secondMatch, hβ, hI, hCA]
        rw [hm]
        refine ⟨rfl, fiberMono2_of_same hy hyt hai hiy true true θ θ (fun _ _ => Iff.rfl)
          ?_ ?_ ?_ (Or.inr rfl)⟩
        · rw [gh_RT2_y hy hyt hai hiy, gh_RP2_y hy hyt hai hiy]
          simp only [ite_true]
        · rw [gh_RT2_i hy hyt hai hiy, gh_RP2_i hy hyt hai hiy, hβ]
          simp only [Bool.false_eq_true, ite_false]
          exact ord_CA_i hI hCA
        · rw [gh_RT2_y hy hyt hai hiy, gh_RP2_i hy hyt hai hiy, hβ]
          simp only [Bool.false_eq_true, ite_false]
          exact ord_CA_le hI hCA
      · have hm : secondMatch i y t hiy hNinv (true, θ) =
            (false, setBit i y true (swapO hNinv θ)) := by
          simp [secondMatch, hβ, hI, hCA]
        rw [hm]
        refine ⟨?_, fiberMono2_of_swap hy hyt hai hiy true false θ _ (hswap_r0 true) ?_ ?_
          (fun h => absurd h Bool.false_ne_true)⟩
        · have := hswap_asc true
          rw [hβ] at this
          simpa using this.symm
        · rw [gh_RT2_i hy hyt hai hiy, bitOf_setBit, hvi, hvy, hvt, gh_RP2_y hy hyt hai hiy]
          simp only [ite_true]
          exact ord_IIa_y hy hA hHt hI hCA
        · rw [gh_RT2_y hy hyt hai hiy, hvy, hvt, gh_RP2_i hy hyt hai hiy, hβ]
          simp only [Bool.false_eq_true, ite_false]
          exact ord_max_swapA hy hA hHt
  · -- `b = β = true`: identity
    have hm : secondMatch i y t hiy hNinv (true, θ) = (true, θ) := by
      simp [secondMatch, hβ]
    rw [hm]
    refine ⟨rfl, fiberMono2_of_same hy hyt hai hiy true true θ θ (fun _ _ => Iff.rfl)
      ?_ (by rw [gh_RT2_i hy hyt hai hiy, gh_RP2_i hy hyt hai hiy, hβ]; simp only [ite_true])
      ?_ (Or.inr rfl)⟩
    · rw [gh_RT2_y hy hyt hai hiy, gh_RP2_y hy hyt hai hiy]
      simp only [ite_true]
    · rw [gh_RT2_y hy hyt hai hiy, gh_RP2_i hy hyt hai hiy, hβ]
      simp only [ite_true]
      exact le_max_right _ _

end SecondSpec

end BounceHRV
end VerticalStripLLT
