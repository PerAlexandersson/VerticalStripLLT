import VerticalStripLLT.BounceTransport
-- Local helper module: VerticalStripLLT.BounceMatching

/-! ## The weighted two-to-one correspondence -/

namespace VerticalStripLLT
namespace BounceHRV

open scoped BigOperators

variable {n : ℕ}

section Matching

variable {B : SchroderPath n} {i y t : Fin n} (hy : y.val = i.val + 1) (hyt : y < t)
  (hiy : (i, y) ∈ B.normalEdges)
  (hSinv : B.strictEdges.map (swapVertexPair i y) = B.strictEdges)
  (hNinv : (B.normalEdges.erase (i, y)).map (swapVertexPair i y) =
    B.normalEdges.erase (i, y))

/-- The source-to-successor matching: `(b, θ) ↦ (k, θ')`, where `θ'` is the successor
orientation and `k` records which of its two preimages `(b, θ)` is. -/
noncomputable def bounceMatch (i y t : Fin n) (hiy : (i, y) ∈ B.normalEdges)
    (hNinv : (B.normalEdges.erase (i, y)).map (swapVertexPair i y) =
      B.normalEdges.erase (i, y)) (p : Bool × Orientation B) : Bool × Orientation B :=
  if gh (r0 i y p.2) t ≤ gh (r0 i y p.2) y then
    (if bitOf hiy p.2 = true ∨ gh (r0 i y p.2) t ≤ gh (r0 i y p.2) i then p
      else (p.1, setBit i y false (swapO hNinv p.2)))
  else
    (if p.1 = true then (bitOf hiy p.2, setBit i y true p.2)
      else (bitOf hiy p.2, setBit i y false (swapO hNinv p.2)))

/-- An explicit left inverse of `bounceMatch`. -/
noncomputable def bounceUnmatch (i y t : Fin n) (hiy : (i, y) ∈ B.normalEdges)
    (hNinv : (B.normalEdges.erase (i, y)).map (swapVertexPair i y) =
      B.normalEdges.erase (i, y)) (q : Bool × Orientation B) : Bool × Orientation B :=
  if bitOf hiy q.2 = true then
    (if gh (r0 i y q.2) t ≤ gh (r0 i y q.2) y then q else (true, setBit i y q.1 q.2))
  else if gh (r0 i y q.2) t ≤ gh (r0 i y q.2) i then
    (if gh (r0 i y q.2) t ≤ gh (r0 i y q.2) y then q else (q.1, swapO hNinv q.2))
  else (false, setBit i y q.1 (swapO hNinv q.2))

theorem gh_r0_setBit (β : Bool) (θ : Orientation B) :
    gh (r0 i y (setBit i y β θ)) = gh (r0 i y θ) :=
  gh_congr (r0_setBit β θ)

include hy hSinv in
theorem gh_r0_swapO_i (θ : Orientation B) :
    gh (r0 i y (swapO hNinv θ)) i = Equiv.swap i y (gh (r0 i y θ) y) := by
  have := swap_value hy (r0_swapO hy hSinv hNinv θ) y (Or.inr rfl)
  rwa [Equiv.swap_apply_right] at this

include hy hSinv in
theorem gh_r0_swapO_y (θ : Orientation B) :
    gh (r0 i y (swapO hNinv θ)) y = Equiv.swap i y (gh (r0 i y θ) i) := by
  have := swap_value hy (r0_swapO hy hSinv hNinv θ) i (Or.inl rfl)
  rwa [Equiv.swap_apply_left] at this

include hy hyt hSinv in
theorem gh_r0_swapO_t (θ : Orientation B) :
    gh (r0 i y (swapO hNinv θ)) t = gh (r0 i y θ) t :=
  swap_above hy (r0_swapO hy hSinv hNinv θ) t hyt

include hy in
theorem le_swap_iff {H x : Fin n} (hH : y < H) (hx : x = i ∨ x = y ∨ y < x) :
    H ≤ Equiv.swap i y x ↔ H ≤ x := by
  rcases hx with rfl | rfl | hx
  · rw [Equiv.swap_apply_left]
    exact ⟨fun h => absurd hH (not_lt.2 h),
      fun h => absurd (hH.trans_le h) (not_lt.2 (i_lt_y hy).le)⟩
  · rw [Equiv.swap_apply_right]
    exact ⟨fun h => absurd (hH.trans_le h) (not_lt.2 (i_lt_y hy).le),
      fun h => absurd hH (not_lt.2 h)⟩
  · rw [swap_fix_of_lt hy hx]

include hy in
theorem max_swap_eq {H x : Fin n} (hH : y < H) (hx : x = i ∨ y < x) :
    max (Equiv.swap i y x) H = max x H := by
  rcases hx with rfl | hx
  · rw [Equiv.swap_apply_left, max_eq_right hH.le, max_eq_right ((i_lt_y hy).trans hH).le]
  · rw [swap_fix_of_lt hy hx]

include hy hyt hSinv in
theorem bounceUnmatch_bounceMatch (p : Bool × Orientation B) :
    bounceUnmatch i y t hiy hNinv (bounceMatch i y t hiy hNinv p) = p := by
  obtain ⟨b, θ⟩ := p
  have hHt : y < gh (r0 i y θ) t := lt_of_lt_of_le hyt (le_gh _ t)
  have hA := A_cases hy θ
  have hC := C_cases (i := i) (y := y) θ
  unfold bounceMatch
  simp only
  by_cases hCH : gh (r0 i y θ) t ≤ gh (r0 i y θ) y
  · rw [ite_eq_left hCH]
    by_cases hc : bitOf hiy θ = true ∨ gh (r0 i y θ) t ≤ gh (r0 i y θ) i
    · rw [ite_eq_left hc]
      unfold bounceUnmatch
      simp only
      rcases hc with hb | hAH
      · rw [ite_eq_left hb, ite_eq_left hCH]
      · by_cases hb : bitOf hiy θ = true
        · rw [ite_eq_left hb, ite_eq_left hCH]
        · rw [ite_eq_right hb, ite_eq_left hAH, ite_eq_left hCH]
    · rw [ite_eq_right hc]
      push Not at hc
      unfold bounceUnmatch
      simp only [bitOf_setBit, Bool.false_eq_true, ite_false, gh_r0_setBit,
        gh_r0_swapO_i hy hSinv, gh_r0_swapO_y hy hSinv, gh_r0_swapO_t hy hyt hSinv]
      rw [ite_eq_left ((le_swap_iff hy hHt (Or.inr hC)).2 hCH),
        ite_eq_right (fun h => not_le.2 hc.2 ((le_swap_iff hy hHt (hA.imp_right Or.inr)).1 h)),
        swapO_setBit, swapO_swapO]
      have hb : bitOf hiy θ = false := by simpa using hc.1
      rw [← hb, setBit_bitOf]
  · rw [ite_eq_right hCH]
    have hCH' := not_le.1 hCH
    cases b
    · simp only [Bool.false_eq_true, ite_false]
      unfold bounceUnmatch
      simp only [bitOf_setBit, Bool.false_eq_true, ite_false, gh_r0_setBit,
        gh_r0_swapO_i hy hSinv, gh_r0_swapO_t hy hyt hSinv]
      rw [ite_eq_right (fun h => hCH ((le_swap_iff hy hHt (Or.inr hC)).1 h)), swapO_setBit,
        swapO_swapO, setBit_setBit, setBit_bitOf]
    · simp only [ite_true]
      unfold bounceUnmatch
      simp only [bitOf_setBit, ite_true, gh_r0_setBit]
      rw [ite_eq_right hCH, setBit_setBit, setBit_bitOf]

include hy hyt hSinv in
theorem bounceMatch_bijective : Function.Bijective (bounceMatch i y t hiy hNinv) :=
  (Function.LeftInverse.injective
    (bounceUnmatch_bounceMatch hy hyt hiy hSinv hNinv)).bijective_of_finite

include hy hyt hiy in
theorem fiberMono_of_same (b : Bool) (θ θ' : Orientation B)
    (hr0 : ∀ u w, r0 i y θ' u w ↔ r0 i y θ u w)
    (hY : gh (RT y t θ') y = gh (RP i y t b θ) y)
    (hI : gh (RT y t θ') i = gh (RP i y t b θ) i) :
    fiberMono (gh (RT y t θ')) = fiberMono (gh (RP i y t b θ)) :=
  fiberMono_conj _ _ (Equiv.refl _) (Equiv.refl _) (gh_eq_of_same hy hyt hiy b θ θ' hr0 hY hI)

include hy hyt hiy in
theorem fiberMono_of_swap (b : Bool) (θ θ' : Orientation B)
    (hr0 : ∀ u w, r0 i y θ' u w ↔ r0 i y θ (Equiv.swap i y u) (Equiv.swap i y w))
    (hY : gh (RT y t θ') i = Equiv.swap i y (gh (RP i y t b θ) y))
    (hI : gh (RT y t θ') y = gh (RP i y t b θ) i) :
    fiberMono (gh (RT y t θ')) = fiberMono (gh (RP i y t b θ)) :=
  fiberMono_conj _ _ (Equiv.swap i y) (Equiv.swap i y)
    (gh_eq_of_swap hy hyt hiy b θ θ' hr0 hY hI)

include hy hyt hSinv in
/-- Ascent and fibre-monomial bookkeeping for each matched pair. -/
theorem bounceMatch_spec (p : Bool × Orientation B) :
    orientationAsc B p.2 + (if p.1 then 1 else 0) =
      orientationAsc B (bounceMatch i y t hiy hNinv p).2 +
        (if (bounceMatch i y t hiy hNinv p).1 then 1 else 0) ∧
    fiberMono (gh (RT y t (bounceMatch i y t hiy hNinv p).2)) =
      fiberMono (gh (RP i y t p.1 p.2)) := by
  obtain ⟨b, θ⟩ := p
  have hHt : y < gh (r0 i y θ) t := lt_of_lt_of_le hyt (le_gh _ t)
  have hA := A_cases hy θ
  have hswap_r0 : ∀ u w, r0 i y (setBit i y false (swapO hNinv θ)) u w ↔
      r0 i y θ (Equiv.swap i y u) (Equiv.swap i y w) := fun u w =>
    (r0_setBit false _ u w).trans (r0_swapO hy hSinv hNinv θ u w)
  have hswap_asc : orientationAsc B (setBit i y false (swapO hNinv θ)) +
      (if bitOf hiy θ then 1 else 0) = orientationAsc B θ := by
    have := orientationAsc_setBit hiy false (swapO hNinv θ)
    rw [bitOf_swapO hiy hNinv, orientationAsc_swapO] at this
    simpa using this
  have hswapY : gh (RT y t (setBit i y false (swapO hNinv θ))) i =
      Equiv.swap i y (gh (r0 i y θ) y) := by
    rw [gh_RT_i hy hyt hiy, bitOf_setBit, gh_r0_setBit, gh_r0_swapO_i hy hSinv]
    simp
  have hswapI : gh (RT y t (setBit i y false (swapO hNinv θ))) y =
      max (gh (r0 i y θ) i) (gh (r0 i y θ) t) := by
    rw [gh_RT_y hy hyt hiy, gh_r0_setBit, gh_r0_swapO_y hy hSinv, gh_r0_swapO_t hy hyt hSinv,
      max_swap_eq hy hHt hA]
  unfold bounceMatch
  simp only
  by_cases hCH : gh (r0 i y θ) t ≤ gh (r0 i y θ) y
  · rw [ite_eq_left hCH]
    have hmC : max (gh (r0 i y θ) y) (gh (r0 i y θ) t) = gh (r0 i y θ) y := max_eq_left hCH
    by_cases hc : bitOf hiy θ = true ∨ gh (r0 i y θ) t ≤ gh (r0 i y θ) i
    · rw [ite_eq_left hc]
      refine ⟨rfl, fiberMono_of_same hy hyt hiy b θ θ (fun _ _ => Iff.rfl) ?_ ?_⟩
      · rw [gh_RT_y hy hyt hiy, gh_RP_y hy hyt hiy, hmC]
        cases b <;> simp
      · rw [gh_RT_i hy hyt hiy, gh_RP_i hy hyt hiy]
        rcases hc with hb | hAH
        · simp [hb]
        · cases hb : bitOf hiy θ
          · simp [max_eq_left hAH]
          · simp
    · rw [ite_eq_right hc]
      push Not at hc
      have hb : bitOf hiy θ = false := by simpa using hc.1
      refine ⟨?_, fiberMono_of_swap hy hyt hiy b θ _ hswap_r0 ?_ ?_⟩
      · simp only
        rw [← hswap_asc, hb]
        simp
      · rw [hswapY, gh_RP_y hy hyt hiy]
        cases b <;> simp [hmC]
      · rw [hswapI, gh_RP_i hy hyt hiy, hb]
        simp
  · rw [ite_eq_right hCH]
    have hmC : max (gh (r0 i y θ) y) (gh (r0 i y θ) t) = gh (r0 i y θ) t :=
      max_eq_right (not_le.1 hCH).le
    have hI : gh (RP i y t b θ) i = max (gh (r0 i y θ) i) (gh (r0 i y θ) t) := by
      rw [gh_RP_i hy hyt hiy, hmC]
      simp
    cases b
    · simp only [Bool.false_eq_true, ite_false]
      refine ⟨?_, fiberMono_of_swap hy hyt hiy false θ _ hswap_r0 ?_ ?_⟩
      · rw [hswap_asc]; simp
      · rw [hswapY, gh_RP_y hy hyt hiy]
        simp
      · rw [hswapI, hI]
    · simp only [ite_true]
      refine ⟨?_, fiberMono_of_same hy hyt hiy true θ _ (r0_setBit true θ) ?_ ?_⟩
      · have := orientationAsc_setBit hiy true θ
        simp only [ite_true] at this
        lia
      · rw [gh_RT_y hy hyt hiy, gh_RP_y hy hyt hiy, gh_r0_setBit]
        simp
      · rw [gh_RT_i hy hyt hiy, bitOf_setBit, gh_r0_setBit, hI, hmC]
        simp

end Matching

end BounceHRV
end VerticalStripLLT

