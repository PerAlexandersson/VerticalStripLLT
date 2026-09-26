import VerticalStripLLT.SecondBounceDistinguished
-- Local helper module: VerticalStripLLT.SecondBounceTransport

/-! ## Transport of highest reachable vertices along `id` or the swap `(i y)` -/

namespace VerticalStripLLT
namespace BounceHRV

open scoped BigOperators

variable {n : ℕ}

section SecondTransport

variable {B : SchroderPath n} {a i y t : Fin n} (hy : y.val = i.val + 1) (hyt : y < t)
  (hai : a < i) (hiy : (i, y) ∈ B.normalEdges)

include hy hyt hai hiy in
/-- The general conjugation principle: if the backgrounds are related by a permutation
`σ` fixing everything except `i,y`, the values at `i,y` are conjugate, and the extra
successor edges of `a` in the successor have the same maximal value as the strict edge
`(a,i)` of the source, then the full highest-reachable-vertex maps are conjugate. -/
theorem gh2_conj (σ : Equiv.Perm (Fin n)) (hfix : ∀ u, u ≠ i → u ≠ y → σ u = u)
    (hinv : ∀ u, σ (σ u) = u) (hmono : ∀ x x', x ≤ x' → x ≠ i → σ x ≤ σ x')
    (b c : Bool) (θ θ' : Orientation B)
    (hr0 : ∀ u w, r0 i y θ' u w ↔ r0 i y θ (σ u) (σ w))
    (hY : gh (RT2 a i y t c θ') (σ y) = σ (gh (RP2 a i y t b θ) y))
    (hI : gh (RT2 a i y t c θ') (σ i) = σ (gh (RP2 a i y t b θ) i))
    (hA1 : gh (RT2 a i y t c θ') y ≤ gh (RP2 a i y t b θ) i)
    (hA2 : c = true → gh (RT2 a i y t c θ') i ≤ gh (RP2 a i y t b θ) i)
    (hA3 : gh (RT2 a i y t c θ') y = gh (RP2 a i y t b θ) i ∨
      (c = true ∧ gh (RT2 a i y t c θ') i = gh (RP2 a i y t b θ) i)) :
    ∀ u, gh (RT2 a i y t c θ') (σ u) = σ (gh (RP2 a i y t b θ) u) := by
  have hiy' : i < y := i_lt_y hy
  refine down_induction fun u ih => ?_
  by_cases huy : u = y
  · rw [huy]; exact hY
  by_cases hui : u = i
  · rw [hui]; exact hI
  have hfu : σ u = u := hfix u hui huy
  by_cases hua : u = a
  · rw [hua] at hfu ih ⊢
    rw [hfu]
    have hPi : gh (RP2 a i y t b θ) i ≤ gh (RP2 a i y t b θ) a :=
      gh_le_of_step _ (show RP2 a i y t b θ a i from Or.inr rfl)
    have hgt : y < gh (RP2 a i y t b θ) a :=
      lt_of_lt_of_le hyt ((t_le_gh_RP2_i b θ).trans hPi)
    have hσPa : σ (gh (RP2 a i y t b θ) a) = gh (RP2 a i y t b θ) a :=
      hfix _ (ne_of_gt (hiy'.trans hgt)) (ne_of_gt hgt)
    rw [hσPa]
    apply gh_eq_of
    · exact le_gh _ a
    · intro w hw
      rcases (RT2_a_iff hy hai hiy c θ' w).1 hw with hw | rfl | ⟨rfl, hc⟩
      · have hw' := (hr0 a w).1 hw
        rw [hfu] at hw'
        have hv := ih (σ w) (r0_lt hw')
        rw [hinv] at hv
        rw [hv]
        have hle : gh (RP2 a i y t b θ) (σ w) ≤ gh (RP2 a i y t b θ) a :=
          gh_le_of_step _ ((RP2_a_iff hy hai hiy b θ _).2 (Or.inl hw'))
        calc σ (gh (RP2 a i y t b θ) (σ w)) ≤ σ (gh (RP2 a i y t b θ) a) :=
              hmono _ _ hle (gh_RP2_ne_i hy hyt b θ _)
          _ = gh (RP2 a i y t b θ) a := hσPa
      · exact hA1.trans hPi
      · exact (hA2 hc).trans hPi
    · rcases gh_cases (RP2 a i y t b θ) a with h | ⟨v, hv, hv'⟩
      · exact Or.inl h
      · right
        rcases (RP2_a_iff hy hai hiy b θ v).1 hv with hv0 | rfl
        · refine ⟨σ v, (RT2_a_iff hy hai hiy c θ' _).2
            (Or.inl ((hr0 a (σ v)).2 (by rw [hfu, hinv]; exact hv0))), ?_⟩
          rw [ih v (r0_lt hv0), hv', hσPa]
        · rcases hA3 with h3 | ⟨hc, h3⟩
          · exact ⟨y, (RT2_a_iff hy hai hiy c θ' _).2 (Or.inr (Or.inl rfl)), by rw [h3, hv']⟩
          · exact ⟨v, (RT2_a_iff hy hai hiy c θ' _).2 (Or.inr (Or.inr ⟨rfl, hc⟩)),
              by rw [h3, hv']⟩
  · refine transfer_step (RP2 a i y t b θ) (RT2 a i y t c θ') σ σ u rfl (fun w => ?_)
      (fun v hv => ih v (RP2_lt hy hyt hai hv)) (hmono _ _ (le_gh _ u) hui)
      (fun v hv => hmono _ _ (gh_le_of_step _ hv) (gh_RP2_ne_i hy hyt b θ v))
    rw [hfu, RT2_iff_r0_of_ne hiy c θ' hua hui huy, hr0, hfu]
    constructor
    · intro h
      exact ⟨σ w, (RP2_iff_r0_of_ne hiy b θ hua hui huy _).2 h, (hinv w).symm⟩
    · rintro ⟨v, hv, rfl⟩
      rw [hinv]
      exact (RP2_iff_r0_of_ne hiy b θ hua hui huy v).1 hv

include hy hyt hai hiy in
/-- Fibre monomials agree when the background is unchanged away from `(i,y)`. -/
theorem fiberMono2_of_same (b c : Bool) (θ θ' : Orientation B)
    (hr0 : ∀ u w, r0 i y θ' u w ↔ r0 i y θ u w)
    (hY : gh (RT2 a i y t c θ') y = gh (RP2 a i y t b θ) y)
    (hI : gh (RT2 a i y t c θ') i = gh (RP2 a i y t b θ) i)
    (hA1 : gh (RT2 a i y t c θ') y ≤ gh (RP2 a i y t b θ) i)
    (hA3 : gh (RT2 a i y t c θ') y = gh (RP2 a i y t b θ) i ∨ c = true) :
    fiberMono (gh (RT2 a i y t c θ')) = fiberMono (gh (RP2 a i y t b θ)) :=
  fiberMono_conj _ _ (Equiv.refl _) (Equiv.refl _)
    (gh2_conj hy hyt hai hiy (Equiv.refl _) (fun _ _ _ => rfl) (fun _ => rfl)
      (fun _ _ h _ => h) b c θ θ' hr0 hY hI hA1 (fun _ => hI.le)
      (hA3.imp_right fun hc => ⟨hc, hI⟩))

include hy hyt hai hiy in
/-- Fibre monomials agree when the background is swapped by `(i y)` away from `(i,y)`. -/
theorem fiberMono2_of_swap (b c : Bool) (θ θ' : Orientation B)
    (hr0 : ∀ u w, r0 i y θ' u w ↔ r0 i y θ (Equiv.swap i y u) (Equiv.swap i y w))
    (hY : gh (RT2 a i y t c θ') i = Equiv.swap i y (gh (RP2 a i y t b θ) y))
    (hI : gh (RT2 a i y t c θ') y = gh (RP2 a i y t b θ) i)
    (hA2 : c = true → gh (RT2 a i y t c θ') i ≤ gh (RP2 a i y t b θ) i) :
    fiberMono (gh (RT2 a i y t c θ')) = fiberMono (gh (RP2 a i y t b θ)) := by
  have hgt : y < gh (RP2 a i y t b θ) i := lt_of_lt_of_le hyt (t_le_gh_RP2_i b θ)
  refine fiberMono_conj _ _ (Equiv.swap i y) (Equiv.swap i y)
    (gh2_conj hy hyt hai hiy (Equiv.swap i y) (fun u h1 h2 => Equiv.swap_apply_of_ne_of_ne h1 h2)
      (fun u => Equiv.swap_apply_self _ _ _)
      (fun x x' h hx => swap_mono hy h (fun h' => hx h'.1)) b c θ θ' hr0 ?_ ?_
      (hI.le) hA2 (Or.inl hI))
  · rw [Equiv.swap_apply_right]; exact hY
  · rw [Equiv.swap_apply_left, hI, swap_fix_of_lt hy hgt]

end SecondTransport

end BounceHRV
end VerticalStripLLT
