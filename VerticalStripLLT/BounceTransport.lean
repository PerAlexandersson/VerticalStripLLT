import VerticalStripLLT.BounceDistinguished
-- Local helper module: VerticalStripLLT.BounceTransport

/-! ## Background values under the vertex swap -/

namespace VerticalStripLLT
namespace BounceHRV

open scoped BigOperators

variable {n : ℕ}

section SwapValues

variable {B : SchroderPath n} {i y : Fin n} (hy : y.val = i.val + 1)
  {θ θ' : Orientation B}
  (hr0 : ∀ u w, r0 i y θ' u w ↔ r0 i y θ (Equiv.swap i y u) (Equiv.swap i y w))

include hr0 in
theorem swap_steps (u w : Fin n) :
    r0 i y θ' (Equiv.swap i y u) w ↔ ∃ v, r0 i y θ u v ∧ w = Equiv.swap i y v := by
  rw [hr0, Equiv.swap_apply_self]
  exact ⟨fun h => ⟨_, h, (Equiv.swap_apply_self _ _ _).symm⟩,
    fun ⟨v, hv, he⟩ => by rw [he, Equiv.swap_apply_self]; exact hv⟩

include hy hr0 in
theorem swap_above : ∀ w, y < w → gh (r0 i y θ') w = gh (r0 i y θ) w := by
  refine gh_agree_above _ _ y (fun _ _ h => r0_lt h) fun u hu w => ?_
  rw [hr0, swap_fix_of_lt hy hu]
  by_cases hw : y < w
  · rw [swap_fix_of_lt hy hw]
  · have hle : w ≤ y := not_lt.1 hw
    have hsw : Equiv.swap i y w ≤ y := by
      rw [Equiv.swap_apply_def]
      split_ifs with h1 h2
      · exact le_rfl
      · exact (i_lt_y hy).le
      · exact hle
    constructor
    · intro h; exact absurd (lt_of_lt_of_le (hu.trans (r0_lt h)) hsw) (lt_irrefl _)
    · intro h; exact absurd (lt_of_lt_of_le (hu.trans (r0_lt h)) hle) (lt_irrefl _)

include hy hr0 in
theorem swap_value (u : Fin n) (hu : u = i ∨ u = y) :
    gh (r0 i y θ') (Equiv.swap i y u) = Equiv.swap i y (gh (r0 i y θ) u) := by
  have hsucc : ∀ v, r0 i y θ u v → y < v := by
    intro v hv
    rcases hu with rfl | rfl
    · exact r0_succ_i hy hv
    · exact r0_succ_y hv
  refine transfer_step (r0 i y θ) (r0 i y θ') (Equiv.swap i y) (Equiv.swap i y) u rfl
    (swap_steps hr0 u) (fun v hv => ?_) ?_ (fun v hv => ?_)
  · have h1 := hsucc v hv
    rw [swap_fix_of_lt hy h1, swap_above hy hr0 v h1,
      swap_fix_of_lt hy (lt_of_lt_of_le h1 (le_gh _ v))]
  · apply swap_mono hy (le_gh _ u)
    rintro ⟨rfl, h⟩
    rcases A_cases hy θ with h' | h'
    · rw [h'] at h; exact absurd h (ne_of_lt (i_lt_y hy))
    · rw [h] at h'; exact lt_irrefl _ h'
  · apply swap_mono hy (gh_le_of_step _ hv)
    rintro ⟨h, _⟩
    have := lt_of_lt_of_le (hsucc v hv) (le_gh (r0 i y θ) v)
    rw [h] at this
    exact absurd ((i_lt_y hy).trans this) (lt_irrefl _)

end SwapValues

/-! ## Transport of highest reachable vertices between source and successor -/

section Transport

variable {B : SchroderPath n} {i y t : Fin n} (hy : y.val = i.val + 1) (hyt : y < t)
  (hiy : (i, y) ∈ B.normalEdges)

include hy hyt hiy in
/-- Same background away from `(i,y)`: equal values at `i,y` give equal maps. -/
theorem gh_eq_of_same (b : Bool) (θ θ' : Orientation B)
    (hr0 : ∀ u w, r0 i y θ' u w ↔ r0 i y θ u w)
    (hY : gh (RT y t θ') y = gh (RP i y t b θ) y)
    (hI : gh (RT y t θ') i = gh (RP i y t b θ) i) :
    ∀ u, gh (RT y t θ') u = gh (RP i y t b θ) u := by
  refine down_induction fun u ih => ?_
  by_cases huy : u = y
  · rw [huy]; exact hY
  by_cases hui : u = i
  · rw [hui]; exact hI
  refine transfer_step (RP i y t b θ) (RT y t θ') id id u rfl (fun w => ?_)
    (fun v hv => ih v (RP_lt hy hyt hv)) (le_gh _ u) (fun v hv => gh_le_of_step _ hv)
  change RT y t θ' u w ↔ _
  rw [RT_iff_r0_of_ne hiy θ' hui huy, hr0]
  constructor
  · intro h; exact ⟨w, (RP_iff_r0_of_ne hiy b θ hui huy w).2 h, rfl⟩
  · rintro ⟨v, hv, hw⟩
    rw [show w = v from hw]
    exact (RP_iff_r0_of_ne hiy b θ hui huy v).1 hv

include hy hyt hiy in
/-- Swapped background away from `(i,y)`: exchanged values at `i,y` give conjugate maps. -/
theorem gh_eq_of_swap (b : Bool) (θ θ' : Orientation B)
    (hr0 : ∀ u w, r0 i y θ' u w ↔ r0 i y θ (Equiv.swap i y u) (Equiv.swap i y w))
    (hY : gh (RT y t θ') i = Equiv.swap i y (gh (RP i y t b θ) y))
    (hI : gh (RT y t θ') y = gh (RP i y t b θ) i) :
    ∀ u, gh (RT y t θ') (Equiv.swap i y u) = Equiv.swap i y (gh (RP i y t b θ) u) := by
  refine down_induction fun u ih => ?_
  by_cases huy : u = y
  · rw [huy, Equiv.swap_apply_right]; exact hY
  by_cases hui : u = i
  · rw [hui, Equiv.swap_apply_left, hI]
    have ht : t ≤ gh (RP i y t b θ) i :=
      (le_gh _ t).trans (gh_le_of_step _ (show RP i y t b θ i t from Or.inr (Or.inl rfl)))
    rw [swap_fix_of_lt hy (lt_of_lt_of_le hyt ht)]
  have hfix : Equiv.swap i y u = u := Equiv.swap_apply_of_ne_of_ne hui huy
  refine transfer_step (RP i y t b θ) (RT y t θ') (Equiv.swap i y) (Equiv.swap i y) u rfl
    (fun w => ?_) (fun v hv => ih v (RP_lt hy hyt hv)) ?_
    (fun v hv => swap_mono hy (gh_le_of_step _ hv) (fun h => gh_RP_ne_i hy hyt b θ v h.1))
  · rw [hfix, RT_iff_r0_of_ne hiy θ' hui huy, hr0, hfix]
    constructor
    · intro h
      exact ⟨Equiv.swap i y w, (RP_iff_r0_of_ne hiy b θ hui huy _).2 h,
        (Equiv.swap_apply_self _ _ _).symm⟩
    · rintro ⟨v, hv, rfl⟩
      rw [Equiv.swap_apply_self]
      exact (RP_iff_r0_of_ne hiy b θ hui huy v).1 hv
  · exact swap_mono hy (le_gh _ u) (fun h => hui h.1)

end Transport

end BounceHRV
end VerticalStripLLT

