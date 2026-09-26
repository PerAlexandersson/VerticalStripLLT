import VerticalStripLLT.BounceRelations
-- Local helper module: VerticalStripLLT.BounceDistinguished

/-! ## Highest reachable vertices at the three distinguished vertices -/

namespace VerticalStripLLT
namespace BounceHRV

open scoped BigOperators

variable {n : ℕ}

theorem gh_extra (r r0 : Fin n → Fin n → Prop) (u : Fin n) (X : Fin n → Prop)
    (hsucc : ∀ w, r u w ↔ r0 u w ∨ X w) (hagree : ∀ w, r0 u w → gh r w = gh r0 w)
    (m : Fin n) (hm1 : ∀ w, X w → gh r w ≤ m) (hm2 : m = u ∨ ∃ w, X w ∧ gh r w = m) :
    gh r u = max (gh r0 u) m := by
  apply gh_eq_of
  · exact (le_gh r0 u).trans (le_max_left _ _)
  · intro w hw
    rcases (hsucc w).1 hw with hw | hw
    · rw [hagree w hw]
      exact (gh_le_of_step r0 hw).trans (le_max_left _ _)
    · exact (hm1 w hw).trans (le_max_right _ _)
  · rcases le_total m (gh r0 u) with hle | hle
    · rw [max_eq_left hle]
      rcases gh_cases r0 u with h | ⟨v, hv, hv'⟩
      · exact Or.inl h
      · exact Or.inr ⟨v, (hsucc v).2 (Or.inl hv), by rw [hagree v hv, hv']⟩
    · rw [max_eq_right hle]
      rcases hm2 with h | ⟨w, hw, hw'⟩
      · exact Or.inl h
      · exact Or.inr ⟨w, (hsucc w).2 (Or.inr hw), hw'⟩

theorem swap_mono {i y : Fin n} (hy : y.val = i.val + 1) {x x' : Fin n} (hle : x ≤ x')
    (hne : ¬(x = i ∧ x' = y)) : Equiv.swap i y x ≤ Equiv.swap i y x' := by
  rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
  rw [Fin.le_def] at hle
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;>
    simp only [Fin.ext_iff, Fin.le_def] at * <;> lia

theorem swap_fix_of_lt {i y : Fin n} (hy : y.val = i.val + 1) {x : Fin n} (hx : y < x) :
    Equiv.swap i y x = x := by
  rw [Fin.lt_def] at hx
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h; rw [h] at hx; lia
  · intro h; rw [h] at hx; lia

section Distinguished

variable {B : SchroderPath n} {i y t : Fin n} (hy : y.val = i.val + 1) (hyt : y < t)
  (hiy : (i, y) ∈ B.normalEdges)

include hy in
theorem i_lt_y : i < y := by rw [Fin.lt_def]; lia

include hy in
theorem r0_succ_i {θ : Orientation B} {w : Fin n} (h : r0 i y θ i w) : y < w := by
  have h1 := r0_lt h
  have h2 : w ≠ y := fun hw => h.2 (by rw [hw])
  rw [Fin.lt_def] at h1 ⊢
  have : w.val ≠ y.val := fun hv => h2 (Fin.ext hv)
  lia

theorem r0_succ_y {θ : Orientation B} {w : Fin n} (h : r0 i y θ y w) : y < w := r0_lt h

include hy in
theorem A_cases (θ : Orientation B) : gh (r0 i y θ) i = i ∨ y < gh (r0 i y θ) i := by
  rcases gh_cases (r0 i y θ) i with h | ⟨v, hv, hv'⟩
  · exact Or.inl h
  · exact Or.inr (hv' ▸ lt_of_lt_of_le (r0_succ_i hy hv) (le_gh _ v))

theorem C_cases (θ : Orientation B) : gh (r0 i y θ) y = y ∨ y < gh (r0 i y θ) y := by
  rcases gh_cases (r0 i y θ) y with h | ⟨v, hv, hv'⟩
  · exact Or.inl h
  · exact Or.inr (hv' ▸ lt_of_lt_of_le (r0_succ_y hv) (le_gh _ v))

include hiy in
theorem RP_iff_r0_of_ne (b : Bool) (θ : Orientation B) {u : Fin n} (hi : u ≠ i) (hy' : u ≠ y)
    (w : Fin n) : RP i y t b θ u w ↔ r0 i y θ u w := by
  unfold RP
  rw [upwardStep_iff_r0 hiy]
  constructor
  · rintro ((h | ⟨h, _⟩) | h | ⟨h, _⟩)
    · exact h
    · exact absurd (Prod.mk.inj h).1 hi
    · exact absurd (Prod.mk.inj h).1 hi
    · exact absurd (Prod.mk.inj h).1 hy'
  · intro h; exact Or.inl (Or.inl h)

include hiy in
theorem RT_iff_r0_of_ne (θ : Orientation B) {u : Fin n} (hi : u ≠ i) (hy' : u ≠ y)
    (w : Fin n) : RT y t θ u w ↔ r0 i y θ u w := by
  unfold RT
  rw [upwardStep_iff_r0 hiy]
  constructor
  · rintro ((h | ⟨h, _⟩) | h)
    · exact h
    · exact absurd (Prod.mk.inj h).1 hi
    · exact absurd (Prod.mk.inj h).1 hy'
  · intro h; exact Or.inl (Or.inl h)

include hy hyt in
theorem RP_lt {b : Bool} {θ : Orientation B} {u w : Fin n} (h : RP i y t b θ u w) : u < w := by
  rcases h with h | h | ⟨h, _⟩
  · exact upwardStep_lt h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact (i_lt_y hy).trans hyt
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hyt

include hyt in
theorem RT_lt {θ : Orientation B} {u w : Fin n} (h : RT y t θ u w) : u < w := by
  rcases h with h | h
  · exact upwardStep_lt h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hyt

include hy hiy in
theorem RP_above (b : Bool) (θ : Orientation B) :
    ∀ w, y < w → gh (RP i y t b θ) w = gh (r0 i y θ) w :=
  gh_agree_above _ _ y (fun _ _ h => r0_lt h) fun _ hu w =>
    RP_iff_r0_of_ne hiy b θ (ne_of_gt ((i_lt_y hy).trans hu)) (ne_of_gt hu) w

include hy hiy in
theorem RT_above (θ : Orientation B) :
    ∀ w, y < w → gh (RT y t θ) w = gh (r0 i y θ) w :=
  gh_agree_above _ _ y (fun _ _ h => r0_lt h) fun _ hu w =>
    RT_iff_r0_of_ne hiy θ (ne_of_gt ((i_lt_y hy).trans hu)) (ne_of_gt hu) w

include hy hyt hiy in
theorem gh_RP_y (b : Bool) (θ : Orientation B) :
    gh (RP i y t b θ) y = if b then max (gh (r0 i y θ) y) (gh (r0 i y θ) t)
      else gh (r0 i y θ) y := by
  have hne : y ≠ i := ne_of_gt (i_lt_y hy)
  rw [gh_extra (RP i y t b θ) (r0 i y θ) y (fun w => w = t ∧ b = true) ?_
    (fun w hw => RP_above hy hiy b θ w (r0_succ_y hw))
    (if b then gh (r0 i y θ) t else y) ?_ ?_]
  · cases b
    · simp [le_gh]
    · simp
  · intro w
    unfold RP
    rw [upwardStep_iff_r0 hiy]
    constructor
    · rintro ((h | ⟨h, _⟩) | h | ⟨h, hb⟩)
      · exact Or.inl h
      · exact absurd (Prod.mk.inj h).1 hne
      · exact absurd (Prod.mk.inj h).1 hne
      · exact Or.inr ⟨(Prod.mk.inj h).2, hb⟩
    · rintro (h | ⟨rfl, hb⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inr ⟨rfl, hb⟩)
  · rintro w ⟨hw, hb⟩
    rw [hw, RP_above (t := t) hy hiy b θ t hyt, hb, ite_eq_left rfl]
  · cases b
    · simp
    · exact Or.inr ⟨t, ⟨rfl, rfl⟩, by rw [RP_above (t := t) hy hiy true θ t hyt]; simp⟩

include hy hyt hiy in
theorem gh_RT_y (θ : Orientation B) :
    gh (RT y t θ) y = max (gh (r0 i y θ) y) (gh (r0 i y θ) t) := by
  have hne : y ≠ i := ne_of_gt (i_lt_y hy)
  rw [gh_extra (RT y t θ) (r0 i y θ) y (fun w => w = t) ?_
    (fun w hw => RT_above hy hiy θ w (r0_succ_y hw)) (gh (r0 i y θ) t) ?_ ?_]
  · intro w
    unfold RT
    rw [upwardStep_iff_r0 hiy]
    constructor
    · rintro ((h | ⟨h, _⟩) | h)
      · exact Or.inl h
      · exact absurd (Prod.mk.inj h).1 hne
      · exact Or.inr (Prod.mk.inj h).2
    · rintro (h | rfl)
      · exact Or.inl (Or.inl h)
      · exact Or.inr rfl
  · rintro w hw
    rw [hw, RT_above (t := t) hy hiy θ t hyt]
  · exact Or.inr ⟨t, rfl, RT_above (t := t) hy hiy θ t hyt⟩

include hy hyt hiy in
theorem gh_RP_i (b : Bool) (θ : Orientation B) :
    gh (RP i y t b θ) i = if bitOf hiy θ then
      max (gh (r0 i y θ) i) (max (gh (r0 i y θ) y) (gh (r0 i y θ) t))
      else max (gh (r0 i y θ) i) (gh (r0 i y θ) t) := by
  have hne : i ≠ y := ne_of_lt (i_lt_y hy)
  have hH := RP_above (t := t) hy hiy b θ t hyt
  have hY := gh_RP_y hy hyt hiy b θ
  rw [gh_extra (RP i y t b θ) (r0 i y θ) i
    (fun w => (w = y ∧ bitOf hiy θ = true) ∨ w = t) ?_
    (fun w hw => RP_above hy hiy b θ w (r0_succ_i hy hw))
    (if bitOf hiy θ then max (gh (RP i y t b θ) y) (gh (r0 i y θ) t)
      else gh (r0 i y θ) t) ?_ ?_]
  · rw [hY]
    cases bitOf hiy θ
    · simp
    · cases b
      · simp
      · simp only [ite_true]
        rw [max_eq_left (le_max_right (gh (r0 i y θ) y) (gh (r0 i y θ) t))]
  · intro w
    unfold RP
    rw [upwardStep_iff_r0 hiy]
    constructor
    · rintro ((h | ⟨h, hb⟩) | h | ⟨h, _⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨(Prod.mk.inj h).2, hb⟩)
      · exact Or.inr (Or.inr (Prod.mk.inj h).2)
      · exact absurd (Prod.mk.inj h).1 hne
    · rintro (h | ⟨rfl, hb⟩ | hw)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨rfl, hb⟩)
      · exact Or.inr (Or.inl (by rw [hw]))
  · rintro w (⟨rfl, hb⟩ | hw)
    · rw [hb, ite_eq_left rfl]; exact le_max_left _ _
    · rw [hw, hH]
      split_ifs
      · exact le_max_right _ _
      · exact le_rfl
  · right
    split_ifs with hb
    · rcases le_total (gh (RP i y t b θ) y) (gh (r0 i y θ) t) with hle | hle
      · exact ⟨t, Or.inr rfl, by rw [hH, max_eq_right hle]⟩
      · exact ⟨y, Or.inl ⟨rfl, hb⟩, by rw [max_eq_left hle]⟩
    · exact ⟨t, Or.inr rfl, hH⟩

include hy hyt hiy in
theorem gh_RT_i (θ : Orientation B) :
    gh (RT y t θ) i = if bitOf hiy θ then
      max (gh (r0 i y θ) i) (max (gh (r0 i y θ) y) (gh (r0 i y θ) t))
      else gh (r0 i y θ) i := by
  have hne : i ≠ y := ne_of_lt (i_lt_y hy)
  have hY := gh_RT_y hy hyt hiy θ
  rw [gh_extra (RT y t θ) (r0 i y θ) i (fun w => w = y ∧ bitOf hiy θ = true) ?_
    (fun w hw => RT_above hy hiy θ w (r0_succ_i hy hw))
    (if bitOf hiy θ then gh (RT y t θ) y else i) ?_ ?_]
  · rw [hY]
    cases bitOf hiy θ
    · simp [le_gh]
    · simp
  · intro w
    unfold RT
    rw [upwardStep_iff_r0 hiy]
    constructor
    · rintro ((h | ⟨h, hb⟩) | h)
      · exact Or.inl h
      · exact Or.inr ⟨(Prod.mk.inj h).2, hb⟩
      · exact absurd (Prod.mk.inj h).1 hne
    · rintro (h | ⟨rfl, hb⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨rfl, hb⟩)
  · rintro w ⟨rfl, hb⟩
    rw [hb, ite_eq_left rfl]
  · split_ifs with hb
    · exact Or.inr ⟨y, ⟨rfl, hb⟩, rfl⟩
    · exact Or.inl rfl

include hy hyt in
theorem gh_RP_ne_i (b : Bool) (θ : Orientation B) (v : Fin n) : gh (RP i y t b θ) v ≠ i := by
  intro h
  have hreach := gh_reach (RP i y t b θ) v
  rw [h] at hreach
  have ht := le_gh_of_reach (RP i y t b θ)
    (hreach.tail (show RP i y t b θ i t from Or.inr (Or.inl rfl)))
  rw [h] at ht
  exact absurd ((i_lt_y hy).trans hyt) (not_lt.2 ht)

end Distinguished

end BounceHRV
end VerticalStripLLT

