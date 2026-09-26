import VerticalStripLLT.SecondBounceRelations
-- Local helper module: VerticalStripLLT.SecondBounceDistinguished

/-! ## Highest reachable vertices of the second-bounce relations at `a`, `i`, `y` -/

namespace VerticalStripLLT
namespace BounceHRV

open scoped BigOperators

variable {n : ℕ}

section SecondDistinguished

variable {B : SchroderPath n} {a i y t : Fin n} (hy : y.val = i.val + 1) (hyt : y < t)
  (hai : a < i) (hiy : (i, y) ∈ B.normalEdges)

include hy hyt hai in
theorem RP2_lt {b : Bool} {θ : Orientation B} {u w : Fin n} (h : RP2 a i y t b θ u w) :
    u < w := by
  rcases h with h | h
  · exact RP_lt hy hyt h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hai

include hy hyt hai in
theorem RT2_lt {c : Bool} {θ : Orientation B} {u w : Fin n} (h : RT2 a i y t c θ u w) :
    u < w := by
  rcases h with h | h | ⟨h, _⟩
  · exact RT_lt hyt h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hai.trans (i_lt_y hy)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hai

include hy hyt in
theorem RP2_above (b : Bool) (θ : Orientation B) :
    ∀ v, a < v → gh (RP2 a i y t b θ) v = gh (RP i y t b θ) v :=
  gh_agree_above _ _ a (fun _ _ h => RP_lt hy hyt h) fun _ hu _ =>
    ⟨fun h => h.elim id (fun h => absurd (Prod.mk.inj h).1 (ne_of_gt hu)), Or.inl⟩

include hyt in
theorem RT2_above (c : Bool) (θ : Orientation B) :
    ∀ v, a < v → gh (RT2 a i y t c θ) v = gh (RT y t θ) v :=
  gh_agree_above _ _ a (fun _ _ h => RT_lt hyt h) fun _ hu _ =>
    ⟨fun h => h.elim id (fun h => h.elim (fun h => absurd (Prod.mk.inj h).1 (ne_of_gt hu))
      (fun h => absurd (Prod.mk.inj h.1).1 (ne_of_gt hu))), Or.inl⟩

include hy hyt hai hiy in
theorem gh_RP2_y (b : Bool) (θ : Orientation B) :
    gh (RP2 a i y t b θ) y = if b then max (gh (r0 i y θ) y) (gh (r0 i y θ) t)
      else gh (r0 i y θ) y := by
  rw [RP2_above hy hyt b θ y (hai.trans (i_lt_y hy))]
  exact gh_RP_y hy hyt hiy b θ

include hy hyt hai hiy in
theorem gh_RP2_i (b : Bool) (θ : Orientation B) :
    gh (RP2 a i y t b θ) i = if bitOf hiy θ then
      max (gh (r0 i y θ) i) (max (gh (r0 i y θ) y) (gh (r0 i y θ) t))
      else max (gh (r0 i y θ) i) (gh (r0 i y θ) t) := by
  rw [RP2_above hy hyt b θ i hai]
  exact gh_RP_i hy hyt hiy b θ

include hy hyt hai hiy in
theorem gh_RT2_y (c : Bool) (θ : Orientation B) :
    gh (RT2 a i y t c θ) y = max (gh (r0 i y θ) y) (gh (r0 i y θ) t) := by
  rw [RT2_above hyt c θ y (hai.trans (i_lt_y hy))]
  exact gh_RT_y hy hyt hiy θ

include hy hyt hai hiy in
theorem gh_RT2_i (c : Bool) (θ : Orientation B) :
    gh (RT2 a i y t c θ) i = if bitOf hiy θ then
      max (gh (r0 i y θ) i) (max (gh (r0 i y θ) y) (gh (r0 i y θ) t))
      else gh (r0 i y θ) i := by
  rw [RT2_above hyt c θ i hai]
  exact gh_RT_i hy hyt hiy θ

include hiy in
theorem RP2_iff_r0_of_ne (b : Bool) (θ : Orientation B) {u : Fin n} (ha : u ≠ a) (hi : u ≠ i)
    (hy' : u ≠ y) (w : Fin n) : RP2 a i y t b θ u w ↔ r0 i y θ u w := by
  unfold RP2
  rw [RP_iff_r0_of_ne hiy b θ hi hy' w]
  exact ⟨fun h => h.elim id (fun h => absurd (Prod.mk.inj h).1 ha), Or.inl⟩

include hiy in
theorem RT2_iff_r0_of_ne (c : Bool) (θ : Orientation B) {u : Fin n} (ha : u ≠ a) (hi : u ≠ i)
    (hy' : u ≠ y) (w : Fin n) : RT2 a i y t c θ u w ↔ r0 i y θ u w := by
  unfold RT2
  rw [RT_iff_r0_of_ne hiy θ hi hy' w]
  exact ⟨fun h => h.elim id (fun h => h.elim (fun h => absurd (Prod.mk.inj h).1 ha)
    (fun h => absurd (Prod.mk.inj h.1).1 ha)), Or.inl⟩

include hy hai hiy in
theorem RP2_a_iff (b : Bool) (θ : Orientation B) (w : Fin n) :
    RP2 a i y t b θ a w ↔ r0 i y θ a w ∨ w = i := by
  unfold RP2
  rw [RP_iff_r0_of_ne hiy b θ (ne_of_lt hai) (ne_of_lt (hai.trans (i_lt_y hy))) w]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Prod.mk.inj h).2
  · rintro (h | rfl)
    · exact Or.inl h
    · exact Or.inr rfl

include hy hai hiy in
theorem RT2_a_iff (c : Bool) (θ : Orientation B) (w : Fin n) :
    RT2 a i y t c θ a w ↔ r0 i y θ a w ∨ w = y ∨ (w = i ∧ c = true) := by
  unfold RT2
  rw [RT_iff_r0_of_ne hiy θ (ne_of_lt hai) (ne_of_lt (hai.trans (i_lt_y hy))) w]
  constructor
  · rintro (h | h | ⟨h, hc⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl (Prod.mk.inj h).2)
    · exact Or.inr (Or.inr ⟨(Prod.mk.inj h).2, hc⟩)
  · rintro (h | rfl | ⟨rfl, hc⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨rfl, hc⟩)

theorem t_le_gh_RP2_i (b : Bool) (θ : Orientation B) : t ≤ gh (RP2 a i y t b θ) i :=
  (le_gh _ t).trans (gh_le_of_step _ (show RP2 a i y t b θ i t from Or.inl (Or.inr (Or.inl rfl))))

include hy hyt in
theorem gh_RP2_ne_i (b : Bool) (θ : Orientation B) (v : Fin n) :
    gh (RP2 a i y t b θ) v ≠ i := by
  intro h
  have hreach := gh_reach (RP2 a i y t b θ) v
  rw [h] at hreach
  have ht := le_gh_of_reach (RP2 a i y t b θ)
    (hreach.tail (show RP2 a i y t b θ i t from Or.inl (Or.inr (Or.inl rfl))))
  rw [h] at ht
  exact absurd ((i_lt_y hy).trans hyt) (not_lt.2 ht)

end SecondDistinguished

end BounceHRV
end VerticalStripLLT
