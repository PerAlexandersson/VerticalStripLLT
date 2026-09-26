import VerticalStripLLT.Circular.ReverseBounceContacts
import VerticalStripLLT.Circular.CountedBounce
import VerticalStripLLT.Circular.DNStrictRows
import VerticalStripLLT.Circular.ContactEndpoints
import VerticalStripLLT.Circular.NeutralContacts

/-! Counted reverse bounces in terms of iterated boundaries, and the residue
separation of their main and parallel contact rows. -/

namespace VerticalStripLLT.Circular.Diagram

variable {n : ℕ} (D : Diagram n)

/-- A double-strict contact row with no east gap. -/
def DDContact (z : ℤ) : Prop :=
  D.eastGap z = 0 ∧ D.strictAt z ∧ D.strictAt (z + 1)

theorem reverseBounceN_iff_iterate {s x : ℤ} {j : ℕ} :
    ReverseBounceN D s x j ↔
      x = D.boundary^[j + 1] s ∧
      (∀ i, 1 ≤ i → i ≤ j → D.DDContact (D.boundary^[i] s)) ∧
      D.eastGap x = 0 ∧ ¬ (D.strictAt x ∧ D.strictAt (x + 1)) := by
  induction j generalizing s with
  | zero =>
    rw [ReverseBounceN.zero_iff]
    constructor
    · rintro ⟨rfl, hg, hn⟩
      exact ⟨rfl, fun i h1 h2 => by lia, hg, hn⟩
    · rintro ⟨rfl, _, hg, hn⟩
      exact ⟨rfl, hg, hn⟩
  | succ j ih =>
    rw [reverseBounceN_succ_iff, ih, Function.iterate_succ_apply D.boundary (j + 1)]
    constructor
    · rintro ⟨hg, h1, h2, hx, hdd, hgx, hnx⟩
      refine ⟨hx, fun i hi1 hij => ?_, hgx, hnx⟩
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by lia⟩
      rw [Function.iterate_succ_apply]
      rcases Nat.eq_zero_or_pos i' with rfl | hi'
      · exact ⟨hg, h1, h2⟩
      · exact hdd i' hi' (by lia)
    · rintro ⟨hx, hdd, hgx, hnx⟩
      obtain ⟨hg, h1, h2⟩ := hdd 1 le_rfl (by lia)
      refine ⟨hg, h1, h2, hx, fun i hi1 hij => ?_, hgx, hnx⟩
      have := hdd (i + 1) (by lia) (by lia)
      rwa [Function.iterate_succ_apply] at this

end VerticalStripLLT.Circular.Diagram

namespace VerticalStripLLT.Circular.Diagram

variable {n : ℕ} {D : Diagram n} {t : ℤ} {k : ℕ}

theorem bounce_strict_iterate (ht : D.strictAt t)
    (hdd : ∀ i, 1 ≤ i → i ≤ k + 1 → D.DDContact (D.boundary^[i] t))
    (i : ℕ) (hi : i ≤ k + 1) : D.strictAt (D.boundary^[i] t) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · exact ht
  · exact (hdd i hi0 hi).2.1

theorem bounce_main_step (ht : D.strictAt t)
    (hdd : ∀ i, 1 ≤ i → i ≤ k + 1 → D.DDContact (D.boundary^[i] t))
    (i : ℕ) (hi : i ≤ k + 1) :
    D.edgeData.selected ∅ (D.residue (D.boundary^[i + 1] t))
      (D.residue (D.boundary^[i] t)) := by
  rw [Function.iterate_succ_apply']
  exact D.selected_of_strictAt (bounce_strict_iterate ht hdd i hi)

theorem bounce_parallel_step
    (hdd : ∀ i, 1 ≤ i → i ≤ k + 1 → D.DDContact (D.boundary^[i] t))
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ k + 1) :
    D.edgeData.selected ∅ (D.residue (D.boundary^[i + 1] t + 1))
      (D.residue (D.boundary^[i] t + 1)) := by
  rw [Function.iterate_succ_apply']
  obtain ⟨hg, h1, h2⟩ := hdd i hi1 hi
  exact D.parallel_selected_of_dd hg h1 h2

theorem bounce_reach (ht : D.strictAt t)
    (hdd : ∀ i, 1 ≤ i → i ≤ k + 1 → D.DDContact (D.boundary^[i] t))
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ k + 2) :
    Relation.ReflTransGen (D.edgeData.selected ∅) (D.residue (D.boundary^[i] t))
      (D.residue (D.boundary t)) := by
  induction i with
  | zero => lia
  | succ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.head (bounce_main_step ht hdd i (by lia))
        (ih hi0 (by lia))

theorem bounce_residue_ne_root (ht : D.strictAt t) (ha : D.edgeData.Admissible ∅)
    (hdd : ∀ i, 1 ≤ i → i ≤ k + 1 → D.DDContact (D.boundary^[i] t))
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ k + 2) :
    D.residue (D.boundary^[i] t) ≠ D.residue t := by
  intro heq
  have hr := bounce_reach ht hdd i hi1 hi
  rw [heq] at hr
  exact ha _ (Relation.TransGen.tail' hr (D.selected_of_strictAt ht))

theorem bounce_residue_ne_contact (ht : D.strictAt t) (ha : D.edgeData.Admissible ∅)
    (hdd : ∀ i, 1 ≤ i → i ≤ k + 1 → D.DDContact (D.boundary^[i] t))
    (i : ℕ) (hi1 : 2 ≤ i) (hi : i ≤ k + 2) :
    D.residue (D.boundary^[i] t) ≠ D.residue (D.boundary t) := by
  intro heq
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by lia⟩
  have hs := bounce_main_step ht hdd i' (by lia)
  have hr := bounce_reach ht hdd i' (by lia) (by lia)
  rw [heq] at hs
  exact ha _ (Relation.TransGen.head' hs hr)

theorem bounce_residue_ne_parallel_end (htE : D.EligibleDE t) (hn : 2 ≤ n)
    (hdd : ∀ i, 1 ≤ i → i ≤ k + 1 → D.DDContact (D.boundary^[i] t))
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ k + 2) :
    D.residue (D.boundary^[i] t) ≠ D.residue (D.boundary t + 1) := by
  intro heq
  have hr := bounce_reach htE.1 hdd i hi1 hi
  rw [heq] at hr
  rcases Relation.ReflTransGen.cases_head hr with h | ⟨v, hv, _⟩
  · exact D.residue_p_ne_succ hn _ h.symm
  · exact htE.parallel_end_free D v hv

theorem bounce_succ_residue_ne_parallel_end (ht : D.strictAt t)
    (ha : D.edgeData.Admissible ∅)
    (hdd : ∀ i, 1 ≤ i → i ≤ k + 1 → D.DDContact (D.boundary^[i] t))
    (i : ℕ) (hi1 : 2 ≤ i) (hi : i ≤ k + 2) :
    D.residue (D.boundary^[i] t + 1) ≠ D.residue (D.boundary t + 1) := by
  intro heq
  rw [D.residue_succ, D.residue_succ] at heq
  exact bounce_residue_ne_contact ht ha hdd i hi1 hi (D.area.next_injective heq)

/-- The parallel contact rows avoid the root and the last main contact. -/
theorem bounce_succ_residue_ne_main (ht : D.strictAt t)
    (hdd : ∀ i, 1 ≤ i → i ≤ k + 1 → D.DDContact (D.boundary^[i] t))
    (hx1 : ¬ D.strictAt (D.boundary^[k + 2] t + 1))
    (i j : ℕ) (hi1 : 2 ≤ i) (hi : i ≤ k + 2) (hj : j ≤ 1) :
    D.residue (D.boundary^[i] t + 1) ≠ D.residue (D.boundary^[j] t) := by
  intro heq
  have hshift : ∀ l, i + l ≤ k + 2 →
      D.residue (D.boundary^[i + l] t + 1) = D.residue (D.boundary^[j + l] t) := by
    intro l
    induction l with
    | zero => intro _; exact heq
    | succ l ih =>
      intro hl
      have hpar := bounce_parallel_step hdd (i + l) (by lia) (by lia)
      have hmain := bounce_main_step ht hdd (j + l) (by lia)
      rw [ih (by lia)] at hpar
      exact D.strict_selected_leftUnique hpar hmain
  have hlast := hshift (k + 2 - i) (by lia)
  rw [show i + (k + 2 - i) = k + 2 by lia] at hlast
  apply hx1
  rw [D.strictAt_iff_exists_selected, hlast]
  exact ⟨_, bounce_main_step ht hdd (j + (k + 2 - i)) (by lia)⟩

end VerticalStripLLT.Circular.Diagram



