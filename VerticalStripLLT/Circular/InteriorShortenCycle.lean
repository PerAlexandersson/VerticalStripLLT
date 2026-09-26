import VerticalStripLLT.Circular.InteriorFirstContact
import VerticalStripLLT.Circular.NDSeparatedBasic

/-! Shortening the original root in an interior overlap closes a strict cycle.
This describes the target geometry; it does not assert an ND recurrence. -/

namespace VerticalStripLLT.Circular.Diagram

private theorem parallel_contact_path {n : ℕ} {D : Diagram n} {t : ℤ} {k : ℕ}
    (hdd : ∀ i, 1 ≤ i → i ≤ k + 1 → D.DDContact (D.boundary^[i] t))
    {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ k + 2) :
    Relation.TransGen (D.edgeData.selected ∅)
      (D.residue (D.boundary^[b] t + 1)) (D.residue (D.boundary^[a] t + 1)) := by
  induction b with
  | zero => lia
  | succ b ih =>
    have hs := bounce_parallel_step hdd b (by lia) (by lia)
    by_cases heq : a = b
    · subst a
      exact Relation.TransGen.single hs
    · exact Relation.TransGen.head hs (ih (by lia) (by lia))

/-- In an acyclic interior-overlap source, the naively shortened root is cyclic. -/
theorem shortenEligible_not_admissible_of_interior_overlap {n : ℕ} (D : Diagram n)
    {t x : ℤ} {k : ℕ} (ha : D.edgeData.Admissible ∅) (ht : D.EligibleDE t)
    (h : ReverseBounceN D t x (k + 1))
    (hinner : ∃ i : ℕ, 1 ≤ i ∧ i ≤ k + 1 ∧
      D.residue (D.boundary^[i] t) = D.residue (x + 1)) :
    ¬ (D.shortenEligible t ht).edgeData.Admissible ∅ := by
  classical
  obtain ⟨i, hi1, hik, hires⟩ := hinner
  obtain ⟨hx, hdd, _, _⟩ := (D.reverseBounceN_iff_iterate).mp h
  subst x
  have hprop : ∀ l, l ≤ i →
      D.residue (D.boundary^[i - l] t) = D.residue (D.boundary^[k + 2 - l] t + 1) := by
    intro l
    induction l with
    | zero => intro _; simpa using hires
    | succ l ih =>
      intro hl
      have hmain := bounce_main_step ht.1 hdd (i - (l + 1)) (by lia)
      have hpar := bounce_parallel_step hdd (k + 1 - l) (by lia) (by lia)
      rw [show i - (l + 1) + 1 = i - l by lia, ih (by lia)] at hmain
      rw [show k + 1 - l + 1 = k + 2 - l by lia] at hpar
      rw [show k + 2 - (l + 1) = k + 1 - l by lia]
      exact D.strict_selected_rightUnique hmain hpar
  let j := k + 2 - i
  have hj1 : 1 ≤ j := by dsimp [j]; lia
  have hjk : j ≤ k + 1 := by dsimp [j]; lia
  have hroot : D.residue (D.boundary^[j] t + 1) = D.residue t := by
    simpa only [Nat.sub_self, Function.iterate_zero_apply] using (hprop i le_rfl).symm
  let Q := D.shortenEligible t ht
  have hboundary (z : ℤ) (hz : D.residue z ≠ D.residue t) :
      Q.boundary z = D.boundary z := by
    unfold boundary
    change z - (Q.area.area (D.residue z) : ℤ) = _
    rw [show Q.area.area = _ from D.shortenEligible_area t ht,
      Function.update_of_ne hz]
  have hstep (r : ℕ) (hr1 : 1 ≤ r) (hrj : r < j) :
      Q.edgeData.selected ∅ (D.residue (D.boundary^[r + 1] t + 1))
        (D.residue (D.boundary^[r] t + 1)) := by
    have hne : D.residue (D.boundary^[r] t + 1) ≠ D.residue t := by
      intro heq
      have hp := parallel_contact_path hdd hr1 hrj (by lia : j ≤ k + 2)
      rw [hroot, heq] at hp
      exact ha _ hp
    have hs := bounce_parallel_step hdd r hr1 (by lia)
    rw [D.ndSep_selected_residue_iff] at hs
    apply (Q.ndSep_selected_residue_iff _ _).mpr
    refine ⟨(D.shortenEligible_strictAt_iff t ht _).mpr hs.1, ?_⟩
    rw [hboundary _ hne]
    exact hs.2
  have hreach : ∀ r, 1 ≤ r → r ≤ j →
      Relation.ReflTransGen (Q.edgeData.selected ∅)
        (D.residue (D.boundary^[r] t + 1)) (D.residue (D.boundary t + 1)) := by
    intro r
    induction r with
    | zero => intro hr; lia
    | succ r ih =>
      intro hr hrj
      by_cases hr0 : r = 0
      · subst r
        exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.head (hstep r (by lia) (by lia))
          (ih (by lia) (by lia))
  have hbroot : Q.boundary t = D.boundary t + 1 := by
    unfold boundary
    change t - (Q.area.area (D.residue t) : ℤ) = _
    rw [show Q.area.area = _ from D.shortenEligible_area t ht, Function.update_self]
    have := ht.2.1
    lia
  have hclose := Q.selected_of_strictAt ((D.shortenEligible_strictAt_iff t ht t).mpr ht.1)
  rw [hbroot] at hclose
  have hp := hreach j hj1 le_rfl
  rw [hroot] at hp
  intro hQ
  exact hQ _ (Relation.TransGen.tail' hp hclose)

theorem coloringLLT_shortenEligible_eq_zero_of_interior_overlap {n : ℕ} (D : Diagram n)
    {t x : ℤ} {k : ℕ} (ha : D.edgeData.Admissible ∅) (ht : D.EligibleDE t)
    (h : ReverseBounceN D t x (k + 1))
    (hinner : ∃ i : ℕ, 1 ≤ i ∧ i ≤ k + 1 ∧
      D.residue (D.boundary^[i] t) = D.residue (x + 1)) (m : ℕ) :
    (D.shortenEligible t ht).coloringLLT m = 0 :=
  coloringLLT_eq_zero_of_not_admissible_empty _
    (D.shortenEligible_not_admissible_of_interior_overlap ha ht h hinner) m

theorem shiftedOrientationExpansion_shortenEligible_eq_zero_of_interior_overlap
    {n : ℕ} (D : Diagram n) {t x : ℤ} {k : ℕ}
    (ha : D.edgeData.Admissible ∅) (ht : D.EligibleDE t)
    (h : ReverseBounceN D t x (k + 1))
    (hinner : ∃ i : ℕ, 1 ≤ i ∧ i ≤ k + 1 ∧
      D.residue (D.boundary^[i] t) = D.residue (x + 1)) :
    shiftedOrientationExpansion (D.shortenEligible t ht) = 0 :=
  shiftedOrientationExpansion_eq_zero_of_not_admissible_empty _
    (D.shortenEligible_not_admissible_of_interior_overlap ha ht h hinner)

end VerticalStripLLT.Circular.Diagram
