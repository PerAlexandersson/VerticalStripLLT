import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Adjacent transpositions on an arbitrary set of integer rows. -/

namespace VerticalStripLLT.Circular

noncomputable def adjacentSwap (L : Set ℤ) (z : ℤ) : ℤ := by
  classical
  exact if z ∈ L then z + 1 else if z - 1 ∈ L then z - 1 else z

theorem adjacentSwap_involutive (L : Set ℤ)
    (hsep : ∀ z ∈ L, z + 1 ∉ L) :
    Function.Involutive (adjacentSwap L) := by
  classical
  intro z
  unfold adjacentSwap
  by_cases hz : z ∈ L
  · have hz1 : z + 1 ∉ L := hsep z hz
    simp [hz, hz1]
  · by_cases hz1 : z - 1 ∈ L
    · simp [hz, hz1]
    · simp [hz, hz1]

theorem adjacentSwap_translate (L : Set ℤ) (n z k : ℤ)
    (hper : ∀ x k, x ∈ L ↔ x + n * k ∈ L) :
    adjacentSwap L (z + n * k) = adjacentSwap L z + n * k := by
  classical
  have hper' := hper z k
  have hper'' := hper (z - 1) k
  unfold adjacentSwap
  by_cases hz : z ∈ L
  · have hz' : z + n * k ∈ L := hper'.mp hz
    simp [hz, hz']
    ring
  · have hz' : z + n * k ∉ L := by
      intro h
      exact hz (hper'.mpr h)
    by_cases hz1 : z - 1 ∈ L
    · have hz1' : z + n * k - 1 ∈ L := by
        rw [show z + n * k - 1 = (z - 1) + n * k by ring]
        exact hper''.mp hz1
      simp [hz, hz', hz1, hz1']
      ring
    · have hz1' : z + n * k - 1 ∉ L := by
        intro h
        apply hz1
        apply hper''.mpr
        rwa [show (z - 1) + n * k = z + n * k - 1 by ring]
      simp [hz, hz', hz1, hz1']

theorem adjacentSwap_threshold_iff (L : Set ℤ) (c u : ℤ)
    (hc : c - 1 ∉ L) : c ≤ u ↔ c ≤ adjacentSwap L u := by
  classical
  unfold adjacentSwap
  split_ifs with hu hu1
  · have hnot : u ≠ c - 1 := fun h => hc (h ▸ hu)
    lia
  · have hnot : u ≠ c := fun h => hc (h ▸ hu1)
    lia
  · rfl

theorem adjacentSwap_bounds (L : Set ℤ) (z : ℤ) :
    z - 1 ≤ adjacentSwap L z ∧ adjacentSwap L z ≤ z + 1 := by
  classical
  unfold adjacentSwap
  split_ifs <;> constructor <;> lia

theorem adjacentSwap_strictMonoOn (L T : Set ℤ)
    (hdisjoint : ∀ z ∈ L, z + 1 ∉ L)
    (hsep : ∀ z ∈ L, ¬ (z ∈ T ∧ z + 1 ∈ T)) :
    StrictMonoOn (adjacentSwap L) T := by
  classical
  intro u hu v hv huv
  by_cases huL : u ∈ L
  · rw [adjacentSwap, ite_eq_left huL]
    have hv1 : v ≠ u + 1 := fun h => hsep u huL ⟨hu, h ▸ hv⟩
    by_cases hvL : v ∈ L
    · rw [adjacentSwap, ite_eq_left hvL]
      lia
    by_cases hvP : v - 1 ∈ L
    · rw [adjacentSwap, ite_eq_right hvL, ite_eq_left hvP]
      have hv2 : v ≠ u + 2 := by
        intro h
        apply hdisjoint u huL
        convert hvP using 1; lia
      lia
    · rw [adjacentSwap, ite_eq_right hvL, ite_eq_right hvP]
      lia
  · by_cases huP : u - 1 ∈ L
    · rw [adjacentSwap, ite_eq_right huL, ite_eq_left huP]
      have := (adjacentSwap_bounds L v).1
      lia
    · rw [adjacentSwap, ite_eq_right huL, ite_eq_right huP]
      by_cases hvL : v ∈ L
      · rw [adjacentSwap, ite_eq_left hvL]
        lia
      by_cases hvP : v - 1 ∈ L
      · rw [adjacentSwap, ite_eq_right hvL, ite_eq_left hvP]
        have hv1 : v ≠ u + 1 := by
          intro h
          apply huL
          convert hvP using 1; lia
        lia
      · rw [adjacentSwap, ite_eq_right hvL, ite_eq_right hvP]
        exact huv

end VerticalStripLLT.Circular
