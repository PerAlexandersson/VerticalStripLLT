import VerticalStripLLT.Circular.PeriodicSwap

/-! Boundary-edge swap invariance. Aristotle candidate; see docs/ARISTOTLE.md. -/

namespace VerticalStripLLT.Circular

def periodicBridge (n p u v : ℤ) : Prop :=
  ∃ k : ℤ, u = p + n * k ∧ v = p + 1 + n * k

theorem periodicSwap_base (n p k : ℤ) (hn : 2 ≤ n) :
    periodicSwap n p (p + n * k) = p + 1 + n * k ∧
      periodicSwap n p (p + 1 + n * k) = p + n * k := by
  have h1 : (1 : ℤ) % n = 1 := Int.emod_eq_of_lt (by lia) (by lia)
  rw [periodicSwap_translate n p p k hn, periodicSwap_translate n p (p + 1) k hn]
  unfold periodicSwap
  simp [h1]

theorem periodicSwap_b_eq (n p : ℤ) (b : ℤ → ℤ)
    (hperiod : ∀ z k : ℤ, b (z + n * k) = b z + n * k)
    (hsame : b (p + 1) = b p) (v : ℤ) :
    b (periodicSwap n p v) = b v := by
  have hd := Int.emod_add_mul_ediv (v - p) n
  generalize (v - p) / n = k at hd
  have key : b (p + 1 + n * k) = b (p + n * k) := by
    rw [hperiod, hperiod, hsame]
  unfold periodicSwap
  split_ifs with h0 h1
  · have hv : v = p + n * k := by lia
    subst hv
    rw [show p + n * k + 1 = p + 1 + n * k by ring, key]
  · have hv : v = p + 1 + n * k := by lia
    subst hv
    rw [show p + 1 + n * k - 1 = p + n * k by ring, key]
  · rfl

theorem periodicSwap_le_iff (n p : ℤ) (w : ℤ)
    (havoid : ∀ k : ℤ, w ≠ p + 1 + n * k) (u : ℤ) :
    w ≤ u ↔ w ≤ periodicSwap n p u := by
  have hd := Int.emod_add_mul_ediv (u - p) n
  generalize (u - p) / n = k at hd
  have := havoid k
  unfold periodicSwap
  split_ifs with h0 h1 <;> lia

theorem periodicSwap_boundary_forward (n p : ℤ) (hn : 2 ≤ n) (b : ℤ → ℤ)
    (hperiod : ∀ z k : ℤ, b (z + n * k) = b z + n * k)
    (hsame : b (p + 1) = b p)
    (havoid : ∀ z k : ℤ, b z ≠ p + 1 + n * k) (u v : ℤ)
    (h : b v ≤ u ∧ u < v ∧ ¬ periodicBridge n p u v) :
    b (periodicSwap n p v) ≤ periodicSwap n p u ∧
      periodicSwap n p u < periodicSwap n p v ∧
      ¬ periodicBridge n p (periodicSwap n p u) (periodicSwap n p v) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [periodicSwap_b_eq n p b hperiod hsame]
    exact (periodicSwap_le_iff n p (b v) (havoid v) u).1 h1
  · have hS : ∀ k : ℤ, ¬ (p + n * k ∈ ({u, v} : Set ℤ) ∧ p + 1 + n * k ∈ ({u, v} : Set ℤ)) := by
      rintro k ⟨ha, hb⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · lia
      · exact h3 ⟨k, ha.symm, hb.symm⟩
      · lia
      · lia
    exact periodicSwap_strictMonoOn n p hn _ hS (by simp) (by simp) h2
  · rintro ⟨k, hu, hv⟩
    have hi := periodicSwap_involutive n p hn
    obtain ⟨e1, e2⟩ := periodicSwap_base n p k hn
    have hu' : u = p + 1 + n * k := by rw [← hi u, hu, e1]
    have hv' : v = p + n * k := by rw [← hi v, hv, e2]
    lia

theorem periodicSwap_boundary_relation (n p : ℤ) (hn : 2 ≤ n) (b : ℤ → ℤ)
    (hperiod : ∀ z k : ℤ, b (z + n * k) = b z + n * k)
    (hsame : b (p + 1) = b p)
    (havoid : ∀ z k : ℤ, b z ≠ p + 1 + n * k) (u v : ℤ) :
    (b v ≤ u ∧ u < v ∧ ¬ periodicBridge n p u v) ↔
      (b (periodicSwap n p v) ≤ periodicSwap n p u ∧
        periodicSwap n p u < periodicSwap n p v ∧
        ¬ periodicBridge n p (periodicSwap n p u) (periodicSwap n p v)) := by
  refine ⟨periodicSwap_boundary_forward n p hn b hperiod hsame havoid u v, fun h => ?_⟩
  have hi := periodicSwap_involutive n p hn
  have := periodicSwap_boundary_forward n p hn b hperiod hsame havoid _ _ h
  rwa [hi u, hi v] at this

end VerticalStripLLT.Circular
