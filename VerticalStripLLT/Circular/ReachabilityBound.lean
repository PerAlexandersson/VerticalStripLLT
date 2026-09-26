import VerticalStripLLT.Circular.WalkBound
import Mathlib.Data.Fin.Tuple.Basic

/-! Actual reachability bounds. Aristotle project e0fb05e6-3945-4336-a5a2-12db81eee4c5;
service namespace packaging was repaired and the extracted proof is checked locally. -/

namespace VerticalStripLLT.Circular

/-- Helper: a reflexive-transitive path yields a finite indexed walk. -/
theorem reflTransGen_exists_walk {S : ℤ → ℤ → Prop} {z w : ℤ}
    (hpath : Relation.ReflTransGen S z w) :
    ∃ (k : ℕ) (p : Fin (k + 1) → ℤ), p 0 = z ∧ p (Fin.last k) = w ∧
      ∀ i : Fin k, S (p i.castSucc) (p i.succ) := by
  induction hpath with
  | refl => exact ⟨0, fun _ => z, rfl, rfl, fun i => i.elim0⟩
  | tail _ hbc ih =>
    obtain ⟨k, p, h0, hl, hs⟩ := ih
    rename_i b c _
    refine ⟨k + 1, Fin.snoc p c, ?_, by simp, ?_⟩
    · have : (0 : Fin (k + 2)) = Fin.castSucc (0 : Fin (k + 1)) := rfl
      rw [this, Fin.snoc_castSucc, h0]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc, hl]; exact hbc
      · rw [← Fin.castSucc_succ, Fin.snoc_castSucc, Fin.snoc_castSucc]; exact hs j

/-- Projected acyclicity bounds every actual reflexive-transitive lifted path. -/
theorem projected_reachable_bounds {n : ℕ}
    (R : Fin n → Fin n → Prop) (hacyclic : ∀ v, ¬ Relation.TransGen R v v)
    (S : ℤ → ℤ → Prop) (π : ℤ → Fin n)
    (hproject : ∀ {z w}, S z w → R (π z) (π w))
    (hstep : ∀ {z w}, S z w → 0 < w - z ∧ w - z ≤ (n - 1 : ℕ))
    {z w : ℤ} (hpath : Relation.ReflTransGen S z w) :
    z ≤ w ∧ w - z ≤ ((n - 1 : ℕ) : ℤ) ^ 2 := by
  constructor
  · induction hpath with
    | refl => exact le_refl _
    | tail _ hbc ih => have := (hstep hbc).1; lia
  · obtain ⟨k, p, h0, hl, hs⟩ := reflTransGen_exists_walk hpath
    have h := VerticalStripLLT.Circular.acyclic_lifted_walk_span_le R hacyclic (π ∘ p)
      (fun i => hproject (hs i)) p (fun i => (hstep (hs i)).2)
    rw [h0, hl] at h
    exact h

end VerticalStripLLT.Circular
