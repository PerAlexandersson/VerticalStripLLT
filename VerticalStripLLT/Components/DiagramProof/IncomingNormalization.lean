import VerticalStripLLT.Components.DiagramProof.IncomingFlip
import VerticalStripLLT.Components.DiagramProof.ForkNormalization
import VerticalStripLLT.Components.DiagramProof.RestrictedFlips

/-! Eliminate incoming cover forks inside a prescribed vertex set by actual flips. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {n : ℕ} {D : Diagram n}

private theorem exists_reverseFlipWithin_of_not_leftUnique_covers
    (hforward : Forward D) (S : Set (Fin n)) (θ : Orientation D)
    (h : ¬ Relator.LeftUnique (fun u v => S u ∧ S v ∧ Cover θ u v)) :
    ∃ η, DirectedFlipWithin S η θ := by
  change ¬ ∀ ⦃a b c : Fin n⦄,
    (S a ∧ S c ∧ Cover θ a c) → (S b ∧ S c ∧ Cover θ b c) → a = b at h
  push Not at h
  obtain ⟨a, b, c, ⟨ha, hc, hac⟩, ⟨hb, _, hbc⟩, hne⟩ := h
  rcases lt_or_gt_of_ne hne with hab | hba
  · obtain ⟨η, w, hat, hah, _, hbh⟩ :=
      exists_reverseFlip_of_sourceCovers hforward θ a b c hbc hac hab
    exact ⟨η, w, hat ▸ ha, hah ▸ hb, hbh ▸ hc⟩
  · obtain ⟨η, w, hat, hah, _, hbh⟩ :=
      exists_reverseFlip_of_sourceCovers hforward θ b a c hac hbc hba
    exact ⟨η, w, hat ▸ hb, hah ▸ ha, hbh ▸ hc⟩

/-- Incoming cover forks terminate because each reverse flip decreases the tail sum.
A step from `α` to `β` uses the directed witness from `β` to `α`. -/
theorem exists_leftUnique_covers_within (hforward : Forward D)
    (S : Set (Fin n)) (θ : Orientation D) :
    ∃ η : Orientation D,
      Relation.ReflTransGen (fun α β => DirectedFlipWithin S β α) θ η ∧
        Relator.LeftUnique (fun u v => S u ∧ S v ∧ Cover η u v) := by
  classical
  generalize hN : selectedTailSum θ = N
  induction N using Nat.strong_induction_on generalizing θ with
  | h N ih =>
    by_cases hf : Relator.LeftUnique (fun u v => S u ∧ S v ∧ Cover θ u v)
    · exact ⟨θ, Relation.ReflTransGen.refl, hf⟩
    · obtain ⟨η, hηθ⟩ :=
        exists_reverseFlipWithin_of_not_leftUnique_covers hforward S θ hf
      have hlt : selectedTailSum η < N := by
        rw [← hN]
        exact selectedTailSum_lt_of_directedFlip hforward hηθ.choose
      obtain ⟨ξ, hηξ, hξ⟩ := ih _ hlt η rfl
      exact ⟨ξ, hηξ.head hηθ, hξ⟩

/-- In particular, every state has an actual-flip endpoint with unique incoming covers. -/
theorem exists_leftUnique_covers (hforward : Forward D) (θ : Orientation D) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧
      Relator.LeftUnique (Cover η) := by
  obtain ⟨η, hp, hη⟩ := exists_leftUnique_covers_within hforward Set.univ θ
  refine ⟨η, flip_reachable_of_reverse_directed_within hp, ?_⟩
  intro a b c hac hbc
  exact hη ⟨Set.mem_univ a, Set.mem_univ c, hac⟩
    ⟨Set.mem_univ b, Set.mem_univ c, hbc⟩

end VerticalStripLLT.Circular.DiagramProof
