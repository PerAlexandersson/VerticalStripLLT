import VerticalStripLLT.Components.DiagramProof.TwoChainBase
import Mathlib.SetTheory.Cardinal.Finite

/-! Two-terminal connectivity from a cardinality bound on terminal fibres. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

open Classical

noncomputable section

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hD : Forward D)

theorem commonCover_connected_of_terminal_card_le_two
    (hn : 0 < n)
    (hcard : Nat.card {t : Fin n // F.terminal hD t = t} ≤ 2)
    {θ η : Orientation D} (hθ : F.CommonCover θ) (hη : F.CommonCover η)
    (hsize : totalSelected θ = totalSelected η) :
    Relation.ReflTransGen (Flip D) θ η := by
  let V := {t : Fin n // F.terminal hD t = t}
  let T : Finset V := Finset.univ
  have hTc : T.card ≤ 2 := by
    simpa only [T, V, Finset.card_univ, Nat.card_eq_fintype_card] using hcard
  let z0 : V := ⟨F.terminal hD ⟨0, hn⟩,
    F.terminal_idempotent hD ⟨0, hn⟩⟩
  have hz0 : z0 ∈ T := Finset.mem_univ _
  have hterminal : ∃ r s : Fin n, r ≤ s ∧
      ∀ v, F.terminal hD v = r ∨ F.terminal hD v = s := by
    have hcases : T.card = 0 ∨ T.card = 1 ∨ T.card = 2 := by
      lia
    rcases hcases with hzero | h_one | h_two
    · have hne : T.Nonempty := ⟨z0, hz0⟩
      have hp := Finset.card_pos.mpr hne
      lia
    · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h_one
      refine ⟨x.1, x.1, le_rfl, ?_⟩
      intro v
      have hv : (⟨F.terminal hD v, F.terminal_idempotent hD v⟩ : V) ∈ T :=
        Finset.mem_univ _
      have heq : (⟨F.terminal hD v, F.terminal_idempotent hD v⟩ : V) = x := by
        rw [hx] at hv
        simpa using hv
      exact Or.inl (congrArg Subtype.val heq)
    · obtain ⟨x, y, _, hTxy⟩ := Finset.card_eq_two.mp h_two
      by_cases hxy' : x.1 ≤ y.1
      · refine ⟨x.1, y.1, hxy', ?_⟩
        intro v
        have hv : (⟨F.terminal hD v, F.terminal_idempotent hD v⟩ : V) ∈ T :=
          Finset.mem_univ _
        rw [hTxy] at hv
        have hv' : (⟨F.terminal hD v, F.terminal_idempotent hD v⟩ : V) = x ∨
            (⟨F.terminal hD v, F.terminal_idempotent hD v⟩ : V) = y := by
          simpa using hv
        exact hv'.imp (congrArg Subtype.val) (congrArg Subtype.val)
      · refine ⟨y.1, x.1, le_of_not_ge hxy', ?_⟩
        intro v
        have hv : (⟨F.terminal hD v, F.terminal_idempotent hD v⟩ : V) ∈ T :=
          Finset.mem_univ _
        rw [hTxy] at hv
        have hv' : (⟨F.terminal hD v, F.terminal_idempotent hD v⟩ : V) = x ∨
            (⟨F.terminal hD v, F.terminal_idempotent hD v⟩ : V) = y := by
          simpa using hv
        exact hv'.symm.imp (congrArg Subtype.val) (congrArg Subtype.val)
  obtain ⟨r, s, hrs, hterminal⟩ := hterminal
  exact F.commonCover_connected_of_two_terminals hD hrs hterminal hθ hη hsize

end

end VerticalStripLLT.Circular.DiagramProof.CornerFamily
