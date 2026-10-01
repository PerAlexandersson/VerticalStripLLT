import Mathlib.Data.Finset.Card

/-! Choosing a fixed-size chord subset containing two prescribed non-outer positions. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {V : Type*} [DecidableEq V]

/-- A subset of size at least two can be replaced by one of the same size that
contains two prescribed distinct positions while avoiding the distinguished position. -/
theorem exists_subset_with_prescribed_pair_away_from
    (U S : Finset V) (p a b : V)
    (haU : a ∈ U) (hbU : b ∈ U)
    (hap : a ≠ p) (hbp : b ≠ p) (hab : a ≠ b)
    (hS : S ⊆ U) (hpS : p ∉ S) (hcard : 2 ≤ S.card) :
    ∃ T, T ⊆ U ∧ p ∉ T ∧ a ∈ T ∧ b ∈ T ∧ T.card = S.card := by
  let A : Finset V := insert a {b}
  have haA : a ∈ A := by simp [A]
  have hbA : b ∈ A := by simp [A]
  have hAcard : A.card ≤ S.card := by
    change (insert a {b} : Finset V).card ≤ S.card
    rw [Finset.card_insert_of_notMem]
    · simpa using hcard
    · simp [hab]
  have hAerase : A ⊆ U.erase p := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_erase.mpr ⟨hap, haU⟩
    · have hxb : x = b := Finset.mem_singleton.mp hx
      subst x
      exact Finset.mem_erase.mpr ⟨hbp, hbU⟩
  have hSerase : S ⊆ U.erase p := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨fun hxp => hpS (hxp ▸ hx), hS hx⟩
  obtain ⟨T, hAT, hTU, hTcard⟩ :=
    Finset.exists_subsuperset_card_eq hAerase hAcard (Finset.card_le_card hSerase)
  refine ⟨T, hTU.trans (Finset.erase_subset p U), ?_, hAT haA, hAT hbA, hTcard⟩
  intro hpT
  exact (Finset.mem_erase.mp (hTU hpT)).1 rfl

end VerticalStripLLT.Circular.DiagramProof
