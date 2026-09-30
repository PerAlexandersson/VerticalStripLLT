import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union

/-! Packing a finite set with prescribed counts in each label class. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

variable {I V : Type*} [Fintype I]

/-- A required subset can be enlarged inside an allowed subset to prescribed
counts in every finite label class. -/
theorem exists_subset_with_label_counts
    (R A : Finset V) (labelOf : V → I) (m : I → ℕ)
    (hRA : R ⊆ A)
    (hR : ∀ i, (R.filter (fun v => labelOf v = i)).card ≤ m i)
    (hA : ∀ i, m i ≤ (A.filter (fun v => labelOf v = i)).card) :
    ∃ T : Finset V, R ⊆ T ∧ T ⊆ A ∧
      ∀ i, (T.filter (fun v => labelOf v = i)).card = m i := by
  classical
  have hpack : ∀ i, ∃ X : Finset V,
      R.filter (fun v => labelOf v = i) ⊆ X ∧
        X ⊆ A.filter (fun v => labelOf v = i) ∧ X.card = m i := by
    intro i
    exact Finset.exists_subsuperset_card_eq
      (by
        intro v hv
        exact Finset.mem_filter.mpr
          ⟨hRA (Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2⟩)
      (hR i) (hA i)
  choose X hRX hXA hXcard using hpack
  let T : Finset V := Finset.univ.biUnion X
  have hfilter : ∀ i, T.filter (fun v => labelOf v = i) = X i := by
    intro i
    ext v
    constructor
    · intro hv
      have hvi : labelOf v = i := (Finset.mem_filter.mp hv).2
      have hvT : v ∈ T := (Finset.mem_filter.mp hv).1
      have hvT' : v ∈ Finset.univ.biUnion X := by simpa [T] using hvT
      obtain ⟨j, _, hvj⟩ := Finset.mem_biUnion.mp hvT'
      have hvjA : v ∈ A.filter (fun w => labelOf w = j) := hXA j hvj
      have hvjLabel : labelOf v = j := (Finset.mem_filter.mp hvjA).2
      have hji : j = i := hvjLabel.symm.trans hvi
      rw [← hji]
      exact hvj
    · intro hv
      have hvA : v ∈ A.filter (fun w => labelOf w = i) := hXA i hv
      have hvi : labelOf v = i := (Finset.mem_filter.mp hvA).2
      apply Finset.mem_filter.mpr
      refine ⟨?_, hvi⟩
      apply Finset.mem_biUnion.mpr
      exact ⟨i, Finset.mem_univ _, hv⟩
  refine ⟨T, ?_, ?_, ?_⟩
  · intro v hv
    apply Finset.mem_biUnion.mpr
    exact ⟨labelOf v, Finset.mem_univ _, hRX _ (Finset.mem_filter.mpr ⟨hv, rfl⟩)⟩
  · intro v hv
    obtain ⟨i, _, hvi⟩ := Finset.mem_biUnion.mp hv
    exact (Finset.mem_filter.mp (hXA i hvi)).1
  · intro i
    rw [hfilter i]
    exact hXcard i

end VerticalStripLLT.Circular.DiagramProof
