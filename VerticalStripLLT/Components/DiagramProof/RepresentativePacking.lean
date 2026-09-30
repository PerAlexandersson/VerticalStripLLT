import VerticalStripLLT.Components.DiagramProof.LabelPacking

/-! Packing a source while controlling one representative in each label class. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

variable {I V : Type*} [Fintype I]

/-- Repack a source inside an allowed pool while omitting a vacant receiver from
the representative set and retaining exactly the occupied representatives. -/
theorem exists_representative_packing
    (S A C P : Finset V) (labelOf : V → I) (f : V)
    (hSA : S ⊆ A) (hCS : C ⊆ S) (hPA : P ⊆ A)
    (hPinj : ∀ ⦃p q : V⦄, p ∈ P → q ∈ P → labelOf p = labelOf q → p = q)
    (hCP : ∀ c ∈ C, ∀ p ∈ P, labelOf c ≠ labelOf p)
    (hfP : f ∈ P)
    (hvac : (S.filter (fun v => labelOf v = labelOf f)).card <
      (A.filter (fun v => labelOf v = labelOf f)).card) :
    ∃ T : Finset V,
      C ⊆ T ∧ T ⊆ A ∧
        (∀ i, (T.filter (fun v => labelOf v = i)).card =
          (S.filter (fun v => labelOf v = i)).card) ∧
        (∀ p ∈ P, p ∈ T ↔
          0 < (S.filter (fun v => labelOf v = labelOf p)).card ∧ p ≠ f) := by
  classical
  let count : I → ℕ := fun i => (S.filter (fun v => labelOf v = i)).card
  let requested : V → Prop := fun p => 0 < count (labelOf p) ∧ p ≠ f
  let R : Finset V := C ∪ P.filter requested
  have hfA : f ∈ A := hPA hfP
  have hRA : R ⊆ A.erase f := by
    intro v hv
    change v ∈ C ∪ P.filter requested at hv
    rcases Finset.mem_union.mp hv with hvc | hvp
    · have hvf : v ≠ f := by
        intro h
        exact (hCP v hvc f hfP (by rw [h])).elim
      exact Finset.mem_erase.mpr ⟨hvf, hSA (hCS hvc)⟩
    · have hvp' := Finset.mem_filter.mp hvp
      exact Finset.mem_erase.mpr ⟨hvp'.2.2, hPA hvp'.1⟩
  have hR : ∀ i, (R.filter (fun v => labelOf v = i)).card ≤ count i := by
    intro i
    by_cases hex : ∃ p, p ∈ P ∧ labelOf p = i ∧
        0 < count i ∧ p ≠ f
    · obtain ⟨p, hpP, hpi, hpos, hpf⟩ := hex
      have hsub : R.filter (fun v => labelOf v = i) ⊆ ({p} : Finset V) := by
        intro v hv
        have hvi : labelOf v = i := (Finset.mem_filter.mp hv).2
        have hvR := (Finset.mem_filter.mp hv).1
        change v ∈ C ∪ P.filter requested at hvR
        rcases Finset.mem_union.mp hvR with hvc | hvp
        · exact (hCP v hvc p hpP (hvi.trans hpi.symm)).elim
        · have hvp' := Finset.mem_filter.mp hvp
          have hv_eq : v = p := hPinj hvp'.1 hpP (hvi.trans hpi.symm)
          exact hv_eq ▸ Finset.mem_singleton_self p
      calc
        (R.filter (fun v => labelOf v = i)).card ≤ ({p} : Finset V).card :=
          Finset.card_le_card hsub
        _ = 1 := Finset.card_singleton p
        _ ≤ count i := by lia
    · have hsub : R.filter (fun v => labelOf v = i) ⊆
          S.filter (fun v => labelOf v = i) := by
        intro v hv
        have hvi : labelOf v = i := (Finset.mem_filter.mp hv).2
        have hvR := (Finset.mem_filter.mp hv).1
        change v ∈ C ∪ P.filter requested at hvR
        rcases Finset.mem_union.mp hvR with hvc | hvp
        · exact Finset.mem_filter.mpr ⟨hCS hvc, hvi⟩
        · have hvp' := Finset.mem_filter.mp hvp
          have hpos : 0 < count i := by simpa [hvi] using hvp'.2.1
          exact (hex ⟨v, hvp'.1, hvi, hpos, hvp'.2.2⟩).elim
      exact Finset.card_le_card hsub
  have hA : ∀ i, count i ≤
      ((A.erase f).filter (fun v => labelOf v = i)).card := by
    intro i
    by_cases hi : i = labelOf f
    · subst i
      have hfin : f ∈ A.filter (fun v => labelOf v = labelOf f) :=
        Finset.mem_filter.mpr ⟨hfA, rfl⟩
      have hfilter :
          (A.erase f).filter (fun v => labelOf v = labelOf f) =
            (A.filter (fun v => labelOf v = labelOf f)).erase f := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_erase]
        tauto
      have hcard := Finset.card_erase_add_one hfin
      rw [hfilter]
      have hvac' : count (labelOf f) <
          (A.filter (fun v => labelOf v = labelOf f)).card := by
        simpa [count] using hvac
      lia
    · have hfilter :
          (A.erase f).filter (fun v => labelOf v = i) =
            A.filter (fun v => labelOf v = i) := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨⟨_, hvA⟩, hvi⟩
          exact ⟨hvA, hvi⟩
        · rintro ⟨hvA, hvi⟩
          refine ⟨⟨?_, hvA⟩, hvi⟩
          intro hvf
          subst v
          exact hi hvi.symm
      rw [hfilter]
      have hsub : S.filter (fun v => labelOf v = i) ⊆
          A.filter (fun v => labelOf v = i) := by
        intro v hv
        exact Finset.mem_filter.mpr ⟨hSA (Finset.mem_filter.mp hv).1,
          (Finset.mem_filter.mp hv).2⟩
      exact Finset.card_le_card hsub
  obtain ⟨T, hRT, hTA, hcount⟩ :=
    exists_subset_with_label_counts R (A.erase f) labelOf count hRA hR hA
  refine ⟨T, ?_, hTA.trans (Finset.erase_subset f A), ?_, ?_⟩
  · intro c hc
    apply hRT
    change c ∈ C ∪ P.filter requested
    exact Finset.mem_union_left _ hc
  · intro i
    simpa [count] using hcount i
  · intro p hpP
    constructor
    · intro hpT
      have hpne : p ≠ f := (Finset.mem_erase.mp (hTA hpT)).1
      have hpclass : p ∈ T.filter (fun v => labelOf v = labelOf p) :=
        Finset.mem_filter.mpr ⟨hpT, rfl⟩
      have hposT : 0 <
          (T.filter (fun v => labelOf v = labelOf p)).card :=
        Finset.card_pos.mpr ⟨p, hpclass⟩
      have hposCount : 0 < count (labelOf p) := by
        rw [← hcount (labelOf p)]
        exact hposT
      exact ⟨by simpa [count] using hposCount, hpne⟩
    · rintro ⟨hpos, hpne⟩
      apply hRT
      change p ∈ C ∪ P.filter requested
      exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hpP, by simpa [count] using hpos, hpne⟩)

end VerticalStripLLT.Circular.DiagramProof
