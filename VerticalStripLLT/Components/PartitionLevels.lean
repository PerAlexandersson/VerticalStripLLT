import VerticalStripLLT.Components.OrderedPartitions

/-! Actual top-first partitions as finite level assignments. -/

namespace VerticalStripLLT.Components.OrderedPartitions

open Classical

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- The first block has highest level; absent vertices receive zero. -/
def blockLevel : List (Finset V) → V → ℕ
  | [], _ => 0
  | U :: bs, v => if v ∈ U then bs.length else blockLevel bs v

theorem blockLevel_lt_length {S : Finset V} {bs : List (Finset V)}
    (h : IsCompatible (fun _ _ => False) S bs) {v : V} (hv : v ∈ S) :
    blockLevel bs v < bs.length := by
  induction bs generalizing S with
  | nil =>
    change S = ∅ at h
    simp [h] at hv
  | cons U bs ih =>
    obtain ⟨hU, hbs⟩ := h
    by_cases hvU : v ∈ U
    · simp [blockLevel, hvU]
    · have hi := ih hbs (Finset.mem_sdiff.mpr ⟨hv, hvU⟩)
      simp only [blockLevel, ite_eq_right hvU, List.length_cons]
      lia

/-- Compatibility depends exactly on edges being nondecreasing in the block levels. -/
theorem compatible_iff_blockLevel (R : V → V → Prop) {S : Finset V}
    {bs : List (Finset V)} (hbase : IsCompatible (fun _ _ => False) S bs) :
    IsCompatible R S bs ↔
      ∀ x ∈ S, ∀ y ∈ S, R x y → blockLevel bs x ≤ blockLevel bs y := by
  induction bs generalizing S with
  | nil =>
    change S = ∅ at hbase
    subst S
    simp [IsCompatible]
  | cons U bs ih =>
    obtain ⟨hU, hbs⟩ := hbase
    obtain ⟨hUS, hUne, _⟩ := (mem_topBlocks _ S U).mp hU
    constructor
    · rintro ⟨hUR, hbsR⟩ x hx y hy hxy
      have hup := ((mem_topBlocks R S U).mp hUR).2.2
      by_cases hxU : x ∈ U
      · have hyU := hup hxU hy hxy
        simp only [blockLevel, ite_eq_left hxU, ite_eq_left hyU, le_refl]
      · by_cases hyU : y ∈ U
        · have hi := blockLevel_lt_length hbs (Finset.mem_sdiff.mpr ⟨hx, hxU⟩)
          simpa only [blockLevel, ite_eq_right hxU, ite_eq_left hyU] using hi.le
        · simpa only [blockLevel, ite_eq_right hxU, ite_eq_right hyU] using
            (ih hbs).mp hbsR x (Finset.mem_sdiff.mpr ⟨hx, hxU⟩)
              y (Finset.mem_sdiff.mpr ⟨hy, hyU⟩) hxy
    · intro h
      constructor
      · apply (mem_topBlocks R S U).mpr
        refine ⟨hUS, hUne, ?_⟩
        intro x y hxU hy hxy
        by_contra hyU
        have hle := h x (hUS hxU) y hy hxy
        have hlt := blockLevel_lt_length hbs (Finset.mem_sdiff.mpr ⟨hy, hyU⟩)
        simp only [blockLevel, ite_eq_left hxU, ite_eq_right hyU] at hle
        lia
      · apply (ih hbs).mpr
        intro x hx y hy hxy
        obtain ⟨hxS, hxU⟩ := Finset.mem_sdiff.mp hx
        obtain ⟨hyS, hyU⟩ := Finset.mem_sdiff.mp hy
        simpa only [blockLevel, ite_eq_right hxU, ite_eq_right hyU] using h x hxS y hyS hxy

theorem compatible_false_of_compatible (R : V → V → Prop) {S : Finset V}
    {bs : List (Finset V)} (h : IsCompatible R S bs) :
    IsCompatible (fun _ _ => False) S bs := by
  induction bs generalizing S with
  | nil => exact h
  | cons U bs ih =>
    obtain ⟨hU, hbs⟩ := h
    obtain ⟨hUS, hUne, _⟩ := (mem_topBlocks _ S U).mp hU
    exact ⟨(mem_topBlocks _ S U).mpr ⟨hUS, hUne, fun _ _ _ _ hf => hf.elim⟩, ih hbs⟩

/-- All compatible partitions are selected from the same finite ambient family. -/
theorem partitions_eq_filter (R : V → V → Prop) (S : Finset V) :
    partitions R S = (partitions (fun _ _ => False) S).filter (IsCompatible R S) := by
  ext bs
  simp only [mem_partitions, Finset.mem_filter]
  exact ⟨fun h => ⟨compatible_false_of_compatible R h, h⟩, fun h => h.2⟩

end

end VerticalStripLLT.Components.OrderedPartitions
