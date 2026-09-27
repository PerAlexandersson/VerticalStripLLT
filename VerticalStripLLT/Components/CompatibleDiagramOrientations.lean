import VerticalStripLLT.Components.CompatibleDiagramEdges

/-! Orientations on the ranked diagram and on its compatible original intervals. -/

namespace VerticalStripLLT.Circular.Diagram

open Classical

noncomputable section

variable {n : ℕ} (D : Diagram n) (q : Fin n → ℤ) (σ : Fin n ≃ Fin n)
variable (hmono : StrictMono (q ∘ σ)) (hq : ∀ v, D.residue (q v) = v)
variable (hstrict : D.strict = ∅)

include hq hstrict in
/-- Original orientations obtained from ranked orientations use only compatible intervals. -/
theorem compatible_image_balancedPotential
    (A : Finset (Edge (D.compatibleDiagram q σ hmono).area)) :
    D.naturalGain.BalancedPotential (D.strict ∪ A.image (D.compatibleEdge q σ hmono)) q := by
  intro e he
  rw [hstrict, Finset.empty_union] at he
  obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp he
  exact (D.mem_range_compatibleEdge_iff q σ hmono hq _).mp ⟨f, rfl⟩

/-- Transport an ordinary orientation back to the original circular diagram. -/
def orientationFromCompatible (η : Orientation (D.compatibleDiagram q σ hmono)) :
    Orientation D := by
  let A := η.val.image (D.compatibleEdge q σ hmono)
  have hp := D.compatible_image_balancedPotential q σ hmono hq hstrict η.val
  refine ⟨A, ?_, ?_⟩
  · intro e he
    apply Finset.mem_sdiff.mpr
    exact ⟨Finset.mem_univ _, by simp [edgeData, hstrict]⟩
  · intro v hcycle
    apply (lt_irrefl (σ.symm v))
    apply D.edgeData.lt_of_transGen A σ.symm _ hcycle
    intro e he
    have hl : q e.head - q e.tail = (e.length.val : ℤ) := hp e he
    have hpos : 0 < e.length.val := e.property.1
    apply hmono.lt_iff_lt.mp
    change q (σ (σ.symm e.tail)) < q (σ (σ.symm e.head))
    simp only [Equiv.apply_symm_apply]
    apply sub_pos.mp
    rw [hl]
    exact_mod_cast hpos

@[simp]
theorem orientationFromCompatible_val (η : Orientation (D.compatibleDiagram q σ hmono)) :
    (D.orientationFromCompatible q σ hmono hq hstrict η).val =
      η.val.image (D.compatibleEdge q σ hmono) := rfl

theorem orientationFromCompatible_balancedPotential
    (η : Orientation (D.compatibleDiagram q σ hmono)) :
    D.naturalGain.BalancedPotential
      (D.strict ∪ (D.orientationFromCompatible q σ hmono hq hstrict η).val) q :=
  D.compatible_image_balancedPotential q σ hmono hq hstrict η.val

/-- Pull any selected compatible intervals back to the rank diagram. -/
def orientationToCompatible (θ : Orientation D) :
    Orientation (D.compatibleDiagram q σ hmono) :=
  (D.compatibleDiagram q σ hmono).orientationOfForward
    (D.compatibleDiagram_forward q σ hmono)
    (Finset.univ.filter fun e => D.compatibleEdge q σ hmono e ∈ θ.val)
    (by
      intro e he
      change e ∈ Finset.univ \ ∅
      simp)

@[simp]
theorem orientationToCompatible_mem (θ : Orientation D)
    (e : Edge (D.compatibleDiagram q σ hmono).area) :
    e ∈ (D.orientationToCompatible q σ hmono θ).val ↔
      D.compatibleEdge q σ hmono e ∈ θ.val := by
  simp [orientationToCompatible, orientationOfForward]

theorem orientationToCompatible_fromCompatible
    (η : Orientation (D.compatibleDiagram q σ hmono)) :
    D.orientationToCompatible q σ hmono
      (D.orientationFromCompatible q σ hmono hq hstrict η) = η := by
  apply Subtype.ext
  ext e
  rw [D.orientationToCompatible_mem, D.orientationFromCompatible_val]
  constructor
  · intro he
    obtain ⟨f, hf, heq⟩ := Finset.mem_image.mp he
    have hfe := D.compatibleEdge_injective q σ hmono hq heq
    exact hfe ▸ hf
  · intro he
    exact Finset.mem_image.mpr ⟨e, he, rfl⟩

theorem orientationFromCompatible_toCompatible (θ : Orientation D)
    (hp : D.naturalGain.BalancedPotential (D.strict ∪ θ.val) q) :
    D.orientationFromCompatible q σ hmono hq hstrict
      (D.orientationToCompatible q σ hmono θ) = θ := by
  apply Subtype.ext
  ext e
  simp only [orientationFromCompatible_val, Finset.mem_image, orientationToCompatible_mem]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact hf
  · intro he
    obtain ⟨f, hf⟩ := (D.mem_range_compatibleEdge_iff q σ hmono hq e).mpr
      (hp e (Finset.mem_union_right _ he))
    exact ⟨f, hf ▸ he, hf⟩

/-- The actual selected relations are conjugate by the sorting permutation. -/
theorem orientationFromCompatible_selected
    (η : Orientation (D.compatibleDiagram q σ hmono)) (i j : Fin n) :
    (D.compatibleDiagram q σ hmono).edgeData.selected η.val i j ↔
      D.edgeData.selected
        (D.orientationFromCompatible q σ hmono hq hstrict η).val (σ i) (σ j) := by
  constructor
  · rintro ⟨e, he, ht, hh⟩
    refine ⟨D.compatibleEdge q σ hmono e, ?_, ?_, ?_⟩
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨e, by
        change e ∈ ∅ ∪ η.val at he
        rcases Finset.mem_union.mp he with he | he
        · exact (Finset.notMem_empty e he).elim
        · exact he, rfl⟩
    · change (D.compatibleEdge q σ hmono e).tail = σ i
      rw [D.compatibleEdge_tail q σ hmono hq]
      exact congrArg σ ht
    · change (D.compatibleEdge q σ hmono e).head = σ j
      rw [D.compatibleEdge_head q σ hmono hq]
      exact congrArg σ hh
  · rintro ⟨e, he, ht, hh⟩
    change e ∈ D.strict ∪ _ at he
    rw [hstrict, Finset.empty_union] at he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    refine ⟨f, Finset.mem_union_right _ hf, ?_, ?_⟩
    · change (D.compatibleEdge q σ hmono f).tail = σ i at ht
      rw [D.compatibleEdge_tail q σ hmono hq] at ht
      exact σ.injective ht
    · change (D.compatibleEdge q σ hmono f).head = σ j at hh
      rw [D.compatibleEdge_head q σ hmono hq] at hh
      exact σ.injective hh

end

end VerticalStripLLT.Circular.Diagram
