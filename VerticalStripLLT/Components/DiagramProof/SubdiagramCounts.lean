import VerticalStripLLT.Components.DiagramProof.CompleteSubdiagram

/-! Selected-edge counts under restriction to a complete subdiagram. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k n : ℕ} (ι : Fin (k + 1) ↪o Fin (n + 1))

/-- The canonical embedding of complete-diagram edges induced by a vertex embedding. -/
def completeEdgeEmbed :
    Edge (completeDiagram k).area ↪ Edge (completeDiagram n).area :=
  ⟨fun e => completeEdge n (ι e.tail) (ι e.head)
      (ι.strictMono (complete_forward k e)), by
    intro e f hef
    change completeEdge n (ι e.tail) (ι e.head) _ =
      completeEdge n (ι f.tail) (ι f.head) _ at hef
    have htail : ι e.tail = ι f.tail := by
      simpa only [completeEdge_tail] using congrArg Edge.tail hef
    have hhead : ι e.head = ι f.head := by
      simpa only [completeEdge_head] using congrArg Edge.head hef
    have htail' : e.tail = f.tail := ι.injective htail
    have hhead' : e.head = f.head := ι.injective hhead
    exact (completeDiagram k).endpointEmbedding.injective (Prod.ext htail' hhead')⟩

@[simp]
theorem completeEdgeEmbed_tail (e : Edge (completeDiagram k).area) :
    (completeEdgeEmbed ι e).tail = ι e.tail := by
  exact completeEdge_tail n (ι e.tail) (ι e.head) (ι.strictMono (complete_forward k e))

@[simp]
theorem completeEdgeEmbed_head (e : Edge (completeDiagram k).area) :
    (completeEdgeEmbed ι e).head = ι e.head := by
  rfl

theorem completeEdgeEmbed_injective : Function.Injective (completeEdgeEmbed ι) :=
  (completeEdgeEmbed ι).injective

/-- An ambient edge has both endpoints in the image of the smaller diagram. -/
def completeEdgeInImage (e : Edge (completeDiagram n).area) : Prop :=
  ∃ a b, ι a = e.tail ∧ ι b = e.head

theorem completeEdgeEmbed_image_fullSelection (θ : Orientation (completeDiagram n)) :
    (fullSelection (completeRestrictAlong ι θ)).image (completeEdgeEmbed ι) =
      (fullSelection θ).filter (completeEdgeInImage ι) := by
  ext e
  constructor
  · rintro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    refine Finset.mem_filter.mpr ⟨?_, ⟨f.tail, f.head,
      (completeEdgeEmbed_tail ι f).symm, (completeEdgeEmbed_head ι f).symm⟩⟩
    apply (mem_fullSelection_iff_selected θ _).mpr
    rw [completeEdgeEmbed_tail, completeEdgeEmbed_head]
    exact (completeRestrictAlong_selected ι θ f.tail f.head).mp
      ((mem_fullSelection_iff_selected (completeRestrictAlong ι θ) f).mp hf)
  · rintro he
    obtain ⟨hefull, a, b, ha, hb⟩ := Finset.mem_filter.mp he
    have hab' : ι a < ι b := by
      have hforward := complete_forward n e
      rw [← ha, ← hb] at hforward
      exact hforward
    have hab : a < b := ι.lt_iff_lt.mp hab'
    let f : Edge (completeDiagram k).area := completeEdge k a b hab
    refine Finset.mem_image.mpr ⟨f, ?_, ?_⟩
    · apply (mem_fullSelection_iff_selected (completeRestrictAlong ι θ) f).mpr
      apply (completeRestrictAlong_selected ι θ f.tail f.head).mpr
      simpa [f, ha, hb] using (mem_fullSelection_iff_selected θ e).mp hefull
    · simpa [completeEdgeEmbed, f, ha, hb] using completeEdge_eq_of_endpoints n e

theorem fullSelection_filter_not_completeEdgeInImage_eq
    (θ η : Orientation (completeDiagram n))
    (houtside : ∀ u v, (¬ ∃ a b, ι a = u ∧ ι b = v) →
      ((completeDiagram n).edgeData.selected θ.val u v ↔
        (completeDiagram n).edgeData.selected η.val u v)) :
    (fullSelection θ).filter (fun e => ¬ completeEdgeInImage ι e) =
      (fullSelection η).filter (fun e => ¬ completeEdgeInImage ι e) := by
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨he, hnot⟩
    refine ⟨?_, hnot⟩
    apply (mem_fullSelection_iff_selected η e).mpr
    apply (houtside e.tail e.head (by simpa [completeEdgeInImage] using hnot)).mp
    exact (mem_fullSelection_iff_selected θ e).mp he
  · rintro ⟨he, hnot⟩
    refine ⟨?_, hnot⟩
    apply (mem_fullSelection_iff_selected θ e).mpr
    apply (houtside e.tail e.head (by simpa [completeEdgeInImage] using hnot)).mpr
    exact (mem_fullSelection_iff_selected η e).mp he

/-- Equal ambient counts and equal exterior selections give equal restricted counts. -/
theorem completeRestrictAlong_totalSelected_eq
    (θ η : Orientation (completeDiagram n))
    (htotal : totalSelected θ = totalSelected η)
    (houtside : ∀ u v, (¬ ∃ a b, ι a = u ∧ ι b = v) →
      ((completeDiagram n).edgeData.selected θ.val u v ↔
        (completeDiagram n).edgeData.selected η.val u v)) :
    totalSelected (completeRestrictAlong ι θ) =
      totalSelected (completeRestrictAlong ι η) := by
  have houtside' := fullSelection_filter_not_completeEdgeInImage_eq ι θ η houtside
  have hinside : ((fullSelection θ).filter (completeEdgeInImage ι)).card =
      ((fullSelection η).filter (completeEdgeInImage ι)).card := by
    exact Nat.add_right_cancel (by
      calc
        ((fullSelection θ).filter (completeEdgeInImage ι)).card +
            ((fullSelection θ).filter (fun e => ¬ completeEdgeInImage ι e)).card =
            (fullSelection θ).card :=
          Finset.card_filter_add_card_filter_not (completeEdgeInImage ι)
            (s := fullSelection θ)
        _ = (fullSelection η).card := by
          simpa only [totalSelected] using htotal
        _ = ((fullSelection η).filter (completeEdgeInImage ι)).card +
            ((fullSelection η).filter (fun e => ¬ completeEdgeInImage ι e)).card :=
          (Finset.card_filter_add_card_filter_not (completeEdgeInImage ι)
            (s := fullSelection η)).symm
        _ = ((fullSelection η).filter (completeEdgeInImage ι)).card +
            ((fullSelection θ).filter (fun e => ¬ completeEdgeInImage ι e)).card := by
          rw [houtside'])
  calc
    totalSelected (completeRestrictAlong ι θ) =
        ((fullSelection (completeRestrictAlong ι θ)).image (completeEdgeEmbed ι)).card := by
      simpa only [totalSelected] using
        (Finset.card_image_of_injective _ (completeEdgeEmbed_injective ι)).symm
    _ = ((fullSelection θ).filter (completeEdgeInImage ι)).card := by
      rw [completeEdgeEmbed_image_fullSelection]
    _ = ((fullSelection η).filter (completeEdgeInImage ι)).card := hinside
    _ = ((fullSelection (completeRestrictAlong ι η)).image (completeEdgeEmbed ι)).card := by
      rw [completeEdgeEmbed_image_fullSelection]
    _ = totalSelected (completeRestrictAlong ι η) := by
      simpa only [totalSelected] using
        Finset.card_image_of_injective _ (completeEdgeEmbed_injective ι)

end

end VerticalStripLLT.Circular.DiagramProof
