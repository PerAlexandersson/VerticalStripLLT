import VerticalStripLLT.Components.DiagramProof.LastClique.CliqueRestriction

/-! Selected-edge counts in an embedded complete clique. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k n : ℕ} {D : Diagram n}

/-- The ambient edge corresponding to an edge of an embedded natural clique. -/
def cliqueEdgeEmbed (ι : Fin (k + 1) ↪o Fin n)
    (hnatural : ∀ i j, i < j → ∃ e : Edge D.area, e.tail = ι i ∧ e.head = ι j) :
    Edge (completeDiagram k).area ↪ Edge D.area :=
  ⟨fun e => (hnatural e.tail e.head (complete_forward k e)).choose,
    fun e f hef => by
      have he := (hnatural e.tail e.head (complete_forward k e)).choose_spec
      have hf := (hnatural f.tail f.head (complete_forward k f)).choose_spec
      apply (completeDiagram k).endpointEmbedding.injective
      change (e.tail, e.head) = (f.tail, f.head)
      apply Prod.ext
      · apply ι.injective
        exact he.1.symm.trans ((congrArg (fun e : Edge D.area => e.tail) hef).trans hf.1)
      · apply ι.injective
        exact he.2.symm.trans ((congrArg (fun e : Edge D.area => e.head) hef).trans hf.2)⟩

@[simp]
theorem cliqueEdgeEmbed_tail (ι : Fin (k + 1) ↪o Fin n)
    (hnatural : ∀ i j, i < j → ∃ e : Edge D.area, e.tail = ι i ∧ e.head = ι j)
    (e : Edge (completeDiagram k).area) :
    (cliqueEdgeEmbed ι hnatural e).tail = ι e.tail :=
  (hnatural e.tail e.head (complete_forward k e)).choose_spec.1

@[simp]
theorem cliqueEdgeEmbed_head (ι : Fin (k + 1) ↪o Fin n)
    (hnatural : ∀ i j, i < j → ∃ e : Edge D.area, e.tail = ι i ∧ e.head = ι j)
    (e : Edge (completeDiagram k).area) :
    (cliqueEdgeEmbed ι hnatural e).head = ι e.head :=
  (hnatural e.tail e.head (complete_forward k e)).choose_spec.2

/-- An ambient edge has both endpoints in the embedded clique. -/
def cliqueEdgeInImage (ι : Fin (k + 1) ↪o Fin n) (e : Edge D.area) : Prop :=
  ∃ a b, ι a = e.tail ∧ ι b = e.head

/-- The selected edges of a clique restriction are exactly the selected ambient edges
whose endpoints lie in the clique. -/
theorem cliqueEdgeEmbed_image_fullSelection (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n)
    (hnatural : ∀ i j, i < j → ∃ e : Edge D.area, e.tail = ι i ∧ e.head = ι j)
    (θ : Orientation D) :
    (fullSelection (cliqueRestrict hD ι θ)).image (cliqueEdgeEmbed ι hnatural) =
      (fullSelection θ).filter (cliqueEdgeInImage ι) := by
  ext e
  constructor
  · rintro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    refine Finset.mem_filter.mpr ⟨?_, ⟨f.tail, f.head,
      (cliqueEdgeEmbed_tail ι hnatural f).symm,
      (cliqueEdgeEmbed_head ι hnatural f).symm⟩⟩
    apply (mem_fullSelection_iff_selected θ _).mpr
    rw [cliqueEdgeEmbed_tail, cliqueEdgeEmbed_head]
    exact (cliqueRestrict_selected hD ι θ f.tail f.head).mp
      ((mem_fullSelection_iff_selected (cliqueRestrict hD ι θ) f).mp hf)
  · rintro he
    obtain ⟨hefull, a, b, ha, hb⟩ := Finset.mem_filter.mp he
    have hab' : ι a < ι b := by
      have hforward := hD e
      rw [← ha, ← hb] at hforward
      exact hforward
    have hab : a < b := ι.lt_iff_lt.mp hab'
    let f : Edge (completeDiagram k).area := completeEdge k a b hab
    refine Finset.mem_image.mpr ⟨f, ?_, ?_⟩
    · apply (mem_fullSelection_iff_selected (cliqueRestrict hD ι θ) f).mpr
      apply (cliqueRestrict_selected hD ι θ f.tail f.head).mpr
      change D.edgeData.selected θ.val (ι (completeEdge k a b hab).tail)
        (ι (completeEdge k a b hab).head)
      rw [completeEdge_tail k a b hab, completeEdge_head k a b hab, ha, hb]
      exact (mem_fullSelection_iff_selected θ e).mp hefull
    · apply D.endpointEmbedding.injective
      change ((cliqueEdgeEmbed ι hnatural f).tail, (cliqueEdgeEmbed ι hnatural f).head) =
        (e.tail, e.head)
      apply Prod.ext
      · rw [cliqueEdgeEmbed_tail]
        exact (congrArg ι (completeEdge_tail k a b hab)).trans ha
      · rw [cliqueEdgeEmbed_head]
        exact (congrArg ι (completeEdge_head k a b hab)).trans hb

/-- The selected count of a clique restriction is the number of selected ambient edges
whose endpoints lie in the clique. -/
theorem cliqueRestrict_totalSelected_eq_filter (hD : Forward D)
    (ι : Fin (k + 1) ↪o Fin n)
    (hnatural : ∀ i j, i < j → ∃ e : Edge D.area, e.tail = ι i ∧ e.head = ι j)
    (θ : Orientation D) :
    totalSelected (cliqueRestrict hD ι θ) =
      ((fullSelection θ).filter (cliqueEdgeInImage ι)).card := by
  calc
    totalSelected (cliqueRestrict hD ι θ) =
        ((fullSelection (cliqueRestrict hD ι θ)).image (cliqueEdgeEmbed ι hnatural)).card := by
      simpa only [totalSelected] using
        (Finset.card_image_of_injective _ (cliqueEdgeEmbed ι hnatural).injective).symm
    _ = ((fullSelection θ).filter (cliqueEdgeInImage ι)).card := by
      rw [cliqueEdgeEmbed_image_fullSelection]

/-- Replacing one selected edge by an absent edge inside a clique preserves its local count. -/
theorem cliqueRestrict_totalSelected_swap (hD : Forward D)
    (ι : Fin (k + 1) ↪o Fin n)
    (hnatural : ∀ i j, i < j → ∃ e : Edge D.area, e.tail = ι i ∧ e.head = ι j)
    (θ η : Orientation D) (e f : Edge D.area)
    (hfull : fullSelection η = insert f ((fullSelection θ).erase e))
    (he : e ∈ fullSelection θ) (hf : f ∉ fullSelection θ)
    (heinside : cliqueEdgeInImage ι e) (hfinside : cliqueEdgeInImage ι f) :
    totalSelected (cliqueRestrict hD ι θ) = totalSelected (cliqueRestrict hD ι η) := by
  rw [cliqueRestrict_totalSelected_eq_filter hD ι hnatural,
    cliqueRestrict_totalSelected_eq_filter hD ι hnatural, hfull]
  let p : Edge D.area → Prop := cliqueEdgeInImage (D := D) ι
  have he' : e ∈ (fullSelection θ).filter p := Finset.mem_filter.mpr ⟨he, heinside⟩
  have hf' : f ∉ (fullSelection θ).filter p := fun h => hf (Finset.mem_filter.mp h).1
  have hfilter : (insert f ((fullSelection θ).erase e)).filter p =
      insert f (((fullSelection θ).filter p).erase e) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨hx, hpx⟩
      rcases hx with rfl | hx
      · exact Or.inl rfl
      · exact Or.inr ⟨hx.1, hx.2, hpx⟩
    · rintro (rfl | hx)
      · exact ⟨Or.inl rfl, hfinside⟩
      · exact ⟨Or.inr ⟨hx.1, hx.2.1⟩, hx.2.2⟩
  rw [hfilter, Finset.card_insert_of_notMem
    (fun h => hf' (Finset.mem_of_mem_erase h)), Finset.card_erase_of_mem he']
  have hpos := Finset.card_pos.mpr ⟨e, he'⟩
  lia

end

end VerticalStripLLT.Circular.DiagramProof
