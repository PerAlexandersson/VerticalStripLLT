import VerticalStripLLT.Components.DiagramProof.Relational.NaturalRelations

/-!
# Natural area and area moment

The induction order of the diagram proof is lexicographic in the vertex count,
the natural area `∑ j a_j` and the area moment `∑ j j a_j`. For forward diagrams
these are the number of natural pairs and the sum of their heads.
-/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ### Natural area and area moment -/

/-- Total natural area `∑ j a_j`. -/
def naturalArea (D : Diagram n) : ℕ := ∑ j, D.area.area j

/-- Area moment `∑ j j a_j`. -/
def areaMoment (D : Diagram n) : ℕ := ∑ j, j.val * D.area.area j

/-- A column's area counts the natural edges with that head. -/
theorem area_eq_card_naturalRel {D : Diagram n} (j : Fin n) :
    D.area.area j = (Finset.univ.filter fun u => naturalRel D u j).card := by
  have hedges : (Finset.univ.filter fun e : Edge D.area => e.head = j).card =
      D.area.area j := by
    have hbound := D.area.bound j
    refine (Finset.card_bij (t := Finset.Ioc 0 (D.area.area j))
      (fun e _ => e.length.val) ?_ ?_ ?_).trans (by simp)
    · intro e he
      have hj := (Finset.mem_filter.mp he).2
      have hpos := e.length_pos
      have hle := e.length_le_area
      rw [hj] at hle
      exact Finset.mem_Ioc.mpr ⟨hpos, hle⟩
    · intro e he f hf hef
      have hje := (Finset.mem_filter.mp he).2
      have hjf := (Finset.mem_filter.mp hf).2
      apply Subtype.ext
      exact Prod.ext (hje.trans hjf.symm) (Fin.ext hef)
    · intro ℓ hℓ
      obtain ⟨hpos, hle⟩ := Finset.mem_Ioc.mp hℓ
      refine ⟨⟨(j, ⟨ℓ, by lia⟩), hpos, hle⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩
  rw [← hedges]
  apply Finset.card_bij (fun e _ => e.tail)
  · intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, rfl, (Finset.mem_filter.mp he).2⟩
  · intro e he f hf hef
    exact D.endpointEmbedding.injective (Prod.ext hef
      ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm))
  · intro u hu
    obtain ⟨e, ht, hh⟩ := (Finset.mem_filter.mp hu).2
    exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩, ht⟩

theorem area_zero_of_forward {D : Diagram (n + 1)} (hD : Forward D) :
    D.area.area 0 = 0 := by
  rw [area_eq_card_naturalRel, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro u _ hu
  exact (Fin.not_lt_zero u) (naturalRel_forward hD hu)

/-- The finite set of natural endpoint pairs. -/
def naturalPairs (D : Diagram n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun x => naturalRel D x.1 x.2

@[simp]
theorem mem_naturalPairs {D : Diagram n} {x : Fin n × Fin n} :
    x ∈ naturalPairs D ↔ naturalRel D x.1 x.2 := by
  simp [naturalPairs]

theorem card_naturalPairs_fibre {D : Diagram n} (j : Fin n) :
    ((naturalPairs D).filter fun x => x.2 = j).card = D.area.area j := by
  rw [area_eq_card_naturalRel]
  symm
  apply Finset.card_bij (fun u _ => (u, j))
  · intro u hu
    simpa [naturalPairs] using hu
  · intro a _ b _ h
    exact (Prod.mk.inj h).1
  · rintro ⟨u, v⟩ hx
    simp only [naturalPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hn, rfl⟩ := hx
    exact ⟨u, by simpa using hn, rfl⟩

/-- The natural area is the number of natural pairs. -/
theorem naturalArea_eq_card (D : Diagram n) : naturalArea D = (naturalPairs D).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  unfold naturalArea
  exact Finset.sum_congr rfl fun j _ => (card_naturalPairs_fibre j).symm

/-- The area moment is the sum of the heads of the natural pairs. -/
theorem areaMoment_eq_sum (D : Diagram n) :
    areaMoment D = ∑ x ∈ naturalPairs D, x.2.val := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.snd) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  unfold areaMoment
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← card_naturalPairs_fibre j, Finset.sum_congr rfl (g := fun _ => j.val)
    (fun x hx => (Finset.mem_filter.mp hx).2 ▸ rfl), Finset.sum_const, smul_eq_mul, mul_comm]

/-- Equal natural relations have equal measures. -/
theorem measure_eq_of_naturalRel_iff {D E : Diagram n}
    (h : ∀ u v, naturalRel D u v ↔ naturalRel E u v) :
    naturalArea D = naturalArea E ∧ areaMoment D = areaMoment E := by
  have hp : naturalPairs D = naturalPairs E := by
    ext x
    simp only [mem_naturalPairs, h]
  rw [naturalArea_eq_card, naturalArea_eq_card, areaMoment_eq_sum, areaMoment_eq_sum, hp]
  exact ⟨rfl, rfl⟩

/-- A proper subrelation has smaller natural area. -/
theorem naturalArea_lt_of_ssubset {D E : Diagram n} (h : naturalPairs D ⊂ naturalPairs E) :
    naturalArea D < naturalArea E := by
  rw [naturalArea_eq_card, naturalArea_eq_card]
  exact Finset.card_lt_card h

/-- The lexicographic order on (natural area, area moment) for a fixed vertex set. -/
def MeasureLT (D E : Diagram n) : Prop :=
  naturalArea D < naturalArea E ∨ (naturalArea D = naturalArea E ∧ areaMoment D < areaMoment E)

end

end VerticalStripLLT.Circular.DiagramProof
