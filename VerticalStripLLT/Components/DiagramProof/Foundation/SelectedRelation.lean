import VerticalStripLLT.Components.DiagramProof.Foundation.Basic

/-!
# Orientations from endpoint relations

An endpoint relation can be used to specify a full selected edge set when it
has natural-edge witnesses and contains the strict edges.  This is a small
interface for concrete restriction constructions; the state remains the
existing `Orientation` type.
-/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {n : ℕ} {D : Diagram n}

/-- The orientation whose full selected edge set is the natural edges with
endpoints in `R`. -/
def ofSelectedRelation (hforward : Forward D) (R : Fin n → Fin n → Prop)
    (_hnatural : ∀ u v, R u v → ∃ e : Edge D.area, e.tail = u ∧ e.head = v)
    (hstrict : ∀ e ∈ D.strict, R e.tail e.head) : Orientation D :=
  ofFullSelection hforward
    (Finset.univ.filter fun e : Edge D.area => R e.tail e.head)
    (by
      intro e he
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hstrict e he⟩)

theorem selected_ofSelectedRelation (hforward : Forward D) (R : Fin n → Fin n → Prop)
    (hnatural : ∀ u v, R u v → ∃ e : Edge D.area, e.tail = u ∧ e.head = v)
    (hstrict : ∀ e ∈ D.strict, R e.tail e.head) (u v : Fin n) :
    D.edgeData.selected (ofSelectedRelation hforward R hnatural hstrict).val u v ↔
      R u v := by
  let θ := ofSelectedRelation hforward R hnatural hstrict
  have hfull : fullSelection θ =
      Finset.univ.filter fun e : Edge D.area => R e.tail e.head := by
    dsimp [θ, ofSelectedRelation]
    apply fullSelection_ofFullSelection
  constructor
  · intro huv
    obtain ⟨e, he, ht, hh⟩ := huv
    have hef : e ∈ Finset.univ.filter fun f : Edge D.area => R f.tail f.head := by
      rw [← hfull]
      exact he
    change e.tail = u at ht
    change e.head = v at hh
    simpa [ht, hh] using (Finset.mem_filter.mp hef).2
  · intro huv
    obtain ⟨e, ht, hh⟩ := hnatural u v huv
    have hef : e ∈ Finset.univ.filter fun f : Edge D.area => R f.tail f.head := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [ht, hh] using huv⟩
    have hef' : e ∈ fullSelection θ := by rw [hfull]; exact hef
    simpa [ht, hh] using (mem_fullSelection_iff_selected θ e).mp hef'

/-- Recover an orientation by rebuilding it from its selected endpoint
relation. -/
theorem ofSelectedRelation_selected (hforward : Forward D) (θ : Orientation D) :
    ofSelectedRelation hforward (D.edgeData.selected θ.val)
        (by
          intro u v huv
          obtain ⟨e, _, ht, hh⟩ := huv
          exact ⟨e, ht, hh⟩)
        (by
          intro e he
          exact ⟨e, Finset.mem_union_left _ he, rfl, rfl⟩) = θ := by
  apply fullSelection_injective
  ext e
  rw [mem_fullSelection_iff_selected, mem_fullSelection_iff_selected]
  exact selected_ofSelectedRelation hforward _ _ _ e.tail e.head

end

end VerticalStripLLT.Circular.DiagramProof
