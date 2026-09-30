import VerticalStripLLT.Circular.Flip
import VerticalStripLLT.Components.ShortEdges
import VerticalStripLLT.Components.UndecoratedSelection

/-!
# Selected sets and edge layers for the ordinary diagram proof

These are interfaces to the existing orientations and complete flip components.
Total selected size includes strict edges; the original weight exponent does not.
-/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {n : ℕ} {D : Diagram n}

/-- All natural edges increase in the fixed vertex order. -/
def Forward (D : Diagram n) : Prop := ∀ e : Edge D.area, e.tail < e.head

/-- The actual selected edges, including the required strict corners. -/
def fullSelection (θ : Orientation D) : Finset (Edge D.area) := D.strict ∪ θ.val

/-- Layer size is independent of how the selected corners are marked. -/
def totalSelected (θ : Orientation D) : ℕ := (fullSelection θ).card

theorem strict_disjoint_selection (θ : Orientation D) : Disjoint D.strict θ.val := by
  apply Finset.disjoint_left.mpr
  intro e hs he
  exact (Finset.mem_sdiff.mp (θ.property.1 he)).2 hs

theorem totalSelected_eq (θ : Orientation D) :
    totalSelected θ = D.strict.card + θ.val.card :=
  Finset.card_union_of_disjoint (strict_disjoint_selection θ)

theorem fullSelection_sdiff_strict (θ : Orientation D) :
    fullSelection θ \ D.strict = θ.val := by
  ext e
  have hn : e ∈ θ.val → e ∉ D.strict := fun he =>
    (Finset.mem_sdiff.mp (θ.property.1 he)).2
  simp only [fullSelection, Finset.mem_sdiff, Finset.mem_union]
  grind

theorem fullSelection_injective :
    Function.Injective (fullSelection : Orientation D → Finset (Edge D.area)) := by
  intro θ η h
  apply Subtype.ext
  rw [← fullSelection_sdiff_strict θ, ← fullSelection_sdiff_strict η, h]

/-- Every forward full selection containing the strict edges is an actual state. -/
def ofFullSelection (hforward : Forward D) (A : Finset (Edge D.area))
    (_hstrict : D.strict ⊆ A) : Orientation D :=
  D.orientationOfForward hforward (A \ D.strict) (by
    intro e he
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp he).2⟩)

@[simp]
theorem fullSelection_ofFullSelection (hforward : Forward D)
    (A : Finset (Edge D.area)) (hstrict : D.strict ⊆ A) :
    fullSelection (ofFullSelection hforward A hstrict) = A :=
  Finset.union_sdiff_of_subset hstrict

@[simp]
theorem ofFullSelection_fullSelection (hforward : Forward D) (θ : Orientation D) :
    ofFullSelection hforward (fullSelection θ) Finset.subset_union_left = θ := by
  apply fullSelection_injective
  exact fullSelection_ofFullSelection hforward _ _

theorem totalSelected_eq_of_flip {θ η : Orientation D} (h : Flip D θ η) :
    totalSelected θ = totalSelected η := by
  simp only [totalSelected_eq, flip_card_eq h]

theorem totalSelected_eq_of_reachable {θ η : Orientation D}
    (h : Relation.ReflTransGen (Flip D) θ η) : totalSelected θ = totalSelected η := by
  simp only [totalSelected_eq, flip_reachable_card_eq h]

@[simp]
theorem totalSelected_toUndecorated (θ : Orientation D) :
    totalSelected θ.toUndecorated = totalSelected θ := by
  change (∅ ∪ (D.strict ∪ θ.val)).card = (D.strict ∪ θ.val).card
  rw [Finset.empty_union]

/-- An entire fixed-total-edge layer, not a selected collection of anchors. -/
noncomputable def edgeLayer (D : Diagram n) (s : ℕ) : Finset (Orientation D) :=
  Finset.univ.filter fun θ => totalSelected θ = s

@[simp]
theorem mem_edgeLayer {θ : Orientation D} {s : ℕ} :
    θ ∈ edgeLayer D s ↔ totalSelected θ = s := by
  simp [edgeLayer]

theorem flipComponent_subset_edgeLayer {θ : Orientation D} {s : ℕ}
    (hθ : θ ∈ edgeLayer D s) : flipComponent D θ ⊆ edgeLayer D s := by
  intro η hη
  apply mem_edgeLayer.mpr
  exact (totalSelected_eq_of_reachable (mem_flipComponent_iff.mp hη)).symm.trans
    (mem_edgeLayer.mp hθ)

end

end VerticalStripLLT.Circular.DiagramProof
