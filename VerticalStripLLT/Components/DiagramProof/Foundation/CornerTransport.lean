import VerticalStripLLT.Components.DiagramProof.Foundation.Basic
import VerticalStripLLT.Components.UndecoratedComponents
import VerticalStripLLT.Circular.CornerDiagram

/-! Maximal-corner membership and exact component transport after marking a corner. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {n : ℕ} {D : Diagram n}

theorem corner_ne_flip_shorts {θ η : Orientation D} (w : DirectedFlipWitness D θ η)
    {e : Edge D.area} (he : IsCorner e) : e ≠ w.eab ∧ e ≠ w.ebc := by
  let E := D.strictify e he
  have hlong : E.naturalLift w.longEdge w.a w.c := w.longEdge_lift
  obtain ⟨f, g, hf, hg, hfnat, hgnat⟩ := E.normalShortEdges_of_naturalLift
    hlong w.cyclicWindow.1 w.cyclicWindow.2.1
  have hfab : f = w.eab := E.naturalLift_injective hfnat w.ab_lift
  have hgbc : g = w.ebc := E.naturalLift_injective hgnat w.bc_lift
  have hstrict : e ∈ E.strict := Finset.mem_insert_self _ _
  constructor
  · intro heq
    exact (Finset.mem_sdiff.mp hf).2 (hfab.symm ▸ heq ▸ hstrict)
  · intro heq
    exact (Finset.mem_sdiff.mp hg).2 (hgbc.symm ▸ heq ▸ hstrict)

theorem corner_mem_iff_of_flip {θ η : Orientation D} (h : Flip D θ η)
    {e : Edge D.area} (he : IsCorner e) : e ∈ fullSelection θ ↔ e ∈ fullSelection η := by
  have directed {α β : Orientation D} (w : DirectedFlipWitness D α β) :
      e ∈ fullSelection α ↔ e ∈ fullSelection β := by
    obtain ⟨hab, hbc⟩ := corner_ne_flip_shorts w he
    simp only [fullSelection, Finset.mem_union, w.agree_elsewhere e hab hbc]
  rcases h with h | h
  · exact directed h.some
  · exact (directed h.some).symm

theorem corner_mem_iff_of_reachable {θ η : Orientation D}
    (h : Relation.ReflTransGen (Flip D) θ η) {e : Edge D.area} (he : IsCorner e) :
    e ∈ fullSelection θ ↔ e ∈ fullSelection η := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ hstep ih => exact ih.trans (corner_mem_iff_of_flip hstep he)

theorem reachable_toUndecorated_iff {θ η : Orientation D} :
    Relation.ReflTransGen (Flip D.undecorated) θ.toUndecorated η.toUndecorated ↔
      Relation.ReflTransGen (Flip D) θ η := by
  constructor
  · intro h
    obtain ⟨ξ, hξ, hξη⟩ := exists_original_of_undecorated_reachable h
    have hξη' : ξ = η := Orientation.toUndecorated_injective hξη
    exact hξη' ▸ hξ
  · exact reachable_toUndecorated

/-- Reclassify one selected maximal corner as strict, with the full state unchanged. -/
def markCorner (hforward : Forward D) (θ : Orientation D) (e : Edge D.area)
    (he : IsCorner e) (hselected : e ∈ fullSelection θ) : Orientation (D.strictify e he) :=
  ofFullSelection (D := D.strictify e he) hforward (D.strict ∪ θ.val) (by
    intro f hf
    rcases Finset.mem_insert.mp hf with hf | hf
    · exact hf.symm ▸ hselected
    · exact Finset.mem_union_left _ hf)

@[simp]
theorem fullSelection_markCorner (hforward : Forward D) (θ : Orientation D)
    (e : Edge D.area) (he : IsCorner e) (hs : e ∈ fullSelection θ) :
    fullSelection (markCorner hforward θ e he hs) = fullSelection θ :=
  fullSelection_ofFullSelection (D := D.strictify e he) hforward _ _

@[simp]
theorem selected_markCorner_iff (hforward : Forward D) (θ : Orientation D)
    (e : Edge D.area) (he : IsCorner e) (hs : e ∈ fullSelection θ) (u v : Fin n) :
    (D.strictify e he).edgeData.selected (markCorner hforward θ e he hs).val u v ↔
      D.edgeData.selected θ.val u v := by
  change (∃ f ∈ fullSelection (markCorner hforward θ e he hs),
    f.tail = u ∧ f.head = v) ↔ ∃ f ∈ fullSelection θ, f.tail = u ∧ f.head = v
  rw [fullSelection_markCorner]
  rfl

@[simp]
theorem markCorner_toUndecorated (hforward : Forward D) (θ : Orientation D)
    (e : Edge D.area) (he : IsCorner e) (hs : e ∈ fullSelection θ) :
    (markCorner hforward θ e he hs).toUndecorated = θ.toUndecorated := by
  apply Subtype.ext
  exact fullSelection_markCorner hforward θ e he hs

theorem reachable_markCorner_iff (hforward : Forward D) {θ η : Orientation D}
    (e : Edge D.area) (he : IsCorner e)
    (hθ : e ∈ fullSelection θ) (hη : e ∈ fullSelection η) :
    Relation.ReflTransGen (Flip (D.strictify e he))
      (markCorner hforward θ e he hθ) (markCorner hforward η e he hη) ↔
      Relation.ReflTransGen (Flip D) θ η := by
  rw [← reachable_toUndecorated_iff, markCorner_toUndecorated,
    markCorner_toUndecorated]
  change Relation.ReflTransGen (Flip D.undecorated) θ.toUndecorated η.toUndecorated ↔ _
  exact reachable_toUndecorated_iff

/-- Every state in the marked component comes from the whole original component. -/
theorem mem_flipComponent_markCorner_iff (hforward : Forward D) (θ : Orientation D)
    (e : Edge D.area) (he : IsCorner e) (hs : e ∈ fullSelection θ)
    (α : Orientation (D.strictify e he)) :
    α ∈ flipComponent (D.strictify e he) (markCorner hforward θ e he hs) ↔
      ∃ η ∈ flipComponent D θ, fullSelection α = fullSelection η := by
  constructor
  · intro hα
    have hpath := reachable_toUndecorated (mem_flipComponent_iff.mp hα)
    rw [markCorner_toUndecorated] at hpath
    change Relation.ReflTransGen (Flip D.undecorated) θ.toUndecorated α.toUndecorated at hpath
    obtain ⟨η, hη, heq⟩ := exists_original_of_undecorated_reachable (D := D) hpath
    refine ⟨η, mem_flipComponent_iff.mpr hη, ?_⟩
    exact (congrArg Subtype.val heq).symm
  · rintro ⟨η, hη, heq⟩
    have hsη : e ∈ fullSelection η :=
      (corner_mem_iff_of_reachable (mem_flipComponent_iff.mp hη) he).mp hs
    have hαeq : α = markCorner hforward η e he hsη := by
      apply fullSelection_injective
      rw [fullSelection_markCorner]
      exact heq
    rw [hαeq, mem_flipComponent_iff, reachable_markCorner_iff]
    exact mem_flipComponent_iff.mp hη

theorem markCorner_hrv (hforward : Forward D) (θ : Orientation D)
    (e : Edge D.area) (he : IsCorner e) (hs : e ∈ fullSelection θ) :
    (markCorner hforward θ e he hs).hrv = θ.hrv := by
  rw [← Orientation.toUndecorated_hrv (markCorner hforward θ e he hs),
    markCorner_toUndecorated, Orientation.toUndecorated_hrv]

theorem markCorner_strictOrderEnumerator (hforward : Forward D) (θ : Orientation D)
    (e : Edge D.area) (he : IsCorner e) (hs : e ∈ fullSelection θ) (m : ℕ) :
    (D.strictify e he).edgeData.strictOrderEnumerator (markCorner hforward θ e he hs).val m =
      D.edgeData.strictOrderEnumerator θ.val m := by
  rw [← Orientation.toUndecorated_strictOrderEnumerator (markCorner hforward θ e he hs),
    markCorner_toUndecorated]
  exact θ.toUndecorated_strictOrderEnumerator m

end

end VerticalStripLLT.Circular.DiagramProof
