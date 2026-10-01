import VerticalStripLLT.Components.DiagramProof.Relations.ConvexPaths
import VerticalStripLLT.Components.DiagramProof.Foundation.ShortFlip

/-!
# Lifting flips in a convex core

The interface records an actual orientation extension with fixed exterior.
It proves a path lift only; it does not assert that the image is a whole component.
Specific core constructions must still establish their natural/strict geometry.
-/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k n : ℕ} {E : Diagram k} {D : Diagram n}

/-- An induced selected core with fixed exterior, in the existing orientation types. -/
structure CoreExtension (E : Diagram k) (D : Diagram n) where
  embed : Fin k ↪o Fin n
  convex : ConvexImage embed
  state : Orientation E → Orientation D
  inside : ∀ θ u v,
    D.edgeData.selected (state θ).val (embed u) (embed v) ↔ E.edgeData.selected θ.val u v
  outside : ∀ θ η u v, (¬ ∃ a b, embed a = u ∧ embed b = v) →
    (D.edgeData.selected (state θ).val u v ↔ D.edgeData.selected (state η).val u v)

namespace CoreExtension

variable (C : CoreExtension E D) (hD : Forward D) (hE : Forward E)

theorem state_injective : Function.Injective C.state := by
  intro θ η heq
  apply fullSelection_injective
  ext e
  rw [mem_fullSelection_iff_selected, mem_fullSelection_iff_selected,
    ← C.inside θ, ← C.inside η, heq]

include hD in
theorem cover_iff (θ : Orientation E) (u v : Fin k) :
    Cover (C.state θ) (C.embed u) (C.embed v) ↔ Cover θ u v :=
  relationCover_iff_of_convexImage C.embed C.convex
    (fun {_ _} h => (C.state θ).selected_lt_of_forward hD h)
    (fun u v => (C.inside θ u v).symm) u v

/-- Agreement of core relations away from a flip's two short endpoint pairs. -/
private theorem selected_agree {θ η : Orientation E} (w : DirectedFlipWitness E θ η)
    (u v : Fin k)
    (hab : ¬ (u = w.eab.tail ∧ v = w.eab.head))
    (hbc : ¬ (u = w.eab.head ∧ v = w.ebc.head)) :
    E.edgeData.selected θ.val u v ↔ E.edgeData.selected η.val u v := by
  rw [w.target_eq_source_swap,
    E.selected_short_swap_iff θ.val w.eab w.ebc w.eab_normal
      (a := w.eab.tail) (b := w.eab.head) (c := w.ebc.head) rfl
      (Prod.ext w.short_head_tail.symm rfl)]
  simp only [hab, hbc, not_false_eq_true, and_true, false_or]

/-- Cover tests and unchanged exterior suffice to lift an actual flip; the image
need not be order-convex. -/
def liftDirected_of_cover_iff (ι : Fin k ↪o Fin n)
    (state : Orientation E → Orientation D)
    (hinside : ∀ θ u v,
      D.edgeData.selected (state θ).val (ι u) (ι v) ↔ E.edgeData.selected θ.val u v)
    (houtside : ∀ θ η u v, (¬ ∃ a b, ι a = u ∧ ι b = v) →
      (D.edgeData.selected (state θ).val u v ↔ D.edgeData.selected (state η).val u v))
    (hcovers : ∀ θ u v, Cover (state θ) (ι u) (ι v) ↔ Cover θ u v)
    {θ η : Orientation E} (w : DirectedFlipWitness E θ η) :
    DirectedFlipWitness D (state θ) (state η) := by
  let a := w.eab.tail
  let b := w.eab.head
  let c := w.ebc.head
  let wn := w.normalizeForward hE
  have sab : Cover θ a b := (liftCover_iff_cover hE θ a b).mp wn.source_ab
  have sac : Cover θ a c := (liftCover_iff_cover hE θ a c).mp wn.source_ac
  have tac : Cover η a c := (liftCover_iff_cover hE η a c).mp wn.target_ac
  have tbc : Cover η b c := (liftCover_iff_cover hE η b c).mp wn.target_bc
  have snbc : ¬ Cover θ b c := fun h =>
    wn.source_not_bc ((liftCover_iff_cover hE θ b c).mpr h)
  have tnab : ¬ Cover η a b := fun h =>
    wn.target_not_ab ((liftCover_iff_cover hE η a b).mpr h)
  have hbc : b < c := (w.canonical_triple_order hE).2
  have esab := (hcovers θ a b).mpr sab
  have esac := (hcovers θ a c).mpr sac
  let existence := exists_directedFlip_of_sourceCovers hD (state θ)
    (ι a) (ι b) (ι c) esab esac (ι.strictMono hbc)
  let w' := Classical.choose (Classical.choose_spec existence)
  have ends := Classical.choose_spec (Classical.choose_spec existence)
  apply directedFlipOfCovers hD esab.1 (ι.strictMono hbc) w'.eab w'.ebc
    ends.1 ends.2.1 ends.2.2.1 ends.2.2.2 w'.eab_normal w'.ebc_normal
    esab esac (fun h => snbc ((hcovers θ b c).mp h))
    ((hcovers η a c).mpr tac) ((hcovers η b c).mpr tbc)
    (fun h => tnab ((hcovers η a b).mp h))
  intro e heab hebc
  by_cases hnormal : e ∈ D.edgeData.normalEdges
  · rw [normal_mem_iff_selected _ e hnormal, normal_mem_iff_selected _ e hnormal]
    by_cases hcore : ∃ u v, ι u = e.tail ∧ ι v = e.head
    · obtain ⟨u, v, hu, hv⟩ := hcore
      rw [← hu, ← hv, hinside, hinside]
      apply selected_agree w u v
      · rintro ⟨rfl, rfl⟩
        apply heab
        apply D.endpointEmbedding.injective
        exact Prod.ext (hu.symm.trans ends.1.symm) (hv.symm.trans ends.2.1.symm)
      · rintro ⟨rfl, rfl⟩
        apply hebc
        apply D.endpointEmbedding.injective
        exact Prod.ext (hu.symm.trans ends.2.2.1.symm) (hv.symm.trans ends.2.2.2.symm)
    · exact houtside θ η e.tail e.head hcore
  · have hθ : e ∉ (state θ).val := fun h => hnormal ((state θ).property.1 h)
    have hη : e ∉ (state η).val := fun h => hnormal ((state η).property.1 h)
    simp only [hθ, hη]

/-- An actual core flip lifts to an actual ambient flip with the prescribed exterior. -/
def liftDirected {θ η : Orientation E} (w : DirectedFlipWitness E θ η) :
    DirectedFlipWitness D (C.state θ) (C.state η) :=
  liftDirected_of_cover_iff hD hE C.embed C.state C.inside C.outside (C.cover_iff hD) w

include hD hE in
/-- The same cover interface lifts an entire path while retaining the exterior. -/
theorem lift_reachable_of_cover_iff (ι : Fin k ↪o Fin n)
    (state : Orientation E → Orientation D)
    (hinside : ∀ θ u v,
      D.edgeData.selected (state θ).val (ι u) (ι v) ↔ E.edgeData.selected θ.val u v)
    (houtside : ∀ θ η u v, (¬ ∃ a b, ι a = u ∧ ι b = v) →
      (D.edgeData.selected (state θ).val u v ↔ D.edgeData.selected (state η).val u v))
    (hcovers : ∀ θ u v, Cover (state θ) (ι u) (ι v) ↔ Cover θ u v)
    {θ η : Orientation E} (h : Relation.ReflTransGen (Flip E) θ η) :
    Relation.ReflTransGen (Flip D) (state θ) (state η) := by
  apply h.lift state
  intro α β hstep
  rcases hstep with hstep | hstep
  · exact Or.inl ⟨liftDirected_of_cover_iff hD hE ι state hinside houtside hcovers hstep.some⟩
  · exact Or.inr ⟨liftDirected_of_cover_iff hD hE ι state hinside houtside hcovers hstep.some⟩

include hD hE in
theorem lift_flip {θ η : Orientation E} (h : Flip E θ η) :
    Flip D (C.state θ) (C.state η) := by
  rcases h with h | h
  · exact Or.inl ⟨C.liftDirected hD hE h.some⟩
  · exact Or.inr ⟨C.liftDirected hD hE h.some⟩

include hD hE in
theorem lift_reachable {θ η : Orientation E} (h : Relation.ReflTransGen (Flip E) θ η) :
    Relation.ReflTransGen (Flip D) (C.state θ) (C.state η) :=
  h.lift C.state (fun _ _ hs => C.lift_flip hD hE hs)

include hD hE in
theorem lift_mem_flipComponent {θ η : Orientation E} (h : η ∈ flipComponent E θ) :
    C.state η ∈ flipComponent D (C.state θ) :=
  mem_flipComponent_iff.mpr (C.lift_reachable hD hE (mem_flipComponent_iff.mp h))

end CoreExtension

end

end VerticalStripLLT.Circular.DiagramProof
