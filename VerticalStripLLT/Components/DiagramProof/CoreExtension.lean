import VerticalStripLLT.Components.DiagramProof.ConvexPaths
import VerticalStripLLT.Components.DiagramProof.ShortFlip

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

/-- An actual core flip lifts to an actual ambient flip with the prescribed exterior. -/
def liftDirected {θ η : Orientation E} (w : DirectedFlipWitness E θ η) :
    DirectedFlipWitness D (C.state θ) (C.state η) := by
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
  have esab := (C.cover_iff hD θ a b).mpr sab
  have esac := (C.cover_iff hD θ a c).mpr sac
  let existence := exists_directedFlip_of_sourceCovers hD (C.state θ)
    (C.embed a) (C.embed b) (C.embed c) esab esac (C.embed.strictMono hbc)
  let w' := Classical.choose (Classical.choose_spec existence)
  have ends := Classical.choose_spec (Classical.choose_spec existence)
  apply directedFlipOfCovers hD esab.1 (C.embed.strictMono hbc) w'.eab w'.ebc
    ends.1 ends.2.1 ends.2.2.1 ends.2.2.2 w'.eab_normal w'.ebc_normal
    esab esac (fun h => snbc ((C.cover_iff hD θ b c).mp h))
    ((C.cover_iff hD η a c).mpr tac) ((C.cover_iff hD η b c).mpr tbc)
    (fun h => tnab ((C.cover_iff hD η a b).mp h))
  intro e heab hebc
  by_cases hnormal : e ∈ D.edgeData.normalEdges
  · rw [normal_mem_iff_selected _ e hnormal, normal_mem_iff_selected _ e hnormal]
    by_cases hcore : ∃ u v, C.embed u = e.tail ∧ C.embed v = e.head
    · obtain ⟨u, v, hu, hv⟩ := hcore
      rw [← hu, ← hv, C.inside, C.inside]
      apply selected_agree w u v
      · rintro ⟨rfl, rfl⟩
        apply heab
        apply D.endpointEmbedding.injective
        exact Prod.ext (hu.symm.trans ends.1.symm) (hv.symm.trans ends.2.1.symm)
      · rintro ⟨rfl, rfl⟩
        apply hebc
        apply D.endpointEmbedding.injective
        exact Prod.ext (hu.symm.trans ends.2.2.1.symm) (hv.symm.trans ends.2.2.2.symm)
    · exact C.outside θ η e.tail e.head hcore
  · have hθ : e ∉ (C.state θ).val := fun h => hnormal ((C.state θ).property.1 h)
    have hη : e ∉ (C.state η).val := fun h => hnormal ((C.state η).property.1 h)
    simp only [hθ, hη]

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
