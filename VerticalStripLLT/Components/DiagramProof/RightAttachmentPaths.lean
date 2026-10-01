import VerticalStripLLT.Components.DiagramProof.RightAttachmentDiagram

/-!
# Flips and whole components of a right attachment

Every natural triangle of the union lies on one side of the shared vertex,
and a forward path between two vertices of one side never leaves it. Hence
cover tests are internal, a flip of the union is exactly one factor flip
with the other factor fixed, and every whole flip component of the union is
the product of two whole factor components.
-/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {n p q : ℕ}

/-- The target of a directed flip is the source with its two shorts exchanged. -/
theorem target_selected_iff {D : Diagram n} {θ η : Orientation D}
    (w : DirectedFlipWitness D θ η) (u v : Fin n) :
    D.edgeData.selected η.val u v ↔
      (u = w.eab.head ∧ v = w.ebc.head) ∨
        (D.edgeData.selected θ.val u v ∧ ¬ (u = w.eab.tail ∧ v = w.eab.head)) := by
  rw [w.target_eq_source_swap]
  exact D.selected_short_swap_iff θ.val w.eab w.ebc w.eab_normal
    (a := w.eab.tail) (b := w.eab.head) (c := w.ebc.head) rfl
    (Prod.ext w.short_head_tail.symm rfl) u v

namespace IsRightAttachment

variable {G : Diagram (p + q + 1)} {L : Diagram (p + 1)} {R : Diagram (q + 1)}
  (h : IsRightAttachment G L R)

include h

/-! ### Internal cover tests -/

theorem cover_left (A : Orientation L) (B : Orientation R) (a b : Fin (p + 1)) :
    Cover (h.glue A B) (attachLeft p q a) (attachLeft p q b) ↔ Cover A a b :=
  relationCover_iff_of_convexImage (attachLeft p q) attachLeft_convex
    (fun {_ _} hs => (h.glue A B).selected_lt_of_forward h.forward hs)
    (fun a b => (h.glue_selected_left A B a b).symm) a b

theorem cover_right (A : Orientation L) (B : Orientation R) (a b : Fin (q + 1)) :
    Cover (h.glue A B) (attachRight p q a) (attachRight p q b) ↔ Cover B a b :=
  relationCover_iff_of_convexImage (attachRight p q) attachRight_convex
    (fun {_ _} hs => (h.glue A B).selected_lt_of_forward h.forward hs)
    (fun a b => (h.glue_selected_right A B a b).symm) a b

/-! ### Lifting factor flips -/

theorem glue_outside_left (B : Orientation R) (A A' : Orientation L)
    (u v : Fin (p + q + 1)) (hout : ¬ ∃ a b, attachLeft p q a = u ∧ attachLeft p q b = v) :
    G.edgeData.selected (h.glue A B).val u v ↔ G.edgeData.selected (h.glue A' B).val u v := by
  rw [h.glue_selected, h.glue_selected]
  constructor <;> rintro (⟨a, b, ha, hb, -⟩ | hr)
  all_goals first
    | exact (hout ⟨a, b, ha, hb⟩).elim
    | exact Or.inr hr

theorem glue_outside_right (A : Orientation L) (B B' : Orientation R)
    (u v : Fin (p + q + 1)) (hout : ¬ ∃ a b, attachRight p q a = u ∧ attachRight p q b = v) :
    G.edgeData.selected (h.glue A B).val u v ↔ G.edgeData.selected (h.glue A B').val u v := by
  rw [h.glue_selected, h.glue_selected]
  constructor <;> rintro (hl | ⟨a, b, ha, hb, -⟩)
  all_goals first
    | exact (hout ⟨a, b, ha, hb⟩).elim
    | exact Or.inl hl

/-- A directed flip of the left factor, with the right factor fixed. -/
def liftLeftDirected (B : Orientation R) {A A' : Orientation L}
    (w : DirectedFlipWitness L A A') : DirectedFlipWitness G (h.glue A B) (h.glue A' B) :=
  CoreExtension.liftDirected_of_cover_iff h.forward h.forwardL (attachLeft p q)
    (fun A => h.glue A B) (fun A a b => h.glue_selected_left A B a b)
    (fun A A' u v hout => h.glue_outside_left B A A' u v hout)
    (fun A a b => h.cover_left A B a b) w

/-- A directed flip of the right factor, with the left factor fixed. -/
def liftRightDirected (A : Orientation L) {B B' : Orientation R}
    (w : DirectedFlipWitness R B B') : DirectedFlipWitness G (h.glue A B) (h.glue A B') :=
  CoreExtension.liftDirected_of_cover_iff h.forward h.forwardR (attachRight p q)
    (fun B => h.glue A B) (fun B a b => h.glue_selected_right A B a b)
    (fun B B' u v hout => h.glue_outside_right A B B' u v hout)
    (fun B a b => h.cover_right A B a b) w

theorem flip_lift_left (B : Orientation R) {A A' : Orientation L} (hA : Flip L A A') :
    Flip G (h.glue A B) (h.glue A' B) :=
  hA.imp (fun hd => ⟨h.liftLeftDirected B hd.some⟩)
    (fun hd => ⟨h.liftLeftDirected B hd.some⟩)

theorem flip_lift_right (A : Orientation L) {B B' : Orientation R} (hB : Flip R B B') :
    Flip G (h.glue A B) (h.glue A B') :=
  hB.imp (fun hd => ⟨h.liftRightDirected A hd.some⟩)
    (fun hd => ⟨h.liftRightDirected A hd.some⟩)

theorem reachable_lift_left (B : Orientation R) {A A' : Orientation L}
    (hA : Relation.ReflTransGen (Flip L) A A') :
    Relation.ReflTransGen (Flip G) (h.glue A B) (h.glue A' B) :=
  hA.lift (h.glue · B) fun _ _ => h.flip_lift_left B

theorem reachable_lift_right (A : Orientation L) {B B' : Orientation R}
    (hB : Relation.ReflTransGen (Flip R) B B') :
    Relation.ReflTransGen (Flip G) (h.glue A B) (h.glue A B') :=
  hB.lift (h.glue A) fun _ _ => h.flip_lift_right A

/-! ### Projecting flips of the union -/

/-- A directed flip of the union changes exactly one factor, by a factor flip. -/
theorem directedFlip_cases (A : Orientation L) (B : Orientation R) {η : Orientation G}
    (w : DirectedFlipWitness G (h.glue A B) η) :
    (∃ A', DirectedFlip L A A' ∧ η = h.glue A' B) ∨
      (∃ B', DirectedFlip R B B' ∧ η = h.glue A B') := by
  have hord := w.canonical_triple_order h.forward
  let wn := w.normalizeForward h.forward
  have sab : Cover (h.glue A B) w.eab.tail w.eab.head :=
    (liftCover_iff_cover h.forward _ _ _).mp wn.source_ab
  have sac : Cover (h.glue A B) w.eab.tail w.ebc.head :=
    (liftCover_iff_cover h.forward _ _ _).mp wn.source_ac
  have hlong : naturalRel G w.eab.tail w.ebc.head :=
    ⟨w.longEdge, w.longEdge_tail.symm, w.longEdge_head.symm⟩
  have hab : w.eab.tail.val < w.eab.head.val := hord.1
  have hbc : w.eab.head.val < w.ebc.head.val := hord.2
  rcases (h.natural _ _).mp hlong with ⟨a, c, ha, hc, -⟩ | ⟨a, c, ha, hc, -⟩
  · obtain ⟨b, hb⟩ := (exists_attachLeft_iff w.eab.head).mpr (by
      have := (exists_attachLeft_iff _).mp ⟨c, hc⟩
      lia)
    have sab' : Cover A a b := (h.cover_left A B a b).mp (by rw [ha, hb]; exact sab)
    have sac' : Cover A a c := (h.cover_left A B a c).mp (by rw [ha, hc]; exact sac)
    have hbc' : b < c := (attachLeft p q).lt_iff_lt.mp (by rw [hb, hc]; exact hord.2)
    obtain ⟨A', w', hat, hah, -, hch⟩ :=
      exists_directedFlip_of_sourceCovers h.forwardL A a b c sab' sac' hbc'
    refine Or.inl ⟨A', ⟨w'⟩, ?_⟩
    rw [← h.glue_restrict η]
    congr 1
    · apply orientation_eq_of_selected_iff
      intro x y
      rw [restrictLeft_selected, target_selected_iff w, target_selected_iff w',
        glue_selected_left, hat, hah, hch, ← ha, ← hb, ← hc]
      simp only [(attachLeft p q).injective.eq_iff]
    · apply orientation_eq_of_selected_iff
      intro x y
      have hne (s t : Fin (p + 1)) (hst : s < t) :
          ¬ (attachRight p q x = attachLeft p q s ∧ attachRight p q y = attachLeft p q t) := by
        rintro ⟨hs, ht⟩
        obtain ⟨rfl, -⟩ := attachLeft_eq_attachRight_iff.mp hs.symm
        obtain ⟨rfl, -⟩ := attachLeft_eq_attachRight_iff.mp ht.symm
        exact lt_irrefl _ hst
      have hab' : a < b := (attachLeft p q).lt_iff_lt.mp (by rw [ha, hb]; exact hord.1)
      rw [restrictRight_selected, target_selected_iff w, glue_selected_right,
        ← ha, ← hb, ← hc]
      simp only [hne b c hbc', hne a b hab', false_or, not_false_eq_true, and_true]
  · obtain ⟨b, hb⟩ := (exists_attachRight_iff w.eab.head).mpr (by
      have := (exists_attachRight_iff _).mp ⟨a, ha⟩
      lia)
    have sab' : Cover B a b := (h.cover_right A B a b).mp (by rw [ha, hb]; exact sab)
    have sac' : Cover B a c := (h.cover_right A B a c).mp (by rw [ha, hc]; exact sac)
    have hbc' : b < c := (attachRight p q).lt_iff_lt.mp (by rw [hb, hc]; exact hord.2)
    obtain ⟨B', w', hat, hah, -, hch⟩ :=
      exists_directedFlip_of_sourceCovers h.forwardR B a b c sab' sac' hbc'
    refine Or.inr ⟨B', ⟨w'⟩, ?_⟩
    rw [← h.glue_restrict η]
    congr 1
    · apply orientation_eq_of_selected_iff
      intro x y
      have hne (s t : Fin (q + 1)) (hst : s < t) :
          ¬ (attachLeft p q x = attachRight p q s ∧ attachLeft p q y = attachRight p q t) := by
        rintro ⟨hs, ht⟩
        obtain ⟨-, rfl⟩ := attachLeft_eq_attachRight_iff.mp hs
        obtain ⟨-, rfl⟩ := attachLeft_eq_attachRight_iff.mp ht
        exact lt_irrefl _ hst
      have hab' : a < b := (attachRight p q).lt_iff_lt.mp (by rw [ha, hb]; exact hord.1)
      rw [restrictLeft_selected, target_selected_iff w, glue_selected_left,
        ← ha, ← hb, ← hc]
      simp only [hne b c hbc', hne a b hab', false_or, not_false_eq_true, and_true]
    · apply orientation_eq_of_selected_iff
      intro x y
      rw [restrictRight_selected, target_selected_iff w, target_selected_iff w',
        glue_selected_right, hat, hah, hch, ← ha, ← hb, ← hc]
      simp only [(attachRight p q).injective.eq_iff]

/-- A flip of the union is exactly a flip of one factor with the other fixed. -/
theorem flip_glue_iff {A A' : Orientation L} {B B' : Orientation R} :
    Flip G (h.glue A B) (h.glue A' B') ↔
      (Flip L A A' ∧ B = B') ∨ (A = A' ∧ Flip R B B') := by
  constructor
  · rintro (hw | hw)
    · rcases h.directedFlip_cases A B hw.some with ⟨A'', hd, heq⟩ | ⟨B'', hd, heq⟩
      · obtain ⟨rfl, rfl⟩ := h.glue_inj heq
        exact Or.inl ⟨Or.inl hd, rfl⟩
      · obtain ⟨rfl, rfl⟩ := h.glue_inj heq
        exact Or.inr ⟨rfl, Or.inl hd⟩
    · rcases h.directedFlip_cases A' B' hw.some with ⟨A'', hd, heq⟩ | ⟨B'', hd, heq⟩
      · obtain ⟨rfl, rfl⟩ := h.glue_inj heq
        exact Or.inl ⟨Or.inr hd, rfl⟩
      · obtain ⟨rfl, rfl⟩ := h.glue_inj heq
        exact Or.inr ⟨rfl, Or.inr hd⟩
  · rintro (⟨hf, rfl⟩ | ⟨rfl, hf⟩)
    · exact h.flip_lift_left B hf
    · exact h.flip_lift_right A hf

/-- Actual paths of the union project to actual paths of both factors. -/
theorem reachable_restrict {θ η : Orientation G}
    (hp : Relation.ReflTransGen (Flip G) θ η) :
    Relation.ReflTransGen (Flip L) (h.restrictLeft θ) (h.restrictLeft η) ∧
      Relation.ReflTransGen (Flip R) (h.restrictRight θ) (h.restrictRight η) := by
  induction hp with
  | refl => exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | @tail ξ ζ _ hstep ih =>
    rw [← h.glue_restrict ξ, ← h.glue_restrict ζ] at hstep
    rcases h.flip_glue_iff.mp hstep with ⟨hf, hB⟩ | ⟨hA, hf⟩
    · exact ⟨ih.1.tail hf, hB ▸ ih.2⟩
    · exact ⟨hA ▸ ih.1, ih.2.tail hf⟩

theorem reachable_glue_iff (A A' : Orientation L) (B B' : Orientation R) :
    Relation.ReflTransGen (Flip G) (h.glue A B) (h.glue A' B') ↔
      Relation.ReflTransGen (Flip L) A A' ∧ Relation.ReflTransGen (Flip R) B B' := by
  constructor
  · intro hp
    simpa only [restrictLeft_glue, restrictRight_glue] using h.reachable_restrict hp
  · rintro ⟨hA, hB⟩
    exact (h.reachable_lift_left B hA).trans (h.reachable_lift_right A' hB)

/-- The whole component of a union state is the product of the two whole
factor components. -/
theorem flipComponent_glue (A : Orientation L) (B : Orientation R) :
    flipComponent G (h.glue A B) =
      (flipComponent L A ×ˢ flipComponent R B).map h.stateEquiv.toEmbedding := by
  ext η
  obtain ⟨⟨A', B'⟩, rfl⟩ := h.stateEquiv.surjective η
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply, Finset.mem_product,
    mem_flipComponent_iff, mem_flipComponent_iff, mem_flipComponent_iff]
  exact h.reachable_glue_iff A A' B B'

theorem sum_flipComponent_glue {M : Type*} [AddCommMonoid M] (f : Orientation G → M)
    (A : Orientation L) (B : Orientation R) :
    ∑ η ∈ flipComponent G (h.glue A B), f η =
      ∑ A' ∈ flipComponent L A, ∑ B' ∈ flipComponent R B, f (h.glue A' B') := by
  rw [h.flipComponent_glue, Finset.sum_map, Finset.sum_product]
  rfl

end IsRightAttachment

end

end VerticalStripLLT.Circular.DiagramProof
