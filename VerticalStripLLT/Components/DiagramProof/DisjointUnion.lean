import VerticalStripLLT.Components.DiagramProof.RelationalValues
import VerticalStripLLT.Components.DiagramProof.InducedRestriction
import VerticalStripLLT.Components.DiagramProof.InducedDecorations
import VerticalStripLLT.Components.DiagramProof.MarkedValues
import Mathlib.Algebra.BigOperators.Fin

/-!
# Disjoint natural components factor

If no natural edge crosses between the first `p` vertices and the last `q`
vertices, every triangle and every cover test lies on one side. Hence the flip
graph is the Cartesian product of the two flip graphs and every whole component is
a product of whole components. Strictly increasing colourings split into two
independent colourings, and the HRV fibres of the two sides are disjoint, so both
values multiply.
-/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {n p q : ℕ}

/-! ### Embeddings -/

/-- The first `p` vertices. -/
def disjLeft (p q : ℕ) : Fin p ↪o Fin (p + q) :=
  OrderEmbedding.ofStrictMono (fun a => ⟨a.val, by have := a.isLt; lia⟩)
    (fun a b h => by change a.val < b.val; exact h)

/-- The last `q` vertices. -/
def disjRight (p q : ℕ) : Fin q ↪o Fin (p + q) :=
  OrderEmbedding.ofStrictMono (fun b => ⟨p + b.val, by have := b.isLt; lia⟩)
    (fun a b h => by
      have h' : a.val < b.val := h
      change p + a.val < p + b.val
      lia)

@[simp] theorem disjLeft_val (a : Fin p) : (disjLeft p q a).val = a.val := rfl

@[simp] theorem disjRight_val (b : Fin q) : (disjRight p q b).val = p + b.val := rfl

theorem disjLeft_ne_disjRight (a : Fin p) (b : Fin q) : disjLeft p q a ≠ disjRight p q b := by
  intro h
  have := congrArg Fin.val h
  simp only [disjLeft_val, disjRight_val] at this
  have := a.isLt
  lia

theorem exists_disjLeft_iff (u : Fin (p + q)) : (∃ a, disjLeft p q a = u) ↔ u.val < p := by
  constructor
  · rintro ⟨a, rfl⟩
    exact a.isLt
  · intro h
    exact ⟨⟨u.val, h⟩, Fin.ext rfl⟩

theorem exists_disjRight_iff (u : Fin (p + q)) : (∃ b, disjRight p q b = u) ↔ p ≤ u.val := by
  constructor
  · rintro ⟨b, rfl⟩
    simp
  · intro h
    exact ⟨⟨u.val - p, by have := u.isLt; lia⟩, Fin.ext (by simp; lia)⟩

theorem disjLeft_convex : ConvexImage (disjLeft p q) := by
  intro u v z _ hzv
  apply (exists_disjLeft_iff z).mpr
  have : z.val ≤ (disjLeft p q v).val := hzv
  have := v.isLt
  simp only [disjLeft_val] at *
  lia

theorem disjRight_convex : ConvexImage (disjRight p q) := by
  intro u v z huz _
  apply (exists_disjRight_iff z).mpr
  have : (disjRight p q u).val ≤ z.val := huz
  simp only [disjRight_val] at this
  lia

/-! ### Unions of relations -/

/-- A relation holding exactly on the embedded pairs of the two sides. -/
def disjUnion (X : Fin p → Fin p → Prop) (Y : Fin q → Fin q → Prop) (u v : Fin (p + q)) :
    Prop :=
  (∃ a b, disjLeft p q a = u ∧ disjLeft p q b = v ∧ X a b) ∨
    (∃ a b, disjRight p q a = u ∧ disjRight p q b = v ∧ Y a b)

variable {X : Fin p → Fin p → Prop} {Y : Fin q → Fin q → Prop}

theorem disjUnion_left (a b : Fin p) :
    disjUnion X Y (disjLeft p q a) (disjLeft p q b) ↔ X a b := by
  constructor
  · rintro (⟨a', b', ha, hb, h⟩ | ⟨a', b', ha, -, -⟩)
    · rwa [← (disjLeft p q).injective ha, ← (disjLeft p q).injective hb]
    · exact (disjLeft_ne_disjRight a a' ha.symm).elim
  · intro h
    exact Or.inl ⟨a, b, rfl, rfl, h⟩

theorem disjUnion_right (a b : Fin q) :
    disjUnion X Y (disjRight p q a) (disjRight p q b) ↔ Y a b := by
  constructor
  · rintro (⟨a', b', ha, -, -⟩ | ⟨a', b', ha, hb, h⟩)
    · exact (disjLeft_ne_disjRight a' a ha).elim
    · rwa [← (disjRight p q).injective ha, ← (disjRight p q).injective hb]
  · intro h
    exact Or.inr ⟨a, b, rfl, rfl, h⟩

theorem disjUnion_forward (hX : ∀ a b, X a b → a < b) (hY : ∀ a b, Y a b → a < b)
    {u v : Fin (p + q)} (h : disjUnion X Y u v) : u < v := by
  rcases h with ⟨a, b, rfl, rfl, h⟩ | ⟨a, b, rfl, rfl, h⟩
  · exact (disjLeft p q).strictMono (hX a b h)
  · exact (disjRight p q).strictMono (hY a b h)

/-! ### The disjoint-union predicate -/

/-- `G` is the disjoint union of `L` on the first `p` and `R` on the last `q` vertices. -/
structure IsDisjointUnion (G : Diagram (p + q)) (L : Diagram p) (R : Diagram q) : Prop where
  forwardL : Forward L
  forwardR : Forward R
  natural : ∀ u v, naturalRel G u v ↔ disjUnion (naturalRel L) (naturalRel R) u v
  strict : ∀ u v, strictRel G u v ↔ disjUnion (strictRel L) (strictRel R) u v

namespace IsDisjointUnion

variable {G : Diagram (p + q)} {L : Diagram p} {R : Diagram q} (h : IsDisjointUnion G L R)

include h

theorem forward : Forward G := fun e =>
  disjUnion_forward (fun _ _ => naturalRel_forward h.forwardL)
    (fun _ _ => naturalRel_forward h.forwardR) ((h.natural _ _).mp ⟨e, rfl, rfl⟩)

theorem natural_left (a b : Fin p) :
    naturalRel G (disjLeft p q a) (disjLeft p q b) ↔ naturalRel L a b :=
  (h.natural _ _).trans (disjUnion_left a b)

theorem natural_right (a b : Fin q) :
    naturalRel G (disjRight p q a) (disjRight p q b) ↔ naturalRel R a b :=
  (h.natural _ _).trans (disjUnion_right a b)

theorem strict_left (a b : Fin p) :
    strictRel G (disjLeft p q a) (disjLeft p q b) ↔ strictRel L a b :=
  (h.strict _ _).trans (disjUnion_left a b)

theorem strict_right (a b : Fin q) :
    strictRel G (disjRight p q a) (disjRight p q b) ↔ strictRel R a b :=
  (h.strict _ _).trans (disjUnion_right a b)

/-- Restrict a state of the union to the left side. -/
def restrictLeft (θ : Orientation G) : Orientation L :=
  inducedRestrict h.forwardL (disjLeft p q) (fun u v => (h.natural_left u v).symm)
    (fun u v => (h.strict_left u v).symm) θ

/-- Restrict a state of the union to the right side. -/
def restrictRight (θ : Orientation G) : Orientation R :=
  inducedRestrict h.forwardR (disjRight p q) (fun u v => (h.natural_right u v).symm)
    (fun u v => (h.strict_right u v).symm) θ

theorem restrictLeft_selected (θ : Orientation G) (a b : Fin p) :
    L.edgeData.selected (h.restrictLeft θ).val a b ↔
      G.edgeData.selected θ.val (disjLeft p q a) (disjLeft p q b) :=
  inducedRestrict_selected ..

theorem restrictRight_selected (θ : Orientation G) (a b : Fin q) :
    R.edgeData.selected (h.restrictRight θ).val a b ↔
      G.edgeData.selected θ.val (disjRight p q a) (disjRight p q b) :=
  inducedRestrict_selected ..

/-- The selected union of one state of each side. -/
def glue (A : Orientation L) (B : Orientation R) : Orientation G :=
  ofSelectedRelation h.forward
    (disjUnion (L.edgeData.selected A.val) (R.edgeData.selected B.val))
    (by
      rintro u v (⟨a, b, rfl, rfl, e, -, ht, hh⟩ | ⟨a, b, rfl, rfl, e, -, ht, hh⟩)
      · exact (h.natural_left a b).mpr ⟨e, ht, hh⟩
      · exact (h.natural_right a b).mpr ⟨e, ht, hh⟩)
    (by
      intro e he
      rcases (h.strict e.tail e.head).mp ⟨e, he, rfl, rfl⟩ with
        ⟨a, b, ha, hb, f, hf, ht, hh⟩ | ⟨a, b, ha, hb, f, hf, ht, hh⟩
      · exact Or.inl ⟨a, b, ha, hb, f, Finset.mem_union_left _ hf, ht, hh⟩
      · exact Or.inr ⟨a, b, ha, hb, f, Finset.mem_union_left _ hf, ht, hh⟩)

theorem glue_selected (A : Orientation L) (B : Orientation R) (u v : Fin (p + q)) :
    G.edgeData.selected (h.glue A B).val u v ↔
      disjUnion (L.edgeData.selected A.val) (R.edgeData.selected B.val) u v :=
  selected_ofSelectedRelation ..

theorem glue_selected_left (A : Orientation L) (B : Orientation R) (a b : Fin p) :
    G.edgeData.selected (h.glue A B).val (disjLeft p q a) (disjLeft p q b) ↔
      L.edgeData.selected A.val a b :=
  (h.glue_selected A B _ _).trans (disjUnion_left a b)

theorem glue_selected_right (A : Orientation L) (B : Orientation R) (a b : Fin q) :
    G.edgeData.selected (h.glue A B).val (disjRight p q a) (disjRight p q b) ↔
      R.edgeData.selected B.val a b :=
  (h.glue_selected A B _ _).trans (disjUnion_right a b)

theorem selected_iff (θ : Orientation G) (u v : Fin (p + q)) :
    G.edgeData.selected θ.val u v ↔
      disjUnion (L.edgeData.selected (h.restrictLeft θ).val)
        (R.edgeData.selected (h.restrictRight θ).val) u v := by
  constructor
  · intro hs
    obtain ⟨e, -, ht, hh⟩ := id hs
    rcases (h.natural u v).mp ⟨e, ht, hh⟩ with ⟨a, b, rfl, rfl, -⟩ | ⟨a, b, rfl, rfl, -⟩
    · exact Or.inl ⟨a, b, rfl, rfl, (h.restrictLeft_selected θ a b).mpr hs⟩
    · exact Or.inr ⟨a, b, rfl, rfl, (h.restrictRight_selected θ a b).mpr hs⟩
  · rintro (⟨a, b, rfl, rfl, hab⟩ | ⟨a, b, rfl, rfl, hab⟩)
    · exact (h.restrictLeft_selected θ a b).mp hab
    · exact (h.restrictRight_selected θ a b).mp hab

theorem restrictLeft_glue (A : Orientation L) (B : Orientation R) :
    h.restrictLeft (h.glue A B) = A :=
  orientation_eq_of_selected_iff fun a b => by
    rw [restrictLeft_selected, glue_selected_left]

theorem restrictRight_glue (A : Orientation L) (B : Orientation R) :
    h.restrictRight (h.glue A B) = B :=
  orientation_eq_of_selected_iff fun a b => by
    rw [restrictRight_selected, glue_selected_right]

theorem glue_restrict (θ : Orientation G) :
    h.glue (h.restrictLeft θ) (h.restrictRight θ) = θ :=
  orientation_eq_of_selected_iff fun u v => by rw [glue_selected, selected_iff]

theorem glue_inj {A A' : Orientation L} {B B' : Orientation R}
    (heq : h.glue A B = h.glue A' B') : A = A' ∧ B = B' :=
  ⟨by simpa only [restrictLeft_glue] using congrArg h.restrictLeft heq,
    by simpa only [restrictRight_glue] using congrArg h.restrictRight heq⟩

/-- Restriction and selected union are inverse bijections. -/
def stateEquiv : Orientation L × Orientation R ≃ Orientation G where
  toFun x := h.glue x.1 x.2
  invFun θ := (h.restrictLeft θ, h.restrictRight θ)
  left_inv x := Prod.ext (h.restrictLeft_glue x.1 x.2) (h.restrictRight_glue x.1 x.2)
  right_inv θ := h.glue_restrict θ

/-! ### Flips -/

theorem cover_left (A : Orientation L) (B : Orientation R) (a b : Fin p) :
    Cover (h.glue A B) (disjLeft p q a) (disjLeft p q b) ↔ Cover A a b :=
  relationCover_iff_of_convexImage (disjLeft p q) disjLeft_convex
    (fun {_ _} hs => (h.glue A B).selected_lt_of_forward h.forward hs)
    (fun a b => (h.glue_selected_left A B a b).symm) a b

theorem cover_right (A : Orientation L) (B : Orientation R) (a b : Fin q) :
    Cover (h.glue A B) (disjRight p q a) (disjRight p q b) ↔ Cover B a b :=
  relationCover_iff_of_convexImage (disjRight p q) disjRight_convex
    (fun {_ _} hs => (h.glue A B).selected_lt_of_forward h.forward hs)
    (fun a b => (h.glue_selected_right A B a b).symm) a b

theorem glue_outside_left (B : Orientation R) (A A' : Orientation L) (u v : Fin (p + q))
    (hout : ¬ ∃ a b, disjLeft p q a = u ∧ disjLeft p q b = v) :
    G.edgeData.selected (h.glue A B).val u v ↔ G.edgeData.selected (h.glue A' B).val u v := by
  rw [h.glue_selected, h.glue_selected]
  constructor <;> rintro (⟨a, b, ha, hb, -⟩ | hr)
  all_goals first
    | exact (hout ⟨a, b, ha, hb⟩).elim
    | exact Or.inr hr

theorem glue_outside_right (A : Orientation L) (B B' : Orientation R) (u v : Fin (p + q))
    (hout : ¬ ∃ a b, disjRight p q a = u ∧ disjRight p q b = v) :
    G.edgeData.selected (h.glue A B).val u v ↔ G.edgeData.selected (h.glue A B').val u v := by
  rw [h.glue_selected, h.glue_selected]
  constructor <;> rintro (hl | ⟨a, b, ha, hb, -⟩)
  all_goals first
    | exact (hout ⟨a, b, ha, hb⟩).elim
    | exact Or.inl hl

theorem flip_lift_left (B : Orientation R) {A A' : Orientation L} (hA : Flip L A A') :
    Flip G (h.glue A B) (h.glue A' B) := by
  have lift := fun {A A' : Orientation L} (w : DirectedFlipWitness L A A') =>
    CoreExtension.liftDirected_of_cover_iff h.forward h.forwardL (disjLeft p q)
      (fun A => h.glue A B) (fun A a b => h.glue_selected_left A B a b)
      (fun A A' u v hout => h.glue_outside_left B A A' u v hout)
      (fun A a b => h.cover_left A B a b) w
  exact hA.imp (fun hd => ⟨lift hd.some⟩) (fun hd => ⟨lift hd.some⟩)

theorem flip_lift_right (A : Orientation L) {B B' : Orientation R} (hB : Flip R B B') :
    Flip G (h.glue A B) (h.glue A B') := by
  have lift := fun {B B' : Orientation R} (w : DirectedFlipWitness R B B') =>
    CoreExtension.liftDirected_of_cover_iff h.forward h.forwardR (disjRight p q)
      (fun B => h.glue A B) (fun B a b => h.glue_selected_right A B a b)
      (fun B B' u v hout => h.glue_outside_right A B B' u v hout)
      (fun B a b => h.cover_right A B a b) w
  exact hB.imp (fun hd => ⟨lift hd.some⟩) (fun hd => ⟨lift hd.some⟩)

/-- A directed flip of the union changes exactly one side. -/
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
  rcases (h.natural _ _).mp hlong with ⟨a, c, ha, hc, -⟩ | ⟨a, c, ha, hc, -⟩
  · obtain ⟨b, hb⟩ := (exists_disjLeft_iff w.eab.head).mpr (by
      have := (exists_disjLeft_iff _).mp ⟨c, hc⟩
      have : w.eab.head.val < w.ebc.head.val := hord.2
      lia)
    have sab' : Cover A a b := (h.cover_left A B a b).mp (by rw [ha, hb]; exact sab)
    have sac' : Cover A a c := (h.cover_left A B a c).mp (by rw [ha, hc]; exact sac)
    have hbc' : b < c := (disjLeft p q).lt_iff_lt.mp (by rw [hb, hc]; exact hord.2)
    obtain ⟨A', w', hat, hah, -, hch⟩ :=
      exists_directedFlip_of_sourceCovers h.forwardL A a b c sab' sac' hbc'
    refine Or.inl ⟨A', ⟨w'⟩, ?_⟩
    rw [← h.glue_restrict η]
    congr 1
    · apply orientation_eq_of_selected_iff
      intro x y
      rw [restrictLeft_selected, target_selected_iff w, target_selected_iff w']
      simp only [swapRel]
      rw [glue_selected_left, hat, hah, hch, ← ha, ← hb, ← hc]
      simp only [(disjLeft p q).injective.eq_iff]
    · apply orientation_eq_of_selected_iff
      intro x y
      rw [restrictRight_selected, target_selected_iff w]
      simp only [swapRel]
      rw [glue_selected_right, ← ha, ← hb, ← hc]
      have h1 : ¬ (disjRight p q x = disjLeft p q b ∧ disjRight p q y = disjLeft p q c) :=
        fun he => disjLeft_ne_disjRight b x he.1.symm
      have h2 : ¬ (disjRight p q x = disjLeft p q a ∧ disjRight p q y = disjLeft p q b) :=
        fun he => disjLeft_ne_disjRight a x he.1.symm
      simp only [h1, h2, false_or, not_false_eq_true, and_true]
  · obtain ⟨b, hb⟩ := (exists_disjRight_iff w.eab.head).mpr (by
      have := (exists_disjRight_iff _).mp ⟨a, ha⟩
      have : w.eab.tail.val < w.eab.head.val := hord.1
      lia)
    have sab' : Cover B a b := (h.cover_right A B a b).mp (by rw [ha, hb]; exact sab)
    have sac' : Cover B a c := (h.cover_right A B a c).mp (by rw [ha, hc]; exact sac)
    have hbc' : b < c := (disjRight p q).lt_iff_lt.mp (by rw [hb, hc]; exact hord.2)
    obtain ⟨B', w', hat, hah, -, hch⟩ :=
      exists_directedFlip_of_sourceCovers h.forwardR B a b c sab' sac' hbc'
    refine Or.inr ⟨B', ⟨w'⟩, ?_⟩
    rw [← h.glue_restrict η]
    congr 1
    · apply orientation_eq_of_selected_iff
      intro x y
      rw [restrictLeft_selected, target_selected_iff w]
      simp only [swapRel]
      rw [glue_selected_left, ← ha, ← hb, ← hc]
      have h1 : ¬ (disjLeft p q x = disjRight p q b ∧ disjLeft p q y = disjRight p q c) :=
        fun he => disjLeft_ne_disjRight x b he.1
      have h2 : ¬ (disjLeft p q x = disjRight p q a ∧ disjLeft p q y = disjRight p q b) :=
        fun he => disjLeft_ne_disjRight x a he.1
      simp only [h1, h2, false_or, not_false_eq_true, and_true]
    · apply orientation_eq_of_selected_iff
      intro x y
      rw [restrictRight_selected, target_selected_iff w, target_selected_iff w']
      simp only [swapRel]
      rw [glue_selected_right, hat, hah, hch, ← ha, ← hb, ← hc]
      simp only [(disjRight p q).injective.eq_iff]

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

theorem reachable_restrict {θ η : Orientation G} (hp : Relation.ReflTransGen (Flip G) θ η) :
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
    exact (hA.lift (h.glue · B) fun _ _ => h.flip_lift_left B).trans
      (hB.lift (h.glue A') fun _ _ => h.flip_lift_right A')

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

/-! ### Values multiply -/

theorem reachable_left_iff (A : Orientation L) (B : Orientation R) (a : Fin p)
    (z : Fin (p + q)) :
    Relation.ReflTransGen (G.edgeData.selected (h.glue A B).val) (disjLeft p q a) z ↔
      ∃ b, disjLeft p q b = z ∧ Relation.ReflTransGen (L.edgeData.selected A.val) a b := by
  have hpaths := reachable_iff_of_convexImage (disjLeft p q) disjLeft_convex
    (fun {_ _} hs => (h.glue A B).selected_lt_of_forward h.forward hs)
    (fun a b => (h.glue_selected_left A B a b).symm)
  constructor
  · intro hz
    -- A path starting on the left never reaches the right side.
    have hleft : z.val < p := by
      have key : ∀ y, Relation.ReflTransGen (G.edgeData.selected (h.glue A B).val)
          (disjLeft p q a) y → y.val < p := by
        intro y hy
        induction hy with
        | refl => exact a.isLt
        | tail _ hs ih =>
          rename_i y' y''
          rcases (h.glue_selected A B _ _).mp hs with ⟨a', b', ha', hb', -⟩ |
            ⟨a', b', ha', -, -⟩
          · rw [← hb']
            exact b'.isLt
          · rw [← ha'] at ih
            simp at ih
      exact key z hz
    obtain ⟨b, rfl⟩ := (exists_disjLeft_iff z).mpr hleft
    exact ⟨b, rfl, (hpaths a b).mp hz⟩
  · rintro ⟨b, rfl, hab⟩
    exact (hpaths a b).mpr hab

theorem reachable_right_iff (A : Orientation L) (B : Orientation R) (a : Fin q)
    (z : Fin (p + q)) :
    Relation.ReflTransGen (G.edgeData.selected (h.glue A B).val) (disjRight p q a) z ↔
      ∃ b, disjRight p q b = z ∧ Relation.ReflTransGen (R.edgeData.selected B.val) a b := by
  have hpaths := reachable_iff_of_convexImage (disjRight p q) disjRight_convex
    (fun {_ _} hs => (h.glue A B).selected_lt_of_forward h.forward hs)
    (fun a b => (h.glue_selected_right A B a b).symm)
  constructor
  · intro hz
    have hle := reachable_le (fun {_ _} hs => (h.glue A B).selected_lt_of_forward h.forward hs)
      hz
    obtain ⟨b, rfl⟩ := (exists_disjRight_iff z).mpr (by
      have : (disjRight p q a).val ≤ z.val := hle
      simp only [disjRight_val] at this
      lia)
    exact ⟨b, rfl, (hpaths a b).mp hz⟩
  · rintro ⟨b, rfl, hab⟩
    exact (hpaths a b).mpr hab

theorem hrv_glue_left (A : Orientation L) (B : Orientation R) (a : Fin p) :
    (h.glue A B).hrv (disjLeft p q a) = disjLeft p q (A.hrv a) := by
  apply hrv_eq_of_reachable_greatest h.forward
  · exact (h.reachable_left_iff A B a _).mpr ⟨_, rfl, A.hrv_reachable a⟩
  · intro v hv
    obtain ⟨b, rfl, hb⟩ := (h.reachable_left_iff A B a v).mp hv
    exact (disjLeft p q).le_iff_le.mpr (A.reachable_le_hrv_of_forward h.forwardL hb)

theorem hrv_glue_right (A : Orientation L) (B : Orientation R) (a : Fin q) :
    (h.glue A B).hrv (disjRight p q a) = disjRight p q (B.hrv a) := by
  apply hrv_eq_of_reachable_greatest h.forward
  · exact (h.reachable_right_iff A B a _).mpr ⟨_, rfl, B.hrv_reachable a⟩
  · intro v hv
    obtain ⟨b, rfl, hb⟩ := (h.reachable_right_iff A B a v).mp hv
    exact (disjRight p q).le_iff_le.mpr (B.reachable_le_hrv_of_forward h.forwardR hb)

omit h in
/-- Increasing colourings of relations which split over the two sides multiply. -/
theorem relationValue_disj {m : ℕ} (RG : Fin (p + q) → Fin (p + q) → Prop)
    (RL : Fin p → Fin p → Prop) (RR : Fin q → Fin q → Prop)
    (hvalid : ∀ c : Fin (p + q) → Fin m,
      (∀ u v, RG u v → c u < c v) ↔
        (∀ x y, RL x y → c (disjLeft p q x) < c (disjLeft p q y)) ∧
          ∀ x y, RR x y → c (disjRight p q x) < c (disjRight p q y)) :
    relationValue RG m = relationValue RL m * relationValue RR m := by
  let e : (Fin (p + q) → Fin m) ≃ (Fin p → Fin m) × (Fin q → Fin m) :=
    { toFun := fun c => (c ∘ disjLeft p q, c ∘ disjRight p q)
      invFun := fun x => Fin.append x.1 x.2
      left_inv := fun c => by
        exact Fin.append_castAdd_natAdd
      right_inv := fun x => Prod.ext (funext fun i => Fin.append_left x.1 x.2 i)
        (funext fun i => Fin.append_right x.1 x.2 i) }
  unfold relationValue
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  apply Fintype.sum_equiv e
  intro c
  simp only [e, Equiv.coe_fn_mk, ite_zero_mul_ite_zero]
  have hmon : EdgeData.monomial c =
      EdgeData.monomial (c ∘ disjLeft p q) * EdgeData.monomial (c ∘ disjRight p q) := by
    unfold EdgeData.monomial
    exact Fin.prod_univ_add (fun u => MvPolynomial.X (c u))
  rw [hmon]
  exact if_congr (hvalid c) rfl rfl

theorem strictOrderEnumerator_glue (A : Orientation L) (B : Orientation R) (m : ℕ) :
    G.edgeData.strictOrderEnumerator (h.glue A B).val m =
      L.edgeData.strictOrderEnumerator A.val m * R.edgeData.strictOrderEnumerator B.val m := by
  rw [← relationValue_selected, ← relationValue_selected, ← relationValue_selected]
  apply relationValue_disj
  intro c
  constructor
  · intro hc
    exact ⟨fun x y hxy => hc _ _ ((h.glue_selected_left A B x y).mpr hxy),
      fun x y hxy => hc _ _ ((h.glue_selected_right A B x y).mpr hxy)⟩
  · rintro ⟨hl, hr⟩ u v huv
    rcases (h.glue_selected A B u v).mp huv with ⟨x, y, rfl, rfl, hxy⟩ | ⟨x, y, rfl, rfl, hxy⟩
    · exact hl x y hxy
    · exact hr x y hxy

theorem evalElementary_hrvMonomial_glue (A : Orientation L) (B : Orientation R) (m : ℕ) :
    evalElementary m (h.glue A B).hrvMonomial =
      evalElementary m A.hrvMonomial * evalElementary m B.hrvMonomial := by
  have hrel {n' : ℕ} {E : Diagram n'} (θ : Orientation E) (v : Fin n') :
      evalElementary m θ.hrvMonomial = relationValue (fibreRelation θ.hrv) m := by
    rw [← sum_markedE θ v m]
    exact sum_markedRelationValue _ _ _
  rw [hrel (h.glue A B) ⟨0, G.area.positive⟩,
    hrel A ⟨0, L.area.positive⟩, hrel B ⟨0, R.area.positive⟩]
  apply relationValue_disj
  intro c
  constructor
  · intro hc
    refine ⟨fun x y hxy => hc _ _ ⟨(disjLeft p q).strictMono hxy.1, ?_⟩,
      fun x y hxy => hc _ _ ⟨(disjRight p q).strictMono hxy.1, ?_⟩⟩
    · rw [h.hrv_glue_left, h.hrv_glue_left, hxy.2]
    · rw [h.hrv_glue_right, h.hrv_glue_right, hxy.2]
  · rintro ⟨hl, hr⟩ u v ⟨huv, hH⟩
    by_cases hu : u.val < p
    · obtain ⟨x, rfl⟩ := (exists_disjLeft_iff u).mpr hu
      by_cases hv : v.val < p
      · obtain ⟨y, rfl⟩ := (exists_disjLeft_iff v).mpr hv
        rw [h.hrv_glue_left, h.hrv_glue_left] at hH
        exact hl x y ⟨(disjLeft p q).lt_iff_lt.mp huv, (disjLeft p q).injective hH⟩
      · obtain ⟨y, rfl⟩ := (exists_disjRight_iff v).mpr (by lia)
        rw [h.hrv_glue_left, h.hrv_glue_right] at hH
        exact (disjLeft_ne_disjRight _ _ hH).elim
    · obtain ⟨x, rfl⟩ := (exists_disjRight_iff u).mpr (by lia)
      have hv : p ≤ v.val := by
        have : (disjRight p q x).val < v.val := huv
        simp only [disjRight_val] at this
        lia
      obtain ⟨y, rfl⟩ := (exists_disjRight_iff v).mpr hv
      rw [h.hrv_glue_right, h.hrv_glue_right] at hH
      exact hr x y ⟨(disjRight p q).lt_iff_lt.mp huv, (disjRight p q).injective hH⟩

/-- **Disjoint factorization of the strict-coloring value.** -/
theorem componentStrictEnumerator_glue (A : Orientation L) (B : Orientation R) (m : ℕ) :
    componentStrictEnumerator G (h.glue A B) m =
      componentStrictEnumerator L A m * componentStrictEnumerator R B m := by
  unfold componentStrictEnumerator
  rw [h.sum_flipComponent_glue (fun η => G.edgeData.strictOrderEnumerator η.val m),
    Finset.sum_mul_sum]
  simp only [h.strictOrderEnumerator_glue]

/-- **Disjoint factorization of the HRV value.** -/
theorem evalElementary_componentHRV_glue (A : Orientation L) (B : Orientation R) (m : ℕ) :
    evalElementary m (componentHRV G (h.glue A B)) =
      evalElementary m (componentHRV L A) * evalElementary m (componentHRV R B) := by
  unfold componentHRV
  rw [map_sum, map_sum, map_sum, h.sum_flipComponent_glue
    (fun η => evalElementary m η.hrvMonomial), Finset.sum_mul_sum]
  simp only [h.evalElementary_hrvMonomial_glue]

end IsDisjointUnion

/-! ### The two sides of a cut -/

section Cut

variable {p' q' : ℕ} {D : Diagram (p' + 1 + (q' + 1))} (hD : Forward D)

include hD in
/-- A forward diagram with no natural edge crossing `p` is the disjoint union of its
two induced sides. -/
theorem isDisjointUnion_induced
    (hcut : ∀ e : Edge D.area, e.tail.val < p' + 1 → e.head.val < p' + 1) :
    IsDisjointUnion D (inducedDiagram hD (disjLeft (p' + 1) (q' + 1)))
      (inducedDiagram hD (disjRight (p' + 1) (q' + 1))) := by
  have split (u v) (huv : naturalRel D u v) :
      (∃ a b, disjLeft (p' + 1) (q' + 1) a = u ∧ disjLeft (p' + 1) (q' + 1) b = v) ∨
        (∃ a b, disjRight (p' + 1) (q' + 1) a = u ∧ disjRight (p' + 1) (q' + 1) b = v) := by
    obtain ⟨e, rfl, rfl⟩ := huv
    by_cases hu : e.tail.val < p' + 1
    · obtain ⟨a, ha⟩ := (exists_disjLeft_iff e.tail).mpr hu
      obtain ⟨b, hb⟩ := (exists_disjLeft_iff e.head).mpr (hcut e hu)
      exact Or.inl ⟨a, b, ha, hb⟩
    · have hlt : e.tail.val < e.head.val := hD e
      obtain ⟨a, ha⟩ := (exists_disjRight_iff e.tail).mpr (by lia)
      obtain ⟨b, hb⟩ := (exists_disjRight_iff e.head).mpr (by lia)
      exact Or.inr ⟨a, b, ha, hb⟩
  refine
    { forwardL := inducedDiagram_forward hD _
      forwardR := inducedDiagram_forward hD _
      natural := ?_
      strict := ?_ }
  · intro u v
    constructor
    · intro huv
      rcases split u v huv with ⟨a, b, rfl, rfl⟩ | ⟨a, b, rfl, rfl⟩
      · exact Or.inl ⟨a, b, rfl, rfl, (inducedDiagram_naturalEdge_iff hD _ a b).mpr huv⟩
      · exact Or.inr ⟨a, b, rfl, rfl, (inducedDiagram_naturalEdge_iff hD _ a b).mpr huv⟩
    · rintro (⟨a, b, rfl, rfl, hab⟩ | ⟨a, b, rfl, rfl, hab⟩)
      · exact (inducedDiagram_naturalEdge_iff hD _ a b).mp hab
      · exact (inducedDiagram_naturalEdge_iff hD _ a b).mp hab
  · intro u v
    constructor
    · intro huv
      rcases split u v (naturalRel_of_strictRel huv) with
        ⟨a, b, rfl, rfl⟩ | ⟨a, b, rfl, rfl⟩
      · exact Or.inl ⟨a, b, rfl, rfl, (inducedDiagram_strictEndpoint_iff hD _ a b).mpr huv⟩
      · exact Or.inr ⟨a, b, rfl, rfl, (inducedDiagram_strictEndpoint_iff hD _ a b).mpr huv⟩
    · rintro (⟨a, b, rfl, rfl, hab⟩ | ⟨a, b, rfl, rfl, hab⟩)
      · exact (inducedDiagram_strictEndpoint_iff hD _ a b).mp hab
      · exact (inducedDiagram_strictEndpoint_iff hD _ a b).mp hab

end Cut

end

end VerticalStripLLT.Circular.DiagramProof
