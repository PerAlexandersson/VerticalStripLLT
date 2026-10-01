import VerticalStripLLT.Components.DiagramProof.InducedRestriction
import VerticalStripLLT.Components.DiagramProof.NaturalRelations
import VerticalStripLLT.Components.DiagramProof.InducedDecorations

/-!
# Two ordinary diagrams meeting at one endpoint

The left factor occupies the vertices `0, …, p` and the right factor the
vertices `p, …, p+q`; they share exactly the vertex `p`. A natural edge of
the union belongs to exactly one factor, and strict edges are inherited
exactly. `IsRightAttachment G L R` records this edge correspondence for an
arbitrary forward diagram `G`. It holds for the constructed union
`attachDiagram` and for the two induced sides of a diagram with a cut at `p`.

Restriction to the two sides and selected union are inverse maps on actual
orientations; they preserve the full selected relations, including the
strict edges.
-/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {n p q : ℕ}

/-! ### Vertex embeddings -/

/-- The left factor occupies the first `p+1` vertices. -/
def attachLeft (p q : ℕ) : Fin (p + 1) ↪o Fin (p + q + 1) :=
  OrderEmbedding.ofStrictMono (fun i => ⟨i.val, by have := i.isLt; lia⟩)
    (fun a b h => by
      have h' : a.val < b.val := h
      change a.val < b.val
      exact h')

/-- The right factor occupies the last `q+1` vertices, starting at `p`. -/
def attachRight (p q : ℕ) : Fin (q + 1) ↪o Fin (p + q + 1) :=
  OrderEmbedding.ofStrictMono (fun j => ⟨p + j.val, by have := j.isLt; lia⟩)
    (fun a b h => by
      have h' : a.val < b.val := h
      change p + a.val < p + b.val
      lia)

@[simp]
theorem attachLeft_val (i : Fin (p + 1)) : (attachLeft p q i).val = i.val := rfl

@[simp]
theorem attachRight_val (j : Fin (q + 1)) : (attachRight p q j).val = p + j.val := rfl

/-- The two images meet exactly at the shared endpoint. -/
theorem attachLeft_last : attachLeft p q (Fin.last p) = attachRight p q 0 := by
  apply Fin.ext
  simp

theorem attachLeft_eq_attachRight_iff {a : Fin (p + 1)} {b : Fin (q + 1)} :
    attachLeft p q a = attachRight p q b ↔ a = Fin.last p ∧ b = 0 := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    simp only [attachLeft_val, attachRight_val] at hv
    have ha := a.isLt
    constructor
    · apply Fin.ext
      simp only [Fin.val_last]
      lia
    · apply Fin.ext
      simp only [Fin.val_zero]
      lia
  · rintro ⟨rfl, rfl⟩
    exact attachLeft_last

theorem exists_attachLeft_iff (u : Fin (p + q + 1)) :
    (∃ a, attachLeft p q a = u) ↔ u.val ≤ p := by
  constructor
  · rintro ⟨a, rfl⟩
    have := a.isLt
    simp only [attachLeft_val]
    lia
  · intro hu
    exact ⟨⟨u.val, by lia⟩, Fin.ext rfl⟩

theorem exists_attachRight_iff (u : Fin (p + q + 1)) :
    (∃ b, attachRight p q b = u) ↔ p ≤ u.val := by
  constructor
  · rintro ⟨b, rfl⟩
    simp only [attachRight_val]
    lia
  · intro hu
    refine ⟨⟨u.val - p, by have := u.isLt; lia⟩, Fin.ext ?_⟩
    simp only [attachRight_val]
    lia

theorem attachLeft_convex : ConvexImage (attachLeft p q) := by
  intro u v z _ hzv
  apply (exists_attachLeft_iff z).mpr
  have hv := (exists_attachLeft_iff (attachLeft p q v)).mp ⟨v, rfl⟩
  have hzv' : z.val ≤ (attachLeft p q v).val := hzv
  lia

theorem attachRight_convex : ConvexImage (attachRight p q) := by
  intro u v z huz _
  apply (exists_attachRight_iff z).mpr
  have hu := (exists_attachRight_iff (attachRight p q u)).mp ⟨u, rfl⟩
  have huz' : (attachRight p q u).val ≤ z.val := huz
  lia

/-! ### Unions of relations on the two sides -/

/-- A relation on the union holding exactly on the embedded pairs of its two sides. -/
def attachUnion (X : Fin (p + 1) → Fin (p + 1) → Prop)
    (Y : Fin (q + 1) → Fin (q + 1) → Prop) (u v : Fin (p + q + 1)) : Prop :=
  (∃ a b, attachLeft p q a = u ∧ attachLeft p q b = v ∧ X a b) ∨
    (∃ a b, attachRight p q a = u ∧ attachRight p q b = v ∧ Y a b)

variable {X X' : Fin (p + 1) → Fin (p + 1) → Prop}
  {Y Y' : Fin (q + 1) → Fin (q + 1) → Prop}

theorem attachUnion_left (hY : ∀ b, ¬ Y b b) (a b : Fin (p + 1)) :
    attachUnion X Y (attachLeft p q a) (attachLeft p q b) ↔ X a b := by
  constructor
  · rintro (⟨a', b', ha, hb, h⟩ | ⟨a', b', ha, hb, h⟩)
    · rwa [← (attachLeft p q).injective ha, ← (attachLeft p q).injective hb]
    · obtain ⟨-, rfl⟩ := attachLeft_eq_attachRight_iff.mp ha.symm
      obtain ⟨-, rfl⟩ := attachLeft_eq_attachRight_iff.mp hb.symm
      exact (hY _ h).elim
  · intro h
    exact Or.inl ⟨a, b, rfl, rfl, h⟩

theorem attachUnion_right (hX : ∀ a, ¬ X a a) (a b : Fin (q + 1)) :
    attachUnion X Y (attachRight p q a) (attachRight p q b) ↔ Y a b := by
  constructor
  · rintro (⟨a', b', ha, hb, h⟩ | ⟨a', b', ha, hb, h⟩)
    · obtain ⟨rfl, -⟩ := attachLeft_eq_attachRight_iff.mp ha
      obtain ⟨rfl, -⟩ := attachLeft_eq_attachRight_iff.mp hb
      exact (hX _ h).elim
    · rwa [← (attachRight p q).injective ha, ← (attachRight p q).injective hb]
  · intro h
    exact Or.inr ⟨a, b, rfl, rfl, h⟩

theorem attachUnion_mono (hX : ∀ a b, X a b → X' a b) (hY : ∀ a b, Y a b → Y' a b)
    {u v : Fin (p + q + 1)} (h : attachUnion X Y u v) : attachUnion X' Y' u v := by
  rcases h with ⟨a, b, ha, hb, h⟩ | ⟨a, b, ha, hb, h⟩
  · exact Or.inl ⟨a, b, ha, hb, hX a b h⟩
  · exact Or.inr ⟨a, b, ha, hb, hY a b h⟩

theorem attachUnion_forward (hX : ∀ a b, X a b → a < b) (hY : ∀ a b, Y a b → a < b)
    {u v : Fin (p + q + 1)} (h : attachUnion X Y u v) : u < v := by
  rcases h with ⟨a, b, rfl, rfl, h⟩ | ⟨a, b, rfl, rfl, h⟩
  · exact (attachLeft p q).strictMono (hX a b h)
  · exact (attachRight p q).strictMono (hY a b h)

/-- No pair of the union crosses the shared vertex. -/
theorem attachUnion_cut {u v : Fin (p + q + 1)} (h : attachUnion X Y u v)
    (hu : u.val < p) : v.val ≤ p := by
  rcases h with ⟨a, b, -, rfl, -⟩ | ⟨a, b, rfl, -, -⟩
  · exact (exists_attachLeft_iff _).mp ⟨b, rfl⟩
  · simp only [attachRight_val] at hu
    lia

/-! ### The attachment predicate -/

/-- `G` is the union of `L` on `0..p` and `R` on `p..p+q`, sharing only `p`.
Its natural and strict edges are exactly those of the two factors. -/
structure IsRightAttachment (G : Diagram (p + q + 1)) (L : Diagram (p + 1))
    (R : Diagram (q + 1)) : Prop where
  forwardL : Forward L
  forwardR : Forward R
  natural : ∀ u v, naturalRel G u v ↔ attachUnion (naturalRel L) (naturalRel R) u v
  strict : ∀ u v, strictRel G u v ↔ attachUnion (strictRel L) (strictRel R) u v

namespace IsRightAttachment

variable {G : Diagram (p + q + 1)} {L : Diagram (p + 1)} {R : Diagram (q + 1)}
  (h : IsRightAttachment G L R)

include h

theorem naturalL_irrefl (a : Fin (p + 1)) : ¬ naturalRel L a a :=
  fun ha => lt_irrefl a (naturalRel_forward h.forwardL ha)

theorem naturalR_irrefl (b : Fin (q + 1)) : ¬ naturalRel R b b :=
  fun hb => lt_irrefl b (naturalRel_forward h.forwardR hb)

theorem forward : Forward G := by
  intro e
  exact attachUnion_forward (fun _ _ => naturalRel_forward h.forwardL)
    (fun _ _ => naturalRel_forward h.forwardR) ((h.natural _ _).mp ⟨e, rfl, rfl⟩)

theorem natural_left (a b : Fin (p + 1)) :
    naturalRel G (attachLeft p q a) (attachLeft p q b) ↔ naturalRel L a b :=
  (h.natural _ _).trans (attachUnion_left h.naturalR_irrefl a b)

theorem natural_right (a b : Fin (q + 1)) :
    naturalRel G (attachRight p q a) (attachRight p q b) ↔ naturalRel R a b :=
  (h.natural _ _).trans (attachUnion_right h.naturalL_irrefl a b)

theorem strict_left (a b : Fin (p + 1)) :
    strictRel G (attachLeft p q a) (attachLeft p q b) ↔ strictRel L a b :=
  (h.strict _ _).trans (attachUnion_left
    (fun b hb => h.naturalR_irrefl b (naturalRel_of_strictRel hb)) a b)

theorem strict_right (a b : Fin (q + 1)) :
    strictRel G (attachRight p q a) (attachRight p q b) ↔ strictRel R a b :=
  (h.strict _ _).trans (attachUnion_right
    (fun a ha => h.naturalL_irrefl a (naturalRel_of_strictRel ha)) a b)

/-- Every natural edge of the union stays on one side of the shared vertex. -/
theorem natural_cut (e : Edge G.area) (he : e.tail.val < p) : e.head.val ≤ p :=
  attachUnion_cut ((h.natural _ _).mp ⟨e, rfl, rfl⟩) he

/-! ### Restriction and selected union -/

omit h in
private theorem selected_irrefl {D : Diagram n} (hD : Forward D) (θ : Orientation D)
    (u : Fin n) : ¬ D.edgeData.selected θ.val u u :=
  fun hu => lt_irrefl u (θ.selected_lt_of_forward hD hu)

/-- Restrict an actual state of the union to the left factor. -/
def restrictLeft (θ : Orientation G) : Orientation L :=
  inducedRestrict h.forwardL (attachLeft p q) (fun u v => (h.natural_left u v).symm)
    (fun u v => (h.strict_left u v).symm) θ

/-- Restrict an actual state of the union to the right factor. -/
def restrictRight (θ : Orientation G) : Orientation R :=
  inducedRestrict h.forwardR (attachRight p q) (fun u v => (h.natural_right u v).symm)
    (fun u v => (h.strict_right u v).symm) θ

@[simp]
theorem restrictLeft_selected (θ : Orientation G) (a b : Fin (p + 1)) :
    L.edgeData.selected (h.restrictLeft θ).val a b ↔
      G.edgeData.selected θ.val (attachLeft p q a) (attachLeft p q b) :=
  inducedRestrict_selected ..

@[simp]
theorem restrictRight_selected (θ : Orientation G) (a b : Fin (q + 1)) :
    R.edgeData.selected (h.restrictRight θ).val a b ↔
      G.edgeData.selected θ.val (attachRight p q a) (attachRight p q b) :=
  inducedRestrict_selected ..

/-- The selected union of one state on each side, as an actual state of `G`. -/
def glue (A : Orientation L) (B : Orientation R) : Orientation G :=
  ofSelectedRelation h.forward
    (attachUnion (L.edgeData.selected A.val) (R.edgeData.selected B.val))
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

theorem glue_selected (A : Orientation L) (B : Orientation R) (u v : Fin (p + q + 1)) :
    G.edgeData.selected (h.glue A B).val u v ↔
      attachUnion (L.edgeData.selected A.val) (R.edgeData.selected B.val) u v :=
  selected_ofSelectedRelation ..

@[simp]
theorem glue_selected_left (A : Orientation L) (B : Orientation R) (a b : Fin (p + 1)) :
    G.edgeData.selected (h.glue A B).val (attachLeft p q a) (attachLeft p q b) ↔
      L.edgeData.selected A.val a b :=
  (h.glue_selected A B _ _).trans
    (attachUnion_left (selected_irrefl h.forwardR B) a b)

@[simp]
theorem glue_selected_right (A : Orientation L) (B : Orientation R) (a b : Fin (q + 1)) :
    G.edgeData.selected (h.glue A B).val (attachRight p q a) (attachRight p q b) ↔
      R.edgeData.selected B.val a b :=
  (h.glue_selected A B _ _).trans
    (attachUnion_right (selected_irrefl h.forwardL A) a b)

/-- Every selected pair of the union is a selected pair of one restriction. -/
theorem selected_iff (θ : Orientation G) (u v : Fin (p + q + 1)) :
    G.edgeData.selected θ.val u v ↔
      attachUnion (L.edgeData.selected (h.restrictLeft θ).val)
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

@[simp]
theorem restrictLeft_glue (A : Orientation L) (B : Orientation R) :
    h.restrictLeft (h.glue A B) = A := by
  apply orientation_eq_of_selected_iff
  intro a b
  rw [restrictLeft_selected, glue_selected_left]

@[simp]
theorem restrictRight_glue (A : Orientation L) (B : Orientation R) :
    h.restrictRight (h.glue A B) = B := by
  apply orientation_eq_of_selected_iff
  intro a b
  rw [restrictRight_selected, glue_selected_right]

@[simp]
theorem glue_restrict (θ : Orientation G) :
    h.glue (h.restrictLeft θ) (h.restrictRight θ) = θ := by
  apply orientation_eq_of_selected_iff
  intro u v
  rw [glue_selected, selected_iff]

theorem glue_inj {A A' : Orientation L} {B B' : Orientation R}
    (heq : h.glue A B = h.glue A' B') : A = A' ∧ B = B' := by
  constructor
  · simpa only [restrictLeft_glue] using congrArg h.restrictLeft heq
  · simpa only [restrictRight_glue] using congrArg h.restrictRight heq

/-- Restriction and selected union are inverse bijections of actual states. -/
def stateEquiv : Orientation L × Orientation R ≃ Orientation G where
  toFun x := h.glue x.1 x.2
  invFun θ := (h.restrictLeft θ, h.restrictRight θ)
  left_inv x := Prod.ext (h.restrictLeft_glue x.1 x.2) (h.restrictRight_glue x.1 x.2)
  right_inv θ := h.glue_restrict θ

@[simp]
theorem stateEquiv_apply (x : Orientation L × Orientation R) :
    h.stateEquiv x = h.glue x.1 x.2 := rfl

end IsRightAttachment

/-! ### The constructed union -/

section Construction

variable (L : Diagram (p + 1)) (R : Diagram (q + 1)) (hL : Forward L) (hR : Forward R)

include hL hR in
theorem attachNatural_interval {u v w : Fin (p + q + 1)}
    (h : attachUnion (naturalRel L) (naturalRel R) u w) (huv : u < v) (hvw : v < w) :
    attachUnion (naturalRel L) (naturalRel R) u v ∧
      attachUnion (naturalRel L) (naturalRel R) v w := by
  rcases h with ⟨a, c, rfl, rfl, hac⟩ | ⟨a, c, rfl, rfl, hac⟩
  · obtain ⟨b, rfl⟩ := (exists_attachLeft_iff v).mpr (by
      have hc := (exists_attachLeft_iff (attachLeft p q c)).mp ⟨c, rfl⟩
      have hvw' : v.val < (attachLeft p q c).val := hvw
      lia)
    obtain ⟨hab, hbc⟩ := naturalRel_interval hL hac
      ((attachLeft p q).lt_iff_lt.mp huv) ((attachLeft p q).lt_iff_lt.mp hvw)
    exact ⟨Or.inl ⟨a, b, rfl, rfl, hab⟩, Or.inl ⟨b, c, rfl, rfl, hbc⟩⟩
  · obtain ⟨b, rfl⟩ := (exists_attachRight_iff v).mpr (by
      have ha := (exists_attachRight_iff (attachRight p q a)).mp ⟨a, rfl⟩
      have huv' : (attachRight p q a).val < v.val := huv
      lia)
    obtain ⟨hab, hbc⟩ := naturalRel_interval hR hac
      ((attachRight p q).lt_iff_lt.mp huv) ((attachRight p q).lt_iff_lt.mp hvw)
    exact ⟨Or.inr ⟨a, b, rfl, rfl, hab⟩, Or.inr ⟨b, c, rfl, rfl, hbc⟩⟩

/-- The natural union, before adding its strict markings. -/
def attachUndecorated : Diagram (p + q + 1) :=
  Diagram.ofIntervalRelation (attachUnion (naturalRel L) (naturalRel R))
    (fun h huv hvw => attachNatural_interval L R hL hR h huv hvw) (Nat.succ_pos _)

theorem attachUndecorated_naturalRel (u v : Fin (p + q + 1)) :
    naturalRel (attachUndecorated L R hL hR) u v ↔
      attachUnion (naturalRel L) (naturalRel R) u v :=
  Diagram.ofIntervalRelation_naturalEdge_iff _
    (fun h => attachUnion_forward (fun _ _ => naturalRel_forward hL)
      (fun _ _ => naturalRel_forward hR) h) _ _ u v

theorem attachUndecorated_forward : Forward (attachUndecorated L R hL hR) := by
  intro e
  exact attachUnion_forward (fun _ _ => naturalRel_forward hL)
    (fun _ _ => naturalRel_forward hR)
    ((attachUndecorated_naturalRel L R hL hR _ _).mp ⟨e, rfl, rfl⟩)

/-- A strict corner of either factor is still a maximal natural interval of the union. -/
theorem attach_isCorner (e : Edge (attachUndecorated L R hL hR).area)
    (he : attachUnion (strictRel L) (strictRel R) e.tail e.head) : IsCorner e := by
  have hU := attachUndecorated_forward L R hL hR
  apply (isCorner_iff_maximal hU e).mpr
  intro g hgt hgh
  have hg := (attachUndecorated_naturalRel L R hL hR _ _).mp ⟨g, rfl, rfl⟩
  have hgfwd : g.tail < g.head := hU g
  apply (attachUndecorated L R hL hR).endpointEmbedding.injective
  rcases he with ⟨a, b, ha, hb, f, hf, rfl, rfl⟩ | ⟨a, b, ha, hb, f, hf, rfl, rfl⟩
  · have hmax := (isCorner_iff_maximal hL f).mp (L.strict_corner f hf)
    have hfb : f.head.val ≤ p := by have := f.head.isLt; lia
    rcases hg with ⟨a', b', ha', hb', g', rfl, rfl⟩ | ⟨a', b', ha', hb', -⟩
    · have hgf := hmax g'
        ((attachLeft p q).le_iff_le.mp (by rw [ha', ha]; exact hgt))
        ((attachLeft p q).le_iff_le.mp (by rw [hb', hb]; exact hgh))
      subst hgf
      exact Prod.ext (ha'.symm.trans ha) (hb'.symm.trans hb)
    · exfalso
      have h1 : (g.tail).val ≤ (e.tail).val := hgt
      rw [← ha', ← ha] at h1
      simp only [attachLeft_val, attachRight_val] at h1
      have hft : f.tail < f.head := hL f
      have hft' : f.tail.val < f.head.val := hft
      lia
  · have hmax := (isCorner_iff_maximal hR f).mp (R.strict_corner f hf)
    rcases hg with ⟨a', b', ha', hb', -⟩ | ⟨a', b', ha', hb', g', rfl, rfl⟩
    · exfalso
      have h1 : (e.head).val ≤ (g.head).val := hgh
      rw [← hb', ← hb] at h1
      simp only [attachLeft_val, attachRight_val] at h1
      have hft : f.tail < f.head := hR f
      have hft' : f.tail.val < f.head.val := hft
      have := b'.isLt
      lia
    · have hgf := hmax g'
        ((attachRight p q).le_iff_le.mp (by rw [ha', ha]; exact hgt))
        ((attachRight p q).le_iff_le.mp (by rw [hb', hb]; exact hgh))
      subst hgf
      exact Prod.ext (ha'.symm.trans ha) (hb'.symm.trans hb)

/-- The ordinary diagram obtained by gluing `R` to the right endpoint of `L`. -/
def attachDiagram : Diagram (p + q + 1) where
  area := (attachUndecorated L R hL hR).area
  strict := Finset.univ.filter fun e =>
    attachUnion (strictRel L) (strictRel R) e.tail e.head
  strict_corner := by
    intro e he
    exact attach_isCorner L R hL hR e (Finset.mem_filter.mp he).2

theorem attachDiagram_isRightAttachment :
    IsRightAttachment (attachDiagram L R hL hR) L R where
  forwardL := hL
  forwardR := hR
  natural := attachUndecorated_naturalRel L R hL hR
  strict := by
    intro u v
    constructor
    · rintro ⟨e, he, rfl, rfl⟩
      exact (Finset.mem_filter.mp he).2
    · intro huv
      obtain ⟨e, rfl, rfl⟩ := (attachUndecorated_naturalRel L R hL hR u v).mpr
        (attachUnion_mono (fun _ _ => naturalRel_of_strictRel)
          (fun _ _ => naturalRel_of_strictRel) huv)
      exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv⟩, rfl, rfl⟩

end Construction

/-! ### The two induced sides of a diagram with a cut -/

section Cut

variable {D : Diagram (p + q + 1)} (hD : Forward D)

include hD in
/-- A forward diagram with no natural edge crossing `p` is the union of its two
induced sides, with their exactly inherited strict edges. -/
theorem isRightAttachment_induced
    (hcut : ∀ e : Edge D.area, e.tail.val < p → e.head.val ≤ p) :
    IsRightAttachment D (inducedDiagram hD (attachLeft p q))
      (inducedDiagram hD (attachRight p q)) := by
  have split (u v : Fin (p + q + 1)) (huv : naturalRel D u v) :
      (∃ a b, attachLeft p q a = u ∧ attachLeft p q b = v) ∨
        (∃ a b, attachRight p q a = u ∧ attachRight p q b = v) := by
    obtain ⟨e, rfl, rfl⟩ := huv
    by_cases hu : e.tail.val < p
    · have hv := hcut e hu
      obtain ⟨a, ha⟩ := (exists_attachLeft_iff e.tail).mpr hu.le
      obtain ⟨b, hb⟩ := (exists_attachLeft_iff e.head).mpr hv
      exact Or.inl ⟨a, b, ha, hb⟩
    · have hlt : e.tail.val < e.head.val := hD e
      obtain ⟨a, ha⟩ := (exists_attachRight_iff e.tail).mpr (by lia)
      obtain ⟨b, hb⟩ := (exists_attachRight_iff e.head).mpr (by lia)
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
