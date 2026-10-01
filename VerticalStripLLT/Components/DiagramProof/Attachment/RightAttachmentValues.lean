import VerticalStripLLT.Components.DiagramProof.Attachment.RightAttachmentPaths
import VerticalStripLLT.Components.DiagramProof.Foundation.MarkedValues

/-!
# Values of a right attachment

A left vertex whose HRV is below the shared vertex keeps its HRV; a left
vertex reaching the shared vertex acquires the right HRV of that vertex;
right vertices keep their right HRV. Thus exactly the left fibre ending at
the shared vertex and the right fibre beginning there merge, and their
increasing chains concatenate.

The attachment factor uses the coloring weight with the shared vertex
omitted: a product over the other vertices, not division by a variable.
For a fixed color at the shared vertex, strictly increasing colorings of
the union are exactly pairs of colorings agreeing there.
-/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical
open scoped BigOperators

noncomputable section

variable {n p q : ℕ}

/-! ### Endpoint-omitted values -/

/-- Colorings increasing on `R`, with `v` colored `β` and its weight omitted. -/
def omittedRelationValue (R : Fin n → Fin n → Prop) (v : Fin n) (m : ℕ) (β : Fin m) :
    XPoly m :=
  ∑ c : Fin n → Fin m,
    if c v = β ∧ ∀ u w, R u w → c u < c w then
      ∏ u ∈ Finset.univ.erase v, MvPolynomial.X (c u) else 0

variable {D : Diagram n}

/-- The right-marked K value with the weight of the marked vertex `v` omitted. -/
def omittedMarkedK (θ : Orientation D) (v : Fin n) (m : ℕ) (β : Fin m) : XPoly m :=
  omittedRelationValue (D.edgeData.selected θ.val) v m β

/-- The right-marked E value with the weight of the marked vertex `v` omitted. -/
def omittedMarkedE (θ : Orientation D) (v : Fin n) (m : ℕ) (β : Fin m) : XPoly m :=
  omittedRelationValue (fibreRelation θ.hrv) v m β

/-- `omittedMarkedK` summed over the whole component of `θ`. -/
def componentOmittedMarkedK (θ : Orientation D) (v : Fin n) (m : ℕ) (β : Fin m) :
    XPoly m :=
  ∑ η ∈ flipComponent D θ, omittedMarkedK η v m β

/-- `omittedMarkedE` summed over the whole component of `θ`. -/
def componentOmittedMarkedE (θ : Orientation D) (v : Fin n) (m : ℕ) (β : Fin m) :
    XPoly m :=
  ∑ η ∈ flipComponent D θ, omittedMarkedE η v m β

/-- A one-vertex attachment has omitted weight one at every fixed color. -/
theorem omittedRelationValue_one (R : Fin 1 → Fin 1 → Prop)
    (hR : ∀ u w, R u w → u < w) (m : ℕ) (β : Fin m) :
    omittedRelationValue R 0 m β = 1 := by
  have hR0 (u w : Fin 1) : ¬ R u w := fun huw => by
    rw [Subsingleton.elim u w] at huw
    exact lt_irrefl w (hR w w huw)
  unfold omittedRelationValue
  rw [Fintype.sum_eq_single (fun _ => β)]
  · simp [hR0]
  · intro c hc
    have : c 0 ≠ β := fun h0 => hc (funext fun u => by rw [Fin.fin_one_eq_zero u, h0])
    simp [this]

/-- With an empty alphabet every unmarked value on a nonempty vertex set vanishes. -/
theorem relationValue_zero_alphabet (R : Fin (n + 1) → Fin (n + 1) → Prop) :
    relationValue R 0 = 0 := by
  unfold relationValue
  have : IsEmpty (Fin (n + 1) → Fin 0) := ⟨fun c => (c 0).elim0⟩
  simp

/-! ### Splitting a product over the two sides -/

@[to_additive]
theorem prod_attach_split {M : Type*} [CommMonoid M] (f : Fin (p + q + 1) → M) :
    ∏ u, f u = (∏ a, f (attachLeft p q a)) *
      ∏ b ∈ Finset.univ.erase 0, f (attachRight p q b) := by
  have hdisj : Disjoint (Finset.univ.map (attachLeft p q).toEmbedding)
      ((Finset.univ.erase (0 : Fin (q + 1))).map (attachRight p q).toEmbedding) := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨b, hb, hab⟩ := Finset.mem_map.mp hu'
    have hb0 : b ≠ 0 := Finset.ne_of_mem_erase hb
    have hab' : attachLeft p q a = attachRight p q b := hab.symm
    exact hb0 (attachLeft_eq_attachRight_iff.mp hab').2
  have hunion : Finset.univ.map (attachLeft p q).toEmbedding ∪
      (Finset.univ.erase (0 : Fin (q + 1))).map (attachRight p q).toEmbedding =
        Finset.univ := by
    ext u
    simp only [Finset.mem_union, Finset.mem_map, Finset.mem_univ, true_and,
      Finset.mem_erase, and_true, iff_true]
    by_cases hu : u.val ≤ p
    · obtain ⟨a, ha⟩ := (exists_attachLeft_iff u).mpr hu
      exact Or.inl ⟨a, ha⟩
    · obtain ⟨b, hb⟩ := (exists_attachRight_iff u).mpr (by lia)
      refine Or.inr ⟨b, ?_, hb⟩
      rintro rfl
      apply hu
      rw [← hb]
      simp
  rw [← hunion, Finset.prod_union hdisj, Finset.prod_map, Finset.prod_map]
  rfl

/-! ### Gluing colorings -/

/-- Restrict a coloring of the union to its two sides. -/
def splitColoring {m : ℕ} (c : Fin (p + q + 1) → Fin m) :
    (Fin (p + 1) → Fin m) × (Fin (q + 1) → Fin m) :=
  (c ∘ attachLeft p q, c ∘ attachRight p q)

theorem splitColoring_injective {m : ℕ} :
    Function.Injective (splitColoring (p := p) (q := q) (m := m)) := by
  intro c c' hc
  obtain ⟨hl, hr⟩ := Prod.mk.inj hc
  funext u
  by_cases hu : u.val ≤ p
  · obtain ⟨a, rfl⟩ := (exists_attachLeft_iff u).mpr hu
    exact congrFun hl a
  · obtain ⟨b, rfl⟩ := (exists_attachRight_iff u).mpr (by lia)
    exact congrFun hr b

/-- Two colorings agreeing at the shared vertex glue to a coloring of the union. -/
theorem exists_splitColoring {m : ℕ} (cL : Fin (p + 1) → Fin m)
    (cR : Fin (q + 1) → Fin m) (hc : cL (Fin.last p) = cR 0) :
    ∃ c, splitColoring c = (cL, cR) := by
  refine ⟨fun u => if hu : u.val ≤ p then cL ⟨u.val, by lia⟩
    else cR ⟨u.val - p, by have := u.isLt; lia⟩, Prod.ext ?_ ?_⟩
  · funext a
    have ha := a.isLt
    simp only [splitColoring, Function.comp_apply, attachLeft_val]
    rw [dite_eq_left (by lia)]
  · funext b
    simp only [splitColoring, Function.comp_apply, attachRight_val]
    by_cases hb : b = 0
    · subst hb
      rw [dite_eq_left (by simp), ← hc]
      exact congrArg _ (Fin.ext (by simp))
    · have hb' : 0 < b.val := Fin.pos_iff_ne_zero.mpr hb
      rw [dite_eq_right (by lia)]
      exact congrArg _ (Fin.ext (by simp))

theorem monomial_splitColoring {m : ℕ} (c : Fin (p + q + 1) → Fin m) :
    EdgeData.monomial c = EdgeData.monomial (c ∘ attachLeft p q) *
      ∏ b ∈ Finset.univ.erase 0, MvPolynomial.X (c (attachRight p q b)) :=
  prod_attach_split (fun u => MvPolynomial.X (c u))

/-- The fixed-color gluing formula for relations whose increasing colorings split
into the two sides. -/
theorem relationValue_attach {m : ℕ} (RG : Fin (p + q + 1) → Fin (p + q + 1) → Prop)
    (RL : Fin (p + 1) → Fin (p + 1) → Prop) (RR : Fin (q + 1) → Fin (q + 1) → Prop)
    (hvalid : ∀ c : Fin (p + q + 1) → Fin m,
      (∀ u v, RG u v → c u < c v) ↔
        (∀ x y, RL x y → c (attachLeft p q x) < c (attachLeft p q y)) ∧
          ∀ x y, RR x y → c (attachRight p q x) < c (attachRight p q y)) :
    relationValue RG m =
      ∑ β : Fin m, markedRelationValue RL (Fin.last p) m β *
        omittedRelationValue RR 0 m β := by
  let F : (Fin (p + 1) → Fin m) × (Fin (q + 1) → Fin m) → XPoly m := fun x =>
    if x.1 (Fin.last p) = x.2 0 ∧ (∀ u w, RL u w → x.1 u < x.1 w) ∧
        (∀ u w, RR u w → x.2 u < x.2 w) then
      EdgeData.monomial x.1 * ∏ b ∈ Finset.univ.erase 0, MvPolynomial.X (x.2 b)
    else 0
  have hright : ∑ β : Fin m, markedRelationValue RL (Fin.last p) m β *
      omittedRelationValue RR 0 m β = ∑ x, F x := by
    unfold markedRelationValue omittedRelationValue
    simp only [Finset.sum_mul_sum, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun cL _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun cR _ => ?_
    simp only [ite_zero_mul_ite_zero]
    rw [Finset.sum_eq_single (cL (Fin.last p))]
    · simp only [F]
      apply if_congr _ rfl rfl
      constructor
      · rintro ⟨⟨-, h1⟩, h2, h3⟩
        exact ⟨h2.symm, h1, h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨trivial, h2⟩, h1.symm, h3⟩
    · intro β _ hβ
      rw [ite_eq_right]
      rintro ⟨⟨h1, -⟩, -⟩
      exact hβ h1.symm
    · intro hβ
      exact absurd (Finset.mem_univ _) hβ
  rw [hright]
  unfold relationValue
  apply Fintype.sum_of_injective splitColoring splitColoring_injective
  · rintro ⟨cL, cR⟩ hx
    simp only [F]
    rw [ite_eq_right]
    rintro ⟨hc, -⟩
    obtain ⟨c, hcx⟩ := exists_splitColoring cL cR hc
    exact hx ⟨c, hcx⟩
  · intro c
    simp only [F, splitColoring, Function.comp_apply, attachLeft_last, true_and]
    rw [← monomial_splitColoring]
    by_cases hv : ∀ u v, RG u v → c u < c v
    · rw [ite_eq_left hv, ite_eq_left ((hvalid c).mp hv)]
    · rw [ite_eq_right hv, ite_eq_right (fun h => hv ((hvalid c).mpr h))]

namespace IsRightAttachment

variable {G : Diagram (p + q + 1)} {L : Diagram (p + 1)} {R : Diagram (q + 1)}
  (h : IsRightAttachment G L R)

include h

/-! ### Reachability through the shared vertex -/

theorem glue_cut (A : Orientation L) (B : Orientation R) {u v : Fin (p + q + 1)}
    (huv : G.edgeData.selected (h.glue A B).val u v) (hu : u.val < p) : v.val ≤ p :=
  attachUnion_cut ((h.glue_selected A B u v).mp huv) hu

/-- A forward path from the left side to the right side passes through `p`. -/
theorem reachable_through_shared (A : Orientation L) (B : Orientation R)
    {x z : Fin (p + q + 1)}
    (hxz : Relation.ReflTransGen (G.edgeData.selected (h.glue A B).val) x z)
    (hx : x.val ≤ p) (hz : p ≤ z.val) :
    Relation.ReflTransGen (G.edgeData.selected (h.glue A B).val) x
        (attachRight p q 0) ∧
      Relation.ReflTransGen (G.edgeData.selected (h.glue A B).val)
        (attachRight p q 0) z := by
  induction hxz with
  | refl =>
    have hx0 : x = attachRight p q 0 := Fin.ext (by
      simp only [attachRight_val, Fin.val_zero, add_zero]
      lia)
    subst hx0
    exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | @tail y z hxy hyz ih =>
    by_cases hy : p ≤ y.val
    · obtain ⟨h1, h2⟩ := ih hy
      exact ⟨h1, h2.tail hyz⟩
    · have hzp := h.glue_cut A B hyz (by lia)
      have hz0 : z = attachRight p q 0 := Fin.ext (by
        simp only [attachRight_val, Fin.val_zero, add_zero]
        lia)
      subst hz0
      exact ⟨hxy.tail hyz, Relation.ReflTransGen.refl⟩

theorem reachable_left_iff (A : Orientation L) (B : Orientation R) (x y : Fin (p + 1)) :
    Relation.ReflTransGen (G.edgeData.selected (h.glue A B).val)
        (attachLeft p q x) (attachLeft p q y) ↔
      Relation.ReflTransGen (L.edgeData.selected A.val) x y :=
  reachable_iff_of_convexImage (attachLeft p q) attachLeft_convex
    (fun {_ _} hs => (h.glue A B).selected_lt_of_forward h.forward hs)
    (fun a b => (h.glue_selected_left A B a b).symm) x y

theorem reachable_right_iff (A : Orientation L) (B : Orientation R) (x : Fin (q + 1))
    (z : Fin (p + q + 1)) :
    Relation.ReflTransGen (G.edgeData.selected (h.glue A B).val) (attachRight p q x) z ↔
      ∃ y, attachRight p q y = z ∧ Relation.ReflTransGen (R.edgeData.selected B.val) x y := by
  have hpaths := reachable_iff_of_convexImage (attachRight p q) attachRight_convex
    (fun {_ _} hs => (h.glue A B).selected_lt_of_forward h.forward hs)
    (fun a b => (h.glue_selected_right A B a b).symm)
  constructor
  · intro hxz
    have hle := reachable_le (fun {_ _} hs => (h.glue A B).selected_lt_of_forward h.forward hs)
      hxz
    obtain ⟨y, rfl⟩ := (exists_attachRight_iff z).mpr (by
      have := (exists_attachRight_iff (attachRight p q x)).mp ⟨x, rfl⟩
      have hle' : (attachRight p q x).val ≤ z.val := hle
      lia)
    exact ⟨y, rfl, (hpaths x y).mp hxz⟩
  · rintro ⟨y, rfl, hxy⟩
    exact (hpaths x y).mpr hxy

/-! ### The HRV fibre merger -/

omit h in
theorem hrv_eq_of_reachable_greatest {D : Diagram n} (hD : Forward D) (θ : Orientation D)
    {u x : Fin n} (hx : Relation.ReflTransGen (D.edgeData.selected θ.val) u x)
    (hmax : ∀ v, Relation.ReflTransGen (D.edgeData.selected θ.val) u v → v ≤ x) :
    θ.hrv u = x :=
  le_antisymm (hmax _ (θ.hrv_reachable u)) (θ.reachable_le_hrv_of_forward hD hx)

theorem hrv_last (A : Orientation L) : A.hrv (Fin.last p) = Fin.last p :=
  le_antisymm (Fin.le_last _) (A.reachable_le_hrv_of_forward h.forwardL
    Relation.ReflTransGen.refl)

theorem hrv_glue_right (A : Orientation L) (B : Orientation R) (y : Fin (q + 1)) :
    (h.glue A B).hrv (attachRight p q y) = attachRight p q (B.hrv y) := by
  apply hrv_eq_of_reachable_greatest h.forward
  · exact (h.reachable_right_iff A B y _).mpr ⟨_, rfl, B.hrv_reachable y⟩
  · intro v hv
    obtain ⟨y', rfl, hy'⟩ := (h.reachable_right_iff A B y v).mp hv
    exact (attachRight p q).le_iff_le.mpr (B.reachable_le_hrv_of_forward h.forwardR hy')

theorem hrv_glue_left (A : Orientation L) (B : Orientation R) (x : Fin (p + 1)) :
    (h.glue A B).hrv (attachLeft p q x) =
      if A.hrv x = Fin.last p then attachRight p q (B.hrv 0)
      else attachLeft p q (A.hrv x) := by
  split_ifs with hx
  · apply hrv_eq_of_reachable_greatest h.forward
    · have h1 := (h.reachable_left_iff A B x _).mpr (A.hrv_reachable x)
      rw [hx, attachLeft_last] at h1
      exact h1.trans ((h.reachable_right_iff A B 0 _).mpr ⟨_, rfl, B.hrv_reachable 0⟩)
    · intro v hv
      by_cases hvp : p ≤ v.val
      · have hx' : (attachLeft p q x).val ≤ p := (exists_attachLeft_iff _).mp ⟨x, rfl⟩
        obtain ⟨-, h2⟩ := h.reachable_through_shared A B hv hx' hvp
        obtain ⟨y', rfl, hy'⟩ := (h.reachable_right_iff A B 0 v).mp h2
        exact (attachRight p q).le_iff_le.mpr (B.reachable_le_hrv_of_forward h.forwardR hy')
      · change v.val ≤ p + (B.hrv 0).val
        lia
  · apply hrv_eq_of_reachable_greatest h.forward
    · exact (h.reachable_left_iff A B x _).mpr (A.hrv_reachable x)
    · intro v hv
      by_cases hvp : p ≤ v.val
      · exfalso
        have hx' : (attachLeft p q x).val ≤ p := (exists_attachLeft_iff _).mp ⟨x, rfl⟩
        obtain ⟨h1, -⟩ := h.reachable_through_shared A B hv hx' hvp
        rw [← attachLeft_last] at h1
        have hlast := A.reachable_le_hrv_of_forward h.forwardL
          ((h.reachable_left_iff A B x _).mp h1)
        exact hx (le_antisymm (Fin.le_last _) hlast)
      · obtain ⟨y, rfl⟩ := (exists_attachLeft_iff v).mpr (by lia)
        exact (attachLeft p q).le_iff_le.mpr
          (A.reachable_le_hrv_of_forward h.forwardL ((h.reachable_left_iff A B x y).mp hv))

theorem hrv_glue_left_eq_iff (A : Orientation L) (B : Orientation R) (x y : Fin (p + 1)) :
    (h.glue A B).hrv (attachLeft p q x) = (h.glue A B).hrv (attachLeft p q y) ↔
      A.hrv x = A.hrv y := by
  rw [h.hrv_glue_left, h.hrv_glue_left]
  have hne {s : Fin (p + 1)} (hs : A.hrv s ≠ Fin.last p) (t : Fin (q + 1)) :
      attachLeft p q (A.hrv s) ≠ attachRight p q t :=
    fun heq => hs (attachLeft_eq_attachRight_iff.mp heq).1
  split_ifs with hx hy hy
  · exact iff_of_true rfl (hx.trans hy.symm)
  · exact iff_of_false (fun heq => hne hy _ heq.symm) (fun heq => hy (heq.symm.trans hx))
  · exact iff_of_false (hne hx _) (fun heq => hx (heq.trans hy))
  · exact (attachLeft p q).injective.eq_iff

theorem hrv_glue_right_eq_iff (A : Orientation L) (B : Orientation R) (x y : Fin (q + 1)) :
    (h.glue A B).hrv (attachRight p q x) = (h.glue A B).hrv (attachRight p q y) ↔
      B.hrv x = B.hrv y := by
  rw [h.hrv_glue_right, h.hrv_glue_right]
  exact (attachRight p q).injective.eq_iff

/-- Increasing chains on the glued fibres are exactly pairs of increasing chains:
the two fibres at the shared vertex concatenate. -/
theorem fibre_glue_valid {m : ℕ} (A : Orientation L) (B : Orientation R)
    (c : Fin (p + q + 1) → Fin m) :
    (∀ u v, fibreRelation (h.glue A B).hrv u v → c u < c v) ↔
      (∀ x y, fibreRelation A.hrv x y → c (attachLeft p q x) < c (attachLeft p q y)) ∧
        ∀ x y, fibreRelation B.hrv x y →
          c (attachRight p q x) < c (attachRight p q y) := by
  constructor
  · intro hc
    exact ⟨fun x y hxy => hc _ _ ⟨(attachLeft p q).strictMono hxy.1,
        (h.hrv_glue_left_eq_iff A B x y).mpr hxy.2⟩,
      fun x y hxy => hc _ _ ⟨(attachRight p q).strictMono hxy.1,
        (h.hrv_glue_right_eq_iff A B x y).mpr hxy.2⟩⟩
  · rintro ⟨hl, hr⟩ u v ⟨huv, hH⟩
    have huv' : u.val < v.val := huv
    by_cases hv : v.val ≤ p
    · obtain ⟨x, rfl⟩ := (exists_attachLeft_iff u).mpr (by lia)
      obtain ⟨y, rfl⟩ := (exists_attachLeft_iff v).mpr hv
      exact hl x y ⟨(attachLeft p q).lt_iff_lt.mp huv,
        (h.hrv_glue_left_eq_iff A B x y).mp hH⟩
    by_cases hu : p ≤ u.val
    · obtain ⟨x, rfl⟩ := (exists_attachRight_iff u).mpr hu
      obtain ⟨y, rfl⟩ := (exists_attachRight_iff v).mpr (by lia)
      exact hr x y ⟨(attachRight p q).lt_iff_lt.mp huv,
        (h.hrv_glue_right_eq_iff A B x y).mp hH⟩
    obtain ⟨x, rfl⟩ := (exists_attachLeft_iff u).mpr (by lia)
    obtain ⟨y, rfl⟩ := (exists_attachRight_iff v).mpr (by lia)
    rw [h.hrv_glue_left, h.hrv_glue_right] at hH
    split_ifs at hH with hx
    · have hxl : x < Fin.last p := by
        change x.val < p
        simp only [attachLeft_val] at hu
        lia
      have hy0 : (0 : Fin (q + 1)) < y := by
        change 0 < y.val
        simp only [attachRight_val] at hv
        lia
      have h1 := hl x (Fin.last p) ⟨hxl, hx.trans (h.hrv_last A).symm⟩
      have h2 := hr 0 y ⟨hy0, (attachRight p q).injective hH⟩
      rw [attachLeft_last] at h1
      exact h1.trans h2
    · exact (hx (attachLeft_eq_attachRight_iff.mp hH).1).elim

theorem selected_glue_valid {m : ℕ} (A : Orientation L) (B : Orientation R)
    (c : Fin (p + q + 1) → Fin m) :
    (∀ u v, G.edgeData.selected (h.glue A B).val u v → c u < c v) ↔
      (∀ x y, L.edgeData.selected A.val x y →
          c (attachLeft p q x) < c (attachLeft p q y)) ∧
        ∀ x y, R.edgeData.selected B.val x y →
          c (attachRight p q x) < c (attachRight p q y) := by
  constructor
  · intro hc
    exact ⟨fun x y hxy => hc _ _ ((h.glue_selected_left A B x y).mpr hxy),
      fun x y hxy => hc _ _ ((h.glue_selected_right A B x y).mpr hxy)⟩
  · rintro ⟨hl, hr⟩ u v huv
    rcases (h.glue_selected A B u v).mp huv with
      ⟨x, y, rfl, rfl, hxy⟩ | ⟨x, y, rfl, rfl, hxy⟩
    · exact hl x y hxy
    · exact hr x y hxy

/-! ### State and component values -/

theorem strictOrderEnumerator_glue (A : Orientation L) (B : Orientation R) (m : ℕ) :
    G.edgeData.strictOrderEnumerator (h.glue A B).val m =
      ∑ β : Fin m, markedK A (Fin.last p) m β * omittedMarkedK B 0 m β := by
  rw [← relationValue_selected]
  exact relationValue_attach _ _ _ (h.selected_glue_valid A B)

theorem evalElementary_hrvMonomial_glue (A : Orientation L) (B : Orientation R) (m : ℕ) :
    evalElementary m (h.glue A B).hrvMonomial =
      ∑ β : Fin m, markedE A (Fin.last p) m β * omittedMarkedE B 0 m β := by
  rw [← sum_markedE (h.glue A B) 0 m]
  unfold markedE
  rw [sum_markedRelationValue]
  exact relationValue_attach _ _ _ (h.fibre_glue_valid A B)

omit h in
private theorem sum_component_product {M : Type*} [CommSemiring M] {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) {m : ℕ} (f : ι → Fin m → M) (g : κ → Fin m → M) :
    ∑ a ∈ s, ∑ b ∈ t, ∑ β, f a β * g b β =
      ∑ β, (∑ a ∈ s, f a β) * ∑ b ∈ t, g b β := by
  simp only [Finset.sum_mul_sum]
  calc _ = ∑ a ∈ s, ∑ β, ∑ b ∈ t, f a β * g b β :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- The K value of a whole attached component, at each alphabet size. -/
theorem componentStrictEnumerator_glue (A : Orientation L) (B : Orientation R) (m : ℕ) :
    componentStrictEnumerator G (h.glue A B) m =
      ∑ β : Fin m, componentMarkedK A (Fin.last p) m β * componentOmittedMarkedK B 0 m β := by
  unfold componentStrictEnumerator componentMarkedK componentOmittedMarkedK
  rw [h.sum_flipComponent_glue (fun η => G.edgeData.strictOrderEnumerator η.val m)]
  simp only [h.strictOrderEnumerator_glue]
  exact sum_component_product _ _ (fun a β => markedK a (Fin.last p) m β)
    (fun b β => omittedMarkedK b 0 m β)

/-- The E value of a whole attached component, at each alphabet size. -/
theorem evalElementary_componentHRV_glue (A : Orientation L) (B : Orientation R) (m : ℕ) :
    evalElementary m (componentHRV G (h.glue A B)) =
      ∑ β : Fin m, componentMarkedE A (Fin.last p) m β * componentOmittedMarkedE B 0 m β := by
  unfold componentHRV componentMarkedE componentOmittedMarkedE
  rw [map_sum, h.sum_flipComponent_glue (fun η => evalElementary m η.hrvMonomial)]
  simp only [h.evalElementary_hrvMonomial_glue]
  exact sum_component_product _ _ (fun a β => markedE a (Fin.last p) m β)
    (fun b β => omittedMarkedE b 0 m β)

end IsRightAttachment

end

end VerticalStripLLT.Circular.DiagramProof
