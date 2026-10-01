import VerticalStripLLT.Components.DiagramProof.CommonCoverUniqueness
import VerticalStripLLT.Components.DiagramProof.InitialVertexCounts
import VerticalStripLLT.Components.DiagramProof.NaturalRelations

/-!
# Common-cover uniqueness after an initial path

If the only natural edge at zero is `01`, every state selects it, flips never
involve zero, and the remaining core carries all connected common-cover data.
Deleting the forced pendant vertices one at a time therefore extends
common-cover uniqueness from a diagram without articulation to the same
diagram preceded by an initial path. This is a statement about actual paths
only; no component value is compared under pendant deletion.
-/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical CornerFamily

noncomputable section

section Pendant

variable {k : ℕ} {D : Diagram (k + 2)}

/-- The core obtained by deleting the vertex zero. -/
abbrev pendantCore (hD : Forward D) : Diagram (k + 1) :=
  inducedDiagram hD (Fin.succOrderEmb (k + 1))

theorem isCorner_zero_one (hD : Forward D) (hpend : ∀ v, naturalRel D 0 v ↔ v = 1)
    (e : Edge D.area) (ht : e.tail = 0) : IsCorner e := by
  apply (isCorner_iff_maximal hD e).mpr
  intro g hgt hgh
  have hg0 : g.tail = 0 := Fin.le_zero_iff.mp (ht ▸ hgt)
  have hgh1 := (hpend g.head).mp ⟨g, hg0, rfl⟩
  have heh1 := (hpend e.head).mp ⟨e, ht, rfl⟩
  exact D.endpointEmbedding.injective (Prod.ext (hg0.trans ht.symm) (hgh1.trans heh1.symm))

theorem selected_zero_iff (hD : Forward D) (hpend : ∀ v, naturalRel D 0 v ↔ v = 1)
    {θ : Orientation D} (hθ : (allCorners D).CommonCover θ) (v : Fin (k + 2)) :
    D.edgeData.selected θ.val 0 v ↔ v = 1 := by
  constructor
  · intro hs
    exact (hpend v).mp (naturalRel_of_selected hs)
  · rintro rfl
    obtain ⟨e, ht, hh⟩ := (hpend 1).mpr rfl
    have hcov := hθ e (Finset.mem_filter.mpr ⟨Finset.mem_univ _, isCorner_zero_one hD hpend e ht⟩)
    rw [ht, hh] at hcov
    exact selected_of_cover hD hcov

/-- The core of a common-cover state is a common-cover state. -/
theorem commonCover_restrict (hD : Forward D) (hpend : ∀ v, naturalRel D 0 v ↔ v = 1)
    {θ : Orientation D} (hθ : (allCorners D).CommonCover θ) :
    (allCorners (pendantCore hD)).CommonCover (initialVertexRestrict hD θ) := by
  intro e he
  let ι := Fin.succOrderEmb (k + 1)
  have hE := inducedDiagram_forward hD ι
  have heC : IsCorner e := (Finset.mem_filter.mp he).2
  -- The ambient edge with the shifted endpoints is a corner of `D`.
  obtain ⟨f, hft, hfh⟩ := (inducedDiagram_naturalEdge_iff hD ι e.tail e.head).mp ⟨e, rfl, rfl⟩
  have hfC : IsCorner f := by
    apply (isCorner_iff_maximal hD f).mpr
    intro g hgt hgh
    have hgt0 : g.tail ≠ 0 := by
      intro h0
      have hgh1 := (hpend g.head).mp ⟨g, h0, rfl⟩
      have : (2 : ℕ) ≤ g.head.val := by
        have h1 := hgh
        rw [hfh] at h1
        have h2 : (ι e.head).val ≤ g.head.val := h1
        simp only [ι, Fin.coe_succOrderEmb, Fin.val_succ] at h2
        have := hE e
        have he' : e.tail.val < e.head.val := this
        lia
      rw [hgh1] at this
      simp at this
    obtain ⟨a, ha⟩ := Fin.eq_succ_of_ne_zero hgt0
    have hgh0 : g.head ≠ 0 := ne_of_gt ((Fin.pos_iff_ne_zero.mpr hgt0).trans (hD g))
    obtain ⟨b, hb⟩ := Fin.eq_succ_of_ne_zero hgh0
    obtain ⟨g', hg't, hg'h⟩ := (inducedDiagram_naturalEdge_iff hD ι a b).mpr
      ⟨g, ha, hb⟩
    have hmax := (isCorner_iff_maximal hE e).mp heC g'
      (by
        rw [hg't]
        apply ι.le_iff_le.mp
        simpa only [ι, Fin.coe_succOrderEmb, ← ha, ← hft] using hgt)
      (by
        rw [hg'h]
        apply ι.le_iff_le.mp
        simpa only [ι, Fin.coe_succOrderEmb, ← hb, ← hfh] using hgh)
    subst hmax
    apply D.endpointEmbedding.injective
    apply Prod.ext
    · show g.tail = f.tail
      rw [ha, hft, hg't]
      rfl
    · show g.head = f.head
      rw [hb, hfh, hg'h]
      rfl
  have hcov := hθ f (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfC⟩)
  rw [hft, hfh] at hcov
  apply (relationCover_iff_of_convexImage ι (convex_succOrderEmb (k + 1))
    (fun {_ _} hs => θ.selected_lt_of_forward hD hs)
    (fun x y => initialVertexRestrict_selected hD θ x y) e.tail e.head).mp
  exact hcov

/-- Deleting a pendant zero keeps a connected selected relation connected. -/
theorem connected_restrict (hD : Forward D) (hpend : ∀ v, naturalRel D 0 v ↔ v = 1)
    {θ : Orientation D} (hcθ : SelectedConnected θ) :
    SelectedConnected (initialVertexRestrict hD θ) := by
  let proj : Fin (k + 2) → Fin (k + 1) := fun u => if h : u = 0 then 0 else u.pred h
  have hproj (u : Fin (k + 1)) : proj u.succ = u := by
    simp only [proj, Fin.succ_ne_zero, dite_false, Fin.pred_succ]
  have hstep : ∀ a b, D.edgeData.selected θ.val a b →
      WeakReach (initialVertexRestrict hD θ) (proj a) (proj b) := by
    intro a b hab
    by_cases ha : a = 0
    · subst ha
      have hb := (hpend b).mp (naturalRel_of_selected hab)
      subst hb
      have h1 : proj 1 = 0 := by
        simp only [proj]
        rw [dite_eq_right (by simp)]
        exact Fin.ext (by simp)
      have h0 : proj 0 = 0 := by simp [proj]
      rw [h0, h1]
      exact Relation.EqvGen.refl _
    · obtain ⟨a', rfl⟩ := Fin.eq_succ_of_ne_zero ha
      have hb : b ≠ 0 := ne_of_gt ((Fin.succ_pos a').trans (θ.selected_lt_of_forward hD hab))
      obtain ⟨b', rfl⟩ := Fin.eq_succ_of_ne_zero hb
      rw [hproj, hproj]
      exact Relation.EqvGen.rel _ _ ((initialVertexRestrict_selected hD θ a' b').mpr hab)
  intro x y
  have hxy := hcθ x.succ y.succ
  have key : ∀ a b, WeakReach θ a b →
      WeakReach (initialVertexRestrict hD θ) (proj a) (proj b) := by
    intro a b h
    induction h with
    | rel a b hs => exact hstep a b hs
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  simpa only [hproj] using key _ _ hxy

/-- Common-cover uniqueness passes from the core to a diagram with a pendant zero. -/
theorem commonCoverUnique_of_pendant (hD : Forward D)
    (hpend : ∀ v, naturalRel D 0 v ↔ v = 1)
    (hcore : CommonCoverUnique (pendantCore hD)) : CommonCoverUnique D := by
  intro θ τ hθ hτ hcθ hcτ htotal
  let ι := Fin.succOrderEmb (k + 1)
  have hrow (v : Fin (k + 2)) :
      D.edgeData.selected θ.val 0 v ↔ D.edgeData.selected τ.val 0 v := by
    rw [selected_zero_iff hD hpend hθ, selected_zero_iff hD hpend hτ]
  have hpath := hcore _ _ (commonCover_restrict hD hpend hθ) (commonCover_restrict hD hpend hτ)
    (connected_restrict hD hpend hcθ) (connected_restrict hD hpend hcτ)
    (initialVertex_core_count_eq hD θ τ htotal hrow)
  have hlift := initialVertex_lift_reachable hD θ _ hpath
  convert hlift using 1
  apply orientation_eq_of_selected_iff
  intro u v
  rw [inducedExtend_selected]
  by_cases hin : ∃ a b, ι a = u ∧ ι b = v
  · obtain ⟨a, b, rfl, rfl⟩ := hin
    constructor
    · intro hs
      exact Or.inl ⟨a, b, rfl, rfl, (initialVertexRestrict_selected hD τ a b).mpr hs⟩
    · rintro (⟨a', b', ha, hb, hs⟩ | ⟨hno, -⟩)
      · rw [ι.injective ha, ι.injective hb] at hs
        exact (initialVertexRestrict_selected hD τ a b).mp hs
      · exact (hno ⟨a, b, rfl, rfl⟩).elim
  · by_cases hu : u = 0
    · subst hu
      constructor
      · intro hs
        exact Or.inr ⟨hin, (hrow v).mpr hs⟩
      · rintro (⟨a, b, ha, hb, -⟩ | ⟨-, hs⟩)
        · exact (hin ⟨a, b, ha, hb⟩).elim
        · exact (hrow v).mp hs
    · have hv : v = 0 := by
        by_contra hv
        obtain ⟨a, ha⟩ := Fin.eq_succ_of_ne_zero hu
        obtain ⟨b, hb⟩ := Fin.eq_succ_of_ne_zero hv
        exact hin ⟨a, b, ha.symm, hb.symm⟩
      subst hv
      have hn1 : ¬ D.edgeData.selected τ.val u 0 := fun hs =>
        Fin.not_lt_zero _ (τ.selected_lt_of_forward hD hs)
      have hn2 : ¬ D.edgeData.selected θ.val u 0 := fun hs =>
        Fin.not_lt_zero _ (θ.selected_lt_of_forward hD hs)
      simp only [hn1, hn2, and_false, or_false, false_iff]
      rintro ⟨a, b, -, hb, -⟩
      simp at hb

end Pendant

/-- An initial path `0, …, b` followed by a block in which every short natural edge
is present. Every natural edge leaving the path is adjacent. -/
def InitialPathBlock {n : ℕ} (D : Diagram n) (b : ℕ) : Prop :=
  (∀ u v : Fin n, naturalRel D u v → u.val < b → v.val = u.val + 1) ∧
  (∀ u v : Fin n, b ≤ u.val → u < v → v.val ≤ u.val + 2 → naturalRel D u v) ∧
  (∀ u v : Fin n, u.val < b → v.val = u.val + 1 → naturalRel D u v)

/-- **Common-cover uniqueness after an initial path.** -/
theorem commonCoverUnique_of_initialPathBlock :
    ∀ (b : ℕ) {n : ℕ} {D : Diagram n}, Forward D → InitialPathBlock D b →
      CommonCoverUnique D := by
  intro b
  induction b with
  | zero =>
    intro n D hD hblock
    exact commonCoverUnique_of_shortEdges hD fun u v huv hgap =>
      hblock.2.1 u v (Nat.zero_le _) huv hgap
  | succ b ih =>
    intro n D hD hblock
    by_cases hn : n < 2
    · apply commonCoverUnique_of_shortEdges hD
      intro u v huv _
      have := v.isLt
      have huv' : u.val < v.val := huv
      lia
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by lia⟩
    have hpend : ∀ v, naturalRel D 0 v ↔ v = 1 := by
      intro v
      constructor
      · intro h
        apply Fin.ext
        have := hblock.1 0 v h (by simp)
        simpa using this
      · rintro rfl
        exact hblock.2.2 0 1 (by simp) (by simp)
    apply commonCoverUnique_of_pendant hD hpend
    apply ih (inducedDiagram_forward hD _)
    refine ⟨?_, ?_, ?_⟩
    · intro u v huv hu
      have h := hblock.1 u.succ v.succ ((inducedDiagram_naturalEdge_iff hD _ u v).mp huv)
        (by simp only [Fin.val_succ]; lia)
      simp only [Fin.val_succ] at h
      lia
    · intro u v hu huv hgap
      apply (inducedDiagram_naturalEdge_iff hD _ u v).mpr
      exact hblock.2.1 u.succ v.succ (by simp only [Fin.val_succ]; lia)
        (Fin.succ_lt_succ_iff.mpr huv) (by simp only [Fin.val_succ]; lia)
    · intro u v hu huv
      apply (inducedDiagram_naturalEdge_iff hD _ u v).mpr
      exact hblock.2.2 u.succ v.succ (by simp only [Fin.val_succ]; lia)
        (by simp only [Fin.val_succ]; lia)

end

end VerticalStripLLT.Circular.DiagramProof
