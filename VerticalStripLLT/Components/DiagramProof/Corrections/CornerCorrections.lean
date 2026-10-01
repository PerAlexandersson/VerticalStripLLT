import VerticalStripLLT.Components.DiagramProof.Corrections.AlternatingCertificate

/-!
# Corner corrections

Two corrections change only the strict decorations or remove an unused corner;
they keep every selected relation and therefore carry whole components
bijectively. A component omitting a maximal corner is the same component of the
diagram with that natural corner deleted, of smaller area. A component selecting
every maximal corner is the same component of the saturated diagram, in which all
maximal corners are strict. Combined with alternating deletion, a component which
selects every maximal corner but never has all of them covering simultaneously
has a signed certificate by smaller whole components.
-/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {n : ℕ} {D E : Diagram n}

/-- Covers depend only on the selected relation. -/
theorem cover_iff_of_selected_iff {θ : Orientation D} {θ' : Orientation E}
    (h : ∀ u v, E.edgeData.selected θ'.val u v ↔ D.edgeData.selected θ.val u v) (a c : Fin n) :
    Cover θ' a c ↔ Cover θ a c :=
  (corresponds_refl h).cover_iff a c

/-- A state whose relation is valid in another forward diagram corresponds to a state there. -/
theorem exists_corresponds_refl (hE : Forward E) (θ : Orientation D)
    (hnat : ∀ u v, D.edgeData.selected θ.val u v → naturalRel E u v)
    (hstrict : ∀ u v, strictRel E u v → D.edgeData.selected θ.val u v) :
    ∃ θ' : Orientation E, Corresponds (Equiv.refl _) θ θ' := by
  obtain ⟨θ', h⟩ := exists_orientation_of_relation hE _ hnat hstrict
  exact ⟨θ', corresponds_refl h⟩

/-- Diagrams with the same natural relation are equally large. -/
theorem measureLT_congr_right {D₁ D₂ E : Diagram n}
    (h : ∀ u v, naturalRel D₁ u v ↔ naturalRel D₂ u v) :
    MeasureLT E D₁ ↔ MeasureLT E D₂ := by
  obtain ⟨ha, hm⟩ := measure_eq_of_naturalRel_iff h
  unfold MeasureLT
  rw [ha, hm]

section

variable {k : ℕ} {D : Diagram (k + 1)} (hD : Forward D)

theorem Comp.K_eq_of_corresponds {E : Diagram (k + 1)} (hE : Forward E) {θ : Orientation D}
    {θ' : Orientation E} (h : Corresponds (Equiv.refl _) θ θ') (m : ℕ) (β : Fin m) :
    (⟨E, hE, θ'⟩ : Comp k).K m β = (⟨D, hD, θ⟩ : Comp k).K m β :=
  h.componentMarkedK_eq hD hE rfl m β

theorem Comp.E_eq_of_corresponds {E : Diagram (k + 1)} (hE : Forward E) {θ : Orientation D}
    {θ' : Orientation E} (h : Corresponds (Equiv.refl _) θ θ') (m : ℕ) (β : Fin m) :
    (⟨E, hE, θ'⟩ : Comp k).E m β = (⟨D, hD, θ⟩ : Comp k).E m β :=
  h.componentMarkedE_eq hD hE rfl m β

/-- A certificate for a corresponding component of an equally large diagram. -/
theorem certifies_of_corresponds {E : Diagram (k + 1)} (hE : Forward E) {θ : Orientation D}
    {θ' : Orientation E} (h : Corresponds (Equiv.refl _) θ θ')
    (hnat : ∀ u v, naturalRel D u v ↔ naturalRel E u v) {c : Cert k}
    (hc : Certifies ⟨E, hE, θ'⟩ c) : Certifies ⟨D, hD, θ⟩ c := by
  refine ⟨fun m β => ?_, fun y hy => (measureLT_congr_right hnat).mpr (hc.2 y hy)⟩
  rw [← Comp.K_eq_of_corresponds hD hE h, ← Comp.E_eq_of_corresponds hD hE h]
  exact hc.1 m β

/-! ### Deleting an unused corner -/

/-- Delete a maximal natural pair which is not strict. -/
def deleteCorner {s t : Fin (k + 1)} (hmax : MaximalPair (naturalRel D) s t)
    (hns : ¬ strictRel D s t) : Diagram (k + 1) :=
  ofRelations (fun u v => naturalRel D u v ∧ ¬ (u = s ∧ v = t)) (strictRel D)
    ((ordinaryRelation_naturalRel hD).removeMaximal (fun u v => u = s ∧ v = t)
      (by rintro _ _ ⟨rfl, rfl⟩; exact hmax))
    (fun _ _ h => (maximalPair_of_strictRel hD h).of_le (fun _ _ h' => h'.1)
      ⟨naturalRel_of_strictRel h, fun ⟨h1, h2⟩ => hns (h1 ▸ h2 ▸ h)⟩)
    D.area.positive

theorem deleteCorner_forward {s t : Fin (k + 1)} (hmax : MaximalPair (naturalRel D) s t)
    (hns : ¬ strictRel D s t) : Forward (deleteCorner hD hmax hns) :=
  ofRelations_forward _ _ _ _ _

theorem deleteCorner_naturalRel {s t : Fin (k + 1)} (hmax : MaximalPair (naturalRel D) s t)
    (hns : ¬ strictRel D s t) (u v : Fin (k + 1)) :
    naturalRel (deleteCorner hD hmax hns) u v ↔ naturalRel D u v ∧ ¬ (u = s ∧ v = t) :=
  ofRelations_naturalRel ..

theorem deleteCorner_strictRel {s t : Fin (k + 1)} (hmax : MaximalPair (naturalRel D) s t)
    (hns : ¬ strictRel D s t) (u v : Fin (k + 1)) :
    strictRel (deleteCorner hD hmax hns) u v ↔ strictRel D u v :=
  ofRelations_strictRel ..

/-- **Absent corner.** A component omitting a maximal corner is a whole component of
the diagram with that corner deleted. -/
theorem certifies_absentCorner (θ : Orientation D) {s t : Fin (k + 1)}
    (hmax : MaximalPair (naturalRel D) s t) (hθ : ¬ D.edgeData.selected θ.val s t) :
    ∃ c : Cert k, Certifies ⟨D, hD, θ⟩ c := by
  have hns : ¬ strictRel D s t := fun h => hθ (selected_of_strictRel θ h)
  have hD' := deleteCorner_forward hD hmax hns
  obtain ⟨θ', hc⟩ := exists_corresponds_refl hD' θ
    (fun u v h => (deleteCorner_naturalRel hD hmax hns u v).mpr
      ⟨naturalRel_of_selected h, fun ⟨h1, h2⟩ => hθ (h1 ▸ h2 ▸ h)⟩)
    (fun u v h => selected_of_strictRel θ ((deleteCorner_strictRel hD hmax hns u v).mp h))
  refine ⟨Finsupp.single ⟨deleteCorner hD hmax hns, hD', θ'⟩ 1, fun m β => ?_,
    Cert.smaller_single ?_⟩
  · simp only [Cert.K_single, Cert.E_single, one_smul]
    exact ⟨(Comp.K_eq_of_corresponds hD hD' hc m β).symm,
      (Comp.E_eq_of_corresponds hD hD' hc m β).symm⟩
  · left
    apply naturalArea_lt_of_ssubset
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨(s, t), mem_naturalPairs.mpr hmax.1, ?_⟩
      rw [mem_naturalPairs]
      exact fun h => ((deleteCorner_naturalRel hD hmax hns s t).mp h).2 ⟨rfl, rfl⟩
    · intro x hx
      exact mem_naturalPairs.mpr ((deleteCorner_naturalRel hD hmax hns _ _).mp
        (mem_naturalPairs.mp hx)).1

/-! ### Saturation -/

/-- Mark every maximal natural corner strict. -/
def saturate : Diagram (k + 1) :=
  ofRelations (naturalRel D) (MaximalPair (naturalRel D)) (ordinaryRelation_naturalRel hD)
    (fun _ _ h => h) D.area.positive

theorem saturate_forward : Forward (saturate hD) := ofRelations_forward _ _ _ _ _

theorem saturate_naturalRel (u v : Fin (k + 1)) :
    naturalRel (saturate hD) u v ↔ naturalRel D u v := ofRelations_naturalRel ..

theorem saturate_strictRel (u v : Fin (k + 1)) :
    strictRel (saturate hD) u v ↔ MaximalPair (naturalRel D) u v := ofRelations_strictRel ..

include hD in
theorem maximalPair_of_isCorner {e : Edge D.area} (he : IsCorner e) :
    MaximalPair (naturalRel D) e.tail e.head := by
  refine ⟨⟨e, rfl, rfl⟩, ?_⟩
  rintro x y ⟨f, rfl, rfl⟩ hx hy
  have := (isCorner_iff_maximal hD e).mp he f hx hy
  subst this
  exact ⟨rfl, rfl⟩

/-- A state selecting every maximal corner is a state of the saturated diagram. -/
theorem exists_saturate (θ : Orientation D)
    (hall : ∀ s t, MaximalPair (naturalRel D) s t → D.edgeData.selected θ.val s t) :
    ∃ θ' : Orientation (saturate hD), Corresponds (Equiv.refl _) θ θ' :=
  exists_corresponds_refl (saturate_forward hD) θ
    (fun u v h => (saturate_naturalRel hD u v).mpr (naturalRel_of_selected h))
    (fun u v h => hall u v ((saturate_strictRel hD u v).mp h))

/-- **No common cover.** A component selecting every maximal corner, none of whose
states has all maximal corners covering, has a signed certificate. -/
theorem certifies_noCommonCover (θ : Orientation D)
    (hall : ∀ s t, MaximalPair (naturalRel D) s t → D.edgeData.selected θ.val s t)
    (hno : ∀ η ∈ flipComponent D θ, ¬ (allCorners D).CommonCover η) :
    ∃ c : Cert k, Certifies ⟨D, hD, θ⟩ c := by
  obtain ⟨θs, hc⟩ := exists_saturate hD θ hall
  obtain ⟨c, hcert⟩ := certifies_alternating (saturate_forward hD) θs (by
    intro η' hη'
    obtain ⟨η, hp, hη⟩ := hc.symm.reachable (saturate_forward hD) hD
      (mem_flipComponent_iff.mp hη')
    have hsel : ∀ u v, (saturate hD).edgeData.selected η'.val u v ↔
        D.edgeData.selected η.val u v := fun u v => (hη.selected u v).symm
    have hnc := hno η (mem_flipComponent_iff.mpr hp)
    unfold CornerFamily.CommonCover at hnc
    push Not at hnc
    obtain ⟨e, he, hcov⟩ := hnc
    refine ⟨(e.tail, e.head), mem_strictPairs.mpr ((saturate_strictRel hD _ _).mpr
      (maximalPair_of_isCorner hD (Finset.mem_filter.mp he).2)), ?_⟩
    rw [cover_iff_of_selected_iff hsel]
    exact hcov)
  exact ⟨c, certifies_of_corresponds hD (saturate_forward hD) hc
    (fun u v => (saturate_naturalRel hD u v).symm) hcert⟩

end

end

end VerticalStripLLT.Circular.DiagramProof
