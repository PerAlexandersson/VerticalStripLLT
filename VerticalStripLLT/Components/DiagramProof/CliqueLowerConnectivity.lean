import VerticalStripLLT.Components.DiagramProof.CliquePaths
import VerticalStripLLT.Components.DiagramProof.CliqueBlockReplacement
import VerticalStripLLT.Components.DiagramProof.LowerConnectivity

/-! Connecting the lower intersection of a selected clique block with exact exterior. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {k n : ℕ} {D : Diagram n}

/-- Rearrange one selected clique block so its vertices below the cutoff are connected.
Every previous lower connection survives, and all exterior selected edges are restored. -/
theorem clique_exists_connected_lower_part (hD : Forward D) (e : Edge D.area)
    (ι : Fin (k + 1) ↪o Fin n) (hbounds : ∀ i, e.tail ≤ ι i ∧ ι i ≤ e.head)
    (θ : Orientation D)
    (hblock : ∀ z, (∃ i, ι i = z) ↔ Relation.EqvGen
      (fun x y => (e.tail ≤ x ∧ x ≤ e.head) ∧ (e.tail ≤ y ∧ y ≤ e.head) ∧
        D.edgeData.selected θ.val x y) (ι 0) z)
    (c : Fin n) (t : Fin (k + 1)) (hcut : ∀ i, ι i ≤ c ↔ i ≤ t) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧
      (∀ v, v ≤ t → Relation.EqvGen
        (fun a b => a ≤ c ∧ b ≤ c ∧ D.edgeData.selected η.val a b) (ι 0) (ι v)) ∧
      (∀ x y, (¬ ∃ a b, ι a = x ∧ ι b = y) →
        (D.edgeData.selected η.val x y ↔ D.edgeData.selected θ.val x y)) ∧
      (∀ x y, Relation.EqvGen (cliqueBlockRelation e θ) x y ↔
        Relation.EqvGen (cliqueBlockRelation e η) x y) ∧
      ∀ x y, Relation.EqvGen
        (fun a b => a ≤ c ∧ b ≤ c ∧ D.edgeData.selected θ.val a b) x y →
        Relation.EqvGen
          (fun a b => a ≤ c ∧ b ≤ c ∧ D.edgeData.selected η.val a b) x y := by
  have hc := cliqueRestrict_connected_of_block hD ι θ e.tail e.head hbounds hblock
  obtain ⟨α, hp, hα, hkeep⟩ := exists_connected_lower_part (complete_forward k)
    (cliqueRestrict hD ι θ) 0 t (fun w _ => Fin.zero_le w)
  obtain ⟨η, hθη, hinside, houtside⟩ :=
    clique_lift_core_of_block hD e ι hbounds θ hblock α hp
  have hmap (u v : Fin (k + 1))
      (h : Relation.EqvGen
        (fun a b => a ≤ t ∧ b ≤ t ∧ (completeDiagram k).edgeData.selected α.val a b) u v) :
      Relation.EqvGen
        (fun a b => a ≤ c ∧ b ≤ c ∧ D.edgeData.selected η.val a b) (ι u) (ι v) := by
    induction h with
    | rel a b hab =>
      exact .rel _ _ ⟨(hcut a).mpr hab.1, (hcut b).mpr hab.2.1, (hinside a b).mpr hab.2.2⟩
    | refl => exact .refl _
    | symm a b hab ih => exact .symm _ _ ih
    | trans a b c hab hbc ihab ihbc => exact .trans _ _ _ ihab ihbc
  refine ⟨η, hθη, fun v hv => hmap 0 v (hα v (hc 0 v) hv), houtside, ?_, ?_⟩
  · exact cliqueBlock_weakReach_iff e ι hbounds θ η hblock α
      ((selectedConnected_iff_of_reachable hp).mp hc) hinside
      (fun x y h => (houtside x y h).symm)
  apply Relation.EqvGen.eqvGen_le
  intro x y hxy
  by_cases himage : ∃ a b, ι a = x ∧ ι b = y
  · obtain ⟨a, b, rfl, rfl⟩ := himage
    apply hmap
    apply hkeep a b
    exact .rel _ _ ⟨(hcut a).mp hxy.1, (hcut b).mp hxy.2.1,
      (cliqueRestrict_selected hD ι θ a b).mpr hxy.2.2⟩
  · exact .rel _ _ ⟨hxy.1, hxy.2.1, (houtside x y himage).mpr hxy.2.2⟩

end VerticalStripLLT.Circular.DiagramProof
