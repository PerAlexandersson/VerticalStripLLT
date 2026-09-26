import VerticalStripLLT.Circular.DDResolvedRows
import VerticalStripLLT.Circular.DDResolvedStrict
import VerticalStripLLT.Circular.CornerMeasure

/-! Area and strict-card measures for the resolved DD successor. -/

namespace VerticalStripLLT.Circular.Diagram

open scoped BigOperators Classical

variable {n : ℕ} {D : Diagram n} {t : ℤ} (B : D.DDLocalData t)

theorem DDLocalData.resolved_area_sum :
    ∑ v, B.resolved.area.area v = ∑ v, D.area.area v := by
  have hij : D.residue (D.boundary t + 1) ≠ D.residue t := by
    rw [← B.gh, ← B.fh]
    intro h
    exact B.hfg (D.strict_edge_eq_of_head_eq B.hf B.hg h.symm)
  have hpos : 0 < D.area.area (D.residue t) := by
    rw [← B.fh, ← (D.strict_corner B.f B.hf).1]
    exact B.f.length_pos
  have hsame : D.area.area (D.residue (D.boundary t + 1)) =
      D.area.area (D.residue (D.boundary t)) := by
    rw [D.residue_succ, ← B.eh]
    exact B.sameArea
  have hupdate := B.resolved_area
  rw [← hsame] at hupdate
  exact D.area_sum_eq_of_two_row_update B.resolved _ _ hij hpos hupdate

theorem DDLocalData.resolved_head_image :
    B.resolved.strict.image Edge.head =
      (D.strict.image Edge.head).erase B.e.head := by
  ext v
  constructor
  · intro hv
    obtain ⟨f, hf, hfv⟩ := Finset.mem_image.mp hv
    have hs : B.resolved.strictAt (v.val : ℤ) := by
      refine ⟨f, hf, ?_⟩
      exact hfv.trans (Orientation.residue_intCast_eq v).symm
    have hs' := (B.resolved_strictAt_iff _).mp hs
    have hv : D.residue (v.val : ℤ) ≠ D.residue (D.boundary t) := hs'.2
    have hve : v ≠ B.e.head := by
      intro h
      apply hv
      rw [h, Orientation.residue_intCast_eq, B.eh]
    obtain ⟨s, hs, hsv⟩ := hs'.1
    exact Finset.mem_erase.mpr ⟨hve,
      Finset.mem_image.mpr ⟨s, hs, hsv.trans (Orientation.residue_intCast_eq v)⟩⟩
  · intro hv
    obtain ⟨s, hs, hhead⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hv).2
    have hstrict : D.strictAt (v.val : ℤ) := by
      refine ⟨s, hs, hhead.trans (Orientation.residue_intCast_eq v).symm⟩
    have hne : D.residue (v.val : ℤ) ≠ D.residue (D.boundary t) := by
      intro h
      apply (Finset.mem_erase.mp hv).1
      calc
        v = D.residue (v.val : ℤ) := (Orientation.residue_intCast_eq v).symm
        _ = D.residue (D.boundary t) := h
        _ = B.e.head := B.eh.symm
    obtain ⟨f, hf, hfv⟩ := (B.resolved_strictAt_iff _).mpr ⟨hstrict, hne⟩
    exact Finset.mem_image.mpr ⟨f, hf, hfv.trans (Orientation.residue_intCast_eq v)⟩

theorem DDLocalData.resolved_strict_card :
    B.resolved.strict.card + 1 = D.strict.card := by
  have hcard := congrArg Finset.card B.resolved_head_image
  have he : B.e.head ∈ D.strict.image Edge.head :=
    Finset.mem_image.mpr ⟨B.e, B.he, rfl⟩
  rw [Finset.card_erase_of_mem he] at hcard
  have hRinj : Set.InjOn Edge.head (B.resolved.strict : Set (Edge B.resolved.area)) := by
    intro e he f hf h
    exact B.resolved.strict_edge_eq_of_head_eq he hf h
  have hDinj : Set.InjOn Edge.head (D.strict : Set (Edge D.area)) := by
    intro e he f hf h
    exact D.strict_edge_eq_of_head_eq he hf h
  have hR : B.resolved.strict.card = (B.resolved.strict.image Edge.head).card :=
    (Finset.card_image_of_injOn hRinj).symm
  have hD : D.strict.card = (D.strict.image Edge.head).card :=
    (Finset.card_image_of_injOn hDinj).symm
  rw [← hR, ← hD] at hcard
  have hpos : 0 < D.strict.card := Finset.card_pos.mpr ⟨B.e, B.he⟩
  lia

theorem DDLocalData.resolved_doubledArea :
    B.resolved.doubledArea = D.doubledArea + 1 := by
  have hs := B.resolved_area_sum
  have hc := B.resolved_strict_card
  have hR := B.resolved.strict_card_le_area_sum
  have hD := D.strict_card_le_area_sum
  unfold doubledArea
  lia

theorem DDLocalData.deleted_strict_card :
    (B.deleted).strict.card + 1 = D.strict.card := by
  have hcard := congrArg Finset.card
    (D.deleteCorner_pairGraph_strictEdges B.g (D.strict_corner B.g B.hg))
  have hmem : (B.g.tail, B.g.head) ∈ D.pairGraph.strictEdges := by
    exact (D.mem_pairGraph_strict_iff _).mpr ⟨B.g, B.hg, rfl⟩
  change B.deleted.pairGraph.strictEdges.card =
    (D.pairGraph.strictEdges.erase (B.g.tail, B.g.head)).card at hcard
  rw [Finset.card_erase_of_mem hmem] at hcard
  have hB : B.deleted.pairGraph.strictEdges.card = B.deleted.strict.card :=
    Finset.card_map _
  have hD : D.pairGraph.strictEdges.card = D.strict.card := Finset.card_map _
  rw [hB, hD] at hcard
  have hpos : 0 < D.strict.card := Finset.card_pos.mpr ⟨B.g, B.hg⟩
  lia

theorem DDLocalData.deleted_doubledArea :
    B.deleted.doubledArea + 1 = D.doubledArea := by
  have hs : (∑ i, B.deleted.area.area i) + 1 = ∑ i, D.area.area i :=
    D.deleteCorner_area_sum B.g (D.strict_corner B.g B.hg)
  have hc := B.deleted_strict_card
  have hQ := B.deleted.strict_card_le_area_sum
  have hD := D.strict_card_le_area_sum
  unfold doubledArea
  lia

end VerticalStripLLT.Circular.Diagram
