import VerticalStripLLT.Components.DiagramProof.CliqueBlockEmbedding
import VerticalStripLLT.Components.DiagramProof.CliqueLowerConnectivity
import VerticalStripLLT.Components.DiagramProof.CliqueStar

/-! Embedding-free paths for selected blocks in the last clique. -/

namespace VerticalStripLLT.Circular.DiagramProof

namespace CornerFamily

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hD : Forward D)

theorem exists_last_clique_block_star_path (g : Edge D.area) (hg : g ∈ F.edges)
    (hlast : ∀ v : Fin n, v ≤ g.head) (θ : Orientation D) (hθ : F.Anchor hD θ) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧ F.Anchor hD η ∧
      (∀ v, Relation.EqvGen (cliqueBlockRelation g θ) g.tail v → v < g.head →
        D.edgeData.selected η.val v g.head) ∧
      (∀ x y, (¬ Relation.EqvGen (cliqueBlockRelation g θ) g.tail x ∨
        ¬ Relation.EqvGen (cliqueBlockRelation g θ) g.tail y) →
        (D.edgeData.selected η.val x y ↔ D.edgeData.selected θ.val x y)) ∧
      ∀ x y, Relation.EqvGen (cliqueBlockRelation g θ) x y ↔
        Relation.EqvGen (cliqueBlockRelation g η) x y := by
  obtain ⟨k, ι, hbounds, htail, hblock⟩ :=
    exists_clique_block_embedding g θ g.tail ⟨le_rfl, (hD g).le⟩
  obtain ⟨i, hi⟩ := htail
  have hfirst : ι 0 = g.tail := by
    apply le_antisymm
    · rw [← hi]
      exact ι.monotone (Fin.zero_le i)
    · exact (hbounds 0).1
  have hselected : D.edgeData.selected θ.val g.tail g.head :=
    (mem_fullSelection_iff_selected θ g).mp (hθ.1 hg)
  have htailblock : Relation.EqvGen (cliqueBlockRelation g θ) (ι 0) g.tail :=
    (hblock g.tail).mp ⟨i, hi⟩
  have hheadblock : Relation.EqvGen (cliqueBlockRelation g θ) (ι 0) g.head := by
    apply Relation.EqvGen.trans _ _ _ htailblock
    exact Relation.EqvGen.rel _ _ ⟨⟨le_rfl, (hD g).le⟩,
      ⟨(hD g).le, le_rfl⟩, hselected⟩
  obtain ⟨j, hj⟩ := (hblock g.head).mpr hheadblock
  have hfinal : ι (Fin.last k) = g.head := by
    apply le_antisymm
    · exact (hbounds (Fin.last k)).2
    · rw [← hj]
      exact ι.monotone (Fin.le_last j)
  obtain ⟨η, hθη, hη, hstar, houtside, hblocks⟩ :=
    F.exists_last_clique_block_star hD g hg hlast ι hbounds hfirst hfinal θ hθ hblock
  refine ⟨η, hθη, hη, ?_, ?_, hblocks⟩
  · intro v hv hvg
    obtain ⟨a, ha⟩ := (hblock v).mpr (by simpa only [hfirst] using hv)
    rw [← ha]
    exact hstar a (by simpa only [ha] using hvg)
  · intro x y houtsideblock
    apply houtside x y
    rintro ⟨a, b, ha, hb⟩
    rcases houtsideblock with hx | hy
    · apply hx
      simpa only [hfirst] using (hblock x).mp ⟨a, ha⟩
    · apply hy
      simpa only [hfirst] using (hblock y).mp ⟨b, hb⟩

theorem exists_last_clique_block_lower_path (g : Edge D.area)
    (hlast : ∀ v : Fin n, v ≤ g.head) (θ : Orientation D) (hθ : F.Anchor hD θ)
    (c z : Fin n) (hz : g.tail < z ∧ z ≤ g.head) (hzc : z ≤ c)
    (hseparate : ¬ Relation.EqvGen (cliqueBlockRelation g θ) z g.tail) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧ F.Anchor hD η ∧
      (∀ x y, Relation.EqvGen (cliqueBlockRelation g θ) z x →
        Relation.EqvGen (cliqueBlockRelation g θ) z y → x ≤ c → y ≤ c →
        Relation.EqvGen
          (fun a b => a ≤ c ∧ b ≤ c ∧ D.edgeData.selected η.val a b) x y) ∧
      (∀ x y, (¬ Relation.EqvGen (cliqueBlockRelation g θ) z x ∨
        ¬ Relation.EqvGen (cliqueBlockRelation g θ) z y) →
        (D.edgeData.selected η.val x y ↔ D.edgeData.selected θ.val x y)) ∧
      (∀ x y, Relation.EqvGen (cliqueBlockRelation g θ) x y ↔
        Relation.EqvGen (cliqueBlockRelation g η) x y) ∧
      ∀ x y, Relation.EqvGen
        (fun a b => a ≤ c ∧ b ≤ c ∧ D.edgeData.selected θ.val a b) x y →
        Relation.EqvGen
          (fun a b => a ≤ c ∧ b ≤ c ∧ D.edgeData.selected η.val a b) x y := by
  obtain ⟨k, ι, hbounds, hzimage, hblock⟩ :=
    exists_clique_block_embedding g θ z ⟨hz.1.le, hz.2⟩
  obtain ⟨i, hi⟩ := hzimage
  have hzblock : Relation.EqvGen (cliqueBlockRelation g θ) (ι 0) z :=
    (hblock z).mp ⟨i, hi⟩
  have htail : ∀ i, g.tail < ι i := by
    intro j
    apply lt_of_le_of_ne (hbounds j).1
    intro hEq
    apply hseparate
    apply Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hzblock)
    apply (hblock g.tail).mp
    exact ⟨j, hEq.symm⟩
  obtain ⟨t, hcut⟩ := exists_initial_segment_of_orderEmbedding ι c ⟨i, hi.symm ▸ hzc⟩
  obtain ⟨η, hθη, hlower, houtside, hblocks, hkeep⟩ :=
    clique_exists_connected_lower_part hD g ι hbounds θ hblock c t hcut
  have hη : F.Anchor hD η :=
    F.anchor_of_last_clique_block_replacement hD g hlast ι htail θ η hθ houtside
  refine ⟨η, hθη, hη, ?_, ?_, hblocks, hkeep⟩
  · intro x y hx hy hxc hyc
    obtain ⟨a, ha⟩ := (hblock x).mpr
      (Relation.EqvGen.trans _ _ _ hzblock hx)
    obtain ⟨b, hb⟩ := (hblock y).mpr
      (Relation.EqvGen.trans _ _ _ hzblock hy)
    have hat : a ≤ t := (hcut a).mp (by simpa only [ha] using hxc)
    have hbt : b ≤ t := (hcut b).mp (by simpa only [hb] using hyc)
    rw [← ha, ← hb]
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hlower a hat))
      (hlower b hbt)
  · intro x y houtsideblock
    apply houtside x y
    rintro ⟨a, b, ha, hb⟩
    rcases houtsideblock with hx | hy
    · apply hx
      exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hzblock)
        ((hblock x).mp ⟨a, ha⟩)
    · apply hy
      exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hzblock)
        ((hblock y).mp ⟨b, hb⟩)

end CornerFamily

end VerticalStripLLT.Circular.DiagramProof
