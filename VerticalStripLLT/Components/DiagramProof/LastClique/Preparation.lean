import VerticalStripLLT.Components.DiagramProof.LastClique.LastCliqueBlockPaths

/-! Finite preparation of the nonterminal blocks below a last-clique cutoff. -/

namespace VerticalStripLLT.Circular.DiagramProof

namespace CornerFamily

open Classical

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hD : Forward D)

private theorem prepare_blocks_finset (g : Edge D.area)
    (hlast : ∀ v : Fin n, v ≤ g.head) (σ : Orientation D) (hσ : F.Anchor hD σ)
    (c : Fin n)
    (hstar : ∀ v, Relation.EqvGen (cliqueBlockRelation g σ) g.tail v → v < g.head →
      D.edgeData.selected σ.val v g.head) :
    ∀ s : Finset (Fin n), ∃ η : Orientation D, Relation.ReflTransGen (Flip D) σ η ∧
      F.Anchor hD η ∧
      (∀ x y, Relation.EqvGen (cliqueBlockRelation g σ) x y ↔
        Relation.EqvGen (cliqueBlockRelation g η) x y) ∧
      (∀ v, Relation.EqvGen (cliqueBlockRelation g σ) g.tail v → v < g.head →
        D.edgeData.selected η.val v g.head) ∧
      (∀ z ∈ s, g.tail < z → z ≤ c →
        ¬ Relation.EqvGen (cliqueBlockRelation g σ) z g.tail →
        ∀ y, Relation.EqvGen (cliqueBlockRelation g σ) z y → y ≤ c →
          Relation.EqvGen
            (fun a b => a ≤ c ∧ b ≤ c ∧ D.edgeData.selected η.val a b) z y) := by
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨σ, .refl, hσ, fun _ _ => Iff.rfl, hstar, by simp⟩
  | @insert z s hz ih =>
    obtain ⟨τ, hστ, hτ, hpart, hτstar, hdone⟩ := ih
    by_cases hgood : g.tail < z ∧ z ≤ c ∧
        ¬ Relation.EqvGen (cliqueBlockRelation g σ) z g.tail
    · have hsep : ¬ Relation.EqvGen (cliqueBlockRelation g τ) z g.tail := by
        intro h
        exact hgood.2.2 ((hpart z g.tail).mpr h)
      obtain ⟨η, hτη, hη, hnew, hout, hnewpart, hkeep⟩ :=
        F.exists_last_clique_block_lower_path hD g hlast τ hτ c z
          ⟨hgood.1, hlast z⟩ hgood.2.1 hsep
      refine ⟨η, hστ.trans hτη, hη, ?_, ?_, ?_⟩
      · intro x y
        exact (hpart x y).trans (hnewpart x y)
      · intro v hv hvg
        have hvτ : Relation.EqvGen (cliqueBlockRelation g τ) g.tail v :=
          (hpart g.tail v).mp hv
        have houtside : ¬ Relation.EqvGen (cliqueBlockRelation g τ) z v := by
          intro hzv
          exact hsep (Relation.EqvGen.trans _ _ _ hzv
            (Relation.EqvGen.symm _ _ hvτ))
        exact (hout v g.head (Or.inl houtside)).mpr (hτstar v hv hvg)
      · intro w hw htw hwc hwsep y hwy hyc
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact hnew w y ((hpart w w).mp (.refl _))
            ((hpart w y).mp hwy) hwc hyc
        · exact hkeep w y (hdone w hw htw hwc hwsep y hwy hyc)
    · refine ⟨τ, hστ, hτ, hpart, hτstar, ?_⟩
      intro w hw htw hwc hwsep y hwy hyc
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact (hgood ⟨htw, hwc, hwsep⟩).elim
      · exact hdone w hw htw hwc hwsep y hwy hyc

/-- Preparation below the cutoff `c`: actual flips build the star at `g.head` and confine the
blocks below `c` to the prefix, keeping all clique-block connections. -/
theorem exists_last_clique_preparation (g : Edge D.area) (hg : g ∈ F.edges)
    (hlast : ∀ v : Fin n, v ≤ g.head) (θ : Orientation D) (hθ : F.Anchor hD θ)
    (c : Fin n) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧ F.Anchor hD η ∧
      (∀ v, Relation.EqvGen (cliqueBlockRelation g θ) g.tail v → v < g.head →
        D.edgeData.selected η.val v g.head) ∧
      (∀ x y, g.tail < x → x ≤ c →
        ¬ Relation.EqvGen (cliqueBlockRelation g θ) x g.tail →
        Relation.EqvGen (cliqueBlockRelation g θ) x y → y ≤ c →
          Relation.EqvGen
            (fun a b => a ≤ c ∧ b ≤ c ∧ D.edgeData.selected η.val a b) x y) ∧
      ∀ x y, Relation.EqvGen (cliqueBlockRelation g θ) x y ↔
        Relation.EqvGen (cliqueBlockRelation g η) x y := by
  obtain ⟨σ, hθσ, hσ, hstar, _, hpart⟩ :=
    F.exists_last_clique_block_star_path hD g hg hlast θ hθ
  obtain ⟨η, hση, hη, hpart', hstar', hdone⟩ :=
    prepare_blocks_finset F hD g hlast σ hσ c
      (fun v hv => hstar v ((hpart g.tail v).mpr hv)) Finset.univ
  refine ⟨η, hθσ.trans hση, hη, ?_, ?_, fun x y => (hpart x y).trans (hpart' x y)⟩
  · intro v hv hvg
    exact hstar' v ((hpart g.tail v).mp hv) hvg
  · intro x y htx hxc hsep hxy hyc
    exact hdone x (Finset.mem_univ _) htx hxc
      (fun h => hsep ((hpart x g.tail).mpr h)) y ((hpart x y).mp hxy) hyc

end CornerFamily

end VerticalStripLLT.Circular.DiagramProof
