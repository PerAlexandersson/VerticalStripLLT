import VerticalStripLLT.Components.DiagramProof.InitialVertexRemovable
import VerticalStripLLT.Components.DiagramProof.FirstCliqueInheritance
import VerticalStripLLT.Components.DiagramProof.TwoChainCardinality
import VerticalStripLLT.Components.DiagramProof.LastCliqueNaturalEdges
import VerticalStripLLT.Components.DiagramProof.CompleteBlock
import VerticalStripLLT.Components.DiagramProof.NaturalRelations

/-!
# Common-cover uniqueness without articulation

Every natural edge of length at most two being present is the absence of
articulation vertices for a connected ordinary diagram. Under this hypothesis,
any two connected states selecting every maximal corner as a cover, with the
same total selected size, are joined by actual flips.

The proof is strong induction on the vertex count, following the written
diagram argument. Diagrams with at most two corner chains and complete
diagrams are the bases. Otherwise let `0a` and `bc` be the first two corners.
If `b = 1` we delete `0` and use initial-vertex inheritance; if `b > 1` we keep
`0, b, …, n-1` and use first-clique inheritance. Both smaller diagrams again
have all short natural edges.
-/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical CornerFamily

noncomputable section

variable {n : ℕ}

/-- Every natural edge of length at most two is present. -/
def ShortEdges (D : Diagram n) : Prop :=
  ∀ u v : Fin n, u < v → v.val ≤ u.val + 2 → naturalRel D u v

/-- Connected common-cover states of the same total size lie in one flip component. -/
def CommonCoverUnique (D : Diagram n) : Prop :=
  ∀ θ τ : Orientation D, (allCorners D).CommonCover θ → (allCorners D).CommonCover τ →
    SelectedConnected θ → SelectedConnected τ → totalSelected θ = totalSelected τ →
    Relation.ReflTransGen (Flip D) θ τ

theorem shortEdges_reversed {D : Diagram n} (hD : Forward D) (hshort : ShortEdges D) :
    ShortEdges (reversedDiagram hD) := by
  intro u v huv hgap
  apply (reversedDiagram_naturalEdge_iff hD u v).mpr
  apply hshort v.rev u.rev (Fin.rev_lt_rev.mpr huv)
  simp only [Fin.val_rev]
  have := u.isLt
  have := v.isLt
  have huv' : u.val < v.val := huv
  lia

/-- A diagram whose extreme pair is natural is complete; its connected states
covering that pair are joined at each fixed total size. -/
theorem reachable_of_complete {k : ℕ} {D : Diagram (k + 1)} (hD : Forward D)
    (f : Edge D.area) (hft : f.tail = 0) (hfh : f.head = Fin.last k)
    {θ τ : Orientation D} (hθ : Cover θ 0 (Fin.last k)) (hτ : Cover τ 0 (Fin.last k))
    (hcθ : SelectedConnected θ) (hcτ : SelectedConnected τ)
    (htotal : totalSelected θ = totalSelected τ) :
    Relation.ReflTransGen (Flip D) θ τ := by
  let ι : Fin (k + 1) ↪o Fin (k + 1) := (OrderIso.refl _).toOrderEmbedding
  have hbounds (i : Fin (k + 1)) : f.tail ≤ ι i ∧ ι i ≤ f.head := by
    rw [hft, hfh]
    exact ⟨Fin.zero_le _, Fin.le_last _⟩
  have hcount (σ : Orientation D) :
      totalSelected (cliqueRestrict hD ι σ) = totalSelected σ := by
    rw [totalSelected_eq_card_selected, totalSelected_eq_card_selected]
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, cliqueRestrict_selected]
    rfl
  apply clique_reachable_of_block hD f ι hbounds θ τ
  · intro z
    refine iff_of_true ⟨z, rfl⟩ ?_
    exact Relation.EqvGen.mono (fun x y hxy => ⟨hbounds x, hbounds y, hxy⟩) _ _ (hcθ (ι 0) z)
  · intro u v
    exact Relation.EqvGen.mono
      (fun x y hxy => (cliqueRestrict_selected hD ι τ x y).mpr hxy) _ _ (hcτ u v)
  · exact hθ
  · exact hτ
  · rw [hcount, hcount, htotal]
  · intro u v hout
    exact (hout ⟨u, v, rfl, rfl⟩).elim

theorem exists_corner_of_naturalRel {D : Diagram n} (hD : Forward D) {u v : Fin n}
    (h : naturalRel D u v) :
    ∃ f : Edge D.area, IsCorner f ∧ f.tail ≤ u ∧ v ≤ f.head := by
  obtain ⟨e, rfl, rfl⟩ := h
  exact exists_corner_containing hD e

/-- Two corners with the same tail are equal. -/
theorem corner_eq_of_tail_eq {D : Diagram n} (hD : Forward D) {e f : Edge D.area}
    (he : IsCorner e) (hf : IsCorner f) (ht : e.tail = f.tail) : e = f := by
  have heF : e ∈ (allCorners D).edges := Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
  have hfF : f ∈ (allCorners D).edges := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩
  exact D.endpointEmbedding.injective (Prod.ext ht (le_antisymm
    ((allCorners D).head_le_of_same_tail hD hfF ht)
    ((allCorners D).head_le_of_same_tail hD heF ht.symm)))

/-- **Common-cover uniqueness.** In a forward diagram with every short natural
edge, connected common-cover states of the same total size are joined by flips. -/
theorem commonCoverUnique_of_shortEdges :
    ∀ {n : ℕ} {D : Diagram n}, Forward D → ShortEdges D → CommonCoverUnique D := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
  intro D hD hshort θ τ hθ hτ hcθ hcτ htotal
  let F := allCorners D
  by_cases hcard : Nat.card {t : Fin n // F.terminal hD t = t} ≤ 2
  · exact F.commonCover_connected_of_terminal_card_le_two hD D.area.positive hcard hθ hτ htotal
  have hbound : Nat.card {t : Fin n // F.terminal hD t = t} ≤ n := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
      (Nat.card_le_card_of_injective
        (fun u : {t : Fin n // F.terminal hD t = t} => u.val) Subtype.val_injective)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by lia⟩
  -- The first corner starts at zero.
  obtain ⟨f, hf, hft0, -⟩ := exists_corner_of_naturalRel hD
    (hshort ⟨0, by lia⟩ ⟨1, by lia⟩ (by simp) (by simp))
  have hft : f.tail = 0 := Fin.ext (by
    have : f.tail.val ≤ 0 := hft0
    simp only [Fin.val_zero]
    lia)
  have hfF : f ∈ F.edges := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩
  have hfpos : 0 < f.head.val := by
    have := hD f
    rw [hft] at this
    exact this
  by_cases hfh : f.head = Fin.last (k + 1)
  · have hcover (σ : Orientation D) (hσ : F.CommonCover σ) : Cover σ 0 (Fin.last (k + 1)) := by
      simpa only [hft, hfh] using hσ f hfF
    exact reachable_of_complete hD f hft hfh (hcover θ hθ) (hcover τ hτ) hcθ hcτ htotal
  have hfa : f.head.val < k + 1 := by
    have := f.head.isLt
    have hne : f.head.val ≠ k + 1 := fun h => hfh (Fin.ext h)
    lia
  -- A second corner contains the length-two edge over the first corner head.
  obtain ⟨h0, hh0, hh0t, hh0h⟩ := exists_corner_of_naturalRel hD
    (hshort ⟨f.head.val - 1, by lia⟩ ⟨f.head.val + 1, by lia⟩
      (by rw [Fin.lt_def]; dsimp only; lia) (by dsimp only; lia))
  have hh0t' : h0.tail.val ≤ f.head.val - 1 := hh0t
  have hh0h' : f.head.val + 1 ≤ h0.head.val := hh0h
  have hh0S : h0 ∈ F.edges.erase f := by
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh0⟩⟩
    rintro rfl
    lia
  obtain ⟨g, hgS, hgmin⟩ := (F.edges.erase f).exists_min_image (fun e => e.tail) ⟨h0, hh0S⟩
  have hgf : g ≠ f := (Finset.mem_erase.mp hgS).1
  have hgF : g ∈ F.edges := (Finset.mem_erase.mp hgS).2
  have hg : IsCorner g := F.corner g hgF
  have hafter : ∀ e : Edge D.area, IsCorner e → e ≠ f → g.tail ≤ e.tail := fun e he hef =>
    hgmin e (Finset.mem_erase.mpr ⟨hef, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩)
  have hgpos : 0 < g.tail.val := by
    by_contra hzero
    exact hgf (corner_eq_of_tail_eq hD hg hf (Fin.ext (by rw [hft]; simp only [Fin.val_zero]; lia)))
  have hfg : f.head < g.head := by
    by_contra hle
    have := F.corner_tail_le_of_head_le hD hgF (le_of_not_gt hle)
    rw [hft] at this
    have : g.tail.val ≤ 0 := this
    lia
  have hgfh : g.tail < f.head := by
    have := hgmin h0 hh0S
    change g.tail.val < f.head.val
    have : g.tail.val ≤ h0.tail.val := this
    lia
  by_cases hg1 : g.tail.val = 1
  · -- Initial-vertex inheritance after deleting zero.
    exact commonCover_connected_of_initialVertex_short hD f g hf hg hft
      (Fin.ext (by simpa using hg1)) hfg hshort (by lia)
      (ih (k + 1) (by lia) (inducedDiagram_forward hD _)
        (initialVertex_induced_short_naturalEdges hD hshort))
      θ τ hθ hτ hcθ hcτ htotal
  · -- First-clique inheritance on `0, b, …, n-1`, through the reflected last clique.
    have hD' := reversedDiagram_forward hD
    let ρ := reverseEdgeEquiv hD
    let c : Fin (k + 2) := g.tail.rev
    let e : Fin (k + 2) := f.tail.rev
    have hce : c < e := Fin.rev_lt_rev.mpr (by rw [hft]; exact Fin.lt_def.mpr hgpos)
    let L := lastCliqueEmbed c e hce
    let ι := reverseOrderEmbedding L
    have himage : ∀ z, (∃ w, ι w = z) ↔ g.tail ≤ z ∨ z = f.tail := by
      intro z
      rw [exists_reverseOrderEmbedding_iff, lastCliqueEmbed_image]
      have h1 : z.rev.val ≤ c.val ↔ g.tail ≤ z := by
        simp only [c, Fin.val_rev, Fin.le_iff_val_le_val]
        have := z.isLt
        have := g.tail.isLt
        constructor <;> intro <;> lia
      rw [h1, Fin.rev_eq_iff, Fin.rev_rev]
    have hshortL : ShortEdges (inducedDiagram hD' (reverseOrderEmbedding ι)) := by
      rw [reverseOrderEmbedding_involutive]
      apply lastClique_induced_short_naturalEdges hD' (shortEdges_reversed hD hshort)
        c e hce (ρ f)
      · rw [reverseEdgeEquiv_tail]
        exact Fin.rev_lt_rev.mpr hgfh
      · rw [reverseEdgeEquiv_head]
    have hsize : c.val + 2 < k + 2 := by
      simp only [c, Fin.val_rev]
      lia
    have hfgt : f.tail < g.tail := by
      rw [hft]
      exact Fin.lt_def.mpr hgpos
    exact commonCover_connected_of_firstClique_core hD ι f g hf hg
      (fun v => by rw [hft]; exact Fin.zero_le _) ⟨hfgt, hgfh, hfg⟩ hafter himage
      (ih (c.val + 2) hsize (inducedDiagram_forward hD' _) hshortL)
      θ τ hθ hτ hcθ hcτ htotal

end

end VerticalStripLLT.Circular.DiagramProof
