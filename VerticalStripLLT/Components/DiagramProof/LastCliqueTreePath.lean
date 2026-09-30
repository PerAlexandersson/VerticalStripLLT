import VerticalStripLLT.Components.DiagramProof.LastCliqueTreeReplacement
import VerticalStripLLT.Components.DiagramProof.LastCliqueStarConnectivity
import VerticalStripLLT.Components.DiagramProof.LastCliqueConnectedCore

/-! Preparation, core replacement, and the final last-clique star, as in the diagrams. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k n : ℕ} {D : Diagram n}

/-- Reach a prescribed core tree and the full last star by the three displayed moves.
The smaller-core uniqueness assumption is the induction hypothesis. -/
theorem exists_reachable_lastClique_tree
    (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n) (c : Fin n)
    (g : Edge D.area) (hg : IsCorner g) (hlast : ∀ v : Fin n, v ≤ g.head)
    (hgc : g.tail < c) (hcg : c < g.head)
    (hbefore : ∀ f : Edge D.area, IsCorner f → f ≠ g → f.head ≤ c)
    (himage : ∀ z, (∃ w, ι w = z) ↔ z ≤ c ∨ z = g.head)
    (hcorners : ∀ e : Edge D.area, IsCorner e →
      ∃ u v, ι u = e.tail ∧ ι v = e.head)
    (hunique : ∀ α β : Orientation (inducedDiagram hD ι),
      (allCorners (inducedDiagram hD ι)).CommonCover α →
      (allCorners (inducedDiagram hD ι)).CommonCover β →
      SelectedConnected α → SelectedConnected β → totalSelected α = totalSelected β →
      Relation.ReflTransGen (Flip (inducedDiagram hD ι)) α β)
    (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree)
    (hFT : edgeSetGraph (allCorners (inducedDiagram hD ι)).edges ≤ T)
    (hTG : T ≤ edgeSetGraph ((allCorners (inducedDiagram hD ι)).goodEdges
      (inducedDiagram_forward hD ι)))
    (hstar : ∀ u v, g.tail ≤ ι u → ι u < g.head → ι v = g.head → T.Adj u v)
    (θ : Orientation D) (hθ : (allCorners D).Anchor hD θ)
    (hconn : SelectedConnected θ) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧
      (allCorners D).Anchor hD η ∧
      (∀ e : Edge (inducedDiagram hD ι).area, T.Adj e.tail e.head →
        D.edgeData.selected η.val (ι e.tail) (ι e.head)) ∧
      ∀ v, g.tail ≤ v → v < g.head → D.edgeData.selected η.val v g.head := by
  have hgm : g ∈ (allCorners D).edges :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩
  obtain ⟨α, hθα, hα, hcore, _, _⟩ :=
    (allCorners D).exists_reachable_connected_lastClique_core hD ι c g hgm hlast
      hbefore himage θ hθ hconn
  obtain ⟨ζ, hαζ, hζ, htree, _⟩ := exists_lastClique_tree_replacement hD ι c g hg
    hlast hgc hcg himage hcorners hunique T hT hFT hTG α hα hcore
  have hθζ := hθα.trans hαζ
  have hcζ := (selectedConnected_iff_of_reachable hθζ).mp hconn
  obtain ⟨j, hj⟩ := (himage g.head).mpr (Or.inr rfl)
  have hretained : ∀ u, g.tail ≤ ι u → ι u < g.head →
      D.edgeData.selected ζ.val (ι u) g.head := by
    intro u hau hue
    obtain ⟨f, hft, hfh⟩ := exists_edge_of_naturalLift_of_le
      (D.naturalLift_of_tail_lt_head g (hD g)) hau hue le_rfl
    obtain ⟨e, het, heh⟩ := (inducedDiagram_naturalEdge_iff hD ι u j).mpr
      ⟨f, hft, hfh.trans hj.symm⟩
    have hsel := htree e (by rw [het, heh]; exact hstar u j hau hue hj)
    simpa only [het, heh, hj] using hsel
  have hwhole := lastClique_block_connected_of_star hD ι c g hbefore himage ζ hcζ
    hretained
  obtain ⟨η, hζη, hη, hfullstar, houtside, _⟩ :=
    (allCorners D).exists_last_clique_block_star_path hD g hgm hlast ζ hζ
  have hfinalstar : ∀ v, g.tail ≤ v → v < g.head →
      D.edgeData.selected η.val v g.head := by
    intro v hav hve
    apply hfullstar v _ hve
    exact .trans _ _ _ (hwhole g.tail le_rfl (hD g).le)
      (.symm _ _ (hwhole v hav hve.le))
  refine ⟨η, hθζ.trans hζη, hη, ?_, hfinalstar⟩
  intro e he
  by_cases htail : g.tail ≤ ι e.tail
  · have heforward := ι.strictMono (inducedDiagram_forward hD ι e)
    have hhead : ι e.head = g.head := by
      by_contra hne
      have hh : ι e.head < g.head := lt_of_le_of_ne (hlast _) hne
      exact SimpleGraph.not_adj_of_adjacent_to_same hT.isAcyclic
        (inducedDiagram_forward hD ι e).ne
        (hstar e.tail j htail (heforward.trans hh) hj)
        (hstar e.head j (htail.trans heforward.le) hh hj) he
    rw [hhead]
    exact hfinalstar _ htail (by simpa only [hhead] using heforward)
  · apply (houtside _ _ (Or.inl ?_)).mpr (htree e he)
    intro hblock
    rcases eqvGen_cliqueBlockRelation_eq_or_bounds g ζ hblock with heq | hbounds
    · exact htail heq.le
    · exact htail hbounds.2.1

end

end VerticalStripLLT.Circular.DiagramProof
