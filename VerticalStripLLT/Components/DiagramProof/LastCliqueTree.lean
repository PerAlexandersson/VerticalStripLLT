import VerticalStripLLT.Components.DiagramProof.CornerStarForest
import VerticalStripLLT.Components.DiagramProof.AnchorSizes
import VerticalStripLLT.Components.DiagramProof.CliqueEdges
import VerticalStripLLT.Components.DiagramProof.TreeOmissions

/-! The fixed tree displayed in last-clique inheritance and its forced omissions. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

open Classical

noncomputable section

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hD : Forward D)

/-- Choose a good tree containing the retained corners and the entire terminal star. -/
theorem exists_last_clique_tree (g : Edge D.area) (hg : g ∈ F.edges)
    (hlast : ∀ v : Fin n, v ≤ g.head)
    (θ : Orientation D) (hθ : F.Anchor hD θ) (hconnected : SelectedConnected θ) :
    ∃ T : SimpleGraph (Fin n), edgeSetGraph F.edges ≤ T ∧
      T ≤ edgeSetGraph (F.goodEdges hD) ∧ T.IsTree ∧
      ∀ v, g.tail ≤ v → v < g.head → T.Adj v g.head := by
  let : Nonempty (Fin n) := ⟨g.tail⟩
  let S := Finset.univ.filter fun f : Edge D.area => g.tail < f.tail ∧ f.head = g.head
  have hS : ∀ f ∈ S, g.tail < f.tail ∧ f.head = g.head :=
    fun _ hf => (Finset.mem_filter.mp hf).2
  have hsel : edgeSetGraph (fullSelection θ) ≤ edgeSetGraph (F.goodEdges hD) :=
    edgeSetGraph_mono ((F.anchor_iff_subsets hD θ).mp hθ).2
  have hG : (edgeSetGraph (F.goodEdges hD)).Connected := by
    constructor
    intro u v
    exact ((edgeSetGraph_fullSelection_preconnected_iff θ).mpr hconnected u v).mono hsel
  obtain ⟨T, hreq, hTG, hT⟩ :=
    F.exists_tree_containing_corners_and_last_star hD g hlast S hS hG
  have hFT : edgeSetGraph F.edges ≤ T :=
    (edgeSetGraph_mono (Finset.subset_union_left : F.edges ⊆ F.edges ∪ S)).trans hreq
  refine ⟨T, hFT, hTG, hT, ?_⟩
  intro v hav hve
  rcases hav.eq_or_lt with rfl | hav
  · exact hFT ((edgeSetGraph_adj_iff_mem hD F.edges g).mpr hg)
  · obtain ⟨f, hft, hfh⟩ := exists_edge_of_naturalLift_of_le
      (D.naturalLift_of_tail_lt_head g (hD g)) hav.le hve le_rfl
    have hfS : f ∈ S := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨by rwa [hft], hfh⟩⟩
    have hTf := hreq ((edgeSetGraph_adj_iff_mem hD (F.edges ∪ S) f).mpr
      (Finset.mem_union_right _ hfS))
    simpa only [hft, hfh] using hTf

/-- The tree has no extra edge strictly below the head inside the displayed star. -/
theorem last_clique_tree_no_internal_edge (g : Edge D.area)
    (T : SimpleGraph (Fin n)) (hT : T.IsAcyclic)
    (hstar : ∀ v, g.tail ≤ v → v < g.head → T.Adj v g.head)
    {u v : Fin n} (hau : g.tail ≤ u) (huv : u < v) (hve : v < g.head) :
    ¬ T.Adj u v :=
  SimpleGraph.not_adj_of_adjacent_to_same hT huv.ne
    (hstar u hau (huv.trans hve)) (hstar v (hau.trans huv.le) hve)

include hD in
/-- The diagram path b-c-e-a forces omission of the shared edge b-a from the tree. -/
theorem last_clique_tree_omits_shared_edge (g f : Edge D.area)
    (hf : f ∈ F.edges) (T : SimpleGraph (Fin n)) (hT : T.IsAcyclic)
    (hFT : edgeSetGraph F.edges ≤ T)
    (hstar : ∀ v, g.tail ≤ v → v < g.head → T.Adj v g.head)
    (hba : f.tail < g.tail) (hac : g.tail < f.head) (hce : f.head < g.head) :
    ¬ T.Adj f.tail g.tail :=
  SimpleGraph.not_adj_of_three_edge_path hT hba hac hce
    (hFT ((edgeSetGraph_adj_iff_mem hD F.edges f).mpr hf))
    (hstar f.head hac.le hce) (hstar g.tail le_rfl (hac.trans hce))

end

end VerticalStripLLT.Circular.DiagramProof.CornerFamily
