import VerticalStripLLT.Circular.BoundaryEdges
import VerticalStripLLT.Circular.PairColoringBridge
import VerticalStripLLT.Circular.PeriodicSwapResidue
import VerticalStripLLT.Circular.StrictEdgeInjectivity
import VerticalStripLLT.Circular.PairColoringSwap

/-! Exterior strict-edge invariance for an adjacent periodic swap. -/

namespace VerticalStripLLT.Circular
namespace Diagram

variable {n : ℕ} (D : Diagram n)

theorem strictEdge_tail_boundary {f : Edge D.area} (hf : f ∈ D.strict) :
    f.tail = D.residue (D.boundary (f.head.val : ℤ)) := by
  apply D.residue_tail_of_length
  · exact (Orientation.residue_intCast_eq (D := D) f.head).symm
  · have hc := D.strict_corner f hf
    rw [Diagram.boundary, Orientation.residue_intCast_eq, hc.1]
    ring

theorem firstBounce_strict_exterior_swap
    {e : Edge D.area} (he : e ∈ D.strict) (p : ℤ)
    (htail : e.tail = D.residue p)
    (hleft : ¬ D.strictAt p) (hright : ¬ D.strictAt (p + 1))
    (havoid : ∀ z k : ℤ, D.boundary z ≠ p + 1 + (n : ℤ) * k) :
    ((D.pairGraph.strictEdges.erase (e.tail, e.head)).map
        (swapVertexPair (D.residue p) (D.residue (p + 1)))) =
      D.pairGraph.strictEdges.erase (e.tail, e.head) := by
  classical
  let a : Fin n := D.residue p
  let b : Fin n := D.residue (p + 1)
  have hhead_ne_a : ∀ {f : Edge D.area}, f ∈ D.strict → f ≠ e → f.head ≠ a := by
    intro f hf _hfe hfa
    apply hleft
    exact ⟨f, hf, hfa.trans rfl⟩
  have hhead_ne_b : ∀ {f : Edge D.area}, f ∈ D.strict → f ≠ e → f.head ≠ b := by
    intro f hf _hfe hfb
    apply hright
    exact ⟨f, hf, hfb.trans rfl⟩
  have htail_ne_a : ∀ {f : Edge D.area}, f ∈ D.strict → f ≠ e → f.tail ≠ a := by
    intro f hf hfe hfa
    apply hfe
    exact D.strict_edge_eq_of_tail_eq hf he (hfa.trans htail.symm)
  have htail_ne_b : ∀ {f : Edge D.area}, f ∈ D.strict → f ≠ e → f.tail ≠ b := by
    intro f hf _hfe hfb
    have hboundary := D.strictEdge_tail_boundary hf
    have hres : D.residue (D.boundary (f.head.val : ℤ)) =
        D.residue (p + 1) := by
      exact hboundary.symm.trans hfb
    have hmod := (D.residue_eq_iff_mod_sub_zero).mp hres
    obtain ⟨k, hk⟩ : ∃ k : ℤ,
        D.boundary (f.head.val : ℤ) = p + 1 + (n : ℤ) * k := by
      refine ⟨(D.boundary (f.head.val : ℤ) - (p + 1)) / n, ?_⟩
      have hdiv := Int.mul_ediv_add_emod
        (D.boundary (f.head.val : ℤ) - (p + 1)) (n : ℤ)
      rw [hmod] at hdiv
      lia
    exact havoid _ _ hk
  have hfixed : ∀ {f : Edge D.area}, f ∈ D.strict → f ≠ e →
      swapVertexPair a b (f.tail, f.head) = (f.tail, f.head) := by
    intro f hf hfe
    have hta := htail_ne_a hf hfe
    have htb := htail_ne_b hf hfe
    have hha := hhead_ne_a hf hfe
    have hhb := hhead_ne_b hf hfe
    simp only [swapVertexPair_apply, Equiv.swap_apply_of_ne_of_ne hta htb,
      Equiv.swap_apply_of_ne_of_ne hha hhb]
  have hfixedpair : ∀ y ∈ D.pairGraph.strictEdges.erase (e.tail, e.head),
      swapVertexPair a b y = y := by
    intro y hy
    obtain ⟨hne, hy⟩ := Finset.mem_erase.mp hy
    obtain ⟨f, hf, hp⟩ := (D.mem_pairGraph_strict_iff y).mp hy
    have hfe : f ≠ e := by
      rintro rfl
      exact hne hp.symm
    rw [← hp]
    exact hfixed hf hfe
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_map.mp hx
    rw [hfixedpair y hy] at hxy
    simpa only [hxy] using hy
  · intro hx
    exact Finset.mem_map.mpr ⟨x, hx, hfixedpair x hx⟩

end Diagram
end VerticalStripLLT.Circular
