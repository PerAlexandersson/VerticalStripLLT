import VerticalStripLLT.Components.CompatibleDiagramOrientations
import VerticalStripLLT.Components.ForwardFlipNormalization
import VerticalStripLLT.Components.BalancedCoverTransport

/-!
# Ordinary flips give original circular flips

Normalize the ordinary witness at its canonical ranks, then use the chosen
physical lifts in the original diagram. The retained compatible long edge
supplies the physical window bound. Only this direction is needed to make the
pullback of an original component a union of entire ordinary components.
-/

namespace VerticalStripLLT.Circular.Diagram

open Classical

noncomputable section

variable {n : ℕ} (D : Diagram n) (q : Fin n → ℤ) (σ : Fin n ≃ Fin n)
variable (hmono : StrictMono (q ∘ σ)) (hq : ∀ v, D.residue (q v) = v)
variable (hstrict : D.strict = ∅)

/-- Transfer an actual directed flip from the compatible ranked diagram. -/
def directedFlipFromCompatible
    {η ζ : Orientation (D.compatibleDiagram q σ hmono)}
    (w : DirectedFlipWitness (D.compatibleDiagram q σ hmono) η ζ) :
    DirectedFlipWitness D (D.orientationFromCompatible q σ hmono hq hstrict η)
      (D.orientationFromCompatible q σ hmono hq hstrict ζ) := by
  let w0 := w.normalizeForward (D.compatibleDiagram_forward q σ hmono)
  have hcover (ξ : Orientation (D.compatibleDiagram q σ hmono)) (i j : Fin n) :
      (D.compatibleDiagram q σ hmono).liftCover ξ.val (i.val : ℤ) (j.val : ℤ) ↔
        D.liftCover (D.orientationFromCompatible q σ hmono hq hstrict ξ).val
          (q (σ i)) (q (σ j)) :=
    (D.orientationFromCompatible q σ hmono hq hstrict ξ).liftCover_iff_of_balanced_relabel
      ξ (D.compatibleDiagram_forward q σ hmono) hq
      (D.orientationFromCompatible_balancedPotential q σ hmono hq hstrict ξ)
      σ hmono (D.orientationFromCompatible_selected q σ hmono hq hstrict ξ) i j
  have hord := w.canonical_triple_order (D.compatibleDiagram_forward q σ hmono)
  have hwindow : q (σ w.ebc.head) < q (σ w.eab.tail) + (n : ℤ) := by
    have hlong := (D.compatibleEdge_lift q σ hmono w.longEdge).2
    rw [← w.longEdge_tail, ← w.longEdge_head] at hlong
    have hlen : ((D.compatibleEdge q σ hmono w.longEdge).length.val : ℤ) < (n : ℤ) := by
      exact_mod_cast (D.compatibleEdge q σ hmono w.longEdge).length_lt_n
    lia
  refine {
    a := q (σ w.eab.tail)
    b := q (σ w.eab.head)
    c := q (σ w.ebc.head)
    cyclicWindow := ⟨hmono hord.1, hmono hord.2, hwindow⟩
    eab := D.compatibleEdge q σ hmono w.eab
    ebc := D.compatibleEdge q σ hmono w.ebc
    eab_normal := ?_
    ebc_normal := ?_
    ab_lift := D.compatibleEdge_lift q σ hmono w.eab
    bc_lift := ?_
    source_ab := ?_
    source_ac := ?_
    source_not_bc := ?_
    target_ac := ?_
    target_bc := ?_
    target_not_ab := ?_
    agree_elsewhere := ?_
  }
  · change D.compatibleEdge q σ hmono w.eab ∈ Finset.univ \ D.strict
    simp [hstrict]
  · change D.compatibleEdge q σ hmono w.ebc ∈ Finset.univ \ D.strict
    simp [hstrict]
  · rw [w.short_head_tail]
    exact D.compatibleEdge_lift q σ hmono w.ebc
  · exact (hcover η _ _).mp w0.source_ab
  · exact (hcover η _ _).mp w0.source_ac
  · intro h
    exact w0.source_not_bc ((hcover η _ _).mpr h)
  · exact (hcover ζ _ _).mp w0.target_ac
  · exact (hcover ζ _ _).mp w0.target_bc
  · intro h
    exact w0.target_not_ab ((hcover ζ _ _).mpr h)
  · intro e hab hbc
    change e ∈ η.val.image (D.compatibleEdge q σ hmono) ↔
      e ∈ ζ.val.image (D.compatibleEdge q σ hmono)
    have hagree (f : Edge (D.compatibleDiagram q σ hmono).area)
        (hf : D.compatibleEdge q σ hmono f = e) : f ∈ η.val ↔ f ∈ ζ.val := by
      apply w.agree_elsewhere f
      · intro heq
        apply hab
        exact hf.symm.trans (congrArg (D.compatibleEdge q σ hmono) heq)
      · intro heq
        apply hbc
        exact hf.symm.trans (congrArg (D.compatibleEdge q σ hmono) heq)
    constructor
    · intro he
      obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp he
      exact Finset.mem_image.mpr ⟨f, (hagree f hfe).mp hf, hfe⟩
    · intro he
      obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp he
      exact Finset.mem_image.mpr ⟨f, (hagree f hfe).mpr hf, hfe⟩

/-- Either direction of ordinary adjacency maps to original circular adjacency. -/
theorem flipFromCompatible
    {η ζ : Orientation (D.compatibleDiagram q σ hmono)}
    (h : Flip (D.compatibleDiagram q σ hmono) η ζ) :
    Flip D (D.orientationFromCompatible q σ hmono hq hstrict η)
      (D.orientationFromCompatible q σ hmono hq hstrict ζ) := by
  rcases h with w | w
  · exact Or.inl ⟨D.directedFlipFromCompatible q σ hmono hq hstrict w.some⟩
  · exact Or.inr ⟨D.directedFlipFromCompatible q σ hmono hq hstrict w.some⟩

end

end VerticalStripLLT.Circular.Diagram
