import VerticalStripLLT.Components.DiagramProof.PathTransport
import VerticalStripLLT.Components.DiagramProof.RelationPaths
import VerticalStripLLT.Components.EdgeSwap

/-! The ordinary short-edge flip requires only the two source covers. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {n : ℕ} {D : Diagram n}

/-- Exchange the two short edges inside the existing orientation type. -/
def swapShort (hforward : Forward D) (θ : Orientation D) (eab ebc : Edge D.area)
    (hbcnormal : ebc ∈ D.edgeData.normalEdges) : Orientation D :=
  D.orientationOfForward hforward (insert ebc (θ.val.erase eab)) (by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact hbcnormal
    · exact θ.property.1 (Finset.mem_erase.mp he).2)

/-- Source covers imply all target cover tests, hence an actual directed flip. -/
def directedFlipOfSourceCovers (hforward : Forward D) (θ : Orientation D)
    (eab ebc : Edge D.area) (habnormal : eab ∈ D.edgeData.normalEdges)
    (hbcnormal : ebc ∈ D.edgeData.normalEdges) (htail : ebc.tail = eab.head)
    (hsab : Cover θ eab.tail eab.head) (hsac : Cover θ eab.tail ebc.head) :
    DirectedFlipWitness D θ (swapShort hforward θ eab ebc hbcnormal) := by
  let η := swapShort hforward θ eab ebc hbcnormal
  have hbc : eab.head < ebc.head := htail ▸ hforward ebc
  have hswap : ∀ u v, D.edgeData.selected η.val u v ↔
      (u = eab.head ∧ v = ebc.head) ∨
        (D.edgeData.selected θ.val u v ∧ ¬ (u = eab.tail ∧ v = eab.head)) :=
    D.selected_short_swap_iff θ.val eab ebc habnormal rfl (Prod.ext htail rfl)
  obtain ⟨htac, htbc, hnoab⟩ := relationCover_short_swap
    (fun {_ _} hs => θ.selected_lt_of_forward hforward hs) hbc hsab hsac hswap
  apply directedFlipOfCovers hforward hsab.1 hbc eab ebc rfl rfl htail rfl
    habnormal hbcnormal hsab hsac ?_ htac htbc ?_ ?_
  · intro hsbc
    exact hsac.2.2 eab.head hsab.1 hbc ⟨hsab.2.1, hsbc.2.1⟩
  · exact fun h => hnoab h.2.1
  · intro e hneab hnebc
    change e ∈ θ.val ↔ e ∈ insert ebc (θ.val.erase eab)
    constructor
    · intro he
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hneab, he⟩)
    · intro he
      rcases Finset.mem_insert.mp he with he | he
      · exact (hnebc he).elim
      · exact (Finset.mem_erase.mp he).2

/-- The two-source-cover move lies in the same whole flip component. -/
theorem swapShort_mem_flipComponent (hforward : Forward D) (θ : Orientation D)
    (eab ebc : Edge D.area) (habnormal : eab ∈ D.edgeData.normalEdges)
    (hbcnormal : ebc ∈ D.edgeData.normalEdges) (htail : ebc.tail = eab.head)
    (hsab : Cover θ eab.tail eab.head) (hsac : Cover θ eab.tail ebc.head) :
    swapShort hforward θ eab ebc hbcnormal ∈ flipComponent D θ := by
  apply mem_flipComponent_iff.mpr
  exact Relation.ReflTransGen.single (Or.inl ⟨directedFlipOfSourceCovers
    hforward θ eab ebc habnormal hbcnormal htail hsab hsac⟩)

end

end VerticalStripLLT.Circular.DiagramProof
