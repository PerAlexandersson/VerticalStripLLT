import VerticalStripLLT.Components.DiagramProof.ShortFlip
import VerticalStripLLT.Components.DiagramProof.SweepCovers

/-! Actual incoming short-edge flips, used in backward sweeps and restoration. -/

namespace VerticalStripLLT.Circular.DiagramProof

noncomputable section

variable {n : ℕ} {D : Diagram n}

/-- Exchange the incoming short for the outgoing one, deriving all other cover tests. -/
def reverseFlipOfSourceCovers (hforward : Forward D) (θ : Orientation D)
    (eab ebc : Edge D.area) (habnormal : eab ∈ D.edgeData.normalEdges)
    (hbcnormal : ebc ∈ D.edgeData.normalEdges) (htail : ebc.tail = eab.head)
    (hsbc : Cover θ eab.head ebc.head) (hsac : Cover θ eab.tail ebc.head) :
    DirectedFlipWitness D (swapShort hforward θ ebc eab habnormal) θ := by
  classical
  let η := swapShort hforward θ ebc eab habnormal
  have hab : eab.tail < eab.head := hforward eab
  have hbc : eab.head < ebc.head := htail ▸ hforward ebc
  have hswap : ∀ u v, D.edgeData.selected η.val u v ↔
      (u = eab.tail ∧ v = eab.head) ∨
        (D.edgeData.selected θ.val u v ∧ ¬ (u = eab.head ∧ v = ebc.head)) := by
    intro u v
    change D.edgeData.selected (insert eab (θ.val.erase ebc)) u v ↔ _
    rw [D.selected_insert_erase_normal_iff θ.val ebc eab hbcnormal]
    simp only [htail, eq_comm]
  have ht := relationCover_incoming_swap
    (fun {_ _} hs => θ.selected_lt_of_forward hforward hs) hab hsbc hsac hswap
  apply directedFlipOfCovers hforward hab hbc eab ebc rfl rfl htail rfl
    habnormal hbcnormal ht.2.1 ht.1 (fun h => ht.2.2 h.2.1) hsac hsbc ?_ ?_
  · intro hsab
    exact hsac.2.2 eab.head hab hbc ⟨hsab.2.1, hsbc.2.1⟩
  · intro e heab hebc
    change e ∈ insert eab (θ.val.erase ebc) ↔ e ∈ θ.val
    constructor
    · intro he
      rcases Finset.mem_insert.mp he with he | he
      · exact (heab he).elim
      · exact (Finset.mem_erase.mp he).2
    · intro he
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hebc, he⟩)

theorem incomingSwap_mem_flipComponent (hforward : Forward D) (θ : Orientation D)
    (eab ebc : Edge D.area) (habnormal : eab ∈ D.edgeData.normalEdges)
    (hbcnormal : ebc ∈ D.edgeData.normalEdges) (htail : ebc.tail = eab.head)
    (hsbc : Cover θ eab.head ebc.head) (hsac : Cover θ eab.tail ebc.head) :
    swapShort hforward θ ebc eab habnormal ∈ flipComponent D θ := by
  apply mem_flipComponent_iff.mpr
  exact Relation.ReflTransGen.single (Or.inr ⟨reverseFlipOfSourceCovers
    hforward θ eab ebc habnormal hbcnormal htail hsbc hsac⟩)

/-- Two incoming covers supply a reverse directed flip with explicit short endpoints. -/
theorem exists_reverseFlip_of_sourceCovers (hforward : Forward D) (θ : Orientation D)
    (a b c : Fin n) (hsbc : Cover θ b c) (hsac : Cover θ a c) (hab : a < b) :
    ∃ η : Orientation D, ∃ w : DirectedFlipWitness D η θ,
      w.eab.tail = a ∧ w.eab.head = b ∧ w.ebc.tail = b ∧ w.ebc.head = c := by
  obtain ⟨eab, ebc, habnormal, hbcnormal, hat, hah, hbt, hbh⟩ :=
    exists_normalShortEdges_of_selected hforward θ a b c
      (selected_of_cover hforward hsac) hab hsbc.1
  have hsourcebc : Cover θ eab.head ebc.head := by simpa only [hah, hbh] using hsbc
  have hsourceac : Cover θ eab.tail ebc.head := by simpa only [hat, hbh] using hsac
  exact ⟨_, reverseFlipOfSourceCovers hforward θ eab ebc habnormal hbcnormal
    (hbt.trans hah.symm) hsourcebc hsourceac, hat, hah, hbt, hbh⟩

/-- The incoming move also supplies its exact selected-relation endpoint. -/
theorem exists_incomingSwap_of_covers (hforward : Forward D) (θ : Orientation D)
    (a b c : Fin n) (hsbc : Cover θ b c) (hsac : Cover θ a c) (hab : a < b) :
    ∃ η : Orientation D, Flip D θ η ∧ Cover η a c ∧ Cover η a b ∧
      (∀ u v, D.edgeData.selected η.val u v ↔
        (u = a ∧ v = b) ∨
          (D.edgeData.selected θ.val u v ∧ ¬ (u = b ∧ v = c))) := by
  classical
  obtain ⟨eab, ebc, habnormal, hbcnormal, hat, hah, hbt, hbh⟩ :=
    exists_normalShortEdges_of_selected hforward θ a b c
      (selected_of_cover hforward hsac) hab hsbc.1
  have hsourcebc : Cover θ eab.head ebc.head := by simpa only [hah, hbh] using hsbc
  have hsourceac : Cover θ eab.tail ebc.head := by simpa only [hat, hbh] using hsac
  let w := reverseFlipOfSourceCovers hforward θ eab ebc habnormal hbcnormal
    (hbt.trans hah.symm) hsourcebc hsourceac
  let η := swapShort hforward θ ebc eab habnormal
  have hswap : ∀ u v, D.edgeData.selected η.val u v ↔
      (u = a ∧ v = b) ∨
        (D.edgeData.selected θ.val u v ∧ ¬ (u = b ∧ v = c)) := by
    intro u v
    change D.edgeData.selected (insert eab (θ.val.erase ebc)) u v ↔ _
    rw [D.selected_insert_erase_normal_iff θ.val ebc eab hbcnormal]
    simp only [hat, hah, hbt, hbh, eq_comm]
  have ht := relationCover_incoming_swap
    (fun {_ _} hs => θ.selected_lt_of_forward hforward hs) hab hsbc hsac hswap
  exact ⟨η, Or.inr ⟨w⟩, ht.1, ht.2.1, hswap⟩

end

end VerticalStripLLT.Circular.DiagramProof
