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
  have htarget := relationCover_short_swap
    (fun {_ _} hs => θ.selected_lt_of_forward hforward hs) hbc hsab hsac hswap
  apply directedFlipOfCovers hforward hsab.1 hbc eab ebc rfl rfl htail rfl
    habnormal hbcnormal hsab hsac ?_ htarget.1 htarget.2.1 ?_ ?_
  · intro hsbc
    exact hsac.2.2 eab.head hsab.1 hbc ⟨hsab.2.1, hsbc.2.1⟩
  · exact fun h => htarget.2.2 h.2.1
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

/-- Any selected natural long supplies its two proper normal shorts. -/
theorem exists_normalShortEdges_of_selected (hforward : Forward D) (θ : Orientation D)
    (a b c : Fin n) (hsac : D.edgeData.selected θ.val a c) (hab : a < b) (hbc : b < c) :
    ∃ eab ebc : Edge D.area,
      eab ∈ D.edgeData.normalEdges ∧ ebc ∈ D.edgeData.normalEdges ∧
        eab.tail = a ∧ eab.head = b ∧ ebc.tail = b ∧ ebc.head = c := by
  obtain ⟨e, _, het, heh⟩ := hsac
  change e.tail = a at het
  change e.head = c at heh
  have hlong : D.naturalLift e (a.val : ℤ) (c.val : ℤ) := by
    simpa only [het, heh] using D.naturalLift_of_tail_lt_head e (hforward e)
  obtain ⟨eab, ebc, habnormal, hbcnormal, hablift, hbclift⟩ :=
    D.normalShortEdges_of_naturalLift (b := (b.val : ℤ)) hlong
      (by exact_mod_cast hab) (by exact_mod_cast hbc)
  have endpoints {f : Edge D.area} {u v : Fin n}
      (hf : D.naturalLift f (u.val : ℤ) (v.val : ℤ)) : f.tail = u ∧ f.head = v := by
    constructor
    · exact (Orientation.residue_intCast_eq u).symm.trans hf.1 |>.symm
    · have h := (D.naturalLift_of_tail_lt_head f (hforward f)).2
      have ht : f.tail = u := ((Orientation.residue_intCast_eq u).symm.trans hf.1).symm
      rw [ht] at h
      apply Fin.ext
      have heq : (f.head.val : ℤ) = (v.val : ℤ) := h.trans hf.2.symm
      exact_mod_cast heq
  obtain ⟨habtail, habhead⟩ := endpoints hablift
  obtain ⟨hbctail, hbchead⟩ := endpoints hbclift
  exact ⟨eab, ebc, habnormal, hbcnormal, habtail, habhead, hbctail, hbchead⟩

/-- The long cover supplies both natural normal shorts; no edge data need be assumed. -/
theorem exists_directedFlip_of_sourceCovers (hforward : Forward D) (θ : Orientation D)
    (a b c : Fin n) (hsab : Cover θ a b) (hsac : Cover θ a c) (hbc : b < c) :
    ∃ η : Orientation D, ∃ w : DirectedFlipWitness D θ η,
      w.eab.tail = a ∧ w.eab.head = b ∧ w.ebc.tail = b ∧ w.ebc.head = c := by
  obtain ⟨eab, ebc, habnormal, hbcnormal, habtail, habhead, hbctail, hbchead⟩ :=
    exists_normalShortEdges_of_selected hforward θ a b c
      (selected_of_cover hforward hsac) hsab.1 hbc
  have hsourceab : Cover θ eab.tail eab.head := by simpa only [habtail, habhead] using hsab
  have hsourceac : Cover θ eab.tail ebc.head := by simpa only [habtail, hbchead] using hsac
  exact ⟨_, directedFlipOfSourceCovers hforward θ eab ebc habnormal hbcnormal
    (hbctail.trans habhead.symm) hsourceab hsourceac, habtail, habhead, hbctail, hbchead⟩

/-- Source-cover flips with an exact selected-relation endpoint, ready for sweep induction. -/
theorem exists_outgoingSwap_of_covers (hforward : Forward D) (θ : Orientation D)
    (a b c : Fin n) (hsab : Cover θ a b) (hsac : Cover θ a c) (hbc : b < c) :
    ∃ η : Orientation D, Flip D θ η ∧ Cover η a c ∧ Cover η b c ∧
      (∀ u v, D.edgeData.selected η.val u v ↔
        (u = b ∧ v = c) ∨
          (D.edgeData.selected θ.val u v ∧ ¬ (u = a ∧ v = b))) := by
  obtain ⟨η, w, hat, hah, hbt, hbh⟩ :=
    exists_directedFlip_of_sourceCovers hforward θ a b c hsab hsac hbc
  have hswap : ∀ u v, D.edgeData.selected η.val u v ↔
      (u = b ∧ v = c) ∨ (D.edgeData.selected θ.val u v ∧ ¬ (u = a ∧ v = b)) := by
    intro u v
    rw [w.target_eq_source_swap]
    exact D.selected_short_swap_iff θ.val w.eab w.ebc w.eab_normal
      (Prod.ext hat hah) (Prod.ext hbt hbh) u v
  have ht := relationCover_short_swap
    (fun {_ _} hs => θ.selected_lt_of_forward hforward hs) hbc hsab hsac hswap
  exact ⟨η, Or.inl ⟨w⟩, ht.1, ht.2.1, hswap⟩

end

end VerticalStripLLT.Circular.DiagramProof
