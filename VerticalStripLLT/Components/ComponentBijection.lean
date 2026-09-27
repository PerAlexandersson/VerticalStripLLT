import VerticalStripLLT.Components.ComponentSwap
import VerticalStripLLT.Components.WordNeutral

/-! The conditional short-edge bijection inside one complete flip component. -/

namespace VerticalStripLLT.Components

open Circular
open scoped Classical

variable {n : ℕ} {D : Diagram n}

private theorem selected_forward
    (hforward : ∀ e : Edge D.area, e.tail < e.head)
    (A : Finset (Edge D.area)) :
    ∀ ⦃u v : Fin n⦄, D.edgeData.selected A u v → u < v := by
  intro u v h
  rcases h with ⟨e, _, hu, hv⟩
  rw [← hu, ← hv]
  exact hforward e

private theorem compatible_acb_not_bc (R : Fin n → Fin n → Prop)
    (ρ σ : List (Fin n)) {a b c : Fin n}
    (hw : wordCompatible R (ρ ++ [a, c, b] ++ σ)) : ¬ R b c := by
  have ht : wordCompatible R [a, c, b] := by
    simp only [wordCompatible, List.pairwise_append] at hw ⊢
    grind
  simp [wordCompatible, List.pairwise_cons] at ht
  grind

private theorem compatible_bac_not_ab (R : Fin n → Fin n → Prop)
    (ρ σ : List (Fin n)) {a b c : Fin n}
    (hw : wordCompatible R (ρ ++ [b, a, c] ++ σ)) : ¬ R a b := by
  have ht : wordCompatible R [b, a, c] := by
    simp only [wordCompatible, List.pairwise_append] at hw ⊢
    grind
  simp [wordCompatible, List.pairwise_cons] at ht
  grind

/-- The selected-long-edge occurrences in the two words are paired within the
original complete component. The map exchanges the shorts when one is selected
and retains the state when both are absent. -/
theorem selectedLong_card_eq_of_naturalLift
    (hforward : ∀ e : Edge D.area, e.tail < e.head)
    (base : Circular.Orientation D) (ρ σ : List (Fin n))
    {a b c : Fin n} (hab : a < b) (hbc : b < c)
    (hw : fullWord (ρ ++ [a, c, b] ++ σ))
    (eab ebc eac : Edge D.area)
    (heab : eab ∈ D.edgeData.normalEdges) (hebc : ebc ∈ D.edgeData.normalEdges)
    (habLift : D.naturalLift eab (a.val : ℤ) (b.val : ℤ))
    (hbcLift : D.naturalLift ebc (b.val : ℤ) (c.val : ℤ))
    (hacLift : D.naturalLift eac (a.val : ℤ) (c.val : ℤ)) :
    ((compatibleComponent D base (ρ ++ [a, c, b] ++ σ)).filter
        (fun θ : Circular.Orientation D => D.edgeData.selected θ.val a c)).card =
      ((compatibleComponent D base (ρ ++ [b, a, c] ++ σ)).filter
        (fun θ : Circular.Orientation D => D.edgeData.selected θ.val a c)).card := by
  classical
  let s := (compatibleComponent D base (ρ ++ [a, c, b] ++ σ)).filter
    (fun θ : Circular.Orientation D => D.edgeData.selected θ.val a c)
  let t := (compatibleComponent D base (ρ ++ [b, a, c] ++ σ)).filter
    (fun θ : Circular.Orientation D => D.edgeData.selected θ.val a c)
  let f : Circular.Orientation D → Circular.Orientation D := fun θ =>
    if eab ∈ θ.val then exchangeOrientation hforward θ eab ebc hebc else θ
  let g : Circular.Orientation D → Circular.Orientation D := fun θ =>
    if ebc ∈ θ.val then exchangeOrientation hforward θ ebc eab heab else θ
  change s.card = t.card
  have hs (θ : Circular.Orientation D) : θ ∈ s ↔
      θ ∈ flipComponent D base ∧
        wordCompatible (D.edgeData.selected θ.val) (ρ ++ [a, c, b] ++ σ) ∧
          D.edgeData.selected θ.val a c := by
    simp only [s, Finset.mem_filter, mem_compatibleComponent, and_assoc]
  have ht (θ : Circular.Orientation D) : θ ∈ t ↔
      θ ∈ flipComponent D base ∧
        wordCompatible (D.edgeData.selected θ.val) (ρ ++ [b, a, c] ++ σ) ∧
          D.edgeData.selected θ.val a c := by
    simp only [t, Finset.mem_filter, mem_compatibleComponent, and_assoc]
  have hfullTarget : fullWord (ρ ++ [b, a, c] ++ σ) :=
    (fullWord_acb_bac_iff ρ σ).mp hw
  obtain ⟨habTail, habHead⟩ := Prod.mk.inj (naturalLift_endpoints habLift)
  obtain ⟨hbcTail, hbcHead⟩ := Prod.mk.inj (naturalLift_endpoints hbcLift)
  obtain ⟨hacTail, hacHead⟩ := Prod.mk.inj (naturalLift_endpoints hacLift)
  have habSelected (θ : Circular.Orientation D) :
      D.edgeData.selected θ.val a b ↔ eab ∈ θ.val := by
    simpa only [habTail, habHead] using selected_normal_iff_mem θ.val eab heab
  have hbcSelected (θ : Circular.Orientation D) :
      D.edgeData.selected θ.val b c ↔ ebc ∈ θ.val := by
    simpa only [hbcTail, hbcHead] using selected_normal_iff_mem θ.val ebc hebc
  have hlongAb : eac ≠ eab := by
    intro heq
    have hh := congrArg Edge.head heq
    rw [hacHead, habHead] at hh
    exact hbc.ne hh.symm
  have hlongBc : eac ≠ ebc := by
    intro heq
    have hh := congrArg Edge.tail heq
    rw [hacTail, hbcTail] at hh
    exact hab.ne hh
  have hretain (θ : Circular.Orientation D) (e f : Edge D.area)
      (hf : f ∈ D.edgeData.normalEdges) (hne : eac ≠ e)
      (hac : D.edgeData.selected θ.val a c) :
      D.edgeData.selected (exchangeOrientation hforward θ e f hf).val a c := by
    apply (selected_iff_mem_of_naturalLift _ eac hacLift).mpr
    have hm := (selected_iff_mem_of_naturalLift θ.val eac hacLift).mp hac
    rcases Finset.mem_union.mp hm with hstrict | hnormal
    · exact Finset.mem_union.mpr (Or.inl hstrict)
    · exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, hnormal⟩)))
  have hsourceBc (θ : Circular.Orientation D)
      (hθ : wordCompatible (D.edgeData.selected θ.val) (ρ ++ [a, c, b] ++ σ)) :
      ebc ∉ θ.val := by
    intro hm
    exact compatible_acb_not_bc _ ρ σ hθ ((hbcSelected θ).mpr hm)
  have htargetAb (θ : Circular.Orientation D)
      (hθ : wordCompatible (D.edgeData.selected θ.val) (ρ ++ [b, a, c] ++ σ)) :
      eab ∉ θ.val := by
    intro hm
    exact compatible_bac_not_ab _ ρ σ hθ ((habSelected θ).mpr hm)
  have hf : ∀ θ, θ ∈ s → f θ ∈ t := by
    intro θ hθ
    obtain ⟨hbase, hword, hac⟩ := (hs θ).mp hθ
    by_cases hshort : eab ∈ θ.val
    · have hx := exchangeOrientation_forward hforward θ ρ σ hab hbc hw hword
        eab ebc eac heab hebc habLift hbcLift hacLift hshort
        ((selected_iff_mem_of_naturalLift θ.val eac hacLift).mp hac)
      have hm := (ht (exchangeOrientation hforward θ eab ebc hebc)).mpr
        ⟨mem_flipComponent_of_directedFlip hbase hx.2, hx.1,
          hretain θ eab ebc hebc hlongAb hac⟩
      simpa only [f, ite_eq_left hshort] using hm
    · have hnotAb : ¬ D.edgeData.selected θ.val a b :=
        fun h => hshort ((habSelected θ).mp h)
      have hnotBc := compatible_acb_not_bc _ ρ σ hword
      have hword' := (wordCompatible_acb_bac_iff_of_no_short
        (D.edgeData.selected θ.val) (selected_forward hforward θ.val)
        ρ σ hab hbc hnotAb hnotBc).mp hword
      simpa only [f, ite_eq_right hshort] using (ht θ).mpr ⟨hbase, hword', hac⟩
  have hg : ∀ θ, θ ∈ t → g θ ∈ s := by
    intro θ hθ
    obtain ⟨hbase, hword, hac⟩ := (ht θ).mp hθ
    by_cases hshort : ebc ∈ θ.val
    · have hx := exchangeOrientation_backward hforward θ ρ σ hab hbc hfullTarget hword
        eab ebc eac heab hebc habLift hbcLift hacLift hshort
        ((selected_iff_mem_of_naturalLift θ.val eac hacLift).mp hac)
      have hm := (hs (exchangeOrientation hforward θ ebc eab heab)).mpr
        ⟨mem_flipComponent_of_reverse_directedFlip hbase hx.2, hx.1,
          hretain θ ebc eab heab hlongBc hac⟩
      simpa only [g, ite_eq_left hshort] using hm
    · have hnotAb := compatible_bac_not_ab _ ρ σ hword
      have hnotBc : ¬ D.edgeData.selected θ.val b c :=
        fun h => hshort ((hbcSelected θ).mp h)
      have hword' := (wordCompatible_acb_bac_iff_of_no_short
        (D.edgeData.selected θ.val) (selected_forward hforward θ.val)
        ρ σ hab hbc hnotAb hnotBc).mpr hword
      simpa only [g, ite_eq_right hshort] using (hs θ).mpr ⟨hbase, hword', hac⟩
  have hgf : ∀ θ, θ ∈ s → g (f θ) = θ := by
    intro θ hθ
    have hnot := hsourceBc θ ((hs θ).mp hθ).2.1
    by_cases hshort : eab ∈ θ.val
    · have hnew : ebc ∈ (exchangeOrientation hforward θ eab ebc hebc).val := by
        simp only [exchangeOrientation_val, Finset.mem_insert_self]
      simpa only [f, ite_eq_left hshort, g, ite_eq_left hnew] using
        exchangeOrientation_inverse hforward θ eab ebc heab hebc hshort hnot
    · simp only [f, ite_eq_right hshort, g, ite_eq_right hnot]
  have hfg : ∀ θ, θ ∈ t → f (g θ) = θ := by
    intro θ hθ
    have hnot := htargetAb θ ((ht θ).mp hθ).2.1
    by_cases hshort : ebc ∈ θ.val
    · have hnew : eab ∈ (exchangeOrientation hforward θ ebc eab heab).val := by
        simp only [exchangeOrientation_val, Finset.mem_insert_self]
      simpa only [g, ite_eq_left hshort, f, ite_eq_left hnew] using
        exchangeOrientation_inverse hforward θ ebc eab hebc heab hshort hnot
    · simp only [g, ite_eq_right hshort, f, ite_eq_right hnot]
  exact Finset.card_nbij' f g hf hg hgf hfg

end VerticalStripLLT.Components
