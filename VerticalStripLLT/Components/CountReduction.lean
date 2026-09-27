import VerticalStripLLT.Components.ComponentWords
import VerticalStripLLT.Components.WordSwap

/-! The four-word count reduction after the two short-edge filters are paired. -/

namespace VerticalStripLLT.Components

noncomputable section

open Circular
open scoped Classical

variable {n : ℕ} {D : Diagram n}

private theorem selected_forward
    (hforward : ∀ e : Edge D.area, e.tail < e.head)
    (A : Finset (Edge D.area)) :
    ∀ ⦃u v : Fin n⦄, D.edgeData.selected A u v → u < v := by
  intro u v huv
  rcases huv with ⟨e, he, hu, hv⟩
  rw [← hu, ← hv]
  exact hforward e

/-- The four compatible-word counts satisfy the local four-term reduction once
the filters selecting the retained long edge have equal cardinality.  The four
full-word hypotheses are explicit so this adapter is independent of the
permutation-guard lemmas used elsewhere. -/
theorem componentWordCount_acb_add_bca_eq_cab_add_bac
    (θ : Circular.Orientation D) (ρ σ : List (Fin n))
    {a b c : Fin n} (hab : a < b) (hbc : b < c)
    (hforward : ∀ e : Edge D.area, e.tail < e.head)
    (hw_acb : fullWord (ρ ++ [a, c, b] ++ σ))
    (hw_bca : fullWord (ρ ++ [b, c, a] ++ σ))
    (hw_cab : fullWord (ρ ++ [c, a, b] ++ σ))
    (hw_bac : fullWord (ρ ++ [b, a, c] ++ σ))
    (hcard :
      ((compatibleComponent D θ (ρ ++ [a, c, b] ++ σ)).filter
          (fun η : Circular.Orientation D => D.edgeData.selected η.val a c)).card =
        ((compatibleComponent D θ (ρ ++ [b, a, c] ++ σ)).filter
          (fun η : Circular.Orientation D => D.edgeData.selected η.val a c)).card) :
    componentWordCount D θ (ρ ++ [a, c, b] ++ σ) +
        componentWordCount D θ (ρ ++ [b, c, a] ++ σ) =
      componentWordCount D θ (ρ ++ [c, a, b] ++ σ) +
        componentWordCount D θ (ρ ++ [b, a, c] ++ σ) := by
  classical
  let R_acb := compatibleComponent D θ (ρ ++ [a, c, b] ++ σ)
  let R_bac := compatibleComponent D θ (ρ ++ [b, a, c] ++ σ)
  have hcab :
      compatibleComponent D θ (ρ ++ [c, a, b] ++ σ) =
        R_acb.filter (fun η => ¬ D.edgeData.selected η.val a c) := by
    ext η
    simp only [mem_compatibleComponent, Finset.mem_filter]
    rw [wordCompatible_acb_cab_iff (D.edgeData.selected η.val)
      (selected_forward hforward η.val) ρ σ hab hbc]
    simp [R_acb, and_assoc]
  have hbca :
      compatibleComponent D θ (ρ ++ [b, c, a] ++ σ) =
        R_bac.filter (fun η => ¬ D.edgeData.selected η.val a c) := by
    ext η
    simp only [mem_compatibleComponent, Finset.mem_filter]
    rw [wordCompatible_bac_bca_iff (D.edgeData.selected η.val)
      (selected_forward hforward η.val) ρ σ hab hbc]
    simp [R_bac, and_assoc]
  have hsplit_acb :
      (R_acb.filter (fun η => D.edgeData.selected η.val a c)).card +
          (R_acb.filter (fun η => ¬ D.edgeData.selected η.val a c)).card =
        R_acb.card :=
    Finset.card_filter_add_card_filter_not
      (fun η => D.edgeData.selected η.val a c) (s := R_acb)
  have hsplit_bac :
      (R_bac.filter (fun η => D.edgeData.selected η.val a c)).card +
          (R_bac.filter (fun η => ¬ D.edgeData.selected η.val a c)).card =
        R_bac.card :=
    Finset.card_filter_add_card_filter_not
      (fun η => D.edgeData.selected η.val a c) (s := R_bac)
  have hcard' :
      (R_acb.filter (fun η => D.edgeData.selected η.val a c)).card =
        (R_bac.filter (fun η => D.edgeData.selected η.val a c)).card := by
    exact hcard
  have hsplit_acbZ :
      ((R_acb.filter (fun η => D.edgeData.selected η.val a c)).card : ℤ) +
          ((R_acb.filter (fun η => ¬ D.edgeData.selected η.val a c)).card : ℤ) =
        (R_acb.card : ℤ) := by
    exact_mod_cast hsplit_acb
  have hsplit_bacZ :
      ((R_bac.filter (fun η => D.edgeData.selected η.val a c)).card : ℤ) +
          ((R_bac.filter (fun η => ¬ D.edgeData.selected η.val a c)).card : ℤ) =
        (R_bac.card : ℤ) := by
    exact_mod_cast hsplit_bac
  have hcardZ :
      ((R_acb.filter (fun η => D.edgeData.selected η.val a c)).card : ℤ) =
        ((R_bac.filter (fun η => D.edgeData.selected η.val a c)).card : ℤ) := by
    exact_mod_cast hcard'
  rw [componentWordCount_of_full θ hw_acb,
    componentWordCount_of_full θ hw_bca,
    componentWordCount_of_full θ hw_cab,
    componentWordCount_of_full θ hw_bac, hcab, hbca]
  change (R_acb.card : ℤ) + (R_bac.filter
      (fun η => ¬ D.edgeData.selected η.val a c)).card =
    (R_acb.filter (fun η => ¬ D.edgeData.selected η.val a c)).card +
      (R_bac.card : ℤ)
  rw [← hsplit_acbZ, ← hsplit_bacZ, hcardZ]
  ring

end

end VerticalStripLLT.Components
