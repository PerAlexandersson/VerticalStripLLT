import VerticalStripLLT.Components.WordProof.ComponentBijection
import VerticalStripLLT.Components.WordProof.CountReduction
import VerticalStripLLT.Components.WordProof.WordNeutral

/-! The ordinary component functional and its four-word relation identity. -/

namespace VerticalStripLLT.Components

noncomputable section

open Circular
open scoped Classical

variable {n : ℕ} {D : Diagram n}

private theorem selected_ac_filter_eq_empty_of_no_naturalLift
    (θ : Circular.Orientation D) (w : List (Fin n)) {a c : Fin n}
    (hforward : ∀ e : Edge D.area, e.tail < e.head)
    (hno : ¬ ∃ e : Edge D.area,
      D.naturalLift e (a.val : ℤ) (c.val : ℤ)) :
    (compatibleComponent D θ w).filter
        (fun η : Circular.Orientation D => D.edgeData.selected η.val a c) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro η hη hselected
  rcases hselected with ⟨e, he, htail, hhead⟩
  change e.tail = a at htail
  change e.head = c at hhead
  apply hno
  refine ⟨e, ?_⟩
  have heforward := D.naturalLift_of_tail_lt_head e (hforward e)
  simpa [htail, hhead] using heforward

/-- The ordinary four-term identity for the component count. -/
private theorem componentWordCount_four_of_full
    (θ : Circular.Orientation D) (ρ σ : List (Fin n))
    {a b c : Fin n} (hab : a < b) (hbc : b < c)
    (hforward : ∀ e : Edge D.area, e.tail < e.head)
    (hw : fullWord (ρ ++ [a, c, b] ++ σ)) :
    componentWordCount D θ (ρ ++ [a, c, b] ++ σ) +
        componentWordCount D θ (ρ ++ [b, c, a] ++ σ) =
      componentWordCount D θ (ρ ++ [c, a, b] ++ σ) +
        componentWordCount D θ (ρ ++ [b, a, c] ++ σ) := by
  have hw_bca := (fullWord_acb_bca_iff ρ σ).mp hw
  have hw_cab := (fullWord_acb_cab_iff ρ σ).mp hw
  have hw_bac := (fullWord_acb_bac_iff ρ σ).mp hw
  by_cases heac : ∃ e : Edge D.area,
      D.naturalLift e (a.val : ℤ) (c.val : ℤ)
  · obtain ⟨eac, hacLift⟩ := heac
    have habZ : (a.val : ℤ) < (b.val : ℤ) := by exact_mod_cast hab
    have hbcZ : (b.val : ℤ) < (c.val : ℤ) := by exact_mod_cast hbc
    obtain ⟨eab, ebc, heab, hebc, habLift, hbcLift⟩ :=
      D.normalShortEdges_of_naturalLift hacLift habZ hbcZ
    have hcard := selectedLong_card_eq_of_naturalLift hforward θ ρ σ hab hbc hw
      eab ebc eac heab hebc habLift hbcLift hacLift
    exact componentWordCount_acb_add_bca_eq_cab_add_bac θ ρ σ hab hbc hforward
      hw hw_bca hw_cab hw_bac hcard
  · have hacb_empty :=
      selected_ac_filter_eq_empty_of_no_naturalLift θ
        (ρ ++ [a, c, b] ++ σ) hforward heac
    have hbac_empty :=
      selected_ac_filter_eq_empty_of_no_naturalLift θ
        (ρ ++ [b, a, c] ++ σ) hforward heac
    have hcard :
        ((compatibleComponent D θ (ρ ++ [a, c, b] ++ σ)).filter
              (fun η : Circular.Orientation D => D.edgeData.selected η.val a c)).card =
          ((compatibleComponent D θ (ρ ++ [b, a, c] ++ σ)).filter
              (fun η : Circular.Orientation D => D.edgeData.selected η.val a c)).card := by
      rw [hacb_empty, hbac_empty, Finset.card_empty]
    exact componentWordCount_acb_add_bca_eq_cab_add_bac θ ρ σ hab hbc hforward
      hw hw_bca hw_cab hw_bac hcard

/-- The ordinary four-term identity, including all invalid contextual words. -/
theorem componentWordCount_four
    (θ : Circular.Orientation D) (ρ σ : List (Fin n))
    {a b c : Fin n} (hab : a < b) (hbc : b < c)
    (hforward : ∀ e : Edge D.area, e.tail < e.head) :
    componentWordCount D θ (ρ ++ [a, c, b] ++ σ) +
        componentWordCount D θ (ρ ++ [b, c, a] ++ σ) =
      componentWordCount D θ (ρ ++ [c, a, b] ++ σ) +
        componentWordCount D θ (ρ ++ [b, a, c] ++ σ) := by
  by_cases hw : fullWord (ρ ++ [a, c, b] ++ σ)
  · exact componentWordCount_four_of_full θ ρ σ hab hbc hforward hw
  · have hwbca : ¬ fullWord (ρ ++ [b, c, a] ++ σ) := by
      intro h
      exact hw ((fullWord_acb_bca_iff ρ σ).mpr h)
    have hwcab : ¬ fullWord (ρ ++ [c, a, b] ++ σ) := by
      intro h
      exact hw ((fullWord_acb_cab_iff ρ σ).mpr h)
    have hwbac : ¬ fullWord (ρ ++ [b, a, c] ++ σ) := by
      intro h
      exact hw ((fullWord_acb_bac_iff ρ σ).mpr h)
    rw [componentWordCount_of_not_full θ hw,
      componentWordCount_of_not_full θ hwbca,
      componentWordCount_of_not_full θ hwcab,
      componentWordCount_of_not_full θ hwbac]

/-- The component count annihilates all contextual word relations in the
ordinary forward case. -/
theorem componentWordLinear_relations_le_ker
    (θ : Circular.Orientation D)
    (hforward : ∀ e : Edge D.area, e.tail < e.head) :
    wordRelations (V := Fin n) ≤
      LinearMap.ker (componentWordLinear D θ) := by
  apply relations_le_ker (componentWordLinear D θ)
  · exact fun w hw => componentWordLinear_repeated θ hw
  · intro ρ σ a b c hab hbc
    simpa only [componentWordLinear_basisWord] using
      componentWordCount_four θ ρ σ hab hbc hforward

/-- The ordinary component functional on the contextual word quotient. -/
noncomputable def componentWordFunctional
    (θ : Circular.Orientation D)
    (hforward : ∀ e : Edge D.area, e.tail < e.head) :
    WordQuotient (Fin n) →ₗ[ℤ] ℤ :=
  (wordRelations (V := Fin n)).liftQ (componentWordLinear D θ)
    (componentWordLinear_relations_le_ker θ hforward)

@[simp]
theorem componentWordFunctional_mk_basisWord
    (θ : Circular.Orientation D)
    (hforward : ∀ e : Edge D.area, e.tail < e.head)
    (w : List (Fin n)) :
    componentWordFunctional θ hforward
        ((wordRelations (V := Fin n)).mkQ (basisWord w)) =
      componentWordCount D θ w := by
  change componentWordLinear D θ (basisWord w) =
    componentWordCount D θ w
  exact componentWordLinear_basisWord θ w

end

end VerticalStripLLT.Components
