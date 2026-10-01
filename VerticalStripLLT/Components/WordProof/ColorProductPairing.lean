import VerticalStripLLT.Components.WordProof.ColorProductPositions
import VerticalStripLLT.Components.WordProof.ColoringSubwords
import VerticalStripLLT.Components.WordProof.ComponentColoring
import VerticalStripLLT.Components.WordProof.WordProductExpansion

/-! The finite ordered color product pairs to the actual component's strict enumerator. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace VerticalStripLLT.Components

open scoped BigOperators TensorProduct
open Circular

noncomputable section

theorem sum_subwords_eq_sum_colorings {C V A : Type*}
    [Fintype C] [Fintype V] [DecidableEq C] [DecidableEq V] [AddCommMonoid A]
    (L : List (C × V)) (hL : fullWord L) (f : List (C × V) → A)
    (hf : ∀ S, ¬ fullWord (S.map Prod.snd) → f S = 0) :
    (L.sublists'.map f).sum = ∑ c : V → C, f (selectedColorSubword L c) := by
  classical
  rw [← List.sum_toFinset f (List.nodup_sublists'.mpr hL.1)]
  let T := L.sublists'.toFinset.filter (fun S => fullWord (S.map Prod.snd))
  have hfilter : ∑ S ∈ L.sublists'.toFinset, f S = ∑ S ∈ T, f S := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro S hS hnot
    exact hf S (fun h => hnot (Finset.mem_filter.mpr ⟨hS, h⟩))
  rw [hfilter]
  symm
  apply Finset.sum_bij (fun c _ => selectedColorSubword L c)
  · intro c _
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr
      (List.mem_sublists'.mpr (selectedColorSubword_sublist L c)),
      fullWord_map_snd_selectedColorSubword hL c⟩
  · intro c _ d _ h
    obtain ⟨e, he, hu⟩ := existsUnique_selectedColorSubword hL
      (selectedColorSubword_sublist L c) (fullWord_map_snd_selectedColorSubword hL c)
    exact (hu c rfl).trans (hu d h).symm
  · intro S hS
    obtain ⟨hsub, hfull⟩ := Finset.mem_filter.mp hS
    obtain ⟨c, hc, _⟩ := existsUnique_selectedColorSubword hL
      (List.mem_sublists'.mp (List.mem_toFinset.mp hsub)) hfull
    exact ⟨c, Finset.mem_univ c, hc.symm⟩
  · intro c _
    rfl

theorem prod_selectedColorSubword {C V A : Type*}
    [Fintype C] [Fintype V] [DecidableEq C] [DecidableEq V] [CommMonoid A]
    (L : List (C × V)) (hL : fullWord L) (c : V → C) (weight : C → A) :
    ((selectedColorSubword L c).map (fun p => weight p.1)).prod =
      ∏ v, weight (c v) := by
  classical
  let S := selectedColorSubword L c
  have hfull := fullWord_map_snd_selectedColorSubword hL c
  have hmap : S.map (fun p => weight p.1) =
      (S.map Prod.snd).map (fun v => weight (c v)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro p hp
    have hc : c p.2 = p.1 := by
      simpa [S, selectedColorSubword] using (List.mem_filter.mp hp).2
    simp [hc]
  rw [hmap, ← List.prod_toFinset _ hfull.1]
  have huniv : (S.map Prod.snd).toFinset = Finset.univ := by
    ext v
    exact iff_of_true (List.mem_toFinset.mpr (hfull.2 v)) (Finset.mem_univ v)
  rw [huniv]

local instance colorPairingTensorRing (m n : ℕ) :
    Ring (XPoly m ⊗[ℤ] WordAlgebra (Fin n)) := Algebra.TensorProduct.instRing

theorem componentScalarEval_colorProduct {n m : ℕ} {D : Circular.Diagram n}
    (θ : Circular.Orientation D)
    (hforward : ∀ e : Circular.Edge D.area, e.tail < e.head) :
    componentScalarEval (XPoly m) θ hforward
      (colorProduct (finiteLetter (K := XPoly m) n)
        (scalarAlphabet (List.ofFn (fun k : Fin m => (MvPolynomial.X k : XPoly m))) n) n) =
      componentStrictEnumerator D θ m := by
  classical
  rw [colorProduct_finite_positions]
  have hletter (p : Fin m × Fin n) :
      algebraMap (XPoly m) (XPoly m ⊗[ℤ] WordAlgebra (Fin n)) (MvPolynomial.X p.1) *
        finiteLetter (K := XPoly m) n p.2.1 =
      (MvPolynomial.X p.1 : XPoly m) ⊗ₜ[ℤ] algebraWord [p.2] := by
    simp [finiteLetter, scalarWord, p.2.isLt, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.tmul_mul_tmul]
  simp_rw [hletter]
  rw [componentScalarEval_prod_one_add]
  rw [sum_subwords_eq_sum_colorings (colorPositions n m) (fullWord_colorPositions n m)]
  · rw [componentStrictEnumerator_eq_coloringWord_sum θ hforward]
    apply Finset.sum_congr rfl
    intro c _
    rw [prod_selectedColorSubword _ (fullWord_colorPositions n m)]
    change (∏ v, (MvPolynomial.X (c v) : XPoly m)) *
      algebraMap ℤ (XPoly m) (componentWordCount D θ
        (((colorPositions n m).filter (fun p => decide (c p.2 = p.1))).map Prod.snd)) = _
    rw [colorPositions_filter_map_snd]
    rfl
  · intro S hS
    simp [componentWordCount_of_not_full θ hS]

/-- The ordered Cauchy product has the actual component's coloring semantics. -/
theorem componentScalarEval_cauchyProduct {n m : ℕ} {D : Circular.Diagram n}
    (θ : Circular.Orientation D)
    (hforward : ∀ e : Circular.Edge D.area, e.tail < e.head) :
    componentScalarEval (XPoly m) θ hforward
      (cauchyProduct (finiteLetter (K := XPoly m) n)
        (scalarAlphabet (List.ofFn (fun k : Fin m => (MvPolynomial.X k : XPoly m))) n) n) =
      componentStrictEnumerator D θ m := by
  rw [← finiteWordCauchy]
  exact componentScalarEval_colorProduct θ hforward

end

end VerticalStripLLT.Components
