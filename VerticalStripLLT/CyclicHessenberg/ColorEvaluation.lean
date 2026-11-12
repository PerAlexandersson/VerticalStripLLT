import VerticalStripLLT.CyclicHessenberg.ColorPositions
import VerticalStripLLT.CyclicHessenberg.ColorSubwords
import VerticalStripLLT.CyclicHessenberg.ColorSupport

/-! Evaluate finite color-class products by their colorings. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

private theorem prod_weighted_letters {I V R : Type*} [CommRing R]
    (L : List I) (weight : I → R) (letter : I → V) :
    (L.map fun i => weight i • wordTerm (R := R) [letter i]).prod =
      (L.map weight).prod • wordTerm (R := R) (L.map letter) := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [ih]
    calc
      (weight i • wordTerm (R := R) [letter i]) *
          ((L.map weight).prod • wordTerm (R := R) (L.map letter)) =
          weight i • (wordTerm (R := R) [letter i] *
            ((L.map weight).prod • wordTerm (R := R) (L.map letter))) := by
              rw [smul_mul_assoc]
      _ = weight i • ((L.map weight).prod •
            (wordTerm (R := R) [letter i] *
              wordTerm (R := R) (L.map letter))) := by
              rw [mul_smul_comm]
      _ = ((weight i) * (L.map weight).prod) •
            wordTerm (R := R) (letter i :: L.map letter) := by
              rw [smul_smul, wordTerm_mul]
              rfl

private theorem wordEval_sum_list {V R : Type*} [CommRing R]
    (f : List V → R) (L : List (WordSum R V)) :
    wordEval f [] [] L.sum = (L.map (wordEval f [] [])).sum := by
  induction L with
  | nil => simp
  | cons A L ih => simp [ih]

/-- Evaluate a product of factors indexed by positions as a sum over subwords. -/
theorem wordEval_prod_one_add {I V R : Type*} [CommRing R]
    (f : List V → R) (L : List I) (weight : I → R) (letter : I → V) :
    wordEval f [] []
        ((L.map fun i => 1 + weight i • wordTerm (R := R) [letter i]).prod) =
      (L.sublists.map fun T => (T.map weight).prod * f (T.map letter)).sum := by
  rw [list_prod_one_add_eq_sum_subwords]
  rw [wordEval_sum_list]
  simp only [List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro T hT
  rw [prod_weighted_letters]
  simp [wordEval_term]

/-- A projected subword is full on the subtype exactly when its ambient list is an order. -/
theorem isOrder_subtypeMap_iff_isFullWord {V : Type*} [LinearOrder V]
    (S : Finset V) (l : List S) :
    IsOrder S (l.map Subtype.val) ↔ IsFullWord l := by
  constructor
  · intro h
    constructor
    · exact h.1.of_map _
    · intro v
      have hv : v.val ∈ (l.map Subtype.val).toFinset := by
        rw [h.2]
        exact v.property
      obtain ⟨w, hw, hwv⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
      have heq : w = v := Subtype.ext hwv
      simpa [heq] using hw
  · intro h
    constructor
    · exact h.1.map Subtype.val_injective
    · apply Finset.ext
      intro v
      simp only [List.mem_toFinset]
      constructor
      · intro hv
        obtain ⟨w, hw, hwv⟩ := List.mem_map.mp hv
        simpa [← hwv] using w.property
      · intro hv
        exact List.mem_map.mpr ⟨⟨v, hv⟩, h.2 ⟨v, hv⟩, rfl⟩

/-- The color-class product on its support evaluates as the weighted coloring sum. -/
theorem colorClassProduct_eval {V R : Type*} [LinearOrder V] [CommRing R]
    (S : Finset V) {m : ℕ} (weight : Fin m → R) (f : List V → R)
    (hf : ∀ w, ¬ IsOrder S w → f w = 0) :
    wordEval f [] [] (colorClassProduct S.sort (List.ofFn weight)) =
      ∑ κ : S → Fin m, (∏ v : S, weight (κ v)) *
        f (sortColorOrder κ).val := by
  classical
  have hposition := colorClassProduct_eq_positionProduct S weight
  have hfull := colorPositions_fullWord S m
  have hprojection := selectedColorSubword_map_snd_eq_sortedColorWord S m
  generalize hL : colorPositions S m = L at hposition hfull hprojection
  let positionWeight : Fin m × S → R := fun p => weight p.1
  let positionLetter : Fin m × S → V := fun p => p.2.val
  let subwordValue : List (Fin m × S) → R := fun T =>
    (T.map positionWeight).prod * f (T.map positionLetter)
  have hbad (T : List (Fin m × S))
      (hT : ¬ IsFullWord (T.map Prod.snd)) : subwordValue T = 0 := by
    have hzero : f (T.map fun p => p.2.val) = 0 := by
      apply hf
      intro horder
      apply hT
      have horder' : IsOrder S ((T.map Prod.snd).map Subtype.val) := by
        simpa only [List.map_map, Function.comp_def] using horder
      have hfull := (isOrder_subtypeMap_iff_isFullWord S (T.map Prod.snd)).mp horder'
      simpa only [List.map_map, Function.comp_def] using hfull
    simp [subwordValue, positionWeight, positionLetter, hzero]
  have hsubwords := sum_subwords_eq_sum_colorings L
    hfull subwordValue hbad
  calc
    wordEval f [] [] (colorClassProduct S.sort (List.ofFn weight)) =
        (L.sublists.map subwordValue).sum := by
      rw [hposition]
      rw [wordEval_prod_one_add]
      rfl
    _ = ∑ κ : S → Fin m, subwordValue (selectedColorSubword L κ) := hsubwords
    _ = ∑ κ : S → Fin m, (∏ v : S, weight (κ v)) *
          f (sortColorOrder κ).val := by
      apply Finset.sum_congr rfl
      intro κ hκ
      have hweight := prod_selectedColorSubword L hfull
        κ weight
      have hletters :
          (selectedColorSubword L κ).map positionLetter = (sortColorOrder κ).val := by
        calc
          (selectedColorSubword L κ).map positionLetter =
              ((selectedColorSubword L κ).map Prod.snd).map Subtype.val := by
                simp [positionLetter, List.map_map, Function.comp_def]
          _ = (sortedColorWord κ).map Subtype.val := by
            rw [hprojection]
          _ = (sortColorOrder κ).val := rfl
      dsimp only [subwordValue]
      rw [hletters]
      change ((selectedColorSubword L κ).map (fun p => weight p.1)).prod * _ = _
      rw [hweight]

/-- The same evaluation holds in an ambient alphabet after removing unsupported letters. -/
theorem colorClassProduct_eval_of_subset {V R : Type*} [LinearOrder V] [CommRing R]
    (S T : Finset V) (hST : S ⊆ T) {m : ℕ} (weight : Fin m → R)
    (f : List V → R) (hf : ∀ w, ¬ IsOrder S w → f w = 0) :
    wordEval f [] [] (colorClassProduct T.sort (List.ofFn weight)) =
      ∑ κ : S → Fin m, (∏ v : S, weight (κ v)) *
        f (sortColorOrder κ).val := by
  calc
    wordEval f [] [] (colorClassProduct T.sort (List.ofFn weight)) =
        wordEval f [] [] (colorClassProduct S.sort (List.ofFn weight)) :=
      (colorClassProduct_restrict S T hST f hf (List.ofFn weight)).eval
    _ = _ := colorClassProduct_eval S weight f hf

end VerticalStripLLT.CyclicHessenberg
