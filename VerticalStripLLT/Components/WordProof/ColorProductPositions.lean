import VerticalStripLLT.Components.WordProof.ColoringWord
import VerticalStripLLT.Components.WordProof.FiniteWordCauchy
import Mathlib.Data.List.FinRange

/-! Position lists for the finite color product. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Components

open scoped BigOperators TensorProduct

noncomputable section

/-- The positions are grouped by color and decreasing in the vertex coordinate. -/
def colorPositionFiber (n m : ℕ) (k : Fin m) : List (Fin m × Fin n) :=
  (decWord (Finset.univ : Finset (Fin n))).map (fun v => (k, v))

def colorPositions (n m : ℕ) : List (Fin m × Fin n) :=
  (List.ofFn (colorPositionFiber n m)).flatten

theorem fullWord_colorPositions (n m : ℕ) :
    fullWord (colorPositions n m) := by
  classical
  constructor
  · rw [colorPositions, List.nodup_flatten]
    constructor
    · intro l hl
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hl
      exact (Finset.sort_nodup _ _).map (fun x y h => by
        simpa using congrArg Prod.snd h)
    · rw [List.pairwise_ofFn]
      intro i j hij p hp hq
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
      obtain ⟨w, hw, heq⟩ := List.mem_map.mp hq
      have : i = j := (congrArg Prod.fst heq).symm
      exact (Fin.ne_of_lt hij) this
  · intro p
    rw [colorPositions, List.mem_flatten]
    refine ⟨colorPositionFiber n m p.1, ?_, ?_⟩
    · exact List.mem_ofFn.mpr ⟨p.1, rfl⟩
    · refine List.mem_map.mpr ⟨p.2, ?_, rfl⟩
      change p.2 ∈ Finset.sort (Finset.univ : Finset (Fin n)) (· ≥ ·)
      exact (Finset.mem_sort (r := (· ≥ ·))).mpr (Finset.mem_univ p.2)

private theorem map_filter_flatten {α β : Type*} (L : List (List α))
    (p : α → Bool) (f : α → β) :
    (L.flatten.filter p).map f =
      (L.map (fun l => (l.filter p).map f)).flatten := by
  induction L with
  | nil => simp
  | cons l L ih =>
      simp only [List.flatten_cons, List.filter_append, List.map_append, List.map_cons, ih]

private theorem colorPositionFiber_filter_map_snd {m : ℕ} (n : ℕ) (c : Fin n → Fin m)
    (k : Fin m) :
    ((colorPositionFiber n m k).filter (fun p => decide (c p.2 = p.1))).map Prod.snd =
      decWord (Finset.univ.filter fun v => c v = k) := by
  classical
  simp only [colorPositionFiber, List.filter_map, List.map_map, Function.comp_def]
  rw [List.map_id']
  apply List.SortedGT.eq_of_mem_iff
    ((Finset.sortedGT_sort (Finset.univ : Finset (Fin n))).pairwise.filter _).sortedGT
    (Finset.sortedGT_sort _)
  intro v
  simp [Finset.mem_sort]

theorem colorPositions_filter_map_snd (n m : ℕ) (c : Fin n → Fin m) :
    ((colorPositions n m).filter (fun p => decide (c p.2 = p.1))).map Prod.snd =
      coloringWord c := by
  classical
  rw [colorPositions, map_filter_flatten]
  rw [← List.ofFn_comp']
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext k
  exact colorPositionFiber_filter_map_snd n c k

private theorem decWord_univ_eq_reverse_ofFn (n : ℕ) :
    decWord (Finset.univ : Finset (Fin n)) =
      (List.ofFn (fun i : Fin n => i)).reverse := by
  have h : decWord (Finset.univ : Finset (Fin n)) =
      (List.finRange n).reverse := by
    apply List.SortedGT.eq_reverse_of_mem_iff_of_sortedLT
    · intro a
      simp [decWord]
    · exact Finset.sortedGT_sort _
    · exact List.sortedLT_finRange n
  exact h

private theorem prod_decWord_univ {R : Type*} [Ring R]
    (u : ℕ → R) (t : R) (n : ℕ) :
    ((decWord (Finset.univ : Finset (Fin n))).map
      (fun v => 1 + t * u v.1)).prod = descendingProduct u t n := by
  rw [decWord_univ_eq_reverse_ofFn]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ', List.concat_eq_append, List.reverse_concat',
        List.map_cons, List.prod_cons]
      simp only [Fin.last]
      rw [List.ofFn_comp', ← List.map_reverse]
      simp only [List.map_map]
      change (1 + t * u n) *
        ((List.ofFn (fun i : Fin n => i)).reverse.map (fun v => 1 + t * u v.1)).prod = _
      rw [ih]
      rfl

local instance colorProductTensorRing (m n : ℕ) :
    Ring (XPoly m ⊗[ℤ] WordAlgebra (Fin n)) :=
  Algebra.TensorProduct.instRing

theorem colorProduct_finite_positions {m n : ℕ} :
    colorProduct (finiteLetter (K := XPoly m) n)
        (scalarAlphabet (List.ofFn (fun k : Fin m => (MvPolynomial.X k : XPoly m))) n) n =
      ((colorPositions n m).map (fun p =>
        1 + algebraMap (XPoly m)
            (XPoly m ⊗[ℤ] WordAlgebra (Fin n)) (MvPolynomial.X p.1) *
          finiteLetter (K := XPoly m) n p.2.1)).prod := by
  classical
  unfold colorProduct scalarAlphabet colorPositions
  rw [List.map_flatten, List.prod_flatten]
  simp only [List.map_map, List.map_ofFn, Function.comp_def, colorPositionFiber]
  change (List.ofFn (fun k : Fin m => descendingProduct (finiteLetter n)
      (algebraMap (XPoly m) _ (MvPolynomial.X k)) n)).prod = _
  symm
  congr 1
  apply congrArg List.ofFn
  funext k
  exact prod_decWord_univ _ _ n

end

end VerticalStripLLT.Components
