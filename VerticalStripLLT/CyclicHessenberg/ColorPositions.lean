import VerticalStripLLT.CyclicHessenberg.ColorSubwords
import VerticalStripLLT.CyclicHessenberg.Coloring
import VerticalStripLLT.CyclicHessenberg.ColorInsertion
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.OfFn

set_option autoImplicit false

/-! The canonical full word grouped by color and decreasing vertex. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {V : Type*} [LinearOrder V]

/-- The decreasing list of vertices of `S`, tagged by one color. -/
def colorPositionFiber (S : Finset V) (m : ℕ) (c : Fin m) : List (Fin m × S) :=
  ((Finset.univ : Finset S).sort (· ≥ ·)).map fun v => (c, v)

/-- The position word, grouped by increasing color and decreasing vertex. -/
def colorPositions (S : Finset V) (m : ℕ) : List (Fin m × S) :=
  (List.ofFn (colorPositionFiber S m)).flatten

private theorem map_filter_flatten {α β : Type*} (L : List (List α))
    (p : α → Bool) (f : α → β) :
    (L.flatten.filter p).map f = (L.map fun l => (l.filter p).map f).flatten := by
  induction L with
  | nil => simp
  | cons l L ih =>
    simp only [List.flatten_cons, List.filter_append, List.map_append, List.map_cons, ih]

private theorem subtype_sort_ge_map_val (S : Finset V) :
    ((Finset.univ : Finset S).sort (· ≥ ·)).map Subtype.val = S.sort (· ≥ ·) := by
  classical
  have hpair :
      List.Pairwise (· ≥ ·) (((Finset.univ : Finset S).sort (· ≥ ·)).map Subtype.val) := by
    rw [List.pairwise_map]
    exact Finset.pairwise_sort (Finset.univ : Finset S) (· ≥ ·)
  have hnodup :
      (((Finset.univ : Finset S).sort (· ≥ ·)).map Subtype.val).Nodup :=
    (Finset.sort_nodup (Finset.univ : Finset S) (· ≥ ·)).map Subtype.val_injective
  exact List.SortedGT.eq_of_mem_iff
    (hpair.sortedGE.sortedGT_of_nodup hnodup) (Finset.sortedGT_sort S) (by
      intro v
      simp [Finset.mem_sort])

private theorem finset_sort_ge_eq_reverse (S : Finset V) :
    S.sort (· ≥ ·) = S.sort.reverse := by
  apply List.SortedGT.eq_of_mem_iff (Finset.sortedGT_sort S) (Finset.sortedLT_sort S).reverse
  intro v
  simp

private theorem descendingClass_eq_reverseProd {R : Type*} [CommRing R]
    (t : R) (l : List V) :
    descendingClass t l = (l.reverse.map fun v =>
      1 + t • wordTerm (R := R) [v]).prod := by
  induction l with
  | nil => simp [descendingClass]
  | cons a l ih =>
    simp only [descendingClass, List.reverse_cons, List.map_append,
      List.map_singleton, List.prod_append, List.prod_cons, List.prod_nil, mul_one]
    rw [ih]

/-- The full position word contains each color-vertex pair exactly once. -/
theorem colorPositions_fullWord (S : Finset V) (m : ℕ) :
    IsFullWord (colorPositions S m) := by
  classical
  constructor
  · rw [colorPositions, List.nodup_flatten]
    constructor
    · intro l hl
      obtain ⟨c, rfl⟩ := List.mem_ofFn.mp hl
      exact (Finset.sort_nodup (Finset.univ : Finset S) (· ≥ ·)).map
        (fun a b h => by simpa using congrArg Prod.snd h)
    · rw [List.pairwise_ofFn]
      intro i j hij p hp hq
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
      obtain ⟨w, hw, heq⟩ := List.mem_map.mp hq
      have hij' : i = j := (congrArg Prod.fst heq).symm
      exact (Fin.ne_of_lt hij) hij'
  · intro p
    rw [colorPositions, List.mem_flatten]
    refine ⟨colorPositionFiber S m p.1, ?_, ?_⟩
    · exact List.mem_ofFn.mpr ⟨p.1, rfl⟩
    · refine List.mem_map.mpr ⟨p.2, ?_, rfl⟩
      change p.2 ∈ Finset.sort (Finset.univ : Finset S) (· ≥ ·)
      exact (Finset.mem_sort (r := (· ≥ ·))).mpr (Finset.mem_univ p.2)

private theorem colorPositionFiber_filter_map_snd (S : Finset V) {m : ℕ}
    (κ : S → Fin m) (c : Fin m) :
    ((colorPositionFiber S m c).filter (fun p => decide (κ p.2 = p.1))).map Prod.snd =
      (Finset.univ.filter fun v : S => κ v = c).sort (· ≥ ·) := by
  classical
  simp only [colorPositionFiber, List.filter_map, List.map_map, Function.comp_def]
  rw [List.map_id']
  apply List.SortedGT.eq_of_mem_iff
    ((Finset.sortedGT_sort (Finset.univ : Finset S)).pairwise.filter _).sortedGT
    (Finset.sortedGT_sort _)
  intro v
  simp [Finset.mem_sort]

/-- The vertex projection of the selected positions is the color-sorted full order. -/
theorem selectedColorSubword_map_snd_eq_sortedColorWord (S : Finset V) (m : ℕ)
    (κ : S → Fin m) :
    (selectedColorSubword (colorPositions S m) κ).map Prod.snd = sortedColorWord κ := by
  classical
  have hselected : selectedColorSubword (colorPositions S m) κ =
      (colorPositions S m).filter (fun p => decide (κ p.2 = p.1)) := by
    unfold selectedColorSubword
    congr
    funext p
    exact congrArg (fun h : Decidable (κ p.2 = p.1) => @decide _ h)
      (Subsingleton.elim _ _)
  rw [hselected]
  rw [colorPositions, map_filter_flatten]
  rw [← List.ofFn_comp']
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext c
  change ((colorPositionFiber S m c).filter
    (fun p => decide (κ p.2 = p.1))).map Prod.snd = _
  exact colorPositionFiber_filter_map_snd S κ c

private theorem colorClassProduct_ofFn {R : Type*} [CommRing R] (S : Finset V)
    {m : ℕ} (weight : Fin m → R) :
    colorClassProduct S.sort (List.ofFn weight) =
      (List.ofFn fun c => descendingClass (weight c) S.sort).prod := by
  have hh (Y : List R) : colorClassProduct S.sort Y =
      (Y.map fun t => descendingClass t S.sort).prod := by
    induction Y with
    | nil => rfl
    | cons t Y ih => simp only [colorClassProduct, List.map_cons, List.prod_cons, ih]
  simpa only [List.map_ofFn, Function.comp_def] using hh (List.ofFn weight)

private theorem colorPositionFiber_prod {R : Type*} [CommRing R] (S : Finset V)
    {m : ℕ} (weight : Fin m → R) (c : Fin m) :
    ((colorPositionFiber S m c).map fun p =>
      1 + weight p.1 • wordTerm (R := R) [p.2.val]).prod =
      descendingClass (weight c) S.sort := by
  simp only [colorPositionFiber, List.map_map, Function.comp_def]
  calc
    _ = ((((Finset.univ : Finset S).sort (· ≥ ·)).map Subtype.val).map
        (fun v => 1 + weight c • wordTerm (R := R) [v])).prod := by
      simp only [List.map_map, Function.comp_def]
    _ = _ := by
      rw [subtype_sort_ge_map_val, finset_sort_ge_eq_reverse]
      exact (descendingClass_eq_reverseProd (weight c) S.sort).symm

/-- The ordered color-class product is the product over its colored positions. -/
theorem colorClassProduct_eq_positionProduct {R : Type*} [CommRing R] (S : Finset V)
    {m : ℕ} (weight : Fin m → R) :
    colorClassProduct S.sort (List.ofFn weight) =
      ((colorPositions S m).map fun p =>
        1 + weight p.1 • wordTerm (R := R) [p.2.val]).prod := by
  classical
  rw [colorClassProduct_ofFn]
  rw [colorPositions, List.map_flatten, List.prod_flatten]
  simp only [List.map_map, List.map_ofFn, Function.comp_def]
  apply congrArg List.prod
  apply List.ofFn_inj.mpr
  funext c
  exact (colorPositionFiber_prod S weight c).symm

end VerticalStripLLT.CyclicHessenberg
