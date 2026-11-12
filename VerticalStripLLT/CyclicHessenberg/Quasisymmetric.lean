import VerticalStripLLT.CyclicHessenberg.SortedLoops
import VerticalStripLLT.CyclicHessenberg.RunHeads
import Mathlib.Data.Fintype.List

/-! The run weight is the source's monomial quasisymmetric weight in increasing distinct colors. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {k m : ℕ}

abbrev StrictColorList (β : Composition k) (m : ℕ) :=
  {c : List (Fin m) // c.Pairwise (· < ·) ∧ c.length = β.length}

noncomputable instance strictColorListFintype (β : Composition k) (m : ℕ) :
    Fintype (StrictColorList β m) := by
  let f : StrictColorList β m → {l : List (Fin m) // l.Nodup} :=
    fun c => ⟨c.val, c.property.1.nodup⟩
  have hf : Function.Injective f := by
    intro c d h
    exact Subtype.ext (congrArg (fun x : {l : List (Fin m) // l.Nodup} => x.val) h)
  letI := Finite.of_injective f hf
  exact Fintype.ofFinite _

def positionalWordOfList (l : List (Fin m)) (hl : l.length = k) : Fin k → Fin m :=
  fun i => l.get (Fin.cast hl.symm i)

theorem ofFn_positionalWordOfList (l : List (Fin m)) (hl : l.length = k) :
    List.ofFn (positionalWordOfList l hl) = l := by
  unfold positionalWordOfList
  rw [← List.ofFn_congr hl l.get, List.ofFn_get]

def colorWordToStrictList (β : Composition k) (α : CompositionColorWord β m) :
    StrictColorList β m := by
  refine ⟨blockHeads (List.ofFn α.val).equalityRuns, ?_, ?_⟩
  · rw [← equalityRunHeads_eq_blockHeads]
    apply List.equalityRunHeads_pairwise_lt
    rw [List.pairwise_ofFn]
    exact fun _ _ hij => α.property.1 hij.le
  · rw [blockHeads_length _ (fun _ => List.mem_equalityRun_ne_nil)]
    have hb := congrArg Composition.blocks α.property.2
    have hh := congrArg List.length hb
    simpa only [colorRunComposition, List.length_map] using hh

def strictListToColorWord (β : Composition k) (c : StrictColorList β m) :
    CompositionColorWord β m := by
  let l := (constantBlocks c.val β.blocks).flatten
  have hl : l.length = k :=
    (constantBlocks_flatten_length c.val β.blocks c.property.2).trans β.blocks_sum
  let α := positionalWordOfList l hl
  have hα : List.ofFn α = l := ofFn_positionalWordOfList l hl
  refine ⟨α, ?_, ?_⟩
  · have hp : (List.ofFn α).Pairwise (· ≤ ·) := by
      rw [hα]
      exact constantBlocks_flatten_pairwise_le c.val β.blocks c.property.1
    rw [List.pairwise_ofFn] at hp
    intro i j hij
    rcases lt_or_eq_of_le hij with hij | rfl
    · exact hp hij
    · exact le_rfl
  · apply Composition.ext
    change (List.ofFn α).equalityRuns.map List.length = β.blocks
    rw [hα, equalityRuns_flatten_constantBlocks c.val β.blocks c.property.2 c.property.1
      (fun _ hn => β.blocks_pos hn), constantBlocks_lengths c.val β.blocks c.property.2]

theorem ofFn_strictListToColorWord (β : Composition k) (c : StrictColorList β m) :
    List.ofFn (strictListToColorWord β c).val = (constantBlocks c.val β.blocks).flatten :=
  ofFn_positionalWordOfList _
    ((constantBlocks_flatten_length c.val β.blocks c.property.2).trans β.blocks_sum)

noncomputable def compositionColorWordEquivStrictList (β : Composition k) (m : ℕ) :
    CompositionColorWord β m ≃ StrictColorList β m where
  toFun := colorWordToStrictList β
  invFun := strictListToColorWord β
  left_inv α := by
    apply Subtype.ext
    apply List.ofFn_injective
    rw [ofFn_strictListToColorWord]
    change (constantBlocks (blockHeads (List.ofFn α.val).equalityRuns) β.blocks).flatten = _
    rw [← congrArg Composition.blocks α.property.2]
    change (constantBlocks (blockHeads (List.ofFn α.val).equalityRuns)
      ((List.ofFn α.val).equalityRuns.map List.length)).flatten = _
    rw [constantBlocks_equalityRuns]
    exact List.flatten_splitBy _ _
  right_inv c := by
    apply Subtype.ext
    change blockHeads (List.ofFn (strictListToColorWord β c).val).equalityRuns = c.val
    rw [ofFn_strictListToColorWord,
      equalityRuns_flatten_constantBlocks c.val β.blocks c.property.2 c.property.1
        (fun _ hn => β.blocks_pos hn),
      blockHeads_constantBlocks c.val β.blocks c.property.2 (fun _ hn => β.blocks_pos hn)]

/-- The usual finite monomial quasisymmetric polynomial: choose increasing distinct colors. -/
noncomputable def monomialQuasisymmetric (β : Composition k) (m : ℕ) : XPoly m :=
  ∑ c : StrictColorList β m,
    ((c.val.zip β.blocks).map fun p => (MvPolynomial.X p.1 : XPoly m) ^ p.2).prod

theorem colorWord_monomial_eq_block_powers (β : Composition k) (c : StrictColorList β m) :
    (∏ i : Fin k, (MvPolynomial.X ((strictListToColorWord β c).val i) : XPoly m)) =
      ((c.val.zip β.blocks).map fun p => (MvPolynomial.X p.1 : XPoly m) ^ p.2).prod := by
  rw [← List.prod_ofFn, List.ofFn_comp', ofFn_strictListToColorWord]
  simp only [constantBlocks, List.map_flatten, List.prod_flatten, List.map_map,
    Function.comp_def, List.map_replicate, List.prod_replicate]

/-- Exact identification of the run representation with the increasing-color source weight. -/
theorem runMonomialQuasisymmetric_eq (β : Composition k) (m : ℕ) :
    runMonomialQuasisymmetric β m = monomialQuasisymmetric β m := by
  classical
  unfold runMonomialQuasisymmetric monomialQuasisymmetric
  rw [← (compositionColorWordEquivStrictList β m).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro c hc
  exact colorWord_monomial_eq_block_powers β c

end VerticalStripLLT.CyclicHessenberg
