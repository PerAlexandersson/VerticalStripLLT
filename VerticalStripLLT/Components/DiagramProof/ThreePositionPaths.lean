import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation

/-!
# Fixed-cardinality paths on three positions

The four supplied paths are the only input about the state space.  The finite
subset argument below is independent of diagrams, orientations, and covers.
-/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

private theorem subset_three_cases {V : Type*} [DecidableEq V]
    {a b c : V}
    {S : Finset V} (hS : S ⊆ {a, b, c}) :
    S = ∅ ∨ S = {a} ∨ S = {b} ∨ S = {c} ∨
      S = {a, b} ∨ S = {a, c} ∨ S = {b, c} ∨ S = {a, b, c} := by
  have hmem : ∀ x, x ∈ S → x = a ∨ x = b ∨ x = c := by
    intro x hx
    have hx' := hS hx
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hx'
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> by_cases hc : c ∈ S
  · right; right; right; right; right; right; right
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    grind only
  · right; right; right; right; left
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    grind only
  · right; right; right; right; right; left
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    grind only
  · right; left
    ext x
    simp only [Finset.mem_singleton]
    grind only
  · right; right; right; right; right; right; left
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    grind only
  · right; right; left
    ext x
    simp only [Finset.mem_singleton]
    grind only
  · right; right; right; left
    ext x
    simp only [Finset.mem_singleton]
    grind only
  · left
    ext x
    simp only [Finset.notMem_empty, iff_false]
    grind only

theorem fixed_card_connectivity_on_three_positions
    {V State : Type*} [DecidableEq V]
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (g : Finset V → State) (step : State → State → Prop)
    (hsymm : ∀ X Y, step X Y → step Y X)
    (habpath : Relation.ReflTransGen step (g {a}) (g {b}))
    (hbcpath : Relation.ReflTransGen step (g {b}) (g {c}))
    (hacpath : Relation.ReflTransGen step (g {a, c}) (g {b, c}))
    (hbcabpath : Relation.ReflTransGen step (g {b, c}) (g {a, b}))
    {S T : Finset V} (hS : S ⊆ {a, b, c}) (hT : T ⊆ {a, b, c})
    (hcard : S.card = T.card) :
    Relation.ReflTransGen step (g S) (g T) := by
  have reverse {X Y : State} (h : Relation.ReflTransGen step X Y) :
      Relation.ReflTransGen step Y X := by
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih => exact ih.head (hsymm _ _ hs)
  have hacb : Relation.ReflTransGen step (g {a, c}) (g {a, b}) :=
    hacpath.trans hbcabpath
  have hba : Relation.ReflTransGen step (g {b}) (g {a}) := reverse habpath
  have hcb : Relation.ReflTransGen step (g {c}) (g {b}) := reverse hbcpath
  have hca : Relation.ReflTransGen step (g {c}) (g {a}) := hcb.trans hba
  have hcb_ac : Relation.ReflTransGen step (g {b, c}) (g {a, c}) := reverse hacpath
  have hab_bc : Relation.ReflTransGen step (g {a, b}) (g {b, c}) := reverse hbcabpath
  have hab_ac : Relation.ReflTransGen step (g {a, b}) (g {a, c}) :=
    hab_bc.trans hcb_ac
  have hcasesS := subset_three_cases hS
  have hcasesT := subset_three_cases hT
  rcases hcasesS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hcasesT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp_all [Finset.card_insert_of_notMem]
  all_goals exact Relation.ReflTransGen.refl

end

end VerticalStripLLT.Circular.DiagramProof
