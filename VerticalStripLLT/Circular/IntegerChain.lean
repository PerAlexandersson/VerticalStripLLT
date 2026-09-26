import VerticalStripLLT.Circular.ReverseBounceContacts
import Mathlib.Data.List.Chain
import Mathlib.Tactic.Linarith

/-! Generic eliminators for the snoc-oriented integer contact chains. -/

namespace VerticalStripLLT.Circular

namespace Diagram

variable {R : ℤ → ℤ → Prop}

namespace IntegerSelectedChain

theorem map {S : ℤ → ℤ → Prop} {f : ℤ → ℤ} {l : List ℤ}
    (h : IntegerSelectedChain R l)
    (hf : ∀ ⦃u v⦄, R u v → S (f u) (f v)) :
    IntegerSelectedChain S (l.map f) := by
  induction h with
  | singleton z => simpa using IntegerSelectedChain.singleton (f z)
  | @snoc l u v hchain huv ih =>
    simp only [List.map_append, List.map_cons, List.map_nil] at ih ⊢
    exact IntegerSelectedChain.snoc ih (hf huv)

/-- The contact certificate implies the standard list-chain predicate. -/
theorem isChain {l : List ℤ} (h : IntegerSelectedChain R l) : List.IsChain R l := by
  induction h with
  | singleton z => simp
  | @snoc l u v hchain huv ih =>
    have hpair : List.IsChain R ([u] ++ [v]) := by simpa using huv
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      ih.append_overlap hpair (by simp)

/-- Every adjacent pair of list entries is a relation step. -/
theorem getElem_succ {l : List ℤ} (h : IntegerSelectedChain R l)
    (i : ℕ) (hi : i + 1 < l.length) : R l[i] l[i + 1] := by
  exact List.isChain_iff_getElem.mp h.isChain i hi

end IntegerSelectedChain

end Diagram
end VerticalStripLLT.Circular
