import VerticalStripLLT.Circular.BounceSearch
import Mathlib.Tactic.Linarith

/-! Integer strict contact lists extracted from a reverse bounce. -/

namespace VerticalStripLLT.Circular

namespace Diagram

variable {n : ℕ} (D : Diagram n)

/-- A snoc-oriented chain predicate for integer selected edges. -/
inductive IntegerSelectedChain (R : ℤ → ℤ → Prop) : List ℤ → Prop
  | singleton (z : ℤ) : IntegerSelectedChain R [z]
  | snoc {l : List ℤ} {u v : ℤ} :
      IntegerSelectedChain R (l ++ [u]) → R u v →
      IntegerSelectedChain R (l ++ [u, v])

def integerSelected (u v : ℤ) : Prop :=
  D.edgeData.selected ∅ (D.residue u) (D.residue v)

/-- The integer main and parallel contact chains of a reverse bounce. -/
def ReverseBounceContacts (t x : ℤ) : Prop :=
  ∃ inner : List ℤ, inner ≠ [] ∧
    (∃ rest, inner = x :: rest) ∧
    (∃ init, inner = init ++ [D.boundary t]) ∧
    IntegerSelectedChain D.integerSelected (inner ++ [t]) ∧
    IntegerSelectedChain D.integerSelected (inner.map (fun z : ℤ => z + 1))

private theorem boundary_succ_of_zero_gap {z : ℤ}
    (hgap : D.eastGap z = 0) (hstrict : D.strictAt z) :
    D.boundary (z + 1) = D.boundary z + 1 := by
  unfold eastGap at hgap
  simp [hstrict] at hgap
  linarith

private theorem integer_selected_of_strictAt {z : ℤ} (h : D.strictAt z) :
    D.integerSelected (D.boundary z) z := D.selected_of_strictAt h

theorem parallel_selected_of_dd {z : ℤ}
    (hgap : D.eastGap z = 0) (hfirst : D.strictAt z)
    (hsecond : D.strictAt (z + 1)) :
    D.integerSelected (D.boundary z + 1) (z + 1) := by
  have hboundary := D.boundary_succ_of_zero_gap hgap hfirst
  rw [← hboundary]
  exact D.integer_selected_of_strictAt hsecond

/-- Extract strict integer contact chains by Prop induction on the bounce. -/
theorem ReverseBounce.exists_contacts {t x : ℤ}
    (h : ReverseBounce D t x) (hroot : D.strictAt t) :
    D.ReverseBounceContacts t x := by
  induction h with
  | stop t hgap hnot =>
    refine ⟨[D.boundary t], by simp, ⟨[], rfl⟩, ⟨[], rfl⟩, ?_, ?_⟩
    · simpa using IntegerSelectedChain.snoc (l := [])
        (IntegerSelectedChain.singleton (D.boundary t))
        (D.integer_selected_of_strictAt hroot)
    · simpa using IntegerSelectedChain.singleton (D.boundary t + 1)
  | @descend t x hgap hfirst hsecond child ih =>
    rcases ih hfirst with ⟨inner, hne, hstarts, hends, hmain, hparallel⟩
    refine ⟨inner ++ [D.boundary t], ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · rcases hstarts with ⟨rest, hrest⟩
      exact ⟨rest ++ [D.boundary t], by rw [hrest]; rfl⟩
    · exact ⟨inner, rfl⟩
    · simpa [List.append_assoc] using IntegerSelectedChain.snoc hmain
        (D.integer_selected_of_strictAt hroot)
    · rcases hends with ⟨init, hinit⟩
      rw [hinit, List.map_append] at hparallel ⊢
      simpa [List.append_assoc] using IntegerSelectedChain.snoc hparallel
        (D.parallel_selected_of_dd hgap hfirst hsecond)

end Diagram
end VerticalStripLLT.Circular
