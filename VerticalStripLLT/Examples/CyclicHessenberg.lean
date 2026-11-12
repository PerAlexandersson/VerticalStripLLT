import VerticalStripLLT.CyclicHessenberg
import VerticalStripLLT.CyclicHessenberg.IdentityMatching
import VerticalStripLLT.CyclicHessenberg.SingletonExpansion
import VerticalStripLLT.CyclicHessenberg.CompleteTwoExpansion
import VerticalStripLLT.CyclicHessenberg.CompleteThree
import VerticalStripLLT.CyclicHessenberg.KimOhExample
import VerticalStripLLT.CyclicHessenberg.ZeroParameter
import VerticalStripLLT.CyclicHessenberg.LoopMatchings

/-! Boundary and orientation regressions for the independent cyclic Hessenberg source.
Explicit expansion regressions are imported above; none assumes its own expansion. -/

namespace VerticalStripLLT.CyclicHessenberg.Examples

open VerticalStripLLT.CyclicHessenberg

example {n : ℕ} (h : Tuple 0 n) (m : ℕ) : cyclicLLT h m = 1 := by
  rw [cyclicLLT_eq_loopColoringLLT, loopColoringLLT_empty]

example {k n : ℕ} (h : Tuple k n) (hk : 0 < k) : cyclicLLT h 0 = 0 := by
  rw [cyclicLLT_eq_loopColoringLLT, loopColoringLLT_zero_alphabet h hk]

/-- Equal colors put the larger canonical label first. -/
theorem decreasing_color_tie :
    colorPrecedes (fun _ : Fin 2 => (0 : Fin 1)) 1 0 ∧
      ¬colorPrecedes (fun _ : Fin 2 => (0 : Fin 1)) 0 1 := by
  norm_num [colorPrecedes]

/-- The two loops exchange labels at the middle boundary and return at the end. -/
def reverseEventLoop : LoopCover (completeTwoTuple 2) :=
  ⟨![1, Equiv.swap 0 1, 1], rfl, rfl, by
    intro ℓ a
    change _ ≤ (1 : Fin 2)
    exact Fin.le_last _⟩

/-- A later layer really can contribute the reverse canonical-label event. -/
theorem later_reverse_event :
    ((1 : Fin 2), (1 : Fin 2), (0 : Fin 2)) ∈
      loopAscentEvents (completeTwoTuple 2) reverseEventLoop := by
  simp [loopAscentEvents, reverseEventLoop, completeTwoTuple, completeTwo,
    Hessenberg.complete]

noncomputable def reverseTieEvents : Finset (Fin 2 × Fin 2 × Fin 2) := by
  classical
  exact (loopAscentEvents (completeTwoTuple 2) reverseEventLoop).filter
    (fun e => colorPrecedes (fun _ => (0 : Fin 1)) e.2.1 e.2.2)

/-- Equal colors retain this reverse event; replacing `≤` by `<` would lose it. -/
theorem later_reverse_event_with_tie :
    ((1 : Fin 2), (1 : Fin 2), (0 : Fin 2)) ∈ reverseTieEvents := by
  classical
  exact Finset.mem_filter.mpr ⟨later_reverse_event, decreasing_color_tie.1⟩

theorem reverse_tie_ascent_pos :
    0 < coloredLoopAscentCount (completeTwoTuple 2) reverseEventLoop
      (fun _ => (0 : Fin 1)) :=
  Finset.card_pos.mpr ⟨(1, 1, 0), later_reverse_event_with_tie⟩

private def lowForward : Order ({0, 1} : Finset ℕ) := ⟨[0, 1], by simp [IsOrder]⟩
private def lowReverse : Order ({0, 1} : Finset ℕ) := ⟨[1, 0], by simp [IsOrder, Finset.pair_comm]⟩
private def highForward : Order ({2, 3} : Finset ℕ) := ⟨[2, 3], by simp [IsOrder]⟩
private def highReverse : Order ({2, 3} : Finset ℕ) := ⟨[3, 2], by simp [IsOrder, Finset.pair_comm]⟩
private theorem contextsDisjoint : Disjoint ({0, 1} : Finset ℕ) {2, 3} := by decide

/-- Independent prefix contexts are genuinely different in this restriction. -/
example : lowForward ≠ lowReverse := by
  intro h
  have := congrArg Subtype.val h
  simp [lowForward, lowReverse] at this

example {R : Type*} [CommSemiring R] (q : R)
    (Z : Kernel R (({0, 1} : Finset ℕ) ∪ {2, 3})) (hZ : ExchangeCompatible q Z) :
    ExchangeCompatible q (prefixKernel contextsDisjoint Z lowForward lowReverse) :=
  hZ.prefixKernel contextsDisjoint lowForward lowReverse

/-- Independent suffix contexts are genuinely different too. -/
example : highForward ≠ highReverse := by
  intro h
  have := congrArg Subtype.val h
  simp [highForward, highReverse] at this

example {R : Type*} [CommSemiring R] (q : R)
    (Z : Kernel R (({0, 1} : Finset ℕ) ∪ {2, 3})) (hZ : ExchangeCompatible q Z) :
    ExchangeCompatible q (suffixKernel contextsDisjoint Z highForward highReverse) :=
  hZ.suffixKernel contextsDisjoint highForward highReverse

end VerticalStripLLT.CyclicHessenberg.Examples
