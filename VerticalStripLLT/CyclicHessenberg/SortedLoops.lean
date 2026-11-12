import VerticalStripLLT.CyclicHessenberg.LoopColorOrder
import VerticalStripLLT.CyclicHessenberg.ColorRuns
import Mathlib.Combinatorics.Enumerative.Composition

/-! The independent composition-sorted loop model and its finite color-run weights. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {k n m : ℕ}

/-- An ordered collection of loops, with its actual first-boundary permutation retained. -/
abbrev OrderedLoopCover (h : Tuple k n) := LoopCover h × Equiv.Perm (Fin k)

def orderedLoopValue (h : Tuple k n) (D : OrderedLoopCover h)
    (ℓ : Fin (n + 1)) (i : Fin k) : Fin k := D.1.val ℓ (D.2 i)

/-- The source's sortedness: first-layer labels decrease inside each positive block. -/
def IsSortedLoopDecomposition (h : Tuple k n) (β : Composition k)
    (D : OrderedLoopCover h) : Prop :=
  ∀ block ∈ (List.ofFn D.2).splitWrtComposition β, block.Pairwise (· > ·)

abbrev SortedLoopDecomposition (h : Tuple k n) (β : Composition k) :=
  {D : OrderedLoopCover h // IsSortedLoopDecomposition h β D}

noncomputable instance sortedLoopDecompositionFintype (h : Tuple k n) (β : Composition k) :
    Fintype (SortedLoopDecomposition h β) := Fintype.ofFinite _

/-- Positional ascent events, defined directly on the ordered loop collection. -/
noncomputable def orderedLoopAscentEvents (h : Tuple k n) (D : OrderedLoopCover h) :
    Finset (Fin n × Fin k × Fin k) := by
  classical
  exact Finset.univ.filter fun e => e.2.1 < e.2.2 ∧
    orderedLoopValue h D e.1.castSucc e.2.1 < orderedLoopValue h D e.1.castSucc e.2.2 ∧
    orderedLoopValue h D e.1.castSucc e.2.2 ≤ h e.1 (orderedLoopValue h D e.1.succ e.2.1)

noncomputable def orderedLoopAscentCount (h : Tuple k n) (D : OrderedLoopCover h) : ℕ :=
  (orderedLoopAscentEvents h D).card

/-- Positive run lengths of a positional color word. No sortedness assumption is built in. -/
def colorRunComposition (α : Fin k → Fin m) : Composition k where
  blocks := (List.ofFn α).equalityRuns.map List.length
  blocks_pos := by
    intro i hi
    obtain ⟨run, hr, rfl⟩ := List.mem_map.mp hi
    exact List.length_pos_iff.mpr (List.mem_equalityRun_ne_nil hr)
  blocks_sum := by
    rw [← List.length_flatten]
    simp [List.equalityRuns]

/-- A choice of increasing block colors, represented by its full positional word. -/
abbrev CompositionColorWord (β : Composition k) (m : ℕ) :=
  {α : Fin k → Fin m // Monotone α ∧ colorRunComposition α = β}

noncomputable instance compositionColorWordFintype (β : Composition k) (m : ℕ) :
    Fintype (CompositionColorWord β m) := Fintype.ofFinite _

/-- Finite monomial quasisymmetric weight, selecting exactly the constant runs of `β`.
Its identification with increasing lists of distinct colors is a separate finite bijection. -/
noncomputable def runMonomialQuasisymmetric (β : Composition k) (m : ℕ) : XPoly m :=
  ∑ α : CompositionColorWord β m, ∏ i : Fin k, MvPolynomial.X (α.val i)

/-- The composition-sorted source expression, independent of transfer kernels and deletion. -/
noncomputable def sortedLoopColoringSum (h : Tuple k n) (m : ℕ) : XPoly m :=
  ∑ β : Composition k, ∑ D : SortedLoopDecomposition h β,
    MvPolynomial.C (Polynomial.X ^ orderedLoopAscentCount h D.val) *
      runMonomialQuasisymmetric β m

end VerticalStripLLT.CyclicHessenberg
