import VerticalStripLLT.Polynomial
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Relation

/-! Generic finite edge-coloring semantics for circular LLT instances. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators

/-- A finite directed edge instance with the edges imposing strict inequalities. -/
structure EdgeData (V E : Type*) where
  tail : E → V
  head : E → V
  strict : Finset E

namespace EdgeData

variable {V E : Type*}

/-- The non-strict edges of an edge instance. -/
def normalEdges [Fintype E] [DecidableEq E] (G : EdgeData V E) : Finset E :=
  Finset.univ \ G.strict

/-- A coloring satisfies every strict edge of the instance. -/
def admissibleColoring (G : EdgeData V E) {m : ℕ} (c : V → Fin m) : Prop :=
  ∀ e ∈ G.strict, c (G.tail e) < c (G.head e)

/-- The non-strict edges that are ascents for a coloring. -/
def ascentEdges [Fintype E] [DecidableEq E] (G : EdgeData V E) {m : ℕ}
    (c : V → Fin m) : Finset E :=
  (G.normalEdges).filter fun e => c (G.tail e) < c (G.head e)

/-- The variable monomial of a coloring. -/
noncomputable def monomial [Fintype V] {m : ℕ} (c : V → Fin m) : XPoly m :=
  ∏ v, MvPolynomial.X (c v)

/-- The LLT weight of a coloring, with inadmissible colorings assigned weight zero. -/
noncomputable def coloringWeight [Fintype V] [Fintype E] [DecidableEq E]
    (G : EdgeData V E) {m : ℕ} (c : V → Fin m) : XPoly m := by
  classical
  exact if admissibleColoring G c then
    MvPolynomial.C (Polynomial.X ^ (G.ascentEdges c).card) * monomial c
  else 0

/-- The finite-alphabet coloring LLT polynomial, including the empty alphabet. -/
noncomputable def coloringLLT [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdgeData V E) (m : ℕ) : XPoly m := by
  classical
  exact ∑ c : V → Fin m, G.coloringWeight c

/-- An edge selected either by the original strict set or by an added edge set. -/
def selected [DecidableEq E] (G : EdgeData V E) (A : Finset E) (u v : V) : Prop :=
  ∃ e ∈ G.strict ∪ A, G.tail e = u ∧ G.head e = v

/-- The selected edges contain no directed cycle. -/
def Admissible [DecidableEq E] (G : EdgeData V E) (A : Finset E) : Prop :=
  ∀ v, ¬ Relation.TransGen (G.selected A) v v

/-- The generating polynomial of colorings strictly increasing on all selected edges. -/
noncomputable def strictOrderEnumerator [Fintype V] [DecidableEq V] [DecidableEq E]
    (G : EdgeData V E) (A : Finset E) (m : ℕ) : XPoly m := by
  classical
  exact ∑ c : V → Fin m,
    if ∀ e ∈ G.strict ∪ A, c (G.tail e) < c (G.head e) then monomial c else 0

/-- A coloring increasing on selected edges increases along each selected step. -/
theorem lt_of_selected [DecidableEq E] (G : EdgeData V E) (A : Finset E) {m : ℕ}
    (c : V → Fin m) (hc : ∀ e ∈ G.strict ∪ A, c (G.tail e) < c (G.head e))
    {u v : V} (h : G.selected A u v) : c u < c v := by
  rcases h with ⟨e, he, hu, hv⟩
  rw [← hu, ← hv]
  exact hc e he

/-- A coloring increasing on selected edges strictly increases along every selected path. -/
theorem lt_of_transGen [DecidableEq E] (G : EdgeData V E) (A : Finset E) {m : ℕ}
    (c : V → Fin m) (hc : ∀ e ∈ G.strict ∪ A, c (G.tail e) < c (G.head e))
    {u v : V} (h : Relation.TransGen (G.selected A) u v) : c u < c v := by
  induction h with
  | single h => exact G.lt_of_selected A c hc h
  | tail _ hstep ih => exact ih.trans (G.lt_of_selected A c hc hstep)

/-- A selected directed cycle forbids every strictly increasing coloring. -/
theorem not_selected_coloring_of_cycle [DecidableEq E] (G : EdgeData V E)
    (A : Finset E) {m : ℕ} {v : V} (hcycle : Relation.TransGen (G.selected A) v v)
    (c : V → Fin m) : ¬ ∀ e ∈ G.strict ∪ A, c (G.tail e) < c (G.head e) := by
  intro hc
  exact (lt_irrefl (c v)) (G.lt_of_transGen A c hc hcycle)

/-- Failure of selected-edge admissibility forbids every strictly increasing coloring. -/
theorem not_selected_coloring_of_not_admissible [DecidableEq E] (G : EdgeData V E)
    (A : Finset E) (h : ¬ G.Admissible A) {m : ℕ} (c : V → Fin m) :
    ¬ ∀ e ∈ G.strict ∪ A, c (G.tail e) < c (G.head e) := by
  intro hc
  apply h
  intro v hcycle
  exact G.not_selected_coloring_of_cycle A hcycle c hc

/-- A selected directed cycle makes the strict order enumerator vanish. -/
theorem strictOrderEnumerator_eq_zero_of_cycle [Fintype V] [DecidableEq V] [DecidableEq E]
    (G : EdgeData V E) (A : Finset E) {v : V}
    (hcycle : Relation.TransGen (G.selected A) v v) (m : ℕ) :
    G.strictOrderEnumerator A m = 0 := by
  classical
  unfold strictOrderEnumerator
  apply Finset.sum_eq_zero
  intro c _
  exact ite_eq_right (G.not_selected_coloring_of_cycle A hcycle c)

/-- A non-admissible selected edge set has zero strict order enumerator. -/
theorem strictOrderEnumerator_eq_zero_of_not_admissible
    [Fintype V] [DecidableEq V] [DecidableEq E]
    (G : EdgeData V E) (A : Finset E) (h : ¬ G.Admissible A) (m : ℕ) :
    G.strictOrderEnumerator A m = 0 := by
  classical
  unfold strictOrderEnumerator
  apply Finset.sum_eq_zero
  intro c _
  exact ite_eq_right (G.not_selected_coloring_of_not_admissible A h c)

end EdgeData
end VerticalStripLLT.Circular
