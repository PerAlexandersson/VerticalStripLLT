import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod

/-! Ordinary Schröder paths and their decorated graphs.

We use zero-based vertex labels. At a horizontal or diagonal step starting
at `(x,y)`, full cells give normal edges `(x,v)` with `x < v < y`.
A diagonal step additionally gives the strict edge `(x,y)`.
See the manuscript at lines 633–645 and 1009–1015.
-/

namespace VerticalStripLLT

inductive Step where
  | north | diagonal | east
  deriving DecidableEq, Repr

namespace Step

/-- Check the endpoint and require east/diagonal steps to start above the diagonal. -/
def validFrom (n x y : ℕ) : List Step → Bool
  | [] => (x == n) && (y == n)
  | north :: w => validFrom n x (y + 1) w
  | diagonal :: w => (x < y) && validFrom n (x + 1) (y + 1) w
  | east :: w => (x < y) && validFrom n (x + 1) y w

/-- Full cells below a word, read in path order. -/
def normalFrom (x y u v : ℕ) : List Step → Bool
  | [] => false
  | north :: w => normalFrom x (y + 1) u v w
  | diagonal :: w => ((u == x) && (x < v) && (v < y)) ||
      normalFrom (x + 1) (y + 1) u v w
  | east :: w => ((u == x) && (x < v) && (v < y)) ||
      normalFrom (x + 1) y u v w

/-- Diagonal endpoints, with paper labels translated to zero-based labels. -/
def strictFrom (x y u v : ℕ) : List Step → Bool
  | [] => false
  | north :: w => strictFrom x (y + 1) u v w
  | diagonal :: w => ((u == x) && (v == y)) ||
      strictFrom (x + 1) (y + 1) u v w
  | east :: w => strictFrom (x + 1) y u v w

end Step

/-- A word satisfying the ordinary Schröder path conditions of the manuscript. -/
structure SchroderPath (n : ℕ) where
  steps : List Step
  valid : Step.validFrom n 0 0 steps = true

namespace SchroderPath

def empty : SchroderPath 0 := ⟨[], by decide⟩

def normalEdges {n : ℕ} (P : SchroderPath n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun e => Step.normalFrom 0 0 e.1.val e.2.val P.steps

def strictEdges {n : ℕ} (P : SchroderPath n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun e => Step.strictFrom 0 0 e.1.val e.2.val P.steps

open Step in
def singleton : SchroderPath 1 := ⟨[north, east], by decide⟩

open Step in
def strictPair : SchroderPath 2 := ⟨[north, diagonal, east], by decide⟩

open Step in
def normalPair : SchroderPath 2 := ⟨[north, north, east, east], by decide⟩

open Step in
def disconnectedPair : SchroderPath 2 := ⟨[north, east, north, east], by decide⟩

@[simp] theorem empty_normalEdges : empty.normalEdges = ∅ := by decide
@[simp] theorem empty_strictEdges : empty.strictEdges = ∅ := by decide
@[simp] theorem singleton_normalEdges : singleton.normalEdges = ∅ := by decide
@[simp] theorem singleton_strictEdges : singleton.strictEdges = ∅ := by decide
@[simp] theorem strictPair_normalEdges : strictPair.normalEdges = ∅ := by decide
@[simp] theorem strictPair_strictEdges : strictPair.strictEdges = {(0, 1)} := by decide
@[simp] theorem normalPair_normalEdges : normalPair.normalEdges = {(0, 1)} := by decide
@[simp] theorem normalPair_strictEdges : normalPair.strictEdges = ∅ := by decide
@[simp] theorem disconnectedPair_normalEdges : disconnectedPair.normalEdges = ∅ := by decide
@[simp] theorem disconnectedPair_strictEdges : disconnectedPair.strictEdges = ∅ := by decide

end SchroderPath
end VerticalStripLLT
