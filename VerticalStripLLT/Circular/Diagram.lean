import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod

/-! Finite circular area sequences, edges, and strict corner data.

This file records only the underlying finite diagram model.  Coloring and
orientation semantics are defined in later circular modules.
-/

namespace VerticalStripLLT
namespace Circular

noncomputable section

variable {n : ℕ}

/-- A positive cyclic area sequence with zero-based vertex labels. -/
structure CircularArea (n : ℕ) where
  positive : 0 < n
  area : Fin n → ℕ
  bound : ∀ i, area i < n
  cyclic : ∀ i, area ⟨(i.val + 1) % n, Nat.mod_lt _ positive⟩ ≤ area i + 1

namespace CircularArea

/-- The successor of a vertex, with labels read modulo the circumference. -/
def next (A : CircularArea n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ A.positive⟩

@[simp] theorem next_val (A : CircularArea n) (i : Fin n) :
    (A.next i).val = (i.val + 1) % n := rfl

@[simp] theorem next_area (A : CircularArea n) (i : Fin n) :
    A.area (A.next i) = A.area ⟨(i.val + 1) % n, Nat.mod_lt _ A.positive⟩ := rfl

end CircularArea

/-- An admissible positive-length circular edge, represented by head and length.

The endpoint is not stored: it is obtained by moving backwards by the length
around the circle.
-/
def Edge (A : CircularArea n) :=
  {p : Fin n × Fin n // 0 < p.2.val ∧ p.2.val ≤ A.area p.1}

namespace Edge

variable {A : CircularArea n}

instance (A : CircularArea n) : Fintype (Edge A) := by
  classical
  unfold Edge
  infer_instance

instance (A : CircularArea n) : DecidableEq (Edge A) := Classical.decEq _

def head (e : Edge A) : Fin n := e.1.1

def length (e : Edge A) : Fin n := e.1.2

def tail (e : Edge A) : Fin n :=
  ⟨(e.head.val + n - e.length.val) % n, Nat.mod_lt _ A.positive⟩

@[simp] theorem head_val (e : Edge A) : e.head.val = e.1.1.val := rfl

@[simp] theorem length_val (e : Edge A) : e.length.val = e.1.2.val := rfl

@[simp] theorem tail_val (e : Edge A) :
    e.tail.val = (e.head.val + n - e.length.val) % n := rfl

@[simp] theorem tail_lt (e : Edge A) : e.tail.val < n := e.tail.isLt

end Edge

/-- An edge is a strict corner when it reaches the top of its head column and
the next column is no higher than that column. -/
def IsCorner {n : ℕ} {A : CircularArea n} (e : Edge A) : Prop :=
  e.length.val = A.area e.head ∧ A.area (A.next e.head) ≤ A.area e.head

/-- A circular diagram together with its selected strict corner edges. -/
structure Diagram (n : ℕ) where
  area : CircularArea n
  strict : Finset (Edge area)
  strict_corner : ∀ e ∈ strict, IsCorner e

end
end Circular
end VerticalStripLLT
