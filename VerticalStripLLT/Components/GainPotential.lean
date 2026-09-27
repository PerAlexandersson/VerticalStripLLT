import Mathlib.Order.Lattice.Nat
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.SplitIfs

/-! Least nonnegative integer potentials and invariance under strictly slack edges.

The minimum is taken coordinatewise over feasible potentials. This avoids
choosing maximizing walks; negative-cycle feasibility remains a separate bridge.
-/

namespace VerticalStripLLT.Components

/-- Directed edge instances with arbitrary integer gains, including loops and parallels. -/
structure GainData (V E : Type*) where
  tail : E → V
  head : E → V
  gain : E → ℤ

namespace GainData

noncomputable section

variable {V E : Type*} (G : GainData V E)

/-- A nonnegative integer potential satisfying the selected difference constraints. -/
def Feasible (A : Finset E) (p : V → ℕ) : Prop :=
  ∀ e ∈ A, (p (G.tail e) : ℤ) + G.gain e ≤ p (G.head e)

/-- The least feasible value at each vertex; used only with a feasibility proof. -/
def potential (A : Finset E) (v : V) : ℕ :=
  sInf {k | ∃ p : V → ℕ, G.Feasible A p ∧ p v = k}

theorem feasible_mono {A B : Finset E} (hAB : A ⊆ B) {p : V → ℕ}
    (hp : G.Feasible B p) : G.Feasible A p :=
  fun e he => hp e (hAB he)

theorem potential_le {A : Finset E} {p : V → ℕ} (hp : G.Feasible A p) (v : V) :
    G.potential A v ≤ p v :=
  csInf_le' ⟨p, hp, rfl⟩

theorem potential_attained {A : Finset E} (hA : ∃ p, G.Feasible A p) (v : V) :
    ∃ p, G.Feasible A p ∧ p v = G.potential A v := by
  change G.potential A v ∈ {k | ∃ p : V → ℕ, G.Feasible A p ∧ p v = k}
  apply csInf_mem
  obtain ⟨p, hp⟩ := hA
  exact ⟨p v, p, hp, rfl⟩

/-- Coordinatewise minima are simultaneously feasible for difference constraints. -/
theorem potential_feasible {A : Finset E} (hA : ∃ p, G.Feasible A p) :
    G.Feasible A (G.potential A) := by
  intro e he
  obtain ⟨p, hp, hhead⟩ := G.potential_attained hA (G.head e)
  have htail := G.potential_le hp (G.tail e)
  have hedge := hp e he
  rw [hhead] at hedge
  lia

theorem potential_mono {A B : Finset E} (hAB : A ⊆ B)
    (hB : ∃ p, G.Feasible B p) (v : V) :
    G.potential A v ≤ G.potential B v :=
  G.potential_le (G.feasible_mono hAB (G.potential_feasible hB)) v

variable [DecidableEq E]

/-- An edge already satisfied by the least potential can be inserted without changing it. -/
theorem potential_insert_eq {A : Finset E} {e : E}
    (hA : ∃ p, G.Feasible A p)
    (he : (G.potential A (G.tail e) : ℤ) + G.gain e ≤ G.potential A (G.head e)) :
    G.potential (insert e A) = G.potential A := by
  have hp : G.Feasible (insert e A) (G.potential A) := by
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact he
    · exact G.potential_feasible hA f hf
  funext v
  exact le_antisymm (G.potential_le hp v)
    (G.potential_mono (Finset.subset_insert e A) ⟨_, hp⟩ v)

private def lowerToward (p q : V → ℕ) (v : V) : ℕ :=
  if q v < p v then p v - 1 else p v

private theorem lowerToward_le (p q : V → ℕ) (v : V) :
    lowerToward p q v ≤ p v := by
  unfold lowerToward
  split <;> lia

private theorem le_lowerToward_add_one (p q : V → ℕ) (v : V) :
    p v ≤ lowerToward p q v + 1 := by
  unfold lowerToward
  split <;> lia

/-- Lowering by one exactly where an erased-edge solution is smaller preserves
all original constraints when the erased edge is strictly slack. -/
private theorem lowerToward_feasible {A : Finset E} {e : E} {p q : V → ℕ}
    (hp : G.Feasible A p) (hq : G.Feasible (A.erase e) q)
    (hslack : (p (G.tail e) : ℤ) + G.gain e < p (G.head e)) :
    G.Feasible A (lowerToward p q) := by
  intro f hf
  by_cases hfe : f = e
  · subst f
    have ht := lowerToward_le p q (G.tail e)
    have hh := le_lowerToward_add_one p q (G.head e)
    lia
  · have hp' := hp f hf
    have hq' := hq f (Finset.mem_erase.mpr ⟨hfe, hf⟩)
    simp only [lowerToward]
    split_ifs <;> lia

/-- Removing a strictly slack edge preserves the actual least feasible potential. -/
theorem potential_erase_eq {A : Finset E} {e : E}
    (hA : ∃ p, G.Feasible A p)
    (hslack : (G.potential A (G.tail e) : ℤ) + G.gain e < G.potential A (G.head e)) :
    G.potential (A.erase e) = G.potential A := by
  have hp := G.potential_feasible hA
  have hAe : ∃ p, G.Feasible (A.erase e) p :=
    ⟨_, G.feasible_mono (Finset.erase_subset e A) hp⟩
  have hq := G.potential_feasible hAe
  have hr := G.lowerToward_feasible hp hq hslack
  funext v
  apply le_antisymm (G.potential_mono (Finset.erase_subset e A) hA v)
  by_contra h
  have hdrop : G.potential (A.erase e) v < G.potential A v := by lia
  have hleast := G.potential_le hr v
  simp only [lowerToward, ite_eq_left hdrop] at hleast
  lia

end

end GainData

end VerticalStripLLT.Components
