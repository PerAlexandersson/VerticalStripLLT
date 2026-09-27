import VerticalStripLLT.Components.GainCoefficientCancellation

/-! A totally cyclic zero-gain selection is empty. -/

namespace VerticalStripLLT.Components.GainData

open Classical OrderedPartitions

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq E]

theorem eq_empty_of_zeroGain_simpleNegative_totallyCyclic
    (G : GainData V E) (A : Finset E)
    (hz : ∀ e ∈ A, G.gain e = 0)
    (hn : G.SimpleCyclesNegative A)
    (ht : TotallyCyclic (G.selectedRelation A)) :
    A = ∅ := by
  obtain ⟨p, hp⟩ :=
    (G.exists_feasible_strictScale_iff A (Fintype.card V) le_rfl).mpr hn
  have hstep {x y : V} (hxy : G.selectedRelation A x y) : p x ≤ p y := by
    obtain ⟨e, he, rfl, rfl⟩ := hxy
    have h : (p (G.tail e) : ℤ) + 1 ≤ p (G.head e) := by
      simpa [strictScale, hz e he] using hp e he
    have hnat : p (G.tail e) + 1 ≤ p (G.head e) := by
      exact_mod_cast h
    exact Nat.le_of_lt (Nat.lt_of_succ_le hnat)
  have hmono {x y : V}
      (hxy : Relation.ReflTransGen (G.selectedRelation A) x y) :
      p x ≤ p y := by
    induction hxy with
    | refl => exact le_rfl
    | tail _ hstep' ih => exact ih.trans (hstep hstep')
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have hforward : G.selectedRelation A (G.tail e) (G.head e) :=
    ⟨e, he, rfl, rfl⟩
  have hreverse := ht hforward
  have hle : p (G.head e) ≤ p (G.tail e) := hmono hreverse
  have hstrict : p (G.tail e) < p (G.head e) := by
    have h : (p (G.tail e) : ℤ) + 1 ≤ p (G.head e) := by
      simpa [strictScale, hz e he] using hp e he
    have hnat : p (G.tail e) + 1 ≤ p (G.head e) := by
      exact_mod_cast h
    exact Nat.lt_of_succ_le hnat
  exact (Nat.not_lt_of_ge hle) hstrict

end

end VerticalStripLLT.Components.GainData
