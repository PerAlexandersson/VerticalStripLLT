import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation

/-! Finite ancestor depths for strict directed relations. -/

namespace VerticalStripLLT.Circular

variable {V W : Type*}

/-- The number of proper directed ancestors of a vertex. -/
noncomputable def ancestorDepth [Fintype V] [DecidableEq V] (R : V → V → Prop) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter fun u => Relation.TransGen R u v).card

/-- Along an acyclic strict path, the ancestor depth strictly increases. -/
theorem ancestorDepth_lt_of_transGen [Fintype V] [DecidableEq V] (R : V → V → Prop)
    (acyclic : ∀ v, ¬ Relation.TransGen R v v) {u v : V}
    (huv : Relation.TransGen R u v) :
    ancestorDepth R u < ancestorDepth R v := by
  classical
  unfold ancestorDepth
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨u, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact huv
    · intro huu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at huu
      exact acyclic u huu
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact hw.trans huv

/-- Ancestor depth is invariant under a relation-preserving equivalence of vertices. -/
theorem ancestorDepth_equiv [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (R : V → V → Prop) (T : W → W → Prop) (σ : V ≃ W)
    (hσ : ∀ u v, R u v ↔ T (σ u) (σ v)) (v : V) :
    ancestorDepth T (σ v) = ancestorDepth R v := by
  classical
  have htrans : ∀ u v, Relation.TransGen R u v ↔ Relation.TransGen T (σ u) (σ v) := by
    intro u v
    constructor
    · exact Relation.TransGen.lift σ (fun x y hxy => (hσ x y).mp hxy) _ _
    · intro huv
      have hback := Relation.TransGen.lift σ.symm
        (fun x y hxy => by
          apply (hσ (σ.symm x) (σ.symm y)).mpr
          simpa using hxy) _ _ huv
      simpa [Function.onFun] using hback
  unfold ancestorDepth
  symm
  apply Finset.card_equiv σ
  intro u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact htrans u v

end VerticalStripLLT.Circular
