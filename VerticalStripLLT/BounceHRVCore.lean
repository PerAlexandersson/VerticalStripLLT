import VerticalStripLLT.OrientationUnicellular
import VerticalStripLLT.FirstBounceGraph
-- Local helper module: VerticalStripLLT.BounceHRVCore

/-! Highest reachable vertices for arbitrary relations on `Fin n`, a transfer principle
along vertex relabellings, and fibre monomials. -/

namespace VerticalStripLLT
namespace BounceHRV

open scoped BigOperators

variable {n : ℕ}

/-- Highest vertex reachable from `u` along an arbitrary relation. -/
noncomputable def gh (r : Fin n → Fin n → Prop) (u : Fin n) : Fin n := by
  classical
  exact (Finset.univ.filter (Relation.ReflTransGen r u)).max'
    ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩⟩

theorem gh_reach (r : Fin n → Fin n → Prop) (u : Fin n) :
    Relation.ReflTransGen r u (gh r u) := by
  classical
  unfold gh
  exact (Finset.mem_filter.mp (Finset.max'_mem _ _)).2

theorem le_gh_of_reach (r : Fin n → Fin n → Prop) {u w : Fin n}
    (h : Relation.ReflTransGen r u w) : w ≤ gh r u := by
  classical
  unfold gh
  exact Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

theorem le_gh (r : Fin n → Fin n → Prop) (u : Fin n) : u ≤ gh r u :=
  le_gh_of_reach r Relation.ReflTransGen.refl

theorem gh_le_of_step (r : Fin n → Fin n → Prop) {u v : Fin n} (h : r u v) :
    gh r v ≤ gh r u :=
  le_gh_of_reach r (Relation.ReflTransGen.head h (gh_reach r v))

theorem gh_cases (r : Fin n → Fin n → Prop) (u : Fin n) :
    gh r u = u ∨ ∃ v, r u v ∧ gh r v = gh r u := by
  rcases Relation.ReflTransGen.cases_head (gh_reach r u) with h | ⟨v, huv, hv⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨v, huv, le_antisymm (gh_le_of_step r huv) (le_gh_of_reach r hv)⟩

/-- Uniqueness of the highest reachable vertex from its one-step recurrence. -/
theorem gh_eq_of (r : Fin n → Fin n → Prop) {u m : Fin n} (h1 : u ≤ m)
    (h2 : ∀ v, r u v → gh r v ≤ m) (h3 : m = u ∨ ∃ v, r u v ∧ gh r v = m) :
    gh r u = m := by
  apply le_antisymm
  · rcases gh_cases r u with h | ⟨v, huv, hv⟩
    · rw [h]; exact h1
    · rw [← hv]; exact h2 v huv
  · rcases h3 with h | ⟨v, huv, hv⟩
    · rw [h]; exact le_gh r u
    · rw [← hv]; exact gh_le_of_step r huv

theorem gh_congr {r r' : Fin n → Fin n → Prop} (h : ∀ u w, r u w ↔ r' u w) :
    gh r = gh r' := by
  have : r = r' := by
    funext u w
    exact propext (h u w)
  rw [this]

theorem hrv_eq_gh {P : SchroderPath n} (θ : Orientation P) :
    hrv θ = gh (upwardStep P θ) := by
  funext u
  apply le_antisymm
  · exact le_gh_of_reach _ (reachable_hrv θ u)
  · exact reachable_le_hrv θ u _ (gh_reach _ u)

/-- Downward induction on `Fin n`. -/
theorem down_induction {C : Fin n → Prop} (h : ∀ u, (∀ v, u < v → C v) → C u) :
    ∀ u, C u := by
  intro u
  induction u using WellFoundedGT.induction with
  | _ u ih => exact h u ih

/-- One step of transferring highest reachable vertices along a relabelling. -/
theorem transfer_step (r1 r2 : Fin n → Fin n → Prop) (σ g : Fin n → Fin n) (u : Fin n)
    (hσu : σ u = g u) (hsteps : ∀ w, r2 (σ u) w ↔ ∃ v, r1 u v ∧ w = σ v)
    (ih : ∀ v, r1 u v → gh r2 (σ v) = g (gh r1 v))
    (h1 : g u ≤ g (gh r1 u)) (h2 : ∀ v, r1 u v → g (gh r1 v) ≤ g (gh r1 u)) :
    gh r2 (σ u) = g (gh r1 u) := by
  apply gh_eq_of
  · rw [hσu]; exact h1
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := (hsteps w).1 hw
    rw [ih v hv]
    exact h2 v hv
  · rcases gh_cases r1 u with h | ⟨v, huv, hv⟩
    · left; rw [h, hσu]
    · right
      exact ⟨σ v, (hsteps _).2 ⟨v, huv, rfl⟩, by rw [ih v huv, hv]⟩

/-- Relations agreeing on all sources above `k` have the same highest reachable
vertices above `k`. -/
theorem gh_agree_above (r1 r2 : Fin n → Fin n → Prop) (k : Fin n)
    (hup : ∀ u w, r1 u w → u < w) (hag : ∀ u, k < u → ∀ w, r2 u w ↔ r1 u w) :
    ∀ u, k < u → gh r2 u = gh r1 u := by
  refine down_induction fun u ih hu => ?_
  refine transfer_step r1 r2 id id u rfl (fun w => ?_) (fun v hv => ?_) (le_gh r1 u)
    (fun v hv => gh_le_of_step r1 hv)
  · show r2 u w ↔ _
    rw [hag u hu w]
    exact ⟨fun h => ⟨w, h, rfl⟩, fun ⟨v, hv, he⟩ => he ▸ hv⟩
  · exact ih v (hup u v hv) (hu.trans (hup u v hv))

/-- The monomial determined by the fibres of a vertex map. -/
noncomputable def fiberMono (f : Fin n → Fin n) : EExpansion :=
  ∏ r : Fin n, if h : (Finset.univ.filter (fun u => f u = r)).Nonempty then
    elementary ⟨(Finset.univ.filter (fun u => f u = r)).card, Finset.card_pos.mpr h⟩ else 1

theorem hrvMonomial_eq_fiberMono {P : SchroderPath n} (θ : Orientation P) :
    hrvMonomial θ = fiberMono (hrv θ) := rfl

private theorem fiberTerm_congr {s s' : Finset (Fin n)} (h : s.card = s'.card) :
    (if hs : s.Nonempty then (elementary ⟨s.card, Finset.card_pos.mpr hs⟩ : EExpansion)
      else 1) =
    (if hs : s'.Nonempty then elementary ⟨s'.card, Finset.card_pos.mpr hs⟩ else 1) := by
  by_cases hs : s.Nonempty
  · have hs' : s'.Nonempty := Finset.card_pos.mp (h ▸ Finset.card_pos.mpr hs)
    rw [dite_eq_left hs, dite_eq_left hs']
    congr 2
  · have hs' : ¬ s'.Nonempty := fun hs' => hs (Finset.card_pos.mp (h.symm ▸
      Finset.card_pos.mpr hs'))
    rw [dite_eq_right hs, dite_eq_right hs']

/-- Fibre monomials are invariant under conjugating the vertex map by permutations. -/
theorem fiberMono_conj (f1 f2 : Fin n → Fin n) (σ g : Equiv.Perm (Fin n))
    (h : ∀ u, f2 (σ u) = g (f1 u)) : fiberMono f2 = fiberMono f1 := by
  unfold fiberMono
  rw [← Equiv.prod_comp g]
  refine Finset.prod_congr rfl fun r _ => fiberTerm_congr ?_
  refine Finset.card_bij (fun u _ => σ.symm u) ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    have := h (σ.symm u)
    rw [Equiv.apply_symm_apply, hu] at this
    exact g.injective this.symm
  · intro a _ b _ hab
    exact σ.symm.injective hab
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    refine ⟨σ v, ?_, by simp⟩
    rw [h v, hv]

end BounceHRV
end VerticalStripLLT

