import VerticalStripLLT.Components.BalancedLiftReach
import VerticalStripLLT.Components.ForwardHRV
import VerticalStripLLT.Circular.HRVConjugacy

/-!
# HRV transport from compatible lifts to a forward diagram

A finite relabeling ordered by compatible chosen lifts preserves the highest
reachable vertex and its fibers. The proof compares actual reachable maxima;
it does not extend the chosen lifts to a global order isomorphism of integers.
-/

namespace VerticalStripLLT.Circular.Orientation

open scoped Classical

variable {n : ℕ} {D E : Diagram n} (θ : Orientation D) (η : Orientation E)

/-- A finite selected-relation relabeling preserves and reflects reachability. -/
theorem selectedReach_relabel_iff (σ : Fin n ≃ Fin n)
    (hrel : ∀ i j, E.edgeData.selected η.val i j ↔
      D.edgeData.selected θ.val (σ i) (σ j)) {i j : Fin n} :
    Relation.ReflTransGen (E.edgeData.selected η.val) i j ↔
      Relation.ReflTransGen (D.edgeData.selected θ.val) (σ i) (σ j) := by
  constructor
  · intro h
    exact h.lift σ (fun u v huv => (hrel u v).mp huv)
  · intro h
    have hb := h.lift σ.symm (fun u v huv =>
      (hrel (σ.symm u) (σ.symm v)).mpr (by simpa only [Equiv.apply_symm_apply] using huv))
    change Relation.ReflTransGen (E.edgeData.selected η.val)
      (σ.symm (σ i)) (σ.symm (σ j)) at hb
    simpa only [Equiv.symm_apply_apply] using hb

variable (hforward : ∀ e : Edge E.area, e.tail < e.head)
variable {q : Fin n → ℤ} (hq : ∀ v, D.residue (q v) = v)
variable (hp : D.naturalGain.BalancedPotential (D.strict ∪ θ.val) q)
variable (σ : Fin n ≃ Fin n) (hmono : StrictMono (q ∘ σ))
variable (hrel : ∀ i j, E.edgeData.selected η.val i j ↔
  D.edgeData.selected θ.val (σ i) (σ j))

include hforward hq hp hmono hrel

/-- The original greatest reachable integer is the chosen lift of the forward HRV. -/
theorem liftedHRV_eq_of_balanced_relabel (i : Fin n) :
    θ.liftedHRV (q (σ i)) = q (σ (η.hrv i)) := by
  apply le_antisymm
  · obtain ⟨v, hv, hreach⟩ := θ.exists_chosen_of_liftReach hq hp
      (θ.liftedHRV_reachable (q (σ i)))
    have hreach' : Relation.ReflTransGen (E.edgeData.selected η.val) i (σ.symm v) := by
      apply (θ.selectedReach_relabel_iff η σ hrel).mpr
      simpa only [Equiv.apply_symm_apply] using hreach
    have hle := η.reachable_le_hrv_of_forward hforward hreach'
    have hqle := hmono.monotone hle
    change q (σ (σ.symm v)) ≤ q (σ (η.hrv i)) at hqle
    rw [Equiv.apply_symm_apply] at hqle
    rw [hv]
    exact hqle
  · apply θ.le_liftedHRV_of_reachable
    apply θ.liftReach_of_selectedReach hq hp
    exact (θ.selectedReach_relabel_iff η σ hrel).mp (η.hrv_reachable i)

/-- Projecting the equality at chosen lifts gives the actual finite HRV conjugacy. -/
theorem hrv_eq_of_balanced_relabel (i : Fin n) :
    θ.hrv (σ i) = σ (η.hrv i) := by
  have h := congrArg D.residue
    (θ.liftedHRV_eq_of_balanced_relabel η hforward hq hp σ hmono hrel i)
  simpa only [θ.residue_liftedHRV_eq_hrv, hq] using h

/-- Corresponding HRV fibers have the same cardinality. -/
theorem hrvFiber_card_of_balanced_relabel (r : Fin n) :
    (Finset.univ.filter fun u => θ.hrv u = σ r).card =
      (Finset.univ.filter fun u => η.hrv u = r).card := by
  classical
  exact η.hrvFiber_card_conjugate θ σ
    (θ.hrv_eq_of_balanced_relabel η hforward hq hp σ hmono hrel) r

/-- Relabeling by compatible chosen lifts preserves the actual elementary HRV monomial. -/
theorem hrvMonomial_eq_of_balanced_relabel : θ.hrvMonomial = η.hrvMonomial :=
  η.hrvMonomial_conjugate θ σ
    (θ.hrv_eq_of_balanced_relabel η hforward hq hp σ hmono hrel)

end VerticalStripLLT.Circular.Orientation
