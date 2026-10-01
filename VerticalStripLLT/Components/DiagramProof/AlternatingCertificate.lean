import VerticalStripLLT.Components.DiagramProof.AlternatingDeletion
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# The signed recurrence from alternating corner deletion

If no state of a whole component has every strict corner covering, the
alternating sum over deletion sets vanishes at each state. Moving the empty
deletion to the other side expresses the component by whole components of
diagrams with at least one strict corner deleted, with the same signed integer
coefficients for both marked values.
-/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

/-- All strict endpoint pairs. -/
def strictPairs {n : ℕ} (D : Diagram n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun x => strictRel D x.1 x.2

@[simp]
theorem mem_strictPairs {n : ℕ} {D : Diagram n} {x : Fin n × Fin n} :
    x ∈ strictPairs D ↔ strictRel D x.1 x.2 := by
  simp [strictPairs]

variable {k : ℕ} {D : Diagram (k + 1)} (hD : Forward D)

theorem deleteStrict_measureLT {T : Finset (Fin (k + 1) × Fin (k + 1))}
    (hT : T ⊆ strictPairs D) (hne : T.Nonempty) : MeasureLT (deleteStrict hD T) D := by
  left
  apply naturalArea_lt_of_ssubset
  rw [Finset.ssubset_iff_of_subset]
  · obtain ⟨t, ht⟩ := hne
    have hst : strictRel D t.1 t.2 := mem_strictPairs.mp (hT ht)
    refine ⟨t, mem_naturalPairs.mpr (naturalRel_of_strictRel hst), ?_⟩
    rw [mem_naturalPairs, deleteStrict_naturalRel]
    exact fun h => h.2 ⟨ht, hst⟩
  · intro x hx
    rw [mem_naturalPairs, deleteStrict_naturalRel] at hx
    exact mem_naturalPairs.mpr hx.1

theorem deleteState_empty_values (η : Orientation D) (m : ℕ) (β : Fin m) :
    markedK (deleteState hD ∅ η) (Fin.last k) m β = markedK η (Fin.last k) m β ∧
      markedE (deleteState hD ∅ η) (Fin.last k) m β = markedE η (Fin.last k) m β := by
  apply markedValues_eq_of_transGen_eq (deleteStrict_forward hD ∅) hD
  congr 1
  funext u v
  apply propext
  rw [deleteState_selected]
  simp [RemovedPair]

/-- At a state with a non-covering strict corner, the alternating deletion sum vanishes. -/
theorem alternating_sum_eq_zero (η : Orientation D) {s : Fin (k + 1) × Fin (k + 1)}
    (hs : s ∈ strictPairs D) (hnc : ¬ Cover η s.1 s.2) (m : ℕ) (β : Fin m) :
    ∑ T ∈ (strictPairs D).powerset,
        ((-1 : ℤ) ^ T.card) • markedK (deleteState hD T η) (Fin.last k) m β = 0 ∧
      ∑ T ∈ (strictPairs D).powerset,
        ((-1 : ℤ) ^ T.card) • markedE (deleteState hD T η) (Fin.last k) m β = 0 := by
  have hF : strictPairs D = insert s ((strictPairs D).erase s) := (Finset.insert_erase hs).symm
  have hnot : s ∉ (strictPairs D).erase s := Finset.notMem_erase s _
  have hval (T : Finset (Fin (k + 1) × Fin (k + 1))) (hT : T ∈ ((strictPairs D).erase s).powerset) :
      s ∉ T ∧
      markedK (deleteState hD T η) (Fin.last k) m β =
        markedK (deleteState hD (insert s T) η) (Fin.last k) m β ∧
      markedE (deleteState hD T η) (Fin.last k) m β =
        markedE (deleteState hD (insert s T) η) (Fin.last k) m β := by
    have hsT : s ∉ T := fun h => hnot (Finset.mem_powerset.mp hT h)
    exact ⟨hsT, markedValues_eq_of_transGen_eq (deleteStrict_forward hD T)
      (deleteStrict_forward hD (insert s T)) _ _
      (transGen_delete_insert hD T η (mem_strictPairs.mp hs) hsT hnc) (Fin.last k) m β⟩
  constructor
  · rw [hF, Finset.sum_powerset_insert hnot, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro T hT
    obtain ⟨hsT, hK, -⟩ := hval T hT
    rw [Finset.card_insert_of_notMem hsT, pow_succ, hK, mul_neg_one, neg_smul, add_neg_cancel]
  · rw [hF, Finset.sum_powerset_insert hnot, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro T hT
    obtain ⟨hsT, -, hE⟩ := hval T hT
    rw [Finset.card_insert_of_notMem hsT, pow_succ, hE, mul_neg_one, neg_smul, add_neg_cancel]

/-- The flip-closed deletion image of the component of `θ`. -/
abbrev deleteImage (T : Finset (Fin (k + 1) × Fin (k + 1))) (θ : Orientation D) :
    Finset (Orientation (deleteStrict hD T)) :=
  (flipComponent D θ).image (deleteState hD T)

/-- **Alternating deletion.** A whole component with no state in which every strict
corner covers has a signed certificate by whole components of smaller diagrams. -/
theorem certifies_alternating (θ : Orientation D)
    (hno : ∀ η ∈ flipComponent D θ, ∃ s ∈ strictPairs D, ¬ Cover η s.1 s.2) :
    ∃ c : Cert k, Certifies ⟨D, hD, θ⟩ c := by
  let I := (strictPairs D).powerset.erase ∅
  let cT : Finset (Fin (k + 1) × Fin (k + 1)) → Cert k := fun T =>
    layerCert (deleteStrict_forward hD T) (deleteImage hD T θ) (deleteImage_closed hD T θ)
  refine ⟨∑ T ∈ I, (-((-1 : ℤ) ^ T.card)) • cT T, fun m β => ⟨?_, ?_⟩, ?_⟩
  · -- The strict-coloring value.
    have hsum (T : Finset (Fin (k + 1) × Fin (k + 1))) :
        ∑ η ∈ flipComponent D θ, markedK (deleteState hD T η) (Fin.last k) m β =
          Cert.K (cT T) m β := by
      rw [← layerCert_K, Finset.sum_image (fun x _ y _ h => deleteState_injective hD T h)]
    have hzero : ∑ η ∈ flipComponent D θ, ∑ T ∈ (strictPairs D).powerset,
        ((-1 : ℤ) ^ T.card) • markedK (deleteState hD T η) (Fin.last k) m β = 0 := by
      apply Finset.sum_eq_zero
      intro η hη
      obtain ⟨s, hs, hnc⟩ := hno η hη
      exact (alternating_sum_eq_zero hD η hs hnc m β).1
    rw [Finset.sum_comm, ← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset _)] at hzero
    simp only [Finset.card_empty, pow_zero, one_smul, ← Finset.smul_sum] at hzero
    have hrhs : Cert.K (∑ T ∈ I, (-((-1 : ℤ) ^ T.card)) • cT T) m β =
        -∑ T ∈ (strictPairs D).powerset.erase ∅, ((-1 : ℤ) ^ T.card) •
          ∑ η ∈ flipComponent D θ, markedK (deleteState hD T η) (Fin.last k) m β := by
      rw [Cert.K_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [Cert.K_zsmul, ← hsum, neg_smul]
    rw [hrhs, ← eq_neg_of_add_eq_zero_left hzero]
    unfold Comp.K componentMarkedK
    exact Finset.sum_congr rfl fun η _ => ((deleteState_empty_values hD η m β).1).symm
  · have hsum (T : Finset (Fin (k + 1) × Fin (k + 1))) :
        ∑ η ∈ flipComponent D θ, markedE (deleteState hD T η) (Fin.last k) m β =
          Cert.E (cT T) m β := by
      rw [← layerCert_E, Finset.sum_image (fun x _ y _ h => deleteState_injective hD T h)]
    have hzero : ∑ η ∈ flipComponent D θ, ∑ T ∈ (strictPairs D).powerset,
        ((-1 : ℤ) ^ T.card) • markedE (deleteState hD T η) (Fin.last k) m β = 0 := by
      apply Finset.sum_eq_zero
      intro η hη
      obtain ⟨s, hs, hnc⟩ := hno η hη
      exact (alternating_sum_eq_zero hD η hs hnc m β).2
    rw [Finset.sum_comm, ← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset _)] at hzero
    simp only [Finset.card_empty, pow_zero, one_smul, ← Finset.smul_sum] at hzero
    have hrhs : Cert.E (∑ T ∈ I, (-((-1 : ℤ) ^ T.card)) • cT T) m β =
        -∑ T ∈ (strictPairs D).powerset.erase ∅, ((-1 : ℤ) ^ T.card) •
          ∑ η ∈ flipComponent D θ, markedE (deleteState hD T η) (Fin.last k) m β := by
      rw [Cert.E_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [Cert.E_zsmul, ← hsum, neg_smul]
    rw [hrhs, ← eq_neg_of_add_eq_zero_left hzero]
    unfold Comp.E componentMarkedE
    exact Finset.sum_congr rfl fun η _ => ((deleteState_empty_values hD η m β).2).symm
  · apply Cert.smaller_sum
    intro T hT
    apply Cert.smaller_zsmul
    apply layerCert_smaller
    have hT' := Finset.mem_erase.mp hT
    exact deleteStrict_measureLT hD (Finset.mem_powerset.mp hT'.2)
      (Finset.nonempty_iff_ne_empty.mpr hT'.1)

end

end VerticalStripLLT.Circular.DiagramProof
