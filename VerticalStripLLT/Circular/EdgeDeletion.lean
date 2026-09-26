import VerticalStripLLT.Circular.EdgeColoring
import VerticalStripLLT.ShiftEvaluation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-! Deletion--contraction for a single non-strict edge instance. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

theorem xQShift_C_X_pow' (m k : ℕ) :
    xQShift m (MvPolynomial.C (Polynomial.X ^ k) : XPoly m) =
      MvPolynomial.C ((Polynomial.X + 1) ^ k) := by
  rw [xQShift, MvPolynomial.map_C, map_pow]
  congr 1
  simp [qShift, Polynomial.coe_compRingHom_apply]

theorem xQShift_monomial' {V : Type*} [Fintype V] {m : ℕ} (c : V → Fin m) :
    xQShift m (EdgeData.monomial c) = EdgeData.monomial c := by
  simp [xQShift, EdgeData.monomial]

namespace EdgeData

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Make one more edge strict. -/
def withStrict (G : EdgeData V E) (e : E) : EdgeData V E :=
  { G with strict := insert e G.strict }

/-- Delete one edge. -/
def delete (G : EdgeData V E) (e : E) : EdgeData V {f : E // f ≠ e} where
  tail f := G.tail f.1
  head f := G.head f.1
  strict := G.strict.subtype (· ≠ e)

omit [DecidableEq V] in
theorem shifted_weight (G : EdgeData V E) {m : ℕ} (c : V → Fin m) :
    xQShift m (G.coloringWeight c) =
      if G.admissibleColoring c then
        MvPolynomial.C ((Polynomial.X + 1) ^ (G.ascentEdges c).card) * monomial c
      else 0 := by
  unfold coloringWeight
  split_ifs
  · rw [map_mul, xQShift_C_X_pow', xQShift_monomial']
  · simp

omit [Fintype V] [DecidableEq V] [Fintype E] in
theorem delete_admissible_iff (G : EdgeData V E) (e : E) (he : e ∉ G.strict) {m : ℕ}
    (c : V → Fin m) : (G.delete e).admissibleColoring c ↔ G.admissibleColoring c := by
  constructor
  · intro h f hf
    have hfe : f ≠ e := fun h' => he (h' ▸ hf)
    exact h ⟨f, hfe⟩ (by simpa [delete] using hf)
  · intro h f hf
    exact h f.1 (by simpa [delete] using hf)

omit [Fintype V] [DecidableEq V] [Fintype E] in
theorem withStrict_admissible_iff (G : EdgeData V E) (e : E) {m : ℕ} (c : V → Fin m) :
    (G.withStrict e).admissibleColoring c ↔
      G.admissibleColoring c ∧ c (G.tail e) < c (G.head e) := by
  simp only [admissibleColoring, withStrict, Finset.mem_insert, forall_eq_or_imp]
  tauto

omit [Fintype V] [DecidableEq V] in
theorem withStrict_ascentEdges (G : EdgeData V E) (e : E) {m : ℕ} (c : V → Fin m) :
    (G.withStrict e).ascentEdges c = (G.ascentEdges c).erase e := by
  ext f
  simp only [ascentEdges, normalEdges, withStrict, Finset.mem_filter, Finset.mem_sdiff,
    Finset.mem_univ, Finset.mem_insert, Finset.mem_erase, true_and]
  tauto

omit [Fintype V] [DecidableEq V] in
theorem delete_ascentEdges_card (G : EdgeData V E) (e : E) {m : ℕ} (c : V → Fin m) :
    ((G.delete e).ascentEdges c).card = ((G.ascentEdges c).erase e).card := by
  apply Finset.card_bij (fun f _ => f.1)
  · intro f hf
    simp only [ascentEdges, normalEdges, delete, Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_univ, true_and, Finset.mem_subtype] at hf
    simp only [ascentEdges, normalEdges, Finset.mem_erase, Finset.mem_filter,
      Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact ⟨f.2, hf⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro f hf
    simp only [ascentEdges, normalEdges, Finset.mem_erase, Finset.mem_filter,
      Finset.mem_sdiff, Finset.mem_univ, true_and] at hf
    refine ⟨⟨f, hf.1⟩, ?_, rfl⟩
    simp only [ascentEdges, normalEdges, delete, Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_univ, true_and, Finset.mem_subtype]
    exact hf.2

/-- Deletion--contraction for a non-strict edge, after the `q ↦ q + 1` shift. -/
theorem xQShift_coloringLLT_deletion (G : EdgeData V E) (e : E) (he : e ∉ G.strict)
    (m : ℕ) :
    xQShift m (G.coloringLLT m) =
      MvPolynomial.C Polynomial.X * xQShift m ((G.withStrict e).coloringLLT m) +
        xQShift m ((G.delete e).coloringLLT m) := by
  simp only [coloringLLT, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  rw [shifted_weight, shifted_weight, shifted_weight, delete_admissible_iff G e he,
    withStrict_admissible_iff, withStrict_ascentEdges, delete_ascentEdges_card]
  by_cases hadm : G.admissibleColoring c
  · by_cases hasc : c (G.tail e) < c (G.head e)
    · have hmem : e ∈ G.ascentEdges c := by
        simp [ascentEdges, normalEdges, he, hasc]
      have hcard := Finset.card_erase_add_one hmem
      rw [← hcard]
      simp only [hadm, hasc, and_self, ite_true]
      rw [pow_succ, MvPolynomial.C_mul]
      simp only [map_add, map_one]
      ring
    · have hnot : e ∉ G.ascentEdges c := by
        simp [ascentEdges, hasc]
      rw [Finset.erase_eq_of_notMem hnot]
      simp [hadm, hasc]
  · simp [hadm]

variable {E' : Type*} [Fintype E'] [DecidableEq E']

/-- The coloring LLT polynomial only depends on the edge data up to relabelling edges. -/
theorem coloringLLT_congr (G : EdgeData V E) (G' : EdgeData V E') (σ : E' ≃ E)
    (ht : ∀ f, G'.tail f = G.tail (σ f)) (hh : ∀ f, G'.head f = G.head (σ f))
    (hs : ∀ f, f ∈ G'.strict ↔ σ f ∈ G.strict) (m : ℕ) :
    G'.coloringLLT m = G.coloringLLT m := by
  unfold coloringLLT
  apply Finset.sum_congr rfl
  intro c _
  have hadm : G'.admissibleColoring c ↔ G.admissibleColoring c := by
    constructor
    · intro h f hf
      have := h (σ.symm f) ((hs _).mpr (by simpa using hf))
      simpa [ht, hh] using this
    · intro h f hf
      rw [ht, hh]
      exact h (σ f) ((hs f).mp hf)
  have hcard : (G'.ascentEdges c).card = (G.ascentEdges c).card := by
    apply Finset.card_bij (fun f _ => σ f)
    · intro f hf
      simp only [ascentEdges, normalEdges, Finset.mem_filter, Finset.mem_sdiff,
        Finset.mem_univ, true_and] at hf ⊢
      rw [ht, hh] at hf
      exact ⟨fun h' => hf.1 ((hs f).mpr h'), hf.2⟩
    · intro a _ b _ h
      exact σ.injective h
    · intro f hf
      refine ⟨σ.symm f, ?_, by simp⟩
      simp only [ascentEdges, normalEdges, Finset.mem_filter, Finset.mem_sdiff,
        Finset.mem_univ, true_and] at hf ⊢
      rw [ht, hh, hs]
      simpa using hf
  unfold coloringWeight
  simp only [hadm, hcard]

end EdgeData

end VerticalStripLLT.Circular
