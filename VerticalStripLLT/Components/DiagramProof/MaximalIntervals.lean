import VerticalStripLLT.Components.DiagramProof.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-! Maximal intervals in a finite forward relation. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

theorem exists_maximal_interval
    {n : ℕ} {R : Fin n → Fin n → Prop}
    (hforward : ∀ ⦃a b : Fin n⦄, R a b → a < b)
    {u v : Fin n} (huv : R u v) :
    ∃ a b, R a b ∧ a ≤ u ∧ v ≤ b ∧
      ∀ x y, R x y → x ≤ a → b ≤ y → x = a ∧ y = b := by
  let P : Finset (Fin n × Fin n) :=
    Finset.univ.filter fun p => R p.1 p.2 ∧ p.1 ≤ u ∧ v ≤ p.2
  have hP : P.Nonempty := by
    refine ⟨(u, v), ?_⟩
    simp [P, huv]
  let L : Finset ℕ := P.image (fun p => p.2.val - p.1.val)
  have hL : L.Nonempty := hP.image _
  obtain ⟨p, hpP, hpmax⟩ :=
    Finset.mem_image.mp (Finset.max'_mem L hL)
  have hpR : R p.1 p.2 := (Finset.mem_filter.mp hpP).2.1
  have hpu : p.1 ≤ u := (Finset.mem_filter.mp hpP).2.2.1
  have hpv : v ≤ p.2 := (Finset.mem_filter.mp hpP).2.2.2
  refine ⟨p.1, p.2, hpR, hpu, hpv, ?_⟩
  intro x y hxy hxa hby
  have hqP : (x, y) ∈ P := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hxy, hxa.trans hpu, hpv.trans hby⟩
  have hqL : y.val - x.val ∈ L := Finset.mem_image.mpr ⟨(x, y), hqP, rfl⟩
  have hle : y.val - x.val ≤ p.2.val - p.1.val := by
    exact (Finset.le_max' L _ hqL).trans_eq hpmax.symm
  have hpxy : p.1 < p.2 := hforward hpR
  have hxy' : x < y := hforward hxy
  have hxval : x.val = p.1.val := by
    apply le_antisymm
    · exact hxa
    · change p.1.val ≤ x.val
      lia
  have hyval : y.val = p.2.val := by
    apply le_antisymm
    · change y.val ≤ p.2.val
      lia
    · exact hby
  exact ⟨Fin.ext hxval, Fin.ext hyval⟩

end VerticalStripLLT.Circular.DiagramProof
