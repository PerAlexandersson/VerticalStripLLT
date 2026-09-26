import VerticalStripLLT.Circular.BoundaryRow
import VerticalStripLLT.Circular.StrictEdgeInjectivity

/-! Extensionality principles for circular areas and diagrams. -/

namespace VerticalStripLLT.Circular

open scoped Classical

private theorem residue_intCast_eq {n : ℕ} (D : Diagram n) (v : Fin n) :
    D.residue (v.val : ℤ) = v := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [D.residue_coe_val]
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast v.isLt)

theorem CircularArea.ext_of_area_eq {n : ℕ} {A B : CircularArea n}
    (h : A.area = B.area) : A = B := by
  cases A with
  | mk hp a hb hc =>
    cases B with
    | mk hq b hd he =>
      simp_all only

namespace Diagram

theorem ext_of_area_eq_of_strictAt {n : ℕ} {D D' : Diagram n}
    (harea : D.area.area = D'.area.area)
    (hstrict : ∀ z : ℤ, D.strictAt z ↔ D'.strictAt z) : D = D' := by
  rcases D with ⟨A, S, hS⟩
  rcases D' with ⟨A', T, hT⟩
  have hA : A = A' := CircularArea.ext_of_area_eq harea
  subst A'
  have hs : S = T := by
    ext e
    have hsAt := hstrict (e.head.val : ℤ)
    constructor
    · intro he
      have hz : (Diagram.mk A S hS).strictAt (e.head.val : ℤ) :=
        ⟨e, he, (residue_intCast_eq _ e.head).symm⟩
      obtain ⟨f, hf, hh⟩ := hsAt.mp hz
      have hh' : f.head = e.head := hh.trans (residue_intCast_eq _ e.head)
      have hef : f = e := by
        apply Subtype.ext
        apply Prod.ext hh'
        apply Fin.ext
        change f.length.val = e.length.val
        rw [(hT f hf).1, (hS e he).1, hh']
      simpa only [hef] using hf
    · intro he
      have hz : (Diagram.mk A T hT).strictAt (e.head.val : ℤ) :=
        ⟨e, he, (residue_intCast_eq _ e.head).symm⟩
      obtain ⟨f, hf, hh⟩ := hsAt.mpr hz
      have hh' : f.head = e.head := hh.trans (residue_intCast_eq _ e.head)
      have hef : f = e := by
        apply Subtype.ext
        apply Prod.ext hh'
        apply Fin.ext
        change f.length.val = e.length.val
        rw [(hS f hf).1, (hT e he).1, hh']
      simpa only [hef] using hf
  subst T
  rfl

end Diagram
end VerticalStripLLT.Circular
