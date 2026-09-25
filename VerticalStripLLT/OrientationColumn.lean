import VerticalStripLLT.Column
import VerticalStripLLT.OrientationExpansion

namespace VerticalStripLLT

open scoped BigOperators

theorem orientationExpansionAt_column (k : ℕ) (z : Q) :
    orientationExpansionAt (SchroderPath.column k) z =
      elementary k.succPNat := by
  classical
  let P := SchroderPath.column k
  let : IsEmpty {e // e ∈ P.normalEdges} := ⟨fun e => by
    have he := e.property
    simp [P, SchroderPath.column_normalEdges] at he⟩
  let : Unique (Orientation P) := inferInstance
  have hreach : ∀ θ : Orientation P, ∀ u : Fin (k + 1),
      reachable θ u (Fin.last k) := by
    intro θ u
    induction u using Fin.reverseInduction with
    | last => exact self_reachable θ _
    | cast i hi =>
        apply reachable_trans θ (Relation.ReflTransGen.single ?_) hi
        left
        rw [SchroderPath.column_strict_mem_iff]
        simp
  have hhrv : ∀ θ : Orientation P, ∀ u : Fin (k + 1),
      hrv θ u = Fin.last k := by
    intro θ u
    apply le_antisymm
    · exact Fin.le_last _
    · exact reachable_le_hrv θ u _ (hreach θ u)
  have hfiber : ∀ θ : Orientation P, ∀ r : Fin (k + 1),
      hrvFiber θ r = if r = Fin.last k then Finset.univ else ∅ := by
    intro θ r
    by_cases hr : r = Fin.last k
    · subst r
      ext u
      simp [hhrv]
    · ext u
      simp [hhrv, hr, Ne.symm hr]
  have ha (θ : Orientation P) : orientationAsc P θ = 0 := by
    simp [orientationAsc, Finset.univ_eq_empty]
  have hm (θ : Orientation P) : hrvMonomial θ = elementary k.succPNat := by
    unfold hrvMonomial
    rw [Fintype.prod_eq_single (Fin.last k)]
    · simp [hfiber, Nat.succPNat]
    · intro r hr
      simp [hfiber, hr]
  change orientationExpansionAt P z = _
  simp [orientationExpansionAt, ha, hm]

end VerticalStripLLT
