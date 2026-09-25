import VerticalStripLLT.HRV
import VerticalStripLLT.Polynomial
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi

namespace VerticalStripLLT

open scoped BigOperators

/-- The fiber of the highest reachable vertex map over a representative. -/
noncomputable def hrvFiber {n : ℕ} {P : SchroderPath n} (θ : Orientation P)
    (r : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun u => hrv θ u = r)

@[simp] theorem mem_hrvFiber {n : ℕ} {P : SchroderPath n} (θ : Orientation P)
    (r u : Fin n) : u ∈ hrvFiber θ r ↔ hrv θ u = r := by
  classical
  simp [hrvFiber]

theorem hrvFiber_nonempty_iff {n : ℕ} {P : SchroderPath n} (θ : Orientation P)
    (r : Fin n) : (hrvFiber θ r).Nonempty ↔ hrv θ r = r := by
  classical
  constructor
  · rintro ⟨u, hu⟩
    have hur : hrv θ u = r := (mem_hrvFiber θ r u).mp hu
    calc
      hrv θ r = hrv θ (hrv θ u) := by rw [hur]
      _ = hrv θ u := hrv_reachable_hrv θ u
      _ = r := hur
  · intro hr
    exact ⟨r, (mem_hrvFiber θ r r).mpr hr⟩

noncomputable def hrvMonomial {n : ℕ} {P : SchroderPath n} (θ : Orientation P) :
    EExpansion :=
  ∏ r : Fin n, if h : (hrvFiber θ r).Nonempty then
    elementary ⟨(hrvFiber θ r).card, Finset.card_pos.mpr h⟩ else 1

noncomputable def orientationExpansionAt {n : ℕ} (P : SchroderPath n) (z : Q) :
    EExpansion :=
  ∑ θ : Orientation P, MvPolynomial.C (z ^ orientationAsc P θ) * hrvMonomial θ

noncomputable def orientationExpansion {n : ℕ} (P : SchroderPath n) : EExpansion :=
  orientationExpansionAt P (Polynomial.X - 1)

noncomputable def shiftedOrientationExpansion {n : ℕ} (P : SchroderPath n) : EExpansion :=
  orientationExpansionAt P Polynomial.X

theorem orientationExpansionAt_empty (z : Q) :
    orientationExpansionAt SchroderPath.empty z = 1 := by
  classical
  let : IsEmpty {e // e ∈ SchroderPath.empty.normalEdges} :=
    ⟨fun e => Fin.elim0 e.1.1⟩
  have ha (θ : Orientation SchroderPath.empty) : orientationAsc _ θ = 0 := by
    simp [orientationAsc, Finset.univ_eq_empty]
  simp [orientationExpansionAt, ha, hrvMonomial]

theorem orientationExpansion_empty : orientationExpansion SchroderPath.empty = 1 := by
  exact orientationExpansionAt_empty _

theorem shiftedOrientationExpansion_empty :
    shiftedOrientationExpansion SchroderPath.empty = 1 := by
  exact orientationExpansionAt_empty _

end VerticalStripLLT
