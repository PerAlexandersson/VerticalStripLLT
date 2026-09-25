import VerticalStripLLT.Orientation
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Relation

namespace VerticalStripLLT

def reachable {n : ℕ} {P : SchroderPath n} (θ : Orientation P)
    (u v : Fin n) : Prop := Relation.ReflTransGen (upwardStep P θ) u v

noncomputable def reachableSet {n : ℕ} {P : SchroderPath n} (θ : Orientation P)
    (u : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (reachable θ u)

theorem self_reachable {n : ℕ} {P : SchroderPath n} (θ : Orientation P)
    (u : Fin n) : reachable θ u u := Relation.ReflTransGen.refl

theorem reachableSet_nonempty {n : ℕ} {P : SchroderPath n} (θ : Orientation P)
    (u : Fin n) : (reachableSet θ u).Nonempty := by
  classical
  refine ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, self_reachable θ u⟩⟩

noncomputable def hrv {n : ℕ} {P : SchroderPath n} (θ : Orientation P)
    (u : Fin n) : Fin n :=
  (reachableSet θ u).max' (reachableSet_nonempty θ u)

theorem reachable_hrv {n : ℕ} {P : SchroderPath n} (θ : Orientation P)
    (u : Fin n) : reachable θ u (hrv θ u) := by
  classical
  exact (Finset.mem_filter.mp ((reachableSet θ u).max'_mem _)).2

theorem reachable_le_hrv {n : ℕ} {P : SchroderPath n} (θ : Orientation P)
    (u v : Fin n) (h : reachable θ u v) : v ≤ hrv θ u := by
  classical
  exact (reachableSet θ u).le_max' v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

theorem le_hrv {n : ℕ} {P : SchroderPath n} (θ : Orientation P)
    (u : Fin n) : u ≤ hrv θ u :=
  reachable_le_hrv θ u u (self_reachable θ u)

theorem reachable_trans {n : ℕ} {P : SchroderPath n} (θ : Orientation P)
    {u v w : Fin n} : reachable θ u v → reachable θ v w → reachable θ u w := by
  exact Relation.ReflTransGen.trans

theorem reachable_hrv_le_hrv {n : ℕ} {P : SchroderPath n} (θ : Orientation P)
    {u v : Fin n} (h : reachable θ u v) : hrv θ v ≤ hrv θ u := by
  classical
  apply reachable_le_hrv θ u (hrv θ v)
  exact reachable_trans θ h (reachable_hrv θ v)

theorem hrv_reachable_hrv {n : ℕ} {P : SchroderPath n} (θ : Orientation P)
    (u : Fin n) : hrv θ (hrv θ u) = hrv θ u := by
  apply le_antisymm
  · exact reachable_hrv_le_hrv θ (reachable_hrv θ u)
  · exact le_hrv θ _

end VerticalStripLLT
