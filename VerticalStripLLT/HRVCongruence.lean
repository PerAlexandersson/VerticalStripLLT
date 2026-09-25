import VerticalStripLLT.OrientationExpansion

namespace VerticalStripLLT

theorem reachable_congr_of_upwardStep {n : ℕ} {P Q : SchroderPath n}
    {θ : Orientation P} {η : Orientation Q}
    (hrel : ∀ u v, upwardStep P θ u v ↔ upwardStep Q η u v)
    (u v : Fin n) : reachable θ u v ↔ reachable η u v := by
  have hr : upwardStep P θ = upwardStep Q η := by
    funext a b
    exact propext (hrel a b)
  simp only [reachable, hr]

theorem hrv_congr_of_upwardStep {n : ℕ} {P Q : SchroderPath n}
    {θ : Orientation P} {η : Orientation Q}
    (hrel : ∀ u v, upwardStep P θ u v ↔ upwardStep Q η u v)
    (u : Fin n) : hrv θ u = hrv η u := by
  apply le_antisymm
  · apply reachable_le_hrv η u (hrv θ u)
    exact (reachable_congr_of_upwardStep hrel u (hrv θ u)).mp
      (reachable_hrv θ u)
  · apply reachable_le_hrv θ u (hrv η u)
    exact (reachable_congr_of_upwardStep hrel u (hrv η u)).mpr
      (reachable_hrv η u)

theorem hrvFiber_congr_of_upwardStep {n : ℕ} {P Q : SchroderPath n}
    {θ : Orientation P} {η : Orientation Q}
    (hrel : ∀ u v, upwardStep P θ u v ↔ upwardStep Q η u v)
    (r : Fin n) : hrvFiber θ r = hrvFiber η r := by
  ext u
  simp only [mem_hrvFiber]
  exact hrv_congr_of_upwardStep hrel u ▸ Iff.rfl

theorem hrvMonomial_congr_of_upwardStep {n : ℕ} {P Q : SchroderPath n}
    {θ : Orientation P} {η : Orientation Q}
    (hrel : ∀ u v, upwardStep P θ u v ↔ upwardStep Q η u v) :
    hrvMonomial θ = hrvMonomial η := by
  classical
  simp only [hrvMonomial]
  congr 1
  funext r
  simp only [hrvFiber_congr_of_upwardStep hrel r]

end VerticalStripLLT
