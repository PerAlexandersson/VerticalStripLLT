import VerticalStripLLT.OrientationInsert

namespace VerticalStripLLT

theorem upwardStep_orientationInsert_iff {n : ℕ} {P R : SchroderPath n}
    (a : Fin n × Fin n) (hnot : a ∉ P.normalEdges)
    (hN : R.normalEdges = insert a P.normalEdges)
    (hS : R.strictEdges = P.strictEdges) (b : Bool) (θ : Orientation P)
    (u v : Fin n) :
    upwardStep R ((orientationInsertEquiv a hnot hN).symm (b, θ)) u v ↔
      upwardStep P θ u v ∨ ((u, v) = a ∧ b = true) := by
  classical
  let E := orientationInsertEquiv a hnot hN
  let θR : Orientation R := E.symm (b, θ)
  change upwardStep R θR u v ↔ _
  have haR : a ∈ R.normalEdges := by
    rw [hN]
    simp [hnot]
  have oldR {e : Fin n × Fin n} (he : e ∈ P.normalEdges) :
      e ∈ R.normalEdges := by
    rw [hN]
    simp [he]
  have hnew : θR ⟨a, haR⟩ = b := by
    simp [θR, E, orientationInsertEquiv]
  have hold {e : Fin n × Fin n} (heP : e ∈ P.normalEdges)
      (heR : e ∈ R.normalEdges) :
      θR ⟨e, heR⟩ = θ ⟨e, heP⟩ := by
    have hne : e ≠ a := by
      intro hea
      apply hnot
      simpa [hea] using heP
    simp [θR, E, orientationInsertEquiv, hne]
  constructor
  · intro h
    rcases h with hs | ⟨hn, hv⟩
    · exact Or.inl (Or.inl (by simpa only [hS] using hs))
    · rw [hN] at hn
      rcases Finset.mem_insert.mp hn with rfl | hn
      · right
        exact ⟨rfl, by simpa [hnew] using hv⟩
      · left
        exact Or.inr ⟨hn, hold hn (oldR hn) ▸ hv⟩
  · intro h
    rcases h with h | ⟨ha, hb⟩
    · rcases h with hs | ⟨hn, hv⟩
      · left
        rw [hS]
        exact hs
      · right
        refine ⟨oldR hn, ?_⟩
        exact (hold hn (oldR hn)).symm ▸ hv
    · subst a
      right
      exact ⟨haR, by simpa [hb] using hnew⟩

end VerticalStripLLT
