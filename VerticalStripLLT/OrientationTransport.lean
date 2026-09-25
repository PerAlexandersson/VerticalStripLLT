import VerticalStripLLT.OrientationExpansion

open scoped BigOperators

namespace VerticalStripLLT

def orientationTransport {n : ℕ} {P R : SchroderPath n}
    (hN : P.normalEdges = R.normalEdges) : Orientation P ≃ Orientation R :=
  Equiv.arrowCongr (Equiv.subtypeEquivRight fun e => by rw [hN])
    (Equiv.refl Bool)

@[simp] theorem orientationTransport_apply {n : ℕ} {P R : SchroderPath n}
    (hN : P.normalEdges = R.normalEdges) (θ : Orientation P)
    (e : Fin n × Fin n) (he : e ∈ R.normalEdges) :
    orientationTransport hN θ ⟨e, he⟩ = θ ⟨e, hN ▸ he⟩ := rfl

private theorem card_filter_subtype_transport {α : Type} {s t : Finset α}
    (hst : s = t) (f : {x // x ∈ s} → Bool) :
    (Finset.univ.filter fun x : {x // x ∈ t} =>
      f ⟨x.1, hst ▸ x.2⟩ = true).card =
      (Finset.univ.filter fun x : {x // x ∈ s} => f x = true).card := by
  subst hst
  rfl

theorem orientationAsc_transport {n : ℕ} {P R : SchroderPath n}
    (hN : P.normalEdges = R.normalEdges) (θ : Orientation P) :
    orientationAsc R (orientationTransport hN θ) = orientationAsc P θ := by
  unfold orientationAsc
  exact card_filter_subtype_transport hN θ

theorem upwardStep_transport_iff {n : ℕ} {P R : SchroderPath n}
    (hN : P.normalEdges = R.normalEdges) (θ : Orientation P) (u v : Fin n) :
    upwardStep R (orientationTransport hN θ) u v ↔
      (u, v) ∈ R.strictEdges ∨
        ∃ h : (u, v) ∈ P.normalEdges, θ ⟨(u, v), h⟩ = true := by
  unfold upwardStep
  constructor
  · rintro (hs | ⟨hn, hv⟩)
    · exact Or.inl hs
    · exact Or.inr ⟨hN ▸ hn, hv⟩
  · rintro (hs | ⟨hn, hv⟩)
    · exact Or.inl hs
    · exact Or.inr ⟨hN ▸ hn, hv⟩

theorem orientationExpansionAt_sum_transport {n : ℕ} {P R : SchroderPath n}
    (hN : P.normalEdges = R.normalEdges) (z : Q) :
    ∑ θ : Orientation P,
      MvPolynomial.C (z ^ orientationAsc R (orientationTransport hN θ)) *
        hrvMonomial (orientationTransport hN θ) =
      orientationExpansionAt R z := by
  unfold orientationExpansionAt
  exact Equiv.sum_comp (orientationTransport hN)
    (fun η => MvPolynomial.C (z ^ orientationAsc R η) * hrvMonomial η)

end VerticalStripLLT
