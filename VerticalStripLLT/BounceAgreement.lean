import VerticalStripLLT.GeneralizedFirstBounce
import VerticalStripLLT.GeneralizedSecondBounceReduction
import VerticalStripLLT.GeneralizedThirdBounceReduction

namespace VerticalStripLLT

open Step

namespace SatisfiesReductionRecursion

/-- Agreement below a fixed first-east measure lifts across any terminal generalized bounce. -/
theorem bounce_agreement {K : Type*} [CommRing K] [IsDomain K]
    {q : K} {e : ℕ → K} {F G : ∀ n, SchroderPath n → K}
    (H : SatisfiesReductionRecursion q e F) (HG : SatisfiesReductionRecursion q e G)
    (hq : q - 1 ≠ 0) {n : ℕ} {Y W : List Step} (hseed : BounceSeed Y)
    (hv : validFrom n 0 0 (Y ++ east :: W) = true)
    (hsmall : ∀ Q : SchroderPath n,
      eastCount Q.steps = eastCount (Y ++ east :: W) →
      firstEastHeight Q.steps < firstEastHeight (Y ++ east :: W) → F n Q = G n Q) :
    F n ⟨Y ++ east :: W, hv⟩ = G n ⟨Y ++ east :: W, hv⟩ := by
  obtain ⟨U, V, s, t, hd⟩ := hseed.trace.decompose
  have hp := hd.parts
  cases s <;> cases t
  · obtain ⟨Q, hQ, hF, hQc, hQh⟩ := H.generalizedFirstBounce hq hseed hd hv
    obtain ⟨Q', hQ', hG, _, _⟩ := HG.generalizedFirstBounce hq hseed hd hv
    have hsmallQ := hsmall Q hQc hQh
    have halign : G n Q = G n Q' :=
      SchroderPath.invariant_congr G Q Q' rfl (hQ.trans hQ'.symm)
    calc
      F n ⟨Y ++ east :: W, hv⟩ = q * F n Q := hF
      _ = q * G n Q := by rw [hsmallQ]
      _ = G n ⟨Y ++ east :: W, hv⟩ := by rw [halign, ← hG]
  · obtain ⟨Q, R, hQ, hR, hF, hQc, hRc, hQh, hRh⟩ :=
      H.generalizedThirdBounce hq hseed hd hv
    obtain ⟨Q', R', hQ', hR', hG, _, _, _, _⟩ :=
      HG.generalizedThirdBounce hq hseed hd hv
    have hsmallQ := hsmall Q hQc hQh
    have hsmallR := hsmall R hRc hRh
    have hQalign : G n Q = G n Q' :=
      SchroderPath.invariant_congr G Q Q' rfl (hQ.trans hQ'.symm)
    have hRalign : G n R = G n R' :=
      SchroderPath.invariant_congr G R R' rfl (hR.trans hR'.symm)
    calc
      F n ⟨Y ++ east :: W, hv⟩ = (q - 1) * F n Q + q * F n R := hF
      _ = (q - 1) * G n Q + q * G n R := by rw [hsmallQ, hsmallR]
      _ = G n ⟨Y ++ east :: W, hv⟩ := by rw [hQalign, hRalign, ← hG]
  · exact False.elim (hp.2.1 rfl)
  · obtain ⟨Q, hQ, hF, hQc, hQh⟩ := H.generalizedSecondBounce hq hseed hd hv
    obtain ⟨Q', hQ', hG, _, _⟩ := HG.generalizedSecondBounce hq hseed hd hv
    have hsmallQ := hsmall Q hQc hQh
    have halign : G n Q = G n Q' :=
      SchroderPath.invariant_congr G Q Q' rfl (hQ.trans hQ'.symm)
    calc
      F n ⟨Y ++ east :: W, hv⟩ = F n Q := hF
      _ = G n Q := hsmallQ
      _ = G n ⟨Y ++ east :: W, hv⟩ := by rw [halign, ← hG]
  · exact False.elim (hp.2.2.1 ⟨rfl, rfl⟩)
  · exact False.elim (hp.2.1 rfl)
  · exact False.elim (hp.1 rfl)
  · exact False.elim (hp.1 rfl)
  · exact False.elim (hp.1 rfl)

end SatisfiesReductionRecursion

end VerticalStripLLT
