import VerticalStripLLT.ReductionRecursion
import VerticalStripLLT.RecursionMap

namespace VerticalStripLLT

theorem SatisfiesReductionRecursion.map {A B : Type*} [CommRing A] [CommRing B]
    {q : A} {e : ℕ → A} {F : ∀ n, SchroderPath n → A}
    (H : SatisfiesReductionRecursion q e F) (φ : A →+* B) :
    SatisfiesReductionRecursion (φ q) (fun k => φ (e k))
      (fun n P => φ (F n P)) := by
  refine
    { toSatisfiesRecursion := H.toSatisfiesRecursion.map φ
      firstBounceOneLeadingEast := ?_ }
  intro n U V W hV h hreturn hgap
  simpa only [map_mul] using
    congrArg φ (H.firstBounceOneLeadingEast U V W hV h hreturn hgap)

end VerticalStripLLT
