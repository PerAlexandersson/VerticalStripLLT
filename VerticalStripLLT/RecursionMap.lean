import VerticalStripLLT.Recursion

namespace VerticalStripLLT

theorem SatisfiesRecursion.map {A B : Type*} [CommRing A] [CommRing B]
    {q : A} {e : ℕ → A} {F : ∀ n, SchroderPath n → A}
    (H : SatisfiesRecursion q e F) (φ : A →+* B) :
    SatisfiesRecursion (φ q) (fun k => φ (e k))
      (fun n P => φ (F n P)) := by
  refine
    { empty := ?_
      column := ?_
      concat := ?_
      unicellular := ?_
      firstBounce := ?_
      secondBounce := ?_ }
  · simpa using congrArg φ H.empty
  · intro k
    exact congrArg φ (H.column k)
  · intro n k P Q
    simpa only [map_mul] using congrArg φ (H.concat P Q)
  · intro n U V h
    simpa only [map_sub, map_mul, map_one] using congrArg φ (H.unicellular U V h)
  · intro n U V W hV h hreturn hgap
    simpa only [map_mul] using congrArg φ (H.firstBounce U V W hV h hreturn hgap)
  · intro n U V W hV h hreturn hgap
    exact congrArg φ (H.secondBounce U V W hV h hreturn hgap)

end VerticalStripLLT
