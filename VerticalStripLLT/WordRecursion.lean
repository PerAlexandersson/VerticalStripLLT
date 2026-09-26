import VerticalStripLLT.WordEvaluation
import VerticalStripLLT.ReductionRecursion

namespace VerticalStripLLT

theorem unicellular_word {A : Type*} [CommRing A]
    {q : A} {e : ℕ → A} {F : ∀ n, SchroderPath n → A}
    (H : SatisfiesReductionRecursion q e F) {n : ℕ} (U V : List Step)
    (h : Step.validFrom n 0 0 (U ++ Step.diagonal :: V) = true) :
    SchroderPath.evalWord F n (U ++ Step.north :: Step.east :: V) -
        SchroderPath.evalWord F n (U ++ Step.east :: Step.north :: V) =
      (q - 1) * SchroderPath.evalWord F n
        (U ++ Step.diagonal :: V) := by
  have hv := Step.validFrom_resolve n 0 0 h
  rw [SchroderPath.evalWord_of_valid F n _ hv.1,
    SchroderPath.evalWord_of_valid F n _ hv.2,
    SchroderPath.evalWord_of_valid F n _ h]
  exact H.unicellular U V h

theorem firstBounce_word {A : Type*} [CommRing A]
    {q : A} {e : ℕ → A} {F : ∀ n, SchroderPath n → A}
    (H : SatisfiesReductionRecursion q e F) {n : ℕ}
    (U V W : List Step)
    (hV : ∀ s ∈ V, s = Step.north ∨ s = Step.diagonal)
    (h : Step.validFrom n 0 0
      ((U ++ Step.north :: Step.north :: V) ++
        Step.diagonal :: Step.east :: W) = true)
    (hreturn : (Step.endpointFrom 0 0 U).2 =
      (Step.endpointFrom 0 0 (U ++ Step.north :: Step.north :: V)).1)
    (hgap : (Step.endpointFrom 0 0
      (U ++ Step.north :: Step.north :: V)).1 + 1 <
      (Step.endpointFrom 0 0 (U ++ Step.north :: Step.north :: V)).2) :
    SchroderPath.evalWord F n
        ((U ++ Step.north :: Step.north :: V) ++
          Step.diagonal :: Step.east :: W) =
      q * SchroderPath.evalWord F n
        ((U ++ Step.north :: Step.north :: V) ++
          Step.east :: Step.diagonal :: W) := by
  have hs := (SchroderPath.swapDiagonalEast
    (U ++ Step.north :: Step.north :: V) W h hgap).valid
  simp only [SchroderPath.swapDiagonalEast_steps] at hs
  rw [SchroderPath.evalWord_of_valid F n _ h,
    SchroderPath.evalWord_of_valid F n _ hs]
  exact H.toSatisfiesRecursion.firstBounce U V W hV h hreturn hgap

theorem secondBounce_word {A : Type*} [CommRing A]
    {q : A} {e : ℕ → A} {F : ∀ n, SchroderPath n → A}
    (H : SatisfiesReductionRecursion q e F) {n : ℕ}
    (U V W : List Step)
    (hV : ∀ s ∈ V, s = Step.north ∨ s = Step.diagonal)
    (h : Step.validFrom n 0 0
      ((U ++ Step.diagonal :: Step.north :: V) ++
        Step.diagonal :: Step.east :: W) = true)
    (hreturn : (Step.endpointFrom 0 0 U).2 =
      (Step.endpointFrom 0 0 (U ++ Step.diagonal :: Step.north :: V)).1)
    (hgap : (Step.endpointFrom 0 0
      (U ++ Step.diagonal :: Step.north :: V)).1 + 1 <
      (Step.endpointFrom 0 0 (U ++ Step.diagonal :: Step.north :: V)).2) :
    SchroderPath.evalWord F n
        ((U ++ Step.diagonal :: Step.north :: V) ++
          Step.diagonal :: Step.east :: W) =
      SchroderPath.evalWord F n
        ((U ++ Step.north :: Step.diagonal :: V) ++
          Step.east :: Step.diagonal :: W) := by
  have hs := (SchroderPath.secondBounceSuccessor U V W h hgap).valid
  simp only [SchroderPath.secondBounceSuccessor_steps] at hs
  rw [SchroderPath.evalWord_of_valid F n _ h,
    SchroderPath.evalWord_of_valid F n _ hs]
  exact H.toSatisfiesRecursion.secondBounce U V W hV h hreturn hgap

theorem firstBounceOneLeadingEast_word {A : Type*} [CommRing A]
    {q : A} {e : ℕ → A} {F : ∀ n, SchroderPath n → A}
    (H : SatisfiesReductionRecursion q e F) {n : ℕ}
    (U V W : List Step)
    (hV : ∀ s ∈ V, s = Step.north ∨ s = Step.diagonal)
    (h : Step.validFrom n 0 0
      ((U ++ Step.north :: Step.north :: Step.east :: V) ++
        Step.diagonal :: Step.east :: W) = true)
    (hreturn : (Step.endpointFrom 0 0 U).2 =
      (Step.endpointFrom 0 0
        (U ++ Step.north :: Step.north :: Step.east :: V)).1)
    (hgap : (Step.endpointFrom 0 0
      (U ++ Step.north :: Step.north :: Step.east :: V)).1 + 1 <
      (Step.endpointFrom 0 0
        (U ++ Step.north :: Step.north :: Step.east :: V)).2) :
    SchroderPath.evalWord F n
        ((U ++ Step.north :: Step.north :: Step.east :: V) ++
          Step.diagonal :: Step.east :: W) =
      q * SchroderPath.evalWord F n
        ((U ++ Step.north :: Step.north :: Step.east :: V) ++
          Step.east :: Step.diagonal :: W) := by
  have hs := (SchroderPath.swapDiagonalEast
    (U ++ Step.north :: Step.north :: Step.east :: V) W h hgap).valid
  simp only [SchroderPath.swapDiagonalEast_steps] at hs
  rw [SchroderPath.evalWord_of_valid F n _ h,
    SchroderPath.evalWord_of_valid F n _ hs]
  exact H.firstBounceOneLeadingEast U V W hV h hreturn hgap

theorem secondBounceOneLeadingEast_word {A : Type*} [CommRing A]
    {q : A} {e : ℕ → A} {F : ∀ n, SchroderPath n → A}
    (H : SatisfiesReductionRecursion q e F) {n : ℕ}
    (U V W : List Step)
    (hV : ∀ s ∈ V, s = Step.north ∨ s = Step.diagonal)
    (h : Step.validFrom n 0 0
      ((U ++ Step.diagonal :: Step.north :: Step.east :: V) ++
        Step.diagonal :: Step.east :: W) = true)
    (hreturn : (Step.endpointFrom 0 0 U).2 =
      (Step.endpointFrom 0 0
        (U ++ Step.diagonal :: Step.north :: Step.east :: V)).1)
    (hgap : (Step.endpointFrom 0 0
      (U ++ Step.diagonal :: Step.north :: Step.east :: V)).1 + 1 <
      (Step.endpointFrom 0 0
        (U ++ Step.diagonal :: Step.north :: Step.east :: V)).2) :
    SchroderPath.evalWord F n
        ((U ++ Step.diagonal :: Step.north :: Step.east :: V) ++
          Step.diagonal :: Step.east :: W) =
      SchroderPath.evalWord F n
        ((U ++ Step.north :: Step.diagonal :: Step.east :: V) ++
          Step.east :: Step.diagonal :: W) := by
  have hs := (SchroderPath.secondBounceSuccessor U (Step.east :: V) W h hgap).valid
  simp only [SchroderPath.secondBounceSuccessor_steps] at hs
  rw [SchroderPath.evalWord_of_valid F n _ h,
    SchroderPath.evalWord_of_valid F n _ hs]
  exact H.secondBounceOneLeadingEast U V W hV h hreturn hgap

end VerticalStripLLT
