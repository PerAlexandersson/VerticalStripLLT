import VerticalStripLLT.CyclicHessenberg.MatchingExpansion
import VerticalStripLLT.CyclicHessenberg.BasicExamples

/-! The natural cyclic expansion in the empty and singleton supports. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

private noncomputable def uniqueMatchingTuple {k n : ℕ} (h : Tuple k n)
    [Subsingleton (Fin k)] : Unique (MatchingTuple h) := by
  letI : Subsingleton (Equiv.Perm (Fin k)) := ⟨fun p q => by
    apply Equiv.ext
    intro x
    exact Subsingleton.elim _ _⟩
  refine ⟨⟨fun _ => 1, ?_⟩, ?_⟩
  · intro ℓ x
    simpa using Hessenberg.le_apply (h ℓ) x
  · intro φ
    apply Subtype.ext
    funext ℓ
    exact Subsingleton.elim _ _

private theorem layerAscentCount_eq_zero_of_subsingleton_positions {k : ℕ}
    [Subsingleton (LayerPosition k)] (h : Hessenberg k) (π τ : FullOrder k) :
    layerAscentCount h π τ = 0 := by
  classical
  have hevents : layerAscentEvents h π τ = ∅ := by
    ext e
    have heq : e.1 = e.2 := Subsingleton.elim _ _
    simp [layerAscentEvents, heq]
  simp [layerAscentCount, hevents]

private theorem matchingAscentCount_eq_zero_of_subsingleton_positions {k n : ℕ}
    [Subsingleton (LayerPosition k)] (h : Tuple k n) (φ : MatchingTuple h) :
    matchingAscentCount h φ = 0 := by
  rw [matchingAscentCount_eq_sum]
  apply Finset.sum_eq_zero
  intro ℓ hℓ
  exact layerAscentCount_eq_zero_of_subsingleton_positions (h ℓ)
    ((matchingCanonicalPath h φ).val ℓ.castSucc)
    ((matchingCanonicalPath h φ).val ℓ.succ)

private def emptyCycleDisplay : CycleDisplay (Finset.univ : Finset (Fin 0)) where
  blocks := []
  source_order := by simp [IsOrder, cycleSourceWord]
  root_max := by simp
  roots_desc := by simp

private theorem permutationDisplay_emptyFin :
    permutationDisplay (1 : Equiv.Perm (Fin 0)) = emptyCycleDisplay := by
  have hfull : emptyCycleDisplay.fullPerm = 1 := by
    apply CycleDisplay.fullPerm_eq_of_map_source emptyCycleDisplay 1
    simp [emptyCycleDisplay, CycleDisplay.source, CycleDisplay.target,
      cycleSourceWord, cycleTargetWord]
  rw [← hfull]
  exact permutationDisplay_fullPerm emptyCycleDisplay

private def singletonCycleDisplay : CycleDisplay (Finset.univ : Finset (Fin 1)) where
  blocks := [((0 : Fin 1), [])]
  source_order := by
    constructor
    · simp [cycleSourceWord]
    · ext x
      simp [cycleSourceWord]
  root_max := by
    intro b hb a ha
    rcases List.mem_singleton.mp hb with rfl
    simp at ha
  roots_desc := by
    simp

private theorem permutationDisplay_singletonFin :
    permutationDisplay (1 : Equiv.Perm (Fin 1)) = singletonCycleDisplay := by
  have hfull : singletonCycleDisplay.fullPerm = 1 := by
    apply CycleDisplay.fullPerm_eq_of_map_source singletonCycleDisplay 1
    simp [singletonCycleDisplay, CycleDisplay.source, CycleDisplay.target,
      cycleSourceWord, cycleTargetWord]
  rw [← hfull]
  exact permutationDisplay_fullPerm singletonCycleDisplay

private theorem singletonCycleDisplay_count : singletonCycleDisplay.count = 1 := by
  rfl

private theorem singletonCycleDisplay_shape :
    singletonCycleDisplay.shape = Finsupp.single 1 1 := by
  simp [CycleDisplay.shape, CycleDisplay.blockSize, singletonCycleDisplay]

@[simp] theorem naturalCyclicExpansion_empty_support {n : ℕ} (h : Tuple 0 n) :
    naturalCyclicExpansion h = 1 := by
  classical
  haveI : Subsingleton (Fin 0) := inferInstance
  letI : Unique (MatchingTuple h) := uniqueMatchingTuple h
  let φ : MatchingTuple h := default
  have hmono : matchingMonodromy φ.val = 1 := Subsingleton.elim _ _
  have hdisplay : matchingDisplay h φ = emptyCycleDisplay := by
    simp [matchingDisplay, hmono, permutationDisplay_emptyFin]
  have hcount : matchingCycleCount h φ = 0 := by
    simp [matchingCycleCount, hdisplay, emptyCycleDisplay, CycleDisplay.count]
  have hshape : matchingShape h φ = 0 := by
    simp [matchingShape, hdisplay, emptyCycleDisplay, CycleDisplay.shape]
  haveI : Subsingleton (LayerPosition 0) := by
    have hc : (Finset.univ : Finset (Fin 0)).card = 0 := by simp
    change Subsingleton (Fin ((Finset.univ : Finset (Fin 0)).card))
    rw [hc]
    infer_instance
  have hasc : matchingAscentCount h φ = 0 :=
    matchingAscentCount_eq_zero_of_subsingleton_positions h φ
  simp only [naturalCyclicExpansion, Finset.univ_unique, Finset.sum_singleton]
  change MvPolynomial.C (Polynomial.X ^ (0 - matchingCycleCount h φ) *
    (1 + Polynomial.X) ^ matchingAscentCount h φ) *
      MvPolynomial.monomial (matchingShape h φ) 1 = 1
  rw [hcount, hshape, hasc]
  simp

@[simp] theorem naturalCyclicExpansion_singleton_support {n : ℕ}
    (h : Tuple 1 n) : naturalCyclicExpansion h = natElementary 1 := by
  classical
  haveI : Subsingleton (Fin 1) := inferInstance
  letI : Unique (MatchingTuple h) := uniqueMatchingTuple h
  let φ : MatchingTuple h := default
  have hmono : matchingMonodromy φ.val = 1 := Subsingleton.elim _ _
  have hdisplay : matchingDisplay h φ = singletonCycleDisplay := by
    simp [matchingDisplay, hmono, permutationDisplay_singletonFin]
  have hcount : matchingCycleCount h φ = 1 := by
    simp [matchingCycleCount, hdisplay, singletonCycleDisplay_count]
  have hshape : matchingShape h φ = Finsupp.single 1 1 := by
    simp [matchingShape, hdisplay, singletonCycleDisplay_shape]
  haveI : Subsingleton (LayerPosition 1) := by
    have hc : (Finset.univ : Finset (Fin 1)).card = 1 := by simp
    change Subsingleton (Fin ((Finset.univ : Finset (Fin 1)).card))
    rw [hc]
    infer_instance
  have hasc : matchingAscentCount h φ = 0 :=
    matchingAscentCount_eq_zero_of_subsingleton_positions h φ
  simp only [naturalCyclicExpansion, Finset.univ_unique, Finset.sum_singleton]
  change MvPolynomial.C (Polynomial.X ^ (1 - matchingCycleCount h φ) *
    (1 + Polynomial.X) ^ matchingAscentCount h φ) *
      MvPolynomial.monomial (matchingShape h φ) 1 = natElementary 1
  rw [hcount, hshape, hasc]
  simp [natElementary, MvPolynomial.X]

end VerticalStripLLT.CyclicHessenberg
