import VerticalStripLLT.Path

namespace VerticalStripLLT

/-- Evaluate a path function on a word, using zero on invalid words. -/
def SchroderPath.evalWord {A : Type*} [Zero A]
    (F : ∀ n, SchroderPath n → A) (n : ℕ) (w : List Step) : A :=
  if h : Step.validFrom n 0 0 w = true then F n ⟨w, h⟩ else 0

@[simp] theorem SchroderPath.evalWord_of_valid {A : Type*} [Zero A]
    (F : ∀ n, SchroderPath n → A) (n : ℕ) (w : List Step)
    (h : Step.validFrom n 0 0 w = true) :
    SchroderPath.evalWord F n w = F n ⟨w, h⟩ := by
  simp [SchroderPath.evalWord, h]

@[simp] theorem SchroderPath.evalWord_steps {A : Type*} [Zero A]
    (F : ∀ n, SchroderPath n → A) {n : ℕ} (P : SchroderPath n) :
    SchroderPath.evalWord F n P.steps = F n P := by
  simp [SchroderPath.evalWord, P.valid]

end VerticalStripLLT
