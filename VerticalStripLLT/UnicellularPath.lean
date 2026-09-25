import VerticalStripLLT.Concat

/-! Validity and unchanged edge scanners under the unicellular path replacements.
These are path identities; the general coloring-polynomial relation is a later theorem.
-/

namespace VerticalStripLLT

namespace Step

theorem validFrom_resolve (n x y : ℕ) {U V : List Step}
    (h : validFrom n x y (U ++ diagonal :: V) = true) :
    validFrom n x y (U ++ north :: east :: V) = true ∧
      validFrom n x y (U ++ east :: north :: V) = true := by
  induction U generalizing x y with
  | nil =>
      simp only [List.nil_append, validFrom, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      exact ⟨⟨by lia, h.2⟩, ⟨by lia, h.2⟩⟩
  | cons s U ih =>
      cases s with
      | north =>
          simp only [List.cons_append, validFrom] at h ⊢
          exact ih (x := x) (y := y + 1) h
      | diagonal =>
          simp only [List.cons_append, validFrom, Bool.and_eq_true,
            decide_eq_true_eq] at h ⊢
          have hr := ih (x := x + 1) (y := y + 1) h.2
          exact ⟨⟨h.1, hr.1⟩, ⟨h.1, hr.2⟩⟩
      | east =>
          simp only [List.cons_append, validFrom, Bool.and_eq_true,
            decide_eq_true_eq] at h ⊢
          have hr := ih (x := x + 1) (y := y) h.2
          exact ⟨⟨h.1, hr.1⟩, ⟨h.1, hr.2⟩⟩

theorem normalFrom_resolve (x y u v : ℕ) {U V : List Step} :
    normalFrom x y u v (U ++ east :: north :: V) =
      normalFrom x y u v (U ++ diagonal :: V) := by
  induction U generalizing x y with
  | nil => simp [normalFrom]
  | cons s U ih =>
      cases s <;> simp only [List.cons_append, normalFrom]
      · exact ih (x := x) (y := y + 1)
      · rw [ih (x := x + 1) (y := y + 1)]
      · rw [ih (x := x + 1) (y := y)]

theorem strictFrom_resolve (x y u v : ℕ) {U V : List Step} :
    strictFrom x y u v (U ++ north :: east :: V) =
      strictFrom x y u v (U ++ east :: north :: V) := by
  induction U generalizing x y with
  | nil => simp [strictFrom]
  | cons s U ih =>
      cases s <;> simp only [List.cons_append, strictFrom]
      · exact ih (x := x) (y := y + 1)
      · rw [ih (x := x + 1) (y := y + 1)]
      · exact ih (x := x + 1) (y := y)

end Step

namespace SchroderPath

def resolveNorthEast {n : ℕ} (U V : List Step)
    (h : Step.validFrom n 0 0 (U ++ Step.diagonal :: V) = true) :
    SchroderPath n :=
  ⟨U ++ Step.north :: Step.east :: V, (Step.validFrom_resolve n 0 0 h).1⟩

def resolveEastNorth {n : ℕ} (U V : List Step)
    (h : Step.validFrom n 0 0 (U ++ Step.diagonal :: V) = true) :
    SchroderPath n :=
  ⟨U ++ Step.east :: Step.north :: V, (Step.validFrom_resolve n 0 0 h).2⟩

@[simp] theorem resolveNorthEast_steps {n : ℕ} (U V : List Step)
    (h : Step.validFrom n 0 0 (U ++ Step.diagonal :: V) = true) :
    (resolveNorthEast U V h).steps = U ++ Step.north :: Step.east :: V := rfl

@[simp] theorem resolveEastNorth_steps {n : ℕ} (U V : List Step)
    (h : Step.validFrom n 0 0 (U ++ Step.diagonal :: V) = true) :
    (resolveEastNorth U V h).steps = U ++ Step.east :: Step.north :: V := rfl

end SchroderPath
end VerticalStripLLT
