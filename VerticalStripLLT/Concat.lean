import VerticalStripLLT.Path

/-! Concatenation and translation laws for the path and edge scanners. -/

namespace VerticalStripLLT

namespace Step

private theorem bool_and_true {a b : Bool} :
    (a && b) = true ↔ a = true ∧ b = true := by
  simp

private theorem shift_succ (x k : ℕ) : x + k + 1 = x + 1 + k := by lia

private theorem beq_add (a b k : ℕ) :
    (a + k == b + k) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact Nat.add_right_cancel_iff

theorem validFrom_translate (n x y k : ℕ) (w : List Step) :
    validFrom (n + k) (x + k) (y + k) w = validFrom n x y w := by
  induction w generalizing n x y with
  | nil => simp [validFrom, beq_add]
  | cons s w ih =>
      cases s <;> simp [validFrom, shift_succ, ih]

theorem validFrom_append_of_valid (n N x y : ℕ) (a b : List Step)
    (ha : validFrom n x y a = true) (hb : validFrom N n n b = true) :
    validFrom N x y (a ++ b) = true := by
  induction a generalizing x y with
  | nil =>
      simp only [validFrom, Bool.and_eq_true, beq_iff_eq] at ha
      rcases ha with ⟨rfl, rfl⟩
      exact hb
  | cons s a ih =>
      cases s with
      | north =>
          simp only [List.cons_append, validFrom] at ha ⊢
          exact ih (x := x) (y := y + 1) ha
      | diagonal =>
          simp only [List.cons_append, validFrom] at ha ⊢
          have h := bool_and_true.mp ha
          exact bool_and_true.mpr ⟨h.1, ih (x := x + 1) (y := y + 1) h.2⟩
      | east =>
          simp only [List.cons_append, validFrom] at ha ⊢
          have h := bool_and_true.mp ha
          exact bool_and_true.mpr ⟨h.1, ih (x := x + 1) (y := y) h.2⟩

theorem normalFrom_append_of_valid (n x y u v : ℕ) (a b : List Step)
    (ha : validFrom n x y a = true) :
    normalFrom x y u v (a ++ b) =
      (normalFrom x y u v a || normalFrom n n u v b) := by
  induction a generalizing x y with
  | nil =>
      simp only [validFrom, Bool.and_eq_true, beq_iff_eq] at ha
      rcases ha with ⟨rfl, rfl⟩
      rfl
  | cons s a ih =>
      cases s with
      | north =>
          simp only [List.cons_append, normalFrom, validFrom] at ha ⊢
          rw [ih (x := x) (y := y + 1) ha]
      | diagonal =>
          simp only [List.cons_append, normalFrom, validFrom] at ha ⊢
          rw [ih (x := x + 1) (y := y + 1)
            (bool_and_true.mp ha).2]
          simp only [Bool.or_assoc]
      | east =>
          simp only [List.cons_append, normalFrom, validFrom] at ha ⊢
          rw [ih (x := x + 1) (y := y)
            (bool_and_true.mp ha).2]
          simp only [Bool.or_assoc]

theorem strictFrom_append_of_valid (n x y u v : ℕ) (a b : List Step)
    (ha : validFrom n x y a = true) :
    strictFrom x y u v (a ++ b) =
      (strictFrom x y u v a || strictFrom n n u v b) := by
  induction a generalizing x y with
  | nil =>
      simp only [validFrom, Bool.and_eq_true, beq_iff_eq] at ha
      rcases ha with ⟨rfl, rfl⟩
      rfl
  | cons s a ih =>
      cases s with
      | north =>
          simp only [List.cons_append, strictFrom, validFrom] at ha ⊢
          rw [ih (x := x) (y := y + 1) ha]
      | diagonal =>
          simp only [List.cons_append, strictFrom, validFrom] at ha ⊢
          rw [ih (x := x + 1) (y := y + 1)
            (bool_and_true.mp ha).2]
          simp only [Bool.or_assoc]
      | east =>
          simp only [List.cons_append, strictFrom, validFrom] at ha ⊢
          rw [ih (x := x + 1) (y := y)
            (bool_and_true.mp ha).2]

theorem normalFrom_translate (x y u v k : ℕ) (w : List Step) :
    normalFrom (x + k) (y + k) (u + k) (v + k) w = normalFrom x y u v w := by
  induction w generalizing x y u v with
  | nil => simp [normalFrom]
  | cons s w ih =>
      cases s <;> simp [normalFrom, shift_succ, ih, beq_add]

theorem strictFrom_translate (x y u v k : ℕ) (w : List Step) :
    strictFrom (x + k) (y + k) (u + k) (v + k) w = strictFrom x y u v w := by
  induction w generalizing x y u v with
  | nil => simp [strictFrom]
  | cons s w ih =>
      cases s <;> simp [strictFrom, shift_succ, ih, beq_add]

end Step

namespace SchroderPath

def concat {n m : ℕ} (P : SchroderPath n) (Q : SchroderPath m) :
    SchroderPath (n + m) :=
  ⟨P.steps ++ Q.steps, by
    have hq : Step.validFrom (n + m) n n Q.steps = true := by
      have h := Step.validFrom_translate m 0 0 n Q.steps
      simpa [Nat.add_comm] using h.trans Q.valid
    apply Step.validFrom_append_of_valid n (n + m) 0 0 P.steps Q.steps P.valid
    exact hq⟩

@[simp] theorem concat_steps {n m : ℕ} (P : SchroderPath n) (Q : SchroderPath m) :
    (concat P Q).steps = P.steps ++ Q.steps := rfl

end SchroderPath
end VerticalStripLLT
