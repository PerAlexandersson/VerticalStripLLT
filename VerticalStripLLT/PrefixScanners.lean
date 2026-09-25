import VerticalStripLLT.MarkedDiagonal

/-! Scanner decomposition at an arbitrary prefix endpoint, without validity hypotheses. -/

namespace VerticalStripLLT

namespace Step

theorem endpointFrom_append (x y : ℕ) (U V : List Step) :
    endpointFrom x y (U ++ V) =
      endpointFrom (endpointFrom x y U).1 (endpointFrom x y U).2 V := by
  induction U generalizing x y with
  | nil => simp [endpointFrom]
  | cons s U ih =>
      cases s <;>
        simp only [List.cons_append, endpointFrom] at *
      · exact ih (x := x) (y := y + 1)
      · exact ih (x := x + 1) (y := y + 1)
      · exact ih (x := x + 1) (y := y)

theorem normalFrom_append (x y u v : ℕ) (U V : List Step) :
    normalFrom x y u v (U ++ V) =
      (normalFrom x y u v U ||
        normalFrom (endpointFrom x y U).1 (endpointFrom x y U).2 u v V) := by
  induction U generalizing x y with
  | nil => simp [normalFrom, endpointFrom]
  | cons s U ih =>
      cases s with
      | north =>
          simp only [List.cons_append, normalFrom, endpointFrom] at *
          exact ih (x := x) (y := y + 1)
      | diagonal =>
          simp only [List.cons_append, normalFrom, endpointFrom] at *
          rw [ih (x := x + 1) (y := y + 1), Bool.or_assoc]
      | east =>
          simp only [List.cons_append, normalFrom, endpointFrom] at *
          rw [ih (x := x + 1) (y := y), Bool.or_assoc]

theorem strictFrom_append (x y u v : ℕ) (U V : List Step) :
    strictFrom x y u v (U ++ V) =
      (strictFrom x y u v U ||
        strictFrom (endpointFrom x y U).1 (endpointFrom x y U).2 u v V) := by
  induction U generalizing x y with
  | nil => simp [strictFrom, endpointFrom]
  | cons s U ih =>
      cases s with
      | north =>
          simp only [List.cons_append, strictFrom, endpointFrom] at *
          exact ih (x := x) (y := y + 1)
      | diagonal =>
          simp only [List.cons_append, strictFrom, endpointFrom] at *
          rw [ih (x := x + 1) (y := y + 1), Bool.or_assoc]
      | east =>
          simp only [List.cons_append, strictFrom, endpointFrom] at *
          exact ih (x := x + 1) (y := y)

end Step
end VerticalStripLLT
