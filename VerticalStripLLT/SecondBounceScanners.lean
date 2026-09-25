import VerticalStripLLT.PrefixScanners
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto

namespace VerticalStripLLT
namespace Step

theorem endpointFrom_secondBounce_source (U V : List Step) :
    endpointFrom 0 0 ((U ++ [east]) ++ north :: north :: V) =
      endpointFrom 0 0 (U ++ diagonal :: north :: V) := by
  simp only [endpointFrom_append, endpointFrom, List.append_assoc]

theorem endpointFrom_secondBounce_target (U V : List Step) :
    endpointFrom 0 0 ((U ++ [east]) ++ north :: north :: V) =
      endpointFrom 0 0 (U ++ north :: diagonal :: V) := by
  simp only [endpointFrom_append, endpointFrom, List.append_assoc]

theorem normalFrom_secondBounce_source (U V X : List Step) (u v : ℕ) :
    normalFrom 0 0 u v ((U ++ diagonal :: north :: V) ++ X) =
      normalFrom 0 0 u v (((U ++ [east]) ++ north :: north :: V) ++ X) := by
  simp only [normalFrom_append, endpointFrom_append, normalFrom, endpointFrom,
    Bool.or_false, Bool.or_assoc]

theorem strictFrom_secondBounce_source (U V X : List Step) (u v : ℕ) :
    strictFrom 0 0 u v ((U ++ diagonal :: north :: V) ++ X) = true ↔
      strictFrom 0 0 u v (((U ++ [east]) ++ north :: north :: V) ++ X) = true ∨
        (u = (endpointFrom 0 0 U).1 ∧ v = (endpointFrom 0 0 U).2) := by
  simp only [strictFrom_append, endpointFrom_append, strictFrom, endpointFrom,
    Bool.or_false, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  tauto

theorem normalFrom_secondBounce_target (U V X : List Step) (u v : ℕ)
    (hlt : (endpointFrom 0 0 U).1 < (endpointFrom 0 0 U).2) :
    normalFrom 0 0 u v ((U ++ north :: diagonal :: V) ++ X) = true ↔
      normalFrom 0 0 u v (((U ++ [east]) ++ north :: north :: V) ++ X) = true ∨
        (u = (endpointFrom 0 0 U).1 ∧ v = (endpointFrom 0 0 U).2) := by
  simp only [normalFrom_append, endpointFrom_append, normalFrom, endpointFrom,
    Bool.or_false, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq]
  generalize (endpointFrom 0 0 U).1 = a at *
  generalize (endpointFrom 0 0 U).2 = i at *
  generalize normalFrom 0 0 u v U = p
  generalize normalFrom (a + 1) (i + 1 + 1) u v V = q
  generalize normalFrom _ _ u v X = r
  cases p <;> cases q <;> cases r <;> (simp; try lia)

theorem strictFrom_secondBounce_target (U V X : List Step) (u v : ℕ) :
    strictFrom 0 0 u v ((U ++ north :: diagonal :: V) ++ X) = true ↔
      strictFrom 0 0 u v (((U ++ [east]) ++ north :: north :: V) ++ X) = true ∨
        (u = (endpointFrom 0 0 U).1 ∧ v = (endpointFrom 0 0 U).2 + 1) := by
  simp only [strictFrom_append, endpointFrom_append, strictFrom, endpointFrom,
    Bool.or_false, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  tauto
end Step
end VerticalStripLLT
