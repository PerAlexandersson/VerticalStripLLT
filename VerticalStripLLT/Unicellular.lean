import VerticalStripLLT.MarkedDiagonal
import VerticalStripLLT.UnicellularWeight
import Mathlib.Tactic.Tauto

open scoped BigOperators

/-! Marked-edge scanner identities for the unicellular replacements. -/

namespace VerticalStripLLT

namespace Step

theorem strictFrom_diagonal_eq_or_marked (x y u v : ℕ) (U V : List Step) :
    strictFrom x y u v (U ++ diagonal :: V) =
      (strictFrom x y u v (U ++ east :: north :: V) ||
        ((u == (endpointFrom x y U).1) && (v == (endpointFrom x y U).2))) := by
  induction U generalizing x y with
  | nil =>
      simp only [List.nil_append, strictFrom, endpointFrom]
      cases (u == x && v == y) <;> simp
  | cons s U ih =>
      cases s <;> simp only [List.cons_append, strictFrom, endpointFrom]
      · exact ih x (y + 1)
      · rw [ih (x + 1) (y + 1), Bool.or_assoc]
      · exact ih (x + 1) y

theorem normalFrom_northEast_eq_or_marked (n x y u v : ℕ) (U V : List Step)
    (h : validFrom n x y (U ++ diagonal :: V) = true) :
    normalFrom x y u v (U ++ north :: east :: V) =
      (normalFrom x y u v (U ++ east :: north :: V) ||
        ((u == (endpointFrom x y U).1) && (v == (endpointFrom x y U).2))) := by
  induction U generalizing x y with
  | nil =>
      simp only [List.nil_append, validFrom, Bool.and_eq_true,
        decide_eq_true_eq] at h
      simp only [List.nil_append, normalFrom, endpointFrom]
      have key : ((u == x) && decide (x < v) && decide (v < y + 1)) =
          (((u == x) && decide (x < v) && decide (v < y)) ||
            ((u == x) && (v == y))) := by
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
          decide_eq_true_eq]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          by_cases hv : v = y
          · exact Or.inr ⟨h1, hv⟩
          · exact Or.inl ⟨⟨h1, h2⟩, by lia⟩
        · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨h1, h2⟩)
          · exact ⟨⟨h1, h2⟩, by lia⟩
          · exact ⟨⟨h1, by lia⟩, by lia⟩
      rw [key]
      cases ((u == x) && decide (x < v) && decide (v < y)) <;>
        cases ((u == x) && (v == y)) <;> simp
  | cons s U ih =>
      cases s with
      | north =>
          simp only [List.cons_append, validFrom] at h
          simp only [List.cons_append, normalFrom, endpointFrom]
          exact ih x (y + 1) h
      | diagonal =>
          simp only [List.cons_append, validFrom, Bool.and_eq_true] at h
          simp only [List.cons_append, normalFrom, endpointFrom]
          rw [ih (x + 1) (y + 1) h.2, Bool.or_assoc]
      | east =>
          simp only [List.cons_append, validFrom, Bool.and_eq_true] at h
          simp only [List.cons_append, normalFrom, endpointFrom]
          rw [ih (x + 1) y h.2, Bool.or_assoc]

end Step

namespace SchroderPath

theorem resolve_strictEdges_eq {n : ℕ} (U V : List Step)
    (h : Step.validFrom n 0 0 (U ++ Step.diagonal :: V) = true) :
    (resolveNorthEast U V h).strictEdges = (resolveEastNorth U V h).strictEdges := by
  ext e
  simp only [strictEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [resolveNorthEast_steps, resolveEastNorth_steps]
  rw [Step.strictFrom_resolve]

theorem resolve_diagonal_normalEdges_eq {n : ℕ} (U V : List Step)
    (h : Step.validFrom n 0 0 (U ++ Step.diagonal :: V) = true) :
    (⟨U ++ Step.diagonal :: V, h⟩ : SchroderPath n).normalEdges =
      (resolveEastNorth U V h).normalEdges := by
  ext e
  simp only [normalEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [resolveEastNorth_steps]
  rw [Step.normalFrom_resolve]

theorem diagonal_strictEdges_eq_insert {n : ℕ} (U V : List Step)
    (h : Step.validFrom n 0 0 (U ++ Step.diagonal :: V) = true) :
    (⟨U ++ Step.diagonal :: V, h⟩ : SchroderPath n).strictEdges =
      insert (markedDiagonalEdge U V h) (resolveEastNorth U V h).strictEdges := by
  ext e
  simp only [strictEdges, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ,
    true_and]
  simp only [resolveEastNorth_steps]
  rw [Step.strictFrom_diagonal_eq_or_marked]
  rcases e with ⟨a, b⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, markedDiagonalEdge,
    Prod.mk.injEq, Fin.ext_iff]
  tauto

theorem northEast_normalEdges_eq_insert {n : ℕ} (U V : List Step)
    (h : Step.validFrom n 0 0 (U ++ Step.diagonal :: V) = true) :
    (resolveNorthEast U V h).normalEdges =
      insert (markedDiagonalEdge U V h) (resolveEastNorth U V h).normalEdges := by
  ext e
  simp only [normalEdges, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ,
    true_and]
  simp only [resolveEastNorth_steps, resolveNorthEast_steps]
  rw [Step.normalFrom_northEast_eq_or_marked n 0 0 _ _ U V h]
  rcases e with ⟨a, b⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, markedDiagonalEdge,
    Prod.mk.injEq, Fin.ext_iff]
  tauto

theorem markedDiagonalEdge_not_mem_eastNorth_normalEdges {n : ℕ} (U V : List Step)
    (h : Step.validFrom n 0 0 (U ++ Step.diagonal :: V) = true) :
    markedDiagonalEdge U V h ∉ (resolveEastNorth U V h).normalEdges := by
  rw [← resolve_diagonal_normalEdges_eq]
  exact Finset.disjoint_right.mp (normalEdges_disjoint_strictEdges _)
    (markedDiagonalEdge_mem U V h)

end SchroderPath

end VerticalStripLLT
namespace VerticalStripLLT

theorem coloringLLT_unicellular {n : ℕ} (U V : List Step)
    (h : Step.validFrom n 0 0 (U ++ Step.diagonal :: V) = true) (m : ℕ) :
    coloringLLT (SchroderPath.resolveNorthEast U V h) m -
        coloringLLT (SchroderPath.resolveEastNorth U V h) m =
      MvPolynomial.C (Polynomial.X - 1) *
        coloringLLT (⟨U ++ Step.diagonal :: V, h⟩ : SchroderPath n) m := by
  unfold coloringLLT
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  exact coloringWeight_unicellular_of_edges _ _ _ (SchroderPath.markedDiagonalEdge U V h) c
    (SchroderPath.northEast_normalEdges_eq_insert U V h)
    (SchroderPath.resolve_diagonal_normalEdges_eq U V h)
    (SchroderPath.resolve_strictEdges_eq U V h)
    (SchroderPath.diagonal_strictEdges_eq_insert U V h)
    (SchroderPath.markedDiagonalEdge_not_mem_eastNorth_normalEdges U V h)

end VerticalStripLLT
