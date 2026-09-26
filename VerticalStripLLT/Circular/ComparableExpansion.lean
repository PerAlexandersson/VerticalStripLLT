import VerticalStripLLT.Circular.StrictExpansion
import VerticalStripLLT.Circular.ForcedOrientation
import VerticalStripLLT.Circular.OrientationSum

/-! The full semantic bridge when every normal edge is forced by strict comparability. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

namespace EdgeData

theorem strictOrderEnumerator_insert_of_strict_path
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (G : EdgeData V E) (e : E)
    (hp : Relation.TransGen (G.selected ∅) (G.tail e) (G.head e))
    (A : Finset E) (m : ℕ) :
    G.strictOrderEnumerator (insert e A) m =
      G.strictOrderEnumerator A m := by
  unfold EdgeData.strictOrderEnumerator
  apply Finset.sum_congr rfl
  intro c _
  have hc : (∀ f ∈ G.strict ∪ insert e A, c (G.tail f) < c (G.head f)) ↔
      ∀ f ∈ G.strict ∪ A, c (G.tail f) < c (G.head f) := by
    constructor
    · intro h f hf
      exact h f ((Finset.union_subset_union_right (Finset.subset_insert e A)) hf)
    · intro h f hf
      rcases Finset.mem_union.mp hf with hf | hf
      · exact h f (Finset.mem_union_left _ hf)
      · rcases Finset.mem_insert.mp hf with rfl | hf
        · exact G.lt_of_transGen ∅ c
            (by
              intro g hg
              exact h g (Finset.mem_union_left A
                (by simpa only [Finset.union_empty] using hg))) hp
        · exact h f (Finset.mem_union_right _ hf)
  exact ite_congr (propext hc) (fun _ => rfl) (fun _ => rfl)

end EdgeData

namespace Diagram

variable {n : ℕ} (D : Diagram n)

theorem strictOrderEnumerator_insert_of_strict_path (e : Edge D.area)
    (hp : Relation.TransGen (D.edgeData.selected ∅) e.tail e.head)
    (A : Finset (Edge D.area)) (m : ℕ) :
    D.edgeData.strictOrderEnumerator (insert e A) m =
      D.edgeData.strictOrderEnumerator A m :=
  D.edgeData.strictOrderEnumerator_insert_of_strict_path e hp A m

theorem strictOrderEnumerator_insert_of_reverse_strict_path (e : Edge D.area)
    (hp : Relation.TransGen (D.edgeData.selected ∅) e.head e.tail)
    (A : Finset (Edge D.area)) (m : ℕ) :
    D.edgeData.strictOrderEnumerator (insert e A) m = 0 := by
  apply D.edgeData.strictOrderEnumerator_eq_zero_of_not_admissible
  intro ha
  have hpath : Relation.TransGen (D.edgeData.selected (insert e A)) e.head e.tail := by
    apply Relation.TransGen.mono (fun u v h => ?_) _ _ hp
    obtain ⟨f, hf, ht, hh⟩ := h
    refine ⟨f, ?_, ht, hh⟩
    simp only [Finset.union_empty] at hf
    exact Finset.mem_union_left _ hf
  exact ha e.head (hpath.tail
    ⟨e, Finset.mem_union_right _ (Finset.mem_insert_self _ _), rfl, rfl⟩)

/-- Every selected-set term has the independent HRV interpretation in this base family. -/
theorem strictOrderEnumerator_eq_eval_orientMono_of_normal_comparable
    (hcomp : ∀ e ∈ D.edgeData.normalEdges,
      Relation.TransGen (D.edgeData.selected ∅) e.tail e.head ∨
      Relation.TransGen (D.edgeData.selected ∅) e.head e.tail)
    (A : Finset (Edge D.area)) (hA : A ⊆ D.edgeData.normalEdges) (m : ℕ) :
    D.edgeData.strictOrderEnumerator A m = evalElementary m (D.orientMono A) := by
  induction A using Finset.induction_on with
  | empty =>
    by_cases ha : D.edgeData.Admissible ∅
    · let θ : Orientation D := ⟨∅, Finset.empty_subset _, ha⟩
      have h := strictOrderEnumerator_eq_eval_hrvMonomial_of_empty θ rfl m
      change D.edgeData.strictOrderEnumerator θ.val m = _
      rw [D.orientMono_orientation θ]
      exact h
    · rw [D.edgeData.strictOrderEnumerator_eq_zero_of_not_admissible ∅ ha m,
        D.orientMono_of_not_adm ha, map_zero]
  | @insert e A _ ih =>
    have he : e ∈ D.edgeData.normalEdges := hA (Finset.mem_insert_self _ _)
    have hsub : A ⊆ D.edgeData.normalEdges := (Finset.subset_insert _ _).trans hA
    rcases hcomp e he with hp | hp
    · rw [D.strictOrderEnumerator_insert_of_strict_path e hp A m,
        D.orientMono_insert_of_strict_path e he hp A hsub]
      exact ih hsub
    · rw [D.strictOrderEnumerator_insert_of_reverse_strict_path e hp A m,
        D.orientMono_insert_of_reverse_strict_path e hp A, map_zero]

/-- Forced normal comparisons give the actual circular expansion without any recurrence. -/
theorem coloringLLT_shifted_eq_expansion_of_normal_comparable
    (hcomp : ∀ e ∈ D.edgeData.normalEdges,
      Relation.TransGen (D.edgeData.selected ∅) e.tail e.head ∨
      Relation.TransGen (D.edgeData.selected ∅) e.head e.tail) (m : ℕ) :
    xQShift m (D.coloringLLT m) = evalElementary m (shiftedOrientationExpansion D) := by
  change xQShift m (D.edgeData.coloringLLT m) = _
  rw [D.edgeData.xQShift_coloringLLT_eq_all_selected m,
    D.shiftedOrientationExpansion_eq_sum]
  simp only [map_sum, map_mul, evalElementary_C]
  apply Finset.sum_congr rfl
  intro A hA
  rw [D.strictOrderEnumerator_eq_eval_orientMono_of_normal_comparable hcomp A
    (Finset.mem_powerset.mp hA) m]

/-- In particular, one strict chain through all vertices is a semantic base. -/
theorem coloringLLT_shifted_eq_expansion_of_strict_total
    (htotal : ∀ u v : Fin n, u ≠ v →
      Relation.TransGen (D.edgeData.selected ∅) u v ∨
      Relation.TransGen (D.edgeData.selected ∅) v u) (m : ℕ) :
    xQShift m (D.coloringLLT m) = evalElementary m (shiftedOrientationExpansion D) := by
  apply D.coloringLLT_shifted_eq_expansion_of_normal_comparable
  intro e _
  exact htotal e.tail e.head e.tail_ne_head

end Diagram
end VerticalStripLLT.Circular
