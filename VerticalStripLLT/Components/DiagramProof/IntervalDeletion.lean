import VerticalStripLLT.Components.DiagramProof.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic.Linarith

/-! Short edges connect a set with no two consecutive omissions. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {n : ℕ}

theorem eqvGen_of_short_edges_of_no_consecutive_omissions
    {R : Fin n → Fin n → Prop} {S : Set (Fin n)}
    (hshort : ∀ u v, u < v → v.val ≤ u.val + 2 → R u v)
    (hS : ∀ u v, u.val + 1 = v.val → S u ∨ S v) :
    ∀ u v, S u → S v →
      Relation.EqvGen (fun x y => S x ∧ S y ∧ R x y) u v := by
  let T : Fin n → Fin n → Prop := fun x y => S x ∧ S y ∧ R x y
  have aux : ∀ k : ℕ, ∀ u v : Fin n, u.val + k = v.val →
      S u → S v → Relation.EqvGen T u v := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro u v huv hSu hSv
      by_cases hk0 : k = 0
      · have huv' : u = v := Fin.ext (by lia)
        subst v
        exact Relation.EqvGen.refl _
      by_cases hk1 : k = 1
      · apply Relation.EqvGen.rel
        exact ⟨hSu, hSv, hshort u v (by change u.val < v.val; lia) (by lia)⟩
      have hk2 : 2 ≤ k := by lia
      let x : Fin n := ⟨u.val + 1, by lia⟩
      let y : Fin n := ⟨u.val + 2, by lia⟩
      rcases hS x y (by simp [x, y]) with hSx | hSy
      · apply Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.rel _ _ ⟨hSu, hSx,
            hshort u x (by change u.val < u.val + 1; lia) (by simp [x])⟩)
        apply ih (k - 1) (by lia) x v
        · change u.val + 1 + (k - 1) = v.val
          lia
        · exact hSx
        · exact hSv
      · apply Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.rel _ _ ⟨hSu, hSy,
            hshort u y (by change u.val < u.val + 2; lia) (by simp [y])⟩)
        apply ih (k - 2) (by lia) y v
        · change u.val + 2 + (k - 2) = v.val
          lia
        · exact hSy
        · exact hSv
  intro u v hSu hSv
  rcases le_total u v with huv | hvu
  · exact aux (v.val - u.val) u v (by
      exact Nat.add_sub_of_le (show u.val ≤ v.val from huv)) hSu hSv
  · exact Relation.EqvGen.symm _ _
      (aux (u.val - v.val) v u (by
        exact Nat.add_sub_of_le (show v.val ≤ u.val from hvu)) hSv hSu)

end VerticalStripLLT.Circular.DiagramProof
