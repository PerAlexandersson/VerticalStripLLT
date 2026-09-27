import VerticalStripLLT.Components.ComponentSumPartition

/-! Sums over a flip-closed set are determined componentwise. -/

namespace VerticalStripLLT.Circular

open Classical
open scoped BigOperators

noncomputable section

variable {n : ℕ} {D : Diagram n}

private theorem flipComponent_subset_of_mem_closed
    (S : Finset (Orientation D))
    (hclosed : ∀ θ ∈ S, ∀ η, Flip D θ η → η ∈ S)
    {θ : Orientation D} (hθ : θ ∈ S) :
    ∀ η ∈ flipComponent D θ, η ∈ S := by
  intro η hη
  have hr := mem_flipComponent_iff.mp hη
  clear hη
  induction hr with
  | refl => exact hθ
  | tail _ hstep ih => exact hclosed _ ih _ hstep

private theorem componentClass_fiber_inter_eq_flipComponent
    (S : Finset (Orientation D))
    (hclosed : ∀ θ ∈ S, ∀ η, Flip D θ η → η ∈ S)
    (q : componentClass D) :
    S.filter (fun θ : Orientation D =>
      Quotient.mk (componentSetoid D) θ = q) =
      if q.out ∈ S then flipComponent D q.out else ∅ := by
  ext θ
  by_cases hq : q.out ∈ S
  · simp only [Finset.mem_filter, if_pos hq, Finset.notMem_empty]
    constructor
    · rintro ⟨_, hθ⟩
      apply mem_flipComponent_iff.mpr
      have hrel := Quotient.mk_eq_iff_out.mp hθ
      change Relation.ReflTransGen (Flip D) θ q.out at hrel
      exact flip_reachable_symm hrel
    · intro hθ
      have hrel := mem_flipComponent_iff.mp hθ
      refine ⟨flipComponent_subset_of_mem_closed S hclosed hq θ hθ, ?_⟩
      apply Quotient.mk_eq_iff_out.mpr
      change Relation.ReflTransGen (Flip D) θ q.out
      exact flip_reachable_symm hrel
  · simp only [Finset.mem_filter, if_neg hq, Finset.notMem_empty]
    constructor
    · rintro ⟨hθ, hqθ⟩
      exfalso
      apply hq
      have hrel := Quotient.mk_eq_iff_out.mp hqθ
      change Relation.ReflTransGen (Flip D) θ q.out at hrel
      exact flipComponent_subset_of_mem_closed S hclosed hθ q.out
        (mem_flipComponent_iff.mpr hrel)
    · intro hfalse
      exact False.elim hfalse

/--
If a finite set of orientations is closed under every directed flip, then any
two orientation-valued functions with equal sums on every complete flip
component have equal sums on that set.
-/
theorem sum_eq_of_flipComponent_sum_eq_of_closed
    {M : Type*} [AddCommMonoid M] (S : Finset (Orientation D))
    (hclosed : ∀ θ ∈ S, ∀ η, Flip D θ η → η ∈ S)
    (f g : Orientation D → M)
    (hcomp : ∀ θ : Orientation D,
      (∑ η ∈ flipComponent D θ, f η) =
        ∑ η ∈ flipComponent D θ, g η) :
    (∑ θ ∈ S, f θ) = ∑ θ ∈ S, g θ := by
  let mk : Orientation D → componentClass D :=
    Quotient.mk (componentSetoid D)
  have hsum (h : Orientation D → M) :
      (∑ θ ∈ S, h θ) =
        ∑ q : componentClass D,
          ∑ θ ∈ S.filter (fun θ => mk θ = q), h θ := by
    symm
    exact Finset.sum_fiberwise S mk h
  calc
    (∑ θ ∈ S, f θ) =
        ∑ q : componentClass D,
          ∑ θ ∈ S.filter (fun θ => mk θ = q), f θ := hsum f
    _ = ∑ q : componentClass D,
          if q.out ∈ S then
            ∑ θ ∈ flipComponent D q.out, f θ
          else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [componentClass_fiber_inter_eq_flipComponent S hclosed q]
      split_ifs <;> rfl
    _ = ∑ q : componentClass D,
          if q.out ∈ S then
            ∑ θ ∈ flipComponent D q.out, g θ
          else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      split_ifs with hS
      · exact hcomp q.out
      · rfl
    _ = (∑ θ ∈ S, g θ) := by
      rw [hsum g]
      apply Finset.sum_congr rfl
      intro q hq
      rw [componentClass_fiber_inter_eq_flipComponent S hclosed q]
      split_ifs <;> rfl

end

end VerticalStripLLT.Circular
