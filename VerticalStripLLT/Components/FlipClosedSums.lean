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
  simp only [Finset.mem_filter, componentClass_mk_eq_iff_mem]
  by_cases hq : q.out ∈ S
  · rw [ite_eq_left hq]
    exact ⟨And.right, fun hθ =>
      ⟨flipComponent_subset_of_mem_closed S hclosed hq θ hθ, hθ⟩⟩
  · simp only [ite_eq_right hq, Finset.notMem_empty, iff_false, not_and]
    intro hθ hcomp
    apply hq
    apply flipComponent_subset_of_mem_closed S hclosed hθ q.out
    rw [flipComponent_eq_of_mem hcomp]
    exact self_mem_flipComponent _

/--
If a finite set of orientations is closed under every flip, then any
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
      (∑ θ ∈ S, h θ) = ∑ q : componentClass D,
        if q.out ∈ S then ∑ θ ∈ flipComponent D q.out, h θ else 0 := by
    calc
      (∑ θ ∈ S, h θ) = ∑ q : componentClass D,
          ∑ θ ∈ S.filter (fun θ => mk θ = q), h θ :=
        (Finset.sum_fiberwise S mk h).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro q _
        rw [componentClass_fiber_inter_eq_flipComponent S hclosed q]
        split_ifs <;> rfl
  rw [hsum f, hsum g]
  simp only [hcomp]

end

end VerticalStripLLT.Circular
