import VerticalStripLLT.Concat
import VerticalStripLLT.WordCounts
import VerticalStripLLT.PathBounds

namespace VerticalStripLLT

namespace Step

theorem validFrom_prefix_of_endpoint (n x y k : ℕ) (U V : List Step)
    (h : validFrom n x y (U ++ V) = true)
    (he : endpointFrom x y U = (k, k)) :
    validFrom k x y U = true := by
  induction U generalizing x y k with
  | nil =>
      simp only [endpointFrom, Prod.mk.injEq] at he
      rcases he with ⟨rfl, rfl⟩
      simp [validFrom]
  | cons s U ih =>
      cases s with
      | north =>
          simp only [List.cons_append, validFrom, endpointFrom] at h he ⊢
          exact ih (x := x) (y := y + 1) (k := k) h he
      | diagonal =>
          simp only [List.cons_append, validFrom, endpointFrom,
            Bool.and_eq_true, decide_eq_true_eq] at h he ⊢
          have hu := ih (x := x + 1) (y := y + 1) (k := k) h.2 he
          exact ⟨h.1, hu⟩
      | east =>
          simp only [List.cons_append, validFrom, endpointFrom,
            Bool.and_eq_true, decide_eq_true_eq] at h he ⊢
          have hu := ih (x := x + 1) (y := y) (k := k) h.2 he
          exact ⟨h.1, hu⟩

theorem validFrom_suffix_at_endpoint {n x y k : ℕ} (U V : List Step)
    (h : validFrom n x y (U ++ V) = true)
    (he : endpointFrom x y U = (k, k)) :
    validFrom n k k V = true := by
  have hs := validFrom_suffix n x y U V h
  simpa [he] using hs

end Step

namespace SchroderPath

def prefixAtReturn {n k : ℕ} (U V : List Step)
    (h : Step.validFrom n 0 0 (U ++ V) = true)
    (he : Step.endpointFrom 0 0 U = (k, k)) : SchroderPath k :=
  ⟨U, Step.validFrom_prefix_of_endpoint n 0 0 k U V h he⟩

def suffixAtReturn {n k : ℕ} (U V : List Step)
    (h : Step.validFrom n 0 0 (U ++ V) = true)
    (he : Step.endpointFrom 0 0 U = (k, k)) : SchroderPath (n - k) := by
  have hs := Step.validFrom_suffix_at_endpoint U V h he
  have hk : k ≤ n := by
    have hb := Step.validFrom_bounds n k k hs
    exact hb.2
  have ht := Step.validFrom_translate (n - k) 0 0 k V
  refine ⟨V, ?_⟩
  rw [Nat.sub_add_cancel hk] at ht
  rw [← ht]
  simpa only [Nat.zero_add] using hs

@[simp] theorem prefixAtReturn_steps {n k : ℕ} (U V : List Step)
    (h : Step.validFrom n 0 0 (U ++ V) = true)
    (he : Step.endpointFrom 0 0 U = (k, k)) :
    (prefixAtReturn U V h he).steps = U := rfl

@[simp] theorem suffixAtReturn_steps {n k : ℕ} (U V : List Step)
    (h : Step.validFrom n 0 0 (U ++ V) = true)
    (he : Step.endpointFrom 0 0 U = (k, k)) :
    (suffixAtReturn U V h he).steps = V := rfl

end SchroderPath
end VerticalStripLLT
