import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Pairwise

/-! Word compatibility for one increasing block. -/

namespace VerticalStripLLT.Components

noncomputable section

variable {V : Type*} [LinearOrder V]

/-- The increasing word on a finite set. -/
def incWord (s : Finset V) : List V :=
  s.sort (· ≤ ·)

/-- The decreasing word on a finite set. -/
def decWord (s : Finset V) : List V :=
  s.sort (· ≥ ·)

/-- Put the complement of `T` increasingly before `T` decreasingly. -/
def blockWord (B T : Finset V) : List V :=
  incWord (B \ T) ++ decWord T

/-- A word is compatible when every selected edge points to the right. -/
def wordCompatible (R : V → V → Prop) (w : List V) : Prop :=
  w.Pairwise fun x y => ¬ R y x

/-- A sink of the graph induced on `B`. -/
def sinkOn (R : V → V → Prop) (B : Finset V) (v : V) : Prop :=
  v ∈ B ∧ ∀ w ∈ B, ¬ R v w

private theorem decWord_not_compatible_of_edge (R : V → V → Prop)
    (hinc : ∀ ⦃u v⦄, R u v → u < v) (s : Finset V) {u v : V}
    (hu : u ∈ s) (hv : v ∈ s) (huv : R u v) :
    ¬ wordCompatible R (decWord s) := by
  intro h
  have hp : (decWord s).Pairwise (fun x y => ¬ R x y ∧ ¬ R y x) := by
    apply List.pairwise_and_iff.mpr
    refine ⟨?_, h⟩
    exact (Finset.pairwise_sort s (· ≥ ·)).imp fun hxy hR =>
      (not_lt_of_ge hxy) (hinc hR)
  let : Std.Symm (fun x y => ¬ R x y ∧ ¬ R y x) :=
    ⟨fun _ _ h => ⟨h.2, h.1⟩⟩
  exact (hp.forall (by simpa [decWord] using hu)
    (by simpa [decWord] using hv) (ne_of_lt (hinc huv))).1 huv

/-- The descending part of a block word may contain exactly its induced sinks. -/
theorem blockWord_compatible_iff_forall_sink (R : V → V → Prop)
    (hinc : ∀ ⦃u v⦄, R u v → u < v) (B T : Finset V) (hT : T ⊆ B) :
    wordCompatible R (blockWord B T) ↔ ∀ u ∈ T, sinkOn R B u := by
  classical
  constructor
  · intro h u hu
    change (incWord (B \ T) ++ decWord T).Pairwise (fun x y => ¬ R y x) at h
    refine ⟨hT hu, ?_⟩
    intro v hv huv
    by_cases hvT : v ∈ T
    · have hparts := (List.pairwise_append.mp h)
      exact decWord_not_compatible_of_edge R hinc T hu hvT huv hparts.2.1
    · have hparts := (List.pairwise_append.mp h)
      have hvBT : v ∈ B \ T := Finset.mem_sdiff.mpr ⟨hv, hvT⟩
      have hx : v ∈ incWord (B \ T) := by simpa [incWord] using hvBT
      have hy : u ∈ decWord T := by simpa [decWord] using hu
      exact hparts.2.2 v hx u hy huv
  · intro hs
    rw [wordCompatible, blockWord, List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · refine (Finset.pairwise_sort (B \ T) (· ≤ ·)).imp ?_
      intro x y hxy hyx
      exact (not_lt_of_ge hxy) (hinc hyx)
    · apply List.pairwise_of_forall_mem_list
      intro x hx y hy
      have hxT : x ∈ T := by simpa [decWord] using hx
      have hyT : y ∈ T := by simpa [decWord] using hy
      exact (hs _ hyT).2 _ (hT hxT)
    · intro x hx y hy hyx
      have hxBT : x ∈ B \ T := by simpa [incWord] using hx
      have hyT : y ∈ T := by simpa [decWord] using hy
      exact (hs _ hyT).2 _ (Finset.mem_sdiff.mp hxBT).1 hyx

end

end VerticalStripLLT.Components
