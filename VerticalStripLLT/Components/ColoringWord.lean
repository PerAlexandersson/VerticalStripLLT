import VerticalStripLLT.Components.BlockExtractor
import VerticalStripLLT.Components.ComponentWords
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Nodup

/-! Words obtained by sorting each color fiber decreasingly. -/

namespace VerticalStripLLT.Components

noncomputable section

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The decreasing word in the fiber of a color. -/
def coloringFiber {m : ℕ} (c : V → Fin m) (k : Fin m) : List V :=
  decWord (Finset.univ.filter fun v => c v = k)

/-- List the color fibers in increasing color order, with each fiber decreasing. -/
def coloringWord {m : ℕ} (c : V → Fin m) : List V :=
  (List.ofFn (coloringFiber c)).flatten

private theorem mem_coloringFiber {m : ℕ} (c : V → Fin m) {k : Fin m} {v : V} :
    v ∈ coloringFiber c k ↔ c v = k := by
  simp [coloringFiber, decWord]

theorem fullWord_coloringWord {m : ℕ} (c : V → Fin m) :
    fullWord (coloringWord c) := by
  classical
  constructor
  · rw [coloringWord, List.nodup_flatten]
    constructor
    · intro l hl
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hl
      exact Finset.sort_nodup _ _
    · rw [List.pairwise_ofFn]
      intro i j hij v hv hw
      have hvi : c v = i := (mem_coloringFiber c).mp hv
      have hvj : c v = j := (mem_coloringFiber c).mp hw
      exact (Fin.ne_of_lt hij) (hvi.symm.trans hvj)
  · intro v
    rw [coloringWord, List.mem_flatten]
    refine ⟨coloringFiber c (c v), ?_, ?_⟩
    · exact List.mem_ofFn.mpr ⟨c v, rfl⟩
    · exact (mem_coloringFiber c).mpr rfl

private theorem no_same_color_edge_of_pairwise {m : ℕ} (c : V → Fin m)
    (R : V → V → Prop) (hforward : ∀ ⦃u v⦄, R u v → u < v)
    {k : Fin m} (hp : (coloringFiber c k).Pairwise (fun x y => ¬ R y x))
    {u v : V} (huc : c u = k) (hvc : c v = k) (huv : R u v) : False := by
  have hp' : (coloringFiber c k).Pairwise (fun x y => ¬R x y ∧ ¬R y x) := by
    apply List.pairwise_and_iff.mpr
    refine ⟨?_, hp⟩
    exact (Finset.pairwise_sort _ (· ≥ ·)).imp fun hxy hR =>
      (not_lt_of_ge hxy) (hforward hR)
  let : Std.Symm (fun x y => ¬R x y ∧ ¬R y x) :=
    ⟨fun _ _ h => ⟨h.2, h.1⟩⟩
  exact (hp'.forall ((mem_coloringFiber c).mpr huc)
    ((mem_coloringFiber c).mpr hvc) (ne_of_lt (hforward huv))).1 huv

private theorem pairwise_coloringFiber_of_strict {m : ℕ} (c : V → Fin m)
    (R : V → V → Prop)
    (hstrict : ∀ ⦃u v⦄, R u v → c u < c v) (k : Fin m) :
    (coloringFiber c k).Pairwise (fun x y => ¬ R y x) := by
  apply List.pairwise_of_forall_mem_list
  intro x hx y hy hyx
  have hcol := hstrict hyx
  have hxi := (mem_coloringFiber c).mp hx
  have hyi := (mem_coloringFiber c).mp hy
  rw [hxi, hyi] at hcol
  exact (lt_irrefl _) hcol

theorem wordCompatible_coloringWord_iff {m : ℕ} (c : V → Fin m)
    (R : V → V → Prop) (hforward : ∀ ⦃u v⦄, R u v → u < v) :
    wordCompatible R (coloringWord c) ↔
      ∀ ⦃u v⦄, R u v → c u < c v := by
  classical
  constructor
  · intro hw u v huv
    rw [wordCompatible, coloringWord, List.pairwise_flatten] at hw
    by_cases hcv : c v < c u
    · have hcross := (List.pairwise_ofFn.mp hw.2) hcv
      have hv : v ∈ coloringFiber c (c v) := (mem_coloringFiber c).mpr rfl
      have hu : u ∈ coloringFiber c (c u) := (mem_coloringFiber c).mpr rfl
      exact False.elim (hcross v hv u hu huv)
    · have hcu : c u ≤ c v := le_of_not_gt hcv
      by_cases hsame : c u = c v
      · have hmem : coloringFiber c (c u) ∈ List.ofFn (coloringFiber c) :=
          List.mem_ofFn.mpr ⟨c u, rfl⟩
        exact False.elim (no_same_color_edge_of_pairwise c R hforward
          (hw.1 _ hmem) rfl hsame.symm huv)
      · exact lt_of_le_of_ne hcu hsame
  · intro hstrict
    rw [wordCompatible, coloringWord, List.pairwise_flatten]
    refine ⟨?_, ?_⟩
    · intro l hl
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hl
      exact pairwise_coloringFiber_of_strict c R hstrict k
    · rw [List.pairwise_ofFn]
      intro i j hij x hx y hy hryx
      have hxi : c x = i := (mem_coloringFiber c).mp hx
      have hyj : c y = j := (mem_coloringFiber c).mp hy
      have hcol := hstrict hryx
      exact (not_lt_of_ge (Fin.le_of_lt hij)) (by simpa [hxi, hyj] using hcol)

end

end VerticalStripLLT.Components
