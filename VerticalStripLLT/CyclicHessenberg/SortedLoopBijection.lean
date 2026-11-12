import VerticalStripLLT.CyclicHessenberg.SortedLoops
import VerticalStripLLT.CyclicHessenberg.SortedColorWords
import VerticalStripLLT.CyclicHessenberg.RunLexOrder

/-! The colored-cover model and the independent composition-sorted model have the same objects. -/

namespace VerticalStripLLT.CyclicHessenberg

variable {k n m : ℕ}

theorem positionalColorSorted_iff_sortedBlocks (π : Equiv.Perm (Fin k))
    (α : Fin k → Fin m) (β : Composition k) (hα : Monotone α)
    (hβ : colorRunComposition α = β) :
    PositionalColorSorted π α ↔
      ∀ b ∈ (List.ofFn π).splitWrtComposition β, b.Pairwise (· > ·) := by
  have hcolors : (List.ofFn α).Pairwise (· ≤ ·) := by
    rw [List.pairwise_ofFn]
    exact fun _ _ hij => hα hij.le
  have hblocks : β.blocks = ((List.ofFn α).equalityRuns).map List.length :=
    (congrArg Composition.blocks hβ).symm
  have hh := List.pairwise_zip_composition_iff_blocks_desc (List.ofFn α) (List.ofFn π)
    β (List.length_ofFn _) (List.length_ofFn _) hcolors hblocks
  have hzip : (List.ofFn α).zip (List.ofFn π) = List.ofFn (fun i => (α i, π i)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp [List.getElem_zip, List.getElem_ofFn]
  rw [hzip, List.pairwise_ofFn] at hh
  exact hh

abbrev SortedLoopColorData (h : Tuple k n) (m : ℕ) :=
  Σ β : Composition k, SortedLoopDecomposition h β × CompositionColorWord β m

noncomputable instance sortedLoopColorDataFintype (h : Tuple k n) (m : ℕ) :
    Fintype (SortedLoopColorData h m) := inferInstanceAs (Fintype (Sigma _))

noncomputable def sortColoredLoop (h : Tuple k n)
    (x : LoopCover h × (Fin k → Fin m)) : SortedLoopColorData h m := by
  let p := coloringSortedPairEquiv x.2
  let β := colorRunComposition p.val.2
  refine ⟨β, ⟨⟨⟨x.1, p.val.1⟩, ?_⟩, ⟨p.val.2, p.property.monotone, rfl⟩⟩⟩
  exact (positionalColorSorted_iff_sortedBlocks _ _ _ p.property.monotone rfl).mp p.property

def unsortColoredLoop (h : Tuple k n) (x : SortedLoopColorData h m) :
    LoopCover h × (Fin k → Fin m) :=
  ⟨x.2.1.val.1, fun a => x.2.2.val (x.2.1.val.2.symm a)⟩

theorem unsort_sortColoredLoop (h : Tuple k n) (x : LoopCover h × (Fin k → Fin m)) :
    unsortColoredLoop h (sortColoredLoop h x) = x := by
  apply Prod.ext
  · rfl
  · funext a
    exact congrArg x.2 ((colorSortedPerm x.2).apply_symm_apply a)

theorem sort_unsortColoredLoop (h : Tuple k n) (x : SortedLoopColorData h m) :
    sortColoredLoop h (unsortColoredLoop h x) = x := by
  rcases x with ⟨β, ⟨⟨⟨L, π⟩, hπ⟩, ⟨α, hα, hβ⟩⟩⟩
  have hp : PositionalColorSorted π α :=
    (positionalColorSorted_iff_sortedBlocks π α β hα hβ).mpr hπ
  let p : SortedColorPair k m := ⟨⟨π, α⟩, hp⟩
  have heq := coloringSortedPairEquiv.apply_symm_apply p
  change coloringSortedPairEquiv (fun a => α (π.symm a)) = p at heq
  unfold sortColoredLoop unsortColoredLoop
  dsimp only
  rw [heq]
  dsimp only [p]
  cases hβ
  rfl

/-- The bijection retains the cover, sorts its loops, and records their positive color runs. -/
noncomputable def coloredLoopSortedEquiv (h : Tuple k n) :
    (LoopCover h × (Fin k → Fin m)) ≃ SortedLoopColorData h m where
  toFun := sortColoredLoop h
  invFun := unsortColoredLoop h
  left_inv := unsort_sortColoredLoop h
  right_inv := sort_unsortColoredLoop h

end VerticalStripLLT.CyclicHessenberg
