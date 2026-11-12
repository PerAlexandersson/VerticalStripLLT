import VerticalStripLLT.CyclicHessenberg.PermutationDisplay
import VerticalStripLLT.CyclicHessenberg.CycleBlockAction
import VerticalStripLLT.CyclicHessenberg.CycleDisplayFinite

/-! Canonical displays and permutations are mutually inverse finite representations. -/

namespace VerticalStripLLT.CyclicHessenberg

variable {V : Type*} [LinearOrder V] [Fintype V]

namespace CycleDisplay

theorem block_nodup {S : Finset V} (D : CycleDisplay S) {b : V × List V}
    (hb : b ∈ D.blocks) : (b.1 :: b.2).Nodup :=
  (List.nodup_flatMap.mp D.source_order.1).1 b hb

theorem correctedOrbitList_fullPerm (D : CycleDisplay (Finset.univ : Finset V))
    {b : V × List V} (hb : b ∈ D.blocks) :
    correctedOrbitList D.fullPerm b.1 = b.1 :: b.2 := by
  apply correctedOrbitList_eq_of_action D.fullPerm b.1 b.2 (D.block_nodup hb)
  apply (map_cons_eq_rotated_iff_formPerm_action _ _ _ (D.block_nodup hb)).mp
  exact (map_cycleSourceWord_eq_cycleTargetWord_iff D.fullPerm D.blocks).mp
    D.fullPerm_map_source b hb

theorem block_root_mem_cycleRoots (D : CycleDisplay (Finset.univ : Finset V))
    {b : V × List V} (hb : b ∈ D.blocks) : b.1 ∈ cycleRoots D.fullPerm := by
  apply (mem_cycleRoots_iff _ _).mpr
  intro x hx
  have hm := (mem_correctedOrbitList_iff D.fullPerm b.1 x).mpr hx
  rw [D.correctedOrbitList_fullPerm hb] at hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact le_rfl
  · exact (D.root_max b hb x hm).le

theorem roots_list_eq_sort (D : CycleDisplay (Finset.univ : Finset V)) :
    D.blocks.map Prod.fst = (cycleRoots D.fullPerm).sort (· ≥ ·) := by
  have hdesc : (D.blocks.map Prod.fst).Pairwise (fun a b => b < a) := by
    simpa only [List.pairwise_map] using D.roots_desc
  apply hdesc.eq_of_mem_iff (cycleRoots D.fullPerm).sortedGT_sort.pairwise
  intro r
  rw [Finset.mem_sort]
  constructor
  · intro hr
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr
    exact D.block_root_mem_cycleRoots hb
  · intro hr
    have hm := (D.source_order.mem_iff r).mpr (Finset.mem_univ _)
    obtain ⟨b, hb, hm⟩ := List.mem_flatMap.mp hm
    have hcycle : D.fullPerm.SameCycle b.1 r := by
      apply (mem_correctedOrbitList_iff _ _ _).mp
      rw [D.correctedOrbitList_fullPerm hb]
      exact hm
    have heq := cycleRoots_sameCycle_eq D.fullPerm (D.block_root_mem_cycleRoots hb) hr hcycle
    exact List.mem_map.mpr ⟨b, hb, heq⟩

end CycleDisplay

theorem permutationDisplay_fullPerm (D : CycleDisplay (Finset.univ : Finset V)) :
    permutationDisplay D.fullPerm = D := by
  apply CycleDisplay.ext
  change permutationBlocks D.fullPerm = D.blocks
  rw [permutationBlocks, ← D.roots_list_eq_sort, List.map_map]
  calc
    D.blocks.map (fun b => orbitBlock D.fullPerm b.1) = D.blocks.map id := by
      apply List.map_congr_left
      intro b hb
      apply Prod.ext
      · rfl
      · change (correctedOrbitList D.fullPerm b.1).tail = b.2
        rw [D.correctedOrbitList_fullPerm hb]
        rfl
    _ = D.blocks := List.map_id _

theorem fullPerm_permutationDisplay (p : Equiv.Perm V) :
    (permutationDisplay p).fullPerm = p := by
  apply CycleDisplay.fullPerm_eq_of_map_source
  apply (map_cycleSourceWord_eq_cycleTargetWord_iff p (permutationBlocks p)).mpr
  intro b hb
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
  apply (map_cons_eq_rotated_iff_formPerm_action _ _ _ ?_).mpr
  · rw [orbitBlock_source]
    intro x hx
    exact (correctedOrbitList_formPerm_apply p r x hx).symm
  · rw [orbitBlock_source]
    exact correctedOrbitList_nodup p r

/-- The canonical-cycle representation has exactly one display per permutation. -/
noncomputable def cycleDisplayEquivPerm :
    CycleDisplay (Finset.univ : Finset V) ≃ Equiv.Perm V where
  toFun := CycleDisplay.fullPerm
  invFun := permutationDisplay
  left_inv := permutationDisplay_fullPerm
  right_inv := fullPerm_permutationDisplay

end VerticalStripLLT.CyclicHessenberg
