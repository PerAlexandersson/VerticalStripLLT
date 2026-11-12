import VerticalStripLLT.CyclicHessenberg.CycleDisplay
import VerticalStripLLT.CyclicHessenberg.CycleRoots

/-! Construct the canonical cycle display from a permutation, including its fixed points. -/

namespace VerticalStripLLT.CyclicHessenberg

variable {V : Type*} [LinearOrder V] [Fintype V]

def orbitBlock (p : Equiv.Perm V) (r : V) : V × List V :=
  (r, (correctedOrbitList p r).tail)

theorem orbitBlock_source (p : Equiv.Perm V) (r : V) :
    (orbitBlock p r).1 :: (orbitBlock p r).2 = correctedOrbitList p r := by
  have hn := correctedOrbitList_nonempty p r
  have hh := List.cons_head_tail hn
  rw [correctedOrbitList_head p r hn] at hh
  exact hh

noncomputable def permutationBlocks (p : Equiv.Perm V) : List (V × List V) :=
  ((cycleRoots p).sort (· ≥ ·)).map (orbitBlock p)

theorem permutationBlocks_source (p : Equiv.Perm V) :
    cycleSourceWord (permutationBlocks p) =
      ((cycleRoots p).sort (· ≥ ·)).flatMap (correctedOrbitList p) := by
  simp only [permutationBlocks, cycleSourceWord, List.flatMap_map, Function.comp_def,
    orbitBlock_source]

/-- The independent, orbit-based inverse candidate to reading a display as a permutation. -/
noncomputable def permutationDisplay (p : Equiv.Perm V) :
    CycleDisplay (Finset.univ : Finset V) where
  blocks := permutationBlocks p
  source_order := by
    rw [permutationBlocks_source]
    constructor
    · apply List.nodup_flatMap.mpr
      refine ⟨fun r hr => correctedOrbitList_nodup p r, ?_⟩
      apply ((cycleRoots p).sort_nodup (· ≥ ·)).imp_of_mem
      intro r s hr hs hne
      exact correctedOrbitList_disjoint_of_cycleRoots_ne p
        (by simpa only [Finset.mem_sort] using hr)
        (by simpa only [Finset.mem_sort] using hs) hne
    · apply Finset.ext
      intro x
      simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
      obtain ⟨r, hr, _⟩ := existsUnique_cycleRoot p x
      exact List.mem_flatMap.mpr ⟨r, by simpa only [Finset.mem_sort] using hr.1,
        (mem_correctedOrbitList_iff p r x).mpr hr.2⟩
  root_max := by
    intro b hb x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
    have hmem : x ∈ correctedOrbitList p r := List.mem_of_mem_tail hx
    have hnd := correctedOrbitList_nodup p r
    rw [← orbitBlock_source p r] at hnd
    have hne : x ≠ r := by
      intro heq
      subst x
      exact (List.nodup_cons.mp hnd).1 hx
    exact correctedOrbitList_other_lt_root p r x
      (by simpa only [Finset.mem_sort] using hr) hmem hne
  roots_desc := by
    rw [permutationBlocks, List.pairwise_map]
    exact (cycleRoots p).sortedGT_sort.pairwise

namespace CycleDisplay

/-- Read a full-support display as a permutation on the ambient finite type. -/
def fullPerm (D : CycleDisplay (Finset.univ : Finset V)) : Equiv.Perm V :=
  let e : (Finset.univ : Finset V) ≃ V :=
    Equiv.subtypeUnivEquiv (fun _ => Finset.mem_univ _)
  e.symm.trans (D.toPerm.trans e)

theorem fullPerm_map_source (D : CycleDisplay (Finset.univ : Finset V)) :
    D.source.val.map D.fullPerm = D.target.val := by
  have hs : List.ofFn (fun i => (orderEquiv D.source i).val) = D.source.val :=
    congrArg Subtype.val (orderOfEquiv_orderEquiv D.source)
  have ht : List.ofFn (fun i => (orderEquiv D.target i).val) = D.target.val :=
    congrArg Subtype.val (orderOfEquiv_orderEquiv D.target)
  rw [← hs, List.map_ofFn, ← ht]
  apply congrArg List.ofFn
  funext i
  change (D.toPerm (orderEquiv D.source i)).val = (orderEquiv D.target i).val
  rw [toPerm_apply_source]

theorem fullPerm_eq_of_map_source (D : CycleDisplay (Finset.univ : Finset V))
    (p : Equiv.Perm V) (hp : D.source.val.map p = D.target.val) : D.fullPerm = p := by
  apply Equiv.ext
  intro x
  have hm : x ∈ D.source.val := (D.source.property.mem_iff x).mpr (Finset.mem_univ _)
  exact List.map_inj_left.mp (D.fullPerm_map_source.trans hp.symm) x hm

end CycleDisplay

end VerticalStripLLT.CyclicHessenberg
