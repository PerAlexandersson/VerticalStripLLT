import VerticalStripLLT.FirstBounceGraph
import VerticalStripLLT.SecondBouncePath
import VerticalStripLLT.SecondBounceScanners

namespace VerticalStripLLT
namespace SchroderPath

open Step

section
variable {n : ℕ} (U V W : List Step)
    (h : validFrom n 0 0 ((U ++ diagonal :: north :: V) ++ diagonal :: east :: W) = true)
    (hgap : (endpointFrom 0 0 (U ++ diagonal :: north :: V)).1 + 1 <
      (endpointFrom 0 0 (U ++ diagonal :: north :: V)).2)

include h in
/-- Resolving the first diagonal of the source into `east, north` stays valid. -/
theorem secondBounce_resolved_valid :
    validFrom n 0 0 (((U ++ [east]) ++ north :: north :: V) ++ diagonal :: east :: W) = true := by
  have h₁ : validFrom n 0 0
      (U ++ diagonal :: (north :: V ++ diagonal :: east :: W)) = true := by
    simpa only [List.append_assoc, List.cons_append] using h
  simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using
    (validFrom_resolve n 0 0 h₁).2

include hgap in
theorem secondBounce_resolved_gap :
    (endpointFrom 0 0 ((U ++ [east]) ++ north :: north :: V)).1 + 1 <
      (endpointFrom 0 0 ((U ++ [east]) ++ north :: north :: V)).2 := by
  rw [endpointFrom_secondBounce_source]
  exact hgap

/-- The common background `U e n n V e e n W`. -/
def secondBounceBase : SchroderPath n :=
  firstBounceBase ((U ++ [east]) ++ north :: north :: V) W
    (secondBounce_resolved_valid U V W h) (secondBounce_resolved_gap U V hgap)

theorem secondBounceBase_steps :
    (secondBounceBase U V W h hgap).steps =
      ((U ++ [east]) ++ north :: north :: V) ++ east :: east :: north :: W :=
  firstBounceBase_steps _ _ _ _

include h in
theorem secondBounce_corner_lt :
    (endpointFrom 0 0 U).1 < (endpointFrom 0 0 U).2 ∧ (endpointFrom 0 0 U).2 < n :=
  markedDiagonal_bounds n 0 0 U (north :: V ++ diagonal :: east :: W)
    (by simpa only [List.append_assoc, List.cons_append] using h)

/-- The vertex `a`, the column of the first diagonal. -/
def secondBounceCorner : Fin n :=
  ⟨(endpointFrom 0 0 U).1,
    (secondBounce_corner_lt U V W h).1.trans (secondBounce_corner_lt U V W h).2⟩

/-- The vertex `i`, the column of the second diagonal. -/
def secondBounceLow : Fin n :=
  firstBounceLow ((U ++ [east]) ++ north :: north :: V) W (secondBounce_resolved_valid U V W h)

/-- The vertex `y = i + 1`. -/
def secondBounceMid : Fin n :=
  firstBounceMid ((U ++ [east]) ++ north :: north :: V) W (secondBounce_resolved_valid U V W h)
    (secondBounce_resolved_gap U V hgap)

/-- The vertex `z = j`, the height of the second diagonal. -/
def secondBounceTop : Fin n :=
  firstBounceTop ((U ++ [east]) ++ north :: north :: V) W (secondBounce_resolved_valid U V W h)

theorem secondBounceLow_val :
    (secondBounceLow U V W h).val = (endpointFrom 0 0 (U ++ diagonal :: north :: V)).1 := by
  change (endpointFrom 0 0 ((U ++ [east]) ++ north :: north :: V)).1 = _
  rw [endpointFrom_secondBounce_source]

theorem secondBounceMid_val :
    (secondBounceMid U V W h hgap).val =
      (endpointFrom 0 0 (U ++ diagonal :: north :: V)).1 + 1 := by
  change (endpointFrom 0 0 ((U ++ [east]) ++ north :: north :: V)).1 + 1 = _
  rw [endpointFrom_secondBounce_source]

theorem secondBounceTop_val :
    (secondBounceTop U V W h).val = (endpointFrom 0 0 (U ++ diagonal :: north :: V)).2 := by
  change (endpointFrom 0 0 ((U ++ [east]) ++ north :: north :: V)).2 = _
  rw [endpointFrom_secondBounce_source]

theorem secondBounce_source_normal :
    (⟨(U ++ diagonal :: north :: V) ++ diagonal :: east :: W, h⟩ : SchroderPath n).normalEdges =
      insert (secondBounceMid U V W h hgap, secondBounceTop U V W h)
        (secondBounceBase U V W h hgap).normalEdges := by
  rw [secondBounceBase, secondBounceMid, secondBounceTop, ← firstBounce_source_normal]
  ext e
  simp only [normalEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [normalFrom_secondBounce_source]

theorem secondBounce_fresh_top :
    (secondBounceMid U V W h hgap, secondBounceTop U V W h) ∉
      (secondBounceBase U V W h hgap).normalEdges :=
  firstBounce_fresh _ W _ _

theorem secondBounce_low_mid_mem :
    (secondBounceLow U V W h, secondBounceMid U V W h hgap) ∈
      (secondBounceBase U V W h hgap).normalEdges :=
  firstBounce_low_mid_mem _ W _ _

end

section
variable {n : ℕ} (U V W : List Step)
    (h : validFrom n 0 0 ((U ++ diagonal :: north :: V) ++ diagonal :: east :: W) = true)
    (hreturn : (endpointFrom 0 0 U).2 = (endpointFrom 0 0 (U ++ diagonal :: north :: V)).1)
    (hgap : (endpointFrom 0 0 (U ++ diagonal :: north :: V)).1 + 1 <
      (endpointFrom 0 0 (U ++ diagonal :: north :: V)).2)
include hreturn

theorem secondBounce_target_strict :
    (secondBounceSuccessor U V W h hgap).strictEdges =
      insert (secondBounceCorner U V W h, secondBounceMid U V W h hgap)
        (insert (secondBounceMid U V W h hgap, secondBounceTop U V W h)
          (secondBounceBase U V W h hgap).strictEdges) := by
  rw [secondBounceBase, secondBounceMid, secondBounceTop, ← firstBounce_succ_strict]
  ext ⟨u, v⟩
  simp only [strictEdges, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and,
    Prod.mk.injEq, Fin.ext_iff]
  simp only [secondBounceSuccessor_steps, swapDiagonalEast_steps,
    strictFrom_secondBounce_target, secondBounceCorner, firstBounceMid,
    endpointFrom_secondBounce_source, ← hreturn]
  tauto

theorem secondBounce_source_strict :
    (⟨(U ++ diagonal :: north :: V) ++ diagonal :: east :: W, h⟩ : SchroderPath n).strictEdges =
      insert (secondBounceCorner U V W h, secondBounceLow U V W h)
        (insert (secondBounceLow U V W h, secondBounceTop U V W h)
          (secondBounceBase U V W h hgap).strictEdges) := by
  rw [secondBounceBase, secondBounceLow, secondBounceTop, ← firstBounce_source_strict]
  ext ⟨u, v⟩
  simp only [strictEdges, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and,
    Prod.mk.injEq, Fin.ext_iff]
  simp only [strictFrom_secondBounce_source, secondBounceCorner, firstBounceLow,
    endpointFrom_secondBounce_source, ← hreturn]
  tauto

theorem secondBounce_target_normal :
    (secondBounceSuccessor U V W h hgap).normalEdges =
      insert (secondBounceCorner U V W h, secondBounceLow U V W h)
        (secondBounceBase U V W h hgap).normalEdges := by
  rw [secondBounceBase, secondBounceLow, ← firstBounce_succ_normal]
  ext ⟨u, v⟩
  simp only [normalEdges, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and,
    Prod.mk.injEq, Fin.ext_iff]
  simp only [secondBounceSuccessor_steps, swapDiagonalEast_steps,
    normalFrom_secondBounce_target U V _ u.val v.val (secondBounce_corner_lt U V W h).1,
    secondBounceCorner, firstBounceLow, endpointFrom_secondBounce_source, ← hreturn]
  tauto

omit hreturn in
theorem secondBounce_endpoint_east :
    endpointFrom 0 0 (U ++ [east]) = ((endpointFrom 0 0 U).1 + 1, (endpointFrom 0 0 U).2) := by
  simp only [endpointFrom_append, endpointFrom]

/-- The return condition for the first-bounce prefix `U ++ [east]`. -/
theorem secondBounce_return_east :
    (endpointFrom 0 0 (U ++ [east])).2 =
      (endpointFrom 0 0 ((U ++ [east]) ++ north :: north :: V)).1 := by
  rw [endpointFrom_secondBounce_source, ← hreturn, secondBounce_endpoint_east]

theorem secondBounce_fresh_corner :
    (secondBounceCorner U V W h, secondBounceLow U V W h) ∉
      (secondBounceBase U V W h hgap).normalEdges := by
  have hlt := (secondBounce_corner_lt U V W h).1
  have hE1 : (endpointFrom 0 0 (U ++ [east])).1 = (endpointFrom 0 0 U).1 + 1 := by
    rw [secondBounce_endpoint_east]
  have hE2 : (endpointFrom 0 0 (U ++ [east])).2 = (endpointFrom 0 0 U).2 := by
    rw [secondBounce_endpoint_east]
  have hI := secondBounce_return_east U V hreturn
  simp only [normalEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    secondBounceBase_steps, secondBounceCorner, secondBounceLow, firstBounceLow]
  rw [normalFrom_firstBounce_split]
  rintro (h1 | h1 | h1 | h1 | h1)
  · have := normalFrom_endpoint_bounds 0 0 _ _ h1
    lia
  · have := normalFrom_lower_bound _ _ _ _ h1
    lia
  · lia
  · lia
  · have := normalFrom_lower_bound _ _ _ _ h1
    lia

theorem secondBounce_strict_swap_invariant :
    (secondBounceBase U V W h hgap).strictEdges.map
        (swapVertexPair (secondBounceLow U V W h) (secondBounceMid U V W h hgap)) =
      (secondBounceBase U V W h hgap).strictEdges :=
  firstBounce_strict_swap_invariant (U ++ [east]) V W (secondBounce_resolved_valid U V W h)
    (secondBounce_return_east U V hreturn) (secondBounce_resolved_gap U V hgap)

theorem secondBounce_normal_erase_swap_invariant :
    ((secondBounceBase U V W h hgap).normalEdges.erase
        (secondBounceLow U V W h, secondBounceMid U V W h hgap)).map
        (swapVertexPair (secondBounceLow U V W h) (secondBounceMid U V W h hgap)) =
      (secondBounceBase U V W h hgap).normalEdges.erase
        (secondBounceLow U V W h, secondBounceMid U V W h hgap) :=
  firstBounce_normal_erase_swap_invariant (U ++ [east]) V W
    (secondBounce_resolved_valid U V W h) (secondBounce_return_east U V hreturn)
    (secondBounce_resolved_gap U V hgap)

end

end SchroderPath
end VerticalStripLLT
