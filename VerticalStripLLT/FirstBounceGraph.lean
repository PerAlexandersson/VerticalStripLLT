import VerticalStripLLT.BounceScanners
import VerticalStripLLT.BouncePath
import VerticalStripLLT.SwapSum

namespace VerticalStripLLT
namespace SchroderPath

open Step

/-- The common background `R ++ [east, east, north] ++ W`, obtained by resolving the
diagonal of the swapped path `R ++ [east, diagonal] ++ W` into `east, north`. -/
def firstBounceBase {n : ℕ} (R W : List Step)
    (h : validFrom n 0 0 (R ++ diagonal :: east :: W) = true)
    (hgap : (endpointFrom 0 0 R).1 + 1 < (endpointFrom 0 0 R).2) : SchroderPath n :=
  resolveEastNorth (R ++ [east]) W (by
    simpa only [List.append_assoc, List.singleton_append, swapDiagonalEast_steps] using
      (swapDiagonalEast R W h hgap).valid)

theorem firstBounceBase_steps {n : ℕ} (R W : List Step)
    (h : validFrom n 0 0 (R ++ diagonal :: east :: W) = true)
    (hgap : (endpointFrom 0 0 R).1 + 1 < (endpointFrom 0 0 R).2) :
    (firstBounceBase R W h hgap).steps = R ++ east :: east :: north :: W := by
  simp [firstBounceBase]

theorem firstBounce_top_lt {n : ℕ} (R W : List Step)
    (h : validFrom n 0 0 (R ++ diagonal :: east :: W) = true) :
    (endpointFrom 0 0 R).2 < n :=
  (markedDiagonal_bounds n 0 0 R (east :: W) h).2

theorem firstBounce_normal_split (R X : List Step) (a b : ℕ) :
    normalFrom 0 0 a b (R ++ X) = true ↔ normalFrom 0 0 a b R = true ∨
      normalFrom (endpointFrom 0 0 R).1 (endpointFrom 0 0 R).2 a b X = true := by
  rw [normalFrom_append, Bool.or_eq_true]

theorem firstBounce_strict_split (R X : List Step) (a b : ℕ) :
    strictFrom 0 0 a b (R ++ X) = true ↔ strictFrom 0 0 a b R = true ∨
      strictFrom (endpointFrom 0 0 R).1 (endpointFrom 0 0 R).2 a b X = true := by
  rw [strictFrom_append, Bool.or_eq_true]

/-- The low vertex `i` (the column of the diagonal). -/
def firstBounceLow {n : ℕ} (R W : List Step)
    (h : validFrom n 0 0 (R ++ diagonal :: east :: W) = true) : Fin n :=
  ⟨(endpointFrom 0 0 R).1, (markedDiagonal_bounds n 0 0 R (east :: W) h).1.trans
    (firstBounce_top_lt R W h)⟩

/-- The middle vertex `y = i + 1`. -/
def firstBounceMid {n : ℕ} (R W : List Step)
    (h : validFrom n 0 0 (R ++ diagonal :: east :: W) = true)
    (hgap : (endpointFrom 0 0 R).1 + 1 < (endpointFrom 0 0 R).2) : Fin n :=
  ⟨(endpointFrom 0 0 R).1 + 1, hgap.trans (firstBounce_top_lt R W h)⟩

/-- The top vertex `z = j` (the height of the diagonal). -/
def firstBounceTop {n : ℕ} (R W : List Step)
    (h : validFrom n 0 0 (R ++ diagonal :: east :: W) = true) : Fin n :=
  ⟨(endpointFrom 0 0 R).2, firstBounce_top_lt R W h⟩

section
variable {n : ℕ} (R W : List Step)
    (h : validFrom n 0 0 (R ++ diagonal :: east :: W) = true)
    (hgap : (endpointFrom 0 0 R).1 + 1 < (endpointFrom 0 0 R).2)

theorem firstBounce_source_normal :
    (⟨R ++ diagonal :: east :: W, h⟩ : SchroderPath n).normalEdges =
      insert (firstBounceMid R W h hgap, firstBounceTop R W h)
        (firstBounceBase R W h hgap).normalEdges := by
  ext ⟨a, b⟩
  simp only [normalEdges, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Prod.mk.injEq, Fin.ext_iff, firstBounceBase_steps, firstBounce_normal_split,
    firstBounceMid, firstBounceTop]
  simp only [normalFrom, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  generalize (endpointFrom 0 0 R).1 = i at *
  generalize (endpointFrom 0 0 R).2 = j at *
  generalize normalFrom 0 0 (↑a) (↑b) R = p
  generalize normalFrom (i + 1 + 1) (j + 1) (↑a) (↑b) W = q
  cases p <;> cases q <;> simp only [Bool.false_eq_true, false_or, or_false, or_true,
    true_or]
  lia

theorem firstBounce_source_strict :
    (⟨R ++ diagonal :: east :: W, h⟩ : SchroderPath n).strictEdges =
      insert (firstBounceLow R W h, firstBounceTop R W h)
        (firstBounceBase R W h hgap).strictEdges := by
  ext ⟨a, b⟩
  simp only [strictEdges, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Prod.mk.injEq, Fin.ext_iff, firstBounceBase_steps, firstBounce_strict_split,
    firstBounceLow, firstBounceTop]
  simp only [strictFrom, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  generalize strictFrom 0 0 (↑a) (↑b) R = p
  generalize strictFrom _ _ (↑a) (↑b) W = q
  cases p <;> cases q <;> simp only [Bool.false_eq_true, false_or, or_false, or_true,
    true_or]

theorem firstBounce_succ_normal :
    (swapDiagonalEast R W h hgap).normalEdges = (firstBounceBase R W h hgap).normalEdges := by
  ext ⟨a, b⟩
  simp only [normalEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    firstBounceBase_steps, swapDiagonalEast_steps, firstBounce_normal_split]
  simp only [normalFrom]

theorem firstBounce_succ_strict :
    (swapDiagonalEast R W h hgap).strictEdges =
      insert (firstBounceMid R W h hgap, firstBounceTop R W h)
        (firstBounceBase R W h hgap).strictEdges := by
  ext ⟨a, b⟩
  simp only [strictEdges, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Prod.mk.injEq, Fin.ext_iff, firstBounceBase_steps, swapDiagonalEast_steps,
    firstBounce_strict_split, firstBounceMid, firstBounceTop]
  simp only [strictFrom, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  generalize strictFrom 0 0 (↑a) (↑b) R = p
  generalize strictFrom _ _ (↑a) (↑b) W = q
  cases p <;> cases q <;> simp only [Bool.false_eq_true, false_or, or_false, or_true,
    true_or]

theorem firstBounce_fresh :
    (firstBounceMid R W h hgap, firstBounceTop R W h) ∉
      (firstBounceBase R W h hgap).normalEdges := by
  simp only [normalEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    firstBounceBase_steps, firstBounce_normal_split, firstBounceMid, firstBounceTop]
  simp only [normalFrom, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  rintro (hR | hR | hR | hR)
  · have := normalFrom_endpoint_bounds 0 0 _ _ hR
    lia
  · lia
  · lia
  · have := normalFrom_lower_bound _ _ _ _ hR
    lia

theorem firstBounce_low_mid_mem :
    (firstBounceLow R W h, firstBounceMid R W h hgap) ∈
      (firstBounceBase R W h hgap).normalEdges := by
  simp only [normalEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    firstBounceBase_steps, firstBounce_normal_split, firstBounceLow, firstBounceMid]
  simp only [normalFrom, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  exact Or.inr (Or.inl ⟨⟨trivial, by lia⟩, hgap⟩)

end

end SchroderPath
end VerticalStripLLT

namespace VerticalStripLLT
namespace SchroderPath

open Step

theorem map_swapVertexPair_eq_of_forall {n : ℕ} (a b : Fin n) (S : Finset (Fin n × Fin n))
    (hS : ∀ e ∈ S, swapVertexPair a b e ∈ S) : S.map (swapVertexPair a b) = S := by
  refine Finset.eq_of_subset_of_card_le ?_ (by rw [Finset.card_map])
  intro x hx
  obtain ⟨e, he, rfl⟩ := Finset.mem_map.1 hx
  exact hS e he

theorem swap_val_eq_swapNat {n : ℕ} (i y a : Fin n) (hy : y.val = i.val + 1) :
    (Equiv.swap i y a).val = swapNat i.val a.val := by
  rw [Equiv.swap_apply_def]
  unfold swapNat
  by_cases h1 : a = i
  · subst h1; simp [hy]
  · by_cases h2 : a = y
    · subst h2; simp [hy, h1]
    · have h1' : a.val ≠ i.val := fun h => h1 (Fin.ext h)
      have h2' : a.val ≠ i.val + 1 := fun h => h2 (Fin.ext (h.trans hy.symm))
      simp [h1, h2, h1', h2']

section
variable {n : ℕ} (U V W : List Step)
    (h : validFrom n 0 0 ((U ++ north :: north :: V) ++ diagonal :: east :: W) = true)
    (hreturn : (endpointFrom 0 0 U).2 = (endpointFrom 0 0 (U ++ north :: north :: V)).1)
    (hgap : (endpointFrom 0 0 (U ++ north :: north :: V)).1 + 1 <
      (endpointFrom 0 0 (U ++ north :: north :: V)).2)
include hreturn

theorem firstBounce_strict_swap_invariant :
    (firstBounceBase _ W h hgap).strictEdges.map
        (swapVertexPair (firstBounceLow _ W h) (firstBounceMid _ W h hgap)) =
      (firstBounceBase _ W h hgap).strictEdges := by
  apply map_swapVertexPair_eq_of_forall
  rintro ⟨a, b⟩ he
  have he' : strictFrom 0 0 a.val b.val
      ((U ++ north :: north :: V) ++ east :: east :: north :: W) = true := by
    simpa [strictEdges, firstBounceBase_steps] using he
  have hfix := strictFrom_firstBounce_fixed U V W hreturn a.val b.val he'
  have hy : (firstBounceMid _ W h hgap).val = (firstBounceLow _ W h).val + 1 := rfl
  have ha : Equiv.swap (firstBounceLow _ W h) (firstBounceMid _ W h hgap) a = a :=
    Fin.ext ((swap_val_eq_swapNat _ _ a hy).trans hfix.1)
  have hb : Equiv.swap (firstBounceLow _ W h) (firstBounceMid _ W h hgap) b = b :=
    Fin.ext ((swap_val_eq_swapNat _ _ b hy).trans hfix.2)
  rw [swapVertexPair_apply, ha, hb]
  exact he

theorem firstBounce_normal_erase_swap_invariant :
    ((firstBounceBase _ W h hgap).normalEdges.erase
        (firstBounceLow _ W h, firstBounceMid _ W h hgap)).map
        (swapVertexPair (firstBounceLow _ W h) (firstBounceMid _ W h hgap)) =
      (firstBounceBase _ W h hgap).normalEdges.erase
        (firstBounceLow _ W h, firstBounceMid _ W h hgap) := by
  apply map_swapVertexPair_eq_of_forall
  rintro ⟨a, b⟩ he
  rw [Finset.mem_erase] at he ⊢
  have hy : (firstBounceMid _ W h hgap).val = (firstBounceLow _ W h).val + 1 := rfl
  have he' : normalFrom 0 0 a.val b.val
      ((U ++ north :: north :: V) ++ east :: east :: north :: W) = true := by
    simpa [normalEdges, firstBounceBase_steps] using he.2
  have hne : ¬(a.val = (endpointFrom 0 0 (U ++ north :: north :: V)).1 ∧
      b.val = (endpointFrom 0 0 (U ++ north :: north :: V)).1 + 1) := by
    rintro ⟨h1, h2⟩
    exact he.1 (Prod.ext (Fin.ext h1) (Fin.ext h2))
  have hsw := normalFrom_firstBounce_swap U V W hreturn a.val b.val he' hne
  have hlt := normalFrom_lt 0 0 _ _ he'
  refine ⟨?_, ?_⟩
  · rw [swapVertexPair_apply]
    intro hEq
    have h1 := congrArg (fun p => (Equiv.swap (firstBounceLow _ W h)
      (firstBounceMid _ W h hgap) p.1).val) hEq
    have h2 := congrArg (fun p => (Equiv.swap (firstBounceLow _ W h)
      (firstBounceMid _ W h hgap) p.2).val) hEq
    simp only [Equiv.swap_apply_self, Equiv.swap_apply_left, Equiv.swap_apply_right] at h1 h2
    rw [hy] at h1
    change a.val = (endpointFrom 0 0 (U ++ north :: north :: V)).1 + 1 at h1
    change b.val = (endpointFrom 0 0 (U ++ north :: north :: V)).1 at h2
    lia
  · simp only [normalEdges, Finset.mem_filter, Finset.mem_univ, true_and,
      firstBounceBase_steps, swapVertexPair_apply]
    rw [swap_val_eq_swapNat _ _ a hy, swap_val_eq_swapNat _ _ b hy]
    exact hsw

end

end SchroderPath
end VerticalStripLLT
