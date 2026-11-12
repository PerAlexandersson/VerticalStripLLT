import VerticalStripLLT.CyclicHessenberg.ColorInsertion

/-! Remove forbidden vertices from a color product using its actual word support. -/

namespace VerticalStripLLT.CyclicHessenberg

variable {V R : Type*} [LinearOrder V] [CommRing R]

/-- A full-support functional annihilates a forbidden letter in every context. -/
theorem supported_letter_zero (A : Finset V) (f : List V → R)
    (hf : ∀ w, ¬ IsOrder A w → f w = 0) (a : V) (ha : a ∉ A) :
    ContextEq f (wordTerm [a]) 0 := by
  intro ρ σ
  rw [wordEval_term, map_zero]
  apply hf
  intro hw
  exact ha ((hw.mem_iff a).mp (by simp))

theorem descendingClass_filter (f : List V → R) (p : V → Bool)
    (hkill : ∀ a, p a = false → ContextEq f (wordTerm [a]) 0)
    (t : R) (l : List V) :
    ContextEq f (descendingClass t l) (descendingClass t (l.filter p)) := by
  induction l with
  | nil => exact ContextEq.refl _
  | cons a l ih =>
    by_cases ha : p a = true
    · simpa only [List.filter_cons_of_pos ha, descendingClass] using
        ih.mul (ContextEq.refl (1 + t • wordTerm [a]))
    · have hzero := (ContextEq.refl (1 : WordSum R V)).add
        ((hkill a (Bool.eq_false_iff.mpr ha)).smul t)
      simpa only [List.filter_cons_of_neg ha, descendingClass, smul_zero, add_zero,
        mul_one] using ih.mul hzero

theorem colorClassProduct_filter (f : List V → R) (p : V → Bool)
    (hkill : ∀ a, p a = false → ContextEq f (wordTerm [a]) 0)
    (l : List V) (Y : List R) :
    ContextEq f (colorClassProduct l Y) (colorClassProduct (l.filter p) Y) := by
  induction Y with
  | nil => exact ContextEq.refl _
  | cons t Y ih => exact (descendingClass_filter f p hkill t l).mul ih

theorem filter_sort_of_subset (A T : Finset V) (hAT : A ⊆ T) :
    T.sort.filter (fun a => decide (a ∈ A)) = A.sort := by
  classical
  apply List.SortedLT.eq_of_mem_iff ((Finset.sortedLT_sort T).filter _)
    (Finset.sortedLT_sort A)
  intro a
  simp only [List.mem_filter, Finset.mem_sort, decide_eq_true_eq]
  exact and_iff_right_of_imp (fun ha => hAT ha)

/-- The residual functional discards all factors outside its support, before any coloring sum. -/
theorem colorClassProduct_restrict (A T : Finset V) (hAT : A ⊆ T)
    (f : List V → R) (hf : ∀ w, ¬ IsOrder A w → f w = 0) (Y : List R) :
    ContextEq f (colorClassProduct T.sort Y) (colorClassProduct A.sort Y) := by
  classical
  have hh := colorClassProduct_filter f (fun a => decide (a ∈ A))
    (fun a ha => supported_letter_zero A f hf a (by simpa using ha)) T.sort Y
  rwa [filter_sort_of_subset A T hAT] at hh

/-- A fixed valid prefix leaves exactly the complementary support for the residual word. -/
theorem supported_prefix (S U : Finset V) (hUS : U ⊆ S) (p : Order U)
    (f : List V → R) (hf : ∀ w, ¬ IsOrder S w → f w = 0) :
    ∀ w, ¬ IsOrder (S \ U) w → f (p.val ++ w) = 0 := by
  intro w hw
  apply hf
  intro hpw
  have h := isOrder_append_left_iff p.property (Finset.sdiff_disjoint.symm)
  have hu : U ∪ (S \ U) = S := Finset.union_sdiff_of_subset hUS
  rw [hu] at h
  exact hw (h.mp hpw)

end VerticalStripLLT.CyclicHessenberg
