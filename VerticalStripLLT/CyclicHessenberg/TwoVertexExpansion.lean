import VerticalStripLLT.CyclicHessenberg.ExpansionRootSum

/-! Symbolic small-support regression formulas, retaining independent kernel entries. -/

namespace VerticalStripLLT.CyclicHessenberg

variable {V : Type*} [LinearOrder V]

@[simp] theorem order_singleton_val (a : V) (σ : Order ({a} : Finset V)) : σ.val = [a] := by
  have hl : σ.val.length = 1 := by simpa using σ.property.length
  obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp hl
  have hmem : b ∈ ({a} : Finset V) := (σ.property.mem_iff b).mp (by rw [hb]; simp)
  have hba : b = a := Finset.mem_singleton.mp hmem
  simpa only [hba] using hb

instance orderSingletonUnique (a : V) : Unique (Order ({a} : Finset V)) where
  default := ⟨[a], by simp [IsOrder]⟩
  uniq σ := Subtype.ext (order_singleton_val a σ)

theorem naturalKernelExpansion_singleton (r : V) (Z : List V → List V → Polynomial ℕ) :
    naturalKernelExpansion {r} Z = natElementary 1 * MvPolynomial.C (Z [r] [r]) := by
  have hh := naturalKernelExpansion_insert_max (∅ : Finset V) r (by simp) Z
  simpa using hh

/-- Two vertices have one two-cycle term and one two-singleton term. -/
theorem naturalKernelExpansion_pair (a r : V) (har : a < r)
    (Z : List V → List V → Polynomial ℕ) :
    naturalKernelExpansion {r, a} Z =
      MvPolynomial.C (Z [r, a] [r, a]) * natElementary 1 ^ 2 +
        MvPolynomial.C (Polynomial.X * Z [r, a] [a, r]) * natElementary 2 := by
  classical
  have hne : a ≠ r := ne_of_lt har
  have hr : ∀ b ∈ ({a} : Finset V), b < r := by simpa using har
  have hps : ({a} : Finset V).powerset = {∅, {a}} := by
    ext U
    simp only [Finset.mem_powerset, Finset.subset_singleton_iff, Finset.mem_insert,
      Finset.mem_singleton]
  rw [naturalKernelExpansion_insert_max {a} r hr]
  simp only [hps, Finset.sum_insert, Finset.mem_singleton,
    Finset.empty_ne_singleton, not_false_eq_true, Finset.sum_singleton]
  simp only [Finset.card_empty, Finset.card_singleton, Finset.insert_empty]
  have hdiff : ({r, a} : Finset V) \ {r} = {a} := by
    ext b
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hb | hb, hnot⟩
      · exact (hnot hb).elim
      · exact hb
    · rintro rfl
      exact ⟨Or.inr rfl, hne⟩
  rw [hdiff, naturalKernelExpansion_singleton, Finset.sdiff_self, naturalKernelExpansion_empty]
  simp only [rootDeletion_singleton, List.nil_append, List.cons_append]
  have hroot : rootDeletion (Polynomial.X : Polynomial ℕ) Z {r, a} r [] [] =
      Polynomial.X * Z [r, a] [a, r] := by
    unfold rootDeletion
    have herase : ({r, a} : Finset V).erase r = {a} := by simp [hne, hne.symm]
    rw [herase]
    simp [Finset.card_insert_of_notMem (show r ∉ ({a} : Finset V) by simp [hne.symm])]
  rw [hroot]
  change natElementary 1 * (natElementary 1 * MvPolynomial.C (Z [r, a] [r, a])) +
    natElementary 2 * MvPolynomial.C (Polynomial.X * Z [r, a] [a, r]) = _
  ring

end VerticalStripLLT.CyclicHessenberg
