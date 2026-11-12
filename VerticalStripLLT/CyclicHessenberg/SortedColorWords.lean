import VerticalStripLLT.CyclicHessenberg.LoopColorOrder

/-! Sorting colors gives a finite bijection with lexicographically ordered positional data. -/

namespace VerticalStripLLT.CyclicHessenberg

variable {k m : ℕ}

theorem colorSortedPerm_unique (κ : Fin k → Fin m) (π : Equiv.Perm (Fin k))
    (hπ : ∀ i j, i < j → colorPrecedes κ (π i) (π j)) : π = colorSortedPerm κ := by
  letI : Std.Antisymm (colorPrecedes κ) := ⟨by
    intro a b hab hba
    rcases hab with hab | ⟨hab, hab'⟩ <;>
      rcases hba with hba | ⟨hba, hba'⟩
    · exact False.elim (lt_asymm hab hba)
    · exact False.elim ((ne_of_lt hab) hba.symm)
    · exact False.elim ((ne_of_lt hba) hab.symm)
    · exact False.elim (lt_asymm hab' hba')⟩
  have hp : (List.ofFn π).Pairwise (colorPrecedes κ) := by
    rw [List.pairwise_ofFn]
    exact hπ
  have hc : (List.ofFn (colorSortedPerm κ)).Pairwise (colorPrecedes κ) := by
    rw [List.pairwise_ofFn]
    exact fun _ _ hij => colorSortedPerm_precedes_of_lt κ hij
  have hperm : (List.ofFn π).Perm (List.ofFn (colorSortedPerm κ)) := by
    apply (List.perm_ext_iff_of_nodup (by simpa only [List.nodup_ofFn] using π.injective)
      (by simpa only [List.nodup_ofFn] using (colorSortedPerm κ).injective)).mpr
    intro x
    simp only [List.mem_ofFn]
    exact ⟨fun _ => (colorSortedPerm κ).surjective x, fun _ => π.surjective x⟩
  exact Equiv.ext (congrFun (List.ofFn_injective (List.Perm.eq_of_pairwise' hp hc hperm)))

def PositionalColorSorted (π : Equiv.Perm (Fin k)) (α : Fin k → Fin m) : Prop :=
  ∀ i j, i < j → α i < α j ∨ (α i = α j ∧ π j < π i)

abbrev SortedColorPair (k m : ℕ) :=
  {p : Equiv.Perm (Fin k) × (Fin k → Fin m) // PositionalColorSorted p.1 p.2}

noncomputable instance sortedColorPairFintype : Fintype (SortedColorPair k m) :=
  Fintype.ofFinite _

theorem PositionalColorSorted.monotone {π : Equiv.Perm (Fin k)} {α : Fin k → Fin m}
    (hp : PositionalColorSorted π α) : Monotone α := by
  intro i j hij
  rcases lt_or_eq_of_le hij with hij | rfl
  · rcases hp i j hij with h | ⟨h, _⟩
    · exact h.le
    · exact h.le
  · exact le_rfl

noncomputable def coloringSortedPairEquiv : (Fin k → Fin m) ≃ SortedColorPair k m where
  toFun κ := ⟨⟨colorSortedPerm κ, fun i => κ (colorSortedPerm κ i)⟩,
    fun i j hij => colorSortedPerm_precedes_of_lt κ hij⟩
  invFun p := fun a => p.val.2 (p.val.1.symm a)
  left_inv κ := by funext a; simp
  right_inv p := by
    let κ := fun a => p.val.2 (p.val.1.symm a)
    have hp : p.val.1 = colorSortedPerm κ := by
      apply colorSortedPerm_unique
      intro i j hij
      simpa only [colorPrecedes, κ, Equiv.symm_apply_apply] using p.property i j hij
    apply Subtype.ext
    apply Prod.ext
    · exact hp.symm
    · funext i
      change κ (colorSortedPerm κ i) = p.val.2 i
      rw [← hp]
      exact congrArg p.val.2 (p.val.1.symm_apply_apply i)

end VerticalStripLLT.CyclicHessenberg
