import VerticalStripLLT.CyclicHessenberg.CycleDisplayCons

/-! A canonical display splits uniquely at its maximal-root cycle. -/

namespace VerticalStripLLT.CyclicHessenberg

variable {V : Type*} [LinearOrder V]

namespace CycleDisplay

abbrev RootSet (S : Finset V) (r : V) := {U : Finset V // U ⊆ S ∧ r ∈ U}

noncomputable instance rootSetFintype (S : Finset V) (r : V) : Fintype (RootSet S r) := by
  classical
  exact Fintype.subtype (S.powerset.filter fun U => r ∈ U) (by simp)

abbrev RootData (S : Finset V) (r : V) :=
  Σ U : RootSet S r, Order (U.val.erase r) × CycleDisplay (S \ U.val)

def assemble (S : Finset V) (r : V) (hmax : ∀ a ∈ S, a ≤ r)
    (x : RootData S r) : CycleDisplay S :=
  cons S x.1.val r x.1.property.1 x.1.property.2 hmax x.2.1 x.2.2

theorem assemble_injective (S : Finset V) (r : V) (hmax : ∀ a ∈ S, a ≤ r) :
    Function.Injective (assemble S r hmax) := by
  rintro ⟨U, σ, D⟩ ⟨W, τ, E⟩ heq
  have hb := congrArg CycleDisplay.blocks heq
  change (r, σ.val) :: D.blocks = (r, τ.val) :: E.blocks at hb
  have htail : σ.val = τ.val := congrArg Prod.snd (List.cons.inj hb).1
  have herase : U.val.erase r = W.val.erase r :=
    σ.property.2.symm.trans ((congrArg List.toFinset htail).trans τ.property.2)
  have hU : U = W := by
    apply Subtype.ext
    have hi := congrArg (insert r) herase
    simpa only [Finset.insert_erase U.property.2, Finset.insert_erase W.property.2] using hi
  cases hU
  have hσ : σ = τ := Subtype.ext htail
  cases hσ
  have hD : D = E := CycleDisplay.ext (List.cons.inj hb).2
  cases hD
  rfl

theorem assemble_surjective (S : Finset V) (r : V) (hr : r ∈ S)
    (hmax : ∀ a ∈ S, a ≤ r) : Function.Surjective (assemble S r hmax) := by
  classical
  intro D
  have hne : D.blocks ≠ [] := by
    intro hnil
    have hm := (D.source_order.mem_iff r).mpr hr
    simpa [cycleSourceWord, hnil] using hm
  obtain ⟨b, B, hB⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨r', t⟩ := b
  have hroot : r' = r := by
    apply le_antisymm
    · exact hmax _ (D.root_mem (b := (r', t)) (by rw [hB]; simp))
    · exact D.first_root_max r' t B hB r hr
  subst r'
  let U : Finset V := (r :: t).toFinset
  have hsource : IsOrder S ((r :: t) ++ cycleSourceWord B) := by
    simpa only [hB, cycleSourceWord, List.flatMap_cons] using D.source_order
  have hnd := List.nodup_append'.mp hsource.1
  have hp : IsOrder U (r :: t) := ⟨hnd.1, rfl⟩
  have hUS : U ⊆ S := by
    intro a ha
    exact (hsource.mem_iff a).mp (List.mem_append_left _ ((hp.mem_iff a).mpr ha))
  have hrU : r ∈ U := by simp [U]
  have ht : IsOrder (U.erase r) t := by
    refine ⟨(List.nodup_cons.mp hnd.1).2, ?_⟩
    have hrt : r ∉ t.toFinset := by
      simpa only [List.mem_toFinset] using (List.nodup_cons.mp hnd.1).1
    simp only [U, List.toFinset_cons, Finset.erase_insert hrt]
  have hrest : IsOrder (S \ U) (cycleSourceWord B) := by
    apply (isOrder_append_left_iff hp Finset.disjoint_sdiff).mp
    rw [Finset.union_sdiff_of_subset hUS]
    exact hsource
  let E : CycleDisplay (S \ U) :=
    { blocks := B
      source_order := hrest
      root_max := fun b hb => D.root_max b (by rw [hB]; exact List.mem_cons_of_mem _ hb)
      roots_desc := by
        have hd := D.roots_desc
        rw [hB, List.pairwise_cons] at hd
        exact hd.2 }
  refine ⟨⟨⟨U, hUS, hrU⟩, ⟨t, ht⟩, E⟩, ?_⟩
  apply CycleDisplay.ext
  exact hB.symm

/-- Remove the cycle containing the largest vertex, retaining the exact cyclic tail. -/
noncomputable def deletionEquiv (S : Finset V) (r : V) (hr : r ∈ S)
    (hmax : ∀ a ∈ S, a ≤ r) : RootData S r ≃ CycleDisplay S :=
  Equiv.ofBijective (assemble S r hmax)
    ⟨assemble_injective S r hmax, assemble_surjective S r hr hmax⟩

@[simp] theorem deletionEquiv_apply (S : Finset V) (r : V) (hr : r ∈ S)
    (hmax : ∀ a ∈ S, a ≤ r) (x : RootData S r) :
    deletionEquiv S r hr hmax x = assemble S r hmax x := rfl

end CycleDisplay

end VerticalStripLLT.CyclicHessenberg
