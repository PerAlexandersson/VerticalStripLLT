import VerticalStripLLT.Circular.FirstBounceOrientationIdentity

set_option backward.isDefEq.respectTransparency false

/-! Matching source configurations with target configurations. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

namespace Diagram

variable {n : ℕ} (D : Diagram n)

section NN

variable (e : Edge D.area) (he : e ∈ D.strict) (hlen : 2 ≤ e.length.val)
  (hgap : D.area.area (D.area.next e.head) < D.area.area e.head)
  (hsame : D.boundary ((e.tail.val : ℤ) + 1) = D.boundary (e.tail.val : ℤ))
  (hleft : ¬ D.strictAt (e.tail.val : ℤ))
  (hright : ¬ D.strictAt ((e.tail.val : ℤ) + 1))

include hsame hright in
/-- Both local normal edges chosen: equal reachability with the target configuration. -/
theorem nn_match_top (θ : Finset (Edge D.area)) (hθ : θ ⊆ D.baseSet e he hlen) :
    D.orientMono (insert (D.shortenedOldEdge e he hlen) (insert (D.bridgeEdge e) θ)) =
      (D.shortenStrict e he hlen hgap).orientMono
        (D.targetSet e he hlen hgap (insert (D.bridgeEdge e) θ)) := by
  set D' := D.shortenStrict e he hlen hgap
  set f := D.shortenedOldEdge e he hlen
  set g := D.bridgeEdge e
  have hAsub : insert g θ ⊆ insert g (D.baseSet e he hlen) := Finset.insert_subset_insert _ hθ
  have hAe : e ∉ insert g θ := D.nn_ne_e_of_mem e he hlen _ hAsub hsame hright
  have hY := D.nn_big_subset_normal e he hlen hsame hright θ hθ
  have hZ := D.nn_targetSet_subset e he hlen hgap hsame hright _ hAsub
  have hZY : ∀ x y, D'.liftStep (D.targetSet e he hlen hgap (insert g θ)) x y →
      D.liftStep (insert f (insert g θ)) x y := by
    intro x y h
    obtain ⟨ε, hε, hx, hy⟩ := (D.nn_liftStep_target e he hlen hgap _ hAe x y).mp h
    refine ⟨ε, ?_, hx, hy⟩
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase] at hε ⊢
    tauto
  have hYZ : ∀ x y, D.liftStep (insert f (insert g θ)) x y →
      D'.liftStep (D.targetSet e he hlen hgap (insert g θ)) x y ∨
        (D.residue x = e.tail ∧ y = x + e.length.val) := by
    rintro x y ⟨ε, hε, hx, hy⟩
    by_cases hee : ε = e
    · subst hee; exact Or.inr ⟨hx, hy⟩
    · left
      apply (D.nn_liftStep_target e he hlen hgap _ hAe x y).mpr
      refine ⟨ε, ?_, hx, hy⟩
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase] at hε ⊢
      tauto
  have hreach : ∀ x, D.residue x = e.tail →
      Relation.ReflTransGen (D'.liftStep (D.targetSet e he hlen hgap (insert g θ)))
        x (x + e.length.val) := by
    intro x hx
    have hx' : D.residue x = D.residue (e.tail.val : ℤ) := hx.trans (D.nn_residue_P e).symm
    have s1 : D'.liftStep (D.targetSet e he hlen hgap (insert g θ)) x (x + 1) := by
      apply (D.nn_liftStep_target e he hlen hgap _ hAe x _).mpr
      refine ⟨g, Finset.mem_union_right _ (Finset.mem_insert_self _ _), ?_, ?_⟩
      · rw [D.nn_bridge_tail e hsame]; exact hx'
      · rw [D.nn_bridge_length e hsame]
    have s2 : D'.liftStep (D.targetSet e he hlen hgap (insert g θ)) (x + 1)
        (x + e.length.val) := by
      apply (D.nn_liftStep_target e he hlen hgap _ hAe _ _).mpr
      refine ⟨f, Finset.mem_union_left _ (Finset.mem_insert_self _ _), ?_, ?_⟩
      · rw [D.nn_fE_tail e he hlen, D.residue_succ, D.residue_succ, hx']
      · rw [D.nn_fE_length e he hlen]; ring
    exact (Relation.ReflTransGen.single s1).tail s2
  apply D.orientMono_eq_of _ _ hY hZ
  · intro h
    let θY : Orientation D := ⟨_, hY, h⟩
    have hZadm : D'.edgeData.Admissible (D.targetSet e he hlen hgap (insert g θ)) :=
      θY.admissible_of_potential _ (fun x y hs => θY.liftedHRV_le_of_step (hZY x y hs))
    refine ⟨hZadm, fun h' => ?_⟩
    let η : Orientation D' := ⟨_, hZ, h'⟩
    symm
    apply η.hrvMonomial_eq_of_potential θY
    · intro x y hs
      exact Relation.ReflTransGen.single (hZY x y hs)
    · intro x y hs
      rcases hYZ x y hs with hz | ⟨hx, hy⟩
      · exact η.liftedHRV_le_of_step hz
      · rw [hy]; exact η.liftedHRV_le_of_reach (hreach x hx)
  · intro h'
    let η : Orientation D' := ⟨_, hZ, h'⟩
    apply η.admissible_of_potential
    intro x y hs
    rcases hYZ x y hs with hz | ⟨hx, hy⟩
    · exact η.liftedHRV_le_of_step hz
    · rw [hy]; exact η.liftedHRV_le_of_reach (hreach x hx)

include hgap hsame hleft hright in
/-- Swap conjugacy between the source configuration without local edges and the target. -/
theorem nn_swap_step (θ : Finset (Edge D.area)) (hθ : θ ⊆ D.baseSet e he hlen) (x y : ℤ) :
    D.liftStep θ x y ↔ (D.shortenStrict e he hlen hgap).liftStep
      (D.targetSet e he hlen hgap (D.swapSet e θ))
      (periodicSwap n (e.tail.val : ℤ) x) (periodicSwap n (e.tail.val : ℤ) y) := by
  have hA := D.nn_swapSet_subset e he hlen hgap hsame hleft hright θ hθ
  have hAe : e ∉ D.swapSet e θ := fun h => ((D.mem_baseSet_iff e he hlen e).mp (hA h)).1 he
  have hi := periodicSwap_involutive n (e.tail.val : ℤ) (D.nn_two_le e hlen)
  have hb : ∀ ε, ε ∈ D.strict ∪ θ → ε ≠ D.bridgeEdge e := by
    intro ε hε hεb
    rcases Finset.mem_union.mp hε with h | h
    · exact D.nn_bridge_not_strict e hsame hright (hεb ▸ h)
    · exact ((D.mem_baseSet_iff e he hlen ε).mp (hθ h)).2.2 hεb
  have hb' : ∀ ε, ε ∈ insert (D.shortenedOldEdge e he hlen) (D.strict.erase e) ∪
      D.swapSet e θ → ε ≠ D.bridgeEdge e := by
    intro ε hε hεb
    rcases Finset.mem_union.mp hε with h | h
    · rcases Finset.mem_insert.mp h with h | h
      · exact D.nn_fE_ne_bridge e he hlen hsame (h ▸ hεb)
      · exact D.nn_bridge_not_strict e hsame hright (hεb ▸ (Finset.mem_erase.mp h).2)
    · exact ((D.mem_baseSet_iff e he hlen ε).mp (hA h)).2.2 hεb
  rw [D.nn_liftStep_target e he hlen hgap _ hAe]
  constructor
  · rintro ⟨ε, hε, hx, hy⟩
    have hnl := D.nn_swapEdge_naturalLift e he hlen hgap hsame ε (hb ε hε) ⟨hx, hy⟩
    refine ⟨_, ?_, hnl.1, hnl.2⟩
    by_cases hee : ε = e
    · rw [hee, D.nn_swapEdge_e e he hlen hgap hsame hright]
      simp
    · rcases Finset.mem_union.mp hε with h | h
      · rw [D.nn_swapEdge_fix e he hlen hgap hsame hleft hright ε h hee]
        exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hee, h⟩))
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)
  · rintro ⟨ε, hε, hx, hy⟩
    have hnl := D.nn_swapEdge_naturalLift e he hlen hgap hsame ε (hb' ε hε) ⟨hx, hy⟩
    rw [hi, hi] at hnl
    refine ⟨_, ?_, hnl.1, hnl.2⟩
    rcases Finset.mem_union.mp hε with h | h
    · rcases Finset.mem_insert.mp h with h | h
      · rw [h, ← D.nn_swapEdge_e e he hlen hgap hsame hright,
          D.nn_swapEdge_swapEdge e he hlen hgap hsame e (D.nn_e_ne_bridge e he hsame hright)]
        exact Finset.mem_union_left _ he
      · obtain ⟨hne, hs⟩ := Finset.mem_erase.mp h
        rw [D.nn_swapEdge_fix e he hlen hgap hsame hleft hright ε hs hne]
        exact Finset.mem_union_left _ hs
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
      rw [D.nn_swapEdge_swapEdge e he hlen hgap hsame a (hb a (Finset.mem_union_right _ ha))]
      exact Finset.mem_union_right _ ha

include hgap hsame hleft hright in
/-- No local edges chosen: periodic swap conjugacy with the target configuration. -/
theorem nn_match_bottom (θ : Finset (Edge D.area)) (hθ : θ ⊆ D.baseSet e he hlen) :
    D.orientMono θ = (D.shortenStrict e he hlen hgap).orientMono
      (D.targetSet e he hlen hgap (D.swapSet e θ)) := by
  set D' := D.shortenStrict e he hlen hgap
  have hA := D.nn_swapSet_subset e he hlen hgap hsame hleft hright θ hθ
  have hAsub : D.swapSet e θ ⊆ insert (D.bridgeEdge e) (D.baseSet e he hlen) :=
    hA.trans (Finset.subset_insert _ _)
  have hZ := D.nn_targetSet_subset e he hlen hgap hsame hright _ hAsub
  have hθN : θ ⊆ D.edgeData.normalEdges := hθ.trans (D.nn_baseSet_subset_normal e he hlen)
  have hstep := D.nn_swap_step e he hlen hgap hsame hleft hright θ hθ
  have hn2 := D.nn_two_le e hlen
  have hn2' : 2 ≤ n := by exact_mod_cast hn2
  have hi := periodicSwap_involutive n (e.tail.val : ℤ) hn2
  have hres : ∀ z w, D.residue z = D.residue w →
      D.residue (periodicSwap n (e.tail.val : ℤ) z) =
        D.residue (periodicSwap n (e.tail.val : ℤ) w) := by
    intro z w h
    rw [D.residue_periodicSwap hn2', D.residue_periodicSwap hn2', h]
  apply D.orientMono_eq_of _ _ hθN hZ
  · intro h
    have hZadm : D'.edgeData.Admissible (D.targetSet e he hlen hgap (D.swapSet e θ)) := by
      rw [D'.admissible_iff_lift]
      intro z w hzw hzw'
      have hc : Relation.TransGen (D.liftStep θ) (periodicSwap n (e.tail.val : ℤ) z)
          (periodicSwap n (e.tail.val : ℤ) w) := by
        refine Relation.TransGen.lift _ (fun a b hab => ?_) _ _ hzw
        change D.liftStep θ (periodicSwap n (e.tail.val : ℤ) a)
          (periodicSwap n (e.tail.val : ℤ) b)
        rw [hstep, hi, hi]
        exact hab
      exact (D.admissible_iff_lift θ).mp h _ _ hc (hres z w hzw')
    refine ⟨hZadm, fun h' => ?_⟩
    exact Orientation.hrvMonomial_periodicSwap (⟨θ, hθN, h⟩ : Orientation D)
      (⟨_, hZ, h'⟩ : Orientation D') (e.tail.val : ℤ) hn2
      ⟨_, D.nn_e_step e he θ _ (D.nn_residue_P e)⟩ hstep
  · intro h'
    rw [D.admissible_iff_lift]
    intro z w hzw hzw'
    have hc : Relation.TransGen (D'.liftStep (D.targetSet e he hlen hgap (D.swapSet e θ)))
        (periodicSwap n (e.tail.val : ℤ) z) (periodicSwap n (e.tail.val : ℤ) w) :=
      Relation.TransGen.lift _ (fun a b hab => (hstep a b).mp hab) _ _ hzw
    exact (D'.admissible_iff_lift _).mp h' _ _ hc (hres z w hzw')

end NN

end Diagram

end VerticalStripLLT.Circular

