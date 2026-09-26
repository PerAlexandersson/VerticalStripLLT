import VerticalStripLLT.Circular.FirstBounceOrientationTarget

set_option backward.isDefEq.respectTransparency false

/-! The per-base local identity among the four source configurations. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

namespace Orientation

variable {n : ℕ} {D : Diagram n}

theorem liftedHRV_mono_of_subset (θ θ' : Orientation D) (h : θ.val ⊆ θ'.val) (x : ℤ) :
    θ.liftedHRV x ≤ θ'.liftedHRV x := by
  apply θ'.le_liftedHRV_of_reachable
  refine Relation.ReflTransGen.mono ?_ _ _ (θ.liftedHRV_reachable x)
  rintro a b ⟨ε, hε, ha, hb⟩
  refine ⟨ε, ?_, ha, hb⟩
  rcases Finset.mem_union.mp hε with h' | h'
  · exact Finset.mem_union_left _ h'
  · exact Finset.mem_union_right _ (h h')

end Orientation

namespace Diagram

variable {n : ℕ} (D : Diagram n)

/-- Adding edges along which the HRV potential does not increase changes nothing. -/
theorem orientMono_noop (θ : Orientation D) (Y : Finset (Edge D.area))
    (hYN : Y ⊆ D.edgeData.normalEdges) (hXY : θ.val ⊆ Y)
    (hmono : ∀ ε ∈ Y, ε ∉ θ.val → ∃ x, D.residue x = ε.tail ∧
      θ.liftedHRV (x + ε.length.val) ≤ θ.liftedHRV x) :
    D.orientMono Y = θ.hrvMonomial := by
  have hstep : ∀ x y, D.liftStep Y x y → θ.liftedHRV y ≤ θ.liftedHRV x := by
    rintro x y ⟨ε, hε, hx, hy⟩
    by_cases hθ : ε ∈ D.strict ∪ θ.val
    · exact θ.liftedHRV_le_of_step ⟨ε, hθ, hx, hy⟩
    · have hεY : ε ∈ Y := by
        rcases Finset.mem_union.mp hε with h | h
        · exact absurd (Finset.mem_union_left _ h) hθ
        · exact h
      have hεθ : ε ∉ θ.val := fun h => hθ (Finset.mem_union_right _ h)
      obtain ⟨x0, hx0, hle⟩ := hmono ε hεY hεθ
      obtain ⟨k, hk⟩ := D.residue_eq_exists_period (hx.trans hx0.symm)
      rw [hy, hk, show x0 + n * k + ε.length.val = (x0 + ε.length.val) + n * k by ring,
        θ.liftedHRV_translate, θ.liftedHRV_translate]
      lia
  have hadm := θ.admissible_of_potential Y hstep
  unfold orientMono
  rw [dite_eq_left ⟨hYN, hadm⟩]
  apply θ.hrvMonomial_eq_of_potential
  · rintro x y ⟨ε, hε, hx, hy⟩
    refine Relation.ReflTransGen.single ⟨ε, ?_, hx, hy⟩
    rcases Finset.mem_union.mp hε with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (hXY h)
  · exact hstep

section NN

variable (e : Edge D.area) (he : e ∈ D.strict) (hlen : 2 ≤ e.length.val)
  (hgap : D.area.area (D.area.next e.head) < D.area.area e.head)
  (hsame : D.boundary ((e.tail.val : ℤ) + 1) = D.boundary (e.tail.val : ℤ))
  (hleft : ¬ D.strictAt (e.tail.val : ℤ))
  (hright : ¬ D.strictAt ((e.tail.val : ℤ) + 1))

include he in
theorem nn_e_step (A : Finset (Edge D.area)) (x : ℤ) (hx : D.residue x = e.tail) :
    D.liftStep A x (x + e.length.val) :=
  ⟨e, Finset.mem_union_left _ he, hx, rfl⟩

theorem nn_baseSet_subset_normal : D.baseSet e he hlen ⊆ D.edgeData.normalEdges := by
  intro ε hε
  rw [mem_normalEdges_iff]
  exact ((D.mem_baseSet_iff e he hlen ε).mp hε).1

include hsame hright in
theorem nn_big_subset_normal (θ : Finset (Edge D.area)) (hθ : θ ⊆ D.baseSet e he hlen) :
    insert (D.shortenedOldEdge e he hlen) (insert (D.bridgeEdge e) θ) ⊆
      D.edgeData.normalEdges := by
  have h0 := (hθ.trans (D.nn_baseSet_subset_normal e he hlen))
  intro ε hε
  rcases Finset.mem_insert.mp hε with rfl | hε
  · rw [mem_normalEdges_iff]; exact D.nn_fE_not_strict e he hlen
  rcases Finset.mem_insert.mp hε with rfl | hε
  · rw [mem_normalEdges_iff]; exact D.nn_bridge_not_strict e hsame hright
  exact h0 hε

/-- Case I key inequality: the shortened edge keeps the successor below the tail. -/
theorem nn_caseI_key (θ0 θ1 : Orientation D) (hsub : θ0.val ⊆ θ1.val)
    (hval : ∀ ε ∈ θ1.val, ε ∉ θ0.val → ε = D.shortenedOldEdge e he hlen)
    (hc : θ0.liftedHRV ((e.tail.val : ℤ) + 1) ≤ θ0.liftedHRV (e.tail.val : ℤ)) :
    θ1.liftedHRV ((e.tail.val : ℤ) + 1) ≤ θ1.liftedHRV (e.tail.val : ℤ) := by
  have hw := θ1.liftedHRV_reachable ((e.tail.val : ℤ) + 1)
  rcases reflTransGen_firstUse (R := D.liftStep θ0.val)
      (F := fun x y => D.residue x = (D.shortenedOldEdge e he hlen).tail ∧
        y = x + (D.shortenedOldEdge e he hlen).length.val) (fun x y h => by
        rcases h with ⟨ε, hε, hx, hy⟩
        by_cases h0 : ε ∈ D.strict ∪ θ0.val
        · exact Or.inl ⟨ε, h0, hx, hy⟩
        · right
          have hεθ1 : ε ∈ θ1.val := by
            rcases Finset.mem_union.mp hε with h | h
            · exact absurd (Finset.mem_union_left _ h) h0
            · exact h
          have := hval ε hεθ1 (fun h => h0 (Finset.mem_union_right _ h))
          subst this
          exact ⟨hx, hy⟩) hw with h | ⟨c, c', h1, ⟨hc1, hc2⟩, h3⟩
  · calc θ1.liftedHRV ((e.tail.val : ℤ) + 1) ≤ θ0.liftedHRV ((e.tail.val : ℤ) + 1) :=
          θ0.le_liftedHRV_of_reachable h
      _ ≤ θ0.liftedHRV (e.tail.val : ℤ) := hc
      _ ≤ θ1.liftedHRV (e.tail.val : ℤ) := θ0.liftedHRV_mono_of_subset θ1 hsub _
  · have hcP : c = (e.tail.val : ℤ) + 1 := by
      rcases Relation.reflTransGen_iff_eq_or_transGen.mp h1 with h | h
      · exact h
      · exfalso
        apply θ0.no_lifted_cycle h
        rw [hc1, D.nn_fE_tail e he hlen]
    rw [hc2, hcP, D.nn_fE_length e he hlen,
      show (e.tail.val : ℤ) + 1 + ((e.length.val : ℤ) - 1) =
        (e.tail.val : ℤ) + e.length.val by ring] at h3
    calc θ1.liftedHRV ((e.tail.val : ℤ) + 1) ≤
          θ1.liftedHRV ((e.tail.val : ℤ) + e.length.val) :=
          θ1.le_liftedHRV_of_reachable h3
      _ ≤ θ1.liftedHRV (e.tail.val : ℤ) :=
          θ1.liftedHRV_le_of_step (D.nn_e_step e he _ _ (D.nn_residue_P e))

include he hsame in
/-- Case II key inequality: adding the bridge does not raise the top vertex. -/
theorem nn_caseII_key (θ0 θ2 : Orientation D)
    (hval : ∀ ε ∈ θ2.val, ε ∉ θ0.val → ε = D.bridgeEdge e) :
    θ2.liftedHRV ((e.tail.val : ℤ) + e.length.val) ≤
      θ0.liftedHRV ((e.tail.val : ℤ) + e.length.val) := by
  have hw := θ2.liftedHRV_reachable ((e.tail.val : ℤ) + e.length.val)
  rcases reflTransGen_firstUse (R := D.liftStep θ0.val)
      (F := fun x y => D.residue x = (D.bridgeEdge e).tail ∧
        y = x + (D.bridgeEdge e).length.val) (fun x y h => by
        rcases h with ⟨ε, hε, hx, hy⟩
        by_cases h0 : ε ∈ D.strict ∪ θ0.val
        · exact Or.inl ⟨ε, h0, hx, hy⟩
        · right
          have hεθ2 : ε ∈ θ2.val := by
            rcases Finset.mem_union.mp hε with h | h
            · exact absurd (Finset.mem_union_left _ h) h0
            · exact h
          have := hval ε hεθ2 (fun h => h0 (Finset.mem_union_right _ h))
          subst this
          exact ⟨hx, hy⟩) hw with h | ⟨c, c', h1, ⟨hc1, _⟩, _⟩
  · exact θ0.le_liftedHRV_of_reachable h
  · exfalso
    rw [D.nn_bridge_tail e hsame, nn_residue_P] at hc1
    have hstep := D.nn_e_step e he θ0.val c hc1
    apply θ0.no_lifted_cycle (Relation.TransGen.tail' h1 hstep)
    rw [nn_residue_T, D.residue_add_length e c hc1]

include hsame hright in
/-- The local identity among the four source configurations over a fixed base. -/
theorem nn_local_identity (θ : Finset (Edge D.area)) (hθ : θ ⊆ D.baseSet e he hlen) :
    D.orientMono (insert (D.bridgeEdge e) θ) +
      D.orientMono (insert (D.shortenedOldEdge e he hlen) θ) =
      D.orientMono θ + D.orientMono (insert (D.shortenedOldEdge e he hlen)
        (insert (D.bridgeEdge e) θ)) := by
  have hN11 := D.nn_big_subset_normal e he hlen hsame hright θ hθ
  have hN01 : insert (D.bridgeEdge e) θ ⊆ D.edgeData.normalEdges :=
    (Finset.subset_insert _ _).trans hN11
  have hN00 : θ ⊆ D.edgeData.normalEdges := (Finset.subset_insert _ _).trans hN01
  have hN10 : insert (D.shortenedOldEdge e he hlen) θ ⊆ D.edgeData.normalEdges :=
    (Finset.insert_subset_insert _ (Finset.subset_insert _ _)).trans hN11
  have hfθ : D.shortenedOldEdge e he hlen ∉ θ := fun h =>
    ((D.mem_baseSet_iff e he hlen _).mp (hθ h)).2.1 rfl
  have hgθ : D.bridgeEdge e ∉ θ := fun h =>
    ((D.mem_baseSet_iff e he hlen _).mp (hθ h)).2.2 rfl
  by_cases h0 : D.edgeData.Admissible θ
  swap
  · have hz : ∀ A, θ ⊆ A → D.orientMono A = 0 := fun A hA =>
      D.orientMono_of_not_adm (fun h => h0 (D.admissible_mono hA h))
    rw [hz _ (Finset.subset_insert _ _), hz _ (Finset.subset_insert _ _),
      hz _ (Finset.Subset.refl _),
      hz _ ((Finset.subset_insert _ _).trans (Finset.subset_insert _ _))]
  let θ0 : Orientation D := ⟨θ, hN00, h0⟩
  have hθ0 : D.orientMono θ = θ0.hrvMonomial := D.orientMono_orientation θ0
  have heP : θ0.liftedHRV ((e.tail.val : ℤ) + e.length.val) ≤ θ0.liftedHRV (e.tail.val : ℤ) :=
    θ0.liftedHRV_le_of_step (D.nn_e_step e he _ _ (D.nn_residue_P e))
  have hbl := D.nn_bridge_length e hsame
  have hbt := D.nn_bridge_tail e hsame
  have hft := D.nn_fE_tail e he hlen
  have hfl := D.nn_fE_length e he hlen
  have hcomm : insert (D.shortenedOldEdge e he hlen) (insert (D.bridgeEdge e) θ) =
      insert (D.bridgeEdge e) (insert (D.shortenedOldEdge e he hlen) θ) :=
    Finset.insert_comm _ _ _
  by_cases hc : θ0.liftedHRV ((e.tail.val : ℤ) + 1) ≤ θ0.liftedHRV (e.tail.val : ℤ)
  · -- Case I
    have hg : D.orientMono (insert (D.bridgeEdge e) θ) = θ0.hrvMonomial := by
      apply D.orientMono_noop θ0 _ hN01 (Finset.subset_insert _ _)
      intro ε hε hεθ
      rcases Finset.mem_insert.mp hε with rfl | h
      · exact ⟨(e.tail.val : ℤ), hbt.symm, by rw [hbl]; exact hc⟩
      · exact absurd h hεθ
    have hf : D.orientMono (insert (D.shortenedOldEdge e he hlen) θ) =
        D.orientMono (insert (D.shortenedOldEdge e he hlen) (insert (D.bridgeEdge e) θ)) := by
      by_cases h1 : D.edgeData.Admissible (insert (D.shortenedOldEdge e he hlen) θ)
      · let θ1 : Orientation D := ⟨_, hN10, h1⟩
        rw [D.orientMono_orientation θ1, hcomm]
        symm
        apply D.orientMono_noop θ1 _ (hcomm ▸ hN11) (Finset.subset_insert _ _)
        intro ε hε hεθ
        rcases Finset.mem_insert.mp hε with rfl | h
        · refine ⟨(e.tail.val : ℤ), hbt.symm, ?_⟩
          rw [hbl]
          apply D.nn_caseI_key e he hlen θ0 θ1 (Finset.subset_insert _ _) _ hc
          intro ε hε hεθ
          rcases Finset.mem_insert.mp hε with h | h
          · exact h
          · exact absurd h hεθ
        · exact absurd h hεθ
      · rw [D.orientMono_of_not_adm h1, D.orientMono_of_not_adm
          (fun h => h1 (D.admissible_mono (by rw [hcomm]; exact Finset.subset_insert _ _) h))]
    rw [hg, hf, hθ0, add_comm]
  · -- Case II
    push Not at hc
    have hf : D.orientMono (insert (D.shortenedOldEdge e he hlen) θ) = θ0.hrvMonomial := by
      apply D.orientMono_noop θ0 _ hN10 (Finset.subset_insert _ _)
      intro ε hε hεθ
      rcases Finset.mem_insert.mp hε with rfl | h
      · refine ⟨(e.tail.val : ℤ) + 1, hft.symm, ?_⟩
        rw [hfl, show (e.tail.val : ℤ) + 1 + ((e.length.val : ℤ) - 1) =
          (e.tail.val : ℤ) + e.length.val by ring]
        lia
      · exact absurd h hεθ
    have hg : D.orientMono (insert (D.bridgeEdge e) θ) =
        D.orientMono (insert (D.shortenedOldEdge e he hlen) (insert (D.bridgeEdge e) θ)) := by
      by_cases h2 : D.edgeData.Admissible (insert (D.bridgeEdge e) θ)
      · let θ2 : Orientation D := ⟨_, hN01, h2⟩
        rw [D.orientMono_orientation θ2]
        symm
        apply D.orientMono_noop θ2 _ hN11 (Finset.subset_insert _ _)
        intro ε hε hεθ
        rcases Finset.mem_insert.mp hε with rfl | h
        · refine ⟨(e.tail.val : ℤ) + 1, hft.symm, ?_⟩
          rw [hfl, show (e.tail.val : ℤ) + 1 + ((e.length.val : ℤ) - 1) =
            (e.tail.val : ℤ) + e.length.val by ring]
          have k2 := D.nn_caseII_key e he hsame θ0 θ2 (by
            intro ε hε hεθ
            rcases Finset.mem_insert.mp hε with h | h
            · exact h
            · exact absurd h hεθ)
          have k3 := θ0.liftedHRV_mono_of_subset θ2 (Finset.subset_insert _ _)
            ((e.tail.val : ℤ) + 1)
          lia
        · exact absurd h hεθ
      · rw [D.orientMono_of_not_adm h2, D.orientMono_of_not_adm
          (fun h => h2 (D.admissible_mono (Finset.subset_insert _ _) h))]
    rw [hg, hf, hθ0, add_comm]

end NN

end Diagram

end VerticalStripLLT.Circular

