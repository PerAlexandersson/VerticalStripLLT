import VerticalStripLLT.Components.DiagramProof.Certificates
import VerticalStripLLT.Components.DiagramProof.RelationalDiagram

/-!
# Alternating deletion of strict corners

Deleting a set `T` of strict corners keeps every other strict corner maximal and
identifies states by removing the deleted pairs. A strict corner is a maximal
natural interval, so it lies inside no other natural cover test and is never an
exchanged short. Hence every flip of the deletion diagram lifts to the original
diagram, and the image of a whole component is a union of whole components of
the deletion diagram.

If one strict corner is not a cover in a state, it is redundant through a path
inside its interval; deleting it preserves the transitive closure, whatever else
is deleted. Pairing `T` with `T ∪ {s}` makes the alternating deletion sum vanish.
For a whole component with no state in which every strict corner covers, this
expresses the component by whole components of smaller deletion diagrams, with
the same signed coefficients for both marked values.
-/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {n : ℕ} {D : Diagram n} (hD : Forward D)

/-- The strict pairs removed by deleting `T`. -/
def RemovedPair (D : Diagram n) (T : Finset (Fin n × Fin n)) (u v : Fin n) : Prop :=
  (u, v) ∈ T ∧ strictRel D u v

include hD in
theorem ordinaryRelation_delete (T : Finset (Fin n × Fin n)) :
    OrdinaryRelation (fun u v => naturalRel D u v ∧ ¬ RemovedPair D T u v) :=
  (ordinaryRelation_naturalRel hD).removeMaximal _
    (fun _ _ h => maximalPair_of_strictRel hD h.2)

/-- Delete the strict pairs in `T`. -/
def deleteStrict (T : Finset (Fin n × Fin n)) : Diagram n :=
  ofRelations (fun u v => naturalRel D u v ∧ ¬ RemovedPair D T u v)
    (fun u v => strictRel D u v ∧ (u, v) ∉ T) (ordinaryRelation_delete hD T)
    (fun _ _ h => (maximalPair_of_strictRel hD h.1).of_le (fun _ _ h' => h'.1)
      ⟨naturalRel_of_strictRel h.1, fun h' => h.2 h'.1⟩)
    D.area.positive

theorem deleteStrict_forward (T : Finset (Fin n × Fin n)) : Forward (deleteStrict hD T) :=
  ofRelations_forward _ _ _ _ _

theorem deleteStrict_naturalRel (T : Finset (Fin n × Fin n)) (u v : Fin n) :
    naturalRel (deleteStrict hD T) u v ↔ naturalRel D u v ∧ ¬ RemovedPair D T u v :=
  ofRelations_naturalRel ..

theorem deleteStrict_strictRel (T : Finset (Fin n × Fin n)) (u v : Fin n) :
    strictRel (deleteStrict hD T) u v ↔ strictRel D u v ∧ (u, v) ∉ T :=
  ofRelations_strictRel ..

/-- Remove the deleted strict pairs from a state. -/
def deleteState (T : Finset (Fin n × Fin n)) (θ : Orientation D) :
    Orientation (deleteStrict hD T) :=
  ofSelectedRelation (deleteStrict_forward hD T)
    (fun u v => D.edgeData.selected θ.val u v ∧ ¬ RemovedPair D T u v)
    (fun u v h => (deleteStrict_naturalRel hD T u v).mpr ⟨naturalRel_of_selected h.1, h.2⟩)
    (by
      intro e he
      obtain ⟨hs, hT⟩ := (deleteStrict_strictRel hD T e.tail e.head).mp ⟨e, he, rfl, rfl⟩
      exact ⟨selected_of_strictRel θ hs, fun h => hT h.1⟩)

@[simp]
theorem deleteState_selected (T : Finset (Fin n × Fin n)) (θ : Orientation D) (u v : Fin n) :
    (deleteStrict hD T).edgeData.selected (deleteState hD T θ).val u v ↔
      D.edgeData.selected θ.val u v ∧ ¬ RemovedPair D T u v :=
  selected_ofSelectedRelation ..

include hD in
/-- No deleted pair lies inside a surviving natural pair, except as that pair. -/
theorem not_removed_of_le {T : Finset (Fin n × Fin n)} {a c x y : Fin n}
    (hac : naturalRel D a c) (hacT : ¬ RemovedPair D T a c) (hax : a ≤ x) (hyc : y ≤ c) :
    ¬ RemovedPair D T x y := by
  rintro ⟨hT, hs⟩
  obtain ⟨rfl, rfl⟩ := strictRel_maximal hD hs hac hax hyc
  exact hacT ⟨hT, hs⟩

/-- Cover tests of a surviving natural pair are unchanged by deletion. -/
theorem cover_deleteState_iff (T : Finset (Fin n × Fin n)) (θ : Orientation D)
    {a c : Fin n} (hac : naturalRel D a c) (hacT : ¬ RemovedPair D T a c) :
    Cover (deleteState hD T θ) a c ↔ Cover θ a c := by
  have hfwd : ∀ ⦃u v⦄, D.edgeData.selected θ.val u v → u < v :=
    fun _ _ h => θ.selected_lt_of_forward hD h
  have hfwd' : ∀ ⦃u v⦄,
      (deleteStrict hD T).edgeData.selected (deleteState hD T θ).val u v → u < v :=
    fun _ _ h => (deleteState hD T θ).selected_lt_of_forward (deleteStrict_forward hD T) h
  have down : ∀ x y, Relation.ReflTransGen
      ((deleteStrict hD T).edgeData.selected (deleteState hD T θ).val) x y →
      Relation.ReflTransGen (D.edgeData.selected θ.val) x y := fun x y h =>
    Relation.ReflTransGen.mono (fun _ _ h' => ((deleteState_selected hD T θ _ _).mp h').1) _ _ h
  have up : ∀ x y, a ≤ x → y ≤ c → Relation.ReflTransGen (D.edgeData.selected θ.val) x y →
      Relation.ReflTransGen
        ((deleteStrict hD T).edgeData.selected (deleteState hD T θ).val) x y := by
    intro x y hx hy h
    apply reachable_mono_on_interval hfwd (lo := a) (hi := c) _ h hx hy
    intro u v hu hv huv
    exact (deleteState_selected hD T θ u v).mpr
      ⟨huv, not_removed_of_le hD hac hacT hu hv⟩
  constructor
  · rintro ⟨hlt, hreach, hno⟩
    refine ⟨hlt, down _ _ hreach, ?_⟩
    rintro w haw hwc ⟨h1, h2⟩
    exact hno w haw hwc ⟨up _ _ le_rfl hwc.le h1, up _ _ haw.le le_rfl h2⟩
  · rintro ⟨hlt, hreach, hno⟩
    refine ⟨hlt, up _ _ le_rfl le_rfl hreach, ?_⟩
    rintro w haw hwc ⟨h1, h2⟩
    exact hno w haw hwc ⟨down _ _ h1, down _ _ h2⟩

/-- The state with prescribed surviving relation and all deleted pairs restored. -/
theorem exists_restore (T : Finset (Fin n × Fin n))
    (η' : Orientation (deleteStrict hD T)) :
    ∃ η : Orientation D, deleteState hD T η = η' := by
  obtain ⟨η, hη⟩ := exists_orientation_of_relation hD
    (fun u v => (deleteStrict hD T).edgeData.selected η'.val u v ∨ RemovedPair D T u v)
    (by
      rintro u v (h | h)
      · exact ((deleteStrict_naturalRel hD T u v).mp (naturalRel_of_selected h)).1
      · exact naturalRel_of_strictRel h.2)
    (by
      intro u v hs
      by_cases hT : (u, v) ∈ T
      · exact Or.inr ⟨hT, hs⟩
      · exact Or.inl (selected_of_strictRel η'
          ((deleteStrict_strictRel hD T u v).mpr ⟨hs, hT⟩)))
  refine ⟨η, orientation_eq_of_selected_iff fun u v => ?_⟩
  rw [deleteState_selected, hη]
  constructor
  · rintro ⟨h | h, hr⟩
    · exact h
    · exact (hr h).elim
  · intro h
    exact ⟨Or.inl h, ((deleteStrict_naturalRel hD T u v).mp (naturalRel_of_selected h)).2⟩

theorem deleteState_injective (T : Finset (Fin n × Fin n)) :
    Function.Injective (deleteState hD T) := by
  intro θ η h
  apply orientation_eq_of_selected_iff
  intro u v
  by_cases hr : RemovedPair D T u v
  · exact iff_of_true (selected_of_strictRel θ hr.2) (selected_of_strictRel η hr.2)
  · have hθ := deleteState_selected hD T θ u v
    rw [h, deleteState_selected] at hθ
    simpa only [hr, not_false_eq_true, and_true] using hθ.symm

/-- A forward flip of the deletion diagram lifts to the original diagram. -/
theorem lift_directedFlip (T : Finset (Fin n × Fin n)) {θ : Orientation D}
    {η' : Orientation (deleteStrict hD T)}
    (hf : DirectedFlip (deleteStrict hD T) (deleteState hD T θ) η') :
    ∃ η : Orientation D, DirectedFlip D θ η ∧ deleteState hD T η = η' := by
  obtain ⟨a, b, c, hbc, hab, hac, hη'⟩ :=
    (directedFlip_iff (deleteStrict_forward hD T) _ _).mp hf
  have hnat (x y : Fin n) (h : (deleteStrict hD T).edgeData.selected (deleteState hD T θ).val x y) :
      naturalRel D x y ∧ ¬ RemovedPair D T x y :=
    (deleteStrict_naturalRel hD T x y).mp (naturalRel_of_selected h)
  have hab' := (cover_deleteState_iff hD T θ (hnat a b (selected_of_cover
    (deleteStrict_forward hD T) hab)).1 (hnat a b (selected_of_cover
    (deleteStrict_forward hD T) hab)).2).mp hab
  have hacN := hnat a c (selected_of_cover (deleteStrict_forward hD T) hac)
  have hac' := (cover_deleteState_iff hD T θ hacN.1 hacN.2).mp hac
  obtain ⟨η, w, hat, hah, -, hch⟩ := exists_directedFlip_of_sourceCovers hD θ a b c hab' hac' hbc
  refine ⟨η, ⟨w⟩, orientation_eq_of_selected_iff fun u v => ?_⟩
  rw [deleteState_selected, target_selected_iff w, hat, hah, hch, hη']
  simp only [swapRel, deleteState_selected]
  have hbcT : ¬ RemovedPair D T b c := not_removed_of_le hD hacN.1 hacN.2 hab'.1.le le_rfl
  constructor
  · rintro ⟨⟨rfl, rfl⟩ | ⟨hs, hne⟩, hr⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨⟨hs, hr⟩, hne⟩
  · rintro (⟨rfl, rfl⟩ | ⟨⟨hs, hr⟩, hne⟩)
    · exact ⟨Or.inl ⟨rfl, rfl⟩, hbcT⟩
    · exact ⟨Or.inr ⟨hs, hne⟩, hr⟩

/-- A backward flip of the deletion diagram lifts to the original diagram. -/
theorem lift_directedFlip_rev (T : Finset (Fin n × Fin n)) {θ : Orientation D}
    {η' : Orientation (deleteStrict hD T)}
    (hf : DirectedFlip (deleteStrict hD T) η' (deleteState hD T θ)) :
    ∃ η : Orientation D, DirectedFlip D η θ ∧ deleteState hD T η = η' := by
  obtain ⟨η, rfl⟩ := exists_restore hD T η'
  obtain ⟨ζ, hζ, hζη⟩ := lift_directedFlip hD T hf
  rw [deleteState_injective hD T hζη] at hζ
  exact ⟨η, hζ, rfl⟩

/-- Every state reachable in the deletion diagram is the image of a reachable state. -/
theorem lift_reachable (T : Finset (Fin n × Fin n)) {θ : Orientation D}
    {η' : Orientation (deleteStrict hD T)}
    (hp : Relation.ReflTransGen (Flip (deleteStrict hD T)) (deleteState hD T θ) η') :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧ deleteState hD T η = η' := by
  induction hp with
  | refl => exact ⟨θ, Relation.ReflTransGen.refl, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨ζ, hp, rfl⟩ := ih
    rcases hstep with hstep | hstep
    · obtain ⟨η, h1, h2⟩ := lift_directedFlip hD T hstep
      exact ⟨η, hp.tail (Or.inl h1), h2⟩
    · obtain ⟨η, h1, h2⟩ := lift_directedFlip_rev hD T hstep
      exact ⟨η, hp.tail (Or.inr h1), h2⟩

/-- The deletion image of a whole component is flip-closed. -/
theorem deleteImage_closed (T : Finset (Fin n × Fin n)) (θ : Orientation D) :
    ∀ η' ∈ (flipComponent D θ).image (deleteState hD T),
      flipComponent (deleteStrict hD T) η' ⊆ (flipComponent D θ).image (deleteState hD T) := by
  intro η' hη' ζ' hζ'
  obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp hη'
  obtain ⟨ζ, hp, rfl⟩ := lift_reachable hD T (mem_flipComponent_iff.mp hζ')
  exact Finset.mem_image.mpr ⟨ζ, mem_flipComponent_iff.mpr
    ((mem_flipComponent_iff.mp hη).trans hp), rfl⟩

/-- Relations with mutually bounded transitive closures have the same closure. -/
theorem transGen_eq_of_le_transGen {α : Type*} {R S : α → α → Prop}
    (h₁ : ∀ a b, R a b → Relation.TransGen S a b) (h₂ : ∀ a b, S a b → Relation.TransGen R a b) :
    Relation.TransGen R = Relation.TransGen S := by
  funext a b
  apply propext
  constructor
  · intro hab
    induction hab with
    | single hr => exact h₁ _ _ hr
    | tail _ hr ih => exact ih.trans (h₁ _ _ hr)
  · intro hab
    induction hab with
    | single hr => exact h₂ _ _ hr
    | tail _ hr ih => exact ih.trans (h₂ _ _ hr)

/-- A relation between `S` and the transitive closure of `S` has the same closure. -/
theorem transGen_eq_of_le_of_le_transGen {α : Type*} {R S : α → α → Prop}
    (h₁ : ∀ x y, S x y → R x y) (h₂ : ∀ x y, R x y → Relation.TransGen S x y) :
    Relation.TransGen R = Relation.TransGen S :=
  transGen_eq_of_le_transGen h₂ fun a b h => Relation.TransGen.single (h₁ a b h)

/-! ### The alternating sum at one state -/

/-- Deleting a selected non-covering strict corner preserves the transitive closure. -/
theorem transGen_delete_insert (T : Finset (Fin n × Fin n)) (θ : Orientation D)
    {s : Fin n × Fin n} (hs : strictRel D s.1 s.2) (hsT : s ∉ T)
    (hnc : ¬ Cover θ s.1 s.2) :
    Relation.TransGen ((deleteStrict hD T).edgeData.selected (deleteState hD T θ).val) =
      Relation.TransGen ((deleteStrict hD (insert s T)).edgeData.selected
        (deleteState hD (insert s T) θ).val) := by
  obtain ⟨a, c⟩ := s
  change strictRel D a c at hs
  change ¬ Cover θ a c at hnc
  have hsel := selected_of_strictRel θ hs
  have hac : a < c := θ.selected_lt_of_forward hD hsel
  -- A non-covering selected pair has an intermediate reachable vertex.
  have hmid : ∃ w, a < w ∧ w < c ∧ Relation.ReflTransGen (D.edgeData.selected θ.val) a w ∧
      Relation.ReflTransGen (D.edgeData.selected θ.val) w c := by
    by_contra hno
    push Not at hno
    exact hnc ⟨hac, Relation.ReflTransGen.single hsel, fun w h1 h2 h => hno w h1 h2 h.1 h.2⟩
  obtain ⟨w, haw, hwc, h1, h2⟩ := hmid
  have hfwd : ∀ ⦃u v⦄, D.edgeData.selected θ.val u v → u < v :=
    fun _ _ h => θ.selected_lt_of_forward hD h
  have hacT : ¬ RemovedPair D T a c := fun h => hsT h.1
  -- The two paths survive every deletion avoiding the pair `ac`.
  have survive : ∀ x y, a ≤ x → y ≤ c → ¬ (x = a ∧ y = c) →
      Relation.ReflTransGen (D.edgeData.selected θ.val) x y →
      Relation.ReflTransGen ((deleteStrict hD (insert (a, c) T)).edgeData.selected
        (deleteState hD (insert (a, c) T) θ).val) x y := by
    intro x y hx hy hne h
    apply reachable_mono_on_interval hfwd (lo := x) (hi := y) _ h le_rfl le_rfl
    intro u v hu hv huv
    apply (deleteState_selected hD _ θ u v).mpr
    refine ⟨huv, ?_⟩
    rintro ⟨-, hstr⟩
    obtain ⟨hua, hvc⟩ := strictRel_maximal hD hstr (naturalRel_of_strictRel hs)
      (hx.trans hu) (hv.trans hy)
    exact hne ⟨le_antisymm (hu.trans_eq hua.symm) hx, le_antisymm hy (hvc ▸ hv)⟩
  have hp := (survive a w le_rfl hwc.le (fun h => hwc.ne h.2) h1).trans
    (survive w c haw.le le_rfl (fun h => haw.ne h.1.symm) h2)
  have hpT : Relation.TransGen ((deleteStrict hD (insert (a, c) T)).edgeData.selected
      (deleteState hD (insert (a, c) T) θ).val) a c :=
    (Relation.reflTransGen_iff_eq_or_transGen.mp hp).resolve_left (fun h => hac.ne h.symm)
  apply transGen_eq_of_le_of_le_transGen
  · intro x y hxy
    obtain ⟨hsel', hr⟩ := (deleteState_selected hD _ θ _ _).mp hxy
    exact (deleteState_selected hD T θ _ _).mpr
      ⟨hsel', fun h' => hr ⟨Finset.mem_insert_of_mem h'.1, h'.2⟩⟩
  · intro x y hxy
    obtain ⟨hsel', hr⟩ := (deleteState_selected hD T θ _ _).mp hxy
    by_cases hb : x = a ∧ y = c
    · obtain ⟨rfl, rfl⟩ := hb
      exact hpT
    · apply Relation.TransGen.single
      apply (deleteState_selected hD _ θ _ _).mpr
      refine ⟨hsel', ?_⟩
      rintro ⟨hmem, hstr⟩
      rcases Finset.mem_insert.mp hmem with heq | hmem
      · exact hb (Prod.mk.inj heq)
      · exact hr ⟨hmem, hstr⟩

end

end VerticalStripLLT.Circular.DiagramProof
