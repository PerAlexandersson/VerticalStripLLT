import VerticalStripLLT.Components.DiagramProof.Relational.NaturalRelations
import VerticalStripLLT.Components.DiagramProof.Foundation.ShortFlip
import VerticalStripLLT.Components.DiagramProof.Restriction.RestrictedFlips

/-!
# Flips are determined by selected relations

In a forward diagram a directed flip is exactly a short exchange `ab ↦ bc`
under two covers `ab, ac` of the selected relation. The two shorts below a
selected natural long are automatically natural and normal. Hence actual flips
transport between any two forward diagrams on the same vertex set, along a
vertex bijection that is order-preserving inside every selected weak block.

With the identity bijection this gives one statement for absent-corner deletion,
strict marking and unmarking, and envelope normalization. With a blockwise
order-preserving bijection it gives weak-block reordering. In each case the
entire flip component is carried bijectively onto an entire flip component.
-/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {n : ℕ} {D E : Diagram n}

/-- The selected relation after exchanging the short `ab` for `bc`. -/
def swapRel (R : Fin n → Fin n → Prop) (a b c : Fin n) (u v : Fin n) : Prop :=
  (u = b ∧ v = c) ∨ (R u v ∧ ¬ (u = a ∧ v = b))

/-- The target of a directed flip is the source with its two shorts exchanged. -/
theorem target_selected_iff {θ η : Orientation D} (w : DirectedFlipWitness D θ η)
    (u v : Fin n) :
    D.edgeData.selected η.val u v ↔
      swapRel (D.edgeData.selected θ.val) w.eab.tail w.eab.head w.ebc.head u v := by
  rw [w.target_eq_source_swap]
  exact D.selected_short_swap_iff θ.val w.eab w.ebc w.eab_normal
    (a := w.eab.tail) (b := w.eab.head) (c := w.ebc.head) rfl
    (Prod.ext w.short_head_tail.symm rfl) u v

/-- A directed flip of a forward diagram is exactly a cover-supported short exchange. -/
theorem directedFlip_iff (hD : Forward D) (θ η : Orientation D) :
    DirectedFlip D θ η ↔ ∃ a b c : Fin n, b < c ∧ Cover θ a b ∧ Cover θ a c ∧
      ∀ u v, D.edgeData.selected η.val u v ↔
        swapRel (D.edgeData.selected θ.val) a b c u v := by
  constructor
  · rintro ⟨w⟩
    let wn := w.normalizeForward hD
    exact ⟨w.eab.tail, w.eab.head, w.ebc.head, (w.canonical_triple_order hD).2,
      (liftCover_iff_cover hD θ _ _).mp wn.source_ab,
      (liftCover_iff_cover hD θ _ _).mp wn.source_ac, target_selected_iff w⟩
  · rintro ⟨a, b, c, hbc, hab, hac, hη⟩
    obtain ⟨η₀, w, hat, hah, -, hch⟩ :=
      exists_directedFlip_of_sourceCovers hD θ a b c hab hac hbc
    have heq : η₀ = η := orientation_eq_of_selected_iff fun u v => by
      rw [target_selected_iff w, hat, hah, hch, hη]
    exact ⟨heq ▸ w⟩

/-! ### Corresponding states -/

/-- `θ'` in `E` is the image of `θ` in `D` under `π`, which is order-preserving
inside every selected weak block of `θ`. -/
structure Corresponds (π : Equiv.Perm (Fin n)) (θ : Orientation D) (θ' : Orientation E) :
    Prop where
  selected : ∀ u v, E.edgeData.selected θ'.val (π u) (π v) ↔ D.edgeData.selected θ.val u v
  order : ∀ u v, WeakReach θ u v → (u < v ↔ π u < π v)

namespace Corresponds

variable {π : Equiv.Perm (Fin n)} {θ : Orientation D} {θ' : Orientation E}

theorem reachable_iff (h : Corresponds π θ θ') (u v : Fin n) :
    Relation.ReflTransGen (E.edgeData.selected θ'.val) (π u) (π v) ↔
      Relation.ReflTransGen (D.edgeData.selected θ.val) u v := by
  constructor
  · intro hp
    have key : ∀ x y, Relation.ReflTransGen (E.edgeData.selected θ'.val) x y →
        Relation.ReflTransGen (D.edgeData.selected θ.val) (π.symm x) (π.symm y) := by
      intro x y hxy
      apply hxy.lift π.symm
      intro x y hs
      apply (h.selected _ _).mp
      simpa only [Equiv.apply_symm_apply] using hs
    simpa only [Equiv.symm_apply_apply] using key _ _ hp
  · intro hp
    exact hp.lift π (fun x y hs => (h.selected x y).mpr hs)

theorem weakReach_iff (h : Corresponds π θ θ') (u v : Fin n) :
    WeakReach θ' (π u) (π v) ↔ WeakReach θ u v := by
  constructor
  · intro hp
    have key : ∀ x y, WeakReach θ' x y → WeakReach θ (π.symm x) (π.symm y) := by
      intro x y hxy
      induction hxy with
      | rel x y hs =>
        apply Relation.EqvGen.rel
        apply (h.selected _ _).mp
        simpa only [Equiv.apply_symm_apply] using hs
      | refl => exact Relation.EqvGen.refl _
      | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
      | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
    simpa only [Equiv.symm_apply_apply] using key _ _ hp
  · intro hp
    induction hp with
    | rel x y hs => exact Relation.EqvGen.rel _ _ ((h.selected x y).mpr hs)
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem weakReach_of_reachable {u v : Fin n}
    (hp : Relation.ReflTransGen (D.edgeData.selected θ.val) u v) : WeakReach θ u v := by
  induction hp with
  | refl => exact Relation.EqvGen.refl _
  | tail _ hs ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ hs)

/-- Cover tests are preserved: every intermediate vertex of a cover test lies in
the same weak block. -/
theorem cover_iff (h : Corresponds π θ θ') (a c : Fin n) :
    Cover θ' (π a) (π c) ↔ Cover θ a c := by
  constructor
  · rintro ⟨hlt, hreach, hno⟩
    have hreach' := (h.reachable_iff a c).mp hreach
    refine ⟨(h.order a c (weakReach_of_reachable hreach')).mpr hlt, hreach', ?_⟩
    rintro w haw hwc ⟨h1, h2⟩
    apply hno (π w) ((h.order a w (weakReach_of_reachable h1)).mp haw)
      ((h.order w c (weakReach_of_reachable h2)).mp hwc)
    exact ⟨(h.reachable_iff a w).mpr h1, (h.reachable_iff w c).mpr h2⟩
  · rintro ⟨hlt, hreach, hno⟩
    refine ⟨(h.order a c (weakReach_of_reachable hreach)).mp hlt,
      (h.reachable_iff a c).mpr hreach, ?_⟩
    intro w' haw hwc ⟨h1, h2⟩
    obtain ⟨w, rfl⟩ := π.surjective w'
    have h1' := (h.reachable_iff a w).mp h1
    have h2' := (h.reachable_iff w c).mp h2
    exact hno w ((h.order a w (weakReach_of_reachable h1')).mpr haw)
      ((h.order w c (weakReach_of_reachable h2')).mpr hwc) ⟨h1', h2'⟩

/-- A state corresponding to `θ` is unique. -/
theorem unique {θ₁ θ₂ : Orientation E} (h₁ : Corresponds π θ θ₁)
    (h₂ : Corresponds π θ θ₂) :
    θ₁ = θ₂ := by
  apply orientation_eq_of_selected_iff
  intro x y
  obtain ⟨u, rfl⟩ := π.surjective x
  obtain ⟨v, rfl⟩ := π.surjective y
  rw [h₁.selected, h₂.selected]

/-- The inverse correspondence. -/
theorem symm (h : Corresponds π θ θ') : Corresponds π.symm θ' θ where
  selected u v := by
    rw [← h.selected, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  order u v huv := by
    have hw : WeakReach θ (π.symm u) (π.symm v) := by
      rw [← h.weakReach_iff]
      simpa only [Equiv.apply_symm_apply] using huv
    have := h.order _ _ hw
    simp only [Equiv.apply_symm_apply] at this
    exact this.symm

end Corresponds

/-- A forward directed flip transports to the corresponding state. -/
theorem Corresponds.directedFlip (hD : Forward D) (hE : Forward E) {π : Equiv.Perm (Fin n)}
    {θ η : Orientation D} {θ' : Orientation E} (h : Corresponds π θ θ')
    (hf : DirectedFlip D θ η) :
    ∃ η' : Orientation E, DirectedFlip E θ' η' ∧ Corresponds π η η' := by
  obtain ⟨a, b, c, hbc, hab, hac, hη⟩ := (directedFlip_iff hD θ η).mp hf
  have hbc' : π b < π c := by
    apply (h.order b c _).mp hbc
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _
      (Corresponds.weakReach_of_reachable hab.2.1))
      (Corresponds.weakReach_of_reachable hac.2.1)
  obtain ⟨η', w, hat, hah, -, hch⟩ := exists_directedFlip_of_sourceCovers hE θ' (π a) (π b)
    (π c) ((h.cover_iff a b).mpr hab) ((h.cover_iff a c).mpr hac) hbc'
  refine ⟨η', ⟨w⟩, ?_, ?_⟩
  · intro u v
    rw [target_selected_iff w, hat, hah, hch, hη]
    simp only [swapRel, π.injective.eq_iff, h.selected]
  · intro u v huv
    obtain ⟨wf⟩ := hf
    exact h.order u v ((weakReach_iff_of_directedFlip wf u v).mpr huv)

/-- A backward directed flip transports to the corresponding state. -/
theorem Corresponds.directedFlip_rev (hD : Forward D) (hE : Forward E)
    {π : Equiv.Perm (Fin n)} {θ η : Orientation D} {θ' : Orientation E}
    (h : Corresponds π θ θ') (hf : DirectedFlip D η θ) :
    ∃ η' : Orientation E, DirectedFlip E η' θ' ∧ Corresponds π η η' := by
  obtain ⟨a, b, c, hbc, hab, hac, hθ⟩ := (directedFlip_iff hD η θ).mp hf
  have hselab : D.edgeData.selected η.val a b := selected_of_cover hD hab
  have hselac : D.edgeData.selected η.val a c := selected_of_cover hD hac
  have hnotbc : ¬ D.edgeData.selected η.val b c := fun hs =>
    hac.2.2 b hab.1 hbc ⟨hab.2.1, Relation.ReflTransGen.single hs⟩
  have hηsel (u v : Fin n) : D.edgeData.selected η.val u v ↔
      (u = a ∧ v = b) ∨ (D.edgeData.selected θ.val u v ∧ ¬ (u = b ∧ v = c)) := by
    rw [hθ]
    unfold swapRel
    constructor
    · intro hs
      by_cases hu : u = a ∧ v = b
      · exact Or.inl hu
      · refine Or.inr ⟨Or.inr ⟨hs, hu⟩, ?_⟩
        rintro ⟨rfl, rfl⟩
        exact hnotbc hs
    · rintro (⟨rfl, rfl⟩ | ⟨(⟨rfl, rfl⟩ | ⟨hs, -⟩), hne⟩)
      · exact hselab
      · exact (hne ⟨rfl, rfl⟩).elim
      · exact hs
  have hacθ : D.edgeData.selected θ.val a c := by
    rw [hθ]
    exact Or.inr ⟨hselac, fun h' => (ne_of_lt hbc) h'.2.symm⟩
  have hab' : a < b := hab.1
  have hblock : WeakReach θ a c := Relation.EqvGen.rel _ _ hacθ
  have horder (x : Fin n) (hx : WeakReach θ a x) (y : Fin n) (hy : WeakReach θ a y) :
      x < y ↔ π x < π y :=
    h.order x y (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hx) hy)
  have hb : WeakReach θ a b := by
    obtain ⟨wf⟩ := hf
    exact (weakReach_iff_of_directedFlip wf a b).mp (Relation.EqvGen.rel _ _ hselab)
  have hπab : π a < π b := (horder a (Relation.EqvGen.refl _) b hb).mp hab'
  have hπbc : π b < π c := (horder b hb c hblock).mp hbc
  have hnatac : naturalRel E (π a) (π c) := naturalRel_of_selected ((h.selected a c).mpr hacθ)
  obtain ⟨η', hη'⟩ := exists_orientation_of_relation hE
    (fun x y => D.edgeData.selected η.val (π.symm x) (π.symm y))
    (by
      intro x y hxy
      rcases (hηsel _ _).mp hxy with ⟨hx, hy⟩ | ⟨hs, -⟩
      · have hx' : x = π a := by rw [← hx, Equiv.apply_symm_apply]
        have hy' : y = π b := by rw [← hy, Equiv.apply_symm_apply]
        rw [hx', hy']
        exact (naturalRel_interval hE hnatac hπab hπbc).1
      · exact naturalRel_of_selected (by
          simpa only [Equiv.apply_symm_apply] using (h.selected _ _).mpr hs))
    (by
      intro x y hst
      apply (hηsel _ _).mpr
      right
      refine ⟨(h.selected _ _).mp (by
        simpa only [Equiv.apply_symm_apply] using selected_of_strictRel θ' hst), ?_⟩
      rintro ⟨hx, hy⟩
      have hx' : x = π b := by rw [← hx, Equiv.apply_symm_apply]
      have hy' : y = π c := by rw [← hy, Equiv.apply_symm_apply]
      rw [hx', hy'] at hst
      exact not_strictRel_of_lt hE hnatac hπab.le le_rfl (Or.inl hπab) hst)
  have hcorr : Corresponds π η η' := by
    refine ⟨fun u v => by rw [hη', Equiv.symm_apply_apply, Equiv.symm_apply_apply], ?_⟩
    intro u v huv
    obtain ⟨wf⟩ := hf
    exact h.order u v ((weakReach_iff_of_directedFlip wf u v).mp huv)
  obtain ⟨θ'', hflip, hθ''⟩ := hcorr.directedFlip hD hE hf
  rw [Corresponds.unique hθ'' h] at hflip
  exact ⟨η', hflip, hcorr⟩

/-- An actual flip transports to the corresponding state. -/
theorem Corresponds.flip (hD : Forward D) (hE : Forward E) {π : Equiv.Perm (Fin n)}
    {θ η : Orientation D} {θ' : Orientation E} (h : Corresponds π θ θ') (hf : Flip D θ η) :
    ∃ η' : Orientation E, Flip E θ' η' ∧ Corresponds π η η' := by
  rcases hf with hf | hf
  · obtain ⟨η', h1, h2⟩ := h.directedFlip hD hE hf
    exact ⟨η', Or.inl h1, h2⟩
  · obtain ⟨η', h1, h2⟩ := h.directedFlip_rev hD hE hf
    exact ⟨η', Or.inr h1, h2⟩

/-- Actual paths transport to the corresponding states. -/
theorem Corresponds.reachable (hD : Forward D) (hE : Forward E) {π : Equiv.Perm (Fin n)}
    {θ η : Orientation D} {θ' : Orientation E} (h : Corresponds π θ θ')
    (hp : Relation.ReflTransGen (Flip D) θ η) :
    ∃ η' : Orientation E, Relation.ReflTransGen (Flip E) θ' η' ∧ Corresponds π η η' := by
  induction hp with
  | refl => exact ⟨θ', Relation.ReflTransGen.refl, h⟩
  | tail _ hstep ih =>
    obtain ⟨ζ', hp', hζ⟩ := ih
    obtain ⟨η', hf', hη⟩ := hζ.flip hD hE hstep
    exact ⟨η', hp'.tail hf', hη⟩

/-- Whole components correspond bijectively, so any matching values have equal sums. -/
theorem Corresponds.sum_flipComponent (hD : Forward D) (hE : Forward E)
    {π : Equiv.Perm (Fin n)} {θ : Orientation D} {θ' : Orientation E}
    (h : Corresponds π θ θ') {M : Type*} [AddCommMonoid M]
    (f : Orientation D → M) (g : Orientation E → M)
    (hfg : ∀ η η', Corresponds π η η' → f η = g η') :
    ∑ η ∈ flipComponent D θ, f η = ∑ η' ∈ flipComponent E θ', g η' := by
  have hfwd (η : Orientation D) (hη : η ∈ flipComponent D θ) :
      ∃ η' : Orientation E, η' ∈ flipComponent E θ' ∧ Corresponds π η η' := by
    obtain ⟨η', hp, hc⟩ := h.reachable hD hE (mem_flipComponent_iff.mp hη)
    exact ⟨η', mem_flipComponent_iff.mpr hp, hc⟩
  have hbwd (η' : Orientation E) (hη' : η' ∈ flipComponent E θ') :
      ∃ η : Orientation D, η ∈ flipComponent D θ ∧ Corresponds π.symm η' η := by
    obtain ⟨η, hp, hc⟩ := h.symm.reachable hE hD (mem_flipComponent_iff.mp hη')
    exact ⟨η, mem_flipComponent_iff.mpr hp, hc⟩
  refine Finset.sum_bij' (fun η hη => (hfwd η hη).choose)
    (fun η' hη' => (hbwd η' hη').choose)
    ?_ ?_ ?_ ?_ ?_
  · intro η hη
    exact (hfwd η hη).choose_spec.1
  · intro η' hη'
    exact (hbwd η' hη').choose_spec.1
  · intro η hη
    have h₁ := (hfwd η hη).choose_spec
    have h₂ := (hbwd _ h₁.1).choose_spec
    exact Corresponds.unique h₂.2 h₁.2.symm
  · intro η' hη'
    have h₁ := (hbwd η' hη').choose_spec
    have h₂ := (hfwd _ h₁.1).choose_spec
    exact Corresponds.unique h₂.2 (by simpa only [Equiv.symm_symm] using h₁.2.symm)
  · intro η hη
    exact hfg η _ (hfwd η hη).choose_spec.2

/-! ### Equal relations -/

/-- With the identity bijection the order condition is automatic. -/
theorem corresponds_refl {θ : Orientation D} {θ' : Orientation E}
    (h : ∀ u v, E.edgeData.selected θ'.val u v ↔ D.edgeData.selected θ.val u v) :
    Corresponds (Equiv.refl (Fin n)) θ θ' :=
  ⟨h, fun _ _ _ => Iff.rfl⟩

end

end VerticalStripLLT.Circular.DiagramProof
