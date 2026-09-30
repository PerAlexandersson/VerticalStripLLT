import VerticalStripLLT.Components.DiagramProof.ShortPathClasses
import VerticalStripLLT.Components.DiagramProof.HassePaths

/-! Contracting the retained corner chains preserves selected weak components. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hforward : Forward D)

/-- The vertex of the chain quotient containing an original vertex. -/
noncomputable def chainVertex (v : Fin n) : {t : Fin n // F.terminal hforward t = t} :=
  ⟨F.terminal hforward v, F.terminal_idempotent hforward v⟩

/-- The simple graph obtained by contracting the retained corner chains.
Its vertex set includes chains incident to no selected extra edge. -/
def chainQuotient (A : Finset (Edge D.area)) :
    SimpleGraph {t : Fin n // F.terminal hforward t = t} :=
  SimpleGraph.fromRel (fun B C => ∃ e ∈ A,
    F.terminal hforward e.tail = B.val ∧ F.terminal hforward e.head = C.val)

/-- Keeping good copies retains exactly the natural adjacencies between chains. -/
theorem chainQuotient_goodEdges_eq :
    F.chainQuotient hforward (F.goodEdges hforward) =
      F.chainQuotient hforward Finset.univ := by
  classical
  ext B C
  constructor
  · rintro ⟨hne, h | h⟩
    · obtain ⟨e, _, ht, hh⟩ := h
      exact ⟨hne, Or.inl ⟨e, Finset.mem_univ _, ht, hh⟩⟩
    · obtain ⟨e, _, ht, hh⟩ := h
      exact ⟨hne, Or.inr ⟨e, Finset.mem_univ _, ht, hh⟩⟩
  · have hgood : ∀ B C : {t : Fin n // F.terminal hforward t = t}, B ≠ C →
        (∃ e : Edge D.area,
          F.terminal hforward e.tail = B.val ∧ F.terminal hforward e.head = C.val) →
        (F.chainQuotient hforward (F.goodEdges hforward)).Adj B C := by
      rintro B C hne ⟨e, ht, hh⟩
      have hterm : F.terminal hforward e.tail ≠ F.terminal hforward e.head := by
        intro h
        exact hne (Subtype.ext (ht.symm.trans (h.trans hh)))
      rcases lt_or_gt_of_ne hterm with hlt | hgt
      · exact ⟨hne, Or.inl ⟨e, (F.mem_goodEdges hforward e).mpr (Or.inr hlt), ht, hh⟩⟩
      · have hen : e ∉ F.edges := fun he =>
          hterm ((F.terminal_eq_iff_mem hforward e).mpr he)
        have htail :=
          ((hforward e).trans ((F.le_terminal hforward e.head).trans_lt hgt)).ne
        obtain ⟨f, hef, _⟩ := F.exists_shortSuccessor hforward e hen htail
        obtain ⟨hft, hfh⟩ := F.shortLink_terminals hforward hef
        have hf : f ∈ F.goodEdges hforward := by
          apply (F.mem_goodEdges hforward f).mpr
          exact Or.inr (hfh ▸ hft ▸ hgt)
        exact ⟨hne, Or.inr ⟨f, hf, hfh.symm.trans hh, hft.symm.trans ht⟩⟩
    rintro ⟨hne, h | h⟩
    · obtain ⟨e, _, ht, hh⟩ := h
      exact hgood B C hne ⟨e, ht, hh⟩
    · obtain ⟨e, _, ht, hh⟩ := h
      exact (hgood C B hne.symm ⟨e, ht, hh⟩).symm

/-- Retaining the corner edges connects each vertex to its chain terminal. -/
theorem weakReach_terminal_of_subset {A : Finset (Edge D.area)} (hA : F.edges ⊆ A)
    (v : Fin n) :
    Relation.EqvGen (fun x y => ∃ e ∈ A, e.tail = x ∧ e.head = y)
      v (F.terminal hforward v) := by
  apply Relation.EqvGen.reflTransGen_le_eqvGen
  apply Relation.ReflTransGen.mono _ _ _ (F.reachable_terminal hforward v)
  rintro x y hxy
  obtain ⟨e, he, ht, hh⟩ := (F.step_iff x y).mp hxy
  exact ⟨e, hA he, ht, hh⟩

/-- Contraction preserves every weak block, including isolated corner chains. -/
theorem chainQuotient_reachable_iff (A : Finset (Edge D.area)) (hA : F.edges ⊆ A)
    (u v : Fin n) :
    (F.chainQuotient hforward A).Reachable
      (F.chainVertex hforward u) (F.chainVertex hforward v) ↔
      Relation.EqvGen (fun x y => ∃ e ∈ A, e.tail = x ∧ e.head = y) u v := by
  let R := fun x y => ∃ e ∈ A, e.tail = x ∧ e.head = y
  have ht := F.weakReach_terminal_of_subset hforward hA
  constructor
  · intro h
    have hq := (eqvGen_iff_fromRel_reachable _ _).mpr h
    have hmap : ∀ B C : {t : Fin n // F.terminal hforward t = t},
        Relation.EqvGen
          (fun B C => ∃ e ∈ A, F.terminal hforward e.tail = B.val ∧
            F.terminal hforward e.head = C.val) B C →
          Relation.EqvGen R B.val C.val := by
      intro B C hBC
      induction hBC with
      | rel B C he =>
        obtain ⟨e, he, htB, htC⟩ := he
        rw [← htB, ← htC]
        exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (ht e.tail))
          (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ ⟨e, he, rfl, rfl⟩)
            (ht e.head))
      | refl => exact Relation.EqvGen.refl _
      | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
      | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
    exact Relation.EqvGen.trans _ _ _ (ht u)
      (Relation.EqvGen.trans _ _ _ (hmap _ _ hq) (Relation.EqvGen.symm _ _ (ht v)))
  · intro h
    apply (eqvGen_iff_fromRel_reachable _ _).mp
    induction h with
    | rel x y he =>
      obtain ⟨e, he, rfl, rfl⟩ := he
      exact Relation.EqvGen.rel _ _ ⟨e, he, rfl, rfl⟩
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- The contraction criterion applies directly to actual orientations. -/
theorem chainQuotient_reachable_iff_weakReach (θ : Orientation D)
    (hθ : F.edges ⊆ fullSelection θ) (u v : Fin n) :
    (F.chainQuotient hforward (fullSelection θ)).Reachable
      (F.chainVertex hforward u) (F.chainVertex hforward v) ↔ WeakReach θ u v :=
  F.chainQuotient_reachable_iff hforward (fullSelection θ) hθ u v

/-- Connectivity is unchanged by contracting the corner chains. -/
theorem chainQuotient_preconnected_iff (A : Finset (Edge D.area)) (hA : F.edges ⊆ A) :
    (F.chainQuotient hforward A).Preconnected ↔
      ∀ u v, Relation.EqvGen (fun x y => ∃ e ∈ A, e.tail = x ∧ e.head = y) u v := by
  constructor
  · intro h u v
    exact (F.chainQuotient_reachable_iff hforward A hA u v).mp (h _ _)
  · intro h B C
    have hp := (F.chainQuotient_reachable_iff hforward A hA B.val C.val).mpr (h _ _)
    have hB : F.chainVertex hforward B.val = B := Subtype.ext B.property
    have hC : F.chainVertex hforward C.val = C := Subtype.ext C.property
    simpa only [hB, hC] using hp

/-- An actual state retaining the corners is connected exactly when its quotient is. -/
theorem chainQuotient_preconnected_iff_selectedConnected (θ : Orientation D)
    (hθ : F.edges ⊆ fullSelection θ) :
    (F.chainQuotient hforward (fullSelection θ)).Preconnected ↔ SelectedConnected θ :=
  F.chainQuotient_preconnected_iff hforward (fullSelection θ) hθ

end VerticalStripLLT.Circular.DiagramProof.CornerFamily
