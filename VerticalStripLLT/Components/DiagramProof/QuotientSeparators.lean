import VerticalStripLLT.Components.DiagramProof.ChainSeparators
import VerticalStripLLT.Components.DiagramProof.ChainQuotient

/-! The chain quotient remains connected after deleting one chain. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hforward : Forward D)

theorem chainQuotient_induce_preconnected_avoiding_terminal (hn : 3 ≤ n)
    (hshort : ∀ u v : Fin n, u < v → v.val ≤ u.val + 2 →
      naturalEdgeRelation (D := D) u v) (t : Fin n) :
    (F.chainQuotient hforward (F.goodEdges hforward)).induce
      {B : {r : Fin n // F.terminal hforward r = r} | B.val ≠ t} |>.Preconnected := by
  let V := {B : {t : Fin n // F.terminal hforward t = t} // B.val ≠ t}
  let qv (x : Fin n) (hx : F.terminal hforward x ≠ t) : V :=
    ⟨F.chainVertex hforward x, hx⟩
  let Q : {t : Fin n // F.terminal hforward t = t} →
      {t : Fin n // F.terminal hforward t = t} → Prop := fun B C =>
    ∃ e ∈ F.goodEdges hforward,
      F.terminal hforward e.tail = B.val ∧
        F.terminal hforward e.head = C.val
  let QV : V → V → Prop := fun B C => Q B.val C.val
  have sameMem : ∀ {x y : Fin n},
      Relation.EqvGen (fun a b =>
        F.terminal hforward a ≠ t ∧ F.terminal hforward b ≠ t ∧
          F.goodEdgeRelation hforward a b) x y →
      (F.terminal hforward x ≠ t ↔ F.terminal hforward y ≠ t) := by
    intro x y hxy
    induction hxy with
    | rel _ _ h => exact ⟨fun _ => h.2.1, fun _ => h.1⟩
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have mapped : ∀ {x y : Fin n},
      (hxy : Relation.EqvGen (fun a b =>
        F.terminal hforward a ≠ t ∧ F.terminal hforward b ≠ t ∧
          F.goodEdgeRelation hforward a b) x y) →
      ∀ (hx : F.terminal hforward x ≠ t)
        (hy : F.terminal hforward y ≠ t),
        Relation.EqvGen QV (qv x hx) (qv y hy) := by
    intro x y hxy
    induction hxy with
    | rel x y h =>
        intro hx hy
        rcases h with ⟨_, _, e, he, htail, hhead⟩
        apply Relation.EqvGen.rel
        exact ⟨e, he, congrArg (F.terminal hforward) htail,
          congrArg (F.terminal hforward) hhead⟩
    | refl x =>
        intro hx hy
        exact Relation.EqvGen.refl _
    | symm x y hxy ih =>
        intro hx hy
        exact Relation.EqvGen.symm _ _ (ih hy hx)
    | trans x y z hxy hyz ihxy ihyz =>
        intro hx hz
        have hy : F.terminal hforward y ≠ t := (sameMem hxy).mp hx
        exact Relation.EqvGen.trans _ _ _ (ihxy hx hy) (ihyz hy hz)
  have reachQ : ∀ {B C : V}, Relation.EqvGen QV B C →
      ((F.chainQuotient hforward (F.goodEdges hforward)).induce
        {B : {r : Fin n // F.terminal hforward r = r} | B.val ≠ t}).Reachable B C := by
    intro B C hBC
    induction hBC with
    | rel B C h =>
        by_cases hEq : B = C
        · subst C
          exact SimpleGraph.Reachable.refl _
        · have hEqVal : B.val ≠ C.val := by
            intro hval
            exact hEq (Subtype.ext hval)
          exact ⟨SimpleGraph.Walk.cons
            (show ((F.chainQuotient hforward (F.goodEdges hforward)).induce
                {B : {r : Fin n // F.terminal hforward r = r} | B.val ≠ t}).Adj B C from
              ⟨hEqVal, Or.inl h⟩) SimpleGraph.Walk.nil⟩
    | refl => exact SimpleGraph.Reachable.refl _
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  intro B C
  have hB : F.terminal hforward B.val.val ≠ t := by
    rw [B.val.property]
    exact B.property
  have hC : F.terminal hforward C.val.val ≠ t := by
    rw [C.val.property]
    exact C.property
  have hBC := F.goodEdge_weakReach_avoiding_terminal hforward hn hshort t
    B.val.val C.val.val hB hC
  have hmapped := mapped hBC hB hC
  have hreach := reachQ hmapped
  have hqB : qv B.val.val hB = B := Subtype.ext (Subtype.ext B.val.property)
  have hqC : qv C.val.val hC = C := Subtype.ext (Subtype.ext C.val.property)
  simpa only [hqB, hqC] using hreach

/-- At least one chain survives any one-terminal deletion. -/
theorem chainQuotient_induce_connected_avoiding_terminal (hn : 3 ≤ n)
    (hshort : ∀ u v : Fin n, u < v → v.val ≤ u.val + 2 →
      naturalEdgeRelation (D := D) u v) (t : Fin n) :
    ((F.chainQuotient hforward (F.goodEdges hforward)).induce
      {B : {r : Fin n // F.terminal hforward r = r} | B.val ≠ t}).Connected := by
  classical
  let u : Fin n := ⟨0, by lia⟩
  let v : Fin n := ⟨1, by lia⟩
  have huv := F.terminal_ne_of_consecutive hforward hn hshort u v rfl
  have hex : ∃ w : Fin n, F.terminal hforward w ≠ t := by
    by_cases hu : F.terminal hforward u = t
    · exact ⟨v, fun hv => huv (hu.trans hv.symm)⟩
    · exact ⟨u, hu⟩
  obtain ⟨w, hw⟩ := hex
  exact {
    preconnected :=
      F.chainQuotient_induce_preconnected_avoiding_terminal hforward hn hshort t
    nonempty := ⟨⟨F.chainVertex hforward w, hw⟩⟩ }

end VerticalStripLLT.Circular.DiagramProof.CornerFamily
