import VerticalStripLLT.Components.DiagramProof.Relations.FiniteSubsetPaths
import VerticalStripLLT.Components.DiagramProof.Relations.OverlappingPositions

/-!
# Fixed-position exchanges through two overlapping sets

This is the finite position lemma used by the complete-diagram argument.  The
distinguished position has the same membership at each exchange endpoint,
while all other positions are joined by
the two overlapping sets `J` and `K`.  The move relation is deliberately left
abstract: a local exchange may be realized by any actual reflexive-transitive
path on the underlying finite subsets. Intermediate states on a local path
need not keep the distinguished position fixed.
-/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

/-- Local exchanges inside two overlapping position sets connect all subsets of the same
size that agree at `p`. -/
theorem fixed_card_connectivity_fixing_position
    {V : Type*} [DecidableEq V]
    (U J K : Finset V) (p : V)
    (step : Finset V → Finset V → Prop)
    (hJ : J ⊆ U) (hK : K ⊆ U)
    (hpJ : p ∉ J) (hpK : p ∉ K)
    (hcover : ∀ v, v ∈ U → v ≠ p → v ∈ J ∨ v ∈ K)
    (hoverlap : (J ∩ K).Nonempty)
    (hlocal : ∀ X a b, X ⊆ U →
      ((a ∈ J ∧ b ∈ J) ∨ (a ∈ K ∧ b ∈ K)) →
      a ∈ X.erase p → b ∉ X.erase p →
      ∃ Y, Relation.ReflTransGen step X Y ∧ Y = insert b (X.erase a))
    {S T : Finset V} (hS : S ⊆ U) (hT : T ⊆ U)
    (hcard : S.card = T.card)
    (hp : p ∈ S ↔ p ∈ T) :
    Relation.ReflTransGen step S T := by
  let State := {X : Finset V // X ⊆ U ∧ (p ∈ X ↔ p ∈ S)}
  let selection : State → Finset V := fun X => X.1.erase p
  let stateStep : State → State → Prop := fun X Y => Relation.ReflTransGen step X.1 Y.1
  let R : V → V → Prop := fun a b =>
    (a ∈ J ∧ b ∈ J) ∨ (a ∈ K ∧ b ∈ K)

  have hpaths : ∀ {a b}, a ∈ U → b ∈ U → a ≠ p → b ≠ p →
      Relation.ReflTransGen R a b := by
    intro a b haU hbU hap hbp
    obtain ⟨c, hc⟩ := hoverlap
    obtain ⟨hcJ, hcK⟩ := Finset.mem_inter.mp hc
    have hac : R a c := (hcover a haU hap).elim
      (fun h => Or.inl ⟨h, hcJ⟩) (fun h => Or.inr ⟨h, hcK⟩)
    have hcb : R c b := (hcover b hbU hbp).elim
      (fun h => Or.inl ⟨hcJ, h⟩) (fun h => Or.inr ⟨hcK, h⟩)
    exact (Relation.ReflTransGen.single hac).tail hcb

  have hlocalState : ∀ (X : State) a b, R a b →
      a ∈ selection X → b ∉ selection X →
      ∃ Y : State, Relation.ReflTransGen stateStep X Y ∧
        selection Y = insert b ((selection X).erase a) := by
    intro X a b hR ha hb
    have hR' : (a ∈ J ∧ b ∈ J) ∨ (a ∈ K ∧ b ∈ K) := hR
    have haX : a ∈ X.1 := Finset.mem_of_mem_erase ha
    have hap : a ≠ p := (Finset.mem_erase.mp ha).1
    have hbU : b ∈ U := by
      rcases hR' with h | h
      · exact hJ h.2
      · exact hK h.2
    have hbp : b ≠ p := by
      intro hbp
      rcases hR' with h | h
      · exact hpJ (hbp ▸ h.2)
      · exact hpK (hbp ▸ h.2)
    obtain ⟨Y, hXY, hY⟩ := hlocal X.1 a b X.2.1 hR' ha hb
    have hYsub : Y ⊆ U := by
      rw [hY]
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hbU
      · exact X.2.1 (Finset.mem_of_mem_erase hx)
    have hYS : p ∈ Y ↔ p ∈ S := by
      calc
        p ∈ Y ↔ p ∈ insert b (X.1.erase a) := by rw [hY]
        _ ↔ p ∈ X.1 := by
          simp [Ne.symm hbp, Ne.symm hap]
        _ ↔ p ∈ S := X.2.2
    let Z : State := ⟨Y, hYsub, hYS⟩
    have hXZ : Relation.ReflTransGen stateStep X Z := Relation.ReflTransGen.single hXY
    have hsel : selection Z = insert b ((selection X).erase a) := by
      change Y.erase p = insert b ((X.1.erase p).erase a)
      rw [hY]
      rw [Finset.erase_insert_of_ne hbp]
      congr 1
      ext x
      simp only [Finset.mem_erase]
      tauto

    exact ⟨Z, hXZ, hsel⟩

  have hselection_injective : Function.Injective selection := by
    intro X Y hXY
    apply Subtype.ext
    apply Finset.ext
    intro v
    by_cases hv : v = p
    · subst v
      exact X.2.2.trans Y.2.2.symm
    · have h := congrArg (fun Q => v ∈ Q) hXY
      simpa [selection, Finset.mem_erase, hv] using Iff.of_eq h

  let X₀ : State := ⟨S, hS, Iff.rfl⟩
  let Y₀ : State := ⟨T, hT, hp.symm⟩
  have hcardErase : (selection X₀).card = (selection Y₀).card := by
    by_cases hs : p ∈ S
    · have ht : p ∈ T := hp.mp hs
      simp [X₀, Y₀, selection, Finset.card_erase_of_mem hs,
        Finset.card_erase_of_mem ht, hcard]
    · have ht : p ∉ T := by
        intro ht
        exact hs (hp.mpr ht)
      simp [X₀, Y₀, selection, Finset.erase_eq_of_notMem hs,
        Finset.erase_eq_of_notMem ht, hcard]
  let label : V → Bool := fun v => decide (v ∈ U ∧ v ≠ p)
  have hlabel (X : State) (v : V) (hv : v ∈ selection X) : label v = true := by
    exact decide_eq_true ⟨X.2.1 (Finset.mem_of_mem_erase hv), (Finset.mem_erase.mp hv).1⟩
  have hstate : Relation.ReflTransGen stateStep X₀ Y₀ := by
    apply fixed_label_connectivity selection stateStep label hselection_injective
    · intro X a b hab ha hb
      have hal := hlabel X a ha
      have hbl : label b = true := hab.symm.trans hal
      have hbvalid : b ∈ U ∧ b ≠ p := of_decide_eq_true hbl
      exact reflTransGen_exchange selection stateStep R hlocalState
        (hpaths (X.2.1 (Finset.mem_of_mem_erase ha)) hbvalid.1
          (Finset.mem_erase.mp ha).1 hbvalid.2) ha hb
    · intro l
      cases l with
      | false =>
        have hz (X : State) : (selection X).filter (fun v => label v = false) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro v hv hfalse
          have := hlabel X v hv
          simp_all
        rw [hz, hz]
      | true =>
        have ht (X : State) : (selection X).filter (fun v => label v = true) = selection X :=
          Finset.filter_eq_self.mpr (hlabel X)
        rw [ht, ht]
        exact hcardErase
  have flatten {X Y : State} (h : Relation.ReflTransGen stateStep X Y) :
      Relation.ReflTransGen step X.1 Y.1 := by
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hxy ih => exact ih.trans hxy
  have hflat := flatten hstate

  exact hflat

end

end VerticalStripLLT.Circular.DiagramProof
