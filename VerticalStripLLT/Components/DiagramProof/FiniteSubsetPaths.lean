import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation

/-!
  Generic finite-subset exchange paths.

  The state space is deliberately opaque.  The only information used about a
  local move is its exact effect on the finite selected set.  This makes the
  two lemmas below reusable for both actual flip paths and the auxiliary copy
  relations used in the diagram proof.
-/

namespace VerticalStripLLT.Circular.DiagramProof

variable {V State Label : Type*} [DecidableEq V]

private theorem insert_erase_exchange_assoc (S : Finset V) (a b c : V)
    (ha : a ∈ S) (hc : c ∈ S) (hb : b ∉ S) (hac : a ≠ c) :
    insert c ((insert b (S.erase c)).erase a) = insert b (S.erase a) := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_erase]
  grind

/-!
  A path in `R` can be realized one local exchange at a time.  At the last
  edge of the path, either its tail is absent and we move into it before
  taking the last edge, or it is selected and we move it out first.  The
  latter order is the small point that makes the endpoint set exact.
-/
theorem reflTransGen_exchange
    (selection : State → Finset V) (step : State → State → Prop)
    (R : V → V → Prop)
    (hlocal : ∀ σ a b, R a b → a ∈ selection σ → b ∉ selection σ →
      ∃ τ, Relation.ReflTransGen step σ τ ∧
        selection τ = insert b ((selection σ).erase a))
    {σ : State} {a b : V} (h : Relation.ReflTransGen R a b)
    (ha : a ∈ selection σ) (hb : b ∉ selection σ) :
    ∃ τ, Relation.ReflTransGen step σ τ ∧
      selection τ = insert b ((selection σ).erase a) := by
  induction h generalizing σ with
  | refl =>
    exact (hb (by simpa using ha)).elim
  | @tail c b hpath hstep ih =>
    rcases eq_or_ne c b with rfl | hcb
    · exact ih ha hb
    by_cases hac : a = c
    · subst a
      exact hlocal _ _ _ hstep ha hb
    by_cases hc : c ∈ selection σ
    · obtain ⟨τ, hστ, hτ⟩ := hlocal σ c b hstep hc hb
      have haτ : a ∈ selection τ := by
        rw [hτ]
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hac, ha⟩)
      have hcτ : c ∉ selection τ := by
        rw [hτ]
        simp [hcb]
      obtain ⟨υ, hτυ, hυ⟩ := ih (σ := τ) haτ hcτ
      refine ⟨υ, hστ.trans hτυ, ?_⟩
      rw [hυ, hτ]
      exact insert_erase_exchange_assoc _ _ _ _ ha hc hb hac
    · obtain ⟨τ, hστ, hτ⟩ := ih (σ := σ) ha hc
      have hcτ : c ∈ selection τ := by
        rw [hτ]
        exact Finset.mem_insert_self _ _
      have hbτ : b ∉ selection τ := by
        rw [hτ]
        simp [Ne.symm hcb, hb]
      obtain ⟨υ, hτυ, hυ⟩ := hlocal τ c b hstep hcτ hbτ
      refine ⟨υ, hστ.trans hτυ, ?_⟩
      rw [hυ, hτ]
      simp [hc]


private theorem exists_same_label_target [DecidableEq Label]
    (labelOf : V → Label) (S T : Finset V) (a : V)
    (haS : a ∈ S) (haT : a ∉ T)
    (hcard : ∀ l, (S.filter (fun v => labelOf v = l)).card =
      (T.filter (fun v => labelOf v = l)).card) :
    ∃ b, b ∈ T ∧ b ∉ S ∧ labelOf b = labelOf a := by
  by_contra! hnone
  let P : V → Prop := fun v => labelOf v = labelOf a
  have hsub : T.filter P ⊆ (S.filter P).erase a := by
    intro b hb
    obtain ⟨hbT, hlabel⟩ := Finset.mem_filter.mp hb
    have hbS : b ∈ S := by
      by_contra hbS
      exact hnone b hbT hbS hlabel
    have hba : b ≠ a := fun h => haT (h ▸ hbT)
    exact Finset.mem_erase.mpr ⟨hba, Finset.mem_filter.mpr ⟨hbS, hlabel⟩⟩
  have hamem : a ∈ S.filter P := Finset.mem_filter.mpr ⟨haS, rfl⟩
  have hlt := Finset.card_erase_lt_of_mem hamem
  have hle := Finset.card_le_card hsub
  have heq := hcard (labelOf a)
  change (S.filter P).card = (T.filter P).card at heq
  lia

private theorem filter_card_swap [DecidableEq Label]
    (labelOf : V → Label) (S : Finset V) (a b : V)
    (ha : a ∈ S) (hb : b ∉ S) (hab : labelOf a = labelOf b) (l : Label) :
    ((insert b (S.erase a)).filter (fun v => labelOf v = l)).card =
      (S.filter (fun v => labelOf v = l)).card := by
  by_cases hla : labelOf a = l
  · have hlb : labelOf b = l := hab.symm.trans hla
    have hset : (insert b (S.erase a)).filter (fun v => labelOf v = l) =
        insert b ((S.filter (fun v => labelOf v = l)).erase a) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
      grind
    have hamem : a ∈ S.filter (fun v => labelOf v = l) :=
      Finset.mem_filter.mpr ⟨ha, hla⟩
    have hbnot : b ∉ (S.filter (fun v => labelOf v = l)).erase a :=
      fun h => hb (Finset.mem_filter.mp (Finset.mem_of_mem_erase h)).1
    rw [hset, Finset.card_insert_of_notMem hbnot, Finset.card_erase_of_mem hamem]
    have hpos := Finset.card_pos.mpr ⟨a, hamem⟩
    lia
  · have hlb : labelOf b ≠ l := fun h => hla (hab.trans h)
    have hset : (insert b (S.erase a)).filter (fun v => labelOf v = l) =
        S.filter (fun v => labelOf v = l) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
      grind
    rw [hset]

/-- Exact within-class exchanges connect states with the same class cardinalities. -/
theorem fixed_label_connectivity [DecidableEq Label]
    (selection : State → Finset V) (step : State → State → Prop)
    (labelOf : V → Label) (hinj : Function.Injective selection)
    (hlocal : ∀ σ a b, labelOf a = labelOf b → a ∈ selection σ →
      b ∉ selection σ →
      ∃ τ, Relation.ReflTransGen step σ τ ∧
        selection τ = insert b ((selection σ).erase a))
    {σ τ : State}
    (hcard : ∀ l, ((selection σ).filter (fun v => labelOf v = l)).card =
      ((selection τ).filter (fun v => labelOf v = l)).card) :
    Relation.ReflTransGen step σ τ := by
  generalize hN : (selection σ \ selection τ).card = N
  induction N using Nat.strong_induction_on generalizing σ with
  | h N ih =>
    by_cases hsub : selection σ ⊆ selection τ
    · have hrev : selection τ ⊆ selection σ := by
        intro b hbT
        by_contra hbS
        obtain ⟨a, haS, haT, _⟩ := exists_same_label_target labelOf
          (selection τ) (selection σ) b hbT hbS (fun l => (hcard l).symm)
        exact haT (hsub haS)
      have hstates : σ = τ := hinj (Finset.Subset.antisymm hsub hrev)
      subst τ
      exact Relation.ReflTransGen.refl
    · obtain ⟨a, haS, haT⟩ := Finset.not_subset.mp hsub
      obtain ⟨b, hbT, hbS, hab⟩ := exists_same_label_target labelOf
        (selection σ) (selection τ) a haS haT hcard
      obtain ⟨σ', hσσ', hσ'⟩ := hlocal σ a b hab.symm haS hbS
      have hcard' : ∀ l, ((selection σ').filter (fun v => labelOf v = l)).card =
          ((selection τ).filter (fun v => labelOf v = l)).card := by
        intro l
        rw [hσ']
        exact (filter_card_swap labelOf (selection σ) a b haS hbS hab.symm l).trans
          (hcard l)
      have hdiff : insert b ((selection σ).erase a) \ selection τ =
          (selection σ \ selection τ).erase a := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_sdiff]
        grind
      have hamem : a ∈ selection σ \ selection τ := Finset.mem_sdiff.mpr ⟨haS, haT⟩
      have hlt : (selection σ' \ selection τ).card < N := by
        rw [hσ', hdiff, ← hN]
        exact Finset.card_erase_lt_of_mem hamem
      exact hσσ'.trans (ih _ hlt hcard' rfl)

end VerticalStripLLT.Circular.DiagramProof
