import VerticalStripLLT.Components.DiagramProof.LayerStates
import VerticalStripLLT.Components.DiagramProof.SinkRelabel
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# Splitting a layer at two local pairs

The NN and DN recurrences split the states of a diagram by the two local short
pairs and keep the remaining exterior selection fixed. This module records the
finite sum splitting, the diamond identity for these states, and reindexing of
exterior selections by an involutive vertex relabelling.
-/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

section Sums

variable {α M : Type*} [DecidableEq α] [AddCommMonoid M]

/-- Split the subsets of `S` according to two of its elements. -/
theorem sum_powerset_two {S : Finset α} {q r : α} (hq : q ∈ S) (hr : r ∈ S) (hqr : q ≠ r)
    (g : Finset α → M) :
    ∑ T ∈ S.powerset, g T = ∑ Q ∈ ((S.erase q).erase r).powerset,
      (g Q + g (insert q Q) + g (insert r Q) + g (insert q (insert r Q))) := by
  have hr' : r ∈ S.erase q := Finset.mem_erase.mpr ⟨hqr.symm, hr⟩
  have hS : S = insert q (insert r ((S.erase q).erase r)) := by
    rw [Finset.insert_erase hr', Finset.insert_erase hq]
  have hq' : q ∉ insert r ((S.erase q).erase r) := by
    rw [Finset.insert_erase hr']
    exact Finset.notMem_erase q S
  have hr'' : r ∉ (S.erase q).erase r := Finset.notMem_erase r _
  conv_lhs => rw [hS]
  rw [Finset.sum_powerset_insert hq', Finset.sum_powerset_insert hr'',
    Finset.sum_powerset_insert hr'', ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun Q _ => ?_
  abel

/-- Split the subsets of `S` according to one of its elements. -/
theorem sum_powerset_one {S : Finset α} {q : α} (hq : q ∈ S) (g : Finset α → M) :
    ∑ T ∈ S.powerset, g T = ∑ Q ∈ (S.erase q).powerset, (g Q + g (insert q Q)) := by
  conv_lhs => rw [← Finset.insert_erase hq]
  rw [Finset.sum_powerset_insert (Finset.notMem_erase q S), ← Finset.sum_add_distrib]

end Sums

/-! ### Relabelling exterior selections -/

section Relabel

variable {n : ℕ}

/-- The image of a set of pairs under a vertex relabelling. -/
def relabelPairs (σ : Equiv.Perm (Fin n)) (T : Finset (Fin n × Fin n)) :
    Finset (Fin n × Fin n) :=
  T.map ⟨fun p => (σ p.1, σ p.2), fun p q h => by
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    exact Prod.ext (σ.injective h1) (σ.injective h2)⟩

theorem mem_relabelPairs {σ : Equiv.Perm (Fin n)} {T : Finset (Fin n × Fin n)}
    {u v : Fin n} : (σ u, σ v) ∈ relabelPairs σ T ↔ (u, v) ∈ T := by
  simp only [relabelPairs, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨⟨a, b⟩, hab, h⟩
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [σ.injective h1, σ.injective h2] at hab
    exact hab
  · intro h
    exact ⟨(u, v), h, rfl⟩

theorem card_relabelPairs (σ : Equiv.Perm (Fin n)) (T : Finset (Fin n × Fin n)) :
    (relabelPairs σ T).card = T.card := Finset.card_map _

theorem relabelPairs_involutive {σ : Equiv.Perm (Fin n)} (hσ : ∀ v, σ (σ v) = v)
    (T : Finset (Fin n × Fin n)) : relabelPairs σ (relabelPairs σ T) = T := by
  ext ⟨u, v⟩
  have huv : (u, v) = (σ (σ u), σ (σ v)) := by rw [hσ, hσ]
  conv_lhs => rw [huv]
  rw [mem_relabelPairs, mem_relabelPairs]

/-- An involution preserving `X` reindexes sums over the subsets of `X`. -/
theorem sum_powerset_relabel {M : Type*} [AddCommMonoid M] {σ : Equiv.Perm (Fin n)}
    (hσ : ∀ v, σ (σ v) = v) {X : Finset (Fin n × Fin n)}
    (hX : ∀ p ∈ X, (σ p.1, σ p.2) ∈ X) (f : Finset (Fin n × Fin n) → M) :
    ∑ P ∈ X.powerset, f P = ∑ Q ∈ X.powerset, f (relabelPairs σ Q) := by
  have hmaps : ∀ Q ∈ X.powerset, relabelPairs σ Q ∈ X.powerset := by
    intro Q hQ
    apply Finset.mem_powerset.mpr
    intro p hp
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_map.mp hp
    exact hX _ (Finset.mem_powerset.mp hQ hab)
  apply Finset.sum_nbij' (relabelPairs σ) (relabelPairs σ) hmaps hmaps
  · intro P _
    exact relabelPairs_involutive hσ P
  · intro Q _
    exact relabelPairs_involutive hσ Q
  · intro P _
    rw [relabelPairs_involutive hσ P]

end Relabel

/-! ### The diamond on states -/

section Diamond

variable {n : ℕ} {D : Diagram n} (hD : Forward D)

theorem stateOf_insert_selected (T : Finset (Fin n × Fin n)) {a b : Fin n}
    (hab : naturalRel D a b) (u v : Fin n) :
    D.edgeData.selected (stateOf hD (insert (a, b) T)).val u v ↔
      addPair (D.edgeData.selected (stateOf hD T).val) a b u v := by
  simp only [stateOf_selected, addPair, Finset.mem_insert, Prod.mk.injEq]
  constructor
  · rintro (h | ⟨⟨rfl, rfl⟩ | h, hn⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl (Or.inr ⟨h, hn⟩)
  · rintro ((h | ⟨h, hn⟩) | ⟨rfl, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨Or.inr h, hn⟩
    · exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hab⟩

/-- The diamond at the local pairs `ab, bc` below a selected `ac`. -/
theorem stateOf_diamond (Q : Finset (Fin n × Fin n)) {a b c : Fin n}
    (hab : naturalRel D a b) (hbc : naturalRel D b c)
    (hac : D.edgeData.selected (stateOf hD Q).val a c) (v : Fin n) (m : ℕ) (β : Fin m) :
    markedK (stateOf hD (insert (a, b) Q)) v m β + markedK (stateOf hD (insert (b, c) Q)) v m β =
        markedK (stateOf hD Q) v m β +
          markedK (stateOf hD (insert (a, b) (insert (b, c) Q))) v m β ∧
      markedE (stateOf hD (insert (a, b) Q)) v m β +
          markedE (stateOf hD (insert (b, c) Q)) v m β =
        markedE (stateOf hD Q) v m β +
          markedE (stateOf hD (insert (a, b) (insert (b, c) Q))) v m β := by
  have h1 := stateOf_insert_selected hD Q hab
  have h2 := stateOf_insert_selected hD Q hbc
  have h3 : ∀ u w, D.edgeData.selected (stateOf hD (insert (a, b) (insert (b, c) Q))).val u w ↔
      addPair (D.edgeData.selected (stateOf hD (insert (a, b) Q)).val) b c u w := by
    intro u w
    rw [stateOf_insert_selected hD (insert (b, c) Q) hab]
    simp only [addPair, h1, h2]
    tauto
  exact ⟨markedK_diamond _ _ _ _ a b c v hac h1 h2 h3 m β,
    markedE_diamond hD _ _ _ _ a b c v hac h1 h2 h3 m β⟩

end Diamond

end

end VerticalStripLLT.Circular.DiagramProof
