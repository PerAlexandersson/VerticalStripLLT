import VerticalStripLLT.Components.GainCoefficientCancellation

/-!
# Balanced potentials and contraction to weak blocks

Contraction changes the vertex type but retains the original edge instances.
Its endpoints depend only on the contracted set, not on the chosen potential.
The selected edges of an eventual contracted graph are supplied separately,
typically as `X \ F`.
-/

namespace VerticalStripLLT.Components.GainData

open scoped Classical

noncomputable section

variable {V E : Type*} (G : GainData V E)

/-- An integer potential realizing the prescribed gains on every edge of `F`. -/
def BalancedPotential (F : Finset E) (p : V → ℤ) : Prop :=
  ∀ e ∈ F, p (G.head e) - p (G.tail e) = G.gain e

/-- Balancedness requires exact edge differences, not merely feasible inequalities. -/
def Balanced (F : Finset E) : Prop := ∃ p : V → ℤ, G.BalancedPotential F p

theorem BalancedPotential.mono {F H : Finset E} {p : V → ℤ}
    (hp : G.BalancedPotential F p) (hHF : H ⊆ F) : G.BalancedPotential H p :=
  fun e he => hp e (hHF he)

/-- Weak components of the spanning selected graph, including isolated vertices. -/
def weakBlock (F : Finset E) : Type _ :=
  Quotient (Relation.EqvGen.setoid (G.selectedRelation F))

/-- The weak block containing a vertex. -/
def weakBlockMk (F : Finset E) (v : V) : G.weakBlock F := Quotient.mk _ v

theorem weakBlockMk_surjective (F : Finset E) : Function.Surjective (G.weakBlockMk F) :=
  Quotient.mk_surjective

instance weakBlockFintype [Fintype V] (F : Finset E) : Fintype (G.weakBlock F) :=
  Fintype.ofSurjective (G.weakBlockMk F) (G.weakBlockMk_surjective F)

theorem weakBlockMk_eq_iff {F : Finset E} {x y : V} :
    G.weakBlockMk F x = G.weakBlockMk F y ↔ Relation.EqvGen (G.selectedRelation F) x y :=
  Quotient.eq

theorem weakBlock_card [Fintype V] (F : Finset E) :
    Fintype.card (G.weakBlock F) =
      OrderedPartitions.weakComponentCount (G.selectedRelation F) := by
  change Fintype.card (G.weakBlock F) = Nat.card (G.weakBlock F)
  exact Nat.card_eq_fintype_card.symm

/-- Each edge of `F` has equal endpoint blocks. -/
theorem weakBlockMk_tail_eq_head {F : Finset E} {e : E} (he : e ∈ F) :
    G.weakBlockMk F (G.tail e) = G.weakBlockMk F (G.head e) := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ ⟨e, he, rfl, rfl⟩

/-- Two balanced potentials differ by a constant on every weak block. -/
theorem BalancedPotential.sub_eq_of_weak_connected {F : Finset E} {p q : V → ℤ}
    (hp : G.BalancedPotential F p) (hq : G.BalancedPotential F q)
    {x y : V} (hxy : Relation.EqvGen (G.selectedRelation F) x y) :
    q x - p x = q y - p y := by
  induction hxy with
  | rel x y h =>
    obtain ⟨e, he, rfl, rfl⟩ := h
    have hp' := hp e he
    have hq' := hq e he
    lia
  | refl x => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

theorem BalancedPotential.sub_eq_of_block_eq {F : Finset E} {p q : V → ℤ}
    (hp : G.BalancedPotential F p) (hq : G.BalancedPotential F q)
    {x y : V} (hxy : G.weakBlockMk F x = G.weakBlockMk F y) :
    q x - p x = q y - p y :=
  BalancedPotential.sub_eq_of_weak_connected G hp hq ((G.weakBlockMk_eq_iff).mp hxy)

/-- The difference of balanced potentials descends to a function on weak blocks. -/
def blockPotentialDifference {F : Finset E} {p q : V → ℤ}
    (hp : G.BalancedPotential F p) (hq : G.BalancedPotential F q) : G.weakBlock F → ℤ :=
  Quotient.lift (fun v => q v - p v)
    (fun _ _ hxy => BalancedPotential.sub_eq_of_weak_connected G hp hq hxy)

@[simp]
theorem blockPotentialDifference_mk {F : Finset E} {p q : V → ℤ}
    (hp : G.BalancedPotential F p) (hq : G.BalancedPotential F q) (v : V) :
    G.blockPotentialDifference hp hq (G.weakBlockMk F v) = q v - p v := rfl

/-- Contract `F` while retaining every original edge, including resulting loops
and parallel edges. The vertex maps are definitionally independent of `p`. -/
abbrev contraction (F : Finset E) (p : V → ℤ) : GainData (G.weakBlock F) E where
  tail e := G.weakBlockMk F (G.tail e)
  head e := G.weakBlockMk F (G.head e)
  gain e := G.gain e - (p (G.head e) - p (G.tail e))

@[simp]
theorem contraction_gain_eq_zero {F : Finset E} {p : V → ℤ}
    (hp : G.BalancedPotential F p) {e : E} (he : e ∈ F) :
    (G.contraction F p).gain e = 0 := by
  change G.gain e - (p (G.head e) - p (G.tail e)) = 0
  rw [hp e he, sub_self]

theorem contraction_tail_eq_head {F : Finset E} (p : V → ℤ) {e : E} (he : e ∈ F) :
    (G.contraction F p).tail e = (G.contraction F p).head e :=
  G.weakBlockMk_tail_eq_head he

/-- Selected walks have exactly the same type for all potential choices. -/
theorem contraction_selectedQuiver_eq (F A : Finset E) (p q : V → ℤ) :
    (G.contraction F p).selectedQuiver A = (G.contraction F q).selectedQuiver A := rfl

/-- Changing balanced potential changes gains by a weak-block potential difference. -/
theorem contraction_gain_change {F : Finset E} {p q : V → ℤ}
    (hp : G.BalancedPotential F p) (hq : G.BalancedPotential F q) (e : E) :
    (G.contraction F q).gain e = (G.contraction F p).gain e +
      G.blockPotentialDifference hp hq ((G.contraction F p).tail e) -
      G.blockPotentialDifference hp hq ((G.contraction F p).head e) := by
  change G.gain e - (q (G.head e) - q (G.tail e)) =
    G.gain e - (p (G.head e) - p (G.tail e)) +
      (q (G.tail e) - p (G.tail e)) - (q (G.head e) - p (G.head e))
  lia

end

end VerticalStripLLT.Components.GainData
