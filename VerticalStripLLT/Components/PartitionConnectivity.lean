import VerticalStripLLT.Components.PartitionCondensation
import Mathlib.SetTheory.Cardinal.Finite

/-!
# The signed ordered-partition identity for arbitrary finite digraphs

The strong-component quotient is edgeless precisely when every original edge
has a directed return path. In that case its classes are exactly the weak
components. This completes Lemma A for the existing finite partition sum.
-/

namespace VerticalStripLLT.Components.OrderedPartitions

open scoped Classical

noncomputable section

variable {V : Type*}

/-- Every directed edge has a return path. For a loop, the empty return path suffices. -/
def TotallyCyclic (R : V → V → Prop) : Prop :=
  ∀ ⦃x y⦄, R x y → Relation.ReflTransGen R y x

theorem TotallyCyclic.reverse_reachable {R : V → V → Prop} (hR : TotallyCyclic R)
    {x y : V} (hxy : Relation.ReflTransGen R x y) : Relation.ReflTransGen R y x := by
  induction hxy with
  | refl => exact Relation.ReflTransGen.refl
  | tail h hstep ih => exact (hR hstep).trans ih

theorem eqvGen_of_reachable {R : V → V → Prop} {x y : V}
    (hxy : Relation.ReflTransGen R x y) : Relation.EqvGen R x y := by
  induction hxy with
  | refl => exact Relation.EqvGen.refl _
  | tail h hstep ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ hstep)

/-- When edges return, weak connectivity and mutual directed reachability coincide. -/
theorem eqvGen_iff_mutual_reachable {R : V → V → Prop} (hR : TotallyCyclic R)
    (x y : V) :
    Relation.EqvGen R x y ↔
      Relation.ReflTransGen R x y ∧ Relation.ReflTransGen R y x := by
  constructor
  · intro h
    induction h with
    | rel x y hxy => exact ⟨Relation.ReflTransGen.single hxy, hR hxy⟩
    | refl x => exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
    | symm x y h ih => exact ⟨ih.2, ih.1⟩
    | trans x y z hxy hyz ihxy ihyz =>
      exact ⟨ihxy.1.trans ihyz.1, ihyz.2.trans ihxy.2⟩
  · exact fun h => eqvGen_of_reachable h.1

/-- The number of spanning weak components, including isolated vertices. -/
def weakComponentCount (R : V → V → Prop) : ℕ :=
  Nat.card (Quotient (Relation.EqvGen.setoid R))

/-- Strong and weak component types agree when every edge has a return path. -/
def strongWeakComponentEquiv (R : V → V → Prop) (hR : TotallyCyclic R) :
    letI : Preorder V := reachabilityPreorder R
    Antisymmetrization V (· ≤ ·) ≃ Quotient (Relation.EqvGen.setoid R) := by
  letI : Preorder V := reachabilityPreorder R
  exact Quotient.congrRight (fun x y => (eqvGen_iff_mutual_reachable hR x y).symm)

variable [DecidableEq V] [Fintype V]

omit [DecidableEq V] in
/-- The strict reachability condensation has no edges exactly in the totally cyclic case. -/
theorem condensation_edgeless_iff_totallyCyclic (R : V → V → Prop) :
    letI : Preorder V := reachabilityPreorder R
    Edgeless (fun x y : Antisymmetrization V (· ≤ ·) => x < y)
      (Finset.univ.image (toAntisymmetrization (α := V) (· ≤ ·))) ↔ TotallyCyclic R := by
  let : Preorder V := reachabilityPreorder R
  let q := toAntisymmetrization (α := V) (· ≤ ·)
  constructor
  · intro h x y hxy
    have hx : q x ∈ Finset.univ.image q :=
      Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
    have hy : q y ∈ Finset.univ.image q :=
      Finset.mem_image.mpr ⟨y, Finset.mem_univ y, rfl⟩
    have hle : q x ≤ q y :=
      toAntisymmetrization_le_toAntisymmetrization_iff.mpr
        (Relation.ReflTransGen.single hxy)
    have hge : q y ≤ q x := by
      by_contra hn
      exact h hx hy (lt_iff_le_not_ge.mpr ⟨hle, hn⟩)
    exact toAntisymmetrization_le_toAntisymmetrization_iff.mp hge
  · intro h x y hx hy hxy
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hy
    have hab : Relation.ReflTransGen R a b :=
      toAntisymmetrization_le_toAntisymmetrization_iff.mp hxy.le
    have hba : q b ≤ q a :=
      toAntisymmetrization_le_toAntisymmetrization_iff.mpr (h.reverse_reachable hab)
    exact (not_le_of_gt hxy) hba

omit [DecidableEq V] in
/-- The finite vertex image in the totally cyclic condensation has one element
per weak component. The proof identifies the actual quotient types. -/
theorem condensation_card_eq_weakComponentCount (R : V → V → Prop)
    (hR : TotallyCyclic R) :
    letI : Preorder V := reachabilityPreorder R
    (Finset.univ.image (toAntisymmetrization (α := V) (· ≤ ·))).card =
      weakComponentCount R := by
  let : Preorder V := reachabilityPreorder R
  let Q := Antisymmetrization V (· ≤ ·)
  let q : V → Q := toAntisymmetrization (· ≤ ·)
  have hq : Function.Surjective q := by
    intro x
    exact ⟨ofAntisymmetrization (· ≤ ·) x, by simp [q]⟩
  let : Fintype Q := Fintype.ofSurjective q hq
  have hfull : (Finset.univ : Finset V).image q = (Finset.univ : Finset Q) :=
    Finset.image_univ_of_surjective hq
  change ((Finset.univ : Finset V).image q).card = weakComponentCount R
  rw [hfull, Finset.card_univ, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (strongWeakComponentEquiv R hR)

/-- Lemma A: compatible ordered partitions have signed sum equal to the weak
component parity in the totally cyclic case, and zero otherwise. -/
theorem signedSum_eq_weakComponentCount (R : V → V → Prop) :
    signedSum R (Finset.univ : Finset V) =
      if TotallyCyclic R then (-1 : ℤ) ^ weakComponentCount R else 0 := by
  let : Preorder V := reachabilityPreorder R
  have hacyclic : ∀ x : Antisymmetrization V (· ≤ ·),
      ¬ Relation.TransGen (fun a b : Antisymmetrization V (· ≤ ·) => a < b) x x := by
    intro x hx
    have hxx : x < x := by simpa only [Relation.transGen_eq_self] using hx
    exact (lt_irrefl x) hxx
  rw [signedSum_condensation R, signedSum_eq_of_acyclic _ hacyclic,
    condensation_edgeless_iff_totallyCyclic R]
  by_cases hR : TotallyCyclic R
  · simp only [ite_eq_left hR]
    rw [condensation_card_eq_weakComponentCount R hR]
  · simp only [ite_eq_right hR]

end

end VerticalStripLLT.Components.OrderedPartitions
