import VerticalStripLLT.Components.OrderedPartitions
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.WellFoundedSet
import Mathlib.Logic.Relation

/-!
# The ordered-partition identity for a DAG

We evaluate the actual finite partition sum by its top-block recursion. The
inductive hypothesis needs only a source in every nonempty induced subgraph;
acyclicity of the transitive closure supplies this condition.
-/

namespace VerticalStripLLT.Components.OrderedPartitions

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [DecidableEq V]

theorem edgeHeads_subset (R : V → V → Prop) (S : Finset V) : edgeHeads R S ⊆ S :=
  Finset.filter_subset _ _

theorem edgeHeads_eq_empty_iff (R : V → V → Prop) (S : Finset V) :
    edgeHeads R S = ∅ ↔ Edgeless R S := by
  constructor
  · intro h x y hx hy hxy
    have hm : y ∈ edgeHeads R S := Finset.mem_filter.mpr ⟨hy, x, hx, hxy⟩
    rw [h] at hm
    exact Finset.notMem_empty y hm
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    obtain ⟨hyS, x, hxS, hxy⟩ := Finset.mem_filter.mp hy
    exact h hxS hyS hxy

/-- Complementation changes a sum over supersets into a powerset sum. -/
theorem sum_supersets_complement_sign (S M : Finset V) (hMS : M ⊆ S) :
    (∑ U ∈ S.powerset, if M ⊆ U then (-1 : ℤ) ^ (S \ U).card else 0) =
      ∑ W ∈ (S \ M).powerset, (-1 : ℤ) ^ W.card := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun U _ => S \ U) ?_ ?_ ?_ ?_
  · intro U hU
    obtain ⟨hUS, hMU⟩ := Finset.mem_filter.mp hU
    apply Finset.mem_powerset.mpr
    intro x hx
    obtain ⟨hxS, hxU⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨hxS, fun hxM => hxU (hMU hxM)⟩
  · intro U hU W hW heq
    have hUS := Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1
    have hWS := Finset.mem_powerset.mp (Finset.mem_filter.mp hW).1
    have h := congrArg (fun T : Finset V => S \ T) heq
    simpa only [Finset.sdiff_sdiff_eq_self hUS,
      Finset.sdiff_sdiff_eq_self hWS] using h
  · intro W hW
    have hWsub := Finset.mem_powerset.mp hW
    have hWS : W ⊆ S := hWsub.trans Finset.sdiff_subset
    refine ⟨S \ W, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
      Finset.sdiff_subset, ?_⟩, Finset.sdiff_sdiff_eq_self hWS⟩
    intro x hxM
    refine Finset.mem_sdiff.mpr ⟨hMS hxM, ?_⟩
    intro hxW
    exact (Finset.mem_sdiff.mp (hWsub hxW)).2 hxM
  · intro U hU
    rfl

theorem sum_supersets_complement_sign_eq_zero (S M : Finset V)
    (hMS : M ⊆ S) (hne : M ≠ S) :
    (∑ U ∈ S.powerset, if M ⊆ U then (-1 : ℤ) ^ (S \ U).card else 0) = 0 := by
  rw [sum_supersets_complement_sign S M hMS]
  apply Finset.sum_powerset_neg_one_pow_card_of_nonempty
  apply Finset.sdiff_nonempty.mpr
  intro hSM
  exact hne (Finset.Subset.antisymm hMS hSM)

/-- The DAG evaluation under the exact hereditary source condition used in the induction. -/
theorem signedSum_eq_of_sources (R : V → V → Prop) (S : Finset V)
    (hsource : ∀ T ⊆ S, T.Nonempty → edgeHeads R T ≠ T) :
    signedSum R S = if Edgeless R S then (-1 : ℤ) ^ S.card else 0 := by
  revert hsource
  refine Finset.strongInductionOn S ?_
  intro S ih hsource
  by_cases hS : S = ∅
  · subst S
    simp [Edgeless]
  have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
  let M := edgeHeads R S
  let f : Finset V → ℤ := fun U => if M ⊆ U then (-1 : ℤ) ^ (S \ U).card else 0
  have hzero : (∑ U ∈ S.powerset, f U) = 0 :=
    sum_supersets_complement_sign_eq_zero S M (edgeHeads_subset R S)
      (hsource S Finset.Subset.rfl hSne)
  have htop : topBlocks R S =
      (S.powerset.erase ∅).filter (UpClosed R S) := by
    ext U
    simp only [mem_topBlocks, Finset.mem_filter, Finset.mem_erase, Finset.mem_powerset,
      Finset.nonempty_iff_ne_empty]
    tauto
  have hsum : (∑ U ∈ topBlocks R S, signedSum R (S \ U)) =
      ∑ U ∈ S.powerset.erase ∅, f U := by
    rw [htop, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro U hU
    obtain ⟨hUne, hUS⟩ := Finset.mem_erase.mp hU
    have hsub := Finset.mem_powerset.mp hUS
    by_cases hup : UpClosed R S U
    · rw [ite_eq_left hup]
      have hrec := ih (S \ U)
        (Finset.sdiff_ssubset hsub (Finset.nonempty_iff_ne_empty.mpr hUne))
        (fun T hT hne => hsource T (hT.trans Finset.sdiff_subset) hne)
      rw [hrec]
      have hiff : Edgeless R (S \ U) ↔ M ⊆ U := by
        constructor
        · intro he
          exact (upClosed_edgeless_sdiff_iff R S U hsub).mp ⟨hup, he⟩
        · intro hm
          exact ((upClosed_edgeless_sdiff_iff R S U hsub).mpr hm).2
      simp only [f, hiff]
    · have hnot : ¬ M ⊆ U := by
        intro hm
        exact hup ((upClosed_edgeless_sdiff_iff R S U hsub).mpr hm).1
      simp only [f, ite_eq_right hup, ite_eq_right hnot]
  have herase := Finset.sum_erase_add S.powerset f (Finset.empty_mem_powerset S)
  rw [hzero] at herase
  have hfempty : f ∅ = if Edgeless R S then (-1 : ℤ) ^ S.card else 0 := by
    simp only [f, M, Finset.subset_empty, Finset.sdiff_empty, edgeHeads_eq_empty_iff]
  rw [signedSum_top_recursion R hSne, hsum, ← hfempty]
  lia

/-- An acyclic relation has a source in each finite nonempty induced subgraph. -/
theorem edgeHeads_ne_of_acyclic (R : V → V → Prop)
    (hacyclic : ∀ v, ¬ Relation.TransGen R v v) (S : Finset V) (hS : S.Nonempty) :
    edgeHeads R S ≠ S := by
  letI : IsStrictOrder V (Relation.TransGen R) :=
    { irrefl := hacyclic
      trans := fun _ _ _ h₁ h₂ => h₁.trans h₂ }
  have hw : WellFounded (fun x y : V =>
      Relation.TransGen R x y ∧ x ∈ S ∧ y ∈ S) :=
    Set.wellFoundedOn_iff.mp (S.wellFoundedOn (r := Relation.TransGen R))
  obtain ⟨v, hv, hmin⟩ := hw.has_min (S : Set V) hS
  intro heq
  have hvhead : v ∈ edgeHeads R S := by rw [heq]; exact hv
  obtain ⟨_, x, hx, hxv⟩ := Finset.mem_filter.mp hvhead
  exact hmin x hx ⟨Relation.TransGen.single hxv, hx, hv⟩

/-- Lemma A for a finite DAG: the actual signed partition sum vanishes as soon
as there is an edge, and equals the vertex parity for an edgeless graph. -/
theorem signedSum_eq_of_acyclic (R : V → V → Prop)
    (hacyclic : ∀ v, ¬ Relation.TransGen R v v) (S : Finset V) :
    signedSum R S = if Edgeless R S then (-1 : ℤ) ^ S.card else 0 := by
  exact signedSum_eq_of_sources R S
    (fun T _ hT => edgeHeads_ne_of_acyclic R hacyclic T hT)

end

end VerticalStripLLT.Components.OrderedPartitions
