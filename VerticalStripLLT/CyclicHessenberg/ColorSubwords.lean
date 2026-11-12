import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sublists
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false

/-! Pure finite-list facts relating full colored subwords and colorings. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

/-- A full word lists every vertex exactly once. -/
def IsFullWord {V : Type*} (l : List V) : Prop :=
  l.Nodup ∧ ∀ v, v ∈ l

/-- Keep the entries whose color agrees with the assigned color of their vertex. -/
noncomputable def selectedColorSubword {C V : Type*} (L : List (C × V)) (c : V → C) :
    List (C × V) :=
  by
    classical
    exact L.filter (fun p => c p.2 = p.1)

theorem selectedColorSubword_sublist {C V : Type*} (L : List (C × V)) (c : V → C) :
    (selectedColorSubword L c).Sublist L :=
  List.filter_sublist

theorem fullWord_map_snd_selectedColorSubword {C V : Type*}
    {L : List (C × V)} (hL : IsFullWord L) (c : V → C) :
    IsFullWord ((selectedColorSubword L c).map Prod.snd) := by
  classical
  constructor
  · apply List.Nodup.map_on
    · intro p hp q hq heq
      have hp' : c p.2 = p.1 := by
        simpa [selectedColorSubword] using (List.mem_filter.mp hp).2
      have hq' : c q.2 = q.1 := by
        simpa [selectedColorSubword] using (List.mem_filter.mp hq).2
      apply Prod.ext
      · calc
          p.1 = c p.2 := hp'.symm
          _ = c q.2 := by rw [heq]
          _ = q.1 := hq'
      · exact heq
    · exact hL.1.filter _
  · intro v
    have hp : (c v, v) ∈ L := hL.2 (c v, v)
    have hp' : (c v, v) ∈ selectedColorSubword L c :=
      List.mem_filter_of_mem hp (by simp)
    exact List.mem_map.mpr ⟨(c v, v), hp', rfl⟩

theorem existsUnique_selectedColorSubword {C V : Type*}
    {L : List (C × V)} (hL : IsFullWord L) {S : List (C × V)}
    (hSsub : S.Sublist L) (hS : IsFullWord (S.map Prod.snd)) :
    ∃! c : V → C, S = selectedColorSubword L c := by
  classical
  have hv (v : V) : ∃ x : C, ∃ p : C × V, p ∈ S ∧ p = (x, v) := by
    obtain ⟨p, hp, hpv⟩ := List.mem_map.mp (hS.2 v)
    refine ⟨p.1, p, hp, ?_⟩
    exact Prod.ext rfl hpv
  let c : V → C := fun v => Classical.choose (hv v)
  have hc_spec (v : V) : ∃ p : C × V, p ∈ S ∧ p = (c v, v) := by
    exact Classical.choose_spec (hv v)
  have hcolor {p : C × V} (hp : p ∈ S) : c p.2 = p.1 := by
    obtain ⟨q, hq, hqp⟩ := hc_spec p.2
    have hqeq : q = p :=
      List.inj_on_of_nodup_map hS.1 hq hp (by simpa using congrArg Prod.snd hqp)
    have hpeq : p = (c p.2, p.2) := hqeq ▸ hqp
    exact (congrArg Prod.fst hpeq).symm
  have hmem (p : C × V) : p ∈ S ↔ p ∈ selectedColorSubword L c := by
    constructor
    · intro hp
      exact List.mem_filter_of_mem (hSsub.subset hp) (by simpa using hcolor hp)
    · intro hp
      have hpred : c p.2 = p.1 := by
        simpa [selectedColorSubword] using (List.mem_filter.mp hp).2
      obtain ⟨q, hq, hqp⟩ := hc_spec p.2
      have hqeq : q = p := by
        apply Prod.ext
        · simpa [hpred] using congrArg Prod.fst hqp
        · simpa using congrArg Prod.snd hqp
      exact hqeq ▸ hq
  have hTnodup : (selectedColorSubword L c).Nodup := by
    exact (fullWord_map_snd_selectedColorSubword hL c).1.of_map _
  have hperm : S.Perm (selectedColorSubword L c) :=
    (List.perm_ext_iff_of_nodup (hS.1.of_map _) hTnodup).2 hmem
  have heq : S = selectedColorSubword L c :=
    (List.Nodup.perm_iff_eq_of_sublist hL.1 hSsub
      (selectedColorSubword_sublist L c)).mp hperm
  refine ⟨c, heq, ?_⟩
  intro d hd
  funext v
  obtain ⟨p, hp, hpv⟩ := List.mem_map.mp (hS.2 v)
  have hpc : p ∈ selectedColorSubword L c := by simpa [heq] using hp
  have hpd : p ∈ selectedColorSubword L d := by simpa [hd] using hp
  have hpc' : c p.2 = p.1 := by
    simpa [selectedColorSubword] using (List.mem_filter.mp hpc).2
  have hpd' : d p.2 = p.1 := by
    simpa [selectedColorSubword] using (List.mem_filter.mp hpd).2
  simpa [hpv] using hpd'.trans hpc'.symm

private theorem sum_flatMap_pair {I A : Type*} [AddCommMonoid A] (L : List I)
    (f g : I → A) :
    (L.flatMap fun i => [f i, g i]).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => simp
  | cons i L ih => simp [ih, add_assoc, add_left_comm, add_comm]

/-- Expand an ordered product into the sum over all selected subwords. -/
theorem list_prod_one_add_eq_sum_subwords {I R : Type*} [Semiring R]
    (L : List I) (f : I → R) :
    (L.map (fun i => 1 + f i)).prod =
      (L.sublists.map fun S => (S.map f).prod).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, List.sublists_cons,
      List.bind_eq_flatMap, List.map_flatMap, List.map_nil]
    rw [sum_flatMap_pair, List.sum_map_mul_left, ← ih, add_mul, one_mul]

/-- Full subwords with a full vertex projection are uniquely indexed by colorings. -/
theorem sum_subwords_eq_sum_colorings {C V A : Type*}
    [Fintype C] [Fintype V] [DecidableEq C] [DecidableEq V] [AddCommMonoid A]
    (L : List (C × V)) (hL : IsFullWord L) (f : List (C × V) → A)
    (hf : ∀ S, ¬ IsFullWord (S.map Prod.snd) → f S = 0) :
    (L.sublists.map f).sum = ∑ c : V → C, f (selectedColorSubword L c) := by
  classical
  rw [← List.sum_toFinset f (List.nodup_sublists.mpr hL.1)]
  let T := L.sublists.toFinset.filter (fun S => IsFullWord (S.map Prod.snd))
  have hfilter : ∑ S ∈ L.sublists.toFinset, f S = ∑ S ∈ T, f S := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro S hS hnot
    exact hf S (fun h => hnot (Finset.mem_filter.mpr ⟨hS, h⟩))
  rw [hfilter]
  symm
  apply Finset.sum_bij (fun c _ => selectedColorSubword L c)
  · intro c _
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr
      (List.mem_sublists.mpr (selectedColorSubword_sublist L c)),
      fullWord_map_snd_selectedColorSubword hL c⟩
  · intro c _ d _ h
    obtain ⟨e, he, hu⟩ := existsUnique_selectedColorSubword hL
      (selectedColorSubword_sublist L c) (fullWord_map_snd_selectedColorSubword hL c)
    exact (hu c rfl).trans (hu d h).symm
  · intro S hS
    obtain ⟨hsub, hfull⟩ := Finset.mem_filter.mp hS
    obtain ⟨c, hc, _⟩ := existsUnique_selectedColorSubword hL
      (List.mem_sublists.mp (List.mem_toFinset.mp hsub)) hfull
    exact ⟨c, Finset.mem_univ c, hc.symm⟩
  · intro c _
    rfl

/-- The selected subword contains one entry for each vertex, with its assigned color. -/
theorem prod_selectedColorSubword {C V A : Type*}
    [Fintype C] [Fintype V] [DecidableEq C] [DecidableEq V] [CommMonoid A]
    (L : List (C × V)) (hL : IsFullWord L) (c : V → C) (weight : C → A) :
    ((selectedColorSubword L c).map (fun p => weight p.1)).prod =
      ∏ v, weight (c v) := by
  classical
  let S := selectedColorSubword L c
  have hfull := fullWord_map_snd_selectedColorSubword hL c
  have hmap : S.map (fun p => weight p.1) =
      (S.map Prod.snd).map (fun v => weight (c v)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro p hp
    have hc : c p.2 = p.1 := by
      simpa [S, selectedColorSubword] using (List.mem_filter.mp hp).2
    simp [hc]
  rw [hmap, ← List.prod_toFinset _ hfull.1]
  have huniv : (S.map Prod.snd).toFinset = Finset.univ := by
    ext v
    exact iff_of_true (List.mem_toFinset.mpr (hfull.2 v)) (Finset.mem_univ v)
  rw [huniv]

end VerticalStripLLT.CyclicHessenberg
