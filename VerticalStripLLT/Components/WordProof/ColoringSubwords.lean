import VerticalStripLLT.Components.WordProof.ComponentWords
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sublists

/-! Full subwords of a colored finite alphabet are indexed by colorings. -/

namespace VerticalStripLLT.Components

noncomputable section

variable {C V : Type*} [Fintype C] [Fintype V]
  [DecidableEq C] [DecidableEq V]

/-- Keep the entries of `L` whose color agrees with `c`. -/
def selectedColorSubword (L : List (C × V)) (c : V → C) : List (C × V) :=
  L.filter (fun p => c p.2 = p.1)

theorem selectedColorSubword_sublist (L : List (C × V)) (c : V → C) :
    (selectedColorSubword L c).Sublist L := by
  exact List.filter_sublist

theorem fullWord_map_snd_selectedColorSubword
    {L : List (C × V)} (hL : fullWord L) (c : V → C) :
    fullWord ((selectedColorSubword L c).map Prod.snd) := by
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

theorem existsUnique_selectedColorSubword
    {L : List (C × V)} (hL : fullWord L)
    {S : List (C × V)} (hSsub : S.Sublist L)
    (hS : fullWord (S.map Prod.snd)) :
    ∃! c : V → C, S = selectedColorSubword L c := by
  have hv (v : V) :
      ∃ x : C, ∃ p : C × V, p ∈ S ∧ p = (x, v) := by
    obtain ⟨p, hp, hpv⟩ := List.mem_map.mp (hS.2 v)
    refine ⟨p.1, p, hp, ?_⟩
    exact Prod.ext rfl hpv
  let c : V → C := fun v => Classical.choose (hv v)
  have hc_spec (v : V) :
      ∃ p : C × V, p ∈ S ∧ p = (c v, v) := by
    exact Classical.choose_spec (hv v)
  have hcolor {p : C × V} (hp : p ∈ S) : c p.2 = p.1 := by
    obtain ⟨q, hq, hqp⟩ := hc_spec p.2
    have hqeq : q = p :=
      List.inj_on_of_nodup_map hS.1 hq hp (by simpa using congrArg Prod.snd hqp)
    have hpeq : p = (c p.2, p.2) := hqeq ▸ hqp
    exact (congrArg Prod.fst hpeq).symm
  have hmem (p : C × V) :
      p ∈ S ↔ p ∈ selectedColorSubword L c := by
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

end

end VerticalStripLLT.Components
