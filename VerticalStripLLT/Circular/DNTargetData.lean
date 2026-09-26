import VerticalStripLLT.Circular.DNSwapGeometry
import VerticalStripLLT.Circular.DNNormalPairs

set_option backward.isDefEq.respectTransparency false

-- NEW MODULE VerticalStripLLT.Circular.DNTargetData

/-! Endpoint pairs of the DN target diagram, written in terms of the source. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

namespace Diagram

variable {n : ℕ}

variable (D : Diagram n)

section DN

variable (e f : Edge D.area) (he : e ∈ D.strict) (hf : f ∈ D.strict) (hne : f ≠ e)
  (hcontact : f.tail = e.head)
  (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
  (hb : D.area.area e.head + 1 < n)
  (hns : ∀ g ∈ D.strict, g.head ≠ D.area.next e.head)
  (hlen : 2 ≤ f.length.val)
  (hgap : D.area.area (D.area.next f.head) < D.area.area f.head)

include hcontact in
theorem dn_target_strict :
    (D.dnSuccessor e f he hf hne heq hb hns hlen hgap).pairGraph.strictEdges = D.dnSt' e f := by
  rw [dnSuccessor_pairGraph_strictEdges, hcontact]
  rfl

theorem dn_AI_nat : (e.tail, e.head) ∈ D.naturalPairs :=
  (D.mem_naturalPairs_iff _).mpr ⟨e, rfl⟩

include he heq in
theorem dn_IY_nat : (e.head, D.area.next e.head) ∈ D.naturalPairs :=
  (D.mem_naturalPairs_iff _).mpr ⟨D.dnG e he heq, by rw [dnG_tail, dnG_head]⟩

include hf hcontact hlen in
theorem dn_YZ_nat : (D.area.next e.head, f.head) ∈ D.naturalPairs :=
  (D.mem_naturalPairs_iff _).mpr ⟨D.dnH e f hf hcontact hlen, by rw [dnH_tail, dnH_head]⟩

include hns in
theorem dn_IY_not_strict : (e.head, D.area.next e.head) ∉ D.pairGraph.strictEdges := by
  intro h
  obtain ⟨s, hs, hp⟩ := (D.mem_pairGraph_strict_iff _).mp h
  exact hns s hs (congrArg Prod.snd hp)

include he hf hcontact hb in
theorem dn_YZ_not_strict : (D.area.next e.head, f.head) ∉ D.pairGraph.strictEdges := by
  intro h
  obtain ⟨s, hs, hp⟩ := (D.mem_pairGraph_strict_iff _).mp h
  have hsf : s = f := D.strict_edge_eq_of_head_eq hs hf (congrArg Prod.snd hp)
  have ht : s.tail = D.area.next e.head := congrArg Prod.fst hp
  apply D.dn_Y_ne_I e he hb
  rw [← ht, hsf, hcontact]

include he heq in
theorem dn_AY_not_nat : (e.tail, D.area.next e.head) ∉ D.naturalPairs := by
  intro h
  obtain ⟨ε, hp⟩ := (D.mem_naturalPairs_iff _).mp h
  obtain ⟨ht, hh⟩ := Prod.mk.inj hp
  have hl := Edge.length_succ_of_next_head ht hh
  have hle := ε.length_le_area
  rw [hh, heq, ← D.dn_Le e he, hl] at hle
  exact Nat.not_succ_le_self _ hle

include he heq hns in
theorem dn_IY_mem_N : (e.head, D.area.next e.head) ∈ D.pairGraph.normalEdges := by
  rw [normalPairs_eq_sdiff, Finset.mem_sdiff]
  exact ⟨D.dn_IY_nat e he heq, D.dn_IY_not_strict e hns⟩

include he hf hcontact hb hlen in
theorem dn_YZ_mem_N : (D.area.next e.head, f.head) ∈ D.pairGraph.normalEdges := by
  rw [normalPairs_eq_sdiff, Finset.mem_sdiff]
  exact ⟨D.dn_YZ_nat e f hf hcontact hlen, D.dn_YZ_not_strict e f he hf hcontact hb⟩

include he hf hcontact heq hb hns hlen in
theorem dn_N_eq : D.pairGraph.normalEdges =
    insert (e.head, D.area.next e.head) (insert (D.area.next e.head, f.head) (D.dnB e f)) := by
  have hIY := D.dn_Y_ne_I e he hb
  rw [dnB, Finset.insert_erase (Finset.mem_erase.mpr ⟨fun h => hIY (Prod.mk.inj h).1,
    D.dn_YZ_mem_N e f he hf hcontact hb hlen⟩), Finset.insert_erase (D.dn_IY_mem_N e he heq hns)]

include he hf hcontact heq hb hns hlen in
theorem dn_target_normal :
    (D.dnSuccessor e f he hf hne heq hb hns hlen hgap).pairGraph.normalEdges =
      insert (e.tail, e.head) (insert (e.head, D.area.next e.head) (D.dnB e f)) := by
  rw [D.dnSuccessor_pairGraph_normalEdges, hcontact,
    D.dn_N_eq e f he hf hcontact heq hb hns hlen]
  have hp : (e.head, D.area.next e.head) ≠ (D.area.next e.head, f.head) := by
    intro h
    exact D.dn_Y_ne_I e he hb (congrArg Prod.fst h).symm
  rw [Finset.erase_insert_of_ne hp, Finset.erase_insert]
  exact fun h => ((D.mem_dnB_iff e f _).mp h).1 rfl


end DN

end Diagram

end VerticalStripLLT.Circular

