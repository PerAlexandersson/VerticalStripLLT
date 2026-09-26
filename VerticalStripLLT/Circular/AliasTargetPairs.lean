import VerticalStripLLT.Circular.AliasTarget
import VerticalStripLLT.Circular.PairColoringBridge
import VerticalStripLLT.Circular.EdgeLength
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith

/-! Strict endpoint pairs for the overlapping ND target. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular
namespace Diagram

open scoped Classical

variable {n : ℕ} (D : Diagram n)
  (i : Fin n) (f : Edge D.area) (hf : f ∈ D.strict)
  (hi : D.area.next i = f.head)
  (harea : D.area.area f.head = D.area.area i + 1)
  (hlen : 3 ≤ f.length.val)
  (hgap : D.area.area (D.area.next f.head) < D.area.area f.head)

theorem aliasEdge_head :
    (D.aliasEdge i f hf hi harea hlen hgap).head = i := rfl

theorem aliasEdge_length_add_two :
    (D.aliasEdge i f hf hi harea hlen hgap).length.val + 2 = f.length.val := by
  have hc := (D.strict_corner f hf).1
  change D.area.area i - 1 + 2 = f.length.val
  lia

theorem aliasEdge_tail :
    (D.aliasEdge i f hf hi harea hlen hgap).tail = D.area.next f.tail := by
  let g := D.aliasEdge i f hf hi harea hlen hgap
  have hlen' := D.aliasEdge_length_add_two i f hf hi harea hlen hgap
  have hm : g.tail.val + (g.length.val + 1) ≡
      (D.area.next f.tail).val + (g.length.val + 1) [MOD n] := by
    change (g.tail.val + (g.length.val + 1)) % n =
      ((D.area.next f.tail).val + (g.length.val + 1)) % n
    calc
      _ = (g.head.val + 1) % n := by
        rw [← Nat.add_assoc, Nat.add_mod, g.tail_add_length_mod]
        simpa only [Nat.mod_eq_of_lt g.head.isLt] using
          (Nat.add_mod g.head.val 1 n).symm
      _ = f.head.val := by
        change (i.val + 1) % n = f.head.val
        exact congrArg Fin.val hi
      _ = (f.tail.val + f.length.val) % n := f.tail_add_length_mod.symm
      _ = ((D.area.next f.tail).val + (g.length.val + 1)) % n := by
        change (f.tail.val + f.length.val) % n =
          ((f.tail.val + 1) % n + (g.length.val + 1)) % n
        rw [Nat.mod_add_mod]
        congr 1
        change g.length.val + 2 = f.length.val at hlen'
        lia
  have hc := Nat.ModEq.add_right_cancel' (g.length.val + 1) hm
  apply Fin.ext
  change g.tail.val = (f.tail.val + 1) % n
  exact hc.eq_of_lt_of_lt g.tail.isLt (D.area.next f.tail).isLt

theorem aliasTarget_pairGraph_strictEdges
    (hheads : ∀ g ∈ D.strict, g.head ≠ i) :
    (D.aliasTarget i f hf hi harea hlen hgap hheads).pairGraph.strictEdges =
      insert (D.area.next f.tail, i)
        (D.pairGraph.strictEdges.erase (f.tail, f.head)) := by
  classical
  let Q := D.aliasTarget i f hf hi harea hlen hgap hheads
  let r := D.aliasEdge i f hf hi harea hlen hgap
  have hr : (r.tail, r.head) = (D.area.next f.tail, i) := by
    exact Prod.ext (D.aliasEdge_tail i f hf hi harea hlen hgap) rfl
  ext x
  rw [Q.mem_pairGraph_strict_iff, Finset.mem_insert, Finset.mem_erase,
    D.mem_pairGraph_strict_iff]
  constructor
  · rintro ⟨g, hg, hp⟩
    rcases Finset.mem_insert.mp hg with hgr | hg
    · left
      subst g
      exact hp.symm.trans hr
    · right
      have hmem := (Finset.mem_filter.mp hg).2
      refine ⟨?_, ⟨D.aliasIncl i f hf hi harea hlen hgap g, hmem, ?_⟩⟩
      · intro hbad
        have hhead : g.head = f.head := congrArg Prod.snd (hp.trans hbad)
        have hlenbad : g.length.val = f.length.val := by
          exact Edge.length_eq_of_endpoints
            (congrArg Prod.fst (hp.trans hbad)) hhead
        have hbound := g.property.2
        change g.length.val ≤ D.area.aliasLowerValues i f.head g.head at hbound
        rw [hhead, D.area.aliasLowerValues_right i f.head
          (by intro h; rw [h] at harea; lia)] at hbound
        have hcf := (D.strict_corner f hf).1
        lia
      · exact hp
  · rintro (hx | ⟨hne, hx⟩)
    · refine ⟨r, ?_, hr.trans hx.symm⟩
      exact Finset.mem_insert.mpr (Or.inl rfl)
    · obtain ⟨a, ha, hpair⟩ := hx
      have hae : a ≠ f := by
        intro haf
        subst a
        exact hne hpair.symm
      have hai : a.head ≠ i := hheads a ha
      have hafh : a.head ≠ f.head := by
        intro hh
        exact hae (D.strict_edge_eq_of_head_eq ha hf hh)
      let g : Edge Q.area :=
        ⟨a.val, a.property.1, by
          change a.length.val ≤ D.area.aliasLowerValues i f.head a.head
          rw [D.area.aliasLowerValues_other i f.head a.head hai hafh]
          exact a.property.2⟩
      refine ⟨g, ?_, ?_⟩
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨by
          exact Finset.mem_univ _, by change a ∈ D.strict; exact ha⟩))
      · exact hpair

end Diagram
end VerticalStripLLT.Circular
