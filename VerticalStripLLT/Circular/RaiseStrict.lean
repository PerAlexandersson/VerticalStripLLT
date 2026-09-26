import VerticalStripLLT.Circular.CornerDiagram
import VerticalStripLLT.Circular.CutOrder
import VerticalStripLLT.Circular.StrictEdgeInjectivity

/-! Moving a strict corner across a DN contact by raising the next row. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular

open scoped Classical

namespace CircularArea

variable {n : ℕ}

theorem next_injective (A : CircularArea n) : Function.Injective A.next := by
  intro i j hij
  apply Fin.ext
  have hm : i.val + 1 ≡ j.val + 1 [MOD n] := congrArg Fin.val hij
  have hc := Nat.ModEq.add_right_cancel' 1 hm
  exact hc.eq_of_lt_of_lt i.isLt j.isLt

/-- Increase the successor row across two equal consecutive areas. -/
def raiseNext (A : CircularArea n) (h : Fin n)
    (heq : A.area (A.next h) = A.area h) (hbound : A.area h + 1 < n) :
    CircularArea n where
  positive := A.positive
  area := Function.update A.area (A.next h) (A.area h + 1)
  bound := by
    intro i
    by_cases hi : i = A.next h
    · subst i; simp only [Function.update_self]; exact hbound
    · rw [Function.update_of_ne hi]; exact A.bound i
  cyclic := by
    intro i
    change Function.update A.area (A.next h) (A.area h + 1) (A.next i) ≤
      Function.update A.area (A.next h) (A.area h + 1) i + 1
    have hc := A.cyclic i
    by_cases hi : i = A.next h
    · rw [hi, Function.update_self]
      by_cases hj : A.next (A.next h) = A.next h
      · rw [hj, Function.update_self]; lia
      · rw [Function.update_of_ne hj]
        rw [hi, heq] at hc
        exact hc.trans (by lia)
    · rw [Function.update_of_ne hi]
      by_cases hj : A.next i = A.next h
      · have hh := A.next_injective hj
        rw [hj, Function.update_self, hh]
      · rw [Function.update_of_ne hj]; exact hc

theorem raiseNext_area_le (A : CircularArea n) (h : Fin n)
    (heq : A.area (A.next h) = A.area h) (hbound : A.area h + 1 < n) (i : Fin n) :
    A.area i ≤ (A.raiseNext h heq hbound).area i := by
  change A.area i ≤ Function.update A.area (A.next h) (A.area h + 1) i
  by_cases hi : i = A.next h
  · rw [hi, Function.update_self, heq]; lia
  · rw [Function.update_of_ne hi]

end CircularArea

namespace Diagram

variable {n : ℕ} (D : Diagram n)

noncomputable def raisedIncl (e : Edge D.area)
    (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
    (hb : D.area.area e.head + 1 < n) :
    Edge D.area ↪ Edge (D.area.raiseNext e.head heq hb) where
  toFun g := ⟨g.1, g.2.1, g.2.2.trans (D.area.raiseNext_area_le e.head heq hb g.head)⟩
  inj' := by
    intro g h hgh
    exact Subtype.ext (congrArg (fun x : Edge (D.area.raiseNext e.head heq hb) => x.val) hgh)

noncomputable def raisedEdge (e : Edge D.area) (he : e ∈ D.strict)
    (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
    (hb : D.area.area e.head + 1 < n) : Edge (D.area.raiseNext e.head heq hb) :=
  ⟨(D.area.next e.head, ⟨e.length.val + 1, by rw [(D.strict_corner e he).1]; exact hb⟩),
    by simp, by
      change e.length.val + 1 ≤ Function.update D.area.area (D.area.next e.head)
        (D.area.area e.head + 1) (D.area.next e.head)
      rw [Function.update_self, (D.strict_corner e he).1]⟩

theorem raisedEdge_corner (e : Edge D.area) (he : e ∈ D.strict)
    (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
    (hb : D.area.area e.head + 1 < n) : IsCorner (D.raisedEdge e he heq hb) := by
  constructor
  · change e.length.val + 1 = Function.update D.area.area (D.area.next e.head)
      (D.area.area e.head + 1) (D.area.next e.head)
    rw [Function.update_self, (D.strict_corner e he).1]
  · change Function.update D.area.area (D.area.next e.head) (D.area.area e.head + 1)
      (D.area.next (D.area.next e.head)) ≤
        Function.update D.area.area (D.area.next e.head) (D.area.area e.head + 1)
          (D.area.next e.head)
    rw [Function.update_self]
    by_cases hh : D.area.next (D.area.next e.head) = D.area.next e.head
    · rw [hh, Function.update_self]
    · rw [Function.update_of_ne hh]
      have hc : D.area.area (D.area.next (D.area.next e.head)) ≤
          D.area.area (D.area.next e.head) + 1 := D.area.cyclic (D.area.next e.head)
      rwa [heq] at hc

theorem raisedIncl_corner (e : Edge D.area) (he : e ∈ D.strict)
    (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
    (hb : D.area.area e.head + 1 < n)
    (hns : ∀ f ∈ D.strict, f.head ≠ D.area.next e.head)
    {f : Edge D.area} (hf : f ∈ D.strict) (hne : f ≠ e) :
    IsCorner (D.raisedIncl e heq hb f) := by
  have hh := hns f hf
  have hp : D.area.next f.head ≠ D.area.next e.head := by
    intro h
    exact hne (D.strict_edge_eq_of_head_eq hf he (D.area.next_injective h))
  obtain ⟨hl, hc⟩ := D.strict_corner f hf
  constructor
  · change f.length.val = Function.update D.area.area (D.area.next e.head)
      (D.area.area e.head + 1) f.head
    rw [Function.update_of_ne hh]; exact hl
  · change Function.update D.area.area (D.area.next e.head) (D.area.area e.head + 1)
      (D.area.next f.head) ≤
        Function.update D.area.area (D.area.next e.head) (D.area.area e.head + 1) f.head
    rw [Function.update_of_ne hp, Function.update_of_ne hh]
    exact hc

noncomputable def raiseStrict (e : Edge D.area) (he : e ∈ D.strict)
    (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
    (hb : D.area.area e.head + 1 < n)
    (hns : ∀ f ∈ D.strict, f.head ≠ D.area.next e.head) : Diagram n where
  area := D.area.raiseNext e.head heq hb
  strict := insert (D.raisedEdge e he heq hb) ((D.strict.erase e).map (D.raisedIncl e heq hb))
  strict_corner := by
    intro f hf
    obtain rfl | hf := Finset.mem_insert.mp hf
    · exact D.raisedEdge_corner e he heq hb
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp hf
      exact D.raisedIncl_corner e he heq hb hns (Finset.mem_erase.mp hg).2
        (Finset.mem_erase.mp hg).1

theorem raiseStrict_strict_mem (e : Edge D.area) (he : e ∈ D.strict)
    (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
    (hb : D.area.area e.head + 1 < n)
    (hns : ∀ f ∈ D.strict, f.head ≠ D.area.next e.head)
    (g : Edge (D.raiseStrict e he heq hb hns).area) :
    g ∈ (D.raiseStrict e he heq hb hns).strict ↔ g = D.raisedEdge e he heq hb ∨
      ∃ f ∈ D.strict, f ≠ e ∧ D.raisedIncl e heq hb f = g := by
  simp only [raiseStrict, Finset.mem_insert, Finset.mem_map, Finset.mem_erase]
  tauto

end Diagram
end VerticalStripLLT.Circular
