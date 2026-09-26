import VerticalStripLLT.Circular.CornerDiagram

/-! Lower a strict edge across its predecessor contact. -/

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ} (D : Diagram n)

noncomputable def loweredEdge (i : Fin n) (g : Edge D.area) (hg : g ∈ D.strict)
    (_gh : g.head = D.area.next i)
    (heq : D.area.area g.head = D.area.area i + 1)
    (hpos : 1 ≤ D.area.area i) : Edge (D.cornerArea g (D.strict_corner g hg)) := by
  have hi : i ≠ g.head := by
    intro h
    rw [h] at heq
    lia
  refine ⟨(i, ⟨D.area.area i, D.area.bound i⟩), by lia, ?_⟩
  change D.area.area i ≤ (D.area.lowerAt g.head _ _).area i
  rw [CircularArea.lowerAt_area_of_ne _ _ _ _ hi]

theorem loweredEdge_head (i : Fin n) (g : Edge D.area) (hg : g ∈ D.strict)
    (gh : g.head = D.area.next i) (heq : D.area.area g.head = D.area.area i + 1)
    (hpos : 1 ≤ D.area.area i) :
    (D.loweredEdge i g hg gh heq hpos).head = i := rfl

theorem loweredEdge_length (i : Fin n) (g : Edge D.area) (hg : g ∈ D.strict)
    (gh : g.head = D.area.next i) (heq : D.area.area g.head = D.area.area i + 1)
    (hpos : 1 ≤ D.area.area i) :
    (D.loweredEdge i g hg gh heq hpos).length.val = D.area.area i := rfl

theorem loweredEdge_corner (i : Fin n) (g : Edge D.area) (hg : g ∈ D.strict)
    (gh : g.head = D.area.next i) (heq : D.area.area g.head = D.area.area i + 1)
    (hpos : 1 ≤ D.area.area i) :
    IsCorner (D.loweredEdge i g hg gh heq hpos) := by
  have hi : i ≠ g.head := by
    intro h
    rw [h] at heq
    lia
  constructor
  · change D.area.area i = (D.area.lowerAt g.head _ _).area i
    rw [CircularArea.lowerAt_area_of_ne _ _ _ _ hi]
  · change (D.area.lowerAt g.head _ _).area (D.area.next i) ≤
      (D.area.lowerAt g.head _ _).area i
    rw [← gh, CircularArea.lowerAt_area_self]
    rw [heq]
    rw [CircularArea.lowerAt_area_of_ne _ _ _ _ hi]
    lia

noncomputable def lowerStrict (i : Fin n) (g : Edge D.area) (hg : g ∈ D.strict)
    (gh : g.head = D.area.next i) (heq : D.area.area g.head = D.area.area i + 1)
    (hpos : 1 ≤ D.area.area i) : Diagram n :=
  (D.deleteCorner g (D.strict_corner g hg)).strictify
    (D.loweredEdge i g hg gh heq hpos)
    (D.loweredEdge_corner i g hg gh heq hpos)

theorem lowerStrict_area (i : Fin n) (g : Edge D.area) (hg : g ∈ D.strict)
    (gh : g.head = D.area.next i) (heq : D.area.area g.head = D.area.area i + 1)
    (hpos : 1 ≤ D.area.area i) :
    (D.lowerStrict i g hg gh heq hpos).area.area =
      Function.update D.area.area g.head (D.area.area g.head - 1) := rfl

theorem loweredEdge_tail (i : Fin n) (g : Edge D.area) (hg : g ∈ D.strict)
    (gh : g.head = D.area.next i) (heq : D.area.area g.head = D.area.area i + 1)
    (hpos : 1 ≤ D.area.area i) :
    (D.loweredEdge i g hg gh heq hpos).tail = g.tail := by
  have hlen : g.length.val = D.area.area i + 1 := by
    rw [(D.strict_corner g hg).1, heq]
  have hlt : D.area.area i + 1 < n := by
    rw [← heq]
    exact D.area.bound g.head
  apply Fin.ext
  change (i.val + n - D.area.area i) % n =
    (g.head.val + n - g.length.val) % n
  rw [gh, hlen]
  simp only [CircularArea.next_val]
  by_cases hlast : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlast]
    congr 1
    lia
  · have hi : i.val = n - 1 := by lia
    rw [hi]
    have hrem : n - 1 - D.area.area i < n := by lia
    rw [show n - 1 + 1 = n by lia, Nat.mod_self, Nat.zero_add]
    rw [show n - 1 + n - D.area.area i = n + (n - 1 - D.area.area i) by lia,
      Nat.add_mod_left, Nat.mod_eq_of_lt hrem,
      Nat.mod_eq_of_lt (show n - (D.area.area i + 1) < n by lia)]
    lia

end VerticalStripLLT.Circular.Diagram
