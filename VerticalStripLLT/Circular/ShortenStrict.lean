import VerticalStripLLT.Circular.CornerDiagram

/-! A valid successor obtained by shortening a strict corner edge. -/

namespace VerticalStripLLT.Circular
namespace Diagram

variable {n : ℕ} (D : Diagram n)

/-- The shortened edge in the diagram obtained by deleting a strict corner. -/
def shortenedEdge (e : Edge D.area) (he : e ∈ D.strict) (hlen : 2 ≤ e.length.val) :
    Edge (D.cornerArea e (D.strict_corner e he)) :=
  ⟨(e.head, ⟨e.length.val - 1, by have := e.length_lt_n; lia⟩), by
    constructor
    · change 0 < e.length.val - 1
      lia
    · change e.length.val - 1 ≤ (D.area.lowerAt e.head _ _).area e.head
      rw [CircularArea.lowerAt_area_self, (D.strict_corner e he).1]⟩

@[simp] theorem shortenedEdge_head (e : Edge D.area) (he : e ∈ D.strict)
    (hlen : 2 ≤ e.length.val) : (D.shortenedEdge e he hlen).head = e.head := rfl

@[simp] theorem shortenedEdge_length (e : Edge D.area) (he : e ∈ D.strict)
    (hlen : 2 ≤ e.length.val) :
    (D.shortenedEdge e he hlen).length.val = e.length.val - 1 := rfl

theorem shortenedEdge_isCorner (e : Edge D.area) (he : e ∈ D.strict)
    (hlen : 2 ≤ e.length.val)
    (hgap : D.area.area (D.area.next e.head) < D.area.area e.head) :
    IsCorner (D.shortenedEdge e he hlen) := by
  have hc := D.strict_corner e he
  have hne : D.area.next e.head ≠ e.head := by
    intro h
    rw [h] at hgap
    exact (lt_irrefl _) hgap
  constructor
  · change e.length.val - 1 = (D.area.lowerAt e.head _ _).area e.head
    rw [CircularArea.lowerAt_area_self, hc.1]
  · change (D.area.lowerAt e.head _ _).area (D.area.next e.head) ≤
      (D.area.lowerAt e.head _ _).area e.head
    rw [CircularArea.lowerAt_area_of_ne _ _ _ _ hne, CircularArea.lowerAt_area_self]
    lia

noncomputable def shortenStrict (e : Edge D.area) (he : e ∈ D.strict)
    (hlen : 2 ≤ e.length.val)
    (hgap : D.area.area (D.area.next e.head) < D.area.area e.head) : Diagram n :=
  (D.deleteCorner e (D.strict_corner e he)).strictify (D.shortenedEdge e he hlen)
    (D.shortenedEdge_isCorner e he hlen hgap)

theorem shortenStrict_area (e : Edge D.area) (he : e ∈ D.strict)
    (hlen : 2 ≤ e.length.val)
    (hgap : D.area.area (D.area.next e.head) < D.area.area e.head) :
    (D.shortenStrict e he hlen hgap).area = D.cornerArea e (D.strict_corner e he) := rfl

theorem shortenStrict_edge_length (e : Edge D.area) (he : e ∈ D.strict)
    (hlen : 2 ≤ e.length.val) :
    (D.shortenedEdge e he hlen).length.val + 1 = e.length.val := by
  rw [D.shortenedEdge_length]
  lia

theorem shortenStrict_strict_mem (e : Edge D.area) (he : e ∈ D.strict)
    (hlen : 2 ≤ e.length.val)
    (hgap : D.area.area (D.area.next e.head) < D.area.area e.head)
    (g : Edge (D.cornerArea e (D.strict_corner e he))) :
    g ∈ (D.shortenStrict e he hlen hgap).strict ↔
      g = D.shortenedEdge e he hlen ∨ D.cornerIncl e (D.strict_corner e he) g ∈ D.strict := by
  change g ∈ insert (D.shortenedEdge e he hlen)
    (Finset.univ.filter fun f => D.cornerIncl e (D.strict_corner e he) f ∈ D.strict) ↔ _
  simp

theorem shortened_old_edge_not_strict (e : Edge D.area) (he : e ∈ D.strict)
    (hlen : 2 ≤ e.length.val) :
    D.cornerIncl e (D.strict_corner e he) (D.shortenedEdge e he hlen) ∉ D.strict := by
  intro hf
  have hc := D.strict_corner _ hf
  have hlen' := hc.1
  change e.length.val - 1 = D.area.area e.head at hlen'
  have heq := (D.strict_corner e he).1
  lia

end Diagram
end VerticalStripLLT.Circular
