import VerticalStripLLT.Components.DiagramProof.CopyGeometry
import VerticalStripLLT.Circular.EdgeLength

/-! Maximal-edge characterizations of natural corners in a forward diagram. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

variable {n : ℕ} {D : Diagram n}

private def topEdge (D : Diagram n) (v : Fin n) (hpos : 0 < D.area.area v) :
    Edge D.area :=
  ⟨(v, ⟨D.area.area v, D.area.bound v⟩), ⟨hpos, le_rfl⟩⟩

private theorem topEdge_head (D : Diagram n) (v : Fin n) (hpos : 0 < D.area.area v) :
    (topEdge D v hpos).head = v := rfl

private theorem topEdge_length (D : Diagram n) (v : Fin n) (hpos : 0 < D.area.area v) :
    (topEdge D v hpos).length.val = D.area.area v := rfl

private theorem area_le_head_of_forward (hD : Forward D) (v : Fin n) :
    D.area.area v ≤ v.val := by
  by_cases hv : D.area.area v = 0
  · simp [hv]
  · let f := topEdge D v (Nat.pos_of_ne_zero hv)
    have hforward := hD f
    have hlift := (D.naturalLift_of_tail_lt_head f hforward).2
    have htail : (f.tail.val : ℤ) ≤ v.val := by exact_mod_cast hforward.le
    have hlen : f.length.val = D.area.area v := topEdge_length D v _
    rw [topEdge_head] at hlift
    rw [hlen] at hlift
    exact_mod_cast (by linarith : (D.area.area v : ℤ) ≤ v.val)

/-- A corner is exactly an edge maximal at each of its two endpoints. -/
theorem isCorner_iff_extremal (hD : Forward D) (e : Edge D.area) :
    IsCorner e ↔
      (∀ f : Edge D.area, f.head = e.head → e.tail ≤ f.tail) ∧
      (∀ f : Edge D.area, f.tail = e.tail → f.head ≤ e.head) := by
  constructor
  · intro he
    let F := allCorners D
    have heF : e ∈ F.edges := Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
    constructor
    · intro f hh
      exact F.corner_tail_le_of_head_le hD heF (le_of_eq hh.symm)
    · intro f ht
      exact F.head_le_of_same_tail hD heF ht
  · rintro ⟨hhead, htail⟩
    have hepos : 0 < D.area.area e.head :=
      lt_of_lt_of_le e.length_pos e.length_le_area
    let f := topEdge D e.head hepos
    have hft : e.tail ≤ f.tail := hhead f (topEdge_head D e.head hepos)
    have helift := (D.naturalLift_of_tail_lt_head e (hD e)).2
    have hflift := (D.naturalLift_of_tail_lt_head f (hD f)).2
    have hfhead : f.head = e.head := rfl
    rw [hfhead] at hflift
    have hlen : f.length.val ≤ e.length.val := by
      have hft' : (e.tail.val : ℤ) ≤ f.tail.val := by exact_mod_cast hft
      exact_mod_cast (by linarith : (f.length.val : ℤ) ≤ e.length.val)
    have htop : D.area.area e.head ≤ e.length.val := by
      exact hlen
    have heq : e.length.val = D.area.area e.head :=
      le_antisymm e.length_le_area htop
    refine ⟨heq, ?_⟩
    by_contra hnext
    have hgt : D.area.area e.head < D.area.area (D.area.next e.head) :=
      lt_of_not_ge hnext
    have hheadlt : e.head.val + 1 < n := by
      by_contra hnot
      have hge : n ≤ e.head.val + 1 := le_of_not_gt hnot
      have hlast : e.head.val + 1 = n := by lia
      have hle := area_le_head_of_forward hD (D.area.next e.head)
      have hnextval : (D.area.next e.head).val = 0 := by
        rw [D.area.next_val, hlast, Nat.mod_self]
      rw [hnextval] at hle
      have hz : D.area.area (D.area.next e.head) = 0 := Nat.eq_zero_of_le_zero hle
      rw [hz] at hgt
      exact (not_lt_of_ge (Nat.zero_le _)) hgt
    have hlenle : e.length.val + 1 ≤ D.area.area (D.area.next e.head) := by
      rw [heq]
      exact hgt
    let g : Edge D.area :=
      ⟨(D.area.next e.head, ⟨e.length.val + 1, lt_of_le_of_lt hlenle
        (D.area.bound (D.area.next e.head))⟩), ⟨by lia, hlenle⟩⟩
    have gghead : g.head = D.area.next e.head := rfl
    have ggtail : g.tail = e.tail := by
      apply Fin.ext
      change ((e.head.val + 1) % n + n - (e.length.val + 1)) % n = e.tail.val
      rw [e.tail_val]
      have hsum := (D.naturalLift_of_tail_lt_head e (hD e)).2
      have hsum' : e.tail.val + e.length.val = e.head.val := by
        exact_mod_cast hsum.symm
      have hnext : (e.head.val + 1) % n = e.head.val + 1 := Nat.mod_eq_of_lt hheadlt
      rw [hnext]
      have hsub : e.head.val + 1 + n - (e.length.val + 1) =
          e.head.val + n - e.length.val := by
        lia
      rw [hsub]
    have hheadle := htail g ggtail
    have hnextgt : e.head < g.head := by
      rw [gghead]
      change e.head.val < (D.area.next e.head).val
      rw [D.area.next_val, Nat.mod_eq_of_lt hheadlt]
      lia
    exact (not_lt_of_ge hheadle) hnextgt

end VerticalStripLLT.Circular.DiagramProof
