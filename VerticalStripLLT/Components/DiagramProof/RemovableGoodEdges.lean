import VerticalStripLLT.Components.DiagramProof.ChainSeparators
import VerticalStripLLT.Components.DiagramProof.NaturalSeparators
import VerticalStripLLT.Components.DiagramProof.AnchorSizes

/-! Good non-corner edges are removable when a third corner chain is available. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

open Classical

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hforward : Forward D)

/-- A path outside an endpoint chain cannot use the given edge. -/
theorem weakReach_erase_of_avoiding_terminal (d : Edge D.area) (t u v : Fin n)
    (ht : F.terminal hforward d.tail = t ∨ F.terminal hforward d.head = t)
    (h : Relation.EqvGen (fun x y => F.terminal hforward x ≠ t ∧
      F.terminal hforward y ≠ t ∧ F.goodEdgeRelation hforward x y) u v) :
    Relation.EqvGen (fun x y => ∃ e ∈ (F.goodEdges hforward).erase d,
      e.tail = x ∧ e.head = y) u v := by
  apply Relation.EqvGen.mono _ _ _ h
  rintro x y ⟨hx, hy, e, he, het, heh⟩
  refine ⟨e, Finset.mem_erase.mpr ⟨?_, he⟩, het, heh⟩
  intro hed
  subst e
  rcases ht with ht | ht
  · exact hx (het ▸ ht)
  · exact hy (heh ▸ ht)

/-- A third chain provides a path around a good non-corner edge. -/
theorem weakReach_erase_good_edge (hn : 3 ≤ n)
    (hshort : ∀ u v : Fin n, u < v → v.val ≤ u.val + 2 → naturalRel D u v)
    (d : Edge D.area) (hdG : d ∈ F.goodEdges hforward) (hdF : d ∉ F.edges)
    (w : Fin n) (hwt : F.terminal hforward w ≠ F.terminal hforward d.tail)
    (hwh : F.terminal hforward w ≠ F.terminal hforward d.head) :
    Relation.EqvGen (fun x y => ∃ e ∈ (F.goodEdges hforward).erase d,
      e.tail = x ∧ e.head = y) d.tail d.head := by
  have hdlt := ((F.mem_goodEdges hforward d).mp hdG).resolve_left hdF
  have hp := F.goodEdge_weakReach_avoiding_terminal hforward hn hshort
    (F.terminal hforward d.head) d.tail w hdlt.ne hwh
  have hq := F.goodEdge_weakReach_avoiding_terminal hforward hn hshort
    (F.terminal hforward d.tail) w d.head hwt hdlt.ne.symm
  exact Relation.EqvGen.trans _ _ _
    (F.weakReach_erase_of_avoiding_terminal hforward d _ _ _ (Or.inr rfl) hp)
    (F.weakReach_erase_of_avoiding_terminal hforward d _ _ _ (Or.inl rfl) hq)

/-- Deleting a good non-corner edge leaves the full good-edge graph connected
as soon as there is a third chain. -/
theorem goodEdgeGraph_delete_connected (hn : 3 ≤ n)
    (hshort : ∀ u v : Fin n, u < v → v.val ≤ u.val + 2 → naturalRel D u v)
    (d : Edge D.area) (hdG : d ∈ F.goodEdges hforward) (hdF : d ∉ F.edges)
    (hthird : ∃ w, F.terminal hforward w ≠ F.terminal hforward d.tail ∧
      F.terminal hforward w ≠ F.terminal hforward d.head) :
    ((edgeSetGraph (F.goodEdges hforward)).deleteEdges {s(d.tail, d.head)}).Connected := by
  obtain ⟨w, hwt, hwh⟩ := hthird
  have halt := F.weakReach_erase_good_edge hforward hn hshort d hdG hdF w hwt hwh
  rw [← edgeSetGraph_erase hforward]
  let : Nonempty (Fin n) := ⟨⟨0, by lia⟩⟩
  constructor
  intro u v
  apply (eqvGen_iff_fromRel_reachable u v).mp
  have hnat := naturalRel_connected_of_short hshort u v
  have hg := (F.eqvGen_goodEdgeRelation_iff_eqvGen_naturalRel
    hforward u v).mpr hnat
  apply Relation.EqvGen.eqvGen_le _ u v hg
  rintro x y ⟨e, he, rfl, rfl⟩
  by_cases hed : e = d
  · exact hed ▸ halt
  · exact Relation.EqvGen.rel _ _ ⟨e, Finset.mem_erase.mpr ⟨hed, he⟩, rfl, rfl⟩

/-- The deletion hypothesis needed for the anchor construction follows from
connectivity after every vertex deletion and the existence of a third chain. -/
theorem goodEdgeGraph_delete_connected_of_no_articulation (hn : 3 ≤ n)
    (hconn : ∀ u v, Relation.EqvGen (naturalRel D) u v)
    (hdelete : ∀ w u v, u ≠ w → v ≠ w →
      Relation.EqvGen (fun x y => x ≠ w ∧ y ≠ w ∧ naturalRel D x y) u v)
    (d : Edge D.area) (hdG : d ∈ F.goodEdges hforward) (hdF : d ∉ F.edges)
    (hthird : ∃ w, F.terminal hforward w ≠ F.terminal hforward d.tail ∧
      F.terminal hforward w ≠ F.terminal hforward d.head) :
    ((edgeSetGraph (F.goodEdges hforward)).deleteEdges {s(d.tail, d.head)}).Connected :=
  F.goodEdgeGraph_delete_connected hforward hn
    (naturalRel_short_of_connected_of_delete hforward hconn hdelete) d hdG hdF hthird

/-- With at least three chains, a third terminal exists outside any two given chains. -/
theorem exists_third_terminal
    (hchains : 3 ≤ Nat.card {t : Fin n // F.terminal hforward t = t}) (u v : Fin n) :
    ∃ w, F.terminal hforward w ≠ F.terminal hforward u ∧
      F.terminal hforward w ≠ F.terminal hforward v := by
  let B : {t : Fin n // F.terminal hforward t = t} :=
    ⟨F.terminal hforward u, F.terminal_idempotent hforward u⟩
  let C : {t : Fin n // F.terminal hforward t = t} :=
    ⟨F.terminal hforward v, F.terminal_idempotent hforward v⟩
  have hnot : ¬ (Finset.univ : Finset {t : Fin n // F.terminal hforward t = t}) ⊆ {B, C} := by
    intro hs
    have hc := Finset.card_le_card hs
    have hb : ({B, C} : Finset {t : Fin n // F.terminal hforward t = t}).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    rw [Finset.card_univ] at hc
    rw [Nat.card_eq_fintype_card] at hchains
    lia
  obtain ⟨w, _, hw⟩ := Finset.not_subset.mp hnot
  have hw' : w ≠ B ∧ w ≠ C := by simpa only [Finset.mem_insert,
    Finset.mem_singleton, not_or] using hw
  refine ⟨w.val, ?_, ?_⟩
  · intro h
    exact hw'.1 (Subtype.ext (w.property.symm.trans h))
  · intro h
    exact hw'.2 (Subtype.ext (w.property.symm.trans h))

/-- Every feasible size below the full size admits an anchor omitting the specified edge
when the natural graph has no articulation and at least three corner chains remain. -/
theorem exists_connected_anchor_card_avoiding_of_no_articulation (hn : 3 ≤ n)
    (hconn : ∀ u v, Relation.EqvGen (naturalRel D) u v)
    (hdelete : ∀ w u v, u ≠ w → v ≠ w →
      Relation.EqvGen (fun x y => x ≠ w ∧ y ≠ w ∧ naturalRel D x y) u v)
    (hchains : 3 ≤ Nat.card {t : Fin n // F.terminal hforward t = t})
    (d : Edge D.area) (hdG : d ∈ F.goodEdges hforward) (hdF : d ∉ F.edges)
    (k : ℕ) (hlower : n ≤ k + 1) (hupper : k + 1 ≤ (F.goodEdges hforward).card) :
    ∃ θ : Orientation D, F.Anchor hforward θ ∧ SelectedConnected θ ∧
      totalSelected θ = k ∧ d ∉ fullSelection θ :=
  F.exists_connected_anchor_card_avoiding hforward d hdG hdF
    (F.goodEdgeGraph_delete_connected_of_no_articulation hforward hn hconn hdelete d hdG hdF
      (F.exists_third_terminal hforward hchains d.tail d.head)) k hlower hupper

end VerticalStripLLT.Circular.DiagramProof.CornerFamily
