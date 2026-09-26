import VerticalStripLLT.Circular.ShortenStrict
import VerticalStripLLT.Circular.PairColoringBridge

/-! Exact endpoint sets for the terminal DE-to-ED successor. -/

namespace VerticalStripLLT.Circular
namespace Diagram

variable {n : ℕ} (D : Diagram n)

set_option backward.isDefEq.respectTransparency false

def shortenedOldEdge (e : Edge D.area) (he : e ∈ D.strict) (hlen : 2 ≤ e.length.val) :
    Edge D.area := D.cornerIncl e (D.strict_corner e he) (D.shortenedEdge e he hlen)

theorem shortenedOldEdge_tail (e : Edge D.area) (he : e ∈ D.strict)
    (hlen : 2 ≤ e.length.val) : (D.shortenedOldEdge e he hlen).tail = D.area.next e.tail := by
  let f := D.shortenedOldEdge e he hlen
  have hfhead : f.head = e.head := rfl
  have hflength : f.length.val + 1 = e.length.val := D.shortenStrict_edge_length e he hlen
  have hm : e.tail.val + 1 + f.length.val ≡ f.tail.val + f.length.val [MOD n] := by
    change (e.tail.val + 1 + f.length.val) % n = (f.tail.val + f.length.val) % n
    rw [show e.tail.val + 1 + f.length.val = e.tail.val + e.length.val by lia,
      e.tail_add_length_mod, f.tail_add_length_mod, hfhead]
  have hcancel := Nat.ModEq.add_right_cancel' f.length.val hm
  change (e.tail.val + 1) % n = f.tail.val % n at hcancel
  rw [Nat.mod_eq_of_lt f.tail.isLt] at hcancel
  apply Fin.ext
  change f.tail.val = (e.tail.val + 1) % n
  exact hcancel.symm

theorem shortenStrict_pairGraph_strictEdges (e : Edge D.area) (he : e ∈ D.strict)
    (hlen : 2 ≤ e.length.val)
    (hgap : D.area.area (D.area.next e.head) < D.area.area e.head) :
    (D.shortenStrict e he hlen hgap).pairGraph.strictEdges =
      insert ((D.shortenedOldEdge e he hlen).tail, (D.shortenedOldEdge e he hlen).head)
        (D.pairGraph.strictEdges.erase (e.tail, e.head)) := by
  classical
  let Q := D.shortenStrict e he hlen hgap
  let f := D.shortenedEdge e he hlen
  ext x
  rw [Finset.mem_insert, Finset.mem_erase, Q.mem_pairGraph_strict_iff]
  constructor
  · rintro ⟨g, hg, hp⟩
    rcases (D.shortenStrict_strict_mem e he hlen hgap g).mp hg with rfl | hg
    · exact Or.inl hp.symm
    · right
      refine ⟨?_, (D.mem_pairGraph_strict_iff x).mpr
        ⟨D.cornerIncl e (D.strict_corner e he) g, hg, hp⟩⟩
      intro hx
      apply D.cornerIncl_ne e (D.strict_corner e he) g
      apply D.endpointEmbedding.injective
      exact hp.trans hx
  · rintro (hx | ⟨hne, hx⟩)
    · exact ⟨f, (D.shortenStrict_strict_mem e he hlen hgap f).mpr (Or.inl rfl), hx.symm⟩
    · obtain ⟨g, hg, hp⟩ := (D.mem_pairGraph_strict_iff x).mp hx
      have hge : g ≠ e := by
        intro h
        subst g
        exact hne hp.symm
      let g' := D.cornerRestrict e (D.strict_corner e he) g hge
      exact ⟨g', (D.shortenStrict_strict_mem e he hlen hgap g').mpr (Or.inr hg), hp⟩

theorem shortenStrict_pairGraph_normalEdges (e : Edge D.area) (he : e ∈ D.strict)
    (hlen : 2 ≤ e.length.val)
    (hgap : D.area.area (D.area.next e.head) < D.area.area e.head) :
    (D.shortenStrict e he hlen hgap).pairGraph.normalEdges =
      D.pairGraph.normalEdges.erase
        ((D.shortenedOldEdge e he hlen).tail, (D.shortenedOldEdge e he hlen).head) := by
  classical
  let Q := D.shortenStrict e he hlen hgap
  let f := D.shortenedEdge e he hlen
  ext x
  rw [Finset.mem_erase, Q.mem_pairGraph_normal_iff]
  constructor
  · rintro ⟨g, hg, hp⟩
    have hgnot : g ∉ Q.strict := (Finset.mem_sdiff.mp hg).2
    refine ⟨?_, (D.mem_pairGraph_normal_iff x).mpr
      ⟨D.cornerIncl e (D.strict_corner e he) g, ?_, hp⟩⟩
    · intro hx
      have hgf : g = f := Q.endpointEmbedding.injective (hp.trans hx)
      apply hgnot
      exact (D.shortenStrict_strict_mem e he hlen hgap g).mpr (Or.inl hgf)
    · apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hs
      exact hgnot ((D.shortenStrict_strict_mem e he hlen hgap g).mpr (Or.inr hs))
  · rintro ⟨hne, hx⟩
    obtain ⟨g, hg, hp⟩ := (D.mem_pairGraph_normal_iff x).mp hx
    have hgnot : g ∉ D.strict := (Finset.mem_sdiff.mp hg).2
    have hge : g ≠ e := by rintro rfl; exact hgnot he
    let g' := D.cornerRestrict e (D.strict_corner e he) g hge
    refine ⟨g', Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩, hp⟩
    intro hs
    rcases (D.shortenStrict_strict_mem e he hlen hgap g').mp hs with hgf | hs
    · apply hne
      have hpair : (g'.tail, g'.head) = (f.tail, f.head) :=
        congrArg (fun a : Edge Q.area => (a.tail, a.head)) hgf
      exact hp.symm.trans hpair
    · exact hgnot hs

end Diagram
end VerticalStripLLT.Circular
