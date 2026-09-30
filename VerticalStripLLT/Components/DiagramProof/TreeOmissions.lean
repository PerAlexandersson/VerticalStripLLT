import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Short cycles forbidden in an acyclic selected graph. -/

namespace VerticalStripLLT.Circular.DiagramProof

namespace SimpleGraph

open _root_.SimpleGraph

variable {V : Type*} [LinearOrder V] {T : _root_.SimpleGraph V}

omit [LinearOrder V] in
theorem not_adj_of_adjacent_to_same (hT : T.IsAcyclic) {x y e : V}
    (hxy : x ≠ y) (hxe : T.Adj x e) (hye : T.Adj y e) : ¬ T.Adj x y := by
  intro hxy'
  let p : T.Walk x e := .cons hxy' (.cons hye .nil)
  have hp : p.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simp [p, hxy, hxe.ne, hye.ne]
  have heq := hT.eq_snd_of_adj_start hp hxe p.end_mem_support
  exact hye.ne (by simpa [p] using heq.symm)

theorem not_adj_of_three_edge_path (hT : T.IsAcyclic) {b a c e : V}
    (hba : b < a) (hac : a < c) (hce : c < e)
    (hbc : T.Adj b c) (hce' : T.Adj c e) (hae : T.Adj a e) : ¬ T.Adj b a := by
  intro hba'
  let p : T.Walk b a := .cons hbc (.cons hce' (.cons hae.symm .nil))
  have hp : p.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simp [p, hba.ne, hce.ne, hac.ne',
      (hba.trans hac).ne, (hac.trans hce).ne', ((hba.trans hac).trans hce).ne]
  have heq := hT.eq_snd_of_adj_start hp hba' p.end_mem_support
  exact hac.ne (by simpa [p] using heq)

end SimpleGraph

end VerticalStripLLT.Circular.DiagramProof
