import VerticalStripLLT.Circular.Coloring
import VerticalStripLLT.Circular.NeutralExchange
import VerticalStripLLT.Circular.ParallelPaths
import VerticalStripLLT.Circular.StrictEdgeInjectivity
import VerticalStripLLT.Circular.WalkBound
import Mathlib.Tactic.Linarith

/-! Contact data for a full neutral bounce through arbitrarily many `d.d` contacts. -/

namespace VerticalStripLLT.Circular

/-- The two complete strict contact paths of a neutral bounce. -/
structure FullNeutralBounce {n : ℕ} (D D' : Diagram n) where
  k : ℕ
  main : Fin (k + 3) → Fin n
  parallel : Fin (k + 1) → Fin n
  main_steps : ∀ i : Fin (k + 2),
    D.edgeData.selected ∅ (main i.castSucc) (main i.succ)
  parallel_steps : ∀ i : Fin k,
    D.edgeData.selected ∅ (parallel i.castSucc) (parallel i.succ)
  parallel_next : ∀ i : Fin (k + 1),
    parallel i = D.area.next (main i.succ.castSucc)
  parallel_start : ∀ v, ¬ D.edgeData.selected ∅ v (parallel 0)
  parallel_end : ∀ v, ¬ D.edgeData.selected ∅ (parallel (Fin.last k)) v
  changed : ∀ u v, D'.edgeData.selected ∅ u v ↔
    neutralExchangeRelation (D.edgeData.selected ∅) (main 0) (main (Fin.last (k + 2)))
      (fun i => main i.succ.castSucc) parallel u v

namespace Diagram

variable {n : ℕ} (D : Diagram n)

/-- Strict selected edges have at most one successor. -/
theorem strict_selected_rightUnique : Relator.RightUnique (D.edgeData.selected ∅) := by
  intro u v w huv huw
  rcases huv with ⟨e, he, htail, hhead⟩
  rcases huw with ⟨f, hf, htail', hhead'⟩
  have hes : e ∈ D.strict := by simpa [Diagram.edgeData] using he
  have hfs : f ∈ D.strict := by simpa [Diagram.edgeData] using hf
  have hef : e = f := D.strict_edge_eq_of_tail_eq hes hfs (htail.trans htail'.symm)
  calc
    v = e.head := hhead.symm
    _ = f.head := congrArg Edge.head hef
    _ = w := hhead'

/-- Strict selected edges have at most one predecessor. -/
theorem strict_selected_leftUnique : Relator.LeftUnique (D.edgeData.selected ∅) := by
  intro u v w huv huw
  rcases huv with ⟨e, he, htail, hhead⟩
  rcases huw with ⟨f, hf, htail', hhead'⟩
  have hes : e ∈ D.strict := by simpa [Diagram.edgeData] using he
  have hfs : f ∈ D.strict := by simpa [Diagram.edgeData] using hf
  have hef : e = f := D.strict_edge_eq_of_head_eq hes hfs (hhead.trans hhead'.symm)
  calc
    u = e.tail := htail.symm
    _ = f.tail := congrArg Edge.tail hef
    _ = v := htail'

end Diagram

namespace FullNeutralBounce

variable {n : ℕ} {D D' : Diagram n} (B : FullNeutralBounce D D')

/-- The exchanged interior of the main contact path. -/
def inner : Fin (B.k + 1) → Fin n := fun i => B.main i.succ.castSucc

theorem main_injective (ha : D.edgeData.Admissible ∅) : Function.Injective B.main :=
  acyclic_walk_injective _ ha B.main B.main_steps

theorem parallel_injective (ha : D.edgeData.Admissible ∅) : Function.Injective B.parallel :=
  acyclic_walk_injective _ ha B.parallel B.parallel_steps

theorem main_parallel_disjoint (ha : D.edgeData.Admissible ∅) :
    ∀ i j, B.main i ≠ B.parallel j := by
  exact parallel_paths_disjoint _ D.strict_selected_leftUnique D.strict_selected_rightUnique
    B.main B.parallel (B.main_injective ha) (B.parallel_injective ha) B.main_steps
    B.parallel_steps B.parallel_start B.parallel_end

theorem inner_injective (ha : D.edgeData.Admissible ∅) : Function.Injective B.inner := by
  intro i j hij
  apply Fin.ext
  have hmain := B.main_injective ha hij
  have hval := congrArg Fin.val hmain
  change i.val + 1 = j.val + 1 at hval
  lia

theorem inner_parallel_disjoint (ha : D.edgeData.Admissible ∅) :
    ∀ i j, B.inner i ≠ B.parallel j := by
  intro i j hij
  exact B.main_parallel_disjoint ha i.succ.castSucc j hij

theorem start_not_mem_inner (ha : D.edgeData.Admissible ∅) (i : Fin (B.k + 1)) :
    B.main 0 ≠ B.inner i := by
  intro h
  have hmain := B.main_injective ha h
  have hval := congrArg Fin.val hmain
  change 0 = i.val + 1 at hval
  lia

theorem end_not_mem_inner (ha : D.edgeData.Admissible ∅) (i : Fin (B.k + 1)) :
    B.main (Fin.last (B.k + 2)) ≠ B.inner i := by
  intro h
  have hmain := B.main_injective ha h
  have hval := congrArg Fin.val hmain
  change B.k + 2 = i.val + 1 at hval
  have hi := i.isLt
  lia

theorem start_not_mem_parallel (ha : D.edgeData.Admissible ∅) (i : Fin (B.k + 1)) :
    B.main 0 ≠ B.parallel i := B.main_parallel_disjoint ha 0 i

theorem end_not_mem_parallel (ha : D.edgeData.Admissible ∅) (i : Fin (B.k + 1)) :
    B.main (Fin.last (B.k + 2)) ≠ B.parallel i :=
  B.main_parallel_disjoint ha (Fin.last (B.k + 2)) i

theorem inner_steps (i : Fin B.k) :
    D.edgeData.selected ∅ (B.inner i.castSucc) (B.inner i.succ) := by
  simpa [inner] using B.main_steps i.succ.castSucc

theorem start_step : D.edgeData.selected ∅ (B.main 0) (B.inner 0) := by
  exact B.main_steps 0

theorem end_step :
    D.edgeData.selected ∅ (B.inner (Fin.last B.k)) (B.main (Fin.last (B.k + 2))) := by
  simpa [inner] using B.main_steps (Fin.last (B.k + 1))

noncomputable def permutation (ha : D.edgeData.Admissible ∅) : Equiv.Perm (Fin n) :=
  pairedSwap B.inner B.parallel (B.inner_injective ha) (B.parallel_injective ha)
    (B.inner_parallel_disjoint ha)

theorem selected_iff (ha : D.edgeData.Admissible ∅) (u v : Fin n) :
    D.edgeData.selected ∅ u v ↔
      D'.edgeData.selected ∅ (B.permutation ha u) (B.permutation ha v) := by
  let σ := B.permutation ha
  have hconj := neutralExchange_conjugates (D.edgeData.selected ∅)
    D.strict_selected_leftUnique D.strict_selected_rightUnique
    (B.main 0) (B.main (Fin.last (B.k + 2))) B.inner B.parallel
    (B.inner_injective ha) (B.parallel_injective ha) (B.inner_parallel_disjoint ha)
    (B.start_not_mem_inner ha) (B.start_not_mem_parallel ha)
    (B.end_not_mem_inner ha) (B.end_not_mem_parallel ha)
    B.start_step B.end_step B.inner_steps B.parallel_steps B.parallel_start B.parallel_end u v
  calc
    D.edgeData.selected ∅ u v ↔ neutralExchangeRelation (D.edgeData.selected ∅)
        (B.main 0) (B.main (Fin.last (B.k + 2))) B.inner B.parallel (σ u) (σ v) := hconj
    _ ↔ D'.edgeData.selected ∅ (σ u) (σ v) := (B.changed _ _).symm

end FullNeutralBounce

end VerticalStripLLT.Circular
