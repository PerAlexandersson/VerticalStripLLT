import VerticalStripLLT.Circular.StrictCornerAdjacency
import Mathlib.Order.Fin.Basic

/-! Exact diagram data for a strict chain and one isolated strict vertex. -/

namespace VerticalStripLLT.Circular

/-- An exhaustive enumeration whose strict edges are exactly consecutive chain edges. -/
structure ChainSingletonData {n : ℕ} (D : Diagram n) (k : ℕ) where
  vertices : (Fin (k + 1) ⊕ Unit) ≃ Fin n
  strict_iff : ∀ u v, D.edgeData.selected ∅ u v ↔
    ∃ i : Fin k, u = vertices (.inl i.castSucc) ∧ v = vertices (.inl i.succ)

namespace ChainSingletonData

variable {n k : ℕ} {D : Diagram n} (S : ChainSingletonData D k)

def chain (i : Fin (k + 1)) : Fin n := S.vertices (.inl i)

def isolated : Fin n := S.vertices (.inr ())

include S in
theorem cardinality : n = k + 2 := by
  have h := Fintype.card_congr S.vertices
  simpa using h.symm

theorem chain_injective : Function.Injective S.chain := by
  intro i j h
  exact Sum.inl.inj (S.vertices.injective h)

theorem isolated_ne_chain (i : Fin (k + 1)) : S.isolated ≠ S.chain i := by
  intro h
  have := S.vertices.injective h
  cases this

theorem vertex_cases (v : Fin n) : (∃ i, v = S.chain i) ∨ v = S.isolated := by
  obtain ⟨u, rfl⟩ := S.vertices.surjective v
  cases u with
  | inl i => exact Or.inl ⟨i, rfl⟩
  | inr u => cases u; exact Or.inr rfl

theorem selected_chain_succ (i : Fin k) :
    D.edgeData.selected ∅ (S.chain i.castSucc) (S.chain i.succ) :=
  (S.strict_iff _ _).mpr ⟨i, rfl, rfl⟩

include S in
/-- The exact strict graph is acyclic, independently of its circular embedding. -/
theorem admissible_empty : D.edgeData.Admissible ∅ := by
  let rank : Fin n → ℕ := fun v => (S.vertices.symm v).elim Fin.val (fun _ => 0)
  have hs : ∀ u v, D.edgeData.selected ∅ u v → rank u < rank v := by
    intro u v h
    obtain ⟨i, rfl, rfl⟩ := (S.strict_iff u v).mp h
    simp [rank]
  have hp : ∀ {u v}, Relation.TransGen (D.edgeData.selected ∅) u v →
      rank u < rank v := by
    intro u v h
    induction h with
    | single h => exact hs _ _ h
    | tail _ h ih => exact ih.trans (hs _ _ h)
  intro v h
  exact (lt_irrefl (rank v)) (hp h)

/-- Admissible colors are precisely increasing colors along the enumerated chain. -/
theorem admissibleColoring_iff {m : ℕ} (c : Fin n → Fin m) :
    D.edgeData.admissibleColoring c ↔ StrictMono (fun i => c (S.chain i)) := by
  rw [Fin.strictMono_iff_lt_succ]
  constructor
  · intro hc i
    apply D.edgeData.lt_of_selected ∅ c _ (S.selected_chain_succ i)
    simpa only [Finset.union_empty, EdgeData.admissibleColoring] using hc
  · intro hc e he
    have hsel : D.edgeData.selected ∅ e.tail e.head :=
      ⟨e, by simpa only [Finset.union_empty] using he, rfl, rfl⟩
    obtain ⟨i, ht, hh⟩ := (S.strict_iff _ _).mp hsel
    change c e.tail < c e.head
    rw [ht, hh]
    exact hc i

/-- Successive cross-incidences match, even when the chain winds around the circle. -/
theorem normal_across_succ (i : Fin k) :
    (S.chain i.castSucc, S.isolated) ∈ D.pairGraph.normalEdges ↔
      (S.isolated, S.chain i.succ) ∈ D.pairGraph.normalEdges := by
  obtain ⟨e, he, ht, hh⟩ := S.selected_chain_succ i
  change e.tail = S.chain i.castSucc at ht
  change e.head = S.chain i.succ at hh
  have hes : e ∈ D.strict := by simpa [Diagram.edgeData] using he
  have hvt : S.isolated ≠ e.tail := by rw [ht]; exact S.isolated_ne_chain _
  have hvh : S.isolated ≠ e.head := by rw [hh]; exact S.isolated_ne_chain _
  simpa only [ht, hh] using D.normalPairs_across_strict_corner_iff hes S.isolated hvt hvh

end ChainSingletonData

end VerticalStripLLT.Circular
