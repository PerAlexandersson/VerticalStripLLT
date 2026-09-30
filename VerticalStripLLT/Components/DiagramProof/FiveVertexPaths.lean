import VerticalStripLLT.Components.DiagramProof.ChainStateSelection
import VerticalStripLLT.Components.DiagramProof.IncomingFlip
import VerticalStripLLT.Components.DiagramProof.CoverCut
import Mathlib.Data.Fintype.Powerset
import VerticalStripLLT.Components.DiagramProof.SelectedRelation

/-! The four explicit five-vertex paths, keeping the full selected set at every step. -/

namespace VerticalStripLLT.Circular.DiagramProof

namespace FiveVertex

abbrev Pairs := Finset (Fin 5 × Fin 5)

def ForwardPairs (E : Pairs) : Prop := ∀ u v, (u, v) ∈ E → u < v

instance (E : Pairs) : Decidable (ForwardPairs E) := by
  unfold ForwardPairs
  infer_instance

noncomputable def state (E : Pairs) (hE : ForwardPairs E) : Orientation (completeDiagram 4) :=
  ofSelectedRelation (complete_forward 4) (fun u v => (u, v) ∈ E)
    (fun u v h => (complete_naturalEdge_iff 4 u v).mpr (hE u v h)) (by simp)

theorem state_selected (E : Pairs) (hE : ForwardPairs E) (u v : Fin 5) :
    (completeDiagram 4).edgeData.selected (state E hE).val u v ↔ (u, v) ∈ E :=
  selected_ofSelectedRelation ..

/-- A finite separating set certifies the absence of a bypass of the selected edge. -/
def Cut (E : Pairs) (a b : Fin 5) : Prop :=
  (a, b) ∈ E ∧ ∃ P : Finset (Fin 5), a ∈ P ∧ b ∉ P ∧
    ∀ u v, (u, v) ∈ E → (u = a ∧ v = b) ∨ (u ∈ P → v ∈ P)

instance (E : Pairs) (a b : Fin 5) : Decidable (Cut E a b) := by
  unfold Cut
  infer_instance

def swap (E : Pairs) (a b c : Fin 5) : Pairs :=
  if (a, b) ∈ E then insert (b, c) (E.erase (a, b))
  else insert (a, b) (E.erase (b, c))

def endpoint (E : Pairs) : List (Fin 5 × Fin 5 × Fin 5) → Pairs
  | [] => E
  | (a, b, c) :: ts => endpoint (swap E a b c) ts

/-- Each entry verifies the two source covers for the indicated actual flip. -/
def Trace (E : Pairs) : List (Fin 5 × Fin 5 × Fin 5) → Prop
  | [] => ForwardPairs E
  | (a, b, c) :: ts => ForwardPairs E ∧ a < b ∧ b < c ∧ Cut E a c ∧
      (if (a, b) ∈ E then Cut E a b else Cut E b c) ∧ Trace (swap E a b c) ts

instance (E : Pairs) (ts : List (Fin 5 × Fin 5 × Fin 5)) : Decidable (Trace E ts) := by
  induction ts generalizing E with
  | nil => exact inferInstanceAs (Decidable (ForwardPairs E))
  | cons t ts ih =>
    rcases t with ⟨a, b, c⟩
    dsimp [Trace]
    have := ih (swap E a b c)
    infer_instance

theorem trace_forward {E : Pairs} {ts} (h : Trace E ts) : ForwardPairs E := by
  cases ts with
  | nil => exact h
  | cons t ts => exact h.1

theorem cut_cover (E : Pairs) (hE : ForwardPairs E) (a b : Fin 5) (h : Cut E a b) :
    Cover (state E hE) a b := by
  obtain ⟨hab, P, ha, hb, hc⟩ := h
  apply relationCover_of_cut
    (fun {_ _} hs => (state E hE).selected_lt_of_forward (complete_forward 4) hs)
    ((state_selected E hE a b).mpr hab) (P := fun v => v ∈ P) ha hb
  intro u v huv
  exact hc u v ((state_selected E hE u v).mp huv)

/-- Interpret every checked triple as an actual flip of orientations. -/
theorem trace_path (E : Pairs) (ts : List (Fin 5 × Fin 5 × Fin 5)) (h : Trace E ts) :
    ∃ hF : ForwardPairs (endpoint E ts),
      Relation.ReflTransGen (Flip (completeDiagram 4))
        (state E (trace_forward h)) (state (endpoint E ts) hF) := by
  induction ts generalizing E with
  | nil => exact ⟨h, Relation.ReflTransGen.refl⟩
  | cons t ts ih =>
    rcases t with ⟨a, b, c⟩
    obtain ⟨hE, hab, hbc, hac, hshort, hrest⟩ := h
    obtain ⟨hF, hpath⟩ := ih (swap E a b c) hrest
    have hs : ∃ η, Flip (completeDiagram 4) (state E hE) η ∧
        ∀ u v, (completeDiagram 4).edgeData.selected η.val u v ↔
          (u, v) ∈ swap E a b c := by
      by_cases hmem : (a, b) ∈ E
      · have hshort' : Cut E a b := by simpa only [hmem, ↓reduceIte] using hshort
        obtain ⟨η, hf, _, _, hη⟩ := exists_outgoingSwap_of_covers (complete_forward 4)
          (state E hE) a b c (cut_cover E hE a b hshort') (cut_cover E hE a c hac) hbc
        refine ⟨η, hf, ?_⟩
        intro u v
        rw [hη, state_selected]
        simp only [swap, hmem, ↓reduceIte, Finset.mem_insert, Finset.mem_erase,
          ne_eq, Prod.mk.injEq]
        tauto
      · have hshort' : Cut E b c := by simpa only [hmem, ↓reduceIte] using hshort
        obtain ⟨η, hf, _, _, hη⟩ := exists_incomingSwap_of_covers (complete_forward 4)
          (state E hE) a b c (cut_cover E hE b c hshort') (cut_cover E hE a c hac) hab
        refine ⟨η, hf, ?_⟩
        intro u v
        rw [hη, state_selected]
        simp only [swap, hmem, ↓reduceIte, Finset.mem_insert, Finset.mem_erase,
          ne_eq, Prod.mk.injEq]
        tauto
    obtain ⟨η, hflip, hη⟩ := hs
    have heq : η = state (swap E a b c) (trace_forward hrest) := by
      apply fullSelection_injective
      ext e
      rw [mem_fullSelection_iff_selected, mem_fullSelection_iff_selected, hη, state_selected]
    exact ⟨hF, (Relation.ReflTransGen.single (heq ▸ hflip)).trans hpath⟩

def chain : Pairs := {(0, 4), (1, 2), (2, 3), (3, 4)}
def pairs13 : Pairs := insert (1, 3) chain
def pairs14 : Pairs := insert (1, 4) chain
def pairs24 : Pairs := insert (2, 4) chain
def pairs13_24 : Pairs := insert (1, 3) (insert (2, 4) chain)
def pairs14_24 : Pairs := insert (1, 4) (insert (2, 4) chain)
def pairs13_14 : Pairs := insert (1, 3) (insert (1, 4) chain)

theorem path13_14 :
    Relation.ReflTransGen (Flip (completeDiagram 4))
      (state pairs13 (by decide)) (state pairs14 (by decide)) := by
  have h : Trace pairs13 [(0,3,4), (0,2,3), (0,1,3), (0,1,4), (0,2,3), (0,3,4)] := by
    decide
  obtain ⟨hF, hp⟩ := trace_path _ _ h
  have he : endpoint pairs13
      [(0,3,4), (0,2,3), (0,1,3), (0,1,4), (0,2,3), (0,3,4)] = pairs14 := by decide
  simpa only [he] using hp

theorem path14_24 :
    Relation.ReflTransGen (Flip (completeDiagram 4))
      (state pairs14 (by decide)) (state pairs24 (by decide)) := by
  have h : Trace pairs14
      [(0,3,4), (1,2,4), (0,1,4), (0,2,3), (0,1,2), (0,2,3), (0,3,4)] := by decide
  obtain ⟨hF, hp⟩ := trace_path _ _ h
  have he : endpoint pairs14
      [(0,3,4), (1,2,4), (0,1,4), (0,2,3), (0,1,2), (0,2,3), (0,3,4)] =
      pairs24 := by decide
  simpa only [he] using hp

theorem path13_24_to14_24 :
    Relation.ReflTransGen (Flip (completeDiagram 4))
      (state pairs13_24 (by decide)) (state pairs14_24 (by decide)) := by
  have h : Trace pairs13_24 [(0,3,4), (0,2,4), (0,1,2), (0,1,4), (0,2,4),
      (0,1,3), (0,2,3), (0,1,2), (0,2,3), (0,3,4)] := by decide
  obtain ⟨hF, hp⟩ := trace_path _ _ h
  have he : endpoint pairs13_24 [(0,3,4), (0,2,4), (0,1,2), (0,1,4), (0,2,4),
      (0,1,3), (0,2,3), (0,1,2), (0,2,3), (0,3,4)] = pairs14_24 := by decide
  simpa only [he] using hp

theorem path14_24_to13_14 :
    Relation.ReflTransGen (Flip (completeDiagram 4))
      (state pairs14_24 (by decide)) (state pairs13_14 (by decide)) := by
  have h : Trace pairs14_24
      [(0,3,4), (0,2,3), (0,1,2), (0,1,3), (0,2,3), (1,2,4), (0,3,4)] := by decide
  obtain ⟨hF, hp⟩ := trace_path _ _ h
  have he : endpoint pairs14_24
      [(0,3,4), (0,2,3), (0,1,2), (0,1,3), (0,2,3), (1,2,4), (0,3,4)] =
      pairs13_14 := by decide
  simpa only [he] using hp

end FiveVertex

end VerticalStripLLT.Circular.DiagramProof
