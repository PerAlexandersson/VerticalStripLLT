import VerticalStripLLT.Components.EdgeSwap
import VerticalStripLLT.Components.ShortEdges
import VerticalStripLLT.Components.WordProof.WordFlip
import VerticalStripLLT.Components.WordProof.WordSwap
import VerticalStripLLT.Components.WordProof.WordSwapInverse

/-! Concrete orientation exchanges preserving the original complete component. -/

namespace VerticalStripLLT.Components

open Circular

variable {n : ℕ} {D : Diagram n}

/-- Erase one edge and insert a normal edge in an ordinary diagram. -/
noncomputable def exchangeOrientation
    (hforward : ∀ e : Edge D.area, e.tail < e.head)
    (θ : Circular.Orientation D) (e f : Edge D.area)
    (hf : f ∈ D.edgeData.normalEdges) : Circular.Orientation D :=
  D.orientationOfForward hforward (insert f (θ.val.erase e)) (by
    intro g hg
    rcases Finset.mem_insert.mp hg with rfl | hg
    · exact hf
    · exact θ.property.1 (Finset.mem_erase.mp hg).2)

@[simp]
theorem exchangeOrientation_val
    (hforward : ∀ e : Edge D.area, e.tail < e.head)
    (θ : Circular.Orientation D) (e f : Edge D.area)
    (hf : f ∈ D.edgeData.normalEdges) :
    (exchangeOrientation hforward θ e f hf).val = insert f (θ.val.erase e) := rfl

/-- The two orientation exchanges are inverse when exactly the old edge was selected. -/
theorem exchangeOrientation_inverse
    (hforward : ∀ e : Edge D.area, e.tail < e.head)
    (θ : Circular.Orientation D) (e f : Edge D.area)
    (he : e ∈ D.edgeData.normalEdges) (hf : f ∈ D.edgeData.normalEdges)
    (heθ : e ∈ θ.val) (hfθ : f ∉ θ.val) :
    exchangeOrientation hforward (exchangeOrientation hforward θ e f hf) f e he = θ := by
  apply Subtype.ext
  exact insert_erase_exchange_inverse θ.val heθ hfθ

private theorem selected_forward
    (hforward : ∀ e : Edge D.area, e.tail < e.head)
    (A : Finset (Edge D.area)) {u v : Fin n}
    (h : D.edgeData.selected A u v) : u < v := by
  rcases h with ⟨e, _, hu, hv⟩
  rw [← hu, ← hv]
  exact hforward e

/-- A canonical natural lift identifies the finite endpoints. -/
theorem naturalLift_endpoints
    {e : Edge D.area} {a b : Fin n}
    (h : D.naturalLift e (a.val : ℤ) (b.val : ℤ)) :
    (e.tail, e.head) = (a, b) := by
  apply Prod.ext
  · simpa only [Circular.Orientation.residue_intCast_eq] using h.1.symm
  · have hh := D.residue_add_length e (a.val : ℤ) h.1
    rw [← h.2, Circular.Orientation.residue_intCast_eq] at hh
    exact hh.symm

/-- Selection of an edge's endpoint pair is membership in the full selected set. -/
theorem selected_edge_iff_mem (A : Finset (Edge D.area)) (e : Edge D.area) :
    D.edgeData.selected A e.tail e.head ↔ e ∈ D.strict ∪ A := by
  constructor
  · rintro ⟨f, hf, ht, hh⟩
    have hfe : f = e := by
      apply D.endpointEmbedding.injective
      change (f.tail, f.head) = (e.tail, e.head)
      exact Prod.ext ht hh
    rw [hfe] at hf
    exact hf
  · intro he
    exact ⟨e, he, rfl, rfl⟩

/-- Selection of a normal edge's endpoint pair is membership in the added set. -/
theorem selected_normal_iff_mem (A : Finset (Edge D.area)) (e : Edge D.area)
    (he : e ∈ D.edgeData.normalEdges) :
    D.edgeData.selected A e.tail e.head ↔ e ∈ A := by
  have hns : e ∉ D.strict := (Finset.mem_sdiff.mp he).2
  rw [selected_edge_iff_mem]
  simp only [Finset.mem_union, hns, false_or]

/-- A canonical lift lets selection be expressed using edge membership. -/
theorem selected_iff_mem_of_naturalLift (A : Finset (Edge D.area)) (e : Edge D.area)
    {a b : Fin n} (h : D.naturalLift e (a.val : ℤ) (b.val : ℤ)) :
    D.edgeData.selected A a b ↔ e ∈ D.strict ∪ A := by
  obtain ⟨ht, hh⟩ := Prod.mk.inj (naturalLift_endpoints h)
  simpa only [ht, hh] using selected_edge_iff_mem A e

private theorem fullWord_bac_to_acb (ρ σ : List (Fin n)) {a b c : Fin n}
    (hw : fullWord (ρ ++ [b, a, c] ++ σ)) :
    fullWord (ρ ++ [a, c, b] ++ σ) := by
  have hp : ([a, c, b] : List (Fin n)).Perm [b, a, c] :=
    List.perm_append_singleton b [a, c]
  exact (fullWord_perm_iff
    (List.Perm.append_right σ (List.Perm.append_left ρ hp))).mpr hw

/-- The forward exchange gives a compatible target and an actual directed flip. -/
theorem exchangeOrientation_forward
    (hforward : ∀ e : Edge D.area, e.tail < e.head)
    (θ : Circular.Orientation D) (ρ σ : List (Fin n))
    {a b c : Fin n} (hab : a < b) (hbc : b < c)
    (hw : fullWord (ρ ++ [a, c, b] ++ σ))
    (hcompat : wordCompatible (D.edgeData.selected θ.val) (ρ ++ [a, c, b] ++ σ))
    (eab ebc eac : Edge D.area)
    (heab : eab ∈ D.edgeData.normalEdges) (hebc : ebc ∈ D.edgeData.normalEdges)
    (habLift : D.naturalLift eab (a.val : ℤ) (b.val : ℤ))
    (hbcLift : D.naturalLift ebc (b.val : ℤ) (c.val : ℤ))
    (hacLift : D.naturalLift eac (a.val : ℤ) (c.val : ℤ))
    (habMem : eab ∈ θ.val) (hacMem : eac ∈ D.strict ∪ θ.val) :
    wordCompatible (D.edgeData.selected (exchangeOrientation hforward θ eab ebc hebc).val)
        (ρ ++ [b, a, c] ++ σ) ∧
      DirectedFlip D θ (exchangeOrientation hforward θ eab ebc hebc) := by
  let η := exchangeOrientation hforward θ eab ebc hebc
  have habEnds := naturalLift_endpoints habLift
  have hbcEnds := naturalLift_endpoints hbcLift
  have hrelation : ∀ u v, D.edgeData.selected η.val u v ↔
      (u = b ∧ v = c) ∨
        (D.edgeData.selected θ.val u v ∧ ¬ (u = a ∧ v = b)) := by
    intro u v
    exact D.selected_short_swap_iff θ.val eab ebc heab habEnds hbcEnds u v
  have hη : wordCompatible (D.edgeData.selected η.val) (ρ ++ [b, a, c] ++ σ) :=
    wordCompatible_exchange_of_nodup _ _ hrelation
      (fun _ _ h => selected_forward hforward θ.val h) ρ σ hab hbc hw.1 hcompat
  refine ⟨hη, ⟨?_⟩⟩
  exact directedFlipWitness_of_compatible_triples θ η ρ σ hab hbc hw hcompat hη
    eab ebc eac heab hebc habLift hbcLift hacLift habMem hacMem rfl

/-- Reversing the exchange gives the source word and the same directed flip. -/
theorem exchangeOrientation_backward
    (hforward : ∀ e : Edge D.area, e.tail < e.head)
    (η : Circular.Orientation D) (ρ σ : List (Fin n))
    {a b c : Fin n} (hab : a < b) (hbc : b < c)
    (hw : fullWord (ρ ++ [b, a, c] ++ σ))
    (hcompat : wordCompatible (D.edgeData.selected η.val) (ρ ++ [b, a, c] ++ σ))
    (eab ebc eac : Edge D.area)
    (heab : eab ∈ D.edgeData.normalEdges) (hebc : ebc ∈ D.edgeData.normalEdges)
    (habLift : D.naturalLift eab (a.val : ℤ) (b.val : ℤ))
    (hbcLift : D.naturalLift ebc (b.val : ℤ) (c.val : ℤ))
    (hacLift : D.naturalLift eac (a.val : ℤ) (c.val : ℤ))
    (hbcMem : ebc ∈ η.val) (hacMem : eac ∈ D.strict ∪ η.val) :
    wordCompatible (D.edgeData.selected (exchangeOrientation hforward η ebc eab heab).val)
        (ρ ++ [a, c, b] ++ σ) ∧
      DirectedFlip D (exchangeOrientation hforward η ebc eab heab) η := by
  classical
  let θ := exchangeOrientation hforward η ebc eab heab
  obtain ⟨habTail, habHead⟩ := Prod.mk.inj (naturalLift_endpoints habLift)
  obtain ⟨hbcTail, hbcHead⟩ := Prod.mk.inj (naturalLift_endpoints hbcLift)
  obtain ⟨hacTail, _⟩ := Prod.mk.inj (naturalLift_endpoints hacLift)
  have hrelation : ∀ u v, D.edgeData.selected θ.val u v ↔
      (u = a ∧ v = b) ∨
        (D.edgeData.selected η.val u v ∧ ¬ (u = b ∧ v = c)) := by
    intro u v
    change D.edgeData.selected (insert eab (η.val.erase ebc)) u v ↔ _
    rw [D.selected_insert_erase_normal_iff η.val ebc eab hebc]
    simp only [habTail, habHead, hbcTail, hbcHead, eq_comm]
  have hθ : wordCompatible (D.edgeData.selected θ.val) (ρ ++ [a, c, b] ++ σ) :=
    wordCompatible_exchange_inverse_of_nodup _ _ hrelation
      (fun _ _ h => selected_forward hforward η.val h) ρ σ hab hbc hw.1 hcompat
  have hnotAb : ¬ D.edgeData.selected η.val a b := by
    have htriple : wordCompatible (D.edgeData.selected η.val) [b, a, c] := by
      simp only [wordCompatible, List.pairwise_append] at hcompat ⊢
      grind
    simp [wordCompatible, List.pairwise_cons] at htriple
    grind
  have habNotMem : eab ∉ η.val := by
    intro he
    exact hnotAb ⟨eab, Finset.mem_union.mpr (Or.inr he), habTail, habHead⟩
  have hswap : η.val = insert ebc (θ.val.erase eab) :=
    (insert_erase_exchange_inverse η.val hbcMem habNotMem).symm
  have habMem : eab ∈ θ.val := Finset.mem_insert_self _ _
  have hlong_ne : eac ≠ ebc := by
    intro heq
    have ht := congrArg Edge.tail heq
    rw [hacTail, hbcTail] at ht
    exact hab.ne ht
  have hlong : eac ∈ D.strict ∪ θ.val := by
    rcases Finset.mem_union.mp hacMem with hs | ha
    · exact Finset.mem_union.mpr (Or.inl hs)
    · exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hlong_ne, ha⟩)))
  refine ⟨hθ, ⟨?_⟩⟩
  exact directedFlipWitness_of_compatible_triples θ η ρ σ hab hbc
    (fullWord_bac_to_acb ρ σ hw) hθ hcompat eab ebc eac heab hebc
    habLift hbcLift hacLift habMem hlong hswap

/-- A forward directed exchange stays in the chosen complete component. -/
theorem mem_flipComponent_of_directedFlip
    {base θ η : Circular.Orientation D} (hθ : θ ∈ flipComponent D base)
    (hflip : DirectedFlip D θ η) : η ∈ flipComponent D base := by
  apply mem_flipComponent_iff.mpr
  exact (mem_flipComponent_iff.mp hθ).tail (Or.inl hflip)

/-- A reversed directed exchange also stays in the chosen complete component. -/
theorem mem_flipComponent_of_reverse_directedFlip
    {base θ η : Circular.Orientation D} (hη : η ∈ flipComponent D base)
    (hflip : DirectedFlip D θ η) : θ ∈ flipComponent D base := by
  apply mem_flipComponent_iff.mpr
  exact (mem_flipComponent_iff.mp hη).tail (Or.inr hflip)

end VerticalStripLLT.Components
