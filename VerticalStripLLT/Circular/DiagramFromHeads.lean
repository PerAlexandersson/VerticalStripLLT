import VerticalStripLLT.Circular.Coloring

set_option backward.isDefEq.respectTransparency false

/-! Constructing a circular diagram from the rows carrying strict edges. -/

namespace VerticalStripLLT.Circular

open scoped Classical

namespace Diagram

variable {n : ℕ} {A : CircularArea n}

private noncomputable def edgeAt (v : Fin n) (hv : 0 < A.area v) : Edge A :=
  ⟨(v, ⟨A.area v, A.bound v⟩), ⟨hv, le_rfl⟩⟩

def fullTail (v : Fin n) : Fin n :=
  ⟨(v.val + n - A.area v) % n, Nat.mod_lt _ A.positive⟩

@[simp] private theorem edgeAt_head (v : Fin n) (hv : 0 < A.area v) :
    (edgeAt v hv).head = v := rfl

@[simp] private theorem edgeAt_length (v : Fin n) (hv : 0 < A.area v) :
    (edgeAt v hv).length.val = A.area v := rfl

/-- The diagram whose strict edge at `v` has the full height of row `v`. -/
noncomputable def fromHeads (A : CircularArea n) (S : Finset (Fin n))
    (hpos : ∀ v ∈ S, 0 < A.area v)
    (hcorner : ∀ v ∈ S, A.area (A.next v) ≤ A.area v) : Diagram n :=
  { area := A
    strict := S.attach.image (fun v => edgeAt v.1 (hpos v.1 v.2))
    strict_corner := by
      intro e he
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
      exact ⟨rfl, hcorner v.1 v.2⟩ }

theorem mem_fromHeads_strict_iff
    (S : Finset (Fin n)) (hpos : ∀ v ∈ S, 0 < A.area v)
    (hcorner : ∀ v ∈ S, A.area (A.next v) ≤ A.area v) (e : Edge A) :
    e ∈ (fromHeads A S hpos hcorner).strict ↔
      e.head ∈ S ∧ e.length.val = A.area e.head := by
  constructor
  · intro he
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
    exact ⟨v.2, rfl⟩
  · rintro ⟨he, hlen⟩
    let hv : 0 < A.area e.head := hpos e.head he
    have heq : e = edgeAt e.head hv := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Fin.ext
        exact hlen
    apply Finset.mem_image.mpr
    refine ⟨⟨e.head, he⟩, ?_, heq.symm⟩
    exact Finset.mem_attach S _

theorem fromHeads_strict_head_mem_iff
    (S : Finset (Fin n)) (hpos : ∀ v ∈ S, 0 < A.area v)
    (hcorner : ∀ v ∈ S, A.area (A.next v) ≤ A.area v) (v : Fin n) :
    v ∈ (fromHeads A S hpos hcorner).strict.image Edge.head ↔ v ∈ S := by
  constructor
  · intro hv
    obtain ⟨e, he, hhead⟩ := Finset.mem_image.mp hv
    have hm := (mem_fromHeads_strict_iff S hpos hcorner e).mp he
    rw [← hhead]
    exact hm.1
  · intro hv
    let e := edgeAt v (hpos v hv)
    apply Finset.mem_image.mpr
    refine ⟨e, ?_, rfl⟩
    exact (mem_fromHeads_strict_iff S hpos hcorner e).mpr ⟨hv, rfl⟩

theorem fromHeads_strict_head_image
    (S : Finset (Fin n)) (hpos : ∀ v ∈ S, 0 < A.area v)
    (hcorner : ∀ v ∈ S, A.area (A.next v) ≤ A.area v) :
    (fromHeads A S hpos hcorner).strict.image Edge.head = S := by
  ext v
  exact fromHeads_strict_head_mem_iff S hpos hcorner v

theorem fromHeads_strict_card
    (S : Finset (Fin n)) (hpos : ∀ v ∈ S, 0 < A.area v)
    (hcorner : ∀ v ∈ S, A.area (A.next v) ≤ A.area v) :
    (fromHeads A S hpos hcorner).strict.card = S.card := by
  let f : {v // v ∈ S} → Edge A := fun v => edgeAt v.1 (hpos v.1 v.2)
  have hf : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    exact congrArg Edge.head h
  rw [fromHeads, Finset.card_image_of_injective _ hf, Finset.card_attach]

theorem fromHeads_selected_empty_iff
    (S : Finset (Fin n)) (hpos : ∀ v ∈ S, 0 < A.area v)
    (hcorner : ∀ v ∈ S, A.area (A.next v) ≤ A.area v) (u v : Fin n) :
    (fromHeads A S hpos hcorner).edgeData.selected ∅ u v ↔
      ∃ w ∈ S, u = fullTail (A := A) w ∧ v = w := by
  constructor
  · rintro ⟨e, he, hu, hv⟩
    have hm := (mem_fromHeads_strict_iff S hpos hcorner e).mp
      (by simpa [Diagram.edgeData] using he)
    refine ⟨e.head, hm.1, ?_, ?_⟩
    · change e.tail = u at hu
      have htail : e.tail = fullTail (A := A) e.head := by
        apply Fin.ext
        change (e.head.val + n - e.length.val) % n =
          (e.head.val + n - A.area e.head) % n
        rw [hm.2]
      exact hu.symm.trans htail
    · exact hv.symm
  · rintro ⟨w, hw, hu, hv⟩
    let e := edgeAt w (hpos w hw)
    refine ⟨e, ?_, ?_, hv.symm⟩
    · exact Finset.mem_union_left _ ((mem_fromHeads_strict_iff S hpos hcorner e).mpr
        ⟨hw, rfl⟩)
    · exact hu.symm

end Diagram
end VerticalStripLLT.Circular
