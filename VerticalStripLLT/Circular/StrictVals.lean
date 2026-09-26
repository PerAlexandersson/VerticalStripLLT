import VerticalStripLLT.Circular.NDLocalData
import VerticalStripLLT.Circular.UnstrictCorner
import VerticalStripLLT.Circular.RaiseStrict
import VerticalStripLLT.Circular.DiagramExt

/-! Diagrams are determined by their area sequence and strict (head, length) pairs. -/

namespace VerticalStripLLT.Circular

open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace Edge

variable {n : ℕ}

/-- Reinterpret an edge in another area sequence where it is still valid. -/
def transport {A B : CircularArea n} (e : Edge A) (h : e.length.val ≤ B.area e.head) :
    Edge B :=
  ⟨e.1, e.2.1, h⟩

@[simp] theorem transport_val {A B : CircularArea n} (e : Edge A)
    (h : e.length.val ≤ B.area e.head) : (e.transport h).1 = e.1 := rfl

@[simp] theorem transport_head {A B : CircularArea n} (e : Edge A)
    (h : e.length.val ≤ B.area e.head) : (e.transport h).head = e.head := rfl

@[simp] theorem transport_length {A B : CircularArea n} (e : Edge A)
    (h : e.length.val ≤ B.area e.head) : (e.transport h).length = e.length := rfl

@[simp] theorem transport_tail {A B : CircularArea n} (e : Edge A)
    (h : e.length.val ≤ B.area e.head) : (e.transport h).tail = e.tail := rfl

end Edge

namespace Diagram

variable {n : ℕ}

/-- The underlying (head, length) pairs of the strict edges. -/
noncomputable def strictVals (D : Diagram n) : Finset (Fin n × Fin n) :=
  D.strict.map (Function.Embedding.subtype _)

theorem mem_strictVals (D : Diagram n) (p : Fin n × Fin n) :
    p ∈ D.strictVals ↔ ∃ e ∈ D.strict, e.1 = p := by
  simp only [strictVals, Finset.mem_map, Function.Embedding.coe_subtype]
  exact Iff.rfl

theorem val_mem_strictVals (D : Diagram n) (e : Edge D.area) :
    e.1 ∈ D.strictVals ↔ e ∈ D.strict :=
  Finset.mem_map' (Function.Embedding.subtype _)

theorem card_strictVals (D : Diagram n) : D.strictVals.card = D.strict.card :=
  Finset.card_map _

theorem transport_mem_strict (D : Diagram n) {A : CircularArea n} (e : Edge A)
    (h : e.length.val ≤ D.area.area e.head) :
    e.transport h ∈ D.strict ↔ e.1 ∈ D.strictVals := by
  rw [← D.val_mem_strictVals]
  rfl

theorem ext_of_strictVals {D₁ D₂ : Diagram n} (ha : D₁.area.area = D₂.area.area)
    (hs : D₁.strictVals = D₂.strictVals) : D₁ = D₂ := by
  obtain ⟨A₁, s₁, c₁⟩ := D₁
  obtain ⟨A₂, s₂, c₂⟩ := D₂
  have hA : A₁ = A₂ := by
    cases A₁
    cases A₂
    simp only at ha
    subst ha
    rfl
  subst hA
  congr 1
  ext e
  have h := congrArg (fun s => e.1 ∈ s) hs
  simp only [strictVals, Finset.mem_map, Function.Embedding.coe_subtype] at h
  constructor
  · intro he
    obtain ⟨e', he', hee⟩ := h.mp ⟨e, he, rfl⟩
    rwa [Subtype.ext hee] at he'
  · intro he
    obtain ⟨e', he', hee⟩ := h.mpr ⟨e, he, rfl⟩
    rwa [Subtype.ext hee] at he'

theorem strictVals_strictify (D : Diagram n) (e : Edge D.area) (he : IsCorner e) :
    (D.strictify e he).strictVals = insert e.1 D.strictVals := by
  simp [strictVals, strictify]

theorem strictVals_unstrict (D : Diagram n) (e : Edge D.area) (he : e ∈ D.strict) :
    (D.unstrict e he).strictVals = D.strictVals.erase e.1 := by
  simp [strictVals, unstrict, Finset.map_erase]

theorem strictVals_deleteCorner (D : Diagram n) (e : Edge D.area) (he : IsCorner e) :
    (D.deleteCorner e he).strictVals = D.strictVals.erase e.1 := by
  ext p
  rw [Finset.mem_erase, mem_strictVals, mem_strictVals]
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine ⟨fun h => D.cornerIncl_ne e he f (Subtype.ext h), D.cornerIncl e he f,
      (D.mem_deleteCorner_strict e he f).mp hf, rfl⟩
  · rintro ⟨hp, f, hf, rfl⟩
    have hfe : f ≠ e := fun h => hp (congrArg Subtype.val h)
    exact ⟨D.cornerRestrict e he f hfe,
      (D.mem_deleteCorner_strict e he _).mpr hf, rfl⟩

theorem strictVals_shortenStrict (D : Diagram n) (e : Edge D.area) (he : e ∈ D.strict)
    (hlen : 2 ≤ e.length.val)
    (hgap : D.area.area (D.area.next e.head) < D.area.area e.head) :
    (D.shortenStrict e he hlen hgap).strictVals =
      insert (D.shortenedEdge e he hlen).1 (D.strictVals.erase e.1) := by
  unfold shortenStrict
  rw [strictVals_strictify, strictVals_deleteCorner]

theorem strictVals_raiseStrict (D : Diagram n) (e : Edge D.area) (he : e ∈ D.strict)
    (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
    (hb : D.area.area e.head + 1 < n)
    (hns : ∀ f ∈ D.strict, f.head ≠ D.area.next e.head) :
    (D.raiseStrict e he heq hb hns).strictVals =
      insert (D.raisedEdge e he heq hb).1 (D.strictVals.erase e.1) := by
  simp only [strictVals, raiseStrict, Finset.map_insert, Finset.map_map, Finset.map_erase]
  rfl

theorem area_strictify (D : Diagram n) (e : Edge D.area) (he : IsCorner e) :
    (D.strictify e he).area.area = D.area.area := rfl

theorem area_unstrict (D : Diagram n) (e : Edge D.area) (he : e ∈ D.strict) :
    (D.unstrict e he).area.area = D.area.area := rfl

theorem area_deleteCorner (D : Diagram n) (e : Edge D.area) (he : IsCorner e) :
    (D.deleteCorner e he).area.area =
      Function.update D.area.area e.head (D.area.area e.head - 1) := rfl

theorem area_shortenStrict (D : Diagram n) (e : Edge D.area) (he : e ∈ D.strict)
    (hlen : 2 ≤ e.length.val)
    (hgap : D.area.area (D.area.next e.head) < D.area.area e.head) :
    (D.shortenStrict e he hlen hgap).area.area =
      Function.update D.area.area e.head (D.area.area e.head - 1) := rfl

theorem area_raiseStrict (D : Diagram n) (e : Edge D.area) (he : e ∈ D.strict)
    (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
    (hb : D.area.area e.head + 1 < n)
    (hns : ∀ f ∈ D.strict, f.head ≠ D.area.next e.head) :
    (D.raiseStrict e he heq hb hns).area.area =
      Function.update D.area.area (D.area.next e.head) (D.area.area e.head + 1) := rfl

theorem strictAt_iff_strictVals (D : Diagram n) (z : ℤ) :
    D.strictAt z ↔ ∃ p ∈ D.strictVals, p.1 = D.residue z := by
  constructor
  · rintro ⟨e, he, hh⟩
    exact ⟨e.1, (D.val_mem_strictVals e).mpr he, hh⟩
  · rintro ⟨p, hp, hh⟩
    obtain ⟨e, he, rfl⟩ := (D.mem_strictVals p).mp hp
    exact ⟨e, he, hh⟩

end Diagram
end VerticalStripLLT.Circular

