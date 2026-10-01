import VerticalStripLLT.Components.DiagramProof.RightAttachmentValues
import VerticalStripLLT.Components.DiagramProof.DiagramMeasure

/-!
# Transferring a right-marked recurrence across a right attachment

A paired right-marked recurrence for whole components on a fixed prefix
vertex set gives the same unmarked recurrence, with the same integers, after
gluing one fixed whole component `T` of an arbitrary attachment to every
term. The K and E identities are transferred separately, each with its own
attachment factor; no identity between the two factors of `T` is assumed.

Gluing the same attachment also adds the same natural area to every term and
shifts the area moment uniformly, so a lexicographic decrease on the prefix
persists in the union.
-/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical
open scoped BigOperators

noncomputable section

variable {n p q : ℕ}

/-! ### The semantic transfer -/

section Transfer

variable {ι : Type*} (s : Finset ι) (z : ι → ℤ)
  {G : Diagram (p + q + 1)} {L : Diagram (p + 1)} {R : Diagram (q + 1)}
  (h : IsRightAttachment G L R)
  {Gs : ι → Diagram (p + q + 1)} {Ls : ι → Diagram (p + 1)}
  (hs : ∀ i, IsRightAttachment (Gs i) (Ls i) R)
  (P : Orientation L) (Ps : ∀ i, Orientation (Ls i)) (T : Orientation R) (m : ℕ)

private theorem transfer_aux {M : Type*} [CommRing M] (f : Fin m → M) (fs : ι → Fin m → M)
    (g : Fin m → M) (hf : ∀ β, f β = ∑ i ∈ s, z i • fs i β) :
    ∑ β, f β * g β = ∑ i ∈ s, z i • ∑ β, fs i β * g β := by
  simp only [hf, Finset.sum_mul, smul_mul_assoc, Finset.smul_sum]
  exact Finset.sum_comm

include h hs in
/-- The right-marked strict-coloring recurrence transfers across the attachment. -/
theorem componentStrictEnumerator_attach_transfer
    (hK : ∀ β : Fin m, componentMarkedK P (Fin.last p) m β =
      ∑ i ∈ s, z i • componentMarkedK (Ps i) (Fin.last p) m β) :
    componentStrictEnumerator G (h.glue P T) m =
      ∑ i ∈ s, z i • componentStrictEnumerator (Gs i) ((hs i).glue (Ps i) T) m := by
  rw [h.componentStrictEnumerator_glue]
  simp only [fun i => (hs i).componentStrictEnumerator_glue (Ps i) T m]
  exact transfer_aux s z m _ _ _ hK

include h hs in
/-- The right-marked HRV recurrence transfers across the attachment. -/
theorem evalElementary_componentHRV_attach_transfer
    (hE : ∀ β : Fin m, componentMarkedE P (Fin.last p) m β =
      ∑ i ∈ s, z i • componentMarkedE (Ps i) (Fin.last p) m β) :
    evalElementary m (componentHRV G (h.glue P T)) =
      ∑ i ∈ s, z i • evalElementary m (componentHRV (Gs i) ((hs i).glue (Ps i) T)) := by
  rw [h.evalElementary_componentHRV_glue]
  simp only [fun i => (hs i).evalElementary_componentHRV_glue (Ps i) T m]
  exact transfer_aux s z m _ _ _ hE

include h hs in
/-- The attachment lemma: whole product components and the paired transfer,
with the same coefficients for K and E. -/
theorem attach_transfer
    (hK : ∀ β : Fin m, componentMarkedK P (Fin.last p) m β =
      ∑ i ∈ s, z i • componentMarkedK (Ps i) (Fin.last p) m β)
    (hE : ∀ β : Fin m, componentMarkedE P (Fin.last p) m β =
      ∑ i ∈ s, z i • componentMarkedE (Ps i) (Fin.last p) m β) :
    flipComponent G (h.glue P T) =
        (flipComponent L P ×ˢ flipComponent R T).map h.stateEquiv.toEmbedding ∧
      (∀ i, flipComponent (Gs i) ((hs i).glue (Ps i) T) =
        (flipComponent (Ls i) (Ps i) ×ˢ flipComponent R T).map
          (hs i).stateEquiv.toEmbedding) ∧
      componentStrictEnumerator G (h.glue P T) m =
        ∑ i ∈ s, z i • componentStrictEnumerator (Gs i) ((hs i).glue (Ps i) T) m ∧
      evalElementary m (componentHRV G (h.glue P T)) =
        ∑ i ∈ s, z i • evalElementary m (componentHRV (Gs i) ((hs i).glue (Ps i) T)) :=
  ⟨h.flipComponent_glue P T, fun i => (hs i).flipComponent_glue (Ps i) T,
    componentStrictEnumerator_attach_transfer s z h hs P Ps T m hK,
    evalElementary_componentHRV_attach_transfer s z h hs P Ps T m hE⟩

end Transfer

namespace IsRightAttachment

variable {G : Diagram (p + q + 1)} {L : Diagram (p + 1)} {R : Diagram (q + 1)}
  (h : IsRightAttachment G L R)

include h

theorem area_left (x : Fin (p + 1)) : G.area.area (attachLeft p q x) = L.area.area x := by
  rw [area_eq_card_naturalRel, area_eq_card_naturalRel]
  have hset : (Finset.univ.filter fun u => naturalRel G u (attachLeft p q x)) =
      (Finset.univ.filter fun a => naturalRel L a x).map (attachLeft p q).toEmbedding := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro hu
      rcases (h.natural u _).mp hu with ⟨a, b, rfl, hb, hab⟩ | ⟨a, b, -, hb, hab⟩
      · exact ⟨a, (attachLeft p q).injective hb ▸ hab, rfl⟩
      · obtain ⟨-, rfl⟩ := attachLeft_eq_attachRight_iff.mp hb.symm
        exact absurd (naturalRel_forward h.forwardR hab) (Fin.not_lt_zero a)
    · rintro ⟨a, hax, rfl⟩
      exact (h.natural_left a x).mpr hax
  rw [hset, Finset.card_map]

theorem area_right {y : Fin (q + 1)} (hy : y ≠ 0) :
    G.area.area (attachRight p q y) = R.area.area y := by
  rw [area_eq_card_naturalRel, area_eq_card_naturalRel]
  have hset : (Finset.univ.filter fun u => naturalRel G u (attachRight p q y)) =
      (Finset.univ.filter fun b => naturalRel R b y).map (attachRight p q).toEmbedding := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro hu
      rcases (h.natural u _).mp hu with ⟨a, b, -, hb, -⟩ | ⟨a, b, rfl, hb, hab⟩
      · exact (hy (attachLeft_eq_attachRight_iff.mp hb).2).elim
      · exact ⟨a, (attachRight p q).injective hb ▸ hab, rfl⟩
    · rintro ⟨b, hby, rfl⟩
      exact (h.natural_right b y).mpr hby
  rw [hset, Finset.card_map]

/-- The attachment columns other than the shared vertex keep their areas; the
shared column of the attachment has area zero. -/
theorem sum_area_right (w : Fin (q + 1) → ℕ) :
    ∑ b ∈ Finset.univ.erase 0, w b * G.area.area (attachRight p q b) =
      ∑ b, w b * R.area.area b := by
  rw [← Finset.sum_erase (f := fun b => w b * R.area.area b) Finset.univ
    (by rw [area_zero_of_forward h.forwardR, mul_zero])]
  exact Finset.sum_congr rfl fun b hb => by rw [h.area_right (Finset.ne_of_mem_erase hb)]

/-- Gluing adds the two natural areas. -/
theorem naturalArea_eq : naturalArea G = naturalArea L + naturalArea R := by
  unfold naturalArea
  rw [sum_attach_split]
  simp only [h.area_left]
  have hR := h.sum_area_right (fun _ => 1)
  simp only [one_mul] at hR
  rw [hR]

/-- Gluing shifts the attachment's moment by `p` times its area. -/
theorem areaMoment_eq :
    areaMoment G = areaMoment L + areaMoment R + p * naturalArea R := by
  unfold areaMoment naturalArea
  rw [sum_attach_split]
  simp only [h.area_left, attachLeft_val]
  rw [show ∑ b ∈ Finset.univ.erase 0,
      (attachRight p q b).val * G.area.area (attachRight p q b) =
        ∑ b, (p + b.val) * R.area.area b from h.sum_area_right (fun b => p + b.val)]
  simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  ring

omit h in
/-- Gluing the same attachment to prefixes on the same vertex set preserves a
lexicographic decrease of `(area, moment)`. -/
theorem attach_measure_lt {G' : Diagram (p + q + 1)} {L' : Diagram (p + 1)}
    (h : IsRightAttachment G L R) (h' : IsRightAttachment G' L' R)
    (hlt : naturalArea L' < naturalArea L ∨
      (naturalArea L' = naturalArea L ∧ areaMoment L' < areaMoment L)) :
    naturalArea G' < naturalArea G ∨
      (naturalArea G' = naturalArea G ∧ areaMoment G' < areaMoment G) := by
  rw [h.naturalArea_eq, h'.naturalArea_eq, h.areaMoment_eq, h'.areaMoment_eq]
  generalize p * naturalArea R = k
  lia

end IsRightAttachment

end

end VerticalStripLLT.Circular.DiagramProof
