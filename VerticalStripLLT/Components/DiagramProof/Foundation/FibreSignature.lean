import VerticalStripLLT.Components.DiagramProof.Foundation.LocalIdentities
import Mathlib.Data.Multiset.Filter

/-! Right-marked fibre values depend on fibre sizes and the distinguished fibre. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {n : ℕ}

theorem hrv_eq_last {D : Diagram n} (θ : Orientation D) (hD : Forward D)
    (v : Fin n) (hv : ∀ u, u ≤ v) : θ.hrv v = v :=
  le_antisymm (hv _) (θ.reachable_le_hrv_of_forward hD Relation.ReflTransGen.refl)

/-- Match equally sized fibres in their increasing vertex order. -/
def fibreOrderIso (H J : Fin n → Fin n) (σ : Fin n ≃ Fin n)
    (hcards : ∀ r, Fintype.card {u // H u = r} = Fintype.card {u // J u = σ r})
    (r : Fin n) : {u // H u = r} ≃o {u // J u = σ r} :=
  (Fintype.orderIsoFinOfCardEq {u // H u = r} rfl).symm.trans
    (Fintype.orderIsoFinOfCardEq {u // J u = σ r} (hcards r).symm)

/-- Assemble the increasing fibre bijections into a bijection of actual vertices. -/
def fibreVertexEquiv (H J : Fin n → Fin n) (σ : Fin n ≃ Fin n)
    (hcards : ∀ r, Fintype.card {u // H u = r} = Fintype.card {u // J u = σ r}) :
    Fin n ≃ Fin n :=
  (Equiv.sigmaFiberEquiv H).symm.trans
    ((Equiv.sigmaCongr σ (fun r => (fibreOrderIso H J σ hcards r).toEquiv)).trans
      (Equiv.sigmaFiberEquiv J))

theorem fibreVertexEquiv_apply_of_mem (H J : Fin n → Fin n) (σ : Fin n ≃ Fin n)
    (hcards : ∀ r, Fintype.card {u // H u = r} = Fintype.card {u // J u = σ r})
    (u r : Fin n) (hu : H u = r) :
    fibreVertexEquiv H J σ hcards u = (fibreOrderIso H J σ hcards r ⟨u, hu⟩).val := by
  subst r
  rfl

theorem fibreVertexEquiv_root (H J : Fin n → Fin n) (σ : Fin n ≃ Fin n)
    (hcards : ∀ r, Fintype.card {u // H u = r} = Fintype.card {u // J u = σ r})
    (u : Fin n) : J (fibreVertexEquiv H J σ hcards u) = σ (H u) :=
  (fibreOrderIso H J σ hcards (H u) ⟨u, rfl⟩).property

theorem fibreVertexEquiv_lt_iff (H J : Fin n → Fin n) (σ : Fin n ≃ Fin n)
    (hcards : ∀ r, Fintype.card {u // H u = r} = Fintype.card {u // J u = σ r})
    (u w : Fin n) (hroot : H u = H w) :
    fibreVertexEquiv H J σ hcards u < fibreVertexEquiv H J σ hcards w ↔ u < w := by
  rw [fibreVertexEquiv_apply_of_mem H J σ hcards u (H u) rfl,
    fibreVertexEquiv_apply_of_mem H J σ hcards w (H u) hroot.symm]
  exact (fibreOrderIso H J σ hcards (H u)).lt_iff_lt

theorem fibreVertexEquiv_relation (H J : Fin n → Fin n) (σ : Fin n ≃ Fin n)
    (hcards : ∀ r, Fintype.card {u // H u = r} = Fintype.card {u // J u = σ r})
    (u w : Fin n) :
    fibreRelation H u w ↔ fibreRelation J
      (fibreVertexEquiv H J σ hcards u) (fibreVertexEquiv H J σ hcards w) := by
  unfold fibreRelation
  rw [fibreVertexEquiv_root H J σ hcards u, fibreVertexEquiv_root H J σ hcards w,
    σ.injective.eq_iff]
  constructor
  · rintro ⟨huw, hroot⟩
    exact ⟨(fibreVertexEquiv_lt_iff H J σ hcards u w hroot).mpr huw, hroot⟩
  · rintro ⟨huw, hroot⟩
    exact ⟨(fibreVertexEquiv_lt_iff H J σ hcards u w hroot).mp huw, hroot⟩

/-- The greatest vertex is fixed when its distinguished fibre is matched. -/
theorem fibreVertexEquiv_fix_last (H J : Fin n → Fin n) (σ : Fin n ≃ Fin n)
    (hcards : ∀ r, Fintype.card {u // H u = r} = Fintype.card {u // J u = σ r})
    (v : Fin n) (hv : ∀ u, u ≤ v) (hmark : σ (H v) = J v) :
    fibreVertexEquiv H J σ hcards v = v := by
  let e := fibreVertexEquiv H J σ hcards
  apply le_antisymm (hv _)
  have hroot : H (e.symm v) = H v := by
    apply σ.injective
    rw [← fibreVertexEquiv_root H J σ hcards (e.symm v)]
    change J (e (e.symm v)) = σ (H v)
    rw [e.apply_symm_apply, hmark]
  rcases lt_or_eq_of_le (hv (e.symm v)) with hlt | heq
  · have h := (fibreVertexEquiv_lt_iff H J σ hcards (e.symm v) v hroot).mpr hlt
    change e (e.symm v) < e v at h
    rw [e.apply_symm_apply] at h
    exact h.le
  · have h := congrArg e heq
    rw [e.apply_symm_apply] at h
    exact h.le

/-- Fibre sizes and the matched last fibre suffice, without preserving other vertex labels. -/
theorem markedFibreValue_eq_of_matching_sizes (H J : Fin n → Fin n)
    (σ : Fin n ≃ Fin n)
    (hcards : ∀ r, Fintype.card {u // H u = r} = Fintype.card {u // J u = σ r})
    (v : Fin n) (hv : ∀ u, u ≤ v) (hmark : σ (H v) = J v) (m : ℕ) (β : Fin m) :
    markedRelationValue (fibreRelation H) v m β =
      markedRelationValue (fibreRelation J) v m β := by
  have h := markedRelationValue_relabel (fibreRelation J) (fibreRelation H)
    (fibreVertexEquiv H J σ hcards) (fibreVertexEquiv_relation H J σ hcards) v m β
  rw [fibreVertexEquiv_fix_last H J σ hcards v hv hmark] at h
  exact h

/-- Fibre sizes, with the endpoint's fibre distinguished. Empty root fibres contribute zeros. -/
def markedFibreSignature (H : Fin n → Fin n) (v : Fin n) : Multiset (Bool × ℕ) :=
  Finset.univ.val.map fun r => (decide (r = H v), Fintype.card {u // H u = r})

/-- The sizes of all other root fibres, with zero sizes retained. -/
def otherFibreSizes (H : Fin n → Fin n) (v : Fin n) : Multiset ℕ :=
  (Finset.univ.erase (H v)).val.map fun r => Fintype.card {u // H u = r}

theorem markedFibreSignature_eq_cons (H : Fin n → Fin n) (v : Fin n) :
    markedFibreSignature H v =
      (true, Fintype.card {u // H u = H v}) ::ₘ
        (otherFibreSizes H v).map (fun s => (false, s)) := by
  have hu : (Finset.univ : Finset (Fin n)).val =
      H v ::ₘ (Finset.univ.erase (H v)).val := by
    calc
      _ = (insert (H v) (Finset.univ.erase (H v))).val :=
        congrArg Finset.val (Finset.insert_erase (Finset.mem_univ (H v))).symm
      _ = _ := Finset.insert_val_of_notMem (Finset.notMem_erase _ _)
  unfold markedFibreSignature otherFibreSizes
  rw [hu, Multiset.map_cons, Multiset.map_map]
  simp only [decide_true]
  congr 1
  apply Multiset.map_congr rfl
  intro r hr
  change r ∈ (Finset.univ : Finset (Fin n)).erase (H v) at hr
  have hne : r ≠ H v := (Finset.mem_erase.mp hr).1
  simp only [hne, decide_false, Function.comp_apply]

/-- Equal finite multisets of labels have a label-preserving bijection. -/
theorem exists_equiv_of_multiset_map_eq {I J A : Type*} [Fintype I] [Fintype J]
    (f : I → A) (g : J → A)
    (h : Finset.univ.val.map f = Finset.univ.val.map g) :
    ∃ σ : I ≃ J, ∀ i, g (σ i) = f i := by
  have hcards (a : A) : Fintype.card {i // f i = a} = Fintype.card {j // g j = a} := by
    have hc := congrArg (Multiset.count a) h
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa only [Multiset.count_map, Finset.card, Finset.filter_val, eq_comm] using hc
  let fibres (a : A) := Fintype.equivOfCardEq (hcards a)
  exact ⟨Equiv.ofFiberEquiv fibres, Equiv.ofFiberEquiv_map fibres⟩

/-- The tagged multiset signature supplies a matching of all fibres and the marked one. -/
theorem exists_matching_of_markedFibreSignature_eq (H J : Fin n → Fin n) (v : Fin n)
    (h : markedFibreSignature H v = markedFibreSignature J v) :
    ∃ σ : Fin n ≃ Fin n,
      (∀ r, Fintype.card {u // H u = r} = Fintype.card {u // J u = σ r}) ∧
      σ (H v) = J v := by
  obtain ⟨σ, hσ⟩ := exists_equiv_of_multiset_map_eq
    (fun r => (decide (r = H v), Fintype.card {u // H u = r}))
    (fun r => (decide (r = J v), Fintype.card {u // J u = r})) h
  refine ⟨σ, fun r => (congrArg Prod.snd (hσ r)).symm, ?_⟩
  have hm := congrArg Prod.fst (hσ (H v))
  simpa only [decide_true, decide_eq_true_eq] using hm

theorem markedFibreValue_eq_of_signature (H J : Fin n → Fin n)
    (v : Fin n) (hv : ∀ u, u ≤ v)
    (h : markedFibreSignature H v = markedFibreSignature J v) (m : ℕ) (β : Fin m) :
    markedRelationValue (fibreRelation H) v m β =
      markedRelationValue (fibreRelation J) v m β := by
  obtain ⟨σ, hcards, hmark⟩ := exists_matching_of_markedFibreSignature_eq H J v h
  exact markedFibreValue_eq_of_matching_sizes H J σ hcards v hv hmark m β

theorem markedE_eq_of_signature {D E : Diagram n} (θ : Orientation D) (η : Orientation E)
    (v : Fin n) (hv : ∀ u, u ≤ v)
    (h : markedFibreSignature θ.hrv v = markedFibreSignature η.hrv v)
    (m : ℕ) (β : Fin m) : markedE θ v m β = markedE η v m β :=
  markedFibreValue_eq_of_signature θ.hrv η.hrv v hv h m β

/-- Only the last fibre's size and the multiset of the other sizes determine right-marked E. -/
theorem markedE_eq_of_fibre_sizes {D E : Diagram n} (θ : Orientation D) (η : Orientation E)
    (v : Fin n) (hv : ∀ u, u ≤ v)
    (hlast : Fintype.card {u // θ.hrv u = θ.hrv v} =
      Fintype.card {u // η.hrv u = η.hrv v})
    (hothers : otherFibreSizes θ.hrv v = otherFibreSizes η.hrv v)
    (m : ℕ) (β : Fin m) : markedE θ v m β = markedE η v m β := by
  apply markedE_eq_of_signature θ η v hv
  rw [markedFibreSignature_eq_cons, markedFibreSignature_eq_cons, hlast, hothers]

private theorem multiset_eq_of_positive_filter_eq {s t : Multiset ℕ}
    (hcard : s.card = t.card) (hpos : s.filter (0 < ·) = t.filter (0 < ·)) : s = t := by
  have decomp (a : Multiset ℕ) :
      a.filter (0 < ·) + Multiset.replicate (a.count 0) 0 = a := by
    simpa only [Nat.not_lt, Nat.le_zero, Multiset.filter_eq'] using
      (Multiset.filter_add_not (p := (0 < ·)) a)
  have hs := congrArg Multiset.card (decomp s)
  have ht := congrArg Multiset.card (decomp t)
  simp only [Multiset.card_add, Multiset.card_replicate] at hs ht
  have hz : s.count 0 = t.count 0 := by
    rw [hpos] at hs
    lia
  rw [← decomp s, ← decomp t, hpos, hz]

/-- Empty root fibres can be discarded: their number is determined by the common vertex count. -/
theorem markedE_eq_of_nonempty_fibre_sizes {D E : Diagram n}
    (θ : Orientation D) (η : Orientation E) (v : Fin n) (hv : ∀ u, u ≤ v)
    (hlast : Fintype.card {u // θ.hrv u = θ.hrv v} =
      Fintype.card {u // η.hrv u = η.hrv v})
    (hothers : (otherFibreSizes θ.hrv v).filter (0 < ·) =
      (otherFibreSizes η.hrv v).filter (0 < ·)) (m : ℕ) (β : Fin m) :
    markedE θ v m β = markedE η v m β := by
  apply markedE_eq_of_fibre_sizes θ η v hv hlast
  apply multiset_eq_of_positive_filter_eq ?_ hothers
  simp only [otherFibreSizes, Multiset.card_map]
  change (Finset.univ.erase (θ.hrv v)).card = (Finset.univ.erase (η.hrv v)).card
  rw [Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_erase_of_mem (Finset.mem_univ _)]

end

end VerticalStripLLT.Circular.DiagramProof
