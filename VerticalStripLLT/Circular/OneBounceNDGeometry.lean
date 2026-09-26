import VerticalStripLLT.Circular.StrictVals
import VerticalStripLLT.Circular.LowerStrictRows
import VerticalStripLLT.Circular.ShortenStrictMeasure

/-! The seven diagrams of the one-bounce ND reduction and their geometric identifications. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ}

theorem next_congr (A A' : CircularArea n) (i : Fin n) : A.next i = A'.next i :=
  Fin.ext rfl

@[simp] theorem raisedIncl_val (D : Diagram n) (e : Edge D.area)
    (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
    (hb : D.area.area e.head + 1 < n) (f : Edge D.area) :
    (D.raisedIncl e heq hb f).1 = f.1 := rfl

namespace NDLocalData

variable {D : Diagram n} {t : ℤ} (B : D.NDLocalData t)

theorem g_length : B.g.length.val = D.area.area (D.residue (D.boundary t)) + 1 := by
  rw [(D.strict_corner B.g B.hg).1, B.areaEq]

theorem i_ne_y : D.residue (D.boundary t) ≠ B.g.head := by
  intro h
  have := B.areaEq
  rw [← h] at this
  lia

theorem fhead_ne_i : B.f.head ≠ D.residue (D.boundary t) := by
  rw [← B.ft]
  exact B.f.tail_ne_head.symm

theorem f_ne_g : B.f ≠ B.g := fun h => B.head_ne (congrArg Edge.head h)

include B in
theorem no_strict_at_i : ∀ e ∈ D.strict, e.head ≠ D.residue (D.boundary t) :=
  fun e he h => B.nonstrict ⟨e, he, h⟩

include B in
theorem i_not_mem_vals : ∀ p ∈ D.strictVals, p.1 ≠ D.residue (D.boundary t) := by
  intro p hp h
  obtain ⟨e, he, rfl⟩ := (D.mem_strictVals p).mp hp
  exact B.no_strict_at_i e he h

end NDLocalData
end VerticalStripLLT.Circular.Diagram

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ}

theorem pair_ext {p q : Fin n × Fin n} (h1 : p.1 = q.1) (h2 : p.2.val = q.2.val) : p = q :=
  Prod.ext h1 (Fin.ext h2)

theorem val_eq_of_mem_strictVals_head (D : Diagram n) {p : Fin n × Fin n}
    (hp : p ∈ D.strictVals) {e : Edge D.area} (he : e ∈ D.strict) (hh : p.1 = e.head) :
    p = e.1 := by
  obtain ⟨e', he', rfl⟩ := (D.mem_strictVals p).mp hp
  rw [D.strict_edge_eq_of_head_eq he' he hh]

theorem not_strictAt_of_vals (P : Diagram n) (z : ℤ)
    (h : ∀ p ∈ P.strictVals, p.1 ≠ P.residue z) : ¬ P.strictAt z := by
  rw [strictAt_iff_strictVals]
  rintro ⟨p, hp, hh⟩
  exact h p hp hh

theorem boundary_tail_same (P : Diagram n) (e : Edge P.area)
    (h : P.area.area (P.area.next e.tail) = P.area.area e.tail + 1) :
    P.boundary ((e.tail.val : ℤ) + 1) = P.boundary (e.tail.val : ℤ) := by
  unfold boundary
  rw [P.residue_succ, Orientation.residue_intCast_eq, h]
  push_cast
  ring

theorem residue_tail_succ (P : Diagram n) (e : Edge P.area) :
    P.residue ((e.tail.val : ℤ) + 1) = P.area.next e.tail := by
  rw [P.residue_succ, Orientation.residue_intCast_eq]

theorem gap_of_le {D P : Diagram n} {h : Fin n}
    (hgap : D.area.area (D.area.next h) < D.area.area h)
    (hle : ∀ v, P.area.area v ≤ D.area.area v) (heq : P.area.area h = D.area.area h) :
    P.area.area (P.area.next h) < P.area.area h := by
  rw [heq, next_congr P.area D.area]
  exact (hle _).trans_lt hgap

theorem doubledArea_of_lower_one {D P : Diagram n} (h : Fin n) (hpos : 1 ≤ D.area.area h)
    (harea : P.area.area = Function.update D.area.area h (D.area.area h - 1))
    (hcard : P.strict.card = D.strict.card) :
    P.doubledArea + 2 = D.doubledArea := by
  have hp (i : Fin n) : P.area.area i + (if i = h then 1 else 0) = D.area.area i := by
    rw [harea]
    by_cases hi : i = h
    · subst i
      simp only [Function.update_self, ↓reduceIte]
      lia
    · rw [Function.update_of_ne hi]
      simp only [hi, ↓reduceIte, add_zero]
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun i _ => hp i)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hs
  have hbound := P.strict_card_le_area_sum
  unfold doubledArea
  lia

end VerticalStripLLT.Circular.Diagram

namespace VerticalStripLLT.Circular.Diagram.NDLocalData

open scoped Classical

variable {n : ℕ} {D : Diagram n} {t : ℤ} (B : D.NDLocalData t)

/-- `N`: the upper strict edge `g` made normal. -/
noncomputable def ndN : Diagram n := D.unstrict B.g B.hg

/-- `E`: the upper strict corner `g` deleted. -/
noncomputable def ndE : Diagram n := D.deleteCorner B.g (D.strict_corner B.g B.hg)

/-- The corner at row `x` created by deleting `g`. -/
noncomputable def ell : Edge B.ndE.area :=
  D.loweredEdge (D.residue (D.boundary t)) B.g B.hg B.upper_head B.areaEq B.areaPos

theorem ell_corner : IsCorner B.ell :=
  D.loweredEdge_corner _ B.g B.hg B.upper_head B.areaEq B.areaPos

theorem ell_head : B.ell.head = D.residue (D.boundary t) := rfl

theorem ell_length : B.ell.length.val = D.area.area (D.residue (D.boundary t)) := rfl

/-- `S` is the actual `lowerStrict` diagram. -/
theorem lowered_eq : B.lowered = B.ndE.strictify B.ell B.ell_corner := rfl

/-- `J`: delete the newly strict corner at row `x` from `S`. -/
noncomputable def ndJ : Diagram n := B.ndE.deleteCorner B.ell B.ell_corner

theorem vals_ndN : B.ndN.strictVals = D.strictVals.erase B.g.1 :=
  D.strictVals_unstrict B.g B.hg

theorem vals_ndE : B.ndE.strictVals = D.strictVals.erase B.g.1 :=
  D.strictVals_deleteCorner B.g _

theorem ell_val_not_mem : B.ell.1 ∉ D.strictVals.erase B.g.1 := fun h =>
  B.i_not_mem_vals _ (Finset.mem_of_mem_erase h) rfl

theorem vals_lowered : B.lowered.strictVals = insert B.ell.1 (D.strictVals.erase B.g.1) := by
  rw [lowered_eq, strictVals_strictify, vals_ndE]

theorem vals_ndJ : B.ndJ.strictVals = D.strictVals.erase B.g.1 := by
  rw [ndJ, strictVals_deleteCorner, vals_ndE]
  exact Finset.erase_eq_of_notMem B.ell_val_not_mem

theorem vals_shortened : B.shortened.strictVals =
    insert (D.shortenedEdge B.f B.hf B.rootLength).1 (D.strictVals.erase B.f.1) :=
  D.strictVals_shortenStrict _ _ _ _

theorem area_ndN : B.ndN.area.area = D.area.area := rfl

theorem area_ndE : B.ndE.area.area =
    Function.update D.area.area B.g.head (D.area.area B.g.head - 1) := rfl

theorem area_lowered : B.lowered.area.area =
    Function.update D.area.area B.g.head (D.area.area B.g.head - 1) := rfl

theorem area_ndJ : B.ndJ.area.area =
    Function.update (Function.update D.area.area B.g.head (D.area.area B.g.head - 1))
      (D.residue (D.boundary t)) (D.area.area (D.residue (D.boundary t)) - 1) := by
  change Function.update B.ndE.area.area B.ell.head (B.ndE.area.area B.ell.head - 1) = _
  rw [area_ndE, ell_head, Function.update_of_ne B.i_ne_y]

theorem area_shortened : B.shortened.area.area =
    Function.update D.area.area B.f.head (D.area.area B.f.head - 1) := rfl

end VerticalStripLLT.Circular.Diagram.NDLocalData

namespace VerticalStripLLT.Circular.Diagram.NDLocalData

open scoped Classical

variable {n : ℕ} {D : Diagram n} {t : ℤ} (B : D.NDLocalData t)

theorem f_val_mem : B.f.1 ∈ D.strictVals := (D.val_mem_strictVals _).mpr B.hf

theorem g_val_mem : B.g.1 ∈ D.strictVals := (D.val_mem_strictVals _).mpr B.hg

theorem f_val_ne_g_val : B.f.1 ≠ B.g.1 := fun h => B.head_ne (congrArg Prod.fst h)

theorem vals_head_ne_y : ∀ p ∈ D.strictVals.erase B.g.1, p.1 ≠ B.g.head := fun _ hp h =>
  (Finset.mem_erase.mp hp).1 (D.val_eq_of_mem_strictVals_head (Finset.mem_erase.mp hp).2 B.hg h)

theorem vals_head_ne_i : ∀ p ∈ D.strictVals.erase B.g.1, p.1 ≠ D.residue (D.boundary t) :=
  fun p hp => B.i_not_mem_vals p (Finset.mem_of_mem_erase hp)

theorem f_val_mem_erase_g : B.f.1 ∈ D.strictVals.erase B.g.1 :=
  Finset.mem_erase.mpr ⟨B.f_val_ne_g_val, B.f_val_mem⟩

/-! ### The root edge in `N`, `J` and `S` -/

/-- The root `f` viewed in `N`. -/
noncomputable def fN : Edge B.ndN.area := B.f.transport B.f.length_le_area

theorem fN_mem : B.fN ∈ B.ndN.strict := by
  refine (B.ndN.transport_mem_strict B.f _).mpr ?_
  rw [vals_ndN]
  exact B.f_val_mem_erase_g

theorem gapN : B.ndN.area.area (B.ndN.area.next B.fN.head) < B.ndN.area.area B.fN.head :=
  B.rootGap

/-- `N′`: shorten the root in `N`. -/
noncomputable def ndNs : Diagram n := B.ndN.shortenStrict B.fN B.fN_mem B.rootLength B.gapN

theorem area_ndJ_fhead : B.ndJ.area.area B.f.head = D.area.area B.f.head := by
  rw [area_ndJ, Function.update_of_ne B.fhead_ne_i, Function.update_of_ne B.head_ne]

theorem area_ndJ_le (v : Fin n) : B.ndJ.area.area v ≤ D.area.area v := by
  rw [area_ndJ]
  simp only [Function.update_apply]
  split_ifs <;> lia

/-- The root `f` viewed in `J`. -/
noncomputable def fJ : Edge B.ndJ.area :=
  B.f.transport (B.area_ndJ_fhead ▸ B.f.length_le_area)

theorem fJ_mem : B.fJ ∈ B.ndJ.strict := by
  refine (B.ndJ.transport_mem_strict B.f _).mpr ?_
  rw [vals_ndJ]
  exact B.f_val_mem_erase_g

theorem gapJ : B.ndJ.area.area (B.ndJ.area.next B.fJ.head) < B.ndJ.area.area B.fJ.head :=
  gap_of_le B.rootGap B.area_ndJ_le B.area_ndJ_fhead

/-- `J′`: shorten the root in `J`. -/
noncomputable def ndJs : Diagram n := B.ndJ.shortenStrict B.fJ B.fJ_mem B.rootLength B.gapJ

theorem area_lowered_fhead : B.lowered.area.area B.f.head = D.area.area B.f.head := by
  rw [area_lowered, Function.update_of_ne B.head_ne]

theorem area_lowered_le (v : Fin n) : B.lowered.area.area v ≤ D.area.area v := by
  rw [area_lowered]
  simp only [Function.update_apply]
  split_ifs <;> lia

/-- The root `f` viewed in `S`. -/
noncomputable def fS : Edge B.lowered.area :=
  B.f.transport (B.area_lowered_fhead ▸ B.f.length_le_area)

theorem fS_mem : B.fS ∈ B.lowered.strict := by
  refine (B.lowered.transport_mem_strict B.f _).mpr ?_
  rw [vals_lowered]
  exact Finset.mem_insert_of_mem B.f_val_mem_erase_g

theorem gapS : B.lowered.area.area (B.lowered.area.next B.fS.head) <
    B.lowered.area.area B.fS.head :=
  gap_of_le B.rootGap B.area_lowered_le B.area_lowered_fhead

/-- `R`: shorten the root in `S`. -/
noncomputable def ndR : Diagram n := B.lowered.shortenStrict B.fS B.fS_mem B.rootLength B.gapS

/-! ### The upper edge `g` in `Q` -/

theorem area_shortened_y : B.shortened.area.area B.g.head = D.area.area B.g.head := by
  rw [area_shortened, Function.update_of_ne B.head_ne.symm]

/-- The upper edge `g` viewed in `Q`. -/
noncomputable def gQ : Edge B.shortened.area :=
  B.g.transport (B.area_shortened_y ▸ B.g.length_le_area)

theorem shortened_val_head : (D.shortenedEdge B.f B.hf B.rootLength).1.1 = B.f.head := rfl

theorem shortened_val_ne_g : (D.shortenedEdge B.f B.hf B.rootLength).1 ≠ B.g.1 :=
  fun h => B.head_ne
    (show (D.shortenedEdge B.f B.hf B.rootLength).1.1 = B.g.1.1 from congrArg Prod.fst h)

theorem shortened_val_ne_ell : (D.shortenedEdge B.f B.hf B.rootLength).1 ≠ B.ell.1 :=
  fun h => B.fhead_ne_i
    (show (D.shortenedEdge B.f B.hf B.rootLength).1.1 = B.ell.1.1 from congrArg Prod.fst h)

theorem gQ_mem : B.gQ ∈ B.shortened.strict := by
  refine (B.shortened.transport_mem_strict B.g _).mpr ?_
  rw [vals_shortened]
  exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨B.f_val_ne_g_val.symm, B.g_val_mem⟩)

/-- `E′`: delete the corner `g` from `Q`. -/
noncomputable def ndEs : Diagram n :=
  B.shortened.deleteCorner B.gQ (B.shortened.strict_corner B.gQ B.gQ_mem)

theorem vals_ndEs : B.ndEs.strictVals =
    (insert (D.shortenedEdge B.f B.hf B.rootLength).1 (D.strictVals.erase B.f.1)).erase B.g.1 := by
  rw [ndEs, strictVals_deleteCorner, vals_shortened]
  rfl

theorem area_ndEs : B.ndEs.area.area =
    Function.update (Function.update D.area.area B.f.head (D.area.area B.f.head - 1))
      B.g.head (D.area.area B.g.head - 1) := by
  change Function.update B.shortened.area.area B.g.head
    (B.shortened.area.area B.g.head - 1) = _
  rw [B.area_shortened_y, area_shortened]

theorem area_ndEs_i : B.ndEs.area.area (D.residue (D.boundary t)) =
    D.area.area (D.residue (D.boundary t)) := by
  rw [area_ndEs, Function.update_of_ne B.i_ne_y, Function.update_of_ne B.fhead_ne_i.symm]

/-- The row-`x` corner viewed in `E′`. -/
noncomputable def ellEs : Edge B.ndEs.area :=
  B.ell.transport (by rw [ell_head, area_ndEs_i]; exact le_of_eq rfl)

theorem ellEs_corner : IsCorner B.ellEs := by
  constructor
  · change D.area.area (D.residue (D.boundary t)) = B.ndEs.area.area (D.residue (D.boundary t))
    rw [area_ndEs_i]
  · change B.ndEs.area.area (D.area.next (D.residue (D.boundary t))) ≤
      B.ndEs.area.area (D.residue (D.boundary t))
    rw [area_ndEs_i, ← B.upper_head, area_ndEs, Function.update_self, B.areaEq]
    lia

theorem ellEs_not_mem : B.ellEs ∉ B.ndEs.strict := by
  rw [← B.ndEs.val_mem_strictVals, vals_ndEs]
  intro h
  rcases Finset.mem_insert.mp (Finset.mem_of_mem_erase h) with h | h
  · exact B.shortened_val_ne_ell h.symm
  · exact B.i_not_mem_vals _ (Finset.mem_of_mem_erase h) rfl

end VerticalStripLLT.Circular.Diagram.NDLocalData

namespace VerticalStripLLT.Circular.Diagram.NDLocalData

open scoped Classical

variable {n : ℕ} {D : Diagram n} {t : ℤ} (B : D.NDLocalData t)

theorem ell_val_ne_f_val : B.ell.1 ≠ B.f.1 :=
  fun h => B.fhead_ne_i (show B.f.1.1 = B.ell.1.1 from (congrArg Prod.fst h).symm)

/-- `N′` is `Q` with `g` made normal. -/
theorem ndNs_eq : B.ndNs = B.shortened.unstrict B.gQ B.gQ_mem := by
  refine ext_of_strictVals (by rfl) ?_
  rw [ndNs, strictVals_shortenStrict, strictVals_unstrict, vals_ndN, vals_shortened]
  change insert (D.shortenedEdge B.f B.hf B.rootLength).1 ((D.strictVals.erase B.g.1).erase B.f.1)
    = (insert (D.shortenedEdge B.f B.hf B.rootLength).1 (D.strictVals.erase B.f.1)).erase B.g.1
  rw [Finset.erase_insert_of_ne B.shortened_val_ne_g, Finset.erase_right_comm]

/-- Strictifying the row-`x` corner of `E′` gives `R`. -/
theorem ndEs_strictify_eq : B.ndEs.strictify B.ellEs B.ellEs_corner = B.ndR := by
  apply ext_of_strictVals
  · rw [area_strictify, area_ndEs]
    change _ = Function.update B.lowered.area.area B.f.head (B.lowered.area.area B.f.head - 1)
    rw [area_lowered]
    have h1 := B.head_ne
    funext v
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · rw [strictVals_strictify, ndR, strictVals_shortenStrict, vals_ndEs, vals_lowered]
    change insert B.ell.1 ((insert (D.shortenedEdge B.f B.hf B.rootLength).1
        (D.strictVals.erase B.f.1)).erase B.g.1) =
      insert (D.shortenedEdge B.f B.hf B.rootLength).1
        ((insert B.ell.1 (D.strictVals.erase B.g.1)).erase B.f.1)
    rw [Finset.erase_insert_of_ne B.shortened_val_ne_g,
      Finset.erase_insert_of_ne B.ell_val_ne_f_val, Finset.insert_comm, Finset.erase_right_comm]

/-- Deleting the row-`x` corner of `E′` gives `J′`. -/
theorem ndEs_deleteCorner_eq : B.ndEs.deleteCorner B.ellEs B.ellEs_corner = B.ndJs := by
  apply ext_of_strictVals
  · rw [area_deleteCorner]
    change _ = Function.update B.ndJ.area.area B.f.head (B.ndJ.area.area B.f.head - 1)
    rw [area_ndJ]
    change Function.update B.ndEs.area.area (D.residue (D.boundary t))
      (B.ndEs.area.area (D.residue (D.boundary t)) - 1) = _
    rw [area_ndEs]
    have h1 := B.head_ne
    have h2 := B.i_ne_y
    have h3 := B.fhead_ne_i
    funext v
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · rw [strictVals_deleteCorner, ndJs, strictVals_shortenStrict, vals_ndJ]
    have hn : B.ellEs.1 ∉ B.ndEs.strictVals := by
      rw [B.ndEs.val_mem_strictVals]
      exact B.ellEs_not_mem
    rw [Finset.erase_eq_of_notMem hn, vals_ndEs]
    change (insert (D.shortenedEdge B.f B.hf B.rootLength).1
        (D.strictVals.erase B.f.1)).erase B.g.1 =
      insert (D.shortenedEdge B.f B.hf B.rootLength).1 ((D.strictVals.erase B.g.1).erase B.f.1)
    rw [Finset.erase_insert_of_ne B.shortened_val_ne_g, Finset.erase_right_comm]

end VerticalStripLLT.Circular.Diagram.NDLocalData

namespace VerticalStripLLT.Circular.Diagram.NDLocalData

open scoped Classical

variable {n : ℕ} {D : Diagram n} {t : ℤ} (B : D.NDLocalData t)

/-! ### The DN successor of `S` is `Q` -/

/-- The lowered edge, strict in `S`. -/
noncomputable def ellS : Edge B.lowered.area := B.ell

theorem ellS_mem : B.ellS ∈ B.lowered.strict := Finset.mem_insert_self _ _

theorem fS_ne_ellS : B.fS ≠ B.ellS := fun h => B.fhead_ne_i (congrArg Edge.head h)

theorem fS_contact : B.fS.tail = B.ellS.head := B.ft

theorem lowered_heq : B.lowered.area.area (B.lowered.area.next B.ellS.head) =
    B.lowered.area.area B.ellS.head := by
  change B.lowered.area.area (D.area.next (D.residue (D.boundary t))) =
    B.lowered.area.area (D.residue (D.boundary t))
  rw [← B.upper_head, area_lowered, Function.update_self, Function.update_of_ne B.i_ne_y,
    B.areaEq]
  lia

theorem lowered_hb : B.lowered.area.area B.ellS.head + 1 < n := by
  change B.lowered.area.area (D.residue (D.boundary t)) + 1 < n
  rw [area_lowered, Function.update_of_ne B.i_ne_y, ← B.areaEq]
  exact D.area.bound _

theorem lowered_hns : ∀ e ∈ B.lowered.strict, e.head ≠ B.lowered.area.next B.ellS.head := by
  intro e he
  have hv := (B.lowered.val_mem_strictVals e).mpr he
  rw [vals_lowered] at hv
  change e.1.1 ≠ D.area.next (D.residue (D.boundary t))
  rw [← B.upper_head]
  rcases Finset.mem_insert.mp hv with h | h
  · rw [h]
    exact B.i_ne_y
  · exact B.vals_head_ne_y _ h

/-- The DN successor of `S` along its root. -/
noncomputable def dnS : Diagram n :=
  B.lowered.dnSuccessor B.ellS B.fS B.ellS_mem B.fS_mem B.fS_ne_ellS B.lowered_heq
    B.lowered_hb B.lowered_hns B.rootLength B.gapS

theorem raised_val :
    (B.lowered.raisedEdge B.ellS B.ellS_mem B.lowered_heq B.lowered_hb).1 = B.g.1 := by
  apply pair_ext
  · exact B.upper_head.symm
  · change B.ell.length.val + 1 = B.g.length.val
    rw [ell_length, g_length]

theorem area_raised : (B.lowered.raiseStrict B.ellS B.ellS_mem B.lowered_heq B.lowered_hb
    B.lowered_hns).area.area = D.area.area := by
  rw [area_raiseStrict]
  change Function.update B.lowered.area.area (D.area.next (D.residue (D.boundary t)))
    (B.lowered.area.area (D.residue (D.boundary t)) + 1) = _
  rw [← B.upper_head, area_lowered, Function.update_idem, Function.update_of_ne B.i_ne_y,
    ← B.areaEq, Function.update_eq_self]

/-- The exact DN successor identification: restoring `g` and shortening `f` gives `Q`. -/
theorem dnS_eq : B.dnS = B.shortened := by
  apply ext_of_strictVals
  · change Function.update
      (B.lowered.raiseStrict B.ellS B.ellS_mem B.lowered_heq B.lowered_hb B.lowered_hns).area.area
      B.f.head ((B.lowered.raiseStrict B.ellS B.ellS_mem B.lowered_heq B.lowered_hb
        B.lowered_hns).area.area B.f.head - 1) = _
    rw [area_raised, area_shortened]
  · rw [dnS, dnSuccessor, strictVals_shortenStrict, strictVals_raiseStrict, raised_val,
      vals_lowered, vals_shortened]
    change insert (D.shortenedEdge B.f B.hf B.rootLength).1
        ((insert B.g.1 ((insert B.ell.1 (D.strictVals.erase B.g.1)).erase B.ell.1)).erase B.f.1) =
      insert (D.shortenedEdge B.f B.hf B.rootLength).1 (D.strictVals.erase B.f.1)
    rw [Finset.erase_insert B.ell_val_not_mem, Finset.insert_erase B.g_val_mem]

/-! ### Hypotheses of the two direct NN relations -/

theorem ndN_hsame :
    B.ndN.boundary ((B.fN.tail.val : ℤ) + 1) = B.ndN.boundary (B.fN.tail.val : ℤ) := by
  apply boundary_tail_same
  change D.area.area (D.area.next B.f.tail) = D.area.area B.f.tail + 1
  rw [B.ft, ← B.upper_head, B.areaEq]

theorem ndN_hleft : ¬ B.ndN.strictAt (B.fN.tail.val : ℤ) := by
  apply not_strictAt_of_vals
  intro p hp
  rw [vals_ndN] at hp
  rw [Orientation.residue_intCast_eq]
  change p.1 ≠ B.f.tail
  rw [B.ft]
  exact B.vals_head_ne_i p hp

theorem ndN_hright : ¬ B.ndN.strictAt ((B.fN.tail.val : ℤ) + 1) := by
  apply not_strictAt_of_vals
  intro p hp
  rw [vals_ndN] at hp
  rw [residue_tail_succ]
  change p.1 ≠ D.area.next B.f.tail
  rw [B.ft, ← B.upper_head]
  exact B.vals_head_ne_y p hp

theorem ndJ_hsame :
    B.ndJ.boundary ((B.fJ.tail.val : ℤ) + 1) = B.ndJ.boundary (B.fJ.tail.val : ℤ) := by
  apply boundary_tail_same
  change B.ndJ.area.area (D.area.next B.f.tail) = B.ndJ.area.area B.f.tail + 1
  rw [B.ft, ← B.upper_head, area_ndJ, Function.update_of_ne B.i_ne_y.symm, Function.update_self,
    Function.update_self, B.areaEq]
  have := B.areaPos
  lia

theorem ndJ_hleft : ¬ B.ndJ.strictAt (B.fJ.tail.val : ℤ) := by
  apply not_strictAt_of_vals
  intro p hp
  rw [vals_ndJ] at hp
  rw [Orientation.residue_intCast_eq]
  change p.1 ≠ B.f.tail
  rw [B.ft]
  exact B.vals_head_ne_i p hp

theorem ndJ_hright : ¬ B.ndJ.strictAt ((B.fJ.tail.val : ℤ) + 1) := by
  apply not_strictAt_of_vals
  intro p hp
  rw [vals_ndJ] at hp
  rw [residue_tail_succ]
  change p.1 ≠ D.area.next B.f.tail
  rw [B.ft, ← B.upper_head]
  exact B.vals_head_ne_y p hp

theorem ell_not_mem_ndE : B.ell ∉ B.ndE.strict := by
  rw [← B.ndE.val_mem_strictVals, vals_ndE]
  exact B.ell_val_not_mem

/-! ### Geometric area decreases -/

theorem lowered_doubledArea : B.lowered.doubledArea + 2 = D.doubledArea := by
  apply doubledArea_of_lower_one B.g.head (by rw [B.areaEq]; lia) (B.area_lowered)
  rw [← card_strictVals, ← card_strictVals, vals_lowered,
    Finset.card_insert_of_notMem B.ell_val_not_mem, Finset.card_erase_of_mem B.g_val_mem]
  have := Finset.card_pos.mpr ⟨_, B.g_val_mem⟩
  lia

theorem ndR_doubledArea : B.ndR.doubledArea + 4 = D.doubledArea := by
  have h1 := B.lowered.shortenStrict_doubledArea B.fS B.fS_mem B.rootLength B.gapS
  have h2 := B.lowered_doubledArea
  change B.ndR.doubledArea + 2 = B.lowered.doubledArea at h1
  lia

end VerticalStripLLT.Circular.Diagram.NDLocalData

