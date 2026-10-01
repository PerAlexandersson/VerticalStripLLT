import VerticalStripLLT.Components.DiagramProof.RelationPaths
import Mathlib.Data.Fin.Rev
import Mathlib.Order.Fin.Basic

/-! Transport of finite paths, covers and weak connections through order reversal. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {n : ℕ} {R S : Fin n → Fin n → Prop}

private theorem reflTransGen_reverse {V W : Type*} {P : V → V → Prop}
    {Q : W → W → Prop} (f : V → W) (hmap : ∀ u v, P u v → Q (f v) (f u))
    {u v : V} (h : Relation.ReflTransGen P u v) :
    Relation.ReflTransGen Q (f v) (f u) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact (Relation.ReflTransGen.single (hmap _ _ hs)).trans ih

theorem reflTransGen_rev_iff
    (hrel : ∀ u v, S u v ↔ R v.rev u.rev) (u v : Fin n) :
    Relation.ReflTransGen S u v ↔ Relation.ReflTransGen R v.rev u.rev := by
  constructor
  · exact reflTransGen_reverse Fin.rev (fun x y => (hrel x y).mp)
  · intro h
    have hp := reflTransGen_reverse Fin.rev (P := R) (Q := S) (fun x y hs =>
      (hrel y.rev x.rev).mpr (by simpa only [Fin.rev_rev] using hs)) h
    simpa only [Fin.rev_rev] using hp

theorem relationCover_rev_iff
    (hrel : ∀ u v, S u v ↔ R v.rev u.rev) (u v : Fin n) :
    RelationCover S u v ↔ RelationCover R v.rev u.rev := by
  constructor
  · rintro ⟨huv, hpath, hmin⟩
    refine ⟨Fin.rev_lt_rev.mpr huv, (reflTransGen_rev_iff hrel u v).mp hpath, ?_⟩
    intro w hwv hwu hpath'
    have hwu' : u < w.rev := by simpa using Fin.rev_lt_rev.mpr hwu
    have hwv' : w.rev < v := by simpa using Fin.rev_lt_rev.mpr hwv
    apply hmin w.rev hwu' hwv'
    constructor
    · apply (reflTransGen_rev_iff hrel u w.rev).mpr
      simpa only [Fin.rev_rev] using hpath'.2
    · apply (reflTransGen_rev_iff hrel w.rev v).mpr
      simpa only [Fin.rev_rev] using hpath'.1
  · rintro ⟨hvu, hpath, hmin⟩
    refine ⟨Fin.rev_lt_rev.mp hvu, (reflTransGen_rev_iff hrel u v).mpr hpath, ?_⟩
    intro w huw hwv hpath'
    exact hmin w.rev (Fin.rev_lt_rev.mpr hwv) (Fin.rev_lt_rev.mpr huw)
      ⟨(reflTransGen_rev_iff hrel w v).mp hpath'.2,
        (reflTransGen_rev_iff hrel u w).mp hpath'.1⟩

private theorem eqvGen_reverse {V W : Type*} {P : V → V → Prop}
    {Q : W → W → Prop} (f : V → W) (hmap : ∀ u v, P u v → Q (f v) (f u))
    {u v : V} (h : Relation.EqvGen P u v) : Relation.EqvGen Q (f u) (f v) := by
  induction h with
  | rel _ _ hs => exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (hmap _ _ hs))
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem eqvGen_rev_iff
    (hrel : ∀ u v, S u v ↔ R v.rev u.rev) (u v : Fin n) :
    Relation.EqvGen S u v ↔ Relation.EqvGen R u.rev v.rev := by
  constructor
  · exact eqvGen_reverse Fin.rev (fun x y => (hrel x y).mp)
  · intro h
    have hp := eqvGen_reverse Fin.rev (P := R) (Q := S) (fun x y hs =>
      (hrel y.rev x.rev).mpr (by simpa only [Fin.rev_rev] using hs)) h
    simpa only [Fin.rev_rev] using hp

end VerticalStripLLT.Circular.DiagramProof
