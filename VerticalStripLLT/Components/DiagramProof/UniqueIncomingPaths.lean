import VerticalStripLLT.Components.DiagramProof.FiniteCoverPaths

/-!
# Directed paths from a least weak-block vertex

A relation with unique incoming edges has a common ancestor for every two
vertices in the same weak component.  Applied to reachability covers of a
forward relation, this makes a least vertex of a weak block reach the whole
block.
-/

namespace VerticalStripLLT.Circular.DiagramProof

variable {V : Type*} {R : V → V → Prop}

/-- A directed path gives a weak-reachability witness. -/
theorem eqvGen_of_reflTransGen {a b : V} (h : Relation.ReflTransGen R a b) :
    Relation.EqvGen R a b := by
  induction h with
  | refl => exact Relation.EqvGen.refl _
  | tail _ hstep ih =>
    exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ hstep)

/-- With unique incoming edges, two weakly related vertices have a common
directed ancestor. -/
theorem exists_common_ancestor_of_eqvGen_of_leftUnique
    (hunique : Relator.LeftUnique R) {u v : V} (huv : Relation.EqvGen R u v) :
    ∃ w, Relation.ReflTransGen R w u ∧ Relation.ReflTransGen R w v := by
  induction huv with
  | rel a b hab =>
    exact ⟨a, Relation.ReflTransGen.refl, Relation.ReflTransGen.single hab⟩
  | refl a => exact ⟨a, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | symm _ _ _ ih =>
    obtain ⟨w, hwu, hwv⟩ := ih
    exact ⟨w, hwv, hwu⟩
  | trans a b c _ _ ihab ihbc =>
    obtain ⟨x, hxa, hxb⟩ := ihab
    obtain ⟨y, hyb, hyc⟩ := ihbc
    have htotal := Relation.ReflTransGen.total_of_right_unique hunique.flip
      (Relation.reflTransGen_swap.mpr hxb) (Relation.reflTransGen_swap.mpr hyb)
    rcases htotal with hxy | hyx
    · exact ⟨y, (Relation.reflTransGen_swap.mp hxy).trans hxa, hyc⟩
    · exact ⟨x, hxa, (Relation.reflTransGen_swap.mp hyx).trans hyc⟩

variable {n : ℕ} {R : Fin n → Fin n → Prop}

/-- Replacing selected edges by directed paths of covers preserves every weak block. -/
theorem eqvGen_relationCover_iff (hforward : ∀ ⦃u v⦄, R u v → u < v) (u v : Fin n) :
    Relation.EqvGen (RelationCover R) u v ↔ Relation.EqvGen R u v := by
  constructor
  · exact Relation.EqvGen.eqvGen_le
      (fun x y h => Relation.EqvGen.rel x y (rel_of_relationCover hforward h)) u v
  · exact Relation.EqvGen.eqvGen_le
      (fun _ _ h => eqvGen_of_reflTransGen (relationCover_path_of_rel hforward h)) u v

/-- If `u` is least in its weak block and incoming reachability covers are
unique, then `u` reaches every vertex in that block. -/
theorem reachable_of_eqvGen_of_minimal_of_leftUnique_relationCover
    (hforward : ∀ ⦃u v⦄, R u v → u < v) {u v : Fin n}
    (hmin : ∀ w, Relation.EqvGen R u w → u ≤ w)
    (hweak : Relation.EqvGen R u v)
    (hunique : Relator.LeftUnique (RelationCover R)) :
    Relation.ReflTransGen R u v := by
  have hweakCover := (eqvGen_relationCover_iff hforward u v).mpr hweak
  obtain ⟨w, hwu, hwv⟩ :=
    exists_common_ancestor_of_eqvGen_of_leftUnique hunique hweakCover
  have hwuR : Relation.ReflTransGen R w u :=
    reachable_of_relationCover_path hforward hwu
  have huw : Relation.EqvGen R u w :=
    Relation.EqvGen.symm _ _ (eqvGen_of_reflTransGen hwuR)
  have huwle : u ≤ w := hmin w huw
  have hwule : w ≤ u := reachable_le hforward hwuR
  have hwuEq : w = u := le_antisymm hwule huwle
  subst w
  exact reachable_of_relationCover_path hforward hwv

end VerticalStripLLT.Circular.DiagramProof
