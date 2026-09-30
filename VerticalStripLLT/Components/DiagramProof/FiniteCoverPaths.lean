import VerticalStripLLT.Components.DiagramProof.RelationPaths
import Mathlib.Order.Fin.Basic

/-!
# Finite paths through covers

For a forward relation on `Fin n`, every reachable pair is connected by a
path of reachability covers.  Thus a right-unique cover relation makes each
reachable set into one directed cover chain.
-/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

variable {n : ℕ} {R : Fin n → Fin n → Prop}

/-- A nontrivial path in a forward relation strictly increases its endpoint. -/
theorem reachable_lt_of_ne (hforward : ∀ ⦃u v⦄, R u v → u < v)
    {u v : Fin n} (h : Relation.ReflTransGen R u v) (huv : u ≠ v) : u < v := by
  rcases h.cases_head with heq | ⟨w, huw, hwv⟩
  · exact (huv heq).elim
  · exact (hforward huw).trans_le (reachable_le hforward hwv)

/-- Every path in a finite forward relation factors through its reachability covers. -/
theorem relationCover_reachable (hforward : ∀ ⦃u v⦄, R u v → u < v)
    {u v : Fin n} (h : Relation.ReflTransGen R u v) :
    Relation.ReflTransGen (RelationCover R) u v := by
  classical
  suffices hfactor : ∀ N, ∀ {x y : Fin n}, y.val - x.val = N →
      Relation.ReflTransGen R x y → Relation.ReflTransGen (RelationCover R) x y by
    exact hfactor _ rfl h
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro x y hN hxy
    by_cases hEq : x = y
    · subst y
      exact Relation.ReflTransGen.refl
    have hlt : x < y := reachable_lt_of_ne hforward hxy hEq
    by_cases hcover : RelationCover R x y
    · exact Relation.ReflTransGen.single hcover
    have hsplit : ∃ z, x < z ∧ z < y ∧
        Relation.ReflTransGen R x z ∧ Relation.ReflTransGen R z y := by
      by_contra hnone
      apply hcover
      refine ⟨hlt, hxy, ?_⟩
      intro z hxz hzy hz
      exact hnone ⟨z, hxz, hzy, hz.1, hz.2⟩
    obtain ⟨z, hxz, hzy, hxzPath, hzyPath⟩ := hsplit
    have hxzGap : z.val - x.val < N := by
      have hxz' : x.val < z.val := hxz
      have hzy' : z.val < y.val := hzy
      rw [← hN]
      lia
    have hzyGap : y.val - z.val < N := by
      have hxz' : x.val < z.val := hxz
      have hzy' : z.val < y.val := hzy
      rw [← hN]
      lia
    exact (ih _ hxzGap (x := x) (y := z) rfl hxzPath).trans
      (ih _ hzyGap (x := z) (y := y) rfl hzyPath)

/-- In particular, every selected edge has a path through reachability covers. -/
theorem relationCover_path_of_rel (hforward : ∀ ⦃u v⦄, R u v → u < v)
    {u v : Fin n} (huv : R u v) : Relation.ReflTransGen (RelationCover R) u v :=
  relationCover_reachable hforward (Relation.ReflTransGen.single huv)

/-- A path of reachability covers is a path of the original relation. -/
theorem reachable_of_relationCover_path (hforward : ∀ ⦃u v⦄, R u v → u < v)
    {u v : Fin n} (h : Relation.ReflTransGen (RelationCover R) u v) :
    Relation.ReflTransGen R u v := by
  exact Relation.ReflTransGen.mono
    (fun _ _ hcover => rel_of_relationCover hforward hcover) _ _ h

/-- Forward reachability agrees with reachability through its covers. -/
theorem relationCover_reachable_iff (hforward : ∀ ⦃u v⦄, R u v → u < v)
    {u v : Fin n} :
    Relation.ReflTransGen (RelationCover R) u v ↔ Relation.ReflTransGen R u v :=
  ⟨reachable_of_relationCover_path hforward, relationCover_reachable hforward⟩

/-- Right uniqueness of `R` implies right uniqueness of its reachability covers. -/
theorem relationCover_rightUnique_of_rightUnique
    (hforward : ∀ ⦃u v⦄, R u v → u < v) (hunique : Relator.RightUnique R) :
    Relator.RightUnique (RelationCover R) := by
  intro u v w huv huw
  exact hunique (rel_of_relationCover hforward huv)
    (rel_of_relationCover hforward huw)

/-- Under unique cover successors, two vertices reachable from one source lie on one cover chain. -/
theorem relationCover_reachable_total
    (hforward : ∀ ⦃u v⦄, R u v → u < v)
    (hunique : Relator.RightUnique (RelationCover R))
    {u v w : Fin n} (huv : Relation.ReflTransGen R u v)
    (huw : Relation.ReflTransGen R u w) :
    Relation.ReflTransGen (RelationCover R) v w ∨
      Relation.ReflTransGen (RelationCover R) w v :=
  Relation.ReflTransGen.total_of_right_unique hunique
    (relationCover_reachable hforward huv) (relationCover_reachable hforward huw)

/-- A terminal value constant across cover edges is constant on all forward paths. -/
theorem terminal_eq_of_relationCover_reachable {β : Type*}
    (hforward : ∀ ⦃u v⦄, R u v → u < v) (terminal : Fin n → β)
    (hterminal : ∀ ⦃u v⦄, RelationCover R u v → terminal u = terminal v)
    {u v : Fin n} (huv : Relation.ReflTransGen R u v) : terminal u = terminal v := by
  have hcover := relationCover_reachable hforward huv
  clear huv
  induction hcover with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (hterminal hstep)

/-- In particular, every original edge preserves a terminal value that is constant on covers. -/
theorem terminal_eq_of_rel {β : Type*}
    (hforward : ∀ ⦃u v⦄, R u v → u < v) (terminal : Fin n → β)
    (hterminal : ∀ ⦃u v⦄, RelationCover R u v → terminal u = terminal v)
    {u v : Fin n} (huv : R u v) : terminal u = terminal v :=
  terminal_eq_of_relationCover_reachable hforward terminal hterminal
    (Relation.ReflTransGen.single huv)

/-- A path starting at a sink has no nontrivial endpoint. -/
theorem reachable_eq_of_sink {V : Type*} {R : V → V → Prop} {u v : V} (hsink : ∀ w, ¬ R u w)
    (huv : Relation.ReflTransGen R u v) : v = u := by
  induction huv with
  | refl => rfl
  | tail _ hstep ih =>
    rw [ih] at hstep
    exact (hsink _ hstep).elim

/-- If every vertex has a reachable sink, unique cover successors make that eventual sink
constant along all selected paths.  This is the abstract form used for an HRV map. -/
theorem terminal_eq_of_reachable_of_reachable_sink
    (hforward : ∀ ⦃u v⦄, R u v → u < v)
    (hunique : Relator.RightUnique (RelationCover R)) (terminal : Fin n → Fin n)
    (hterminal_reachable : ∀ u, Relation.ReflTransGen R u (terminal u))
    (hterminal_sink : ∀ u w, ¬ R (terminal u) w)
    {u v : Fin n} (huv : Relation.ReflTransGen R u v) : terminal u = terminal v := by
  have hut : Relation.ReflTransGen R u (terminal u) := hterminal_reachable u
  have hvt : Relation.ReflTransGen R v (terminal v) := hterminal_reachable v
  rcases relationCover_reachable_total hforward hunique hut (huv.trans hvt) with h | h
  · exact (reachable_eq_of_sink (hterminal_sink u)
      (reachable_of_relationCover_path hforward h)).symm
  · exact reachable_eq_of_sink (hterminal_sink v)
      (reachable_of_relationCover_path hforward h)

/-- The eventual-sink form specializes immediately to one selected edge. -/
theorem terminal_eq_of_rel_of_reachable_sink
    (hforward : ∀ ⦃u v⦄, R u v → u < v)
    (hunique : Relator.RightUnique (RelationCover R)) (terminal : Fin n → Fin n)
    (hterminal_reachable : ∀ u, Relation.ReflTransGen R u (terminal u))
    (hterminal_sink : ∀ u w, ¬ R (terminal u) w)
    {u v : Fin n} (huv : R u v) : terminal u = terminal v :=
  terminal_eq_of_reachable_of_reachable_sink hforward hunique terminal
    hterminal_reachable hterminal_sink (Relation.ReflTransGen.single huv)

end VerticalStripLLT.Circular.DiagramProof
