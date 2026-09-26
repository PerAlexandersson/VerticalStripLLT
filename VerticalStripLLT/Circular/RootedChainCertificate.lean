import VerticalStripLLT.Circular.RootedChainColorings

/-! Construct rooted-chain coloring certificates from finite reachability orders. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators

/-- A finite acyclic relation whose root fibers are reachability chains has a coloring certificate.

The hypotheses keep the graph input separate from the algebraic factorization: edges preserve the
chosen root, and any two vertices with a common root are reachability-comparable. -/
noncomputable def rootedChainColoringCertificate
    {V : Type*} [Fintype V] [DecidableEq V] (R : V → V → Prop) (root : V → V)
    (acyclic : ∀ v, ¬ Relation.TransGen R v v)
    (root_edge : ∀ u v, R u v → root u = root v)
    (comparable : ∀ u v, root u = root v →
      Relation.ReflTransGen R u v ∨ Relation.ReflTransGen R v u) :
    RootedChainColoringCertificate V R root := by
  classical
  let fiberOrder : ∀ r : V, LinearOrder {u : V // root u = r} := fun r => by
    let : IsStrictTotalOrder {u : V // root u = r}
        (fun u v => Relation.TransGen R u.val v.val) := {
      irrefl := by
        intro u hu
        exact acyclic u.val hu
      trans := by
        intro u v w huv hvw
        exact huv.trans hvw
      trichotomous := by
        intro u v huv_not hvu_not
        have hroot : root u.val = root v.val := by
          calc
            root u.val = r := u.property
            _ = root v.val := v.property.symm
        rcases comparable u.val v.val hroot with huv | hvu
        · rcases Relation.reflTransGen_iff_eq_or_transGen.mp huv with h | h
          · exact Subtype.ext h.symm
          · exact (huv_not h).elim
        · rcases Relation.reflTransGen_iff_eq_or_transGen.mp hvu with h | h
          · exact Subtype.ext h
          · exact (hvu_not h).elim
    }
    exact linearOrderOfSTO (fun u v => Relation.TransGen R u.val v.val)
  let enumeration : ∀ r : V,
      Fin (Fintype.card {u : V // root u = r}) ≃ {u : V // root u = r} := fun r => by
    let := fiberOrder r
    exact (Fintype.orderIsoFinOfCardEq {u : V // root u = r} rfl).toEquiv
  let vertexEquiv :
      (Σ r : V, Fin (Fintype.card {u : V // root u = r})) ≃ V :=
    (Equiv.sigmaCongrRight enumeration).trans (Equiv.sigmaFiberEquiv root)
  refine
    { vertexEquiv := vertexEquiv
      strictMono_iff := ?_ }
  intro m c
  constructor
  · intro hc r
    let := fiberOrder r
    change StrictMono (fun j => c ((enumeration r j).val))
    intro i j hij
    let E : Fin (Fintype.card {u : V // root u = r}) ≃o {u : V // root u = r} :=
      Fintype.orderIsoFinOfCardEq {u : V // root u = r} rfl
    have hreach : Relation.TransGen R (E i).val (E j).val := by
      have hlt : E i < E j := E.strictMono hij
      exact hlt
    have hcolor : ∀ {a b : V}, Relation.TransGen R a b → c a < c b := by
      intro a b hab
      induction hab with
      | single huv => exact hc _ _ huv
      | tail hxy hyz ih => exact lt_trans ih (hc _ _ hyz)
    simpa [E, enumeration] using hcolor hreach
  · intro hc u v huv
    have hroot : root u = root v := root_edge u v huv
    let r : V := root u
    let := fiberOrder r
    let u' : {x : V // root x = r} := ⟨u, rfl⟩
    let v' : {x : V // root x = r} := ⟨v, by simpa [r] using hroot.symm⟩
    let E : Fin (Fintype.card {x : V // root x = r}) ≃o {x : V // root x = r} :=
      Fintype.orderIsoFinOfCardEq {x : V // root x = r} rfl
    let i : Fin (Fintype.card {x : V // root x = r}) := E.symm u'
    let j : Fin (Fintype.card {x : V // root x = r}) := E.symm v'
    have hreach : u' < v' := by
      change Relation.TransGen R u v
      exact Relation.TransGen.single huv
    have hij : i < j := by
      exact E.symm.strictMono hreach
    have hcolor := hc r hij
    simpa [vertexEquiv, enumeration, E, i, j, u', v', r] using hcolor

end VerticalStripLLT.Circular
