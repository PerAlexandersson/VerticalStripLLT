import VerticalStripLLT.Circular.ChainColorings

/-! Generic algebra for a finite rooted forest whose root fibers are chains. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

/-- A finite rooted-chain decomposition, expressed in the form used by the coloring sum.

The construction of this certificate is graph-theoretic: in the intended application,
right and left uniqueness, acyclicity, and reachability to sinks supply its two fields. -/
structure RootedChainColoringCertificate
    (V : Type*) [Fintype V] [DecidableEq V] (R : V → V → Prop) (root : V → V) where
  vertexEquiv :
    (Σ r : V, Fin (Fintype.card {u : V // root u = r})) ≃ V
  strictMono_iff : ∀ {m : ℕ} (c : V → Fin m),
    (∀ u v, R u v → c u < c v) ↔
      ∀ r, StrictMono (fun j => c (vertexEquiv ⟨r, j⟩))

/-- A strict-coloring enumerator factors over the root fibers of a rooted-chain certificate. -/
theorem rooted_chain_coloring_sum_eq_prod_esymm
    {V : Type*} [Fintype V] [DecidableEq V] (R : V → V → Prop) (root : V → V)
    (C : RootedChainColoringCertificate V R root) (m : ℕ) :
    (∑ c : V → Fin m,
      if ∀ u v, R u v → c u < c v then
        ∏ u, MvPolynomial.X (c u)
      else 0) =
      ∏ r : V, MvPolynomial.esymm (Fin m) Q (Fintype.card {u : V // root u = r}) := by
  classical
  let coloringEquiv : (V → Fin m) ≃
      ((Σ r : V, Fin (Fintype.card {u : V // root u = r})) → Fin m) := {
    toFun c x := c (C.vertexEquiv x)
    invFun d u := d (C.vertexEquiv.symm u)
    left_inv c := by
      funext u
      simp
    right_inv d := by
      funext x
      simp
  }
  calc
    (∑ c : V → Fin m,
      if ∀ u v, R u v → c u < c v then
        ∏ u, MvPolynomial.X (c u)
      else 0) =
        ∑ d : ((Σ r : V, Fin (Fintype.card {u : V // root u = r})) → Fin m),
          if ∀ r, StrictMono (fun j => d ⟨r, j⟩) then
            ∏ x, MvPolynomial.X (d x)
          else 0 := by
            refine Fintype.sum_equiv coloringEquiv
              (fun c =>
                if ∀ u v, R u v → c u < c v then
                  ∏ u, MvPolynomial.X (c u)
                else 0)
              (fun d =>
                if ∀ r, StrictMono (fun j => d ⟨r, j⟩) then
                  ∏ x, MvPolynomial.X (d x)
                else 0) ?_
            intro c
            have hprod :
                (∏ x : Σ r : V, Fin (Fintype.card {u : V // root u = r}),
                  (MvPolynomial.X (c (C.vertexEquiv x)) : XPoly m)) =
                    ∏ u, MvPolynomial.X (c u) :=
              C.vertexEquiv.prod_comp (fun u => MvPolynomial.X (c u))
            dsimp [coloringEquiv]
            exact ite_congr (propext (C.strictMono_iff c)) (fun _ => hprod.symm) (fun _ => rfl)
    _ = ∏ r : V, MvPolynomial.esymm (Fin m) Q (Fintype.card {u : V // root u = r}) :=
      sum_strictMono_sigma_colorings_eq_prod_esymm
        (fun r => Fintype.card {u : V // root u = r}) m

end VerticalStripLLT.Circular
