import VerticalStripLLT.Circular.NeutralExchange
import Mathlib.Logic.Relation

/-! Acyclicity is invariant under a neutral endpoint exchange. -/

namespace VerticalStripLLT.Circular

variable {V : Type*}

theorem neutralExchange_acyclic_iff {k : ℕ} (R : V → V → Prop)
    (hleft : Relator.LeftUnique R) (hright : Relator.RightUnique R)
    (a z : V) (p q : Fin (k + 1) → V) (hp : Function.Injective p)
    (hq : Function.Injective q) (hpq : ∀ i j, p i ≠ q j)
    (haP : ∀ i, a ≠ p i) (haQ : ∀ i, a ≠ q i)
    (hzP : ∀ i, z ≠ p i) (hzQ : ∀ i, z ≠ q i)
    (hpstart : R a (p 0)) (hpend : R (p (Fin.last k)) z)
    (hpchain : ∀ i : Fin k, R (p i.castSucc) (p i.succ))
    (hqchain : ∀ i : Fin k, R (q i.castSucc) (q i.succ))
    (hqzero : ∀ u, ¬ R u (q 0))
    (hqlast : ∀ u, ¬ R (q (Fin.last k)) u) :
    (∀ v, ¬ Relation.TransGen R v v) ↔
      ∀ v, ¬ Relation.TransGen (neutralExchangeRelation R a z p q) v v := by
  classical
  let σ := pairedSwap p q hp hq hpq
  have hc (u v : V) : R u v ↔ neutralExchangeRelation R a z p q (σ u) (σ v) :=
    neutralExchange_conjugates R hleft hright a z p q hp hq hpq
      haP haQ hzP hzQ hpstart hpend hpchain hqchain hqzero hqlast u v
  constructor
  · intro hac v hcycle
    apply hac (σ.symm v)
    exact Relation.TransGen.lift σ.symm
      (fun u v h => (hc (σ.symm u) (σ.symm v)).mpr (by simpa using h)) _ _ hcycle
  · intro hac v hcycle
    apply hac (σ v)
    exact Relation.TransGen.lift σ (fun u v h => (hc u v).mp h) _ _ hcycle

end VerticalStripLLT.Circular
