import VerticalStripLLT.CyclicHessenberg.MatchingExpansion

set_option autoImplicit false

/-! The identity Hessenberg tuple has the expected single elementary term. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators
open Equiv.Perm

def identityHessenbergTuple (k n : ℕ) : Tuple k n := fun _ => Hessenberg.identity k

private theorem perm_eq_one_of_forall_le {k : ℕ} (p : Equiv.Perm (Fin k))
    (hp : ∀ x, x ≤ p x) : p = 1 := by
  classical
  have hsum : (∑ x : Fin k, (p x).val) = ∑ x : Fin k, x.val :=
    Equiv.sum_comp p (fun x : Fin k => x.val)
  have hle : ∀ x ∈ (Finset.univ : Finset (Fin k)), x.val ≤ (p x).val :=
    fun x _ => Fin.le_iff_val_le_val.mp (hp x)
  apply Equiv.ext
  intro x
  apply Fin.ext
  by_contra hne
  have hvalne : x.val ≠ (p x).val := by
    intro hval
    apply hne
    exact hval.symm
  have hlt : x.val < (p x).val :=
    lt_of_le_of_ne (Fin.le_iff_val_le_val.mp (hp x)) hvalne
  have hstrict : (∑ y : Fin k, y.val) < ∑ y : Fin k, (p y).val :=
    Finset.sum_lt_sum hle ⟨x, Finset.mem_univ _, hlt⟩
  rw [hsum] at hstrict
  exact (lt_irrefl _) hstrict

private theorem matchingTuple_identity_val {k n : ℕ}
    (φ : MatchingTuple (identityHessenbergTuple k n)) :
    φ.val = fun _ => (1 : Equiv.Perm (Fin k)) := by
  funext ℓ
  apply perm_eq_one_of_forall_le
  intro x
  simpa [identityHessenbergTuple] using φ.property ℓ x

private def identityMatchingTuple (k n : ℕ) :
    MatchingTuple (identityHessenbergTuple k n) :=
  ⟨fun _ => 1, by
    intro ℓ x
    simpa [identityHessenbergTuple] using (le_rfl : x ≤ x)⟩

private theorem matchingTransport_identity {k n : ℕ} (i : Fin (n + 1)) :
    matchingTransport (fun _ : Fin n => (1 : Equiv.Perm (Fin k))) i = 1 := by
  induction i using Fin.inductionOn with
  | zero => simp
  | succ i ih =>
    rw [matchingTransport_succ]
    simp [ih]

private theorem cycleRoots_one {V : Type*} [LinearOrder V] [Fintype V]
    : cycleRoots (1 : Equiv.Perm V) = Finset.univ := by
  classical
  ext x
  simp [cycleRoots]

private theorem permutationBlocks_one {V : Type*} [LinearOrder V] [Fintype V]
    :
    permutationBlocks (1 : Equiv.Perm V) =
      ((Finset.univ : Finset V).sort (· ≥ ·)).map fun x => (x, []) := by
  rw [permutationBlocks, cycleRoots_one]
  simp [orbitBlock, correctedOrbitList]

private theorem list_sum_single_one {α : Type*} (l : List α) :
    (l.map fun _ => (Finsupp.single (1 : ℕ+) 1 : ℕ+ →₀ ℕ)).sum =
      Finsupp.single 1 l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    rw [← Finsupp.single_add]
    congr 1
    simp [Nat.add_comm]

theorem permutationDisplay_one_count (k : ℕ) :
    (permutationDisplay (1 : Equiv.Perm (Fin k))).count = k := by
  simp [CycleDisplay.count, permutationDisplay, permutationBlocks_one]

theorem permutationDisplay_one_shape (k : ℕ) :
    (permutationDisplay (1 : Equiv.Perm (Fin k))).shape = Finsupp.single 1 k := by
  simp [CycleDisplay.shape, CycleDisplay.blockSize, permutationDisplay,
    permutationBlocks_one, List.map_map, Function.comp_def, list_sum_single_one]

private theorem layerAscentCount_identity_self {k : ℕ} (π : FullOrder k) :
    layerAscentCount (Hessenberg.identity k) π π = 0 := by
  classical
  have hevents : layerAscentEvents (Hessenberg.identity k) π π = ∅ := by
    ext e
    simp only [layerAscentEvents, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false]
    intro he
    have hlt := he.2.1
    have hback : (orderEquiv π e.2).val ≤ (orderEquiv π e.1).val := by
      simpa [Hessenberg.identity] using he.2.2
    exact (not_lt_of_ge hback) hlt
  simp [layerAscentCount, hevents]

/-- For every number of layers, the identity tuple contributes only `e₁^k`. -/
theorem naturalCyclicExpansion_identity (k n : ℕ) :
    naturalCyclicExpansion (identityHessenbergTuple k n) = natElementary 1 ^ k := by
  classical
  let h := identityHessenbergTuple k n
  letI : Unique (MatchingTuple h) := {
    default := identityMatchingTuple k n
    uniq := fun φ => by
      apply Subtype.ext
      exact matchingTuple_identity_val φ
  }
  let φ : MatchingTuple h := default
  have hφ : φ.val = fun _ => (1 : Equiv.Perm (Fin k)) :=
    matchingTuple_identity_val φ
  have hmono : matchingMonodromy φ.val = 1 := by
    rw [matchingMonodromy, hφ]
    exact matchingTransport_identity (Fin.last n)
  let D := matchingDisplay h φ
  have hdisplay : D = permutationDisplay (1 : Equiv.Perm (Fin k)) := by
    simp [D, matchingDisplay, hmono]
  have hcount : matchingCycleCount h φ = k := by
    change D.count = k
    rw [hdisplay, permutationDisplay_one_count]
  have hshape : matchingShape h φ = Finsupp.single 1 k := by
    change D.shape = Finsupp.single 1 k
    rw [hdisplay, permutationDisplay_one_shape]
  let P := matchingCanonicalPath h φ
  have hpath : ∀ i : Fin (n + 1), P.val i = D.source := by
    intro i
    change (fullOrdersPerm k).symm
      ((fullOrdersPerm k D.source).trans (matchingTransport φ.val i)) = D.source
    have htrans : matchingTransport φ.val i = 1 := by
      rw [hφ]
      exact matchingTransport_identity i
    rw [htrans]
    change (fullOrdersPerm k).symm (fullOrdersPerm k D.source) = D.source
    exact (fullOrdersPerm k).symm_apply_apply D.source
  have hasc : matchingAscentCount h φ = 0 := by
    rw [matchingAscentCount_eq_sum]
    apply Finset.sum_eq_zero
    intro ℓ hℓ
    rw [hpath ℓ.castSucc, hpath ℓ.succ]
    exact layerAscentCount_identity_self D.source
  simp only [naturalCyclicExpansion, Finset.univ_unique, Finset.sum_singleton]
  change MvPolynomial.C (Polynomial.X ^ (k - matchingCycleCount h φ) *
    (1 + Polynomial.X) ^ matchingAscentCount h φ) *
      MvPolynomial.monomial (matchingShape h φ) 1 = natElementary 1 ^ k
  rw [hcount, hshape, hasc]
  simp [natElementary, MvPolynomial.X_pow_eq_monomial]

end VerticalStripLLT.CyclicHessenberg
