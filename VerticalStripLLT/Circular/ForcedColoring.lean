import VerticalStripLLT.Circular.PairColoring
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! A normal pair forced to be an ascent by a strict path. -/

namespace VerticalStripLLT.Circular
namespace PairGraph

open scoped BigOperators

def eraseNormal {n : ℕ} (G : PairGraph n) (e : Fin n × Fin n) : PairGraph n :=
  { G with normalEdges := G.normalEdges.erase e }

theorem strict_path_lt {n m : ℕ} (G : PairGraph n) (c : Fin n → Fin m)
    (hc : G.admissible c) {u v : Fin n}
    (h : Relation.TransGen (fun x y => (x, y) ∈ G.strictEdges) u v) :
    c u < c v := by
  induction h with
  | single h => exact hc _ h
  | tail _ hs ih => exact ih.trans (hc _ hs)

theorem ascentCount_eraseNormal_add_one {n m : ℕ} (G : PairGraph n)
    (e : Fin n × Fin n) (he : e ∈ G.normalEdges)
    {c : Fin n → Fin m} (hc : G.admissible c)
    (hpath : Relation.TransGen (fun x y => (x, y) ∈ G.strictEdges) e.1 e.2) :
    G.ascentCount c = (G.eraseNormal e).ascentCount c + 1 := by
  classical
  have hlt : c e.1 < c e.2 := G.strict_path_lt c hc hpath
  have hem : e ∈ G.normalEdges.filter (fun a => c a.1 < c a.2) :=
    Finset.mem_filter.mpr ⟨he, hlt⟩
  have hpos := Finset.card_pos.mpr ⟨e, hem⟩
  unfold ascentCount eraseNormal
  rw [Finset.filter_erase, Finset.card_erase_of_mem hem]
  lia

theorem coloringWeight_eraseNormal_forced {n m : ℕ} (G : PairGraph n)
    (e : Fin n × Fin n) (he : e ∈ G.normalEdges)
    {c : Fin n → Fin m} (hc : G.admissible c)
    (hpath : Relation.TransGen (fun x y => (x, y) ∈ G.strictEdges) e.1 e.2) :
    G.coloringWeight c =
      MvPolynomial.C Polynomial.X * (G.eraseNormal e).coloringWeight c := by
  have hca : (G.eraseNormal e).admissible c := by
    exact hc
  have hcount := G.ascentCount_eraseNormal_add_one e he hc hpath
  unfold coloringWeight
  rw [ite_eq_left hc, ite_eq_left hca, hcount, pow_succ, MvPolynomial.C_mul]
  ring

theorem coloringLLT_eraseNormal_forced {n m : ℕ} (G : PairGraph n)
    (e : Fin n × Fin n) (he : e ∈ G.normalEdges)
    (hpath : Relation.TransGen (fun x y => (x, y) ∈ G.strictEdges) e.1 e.2) :
    G.coloringLLT m =
      MvPolynomial.C Polynomial.X * (G.eraseNormal e).coloringLLT m := by
  classical
  unfold coloringLLT
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hca : G.admissible c
  · exact G.coloringWeight_eraseNormal_forced e he hca hpath
  · have hca' : ¬ (G.eraseNormal e).admissible c := by
      intro h
      exact hca h
    simp [coloringWeight, hca, hca']

/-- An edge directed against a strict path never contributes an ascent. -/
theorem coloringLLT_eraseNormal_descent {n m : ℕ} (G : PairGraph n)
    (e : Fin n × Fin n)
    (hpath : Relation.TransGen (fun x y => (x, y) ∈ G.strictEdges) e.2 e.1) :
    G.coloringLLT m = (G.eraseNormal e).coloringLLT m := by
  classical
  unfold coloringLLT
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : G.admissible c
  · have hc' : (G.eraseNormal e).admissible c := hc
    have hlt := G.strict_path_lt c hc hpath
    have he : e ∉ G.normalEdges.filter (fun a => c a.1 < c a.2) := by
      intro h
      exact (not_lt_of_gt hlt) (Finset.mem_filter.mp h).2
    have hcount : G.ascentCount c = (G.eraseNormal e).ascentCount c := by
      simp only [ascentCount, eraseNormal, Finset.filter_erase, Finset.erase_eq_of_notMem he]
    simp only [coloringWeight, ite_eq_left hc, ite_eq_left hc', hcount]
  · have hc' : ¬ (G.eraseNormal e).admissible c := hc
    simp only [coloringWeight, ite_eq_right hc, ite_eq_right hc']

end PairGraph
end VerticalStripLLT.Circular
