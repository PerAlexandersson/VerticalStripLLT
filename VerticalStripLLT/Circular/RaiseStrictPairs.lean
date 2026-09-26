import VerticalStripLLT.Circular.RaiseStrict
import VerticalStripLLT.Circular.PairColoringBridge
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith

/-! Endpoint and strict-pair bookkeeping for the raised DN successor. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular
namespace Diagram

variable {n : ℕ} (D : Diagram n)

theorem raisedEdge_head (e : Edge D.area) (he : e ∈ D.strict)
    (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
    (hb : D.area.area e.head + 1 < n) :
    (D.raisedEdge e he heq hb).head = D.area.next e.head := rfl

theorem raisedEdge_length (e : Edge D.area) (he : e ∈ D.strict)
    (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
    (hb : D.area.area e.head + 1 < n) :
    (D.raisedEdge e he heq hb).length.val = e.length.val + 1 := rfl

theorem raisedEdge_tail (e : Edge D.area) (he : e ∈ D.strict)
    (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
    (hb : D.area.area e.head + 1 < n) :
    (D.raisedEdge e he heq hb).tail = e.tail := by
  let f := D.raisedEdge e he heq hb
  have hm : e.tail.val + (e.length.val + 1) ≡
      f.tail.val + (e.length.val + 1) [MOD n] := by
    change (e.tail.val + (e.length.val + 1)) % n =
      (f.tail.val + (e.length.val + 1)) % n
    calc
      _ = (e.head.val + 1) % n := by
        rw [← Nat.add_assoc, Nat.add_mod, e.tail_add_length_mod]
        simpa only [Nat.mod_eq_of_lt e.head.isLt] using
          (Nat.add_mod e.head.val 1 n).symm
      _ = f.head.val := rfl
      _ = (f.tail.val + f.length.val) % n := f.tail_add_length_mod.symm
  have hc := Nat.ModEq.add_right_cancel' (e.length.val + 1) hm
  exact Fin.ext (hc.eq_of_lt_of_lt e.tail.isLt f.tail.isLt).symm

theorem raisedIncl_endpoints (e : Edge D.area)
    (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
    (hb : D.area.area e.head + 1 < n) (f : Edge D.area) :
    (D.raisedIncl e heq hb f).tail = f.tail ∧
      (D.raisedIncl e heq hb f).head = f.head := by
  exact ⟨rfl, rfl⟩

theorem raiseStrict_pairGraph_strictEdges (e : Edge D.area) (he : e ∈ D.strict)
    (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
    (hb : D.area.area e.head + 1 < n)
    (hns : ∀ f ∈ D.strict, f.head ≠ D.area.next e.head) :
    (D.raiseStrict e he heq hb hns).pairGraph.strictEdges =
      insert (e.tail, D.area.next e.head)
        (D.pairGraph.strictEdges.erase (e.tail, e.head)) := by
  classical
  let Q := D.raiseStrict e he heq hb hns
  ext x
  rw [Finset.mem_insert, Finset.mem_erase, Q.mem_pairGraph_strict_iff]
  constructor
  · rintro ⟨g, hg, hp⟩
    rcases (D.raiseStrict_strict_mem e he heq hb hns g).mp hg with rfl | ⟨f, hf, hfe, rfl⟩
    · left
      rw [← hp, D.raisedEdge_tail, D.raisedEdge_head]
    · right
      refine ⟨?_, (D.mem_pairGraph_strict_iff _).mpr ⟨f, hf, ?_⟩⟩
      · intro hbad
        exact hfe (D.endpointEmbedding.injective (hp.trans hbad))
      · exact hp
  · rintro (hx | ⟨hne, hx⟩)
    · refine ⟨D.raisedEdge e he heq hb,
        (D.raiseStrict_strict_mem e he heq hb hns _).mpr (Or.inl rfl), ?_⟩
      simpa [D.raisedEdge_tail, D.raisedEdge_head] using hx.symm
    · obtain ⟨f, hf, hpair⟩ := (D.mem_pairGraph_strict_iff _).mp hx
      have hfe : f ≠ e := by
        intro h
        subst f
        exact hne hpair.symm
      refine ⟨D.raisedIncl e heq hb f,
        (D.raiseStrict_strict_mem e he heq hb hns _).mpr
          (Or.inr ⟨f, hf, hfe, rfl⟩), ?_⟩
      exact hpair

end Diagram
end VerticalStripLLT.Circular
