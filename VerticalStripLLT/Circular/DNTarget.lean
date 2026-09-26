import VerticalStripLLT.Circular.RaiseStrict
import VerticalStripLLT.Circular.ShortenStrict

/-! A valid DN successor: extend the first strict edge and shorten the last. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular
namespace Diagram

open scoped Classical

variable {n : ℕ} (D : Diagram n)

theorem raisedIncl_mem_strict (e : Edge D.area) (he : e ∈ D.strict)
    (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
    (hb : D.area.area e.head + 1 < n)
    (hns : ∀ f ∈ D.strict, f.head ≠ D.area.next e.head)
    {f : Edge D.area} (hf : f ∈ D.strict) (hne : f ≠ e) :
    D.raisedIncl e heq hb f ∈ (D.raiseStrict e he heq hb hns).strict := by
  apply (D.raiseStrict_strict_mem e he heq hb hns _).mpr
  exact Or.inr ⟨f, hf, hne, rfl⟩

theorem raisedIncl_gap (e : Edge D.area) (he : e ∈ D.strict)
    (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
    (hb : D.area.area e.head + 1 < n)
    (hns : ∀ f ∈ D.strict, f.head ≠ D.area.next e.head)
    {f : Edge D.area} (hf : f ∈ D.strict) (hne : f ≠ e)
    (hgap : D.area.area (D.area.next f.head) < D.area.area f.head) :
    (D.raiseStrict e he heq hb hns).area.area
        ((D.raiseStrict e he heq hb hns).area.next (D.raisedIncl e heq hb f).head) <
      (D.raiseStrict e he heq hb hns).area.area (D.raisedIncl e heq hb f).head := by
  have hh := hns f hf
  have hp : D.area.next f.head ≠ D.area.next e.head := by
    intro h
    exact hne (D.strict_edge_eq_of_head_eq hf he (D.area.next_injective h))
  change Function.update D.area.area (D.area.next e.head) (D.area.area e.head + 1)
      (D.area.next f.head) <
    Function.update D.area.area (D.area.next e.head) (D.area.area e.head + 1) f.head
  rw [Function.update_of_ne hp, Function.update_of_ne hh]
  exact hgap

/-- Both modified strict corners are valid; no recurrence is part of this definition. -/
noncomputable def dnSuccessor (e f : Edge D.area) (he : e ∈ D.strict)
    (hf : f ∈ D.strict) (hne : f ≠ e)
    (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
    (hb : D.area.area e.head + 1 < n)
    (hns : ∀ g ∈ D.strict, g.head ≠ D.area.next e.head)
    (hlen : 2 ≤ f.length.val)
    (hgap : D.area.area (D.area.next f.head) < D.area.area f.head) : Diagram n :=
  (D.raiseStrict e he heq hb hns).shortenStrict (D.raisedIncl e heq hb f)
    (D.raisedIncl_mem_strict e he heq hb hns hf hne) hlen
    (D.raisedIncl_gap e he heq hb hns hf hne hgap)

/-- The DN move raises one row and lowers the terminal row. -/
theorem dnSuccessor_area (e f : Edge D.area) (he : e ∈ D.strict)
    (hf : f ∈ D.strict) (hne : f ≠ e)
    (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
    (hb : D.area.area e.head + 1 < n)
    (hns : ∀ g ∈ D.strict, g.head ≠ D.area.next e.head)
    (hlen : 2 ≤ f.length.val)
    (hgap : D.area.area (D.area.next f.head) < D.area.area f.head) :
    (D.dnSuccessor e f he hf hne heq hb hns hlen hgap).area.area =
      Function.update (Function.update D.area.area (D.area.next e.head)
        (D.area.area e.head + 1)) f.head (D.area.area f.head - 1) := by
  change Function.update (Function.update D.area.area (D.area.next e.head)
      (D.area.area e.head + 1)) f.head
      (Function.update D.area.area (D.area.next e.head) (D.area.area e.head + 1) f.head - 1)
        = _
  rw [Function.update_of_ne (hns f hf)]

end Diagram
end VerticalStripLLT.Circular
