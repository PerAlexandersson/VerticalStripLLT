# Propagating NN and DN recurrences through DD contacts

This is the audited proof route, not yet an exported generalized recurrence.
Direct NN and direct DN hold for both actual models, with all local geometry
and actual HRV transport checked.

We use the shifted variable: corner R1 has coefficient q. At the last DD
contact, write c=b(z), a=b(c). The source D has strict edges

```
a → c,  a+1 → c+1,  c → z.
```

Let h be the middle strict edge. Construct N by unstricting h with unchanged
area, and E by deleting its corner. Apply direct DN in N to the other two
strict edges to obtain R. For either actual model F, R1 and direct DN give

```
F(N) − F(E) = q F(D),     F(N) = F(R).
```

In E, the next child seed is c, now with positive east gap. In R it is c+1,
whose boundary is the old b(c)=a and whose east gap is positive. Both child
contacts have the same terminal type and exactly one fewer DD contact.
Corner saturation is not required in this auxiliary induction.

Apply the child recurrences to obtain F(R)=γ F(U), F(E)=γ F(V), with γ=q+1
for NN and γ=1 for DN. A further direct DN move gives F(V)=F(W), and the
final corner triple satisfies F(U)−F(W)=q F(T). Consequently

```
q F(D) = γ q F(T).
```

Cancel nonzero q in the polynomial domain. Some intermediate areas increase:
this is induction on DD count, not the final geometric-area induction.
`Diagram.ReverseBounceN` in `Circular/CountedBounce.lean` records that count
and is equivalent to the existing reverse search. The induction must quantify
over diagrams, since the child searches live in E and R.

## Periodic separation

For both NN and DN, the terminal row x+1 has no incoming strict edge. The
parallel path ends at b(z)+1, which has no outgoing strict edge by the root
DE gap. It is therefore a whole component of the strict partial injection.
The raw main path (contact list followed by z) is longer. Acyclicity makes it
injective, so it cannot meet that shorter whole component. All edited main
and parallel residues are separated. This excludes the ND alias phenomenon
for NN/DN propagation, including winding paths.

`RawBounceContacts.main_parallel_disjoint` proves this separation for both
terminal types. It omits the extra terminal strict edge used by the older
DN-only `IndexedBounceContacts`.
Adjacent rows, such as z=c+2, remain possible and must not be excluded.

## Checked geometry and remaining obligations

`exists_ddLocalData` extracts the three concrete strict edges and all constructor
bounds from an eligible counted DD bounce. `DDLocalData.coloring_resolution`
and `orientation_resolution` prove the displayed equation for the independently
defined polynomials. `delete_dd_child` proves the full deletion-child statement:
eligibility, one fewer DD contact, unchanged terminal type, and strict acyclicity.

`DDLocalData.resolved_area`, `resolved_boundary_rows`, and
`resolved_strictAt_iff` identify the other child R exactly. Its boundary changes
only at c+1 (down by one) and z (up by one), and its strict-row predicate loses
exactly c. The complete resolved-child theorem
`DDLocalData.resolved_dd_child` now proves raised-root eligibility, one fewer DD
contact, both unchanged terminal flags, and strict acyclicity for NN/DN.
`BounceIterates` expresses searches through boundary iterates and proves the
needed residue exclusions. `resolved_selected_swap` conjugates each resolved
strict edge into the original relation, giving `resolved_admissible`.

For the algebraic propagation route, the remaining geometry is to show that
the two child targets satisfy the next direct-DN hypotheses and identify the
final R1 triple with the prescribed successor. The broader strategy is local
DD elimination and restart; a general projected ND/R4 identity is not required.
See [remaining goals](../CIRCULAR_GOALS.md).

After these facts, the checked independent model identities supply all six
algebraic equations. Full circular induction remains a separate final step.

## Auxiliary termination and half-square accounting

`DDResolvedMeasure` proves that the resolved child preserves the raw area sum
and loses exactly one strict edge. Its doubled geometric area is therefore
D+1. The deletion child loses one full cell and one strict edge, so its doubled
area is D−1. `DDRecurrences.expansion_of_children` cancels the actual q factor
once both child semantic equalities are available; `expansion_of_resolved`
uses outer area induction only for the deletion child.

`LocalEliminationTermination` considers concrete DD resolutions and full neutral
bounces. On a strictly acyclic diagram, each preserves strict acyclicity and
strictly decreases `(strict.card, strictRank)` lexicographically: DD decreases
the first coordinate, neutral preserves it and decreases the second. Thus an
infinite such sequence forces a strict cycle in the initial diagram, and both
actual polynomial expressions vanish. This proves termination of those
auxiliary segments. It does not supply existence of a next move, include R1
strictification, or replace the remaining cancellation/area assembly.

## Concrete closing triple

The next geometric task can be stated without any new polynomial assumptions.
For NN put T=shorten the original root f in D. Let U shorten the moved strict
edge a→c+1 in R, and let V shorten e:a→c in E. Apply direct DN to V at c,
with root f, to obtain W. The required equalities of actual diagrams are

```
U = T.unstrict(e),       W = T.deleteCorner(e),
```

with e transported into T. Relative to D, the area entries of T and U drop
one at t; those of V drop one at c and c+1; those of W drop one at c and t.
Their strict heads and corner lengths agree as well. R1 then gives
`F(U)−F(W)=q F(T)`, and direct DN gives `F(V)=F(W)`. The two smaller-count NN
identities give `F(R)=(q+1)F(U)` and `F(E)=(q+1)F(V)`. Substitution into the
checked source resolution cancels q and proves the full NN identity with
final doubled-area decrease two.

For DN, replace T by the canonical `dnSuccessor` determined by the terminal
strict edge and original root. The child successors have the same extra
terminal-row update; contact separation permits commuting it through the
closing triple. Their coefficients are one. A bare `FullNeutralBounce` witness
is insufficient for this identification: use the canonical target's actual
area rows and strict edges. The raised-side NN equality is now locally proved by
`DDLocalData.resolved_shorten_eq_unstrict` in `DDClosingNN.lean`, using
`shortenEligible` for canonical root choices. The equality with the deleted
corner and the corresponding DN closing triple remain open.
