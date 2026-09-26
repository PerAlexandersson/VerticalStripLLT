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
exactly c. These formulas do not yet prove its complete child-search statement.

The remaining explicit geometry is:

1. Transport the shorter search to R, first retaining seed c and then using
   equality of the new boundaries at c and c+1. The NN/DN hypothesis that x+1
   is not strict is essential here; an overlapping ND terminal can meet z.
   Main/parallel contact separation excludes the changed rows at every query.
2. Prove eligibility at c+1, the same terminal type, and acyclicity of R.
   For acyclicity, after unstricting h, c+1 is isolated; swapping c and c+1
   conjugates that strict relation to the strict relation of R.
3. Show the two child targets satisfy the next direct-DN constructor hypotheses.
4. Identify the final R1 triple with the prescribed full NN or DN successor.

After these facts, the checked independent model identities supply all six
algebraic equations. Full circular induction remains a separate final step.
