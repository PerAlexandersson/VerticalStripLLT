# Interior overlap by column reversal

Status: the uniform valid target and its strict doubled-area decrease are now
verified in Lean. The strict-head correspondence, periodic integer reversal
and exact strict/exterior lifted transport are also verified. Integer sink
order and actual residual coloring/HRV equality are checked. Restoring internal
forced-edge factors, cancellation and the outer induction remain unfinished. The transport argument was independently
audited by the primary and Astra reviewer. This is the intended discharge of
`InteriorNDInductionStep`, not
a replacement theorem with additional geometric hypotheses.

## Extracting the component

Put r=k+2 and P_a=b^[a](t). If the terminal upper contact P_r+1 aliases P_i,
put j=r-i. The interior contact argument gives i≤k, hence j≥2. The two contact
tracks merge into one strict chain

    w_0 -> w_1 -> ... -> w_(r+j-1).

Its main segment satisfies w_a=res(P_(r-a)) for 0≤a≤r. Its upper segment
satisfies w_(a+j)=res(P_(r-a)+1) for 0≤a<r. In particular,

    next(w_a)=w_(a+j) for 0≤a<r.

The overlap identifies the two descriptions at a=j; strict-successor
uniqueness propagates that identification. Strict acyclicity makes all listed
vertices distinct. The first vertex x is nonstrict. The last vertex is
res(b(t)+1), and `EligibleDE.parallel_end_free` makes it a strict sink.
Strict predecessor/successor uniqueness then shows that this is the entire
strict component and no strict edge joins it to the outside.

`Diagram.exists_interiorMergedComponent_of_overlap` in
`InteriorMergedComponent.lean` now proves this chain certificate from the
actual counted-contact hypotheses. It includes bounded injectivity and the
free endpoints. `InteriorComponentIsolation` now proves exact predecessor and
successor formulas and strict-edge closure of the component, and supplies
`vertexEmbedding` and `size_le`. Local builds and axiom checks pass.

## Columns and their reversal

Write r=qj+s with 0≤s<j. Since r>j in the interior case, q≥1. For 0≤c<j set

    C_c = (w_c, w_(c+j), w_(c+2j), ...),
    l_c = q+1+[c<s].

The next-jump identity makes each column a consecutive circular interval.
Injectivity makes the columns disjoint. A column endpoint has chain index at
least r, so it is not one of the lower contact links. These are exactly the
blocks obtained from links w_a -> next(w_a), a<r. Distinct columns may be
adjacent in the circular order; no outside separator is assumed.

Let pi reverse each column, fixing all other vertices. Its integer lift sigma
reverses each lifted interval and is periodic. Consecutive strict-chain
vertices belong to different columns because j≥2, so their positive lifts
are transported without reversing direction or reaching length n.

The finite permutation is now verified as `InteriorMergedComponent.reversalPerm`,
with the actual column formula, involution and fixation off the component.
`ColumnIndexReversal` supplies the bounded arithmetic permutation;
`InteriorColumnGeometry.vertex_atOffset` verifies that these index columns are
actual circular intervals. `InteriorReversalLift` now constructs the periodic
integer involution, proves its residue correspondence and period translation,
and `InteriorReversalStrict` proves its exact strict-edge transport.

Let H_c be the positive circular distance from the start of C_(c-1) to the
start of C_c, taking the predecessor of column zero to be column j-1.
This is column-index order, not an assumption that columns occur in that
geometric order. Disjointness gives H_c≥l_(c-1)≥2.

The original area values on C_0 are H_0 at its first vertex and H_0+1 at all
remaining vertices. On every C_c with c>0 they are constant H_c. The source
formula also uses b(x+1)=b(x), supplied by the terminal ND contact.

## Explicit target area and strict decoration

Leave all area values outside the component unchanged.

- If s=0, set the whole of C_0 to area H_0-1 and leave other columns unchanged.
- If s>0, set the whole of C_0 to area H_0, decrease every area in C_s by one,
  and leave other columns unchanged.

Transport the strict edges by pi. Equivalently, among the component vertices,
remove the strict head at the last vertex of C_0 and insert the original
source as a strict head; all other heads remain strict. The target's unique
nonstrict component vertex is pi(x), the last vertex of C_0.

For c>0, the transported strict edge length is

    H_c + l_c - l_(c-1).

This drops by one precisely at c=s>0. For c=0 the transported length is

    H_0 + l_0 - l_(j-1) - 1.

It is H_0-1 if s=0 and H_0 otherwise. At the new source the target boundary
is exactly one past the preceding column's end. These formulas identify the
transported strict edges with actual target corners; mere graph relabeling
would not establish that.

The changed boundary values increase as follows:

- s=0: increase by one at the start of C_0 and by two at its other vertices.
- s>0: increase by one at noninitial vertices of C_0 and at every vertex of C_s.

Inside each column, target boundary increments are one. At its endpoint the
new source needs only a nonnegative gap. If s=0 this endpoint is the original
eligible root t, whose boundary gap is at least two. If s>0 the endpoint of
C_s is t and remains strict; its original gap of at least two absorbs the
increase by one. Other strict endpoints retain a gap of at least one.
Increases at a following column's start only help. All target areas stay
positive on these columns and do not increase anywhere, so the upper bound
by n is preserved.

The raw-area decrease is 2q+1 when s=0 and 2q+2 when s>0. The number of strict
edges is unchanged. Thus doubled area strictly decreases. The root-alias
case i=0 formally gives j=r, q=1, s=0 and the familiar decrease of three raw
cells, providing a consistency check; no refactor of that completed proof is
needed.

## Finite decrement implementation of the target

For index a<r+j and s=r mod j, use the following decrement d(a):

```
if a % j = 0:
  if s = 0: 1 if a = 0, otherwise 2
  else:     0 if a = 0, otherwise 1
else:
  1 if a % j = s, otherwise 0
```

Set d=0 off the component and Qarea(v)=Darea(v)-d(v). The new source index is
e0=j*((r+j-1)/j). It equals r if s=0 and r+(j-s) otherwise. Among indices
r≤a<r+j, remainder zero identifies exactly e0, while remainder s identifies
exactly r. This pins down every affected column endpoint.

Cyclic validity follows directly from the old cyclic inequality when the
next decrement is at least the current decrement. When a decrement of one
falls, the old strict-corner inequality suffices. A decrement of two can fall
only at the original eligible root (s=0), whose stronger inequality suffices.
The old source is harmless: its next decrement increases. For retained strict
corners, the only additional endpoint is the root when s>0, again eligible;
the other problematic endpoint is the new source whose strict mark is removed.
The inserted strict corner at w_0 follows from `source_area_jump`.

Positivity follows from the checked area-profile lemmas. In particular rows
decremented by two have old area at least three, from `source_area_ge_two`
and `area_zero_column_succ`; the generic lower bound of two would not suffice.
The target's raw-area sum decreases strictly because every row weakly decreases
and the eligible root strictly decreases. Together with unchanged strict-head
cardinality, this proves doubled-area descent without evaluating the exact sum.

This finite proof route is now verified in `InteriorReversalArea` and
`InteriorReversalTarget`. The latter defines the actual `reversalTarget` and
proves `reversalTarget_strict_card` and `reversalTarget_doubledArea_lt`.
`DiagramFromHeads` constructs genuine full-height corner edges and verifies
head membership and cardinality. The independent source review, full build and
axiom inventory passed. This establishes the target, not yet its semantic
relation to the source. The strict part of that relation is now checked by
`reversalHeads_eq_image`, `reversalArea_reversed_length`,
`boundary_reversalLift_of_strictAt` and `liftStep_empty_reversal_iff`. In
particular the boundary identity is an equality of integers, so no period
ambiguity is hidden in a residue equality.

## Edges to other components

This is essential: conjugating the boundary as sigma b sigma is incorrect.
Outside heads keep their old boundary.

An interior column vertex u, except for the component sink, has a strict
successor v in an interior position of another column, with

    b(v-1)=u-1, b(v)=u, b(v+1)>u

for compatible lifts. Monotonicity then makes v the only lifted head with
boundary u. The exceptional component sink is skipped by the eligible root's
boundary jump. Therefore an outside head cannot have boundary in the interior
of a column. Its incoming interval contains each column wholly or not at all,
and pi preserves that interval.

For component heads, both the original and target incoming thresholds lie
within the preceding column, or immediately after its end. Reversing the
current column and moving that threshold changes only edges internal to the
component. Hence every normal edge between this component and its complement
is transported exactly. All other edges outside the component are unchanged.

This geometry is now verified in `InteriorBoundaryAvoidance`,
`InteriorLiftIntervals`, `InteriorReversalSource`, `InteriorExteriorBoundary`
and `InteriorExteriorPairs`. The main integer statement
`boundaryNaturalLift_reversal_iff` identifies the actual edge intervals, so
positive lengths and winding are included. `normalPairs_reversal_iff` then
identifies the finite normal pairs by removing the transported strict pairs.

## Actual polynomial transport

Erase all normal edges internal to the merged strict chain. Forward ones
contribute a factor (1+q) each after the shift; backward ones contribute no
coloring ascents and kill any orientation selecting them. Both directions
are already covered by the generic forced/descent erasure APIs.

The residual coloring sums agree by vertex relabeling. Residual selected
lifted graphs are conjugate by sigma. Every selected sink is a strict sink.
There is only one strict sink in the moved component, and sigma fixes all
vertices outside that component. Its movement stays in its column, so the order of
all integer sink lifts is preserved, including across periods. Thus
`Orientation.hrv_conjugate` and `hrvMonomial_conjugate` give actual HRV transport.
The generic restricted-sum assembly is now proved and locally verified in
`OrientationSumConjugacy`: `pairset_admissible_conjugate`,
`orientMono_conjugate`, and `orientSum_conjugate`.

The sink-order argument is now proved in `InteriorReversalSinkOrder` for
arbitrary selected edge sets. `InteriorResidualTransport` proves the actual
`orientSum_exterior_reversal` and `coloringLLT_exterior_reversal`, using the
exact exterior pair sets from `InteriorResidualPairs`. Internal forced-factor
restoration is the next unproved step.

No inequality between the two forced-edge counts is needed. If F_D,F_Q are
those counts, write the two shifted coloring polynomials as A^F_D C and
A^F_Q C, and the evaluated HRV expressions as A^F_D E and A^F_Q E, where
A is the coefficient embedding of 1+q. The lower-area induction hypothesis
for Q gives A^F_Q C=A^F_Q E. This nonzero factor can be cancelled in the
polynomial domain, proving C=E and hence the desired equality for D.

## Verification boundary

The implementation is split after the merged-component certificate into four
modules: `InteriorColumnReversal` for column indexing and the finite
permutation; `InteriorReversalTarget` for the actual area sequence, decoration
and area decrease; `InteriorReversalTransport` for exterior edges, one periodic
integer lift and sink order; and `InteriorReversalReduction` for forced-edge
factors, lower-area induction and cancellation. The intermediate data should
contain the chain and its source/root/contact properties, not a target diagram
or the desired polynomial identity. This boundary was independently reviewed.

The formulas and local geometric checks above have been audited by hand.
The merged-chain extraction, component isolation, finite column permutation,
original area profiles, actual valid smaller target, periodic integer lift,
strict/exterior lifted transport, sink order and actual residual coloring/HRV
transport are verified. The remaining Lean work restores the internal
forced-edge factors, cancels the target factor and invokes the existing outer IH.
The older Aristotle request ended with the full target unproved and is excluded.
It predates this construction. No remote result or this note substitutes for
the serialized local build and axiom checks.
