# Component sums through an ordinary DD reduction

2026-09-28. The DD packet identity below is proved mathematically. It uses
the existing DN reconstruction and exact corner branching, with the same
integer coefficients for strict-coloring sums K and HRV elementary sums E.
It does not establish individual-component isolation. We work with ordinary
diagrams and unweighted sums throughout.

## The corner split

Let D have an eligible DD contact, with strict corners

    ac, h=(a+1)(c+1), cz,       a<c<c+1<z.

We retain the full ordinary DD geometry, including equal area entries at
c,c+1 and the terminal gap at z. Put x=c+1. Let N be D with h unmarked,
and let D-h be obtained by deleting that corner. The direct DN move in N
at ac,cz produces R, with these two strict corners replaced by ax,xz.
The other strict corners of N remain fixed.

The selected status of a natural corner is constant on every complete
component: an exchanged short must lie properly inside its retained natural
long, and no natural edge properly contains a corner. Consequently the
complete components of N split into two disjoint families:

- Those selecting h are exactly the complete components of D.
- Those omitting h are exactly the complete components of D-h.

These are graph identifications, including all exterior flips. In the first
family, making h strict changes neither the selected relation nor a possible
flip: h was never an exchanged short. In the second, deleting the unselected
edge leaves every selected relation and cover test unchanged; it removes no
possible retained long. Both identifications preserve K and E state by state.

## DD reconstruction

Apply the auxiliary completion graph J from the
[DN reconstruction](DN_COMPONENT_COMPLETION.md) to N. Its proof requires
the full local DN hypotheses but does not require every natural corner to
be strict. In particular h may be a common exterior normal edge.

For a connected class P of J, let P_1 be its components selecting h and
P_0 its components omitting h, identified with components of D and D-h as
above. DN reconstruction supplies integers g_T, constant on complete target
components T of R. For both X=K and X=E we obtain

    Σ_(C in P_1) X_D(C)
      = Σ_(T a component of R) g_T X_R(T)
        − Σ_(C in P_0) X_(D-h)(C).                 (1)

Indeed, the DN source sum is exactly the sum of the two corner sectors.
Moving the unselected sector to the right gives (1). Every term is a whole
component; no restriction to an incomplete set of orientations is used.
The target coefficients are the same signed integers in the two identities.

There is no factor q in (1), since these are unweighted component sums.
When ascent weights are restored, the selected h is normal in N and strict
in D, so it contributes one extra normal ascent in N. This is the factor
appearing in the aggregate corner relation.

Thus DD transport itself needs no new local valuation identity. Its
remaining component question is whether P_1 can be separated after the
already-proved component reductions, or whether several such packet equations
together have enough independent rows. The two sectors of N need not have
the same weak partition after h is deleted; the proof does not assume this.

## An ordinary induction measure

For an ordinary diagram on vertices 0,...,n-1, put

    A(D) = Σ_j a_j,          M(D) = Σ_j j a_j.

Here A counts natural edges, including strict ones. Represent each component
by its saturated selected-edge envelope, as in the
[minimum-area construction](FLIP_COMPONENT_INDUCTION.md).
The lexicographic triple

    (n, A(D), M(D))                                  (2)

decreases in every target component of the eligible reductions considered
here:

- Vertex factorization reduces n.
- Direct NN removes one natural edge, so A decreases.
- Corner deletion removes one natural edge, so A decreases.
- Direct DN and the DD resolved target replace the two area entries by

      a_x ↦ a_x+1,       a_z ↦ a_z-1,       x<z.

  They preserve A and decrease M by z-x.

Passing to a target component's saturated envelope preserves this decrease.
If any natural edges are removed, A decreases further. If none are removed,
only corners are made strict, which changes neither A nor M. The three
entries in (2) are nonnegative integers, so this gives a well-founded order.

We do not need the raw targets to be saturated. For example, direct DN sends
area (0,1,1,2,3), with strict corners 01,14, to area (0,1,2,2,2), with strict
corners 02,24. The target also has the unmarked natural corner 13. Counting
strict edges or corners before normalization is therefore unnecessary here.

In particular, the DD resolved target has doubled geometric area one larger
than D, but is smaller in (2). All R and D-h terms in (1) are available to
induction on (2). The intermediate N is only used to derive the equation;
we do not assume its component formula as an induction hypothesis.

This argument uses the linear ordinary order x<z. It does not establish a
decreasing moment for a circular move crossing the chosen cut. Nor does it
prove that every unresolved diagram admits one of the eligible reductions.

## Checks and the remaining isolation question

The later one-component inheritance argument below also treats ND. It
does not use a packet-isolation assertion: it reduces the desired DD
and ND component steps to the general DN and NN reassembly statements,
respectively, allowing unmarked exterior corners.

For each packet P, remove from P_1 the already-solved disconnected components,
trees, and components with no state acyclic after reversing all strict
corners of D. The DD isolation question asks whether at most one component
remains. This is a sufficient condition for (1) to prove the individual
component formula; it is not needed merely to derive (1).

Exact enumeration gives:

| Vertices | Eligible saturated DD instances | Components of N counted | J classes counted |
|---|---:|---:|---:|
| 5 | 1 | 14 | 12 |
| 6 | 7 | 232 | 178 |
| 7 | 36 | 3537 | 2505 |

All transported target multiplicities were component-constant. All these
DD instances passed the stated isolation test. The test uses reversed strict
corners of D, including h, on the selected h sector; reversing only the
strict set of N would test a different condition. Counts include repetitions
when a diagram has more than one eligible recurrence. These finite checks
do not prove isolation in general.

The probe reuses the existing actual cover-flip enumeration and DN completion
graph, with no new polynomial generator. Its script and receipt are
`recurrence-continuation/dd_essential_scan.py` and `dd_essential_scan.jsonl`
under the external project request directory. Runtime was 63 seconds under
a 600-second cap. Luna and Astra independently audited the graph split,
reconstruction and corrected measure; primary checked the proof and exact receipts. No Lean
or LaTeX build was run.

Related Lean: `Circular/DDResolvedRows.lean`,
`DDLocalData.resolved_area`; `Circular/DDResolvedMeasure.lean`,
`DDLocalData.resolved_area_sum` and `resolved_doubledArea`. These provide the
existing geometric identities, not a formalization of the new component
packet argument.

## Direct one-component inheritance for DD and ND

2026-09-29. We can avoid a separate component-isolation problem for each
of these two types once the NN/DN steps are proved with arbitrary corner
decorations. This is a reduction of the remaining proof obligations,
not a claim that general NN/DN reassembly is already complete.

Let g be any strict natural corner of an ordinary diagram D, and let
N be the same natural diagram with g unmarked. A complete component C
of D is exactly a complete component C_N in the selected-g sector of N.
Indeed, g cannot be exchanged as a short, since no natural interval
properly contains it. Unmarking g changes neither selected relations
nor any actual adjacency on that sector. Both K and E are unchanged.

In the order (n,A,M) above, D and N have the SAME measure: unmarking
changes no natural edge or area entry. Suppose a direct recurrence at
N transports this particular component C_N into whole components T_i
in smaller diagrams N_i, with the same coefficients for both valuations:

    X_N(C_N)=sum_i m_i X_(N_i)(T_i),        X=K,E.

Then the identical equation holds for X_D(C). Every N_i is also smaller
than D. We invoke induction only for these final output components;
we do not invoke the unknown component identity in the equal-measure
intermediate N. Source additions are allowed exactly as in the main
outline, provided their final identifications also have smaller measure.

### DD uses DN

For DD, take the same obstructing corner h and unmarked diagram N as
in the first section of this note. The direct DN split applies to the
single C_N. Its main target replaces the natural edge cz by a(c+1),
so A is unchanged and M decreases by z-(c+1). Its common deletion
diagram removes cz and therefore decreases A. The whole-component
collection problem is exactly general DN with h as an exterior normal
corner. Once that problem is solved, the preceding inheritance gives
the DD recurrence for C itself.

This also explains the earlier packet formula: packet isolation was
needed there because only packet-level DN was available. A general
one-component DN theorem already supplies the required individual step.

### ND uses NN

Use the ND geometry from [the local ND note](CIRCULAR_DIRECT_ND.md),
restricted to ordinary diagrams. Write

    f=xt,       y=x+1,       g=ay,
    b(x)=b(y)=a,             x<y<t.

The root f is strict and has the required terminal gap. Row x is
nonstrict and row y is strict, with strict incoming edge g. Unmark g
to obtain N. The two contact rows are now nonstrict and still have
equal boundary values, so N has an eligible NN step at (x,y,t).
This is the same N used by the established local ND geometry; no area
entry changes during unmarking.

Apply the exact [one-component NN split](COMPONENT_NN_REDISTRIBUTION.md)
to C_N, retaining g among its exterior normal edges. It gives the SAME
K/E identity for C in the corner-deletion diagram

    D0=N-f.

The identity is valid for one component immediately, before reassembly.
It retains the entire exterior and the membership indicator of C_N;
in particular, source orientations omitting g have coefficient zero.
The split's bottom interchange is allowed to move the selected g to
another normal edge. We do not require all output pieces to select g.

Every orientation of D0 lies in a diagram with A(D0)=A(D)-1. Hence
once the general NN reassembly collects these pieces into whole smaller
components, the ND component recurrence follows with the same induction
order. Further envelope normalization only decreases A or leaves (A,M)
unchanged. The intermediate N needs no induction hypothesis.

This is an unweighted component argument. If ascent weights are restored,
C_N has one more selected normal edge than C, namely g. Working first
with K=E avoids any division by the shift parameter.

## Remaining general inputs after inheritance

DD and ND require no additional one-component reassembly theorem beyond
DN and NN WITH arbitrary exterior corner decorations. A theorem restricted
to saturated NN/DN sources would not suffice, because N has an unmarked
corner. This distinction is part of the required theorem's hypotheses.
The exact direct NN/DN initial splits already allow these decorations;
their general collection into complete components is still open.

Recurrence coverage also remains separate: the present argument assumes
an eligible DD or ND geometry and does not show that every nonterminal
ordinary diagram admits one of the four eligible local moves.
