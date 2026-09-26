# Flip-component induction: redistribution and component equations

Status: mathematical brainstorming after the verified aggregate circular
checkpoint `18fbb4d`. No full component proof is claimed. No Lean source or
Overleaf manuscript is changed by this audit.

We read `LLT flip/main.tex`, especially the local diamonds (around 1704),
component target (around 1980), cut/transport/reassembly discussion
(2527–2595), relations (1')–(4'), signed transfer discussion (3007–3095),
and commented relation-(8') sketch (3387 onward). We also read
`EDITORIAL-AUDIT.md` and the repository component interface. `new-main.tex`
is a shorter partial rewrite, not a replacement for the detailed sketches.
The prior audit's finite computational claims are provenance, not new checks
or proofs performed in this continuation. Independent Astra and Terra reviews
were read-only and build-free.

## The desired induction

Write K_C for the sum of weak order enumerators of orientations in a complete
flip component C, and H_C for its sum of HRV complete-homogeneous monomials.
The strict/e version uses the existing Lean coefficient interface. We retain
that convention for future formalization; omega is not the central issue here.

We want to show that validity for all components of suitable smaller diagrams
implies validity for every component of the source. This is compatible with
redistributing individual coloring occurrences among orientations and among
components. A correspondence between whole orientation components need not
be the primitive operation.

There are two separate obligations:

1. Prove simultaneous local transport identities for K and H with exactly
   the same coefficients, including the actual exterior relations.
2. Prove that enough transported identities isolate each source component.

The aggregate circular theorem does not supply either obligation merely by
summing its orientations differently.

## The coloring redistribution is explicit

Let P00 contain a<c, with arbitrary fixed exterior relations. Let P10 add
a<b, P01 add b<c, and P11 add both. For weak colorings of P00 set
A := [f(a) ≤ f(b)] and B := [f(b) ≤ f(c)]. Since f(a) ≤ f(c), A or B holds.
Consequently

    1_A + 1_B = 1 + 1_(A and B).

This gives a monomial-preserving bijection between the disjoint unions of
colored occurrences for {P10,P01} and {P00,P11}. Send a P10 coloring to P00.
Send a P01 coloring to P11 if A holds, and otherwise to P00. Inverting this
map uses A to decide the preimage of a P00 coloring; a P11 coloring returns
to P01. Every vertex keeps its color. Exterior constraints remain satisfied
because the coloring itself is unchanged.

The same construction works for strict colorings: f(a)<f(c) ensures
[f(a)<f(b)] or [f(b)<f(c)]. The common-base/four-state description must hold
for the actual diagrams, not just their drawn internal edges.

The separate HRV diamond identity matches the multiset of HRV partitions
on the two sides. It requires the actual lifted reachability hypotheses.
This yields both valuation identities without asserting a pointwise HRV
match for the coloring map. The manuscript's false pointwise step in the
commented (8') sketch should stay excluded.

## Do not impose ascent preservation on the unweighted target

The component conjecture K_C=H_C is unweighted. The ascent number is constant
inside a component, but an induction proving all component identities may
use target components at different ascent numbers. The diamond itself takes
two k-ascent states to a (k−1)- and a (k+1)-ascent state.

This narrows the obstruction in the current notes. For the displayed ordinary
relation-(3) instance X=ndnndeee and Y=nndnedee, the source vector is

    H_C = h_(3,2) + 2 h_(4,1) + 2 h_5.

Its failure to lie in the rational span of the three displayed target vectors
is a failure of the SAME-ASCENT span. It does not rule out target components
at other ascents. In Y, the fully ascending orientation contains the entire
adjacent chain, hence has a total-chain poset. It is the unique maximal-ascent
orientation, so its complete component T is a singleton with K_T=H_T=h_5.

The manuscript records, for its six-state target component D,

    K_D − K_C = h_5,    H_D − H_C = h_5.

If the recorded K identity is established by the actual coloring transport,
this gives the simultaneous target-only identity

    X_C = X_D − X_T,    X in {K,H}.

Thus this particular obstruction is repaired using complete TARGET components
at different ascents. We have checked the algebraic implication and the chain
observation here; the recorded K equality has not been newly formalized.
The second same-ascent packet obstruction in the notes likewise does not
settle what happens when all ascent levels and all permitted branches are used.

For an argument retaining the aggregate q-weight, exponent changes must be
accounted for explicitly. For the component identity itself we can work
unweighted and retain each separate local equality before combining them into
one polynomial recurrence. Specializing an aggregate identity alone would
lose this component information.

## Reconstruction and isolation

For a fixed source component or signed collection of components, transport
occurrences while retaining their source labels and recurrence-branch labels.
In branch j let m_j(theta) be the resulting integer multiplicity of target
orientation theta. The transported branch is an integer combination of
complete target components exactly when

    m_j(theta) = m_j(eta) whenever theta and eta differ by a target flip.

This must include exterior and mixed flips with full cover conditions.
Internal local-state tables alone are insufficient: exterior paths can destroy
covers, and an exterior flip can join states separated by the internal table.

A sufficient reduction lemma is

    r_C X_C = sum_T a_(C,T) X_T + sum_B b_(C,B) X_B,  X in {K,H},

with the same integer coefficients, r_C>0, complete components T in diagrams
smaller for a justified induction measure, and independently solved components
B. Components at every ascent level are allowed. Subtracting K and H gives
r_C(K_C−H_C)=0, hence the result in the torsion-free coefficient module.

More generally several packet equations may be needed. After using known
target/base identities they give A Delta=0, where Delta lists all unknown
source-component defects. Full column rank over the rationals is sufficient.
One equation for Delta_C+Delta_C' gives no individual conclusion. Constructing
A from genuine simultaneous identities and proving its rank uniformly is a
mathematical task; matching H-vectors computationally does not prove K-identities.

## A possible constructive organization

We can encode signed finite orientation sums and use only verified common
relations: coloring/HRV diamonds and genuine global identifications. The
component indicator vector is the object to reduce. A successful reduction
expresses a positive multiple of it in terms of smaller-diagram component
indicators and solved bases, modulo these common relations. This keeps
coloring redistribution explicit and permits signed corrections without
requiring a bijection on orientations.

A related observation may help design a reduction algorithm. For positive
multisets on one fixed diagram, replacing the two middle states of a diamond
by its zero/full states increases the sum of squared ascent numbers by two.
It preserves multiset size, so repeated forward diamond replacements terminate.
This is only a termination observation: a terminal multiset may contain an
orientation whose flip partner is absent. It does NOT establish that terminal
orientations are chains or that the desired component identity follows.
A balance invariant ensuring an adequate terminal form would be an additional
lemma, not a consequence of this statistic.

## Proposed full-statement milestones

1. Prove the global component bijections for a corner deletion/strictification
   (relation (1')), including all periodic translates. A corner cannot be a
   toggled short edge of a flip; fixed corner status should give the full
   correspondence. This reduces the conjecture to saturated diagrams.
2. Prove a general coloring-occurrence diamond and its actual lifted HRV
   companion, with arbitrary exterior relations and precise four-state data.
3. Formulate component transport across a genuine local recurrence using all
   ascent levels. Prove reconstruction across every target flip, or replace
   reconstruction by an explicit common-relation reduction of component vectors.
4. Prove component isolation, either by direct signed formulas or a uniformly
   full-rank finite system. Singleton and disconnected-component bases need
   their own proofs; only the zero-normal base is currently exported in Lean.
5. Attach these results to the already verified circular reduction measures.
   The existing half-square-area and strict-rank arguments certify the actual
   diagram reductions. They do not automatically certify arbitrary new packet
   moves or lift the column-reversal proof to complete flip components.

No new warmup examples or broad implementation should precede a precise
transport/isolation target. The current notes contain the local ingredients;
the uniform compatibility and isolation arguments remain open.
