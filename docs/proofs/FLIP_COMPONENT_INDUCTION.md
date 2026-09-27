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

The coefficient proof below now establishes the recorded K identity as well
as the H identity. This gives the simultaneous target-only identity

    X_C = X_D − X_T,    X in {K,H}.

Thus this particular obstruction is repaired using complete TARGET components
at different ascents. This is a checked mathematical proof, not yet a Lean
formalization. The second recorded obstruction is also repaired below: its
two components belong to different branches of a single corner split.

For an argument retaining the aggregate q-weight, exponent changes must be
accounted for explicitly. For the component identity itself we can work
unweighted and retain each separate local equality before combining them into
one polynomial recurrence. Specializing an aggregate identity alone would
lose this component information.

## Exact corner branching and the selected-edge envelope

A natural corner edge cannot be a toggled short edge of a flip: the retained
long edge would require a natural cell above it in its column or to its left
in its row. The same argument applies to every integer translate. Its selected
status is therefore constant on an ENTIRE component.

If it is absent, delete the corner. If it is present, make it strict. Both
operations preserve the selected relation exactly, including all integer
lifts. They preserve admissibility, cover tests, and every flip in both
directions. Thus each branch carries entire components, with their actual
coloring and HRV semantics. Strictification removes one counted normal ascent;
this accounts for the factor t in the aggregate corner recurrence.

Repeating this procedure removes all unselected outer cells and leaves the
interval envelope generated by the selected edges. This envelope is invariant
under flips: the new short edge is inside the retained long edge. Every corner
of the resulting envelope is selected and can be made strict. There is no
claim that fixed ascent determines a component in this saturated diagram;
the first diagnostic below disproves that stronger assertion.

## General reduction: an always-redundant strict corner

**Proved mathematically; not yet formalized.** Let e be a strict corner of D
and C a complete component. Suppose that in EVERY state A of C the natural
lift of e is not a cover. Equivalently, its endpoints are joined by a selected
lifted path not using e. Then deleting e identifies C with an ENTIRE component
of `D.deleteCorner e`, preserving full lifted reachability, coloring enumerators,
and actual HRV monomials state by state. The normal ascent count is unchanged;
the doubled geometric area decreases by one. Thus smaller-area component
induction proves the identity for C.

We prove the claim for the manuscript's actual lifted-cover flips, including
circular diagrams. There are three points to check.

1. A natural corner interval cannot be properly contained in another natural
   edge interval. A path testing the cover of any other natural edge therefore
   cannot use any translate of e: positive steps keep that entire path inside
   the tested interval. Deleting or inserting e does not change any OTHER
   natural-edge cover test. It also cannot toggle e, which is a corner.

2. The union of the selected relations of two admissible flip states is
   projected acyclic. A simple cycle in the union would have to use both
   exchanged edges ab and bc; either one alone belongs to an acyclic endpoint
   state. They must be consecutive on the simple cycle. Replacing them by
   the retained edge ac gives a cycle in both endpoint states, a contradiction.
   Now start with A in C and its image B=A without e. Given any target flip
   B to B', this union is acyclic. The alternative path for e is contained
   in B, so adjoining e to B union B' leaves its reachability unchanged.
   In particular A'=B' plus e is admissible. All the required cover tests
   agree by point 1, so this is a genuine source flip A to A'.

3. Since A' is reached by a source flip, A' belongs to C. The hypothesis on
   the WHOLE component supplies the alternative lifted path for e again.
   Induction along any target flip path therefore constructs its preimage
   in C. Conversely, a source flip in C uses e neither as a short edge
   (it is a corner) nor as its retained long cover (it is noncovering).
   It consequently deletes to a target flip. Insertion/deletion are inverse,
   proving the correspondence with complete components, not just fragments.

Finally, substitute the alternative path for every use of every translate of e.
This proves equality of full lifted reachability on each matched pair.
The projected order constraints and reachable maxima agree, giving both
semantic identifications. This is stronger than projected redundancy alone;
an alternative path ending one period later would not justify the lemma.

Primary and Astra independently checked the reconstruction, including the
acyclicity of reinserted target states. The whole-component hypothesis is
essential: a corner can be redundant at one state and covering at a neighboring
state. In the first diagnostic all three ancillary source components satisfy
the hypothesis for corner 25, but C does not. Their separate base calculations
can therefore be replaced by this general smaller-area reduction.

Related Lean: `Circular/CornerPairs.lean` exports
`deleteCorner_naturalPairs` and `deleteStrictCorner_pairGraph_normalEdges`;
`CornerDeleteOrientation.lean` has the edge inclusion/restriction maps.
`LiftCover.lean`, `Flip.lean`, and `HRVPotential.lean` supply the actual lifted
covers, complete component relation, and HRV transport interfaces. Luna audited
these APIs without building. The existing `orientToDelete` and
`orientFromDelete` require a NONSTRICT corner, so they do not yet implement
this theorem. Also, `D.liftStep (theta.val.erase e)` does not delete a strict e:
`liftStep` always includes `D.strict`. The alternative-path hypothesis must use
the deleted diagram's transported selection or a relation explicitly filtering
out e. There is no global equivalence of all target/source orientations;
reinsertion is justified along the particular component by the proof above.

## Ordinary corner deletion as an exact component quotient

There is a stronger structural statement in the ordinary case. Let e be a
strict corner, without requiring it to be redundant. All orientations of D
identify with orientations of D-e by removing the fixed edge e: all ordinary
selected relations are acyclic and the normal edge set is unchanged.

Under this identification, the flip graph of D is exactly the flip graph
of D-e with the valid flips retaining e as their long edge added. The earlier
corner-interval argument shows that e affects no other natural-edge cover
test. It cannot be a toggled short edge. Thus all old target flips lift, and
the only additional source flips are precisely those supported by e.

Contract each COMPLETE component of the smaller diagram to a vertex, and
keep an edge whenever an e-supported source flip joins two such components.
The connected components of this quotient graph are exactly the complete
source components. Exposure of every OTHER strict corner is preserved
pointwise by deletion. This is an actual graph statement, not a proposed
matching of local-state tables. It must not be extended to arbitrary circular
orientations without checking admissibility of reinsertion.

For e=(a,a+2), there is only one supporting triangle. Its adjacent short edges
are automatically covers when selected; e is redundant precisely in state 11.
The additional quotient edges therefore come from exactly the unconditional
10-to-01 swaps on those shorts, with arbitrary fixed exterior selection.
Deleting e makes a+1 an articulation of the natural graph: any other edge
crossing it would properly contain the maximal corner interval e.

The short edges need not themselves be corners after deletion, so exterior
flips can change their status. This gives a smaller-block connectivity problem,
not an independent cube decomposition. Proving the requisite connectivity of
active quotient classes remains open. The newly proved endpoint/gluing theorem
in `COMPONENT_ENDPOINT_GLUING.md` supplies the separate block-count aggregate
identity needed once such structural isolation is established.

## Diagnostic certificates: the two recorded bounce obstructions

These are repairs of existing proof obstructions, not substitute targets for
the full component theorem. We use one-based labels and weak/h notation.
The same diamonds give strict/e identities, with no appeal to the conjecture.
Primary and the independent Astra reviewer checked both certificates.

### The five-state source and six-state target

For X=`ndnndeee`, let a,b,c,d,e denote normal edges 23,24,34,35,45;
the strict edges are 12,25. Its complete ascent-three components are

    C = {abc,abd,bcd,bde,cde},
    S1 = {acd,ade}, S2 = {abe,bce}, C0 = {ace}.

For Y=`nndnedee`, let A,B,C,D,E denote normals 12,23,24,34,45;
the strict edges are 13,35. Its complete ascent-three components are

    D = {ABC,ACD,ACE,BCD,BCE,CDE},
    T1 = {ABD,ABE}, T2 = {ADE,BDE}.

These lists exhaust all ten three-element normal selections on each side;
the actual cover flips give exactly the listed components. Each of S1,S2,
T1,T2 is a two-state diamond whose zero state is a four-chain plus an isolated
vertex, and whose full state is a five-chain. The triangles are respectively
345,234,345,123. Consequently each has valuation h41+h5, for BOTH valuations.
C0 is a five-chain, so its valuation is h5.

Taking the ascent-three coefficient in the proved DN recurrence gives

    X_C + 2(h41+h5) + h5 = X_D + 2(h41+h5),  X in {K,H}.

Cancelling the solved terms proves X_C+h5=X_D. This uses only aggregate
recursion and independent diamond/chain proofs, not the component identity
for either C or D. The singleton maximal-ascent target supplies the same h5
correction, giving a signed formula entirely in target components.

X is already saturated: its only natural corners are the two strict edges.
All ten states have connected underlying selected graphs on five vertices.
Thus saturation, ascent, and weak connectivity together do not imply that
these states form one component. The recurrence succeeds by eliminating
independently solved source components.

### The two four-state components: split corner 24 first

In Y=`nndnedee`, use lower-case a,b,c,d,e for 12,23,24,34,45.
At ascent two its components are

    C1 = {ac,bc,cd,ce}, C2 = {ad,ae,bd,be}, {ab}, {de}.

Crucially, 24 is an unmarked NATURAL CORNER. Every state of C1 selects it,
whereas every state of C2 omits it. The corner recurrence therefore puts C1
in the strictification branch and C2 in the deletion branch. The eight-state
merger under the unrestricted bounce ignores this useful branch information.

C2 is the product of the diamonds 123 and 345, with 24 absent. Resolve the
first diamond for each state of the second, then resolve the second for each
zero/full state of the first. The four resulting posets are disjoint unions
of chains, of types 311,41,41,5. All exterior edges are retained. Hence

    K_C2 = H_C2 = h311 + 2h41 + h5.

The singletons ab,de each give h41. Consequently the ascent-two aggregate
bounce equation to `nnndeede` isolates C1 after the target components and
these independently solved source terms are handled. This removes the
second recorded same-ascent obstruction; no assertion that arbitrary source
components transport individually is required.

## A full family of independently solved corrections

Take vertices v0<...<v_(2k), retain the k spine edges v_(2i)->v_(2i+2),
and in each triangle choose exactly one of its two short edges. These 2^k
states form an ENTIRE component, even in the complete ordinary ambient graph.
Their selected-edge envelope contains just those consecutive triangles;
every flip stays in it. The only possible flips switch the independent short
choices. No other triangle or cover condition introduces extra states.

Resolve all k diamonds. A subset J of full states gives one chain of length
k+1+|J| and k-|J| isolated middle vertices. Thus both component valuations are

    sum_(j=0)^k binom(k,j) h_(k+1+j) h1^(k-j).

The empty case k=0 is included. Disjoint products with independently solved
components preserve the identity. This is a uniform proved family of source
corrections. It does not assert that all correction components are of this form.

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

## A potentially shorter proof: straightening whole component sums

**Subsequent audit:** the fixed-diagram diamond-and-chain statement below is
false, even with signed rational coefficients. The exact obstruction and a
repair using auxiliary states and an HRV-preserving swap are in
[DIAMOND_STRAIGHTENING_AUDIT.md](DIAMOND_STRAIGHTENING_AUDIT.md). This section
records the proposal that led to that audit, not an active conjecture.

A follow-up independent review suggests separating the proof into two reusable
facts. First, both K and H respect each valid global diamond relation

    [theta10] + [theta01] − [theta00] − [theta11] = 0.

Second, prove a geometric straightening statement: a positive integer multiple
of each complete flip-component indicator is congruent, modulo these diamond
relations, to a signed sum of orientations whose projected reachability posets
are disjoint unions of chains. On these terminal states K and H agree termwise.
For circular orientations each chain has a unique sink, so its HRV fiber is
the whole chain, even when its chosen lifts wind. Applying the two valuations
and cancelling the positive integer would prove the component theorem.

This fixed-diagram statement would avoid transporting complete components
through all the path recurrences. It is a proposed sufficient lemma, not a
proved theorem, and may be stronger than needed. If the available diamonds
are insufficient, enlarge the relations only by separately verified global
identifications or return to the smaller-diagram induction.

The crucial question is compatibility of OVERLAPPING diamonds. Mere pairwise
identities are insufficient: an abstract three-state flip path with defects
satisfying d_a+d_b=0 and d_b+d_c=0 permits (u,−u,u), with nonzero component sum.
This is an abstract warning, not a counterexample among LLT diagrams. The
special circular interval geometry must supply additional relations or force
this alternating defect to vanish.

Neither a unique oriented-flip normal form (already obstructed in the notes)
nor the squared-ascent termination observation proves the straightening lemma.
The next useful proof-search target is a global overlap-completion argument:
when a diamond replacement removes a needed partner for another replacement,
show how the resulting discrepancy is resolved using further valid diamonds,
possibly in a smaller diagram. Preserve exterior cover conditions throughout.
This is where the existing sketches should be mined for a single reusable
argument, before formalizing another large recurrence-by-recurrence framework.
