# Corner exposure: a reduction and an ordinary obstruction

Status: the corner reductions and the implication below are proved
mathematically and independently audited. The first ordinary connectivity
proposal (AU) is FALSE at n=7, despite passing the full n<=6 diagnostic.
A refined companion remains open. No new Lean theorem or full component
formula is claimed.

This route follows the user's original suggestion: split corners into selected
and unselected cases and use recursion to dispose of already solvable terms.
The exact corner correspondence and always-redundant strict-corner deletion
are proved in [the recurrence note](FLIP_COMPONENT_INDUCTION.md).

## Ordinary structural proposal (AU): refuted below

Let G be an ordinary natural edge set on 0,...,n-1, closed under subintervals:
if ij belongs to G and i<=a<b<=j, then ab belongs to G. Let S be the maximal
intervals of G, and declare all of them strict. Thus the diagram is saturated.
A selected state is a subset A of G containing S. All edges point forward.

The flip graph uses the manuscript cover conditions: for a<b<c, exchange ab
with bc while retaining ac, with ab,ac covers before and ac,bc covers after.
All other selected edges agree. A complete component includes every such flip,
including those meeting any proposed local boundary.

Call a component active if each strict corner is a cover in SOME member:

    for every e in S, there exists A in C such that e is a cover in A.

The witnessing member can depend on e. This is not the stronger requirement
that one state exhibit all the corners as covers simultaneously. Call the
component connected if its selected undirected graph connects all n vertices.
This property, and the normal ascent count |A minus S|, are constant under flips.

**(AU), false as stated.** For every ordinary saturated G and every ascent count k,
there is at most one connected active complete component at ascent k.

This is a connectivity assertion about the actual flip graph. Comparing HRV
vectors cannot prove it. It includes, as a special case, connectivity of all
spanning trees having a specified interval envelope: all tree edges are covers.
The latter statement is now proved in full in
[the tree-connectivity note](COMPONENT_TREE_CONNECTIVITY.md). The refinement
beyond trees remains open; see the [current proof map](../FLIP_COMPONENT_STATUS.md).

## The conditional implication, and the information it requires

We induct lexicographically on vertex number and doubled area. Suppose C were
a counterexample minimal for this measure.

An unmarked natural corner has constant status throughout C. Deleting it if
unselected, or strictifying it if selected, identifies C with an entire
component at smaller doubled area and preserves the unweighted contributions.
Therefore a minimal counterexample is saturated.

If C has more than one selected weak connectivity block, every flip stays
within one block. Restricting the natural diagram to each block and compressing
its vertex order gives smaller ordinary diagrams. Complete components and both
valuations factor as products over the blocks. Vertex induction therefore
handles all disconnected components.

If some strict corner is never a cover in C, the general strict-corner deletion
lemma identifies C with an entire smaller-area component. Thus C is active.

Now take the coefficient of its ascent k in the already proved aggregate
ordinary expansion. This gives the sum of K_T-E_T over ALL complete components
at that ascent, with coefficient one for each component. All disconnected
components vanish by vertex induction, and all inactive components vanish by
strict-corner deletion and area induction. Under AU, at most one component
remains, namely C, so its defect must be zero. This is the required contradiction.

Primary and Astra independently audited this conditional implication. It does
not assume componentwise DN transport. The counterexample below prevents using
AU to discharge its hypothesis. The formal corner/component correspondences
must also be implemented before a Lean completion claim. The aggregate theorem
is used only after the individual other terms have been justified.

## Exact ordinary counterexample at n=7

Take natural cliques on the one-based intervals [1,4] and [4,7], meeting only
at vertex 4. The area sequence is (0,1,2,3,1,2,3), with precisely the two
strict corners 14 and 47.

For one K4 block with strict corner 14, order its normal edges as

    (a,b,c,d,e) = (12,13,23,24,34).

Two of its complete connected components are

    T = {ab,ac,ae,bc,bd,cd,ce,de},
    U = {abc,abd,bcd,bde,cde}.

T consists of the eight trees containing 14, at normal ascent two. U has five
states at normal ascent three. Both are active: all tree edges are covers,
and in U the corner is a cover in abc,bcd,cde. These component lists follow
by testing the four possible triangles; the existing exact enumerator gives
the same masks, respectively [3,5,6,10,12,17,20,24] and [7,11,14,26,28].

Every natural triangle of the seven-vertex diagram lies within one of its
two cliques. A forward path cannot leave such a clique and return, so the
other clique does not change its cover tests. The complete component graph
is consequently the Cartesian product of the two block component graphs.

Thus T_left times U_right and U_left times T_right are distinct complete
components, each with 40 states, total normal ascent five, and one connected
selected weak block. Both strict corners can even be covers simultaneously.
The number of selected normal edges in the left clique is invariant under
every flip, and equals two versus three. This proves that the two components
cannot join. Primary found this composition obstruction and Astra independently
audited the entire-component and cover claims.

The useful lesson is precise: weak connectivity alone does not remove an
articulation vertex, and total ascent loses the separate block counts.

## The refinement and its now-proved semantic input

One can ask for active uniqueness at each VECTOR of ascent counts in the
natural graph's articulation blocks, or first restrict to natural graphs
without an articulation. Neither refinement is proved here.

The vector version requires an actual multivariate aggregate HRV theorem,
with an independent q variable for each block. This input is now proved
mathematically in [the endpoint/gluing note](COMPONENT_ENDPOINT_GLUING.md):
strict pendant chains and triangular recovery derive the doubly marked
aggregate theorem from the verified ordinary theorem. The marked formulas
then glue while retaining the articulation's color and HRV fiber. This proves
the aggregate identity with separate block variables, without assuming any
component-level pointed identity. The structural uniqueness refinement is
still open. The two proved corner reductions remain valid.

## A uniform case: all maximal intervals have length two

Suppose the saturated connected graph has every adjacent edge and every
distance-two edge, and no longer edges. Its strict edges are all (i,i+2);
its normal edges are (i,i+1). This is the square of a path, with n≥3.
Encode the normal selection by a binary word of length n−1.

Every possible flip uses three consecutive vertices. The two adjacent edges
are covers whenever selected, and (i,i+2) has an alternate path exactly when
both adjacent edges are selected. Hence flips are exactly adjacent exchanges
10↔01. At each fixed number k of ones, repeated exchanges 10→01 reach the
unique word consisting of zeros followed by k ones. The sum of positions of
the ones strictly increases and is bounded, proving termination and full
connectivity at that ascent.

Thus each ascent coefficient in the aggregate theorem is already one ENTIRE
component sum. This proves its actual HRV formula for all n and alphabets,
including components with undirected cycles. The n≤2 cases are immediate.
Claude supplied the adjacent-swap proof; primary audited it and extracted
the polynomial consequence. It does not extend AU_prime to longer corners.

Deleting a maximal edge of length at least three preserves the natural
distance-two edges and hence the absence of an articulation. It does not
preserve saturation: newly exposed natural corners remain unmarked in the
exact deletion correspondence. For example, deleting strict 14 from K4
leaves 13 and 24 unmarked. Making them strict selects only one branch and
loses other states. The exact bridge graph in the recurrence note remains
valid; it cannot be replaced by the saturated smaller diagram's flip graph.

The region where one strict corner is redundant is not generally a union
of complete components. With strict 14, the states

    {14,13,23,24} ↔ {14,12,13,24}

differ by a genuine flip at 1<2<3 retaining 13. Edge 14 is a cover in the
first and redundant via 12,24 in the second. This refutes the extra closure
condition suggested in Claude's proposed bootstrap. It does not contradict
the proved deletion theorem, which assumes redundancy on an ENTIRE component.

## Why the circular statement needs more information

The direct circular version of AU is false. On four zero-based vertices take
area sequence (2,1,2,3), whose two corners 20 and 03 are strict. The selected
trees

    A = {20,03,01},    B = {20,03,12}

have the same saturated envelope, the same three selected edges in cardinality,
and one weak block. Every selected edge remains a cover in either entire tree
component. Nevertheless their components are different.

Normalize compatible lifts by z0=0, z2=-2, z3=3. In A the edge 01 forces z1=1;
in B the edge 12 forces z1=-3. The compatible-lift preservation theorem in
[the ambient reduction note](COMPONENT_AMBIENT_REDUCTION.md) excludes any flip
path between them. Both directions have natural positive increments and both
selected graphs are admissible. Thus activity, ascent, and weak blocks alone
cannot isolate circular components. This counterexample does not refute the
ordinary statement or the component HRV formula.

A valid ordinary companion proving the component theorem would also settle
all balanced circular components by the existing compatible-lift reduction.
Unbalanced circular components would still require an additional argument.

## Finite evidence and proof-search boundary

Primary tested AU for every ordinary saturated diagram through n=6 using the
previously checked `probe.model` flip enumerator. Cumulative totals are 196
diagrams, 33,867 selected states, 4,228 components, and 176 active connected
components. No counterexample occurred. At n=6 alone there are 132 diagrams
and 32,768 states. These totals count selected subsets, not polynomial values;
the test checks actual covers and full components.

The bounded diagnostic is a thin Python screen over the existing model.
The shared Rust capability guide, metadata, and source search were checked
again; no maintained flip-component enumerator was found. Reusing this screen
avoids a new duplicate implementation or a Rust rebuild. No polynomial family
or shared Rust source was introduced. The maintained integration proposal
remains `suggestions/flip-enumeration-api.md`.

Files under
`/lake-cache/ai-projects/requests/VerticalStripLLT/diamond-exploration/`:

- `active_corner_audit.py`, SHA-256
  `2eb9c8a15afaa16ed3cc481d125c0cd51440a473e2a790a8d873426747085292`;
- `active_corner_audit.log`, SHA-256
  `a3b8061f3be2e228573e1df9ae0b6f81ce02a9cadd96df0684a8be78d93f4661`.

The original saturated five-state example shows why inactivity must be
removed: four components share its ascent and connected block, but three
have corner 25 always redundant. Only the remaining component is active.
Greedy outgoing-fork normalization does not prove AU: the earlier exact
nonconfluence example has distinct terminal states, and terminal states can
hide corners that are exposed elsewhere in their component.

Aristotle initially received AU, its verified conditional implication,
finite evidence, and the circular counterexample. Primary then sent the exact
n=7 ordinary obstruction to the SAME running task and explicitly withdrew AU
as a theorem target. The correction asks for an audit and a usable refinement
that retains the block counts and the required pointed gluing information.
Current project/task identifiers and status are in
`../ARISTOTLE.md` and the repository handoff.
