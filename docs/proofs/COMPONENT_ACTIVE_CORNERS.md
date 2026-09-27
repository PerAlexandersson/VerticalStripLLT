# A companion based on corner exposure

Status: the corner reductions and the implication below are proved
mathematically and independently audited. The ordinary connectivity statement
(AU) is OPEN. No new Lean theorem or full component formula is claimed.

This route follows the user's original suggestion: split corners into selected
and unselected cases and use recursion to dispose of already solvable terms.
The exact corner correspondence and always-redundant strict-corner deletion
are proved in [the recurrence note](FLIP_COMPONENT_INDUCTION.md).

## Ordinary structural target

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

**(AU), open.** For every ordinary saturated G and every ascent count k,
there is at most one connected active complete component at ascent k.

This is a connectivity assertion about the actual flip graph. Comparing HRV
vectors cannot prove it. It includes, as a special case, connectivity of all
spanning trees having a specified interval envelope: all tree edges are covers.
The latter statement is also open in the current work except for special cases.

## Why AU suffices for the full ordinary component formula

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

Primary and Astra independently audited this implication. It does not assume
componentwise DN transport. Its outstanding input is AU itself; the formal
corner/component correspondences must also be implemented before a Lean
completion claim. The already proved aggregate theorem is used only after
the individual other terms have been justified.

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

If AU were proved, the ordinary component theorem would also settle all
balanced circular components by the existing compatible-lift reduction.
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

Aristotle has the precise full AU statement, the verified implication,
finite evidence, and the circular counterexample. It is asked for a proof or
an exact counterexample, not another conditional reduction or a broad finite
enumeration. Current project/task identifiers and status are in
`../ARISTOTLE.md` and the repository handoff.
