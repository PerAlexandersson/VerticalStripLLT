# Ambient reduction and projected-cover components

We reduce the full decorated component problem to unmarked complete circular
diagrams. We also give a stronger sufficient companion using projected covers.
The reductions below are proved mathematical statements; the stronger companion
and the full component formula remain open. None is asserted as a Lean theorem.

## Complete circular diagrams suffice

Let U_n contain every directed natural edge orbit of positive length less than
n, with no strict edges. Let D be any undecorated circular diagram on the same
vertices, and let A be an admissible selected relation in D. Then the ENTIRE
flip component of A in U_n consists of selections in D and equals its component
in D. Both its order-enumerator sum and its actual lifted HRV sum are unchanged.

To prove this, suppose a U_n flip starts at a selected relation in D, with
triangle a<b<c<a+n. Its long edge a->c is selected and retained. Let b_D be
the nondecreasing periodic lower boundary of D. Since a->c is natural,

    b_D(b) <= b_D(c) <= a < b < c.

Thus both a->b and b->c are natural in D. Either direction of the flip stays
inside D. Admissibility and lifted covers depend only on the selected relation,
so the flip conditions agree in both diagrams. Induction along a flip path
proves the assertion for the entire component, not merely a local fragment.

The exact strict-forgetting result in
[sink branching](COMPONENT_SINK_BRANCHING.md) identifies a decorated component
with an entire undecorated component. Combining the two reductions proves
that the original full component goal is equivalent to proving it for U_n,
for every n>=1. At n=1 there are no natural edges. The empty object is handled
separately with value 1. The ascent shift when forgetting strict edges does
not affect the unweighted component identity.

The analogous statement holds for ordinary diagrams and the ordinary complete
graph. An ordinary component embedded in U_n cannot acquire wrap edges:
the zero-cut ordinary natural edge set is invariant by the same argument.

## Redundant edges preserve maxima, not lifted reachability

Let A be a projected DAG. Suppose its selected edge u->v is redundant in
the PROJECTED transitive closure. Removing this edge preserves every actual
lifted HRV maximum, as well as its uniform strict and uniform weak order
enumerators. The claim is about selected order constraints, not the original
LLT q-weight or a mixed strict/weak constraint system.

For n>=2 the edge has a unique positive increment d<n. Lift an alternate
projected u-to-v path from an arbitrary lift x of u. Its positive total
increment L satisfies L=d+k*n for some k>=0. It avoids the removed edge.
In any path using that edge, substitute this alternate path and translate
the remaining continuation upward by k*n. The result avoids the removed
edge and ends at least as high. In particular we can do this to a path to
the old maximum. Relation inclusion gives the reverse inequality, so the
maximum is unchanged at every starting lift. Projected acyclicity bounds
all paths and prevents a repeated projected vertex. The n=1 case is vacuous.

The alternate path also implies the deleted strict inequality (respectively
weak inequality) by transitivity. Thus both uniform order enumerators agree.
Sequentially remove projected redundant edges to reach the unique projected
Hasse diagram. Its cyclic edge increments determine the same HRV maxima.
Consequently the projected poset together with its cyclic vertex labels
determines these semantic quantities.

It does NOT determine full lifted reachability. For n=4, removing 01 from
{01,03,31} loses reachability from lift 0 to lift 1, although lift 5 remains
reachable and the maximum is unchanged. Selected edge multiplicities, ascent
number, strict/normal status, and actual lifted-cover flips must therefore
remain separate data. This reduction does not permit replacing the full
component by projected Hasse diagrams with multiplicity one.

## Projected covers give a stronger sufficient target

Call an actual flip strong when its two cover pairs are covers in the finite
PROJECTED reachability posets on both sides. Strong flips form a subgraph of
the actual lifted-cover flip graph. The strong components therefore partition
each full component. Proving the HRV formula on every strong component would
suffice for the original formula by summation.

For each strong component C of U_n, the following is a precise stronger
companion to seek:

    sum_{A in C} product_r G(b_A(r),s_A(r))
      = sum_{A in C} product_r H_(b_A(r)).                (StrongSrc)

Here b_A(r) is the size of an ACTUAL lifted-HRV fiber, s_A(r) is its number
of global projected sources, G(b,s)=sum_j binom(s,j)t^j e_(b-j), and
H_b=e_b+t e_(b-1). No finite-priority replacement for HRV is used.

The source-reconstruction argument applies to strong components as well.
Fix a deleted source set S and its selected boundary. Paths between retained
vertices cannot enter S, so both projected cover conditions and actual lifted
cover conditions of a smaller flip are unchanged. Every smaller strong flip
lifts reversibly with that boundary. Restrictions therefore have constant
multiplicity on full smaller STRONG components. Source deletion preserves
the remaining HRV fibers, exactly as in the source-branching note.

Thus, if (StrongSrc) holds uniformly, induction on vertices and alphabet size
proves the strong-component formula, and summation proves the actual component
formula. This is a sufficient stronger conjecture, not an equivalence claimed
with the original component conjecture. Its cancellation is still unproved.

## Mixed source/sink deletion covers every strong flip

Let a finite DAG have projected covers a->b and a->c. If all global sources
and sinks belong to {a,b,c}, its unique source is a and all sinks are b or c.
Any additional vertex v would lie on a path from a to b or c, contradicting
the corresponding projected cover. Hence a graph with more than three vertices
has a source or sink outside this triangle.

Such an exterior vertex keeps its extremal status under the flip. Deleting
it preserves the cover conditions. Consequently every strong flip on more
than three vertices descends after deleting a source or a sink. This includes
every ordinary flip. It is a connectivity/coverage lemma, not yet a valuation
identity: restoring a source imposes color inequalities, and restoring a sink
can change HRV fibers. Those extension and overlap terms still require proof.

The assertion fails for general circular lifted-cover flips. In U_4 take

    A={01,02,03,31},       B={02,03,31,12}.

The flip on 0<1<2 replaces 01 by 12. Both lifted cover pairs are valid;
the alternate path 0->3->1 reaches lift 5, not lift 1. The outside vertex
3 is neither source nor sink. The full component has precisely these two
states and {01,03,23,31}; the exceptional flip is its only edge incident to B.
Thus a path of deletion-supported flips cannot replace that edge.

## A common linear order is not available

Even a strong component need not have a common linear extension for all its
selected graphs. In U_4 the following is an entire three-state strong component:

    A={02,03,10,12},
    B={03,10,12,23},
    C={03,10,20,23}.

The first flip uses 0<2<3. The second uses lifts 1<2<4, retaining 1->0.
Inspection of the projected Hasse diagrams gives no other strong neighbors.
The union contains both 02 and 20, so it is cyclic. The actual HRV partitions
are (3,1), (4), and (4). In particular we cannot reduce (StrongSrc) to an
ordinary statement by choosing one common linear order for each component.

## Checks and provenance

Primary and Astra independently checked ambient universality, the exterior
extremum lemma, and both circular counterexamples. Terra checked the redundant
edge argument; primary explicitly retained the distinction between maxima and
full lifted reachability. Luna supplied build-free projected-cover snippets;
primary adopted only the finite reachability predicate and retained the
original lifted-flip check before imposing the stronger cover conditions.
No Lean compilation or manuscript edit was used.

The external Rust diagnostic checked (StrongSrc) on every projected DAG in
U_n for n=1,...,5. Counts of states were 1, 3, 25, 543, 29281; counts of
strong components were 1, 3, 22, 367, 13681. Every formal defect was zero.
The ambient reduction also applies to strong flips, so the same checked
components cover all smaller natural diagrams at these vertex counts.
This remains finite evidence, not a proof of (StrongSrc).

The union-cycle diagnostic stopped at the displayed n=4 counterexample.
Its test harness completed successfully, but its mathematical result is
`UNION_CYCLE`, not a passing check of the proposed common-order property.

Related Rust: `circular_highest_reachable_vertices` in
`/workspace/rust/sym-poly/sym/src/llt.rs` supplied all HRV values. No shared
Rust source or reusable polynomial family was added. Artifacts are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/diamond-exploration/`:

- `projected-components-through-five.log`, SHA-256
  `6b02e70ba31533748d264c1c15af424f96270d22b9bdfdd33dc1d4cbb75fbd5b`;
- `projected-components-final.log`, final-source replay, SHA-256
  `28fca9b8555af90c1c0ca9e0b068b5275be5337f2564130534369ab3a14c3183`;
- `projected-unions-through-five.log`, SHA-256
  `82a003ae4ca0159ecdcb5d415e52b97617a5db8cb982ce86503f02fbc5f380e8`;
- final `hrv-bridge/src/bin/component_source_probe.rs`, SHA-256
  `ada4d95fdfaf752e715e1d94e744849e461d6b5ce1b10db8818e35695662d3b9`;
- `component_source_probe-at-c6305a0.rs` preserves the prior probe.

The ignored diagnostic `diagnostic_projected_components` uses existing model,
flip and formal-defect routines. Setting `VSLLT_CHECK_UNIONS=1` additionally
checks the union of each strong component. Its early return on a counterexample
is intentional; JSON records, not the harness exit status, report the result.
