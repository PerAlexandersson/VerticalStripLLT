# Attached chains and the marked-ideal companion

We prove a larger family of source-companion cancellations inside individual
flip components. We also identify an additional marked-ideal identity needed
to extend this construction to arbitrary internal components. That identity
and the full component theorem remain unproved. The results here are checked
mathematical arguments, not Lean declarations.

We use G(b,s), H_b=e_b+t e_(b-1), and (Src) from
[source branching](COMPONENT_SOURCE_BRANCHING.md). We put e_0=1, e_j=0 for
j<0, G(0,0)=1, and H_0=1. All exterior vertices in this note are isolated.
We work without strict decorations, using the exact strict-forgetting reduction
when applying these ideas to the original goal.

## Attachment transport inside one component

Fix an arc a<v_1<...<v_m<c<a+n, m>=1, with natural edge a->c.
The interval condition makes every forward edge among these vertices natural.
Let P be any selected forward relation on the internal vertices. For each
internal vertex v we form two states:

    P union {a->c, a->v},       P union {a->c, v->c}.

We call their sum the attachment packet of P. These are 2m distinct states.
Every selected path lies inside the arc, so finite maxima agree with actual
integer-cover HRV. We assert no result here for selected exterior paths.

For any cover u->v of P, we can move the incoming attachment from v to u.
Put Q=P\{u->v}. The following list gives the five flips, with Q present
throughout and edge endpoints abbreviated:

    {ac,av,uv} -> {ac,av,au} -> {ac,au,vc}
               -> {ac,uc,vc} -> {ac,uc,uv} -> {ac,au,uv}.

The respective triangles are (a,u,v), (a,v,c), (a,u,c), (u,v,c),
and (a,u,c); the first, fourth, and fifth flips are reverse flips.
Since uv was a cover, Q has no u-to-v path. This excludes the only possible
alternate path that could invalidate the intermediate long-edge covers.
The remaining cover checks use that a and c have no other attachments.
All edges remain forward, so every intermediate relation is acyclic.
The final state restores P. A direct flip on (a,v,c) exchanges the incoming
and outgoing attachment at v.

If the undirected graph underlying P is connected, its cover graph is
connected. The five-flip path therefore connects all attachment states.
Internal flips of P also lift at any fixed attachment: no path between
internal vertices can pass through the new source a or sink c. Thus cover
conditions and the reversibility of an internal flip are unchanged.

Consequently, for a complete internal component C whose selected relations
are connected, all 2m|C| attachment states belong to ONE complete target
component. They need not exhaust it. If the internal relations are
disconnected, we must separate attachments by their internal weak block.
Flips preserve the weak connected vertex partition, and attachments to
different blocks belong to different target components.

## Full source cancellation for an internal chain

Let P be the chain v_1->v_2->...->v_m. We compute the defect L-R of (Src).
For an incoming attachment a->v_j, the fiber at c is {a,c}, with one
source. The internal chain is one fiber of size m. It has no global source
when j=1, and one otherwise. Hence the incoming defects are

    -t H_2 e_(m-1)  for j=1,       0  for j>1.

For an outgoing attachment v_j->c, the fiber at c is
{a,c,v_1,...,v_j}, with two global sources a and v_1. The remaining suffix
has size m-j and has no global source. It is absent when j=m. The defect is

    D_j = t (e_(j+1)e_(m-j) - e_(j+2)e_(m-j-1))
        + t^2 (e_j e_(m-j) - e_(j+1)e_(m-j-1)).

Both differences telescope when we sum j=1,...,m:

    sum_j D_j = t(e_2+t e_1)e_(m-1) = t H_2 e_(m-1).

This cancels the incoming defect. External isolated vertices contribute the
same factor H_1 on both sides. We have therefore proved the entire (Src)
identity for every attached-chain packet, in every degree of t, while keeping
the target component label.

## The additional identity for a complete internal component

For general P write L_P=product_r G(b_r,s_r) and R_P=product_r H_(b_r).
Summing over all incoming attachments gives the exact formulas

    L_in(P) = H_2 (m L_P - t dL_P/dt),
    R_in(P) = m H_2 R_P.

Indeed, attaching to an internal nonsource changes no source count.
Attaching to a source in fiber r reduces s_r by one. Pascal's identity gives
G(b,s)-G(b,s-1)=t G(b-1,s-1), while
dG(b,s)/dt=s G(b-1,s-1). Summing over sources proves the formulas.

For an outgoing attachment at v let I_v be its inclusive predecessor ideal
in P. Put d=|I_v|, i_r=|I_v intersect B_r|, and let u_r count the original
global sources in that intersection. Let u=sum_r u_r. Then

    L_out(P,v) = G(d+2,u+1) product_r G(b_r-i_r,s_r-u_r),
    R_out(P,v) = H_(d+2) product_r H_(b_r-i_r).

The new fiber at c is I_v union {a,c}. Every vertex outside I_v keeps its old
maximum: a path from outside I_v cannot enter I_v. Source status at internal
vertices is unchanged. These observations prove the two formulas, including
empty residual fibers.

Suppose the internal complete component C satisfies (Src). Cancellation for
its whole attachment packet is then equivalent to the additional identity

    sum_{P in C} sum_v (L_out(P,v)-R_out(P,v))
      = t H_2 d/dt (sum_{P in C} R_P).                   (Ideal)

This is a precise open companion, not an implication of the internal (Src)
identity alone established here. The ideal intersections in the outgoing
terms are additional marked data. For disconnected C, a useful componentwise
version must refine the sum by the internal weak block of v.

## Counterexamples to stronger packet claims

An arbitrary fixed internal relation need not give cancellation. Suppose P
has a unique source and a unique sink. Every internal vertex is in one HRV
fiber, and the outgoing defect at v is D_d, with d=|I_v| and D defined above.
Only the incoming attachment at the unique source has nonzero defect,
namely -t H_2 e_(m-1). The chain proof uses each predecessor size 1,...,m
exactly once; that property fails for general P.

For the four-vertex diamond P={12,13,24,34}, the predecessor sizes are
1,2,2,4. Its attachment packet has defect D_2-D_3, namely

    t (e_3 e_2 - 2 e_4 e_1 + e_5)
      + t^2 (e_2^2 - 2 e_3 e_1 + e_4),

which is nonzero. All eight attachment states nevertheless lie in one target
component. Component containment alone does not imply packet cancellation.

Conversely, even full (Src) cancellation for a packet does not establish its
coloring/HRV identity. For any internal coloring of P, endpoints colored i<j
admit m plus the number of internal colors strictly between i and j attachment
choices. Thus the coloring sum of the packet is T_m(K_P), where

    T_m(f) = m e_2 f + sum_{i<k<j} x_i x_j x_k (partial f/partial x_k).

For the two-vertex chain, K_P=e_2 and the internal component is a singleton.
In three colors its four-state attachment packet has coloring sum

    T_2(e_2) = 2 e_2^2 + x_1 x_2 x_3 (x_1+x_3).

Its HRV sum is 2 e_2^2+e_3 e_1+e_4, and e_4=0 in three colors.
The coloring sum is smaller by x_1 x_2^2 x_3 and is nonsymmetric.
Nevertheless this packet satisfies (Src), by the chain result above.

There is no contradiction with the source induction: that induction also
needs restrictions after source deletion to occur with constant multiplicity
on complete smaller components. This condition is proved for FULL components,
not for arbitrary packets inside them. In particular, applying T_m to the
internal component theorem does not identify the packet's HRV sum.

## Source saturation is a separate closure operation

For a packet F and a nonempty vertex set S, consider the multiset of
restrictions A\S for A in F with S contained in the selected sources of A.
A sufficient condition for the source/alphabet induction is that, for each S,
this multiset has constant multiplicity on every smaller complete component.
We also need (Src) for F. These two conditions let us apply smaller component
identities to the nonempty-source terms and alphabet induction to the empty
source term, exactly as in the source-branching note. We do not assert that
this saturation is necessary for every possible proof of a packet identity.

A stronger, geometric closure fixes the selected boundary at S before
completing the smaller component. Repeating this operation amounts to closing
under flips with a global source outside the triangle: delete that source,
perform the smaller flip, and restore the unchanged boundary. Conversely,
every flip in a smaller component lifts in this way. The source-reconstruction
lemma supplies the cover and cycle checks. Empty S is excluded; allowing it
would immediately complete the whole target component by definition.

The two-vertex chain packet gives an explicit obstruction to preserving
cancellation under this closure. On vertices 1,2,3,4 it consists of

    {12,14,23}, {13,14,23}, {14,23,24}, {14,23,34}.

After deleting source 1, the restriction {23,24} appears once, but its flip
partner {24,34} is absent. Fixing the boundary {14} forces us to add
{14,24,34}. Further source-boundary closure adds {12,14,34} and {13,14,24}.
These seven states form a closed family for this operation. The missing
eighth state in their full target component is the outgoing star {12,13,14}.
Its sole source is 1, and every available triangle contains 1, so none of
its flips is allowed by nonempty-source boundary closure.

For completeness, use masks with edge order 12,13,14,23,24,34. The original
packet is {13,14,28,44}, its closure is {13,14,22,28,37,44,52}, and the full
component adds 7. The allowed flip edges are

    14--44,       28--52,       52--37,       52--22.

The state 13 is isolated in this allowed graph; its ordinary flip to 28
uses its only source. These lists also verify closure without relying on
a conjectural classification of components.

The two newly added states with HRV partition (3,1) each have defect

    t(e_2 e_1-e_3) + t^2(e_1^2-e_2).

The newly added incoming star has defect 2t e_3+3t^2 e_2+t^3 e_1.
Thus the seven-state closure has nonzero total defect

    H_2 (2t e_1+t^2).

The excluded outgoing star has the opposite defect. We therefore cannot
complete the attached-chain packet by this source-saturation operation while
expecting its cancellation to persist. A proof needs a rule controlling both
cancellation and closure, including flips involving all available sources.

## Verification and remaining boundary

Primary and Astra independently checked the five-flip transport, telescoping
identity, marked-ideal formulas, and the operator obstruction. Terra checked
the seven-state source closure independently. The existing Rust probe also
returned the exact eight masks of the full target component. No Lean build
was used. The full component goal still requires a componentwise cancellation
or a packet decomposition with controlled multiplicities. Even proving (Ideal)
would require a further argument that these packets suffice for that goal.

Related Rust: the existing `circular_highest_reachable_vertices` API in
`/workspace/rust/sym-poly/sym/src/llt.rs` supplies the HRV values for the
bounded external diagnostic. No shared Rust source was changed. The external
probe and earlier API audit are described in the source-branching note.

`diagnostic_bridge_packets` enumerated all complete internal components in
ordinary complete diagrams with m=1,...,5: respectively 1, 2, 7, 39, and 318
components, covering all 1, 2, 8, 64, and 1024 internal edge subsets. Their
whole attachment packets all had zero formal (Src) defect. These are finite
checks of attachment cancellation, not a proof of (Ideal). Disconnected
packets were not separated by target component in this diagnostic.

Artifacts are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/diamond-exploration/`:

- `bridge-packet-through-five.log`, SHA-256
  `f3f17cae02ea3c869377c3b0bd210ffcfd90ffadd03a905addc1d202500d4cb8`;
- `hrv-bridge/src/bin/component_source_probe.rs`, SHA-256
  `8fc7bfe7adf5ee688336b6c619c311727256861b75d11034a0f9f4c3221e1c52`;
- `component_source_probe-at-6b26e01.rs` preserves the preceding probe.

The diagnostic ran with `cargo test --bin component_source_probe
diagnostic_bridge_packets -- --ignored --nocapture` using the external manifest
and `CARGO_TARGET_DIR=/cargo-target/ai-projects`. We inspected every JSON defect;
the test harness succeeding by itself is not a check of the conjecture.
