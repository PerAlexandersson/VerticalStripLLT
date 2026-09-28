# The leftward transition in the unicyclic NN step

2026-09-28. We prove the leftward counterpart of the
[rightward transition](COMPONENT_NN_INACTIVE_CORRECTIONS.md).
The argument uses tree connectivity and actual flips. It is a local
ingredient of the requested component recurrence; general active-component
isolation remains open.

## Statement and two reductions

We retain the saturated ordinary NN hypotheses of
[the packet theorem](COMPONENT_RECURRENCE_REDUCTION.md). Write
f=ac, q=ab and r=bc, with b=a+1. The corner f is strict, and the
other strict corners avoid a,b. All selected edges point forward.

**Lemma.** Let A be a connected unicyclic state selecting f,q and
omitting r. Suppose f is redundant, and an actual flip q→ta retaining
tb, where t<a, makes f a cover. Then A and A−q+r belong to the
same actual component.

The increasing bypass of f must use q. We write it as q followed
by an increasing path P from b to c. Thus the unique undirected
cycle consists of f,q,P. The edge tb is a bridge. Every other edge
belongs to a tree attached at a single cycle vertex.

Put H=Env(A−f). We use two established facts.

1. If A* is another state reached by flips not using f, has
   Env(A*−f)=H, selects q and has f redundant, then the
   [redundant middle-image lemma](COMPONENT_NN_INACTIVE_CORRECTIONS.md)
   connects A*−q+r to A−q+r. It is therefore enough to prove the
   desired conclusion for A*.
2. If a q-preserving flip makes f cover, it also gives a connection
   between A and A−q+r. The flip lifts after q is replaced by r,
   by the q-preserving lifting lemma in the same note. At the exposed
   state, q→r retaining f is an actual flip.

We prove the lemma by strong induction on t. Saturation supplies a
selected strict corner g=uv containing tb. The NN hypotheses give

    u≤t<a<b<v<c.

The head v cannot be a or b, and v≥c would make g contain f.
The edge g is a bridge, since its tail is smaller than a and the
unique cycle lies in [a,c].

## The containing corner lies in the tree attached by tb

Let X be the component detached by deleting tb. Suppose g lies in X.
Consider the local tree on X together with a,b, with edges q,tb and
the internal edges of X. Replacing tb by av gives another tree with
the same interval envelope: both removed and inserted edges lie
inside the selected g. Tree connectivity connects these two local
trees while retaining every original strict corner.

These flips lift with the exterior present. The exterior meets the
local tree only at a,b, and it has no directed path between them:
there is no backward path, and the only possible forward path between
adjacent vertices is q, which belongs to the local tree. Hence the
exterior cannot create an additional directed path in a local cover
test. Intermediate local trees need not retain q.

At the endpoint A*, q and the original bypass are restored, and av
is a bridge. The actual flip q→bv retaining av makes f cover.
The rightward-transition lemma connects A* to A*−q+r. The local
normalization also preserves H, so reduction 1 finishes this case.

## The head of the containing corner lies on the bypass

Suppose v is a vertex of P, and let yv be its preceding edge.
The flip

    yv → uy, retaining uv,

is actual: uv is a bridge and yv covers, while uy was absent by
uniqueness of the cycle. The removed edge lies properly inside g,
so it is normal. This flip preserves q and breaks the increasing
bypass of f. Reduction 2 proves the claim.

For example, take strict corners 04,25 and

    A={25,23,34,45,13,04}.

Here f=25, q=23, r=35 and t=1. The complete repair has three flips:

| Retained edge | Move |
| --- | --- |
| 04 | 34 → 03 |
| 25 | 23 → 35 |
| 04 | 03 → 34 |

Its endpoint is exactly A−23+35.

## Moving an attached tree towards an earlier cycle vertex

It remains to consider g in a different attached tree, with v off
the cycle. Let k be the root of that tree on the cycle. Distinct
attached trees do not share the vertex t, so u<t. We keep the tree
attached by tb fixed throughout this part of the proof.

Suppose first that k>v. Apply the
[interval-path lemma](COMPONENT_TREE_CONNECTIVITY.md) inside the tree
containing g, together with k, to arrange its k–v path inside [v,k].
This normalization retains g and all original strict corners. It
lifts to the whole graph because the tree has only one attachment.
Write zk for the first edge of this path, so v≤z<k, and let yk be
the preceding edge of the increasing bypass. The vertex z is off
the cycle, so z≠y.

If z<y, the actual flip yk→zy retaining zk breaks the bypass and
preserves q. Reduction 2 applies. If y<z, we instead use

    zk → yz, retaining yk.

The removed edge lies properly inside yk, and hence is normal.
Both required edges cover. This moves the entire part containing g
from k to y, while retaining the increasing bypass. Any other
branches at k stay in place. We repeat with the smaller attachment
vertex y. Each repetition strictly decreases its position along
the finite bypass. We therefore either expose f, or reach k<v.
Equality cannot occur because v remains off the cycle.

## Finishing at an attachment below v

We now have k<v, with u<a≤k<v. Let M be the maximal intervals of
the attached tree's envelope. The edge uv belongs to M. The vertex
k is not in the increasing M-chain containing uv: it is strictly
inside that maximal interval. Consequently M∪{kv} is a forest.
The edge kv is natural, so we can extend this forest to a spanning
tree with the same envelope. Tree connectivity gives a normalization
in which kv is selected.

If k=a, the selected av is a bridge, and the rightward-transition
lemma applies. Suppose k≥b. The actual flip

    kv → uk, retaining uv,

leaves the bypass unchanged. If k>b, let yk be its preceding bypass
edge. Since u<a<b≤y<k, the actual flip yk→uy retaining uk breaks
that bypass while retaining q. Both exchanged edges lie properly
inside their respective retained intervals. Reduction 2 applies.

Finally, if k=b, we have obtained a selected incoming bridge ub with
u<t. The flip q→ua retaining ub makes f cover, so the induction
hypothesis applies to the smaller incoming tail u. All preparations
in this part retain q and the original bypass, and after deleting
f they are tree flips preserving H. Reduction 1 transports the
result back to A, completing the induction.

## When adjoining q forces the bypass

We can now close one more part of the active middle-join argument at
arbitrary a. Let A be a connected unicyclic selected state selecting
f,q, omitting r, and with f redundant. Suppose its actual component
C contains a state in which f covers. Put

    T=A−f,    H=Env(T),    M=maximal intervals of H.

The forced-tree-path theorem shows that M cannot contain a directed
a-to-c path: otherwise inserting f into this whole tree component
would give an inactive-f component. The envelope H omits f,r, and
contains all other original strict corners.

**Proposition.** If F=M∪{q} contains a directed a-to-c path, then
A−q+r belongs to C.

Since M does not force this path, q∉M and the forced path is q
followed by an increasing M-chain from b to c. The graph F is a
forest: distinct adjacent vertices can belong to the same increasing
M-chain only when q is itself in M.

Choose a maximal interval g of H containing q. If g starts at a,
write g=ad. Then b<d<c. The vertex d belongs to the M-chain of a,
and not to the different M-chain of b,c. Choose a spanning tree T*
of H containing F. In A*=T*+f, ad is a bridge off the displayed
cycle, so the rightward-transition lemma gives A*∼A*−q+r.

Otherwise write g=uv with u<a. A maximal natural interval of the
original diagram containing g cannot be f. Saturation makes it another strict corner,
which is selected in T. Maximality of g in H therefore makes g itself
this strict corner. The NN hypotheses now give u<a<b<v<c.

The M-chain containing g skips both interior vertices a,b. Thus
F∪{ub} is a forest, and ub is natural because it lies inside g.
Extend this forest to a spanning tree T* of H. The selected ub is
a bridge off the increasing cycle in A*=T*+f. The leftward lemma
therefore gives A*∼A*−q+r.

In both cases, tree connectivity in H lifts after insertion of
the maximal f, so A* belongs to C. Both A and A* have f redundant
and q selected; the redundant middle-image lemma connects their
middle images. This proves the proposition.

## Scope and verification

Together with the rightward lemma, this handles every flip that
removes q and simultaneously makes redundant f a cover. It also
handles q-preserving transitions exposing f. A general path may
remove q while f remains redundant and expose f only later. Such
paths, and the remaining first mixed joins, are not settled here.
For an active middle join, the proposition reduces the unresolved
case to F=M∪{q} not forcing a→c. The prescribed-forest lemma then
supplies a q-selected tree in which f covers, but a path to that
tree need not retain q. We still need to connect this tree to the
redundant middle-image family.

More precisely, the following sufficient assertion remains unproved:
whenever H has a redundant q-selected tree and M does not force a→c,
some redundant q-selected tree of H has an actual source flip that
makes f cover. The flip may retain or remove q; both cases are now
handled by the local lemmas. The assertion would close the active
middle joins, but further first-join comparisons would still be needed.

Even the NN hypotheses do not ensure q-preserving tree connectivity.
For example, take strict f=04 in K5 and H with maximal intervals
{03,24}. The redundant tree {03,24,01,12} has q=01 and is isolated
among q-selected trees: its only tree flip is 01→13 retaining 03.
That flip exposes f, so the rightward lemma handles this example.
The DN/DD steps and higher cycle ranks remain part of the full goal.

Primary and the existing independent Astra reviewer checked the
containing-corner induction and its cover conditions. Exact local
checks pass the three-flip example, a seven-flip branch slide and
exposure, a three-flip exposure before sliding, and a two-move
preparation reducing the incoming tail from 1 to 0. The last check
also verifies the new exposing q-exit. Its first harness incorrectly
required q to survive that final exit; correcting this assertion
left all mathematical moves unchanged.

The sufficient exposure assertion passes all 55 active redundant
envelopes in the 76 eligible NN instances through six vertices:
211 q-selected redundant states, of which 192 expose f immediately.
The seven-vertex shield fixture contributes five envelopes, 72 states
and 61 immediate exposures. These counts are finite evidence for
the assertion, not a proof. The seven-vertex three-corner fixture
adds three envelopes, 28 states and 18 immediate exposures.

Related Rust: external `left_exit_paths.rs` and
`nn_component_transport.rs --audit-middle-exposure`, reusing the
existing actual-flip model. Frozen consumers, commands, receipts and
review are in `/lake-cache/ai-projects/requests/VerticalStripLLT/left-exit/`.
No Lean or manuscript change is claimed.
