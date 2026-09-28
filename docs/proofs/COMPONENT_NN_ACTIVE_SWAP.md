# Adjacent swaps and right NN comparisons in active components

2026-09-28. We prove the full adjacent-swap identification for a connected
unicyclic component active at every strict corner. It settles every right
first comparison in the repaired NN image. The left comparison, higher
cycle ranks and the other diagram recurrences remain separate.

We retain the saturated ordinary NN notation f=ac, b=a+1, q=ab, r=bc,
and σ=(a b). Other strict corners avoid a,b. A component is active at a
strict corner if that edge is a cover in at least one of its states.
Activity is a component condition; we do not assume that every strict
edge covers in each individual state.

## A state where all strict edges cover

Let W be connected and unicyclic, selecting f,r and omitting q.
If every strict edge covers in W, then W∼σW.

If the unique cycle uses f or r, this is the
[cycle-containing-corner swap](COMPONENT_FOUR_CYCLE_SWAP.md). If the
cycle avoids f,r but meets a or b, that vertex either has an outgoing
cycle edge or is a sink. The
[outgoing-cycle argument](COMPONENT_NN_MIDDLE_JOINS.md#an-outgoing-edge-on-the-cycle)
and [sink repair](COMPONENT_NN_SINK_REPAIR.md) cover these possibilities.

If the cycle avoids a,b, every changed edge is a bridge. Saturation puts
each incoming edge inside a selected strict corner, which covers by
hypothesis. Use the [incoming-bridge theorem](COMPONENT_NN_FIRST_JOINS.md)
to move incoming bridges between a,b, and the
[outgoing theorem](COMPONENT_RIGHT_ARM_TRANSFER.md) for outgoing bridges.
Each endpoint move restores every other edge and preserves the unique
cycle. Thus strict corners continue to cover at these endpoints, and
we may repeat until the entire adjacent swap is completed. Reverse a
bridge transfer when its original attachment is at b. Both f,r remain
selected and are interchanged as a set.

This proof uses covers directly. We need not identify the condition
with acyclicity after reversing strict edges.

## Exposing a remote strict corner

Suppose the unique cycle of W avoids a,b, and a strict corner g=uv is
redundant in W but active in its component. Put Y=W−g, a spanning tree,
and let H=Env(Y), with maximal intervals M. By the
[whole-tree insertion theorem](COMPONENT_TREE_CONNECTIVITY.md), M cannot
force u→v: otherwise inserting g into this entire tree component would
give a component inactive at g, contrary to the hypothesis.

Let F consist of M together with every edge of Y incident to a or b.
It is a forest, being a subgraph of Y, and contains f,r. The unique
u-to-v path in Y is the increasing bypass of g; it avoids a,b. No edge
added to M in forming F lies on this path. Consequently F does not
connect u,v, since such a connection would be that same path and would
already lie in M.

We apply the [prescribed-forest construction](COMPONENT_LEFTMOST_NN_UNICYCLIC.md#forced-reachability-with-a-prescribed-forest)
with a small refinement. The directed quotient H/F is strongly connected.
Choose a simple directed path from [v] to [u], lift its edges, adjoin F,
and extend the resulting forest to a spanning tree Y₀ of H. Its unique
u–v path traverses the chosen quotient edges backwards, so g covers in
Y₀+g. Every such tree omits q: F already connects a,b through f,r.

Retaining the old incident edges is not enough for the swapped tree
envelope to remain fixed. Newly added incoming edges must be controlled.
We next choose their lifts without changing this quotient tree or path.

### Choosing the incoming lifts

Consider a newly added edge sa, s<a. If its swapped edge sb is already
in Env(σY), keep it. Otherwise, any maximal interval of H containing sa
must end at b. Indeed, a container ending at a would swap to a container
ending at b, and a container ending beyond b would still contain sb.
Thus there is tb∈M with t≤s<a. Replace the chosen lift sa by sb.
The replacement is in H and its swap sa lies inside the common edge
σ(tb)=ta.

Vertices a,b are in the same F-component. Hence sa and sb have the same
directed quotient edge. Replacing this lift preserves the quotient tree,
the designated [v]-to-[u] path, and all edges of F. It cannot create a
duplicate: selecting both sa and sb together with the F-path from a to b
would already make a cycle. Nor is a newly added edge internal to an
F-component, since a tree containing F has no such extra edge.

Perform this replacement for every bad incoming lift, and call the final
tree Y*. The reversed quotient path still ensures that g covers in Y*+g.
The remaining new incoming edges sb cause no problem: their swaps sa
lie inside the swap of any maximal interval containing sb. New outgoing
edges at a,b lie, after swapping, inside the common f or r; the NN
outgoing bound gives their heads at most c.

### Comparing the two tree envelopes

We have Env(Y*)=Env(Y)=H, since both contain M. We also have

    Env(σY*)=Env(σY).                                  (1)

For one inclusion, an old incident edge belongs to F and is retained.
Every old nonincident edge lies inside some m∈M. Its endpoints avoid
a,b, so swapping the adjacent endpoints of m cannot move either boundary
past this edge. It therefore remains inside the common σm.

Conversely, all new nonincident edges are likewise contained in σM.
The preceding lift choices deal with new incoming edges, and the common
f,r contain new outgoing edges. These observations prove both inclusions
in (1). All swapped edges are forward and natural: q is absent and we
use the NN exterior swap. The strict edges other than g remain selected;
f and r are interchanged, and all other strict edges are fixed.

Tree connectivity in H gives Y∼Y*. Reinserting maximal g lifts every
flip: a path using g could bypass another natural edge only if that edge
contained g, which is impossible. Thus

    W∼W*,                 W*=Y*+g.

Separately apply tree connectivity in the common envelope (1) and
reinsert g to get σW∼σW*. We do not swap the intermediate states of
the first path; they need not admit that operation.

Finally, g covers in W* and lies on its unique cycle. Every selected edge
then covers. A redundant edge different from g would have the rest of
the cycle as an increasing bypass, and hence would properly contain the
strict corner g. This contradicts maximality of g. The previous section
therefore gives W*∼σW*. Combining the three paths proves W∼σW.

## The full swap for an active component

**Theorem.** Suppose W is connected and unicyclic, selects f,r, omits q,
and its component is active at every strict corner. Then W∼σW.

If every strict corner covers in W, the first section applies. Otherwise
there is exactly one redundant edge, a strict corner g. If the cycle uses
f,r or meets a,b, the same cycle-position lemmas apply directly. In the
remaining case the cycle avoids a,b, g differs from f, and g is active
in the component. The exposure construction above applies. These cases
exhaust all connected unicycles, proving the theorem.

The activity hypothesis matters: there are previously recorded inactive
components whose adjacent-swap images belong to different components.

## Every right first comparison

Consider an actual right target flip at a<b<d<c, with r selected:

    T₀=Q+ad+bd+r,          T₁=Q+ad+q+r.

Assume these target states are connected unicycles.
Its first source comparison has endpoints

    U=σQ+ad+bd+f,          V=Q+ad+f+r.                  (2)

Assume the component of U is active at every strict corner. The target
cover tests, transported by σ, say that ad and bd cover in U. Thus we
may replace bd by q, retaining ad. The active-middle theorem then places

    W=σQ+ad+f+r

in that same component. The full swap gives
σW=Q+bd+f+r. The outgoing-edge theorem, used backwards, replaces bd by
ad and restores every other edge, reaching V. Hence U∼V. In particular,
we did not need r to cover in T₀ or f to cover in U.

Now fix a connected unicyclic source component C active at every strict corner,
and use the [repaired indicator](COMPONENT_NN_UNICYCLIC_REASSEMBLY.md)
h=1_C+Σ_{I∈J(C)}1_I. If U is in any component active at every strict
corner, (2) stays in that component, so h(U)=h(V). If its component is
inactive at f, the unique-neighbor theorem gives the same equality. If
it is inactive at another corner g, the
[other-corner invariant](COMPONENT_UNICYCLIC_REDUNDANCY.md) puts V in
a component inactive at the same g. Both indicators are then zero.

Thus the repaired coefficients agree across every right q-changing flip
between connected selected-r target unicycles. Components inactive at a
strict corner are already reduced by whole-tree deletion. For the remaining
source components, only the left first comparison still needs a uniform
identification. A sufficient remaining lemma would move ta to tb in an
all-strict-active component while restoring all other edges. The existing
incoming-bridge theorem covers part, but not all, of that statement.

## An exact example of the lift correction

Take area (0,1,2,3,4,5,6,3), with strict corners g=06 and f=47, and
a=4,b=5,c=7. Let

    W  ={01,06,12,13,15,36,47,57},
    Y₀ ={01,15,24,34,36,47,57},
    Y* ={01,15,25,34,36,47,57}.

Here g is redundant in W and covers after insertion in either displayed
tree. Both trees have the envelope of W−g, with maxima {01,15,36,47}.
But Env(σY₀) has the extra maximal interval 25. Replacing the new lift
24 by 25 removes that error: σY* and σ(W−g) both have maxima
{01,14,36,47}.

Related Rust: external `first_join_tree_lifts.rs`, mode
`--normalized-swap-exposure`. It verifies six-flip paths for each of the
two tree comparisons, with 383 and 164 local/full cover comparisons.
All strict corners remain selected. Independent complete-component BFS
places all four endpoints in one 38,433-state component with 107,468 flip
edges. This supports the construction without serving as its general proof.

Primary and the existing Astra reviewer independently checked the proof.
The first unrestricted lift choice was rejected during review; the incoming
lift normalization above is essential. Receipts and frozen source are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/nn-active-first-joins/`.

The exhaustive scan of all 76 eligible NN instances through six vertices
checks 951 full swaps and 511 right first comparisons. The seven-vertex
area (0,1,2,3,4,3,4), at corner 26, adds 435 swaps and 216 right
comparisons. Component activity is checked separately for each strict
edge. All assertions pass and the Rust processes exit zero. These checks
support the independently audited arguments; they do not settle the left
comparison or higher cycle ranks.
