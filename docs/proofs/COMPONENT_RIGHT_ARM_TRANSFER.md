# Moving one outgoing edge in a unicyclic NN state

2026-09-28. We prove an actual-flip repair for the right first mixed NN
join. It changes one outgoing edge and fixes every other selected edge.
The preceding middle-component comparison remains open; this lemma alone
is not a whole-component recurrence. Primary and Astra independently
audited the proof and its local cover tests.

The subsequent [leftmost NN theorem](COMPONENT_LEFTMOST_NN_UNICYCLIC.md)
closes all these joins for a=0 in cycle rank one. Statements below
about remaining middle/first joins concern general a unless specified.

## Statement and strategy

We retain the saturated ordinary NN hypotheses and notation from
[the packet theorem](COMPONENT_RECURRENCE_REDUCTION.md): f=ac is strict,
b=a+1, r=bc, q=ab, and σ exchanges a,b.

**Theorem.** Let B be a connected unicyclic selected state containing
f,r,ad and omitting q,bd, where b<d<c. Then B and B−ad+bd belong
to the same actual flip component.

We separate the case where ad is a bridge from the case where it lies
on the unique cycle. In the latter case, the only obstructions to the
two moves through c are directed bypasses of the displayed edges.
We repair those bypasses explicitly.

Every edge exchanged in the displayed local moves and sweeps lies
properly inside f or r, so it is natural and not strict. The tree
normalization used in the bridge case retains strict corners by its
separate connectivity argument. A tree attached to the displayed cycle at one
vertex cannot alter its cover tests. Such trees remain attached while
their roots move, and all original strict edges are retained.

## When ad is a bridge

If f and r both cover, use

    ad → dc, retaining f;
    dc → bd, retaining r.

These moves only transfer the component attached by ad from a to b.
The retained edges keep their cover status.

Otherwise f or r lies on the unique cycle. Remove the tree attached
by ad, leaving a connected unicycle containing f,r and omitting q.
Use the q-free normalization in
[the four-cycle note](COMPONENT_FOUR_CYCLE_SWAP.md) to reach a left or
right four-cycle. If the cycle initially uses r, apply that construction
after exchanging a,b and then exchange them back. The normalization
retains f,r and has no state containing q.

This use needs only the normalizing path, not the full adjacent-swap
theorem. The path remains valid on the reduced vertex set: a,b are
still adjacent, f is still maximal, and all remaining strict edges
remain maximal. Its construction does not require the restricted
diagram to be saturated.

Lift the path with the removed tree still attached at a. At the
four-cycle all core edges cover, so the two displayed moves transfer
that tree to b. Undo the normalization. The tree, now attached only
at b, cannot change any reversed cover test. All other edges return
to their initial positions, proving the bridge case.

## When ad lies on the unique cycle

First note that r covers. A directed bypass of r lies entirely in
[b,c], so its cycle cannot contain ad, whose tail is a<b. Such a
bypass would give a second cycle. We now treat the remaining cases.

**Case 1: f is redundant.** Its unique bypass must start with ad.
Write the rest as

    a → d=x₀ → x₁ → ... → xₖ=c.

All edges on this path are normal, and b<d<c. Starting from the end,
for i=k−1,...,0 make the flip

    xᵢxᵢ₊₁ → bxᵢ, retaining bxᵢ₊₁.

The initial retained edge is r=bc. It is a bridge and covers; every
path edge covers since f is the sole redundant edge. The first move
breaks the bypass of f. After each subsequent move, the cycle consists
of f,r,ad, the initial part of the old path, and the current edge
from b. All these cycle edges cover. Thus the whole backward sweep
is actual.

We reach the four-cycle {f,r,ad,bd}, with each intermediate xᵢ,
1≤i<k, attached to b by bxᵢ. Transfer each of these pendant trees
from b to a by two flips through c. Then, for i=0,...,k−1, make

    axᵢ → xᵢxᵢ₊₁, retaining axᵢ₊₁.

This restores the old path and removes ad, while keeping bd. During
this forward sweep the unprocessed arms cover. Only the final state
makes r redundant, through bd and the restored path; r is not used
after that step. This proves the required transfer in Case 1.

**Case 2: ad is redundant.** Its bypass starts a→x with b<x<d,
since q is absent and the direct edge ad is excluded from its bypass.
The edges f,r are bridges. Use

| Retained edge | Exchanged edges |
| --- | --- |
| f | ax → xc |
| f | ad → dc |
| r | dc → bd |
| f | xc → ax |

The first move breaks the bypass of ad. After the second, xc is the
only redundant edge, through the remainder of that bypass followed by
dc. The third move breaks its bypass, so xc covers when used in the
last move. All other required edges cover. The original bypass and
all exterior edges are restored, while ad has become bd.

**Case 3: f and ad both cover.** The move ad→dc, retaining f,
is actual. If r still covers afterwards, finish with dc→bd,
retaining r.

Suppose instead that this first move makes r redundant. Its new bypass
must use dc, since r covered before the move. Thus the original state
contains a directed path

    b → x → ... → d,       b<x<d.

The inequality x<d uses the absence of bd. This path together with
ad,f,r is already the unique cycle, and all its edges cover. Replace
the attempted two-move path by

| Retained edge | Exchanged edges |
| --- | --- |
| r | bx → xc |
| f | ad → dc |
| r | dc → bd |
| r | xc → bx |

After the second move, only xc is redundant. After the last move,
only bd is redundant. Neither is required to cover at those times.
The intermediate cycle edges otherwise cover, and the table restores
the original b-to-d path. These cases exhaust the possibilities and
prove the theorem.

## What this resolves in the first mixed join

For a right target flip, put Q=T∪{ad,bd} and P=T∪{ad}. The first
mixed source join compares

    S₀∪σT∪{f,ad,bd},       S₀∪T∪{f,ad,r}.

The first state flips bd→q, retaining ad. Its middle partner is
M=S₀∪σT∪{f,ad,r}. Whenever the previously proved full swap applies
to M, we reach

    σM=S₀∪T∪{f,bd,r}.

The theorem, used backwards, now connects σM to the desired second
endpoint. Thus the held outgoing edge is no longer an additional
obstruction. The middle join and the applicability of the full swap
are separate obligations; neither follows from this theorem.

## An incoming edge need not admit the same transfer

We cannot replace the outgoing edge ad by an arbitrary incoming edge
ta in the theorem. Take area (0,1,2,3,4,5,6,4,5), strict corners
06,38, and the eligible NN step a=3,b=4,c=8. Consider

    A={06,02,26,13,38,48,68,35,78},
    B={06,02,26,14,38,48,68,35,78}.

These states are connected unicycles, contain f,r, omit q, and differ
only by the incoming bridge 13 versus 14. Deleting 06 gives trees
with respective maximal envelope intervals

    {02,13,26,38},       {02,14,26,38}.

In both, the maximal chain 0→2→6 forces a bypass of 06 in every tree
of that envelope. The
[whole-component insertion theorem](COMPONENT_TREE_CONNECTIVITY.md)
therefore identifies each source component with its respective whole
tree component. Their different envelopes prove that A and B are in
different source components. Both are inactive at 06. This is a
structural counterexample, not a failure of the component HRV formula.

## Verification

The right transfer passes exact actual-component checks in all 76
eligible NN instances through six vertices: 555 transfers, including
371 whose moved edge lies on the cycle. The two seven-vertex fixtures
area0123434 and area0123343 give 224 and 66 transfers, including 128
and 46 on-cycle cases. The two four-flip tables and the backward/forward
sweeps also pass direct cover checks; sweep lengths range from two to
22 flips. The nine-vertex incoming example is checked by its two tree
envelopes and the forced-chain theorem, without enumerating that whole
state space.

Related Rust: external `nn_component_transport.rs`, mode `--audit-right-arm`,
and `right_arm_paths.rs`, reusing the existing cover/flip and component model.
Frozen sources, commands, receipts and hashes are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/leaf-envelope/`.
No maintained Rust source, Lean build or manuscript change is involved.
