# Restoring the exterior after a core path

We can shorten the restoration step in
[last-clique inheritance](COMPONENT_NN_REDISTRIBUTION.md#extending-the-last-clique-from-a-connected-core)
by applying the existing outgoing-sweep theorem a second time.
We do not need a separate induction over the recorded incoming-sweep moves.

Let the last corner be `ae`, let `a<c<e`, and retain the core

    V = {0,...,c} ∪ {e}.

Suppose the source anchor has no selected `av` with `a<v<e`.
The incoming sweep replaces precisely the selected `ve`, for `c<v<e`,
by `av`. It leaves every core edge unchanged and keeps `ae` covering.
There is then no selected edge from an omitted vertex into `e`, so a
forward path cannot leave the core and return. We may therefore lift a
core path while fixing this swept exterior, even if other retained
corners become redundant during that path.

Suppose the replacement core has `ae` covering and no selected `av`
with `a<v≤c`. At the lifted endpoint, the selected edges `av` with
`a<v<e` are exactly those inserted by the incoming sweep. We now apply
the outgoing sweep across `ae`, taking both its cutoff and its final
vertex to be `e`. It replaces all these `av` by `ve`, in increasing
order of `v`, and keeps `ae` covering.

This restores exactly the original exterior. Indeed, each omitted
`v` recovers its original `ve`; its inserted `av` disappears; and every
other exterior edge is untouched. The replacement core is also unchanged:
no edge `av` with `v≤c` is selected, so the outgoing sweep neither removes
such an edge nor inserts a corresponding core edge `ve`.

For the intended anchor application, both row conditions follow from the
good-edge condition at the last corner tail. A good edge leaving `a`
must be `ae` itself. Thus the construction applies to any actual path
from the source core restriction to a replacement core anchor. The
existence of that core path remains the smaller-core induction hypothesis.

Related Lean: `VerticalStripLLT/Components/DiagramProof/LastCornerRow.lean`,
`anchor_selected_from_last_tail_iff`; `LastCliqueRestoration.lean`,
`lastClique_restore_inside` and `lastClique_restore_outside`;
`LastCliqueCoreReplacement.lean`, `exists_lastClique_core_replacement`.
These files construct paths and exact endpoint selections; they do not
identify the value of an ambient component with a core value.
