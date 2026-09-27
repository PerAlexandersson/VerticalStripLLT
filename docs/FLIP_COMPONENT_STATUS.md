# Flip-component proof status

This is the entry point for the component research notes. The ordinary and
aggregate circular HRV expansions are already formalized. The remaining goal
is the HRV formula for each **entire flip component**, both ordinary and
circular. The [exact interface](CIRCULAR_FLIPS.md) fixes the lifted-cover
semantics. A sum over all components does not establish the individual claims.

## Established results

| Result | Verification | Detailed source |
| --- | --- | --- |
| Ordinary aggregate expansion, positivity, all finite alphabets | Lean, local build and axiom audit | [Ordinary completion](COMPLETION.md) |
| Full circular aggregate expansion and positivity | Lean, local build and axiom audit | [Circular completion](CIRCULAR_COMPLETION.md) |
| Complete-component definitions and zero-normal family | Lean | [Flip interfaces](CIRCULAR_FLIPS.md) |
| Corner selected/unselected split; deletion of an always-redundant strict corner | Audited mathematical proofs | [Recurrence reductions](proofs/FLIP_COMPONENT_INDUCTION.md) |
| Doubly endpoint-marked aggregate identity; separate ascent variables at articulation blocks | Audited mathematical proofs | [Endpoint recovery and gluing](proofs/COMPONENT_ENDPOINT_GLUING.md) |
| Corner leaf normalization; connectivity of all trees with a fixed envelope | Audited mathematical proofs | [Tree connectivity](proofs/COMPONENT_TREE_CONNECTIVITY.md) |
| Connected aggregate extraction; full ordinary and circular forest-component formula | Audited mathematical proofs | [Forest semantic companion](proofs/COMPONENT_CONNECTED_AGGREGATE.md) |
| Saturated distance-two band graphs: one entire component at every ascent, hence its HRV formula | Audited mathematical proof | [Adjacent-swap family](proofs/COMPONENT_ACTIVE_CORNERS.md#a-uniform-case-all-maximal-intervals-have-length-two) |
| Complete circular ambient reduction; compatible lifts identify balanced components with ordinary components | Audited mathematical proofs | [Ambient reductions](proofs/COMPONENT_AMBIENT_REDUCTION.md) |
| Winding lattice; finite-cover compression identifies unbalanced components with entire primitive circular components | Audited mathematical proofs | [Winding reduction](proofs/COMPONENT_WINDING_LATTICE.md) |

The new prose proofs have not yet been ported to Lean. No conditional
connectivity statement has been substituted for the component theorem.

## Main route: corners and component isolation

We follow the manuscript recurrence approach. For a saturated ordinary natural
graph, call a component **active** when every strict corner is a cover in
some member of the component. The witnesses may differ. Call it connected
when its selected undirected graph is connected.

The remaining structural proposal is:

> **AU_prime.** In a saturated ordinary natural graph with no articulation vertex,
> at each normal ascent count there is at most one active connected complete
> flip component.

Equivalently, for a general connected natural graph we fix the ascent count
in **each natural articulation block**. Uniqueness at a fixed total ascent is
false: two K4 blocks sharing a vertex give distinct active components T×U and
U×T. The [corner note](proofs/COMPONENT_ACTIVE_CORNERS.md) records the exact
counterexample and the corrected proposal. AU_prime is proved at tree level
by the new connectivity theorem and remains open beyond trees.

Why this proposal would suffice for ordinary components:

1. Induct lexicographically on vertex number and doubled area.
2. Split unmarked corners into deleted/strict cases, preserving entire
   components and decreasing area.
3. Handle disconnected selected graphs by vertex induction; delete a strict
   corner that is redundant throughout a component by area induction.
4. A minimal counterexample is therefore saturated, connected, and active.
5. Extract its block-ascent coefficient in the proved multivariate aggregate
   identity. Under AU_prime it is the sole remaining component defect.
   All other defects vanish by the justified smaller cases.

The gluing identity needed in step 5 is proved. It glues **aggregate** marked
identities; no unproved pointed component formula is used. The remaining
ordinary obligation is structural connectivity, not endpoint gluing.

## What remains for circular components

Compatible integer vertex lifts are preserved by every flip. Sorting them
identifies an entire balanced circular component with an ordinary component
and preserves the actual HRV data. All forests admit these lifts.

The forest-component formula is now proved by connected aggregate extraction
and tree connectivity, followed by this lift transport. An ordinary component
theorem beyond forests would settle the remaining balanced circular components.
For an unbalanced connected block, the gcd g of its signed cycle windings
is a flip invariant. Compression of the compatible n·g-periodic cover
identifies its entire component, with both sums preserved, with a circular
component whose winding gcd is 1. The [winding reduction](proofs/COMPONENT_WINDING_LATTICE.md)
therefore reduces the remaining circular problem to these primitive components.
Their formula remains open. Direct circular active uniqueness is false even
for a four-vertex tree example. Neither fact is a gap in the **already proved
aggregate circular theorem**.

## Auxiliary route and failed shortcuts

Source/sink deletion gives exact reconstruction and constant multiplicities
on smaller complete components. The cancellation companions Src, S_k and
StrongSrc remain open. Their precise statements are in the
[source](proofs/COMPONENT_SOURCE_BRANCHING.md),
[sink](proofs/COMPONENT_SINK_BRANCHING.md), and
[ambient](proofs/COMPONENT_AMBIENT_REDUCTION.md) notes.
[Leaf packets](proofs/COMPONENT_LEAF_PACKETS.md) and
[attached chains](proofs/COMPONENT_BRIDGE_PACKETS.md) prove uniform partial
families; the marked-ideal extension remains open.

The [diamond audit](proofs/DIAMOND_STRAIGHTENING_AUDIT.md) records why
fixed-diagram straightening alone fails. Local HRV preservation, a terminating
normalization, and small exact tests do not establish complete-component
cancellation. Keep these counterexamples available when changing a proposal.

## Navigation and next work

Current ownership and running consultations belong only in
[HANDOFF](../HANDOFF.md); remote payloads and outcomes belong in
[the Aristotle ledger](ARISTOTLE.md). Detailed experiment receipts stay next
to the claims they test. Historical handoffs are archives, not active plans.

The next mathematical target is AU_prime beyond trees, using strict-corner
deletion and its quotient graph of smaller components. A companion for
primitive circular components is still required for the full goal. Reuse the shared
Rust LLT/HRV and flip tools before adding computation; the capability audit and
any missing maintained interface are recorded in the handoff.
