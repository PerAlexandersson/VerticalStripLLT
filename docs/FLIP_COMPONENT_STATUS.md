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
| Minimum-area saturated envelope; corner branching; deletion of an always-redundant strict corner | Audited mathematical proofs | [Recurrence reductions](proofs/FLIP_COMPONENT_INDUCTION.md) |
| Ordinary signed corner-deletion recurrence; HRV-map-preserving mixed-cycle involution; relative path absorption | Audited mathematical proofs | [Corner differences](proofs/COMPONENT_CORNER_DIFFERENCES.md) |
| Explicit {−1,0,1} HRV-map coefficients and signed component counting refinement | Audited mathematical proofs | [Exact HRV differences](proofs/COMPONENT_HRV_DIFFERENCES.md) |
| Strict-chain normalization by actual flips; deterministic representatives, connected fibers and exact fiber coloring sums | Audited mathematical proofs | [Chain normalization](proofs/COMPONENT_CHAIN_NORMALIZATION.md) |
| Explicit ordinary DN completion graph; simultaneous semantic transport and whole-component reconstruction | Audited mathematical proof, conditional isolation still open | [DN component completion](proofs/DN_COMPONENT_COMPLETION.md) |
| Doubly endpoint-marked aggregate identity; separate ascent variables at articulation blocks | Audited mathematical proofs | [Endpoint recovery and gluing](proofs/COMPONENT_ENDPOINT_GLUING.md) |
| Corner leaf normalization; connectivity of all trees with a fixed envelope | Audited mathematical proofs | [Tree connectivity](proofs/COMPONENT_TREE_CONNECTIVITY.md) |
| Connected aggregate extraction; full ordinary and circular forest-component formula | Audited mathematical proofs | [Forest semantic companion](proofs/COMPONENT_CONNECTED_AGGREGATE.md) |
| Saturated distance-two band graphs: one entire component at every ascent, hence its HRV formula | Audited mathematical proof | [Adjacent-swap family](proofs/COMPONENT_ACTIVE_CORNERS.md#a-uniform-case-all-maximal-intervals-have-length-two) |
| Complete circular ambient reduction; compatible lifts identify balanced components with ordinary components | Audited mathematical proofs | [Ambient reductions](proofs/COMPONENT_AMBIENT_REDUCTION.md) |
| Winding lattice; finite-cover compression identifies unbalanced components with entire primitive circular components | Audited mathematical proofs | [Winding reduction](proofs/COMPONENT_WINDING_LATTICE.md) |
| Aggregate identity at each exact blockwise signed-walk invariant and ascent | Audited mathematical proof | [Exact winding companion](proofs/COMPONENT_LATTICE_AGGREGATE.md) |

The new prose proofs have not yet been ported to Lean. No conditional
connectivity statement has been substituted for the component theorem.

## Main route: pass components through the recurrences

The author recalls a proof by splitting the local orientations and transporting
components through the manuscript relations. The current task is to make
those maps and their regrouping precise. The author's induction parameter is
now explicit: the saturated selected-edge envelope is the unique minimum
half-square-area realization on the fixed vertex order, for ordinary and
circular components. Every corner can be assumed strict. Components with
ANY always-redundant strict corner are already handled by smaller-area
induction. A recurrence may express the desired component as a signed linear
combination of whole smaller components.

The new [corner-difference recurrence](proofs/COMPONENT_CORNER_DIFFERENCES.md)
proves exactly such a signed formula in the ordinary case. It applies whenever
every state becomes cyclic upon reversing the strict corners while keeping
selected normals forward. Inclusion–exclusion supplies its coefficients;
the ordinary deletion quotient proves all right-hand terms are ENTIRE smaller
components. The HRV cancellation uses a sign-reversing involution preserving
the full reachable-maximum map. This includes the case with no state covering
all corners simultaneously, even when every corner is individually active.
A minimum-area ordinary counterexample must therefore have a state acyclic
after reversing its strict corners. That remaining class is not yet solved.
The [exact HRV differences](proofs/COMPONENT_HRV_DIFFERENCES.md) now compute
every surviving map coefficient from local outgoing-edge conditions. At a
fixed map, all contributing normal selections in a component have the same
sign, giving a precise count to compare with the mixed coloring enumerator.
Fixed-color fibers can be disconnected, and canonical HRV chains cannot
preserve each vertex's color: both proposed shortcuts have exact obstructions.
The required matching may redistribute colors while preserving monomials.

The new [strict-chain normalization](proofs/COMPONENT_CHAIN_NORMALIZATION.md)
uses actual flips while preserving mixed acyclicity. Process ALL strict-chain
blocks, including singleton vertices, by decreasing largest vertex. This gives
an explicit idempotent map to states whose normal edges increase the chain
maxima. Every fiber is connected, and its coloring sum has exact constraints
requiring certain colors to lie outside specified intervals. Distinct such
representatives can lie in the same whole component; a single fiber does not
in general satisfy the HRV identity. Strict-long flips between representatives
either disappear inside a fiber or become simultaneous successor slides across
crossing strict corners. The remaining target is their component-level semantic
recurrence, including normal-long flips and mixed-cyclic intermediate states.

Several packet equations may be combined. The proved
[recurrence-generation companion](proofs/FLIP_COMPONENT_INDUCTION.md#signed-recurrence-generation-without-a-uniqueness-requirement)
reduces this to full rational column rank after known components are removed;
integer denominators clear by torsion-free cancellation. The required uniform
generation is open. A uniqueness assertion for each individual packet is a
sufficient special case, not a requirement of this induction. The
[recurrence note](proofs/FLIP_COMPONENT_INDUCTION.md#a-precise-component-transport-criterion)
now gives an exact integer certificate: if B records multiplicity differences
across actual flips, a transport T reconstructs complete components precisely
when B_target T=H B_source for an integer H.

The separate coloring and HRV semantic residuals may factor through B_source;
paired diamonds give this cancellation without pointwise semantic equality.
Signed corrections must land in certified complete packets or states. The
resulting component induction lemma is proved, but the global recurrence
transports and their exterior/mixed-flip certificates are still to be built.
The concrete relation-(3) construction retains the exterior swap in the
zero state and the unchanged exterior in the full state. This gives explicit
signed multiplicities with a free target-diamond parameter. A proved local
classification reduces nonflip blocks to closure-degenerate endpoint terms
or smaller corner-deletion packets. Their global regrouping remains open.
Within this signed transport family, the regrouping equations are equivalent
to integer potential differences on an exterior-subset multigraph. A potential
exists exactly when all closed-walk sums vanish, including those crossing
ascent levels. This criterion is proved. The induced zero/full flip graphs
also have proved transports, using the actual lifted covers.

An ordinary extension removes the paired-multiplicity assumption by adding
an explicit linear corner-deletion residual. Its target cannot always be
reconstructed while that residual stays fixed: the existing saturated
five-state diagnostic gives contradictory equations at two ascent levels.
The two deletion diagrams embed as whole-component sectors of a shared
diagram with two unmarked corners. Resolving a corner places every such
component in a strictly smaller diagram, so its identity is available under
area induction. This common component space is proved; the required joint
redistribution is still open in general.
Alternating corner differences now localize each ordinary component defect
on states acyclic after the chosen corners are reversed. A relative
path-absorption identity removes certain incoming edges without changing
those single-corner differences. Its state projection does not yet reconstruct
whole components. These identities do not require the auxiliary AU_prime
conjecture.

The new [DN completion lemma](proofs/DN_COMPONENT_COMPLETION.md) gives a more
specific sufficient construction. An explicit graph joins source components
according to the local middle pairing and every target flip equation. Any
union of its connected classes transports to an integer combination of
ENTIRE target components, preserving both K and E. This reconstruction is
proved, including the exterior zero-state rows. The remaining assertion is
that each class contains at most one component in which the chosen strict
corner f is a cover somewhere. Every other component can then be deleted
by the proved inactive-corner reduction and subtracted by induction. The
ordinary DN target decreases the area moment at fixed doubled area.

This local isolation assertion remains open. It passes three targeted exact
fixtures, including one with two crossing strict corners and a checked failure
of the uncorrected deletion packet in an earlier fixture.
It is a sufficient restriction of the general signed transport problem,
not an assumption of the aggregate theorem or the auxiliary AU_prime claim.
A new crossing-corner sweep proves that certain boundary flips can be
preconditioned to keep the distinguished corner covering. The case with
both attachments already selected now has a relative valuation identity:
remove the incoming edge using a path through the crossing strict corner.
Applying all corner differences leaves a correction in a smaller diagram;
its signed occurrence multiplicities still need whole-component regrouping.

## Auxiliary route: corners and active uniqueness

We follow the manuscript recurrence approach. For a saturated ordinary natural
graph, call a component **active** when every strict corner is a cover in
some member of the component. The witnesses may differ. Call it connected
when its selected undirected graph is connected.

One sufficient auxiliary structural proposal is:

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
4. A minimal ordinary counterexample is saturated, connected, and contains
   a state acyclic after reversing the strict corners; in particular it is active.
5. Extract its block-ascent coefficient in the proved multivariate aggregate
   identity. Under AU_prime it is the sole remaining component defect.
   All other defects vanish by the justified smaller cases.

The gluing identity needed in step 5 is proved. It glues **aggregate** marked
identities; no unproved pointed component formula is used. For this auxiliary
route, the open obligation is structural connectivity, not endpoint gluing.

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
Their formula remains open. The [exact winding companion](proofs/COMPONENT_LATTICE_AGGREGATE.md)
now refines the aggregate formula to each full signed-walk invariant and
ascent. This still groups several complete components: the note gives two
active primitive components with the same invariant, no chain-poset states,
and different HRV sums. Further component isolation is necessary. These are
obligations for the component theorem; the aggregate circular theorem remains
fully proved. Arbitrary strict-corner deletion does not preserve the ordinary
component quotient in circular diagrams: new admissible target states can
escape the source image. The [corner-difference note](proofs/COMPONENT_CORNER_DIFFERENCES.md#why-the-arbitrary-deletion-quotient-is-ordinary)
gives an exact three-vertex obstruction. The proved always-redundant-corner
reduction remains valid; the unrestricted signed deletion recurrence is
currently ordinary.

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

The next mathematical task is signed recurrence generation for components at
their minimum envelope area. The DN completion graph is one concrete family
of certified packet rows. Its isolation assertion is sufficient, but allow
corrections proved by the corner-difference recurrence and combinations of
several packet equations. The remaining ordinary components have acyclic
reversed-corner states. The shared corner diagram remains available. Use the proved strict-chain
normalization and its connected fibers to organize the remaining states;
their representatives are not individual components. Corner-long pairings
alone already fail lower-diagram reconstruction in the known four-vertex tree
component, as proved in the exact HRV-difference note. Do not freeze the
ordinary residual and try to prove a period assertion already contradicted
by the diagnostic. The corner,
forest, winding and aggregate refinements remain available as tools and solved
correction terms. Reuse the shared Rust LLT/HRV and flip tools before adding
computation; capability audits and missing maintained interfaces are in the
handoff.
