# VerticalStripLLT handoff

## Active implementation — P0/P2/P3/P4 complete, P1/P5 partial

The terminal-clique connectivity theorem is verified and pushed in `f08d1a5`.
The next increment verifies the incoming sweep and conditional core-path lift
for last-clique inheritance. P0/P2/P3/P4 are complete; P1/P5 remain partial;
P6--P10 remain open. The independent diagram formalization and illustrated
circular/ordinary draft are unfinished. The full goal is unchanged.

Primary owns all `DiagramProof/` sources, `DiagramProofVerification.lean`,
this handoff, the formalization plan and the restriction-consolidation suggestion,
and retains the sole serialized build slot. All subagent ownership has returned.
Terra supplied `LastCliquePaths` and `LastCliqueSweep`; Luna supplied
`LastCliqueEmbedding`; `semantic_extract` supplied `InducedRestriction`.
Primary wrote `InducedDiagram` and `LastCliqueLift`, integrated all candidates,
and verified every module locally. Terra independently approved the contracts
and the exact proved/unfinished boundary. No compiler, remote task or subagent
remains active. Historical proof-note prefixes and unrelated ownership remain
unchanged.

### Current P1/P5 increment — last-clique core interfaces

- `lastCliqueEmbed` enumerates the nonconvex core `{v | v ≤ c} ∪ {e}` with
  its original order and exact image.
- `InducedDiagram.inducedUndecorated` realizes the natural edges induced on
  any increasing nonempty vertex list. The edge map is injective with exact
  endpoints and range. Its strict set is explicitly empty: this is not yet
  the inherited decorated core.
- `InducedRestriction` constructs actual restriction and extension maps under
  explicit natural and strict edge correspondences. Extension preserves every
  exterior edge; extending the restriction recovers the source exactly.
- `LastCliquePaths` proves that, when no omitted vertex has an edge into `e`,
  forward paths with core endpoints stay in the core. Reachability and all
  cover tests therefore restrict exactly despite the nonconvex image.
- `exists_lastCliqueSweep` supplies an actual flip path, the exact incoming
  sweep endpoint relation, absence of gap-to-`e` edges, and unchanged core
  selection. `induced_lift_reachable_of_last_gap` then lifts any actual core
  path with this swept exterior fixed, deriving all intermediate cover tests.

Still open: construct the decorated induced core with inherited maximal
corners; transport corner-family, good-edge, common-cover, anchor, connectedness
and count data; restore the original exterior after changing the core. The
lift endpoint retains the SWEPT exterior. Do not reverse the old sweep trace
after the core changes. Restore the recorded edges in increasing order using
the core anchor's pendant last-corner tail. Last-clique inheritance is not yet
proved.

The read-only local-capacity audit also confirmed that the final rearrangement
must count only terminal copies in the last clique plus the crossing-slide
copy `ba`. Copies elsewhere stay fixed and do not count toward capacity.
The terminal-star tree edges lie in this mutable pool: the tree is required
only at endpoints, not throughout the packing paths. Existing
`RepresentativePacking`, `fixed_label_connectivity`, and the noninjective
count descent provide the finite interfaces; actual local paths remain to
be assembled.

### Verified P5 checkpoint `f08d1a5` — terminal-clique connectivity

- `TerminalCapacity` realizes every distinct terminal pair by a good terminal
  copy and proves positive capacity. `OccupancySupport` identifies the exact
  graph after a unit transfer: the donor remains precisely when another copy
  remains, and the receiver is inserted.
- `RepairedTerminalTransfer.exists_terminal_transfer` uses the locally verified
  Aristotle repair theorem. An absent temporary class has positive capacity;
  two actual direct transfers through that class compose to the required
  occupancy change, with the temporary count restored.
- `TerminalReceiver` chooses a deficit receiver preserving connected support.
  For a single-copy bridge it uses a reconnecting edge from the target graph.
  `OccupancyCounts` proves the total count identity, fixed diagonal counts,
  capacity bounds, and realization of differing classes by terminal copies.
- `OccupancyTransfers.reflTransGen_of_occupancy_descent_of_equal_counts` closes
  finite deficit descent with an actual equal-count path. The earlier
  injectivity-based interface remains a wrapper; occupancy is not assumed
  injective on anchors. `EqualSumCounts` supplies a surplus and a deficit.
- `TerminalConnectivity.anchors_connected_of_total_last_clique` connects actual
  connected anchors of equal total size when all chain terminals lie in the
  last clique. `commonCover_connected_of_total_last_clique` adds preparation
  and its reverse, giving the analogous result for common-cover states.

The direct transfer from `2e8f9ff` uses terminal packing and the complete-clique
path with exact exterior and exact selected-to-vacant exchange. The repaired
transfer and descent now discharge its former application obligations.
Last-/first-clique inheritance is still open. These are actual path theorems;
no general signed recurrence or semantic expansion is claimed yet.

### Earlier P5 checkpoints — packing and graph repair

Packing and descent helpers were pushed in `6f16377`; the Aristotle graph
repair was locally verified and pushed in `ea5d895`.

Aristotle project `515b9f61-1e1a-43bf-99b7-9e05cbff2124`, task
`84ef24e0-68a0-41fa-becb-c58e46b183d6`, is **COMPLETE** and returned a proof
candidate for the exact one-temporary-edge repair lemma, without extra
hypotheses. Terra ported `TerminalRepair.lean` build-free, primary verified it
under local Lean 4.34.0 with the narrow graph import, and `semantic_extract`
independently approved its contract and proof. The exact requested theorem is
now locally proved. It does not require finiteness or a separate three-vertex
hypothesis. The caller still supplies positive capacity for every terminal pair
using `exists_terminalEdge_of_last_clique`.
[The ledger](docs/ARISTOTLE.md) records the exact target and external directory.
The final theorem passes the local axiom and independent-import guards.

### Earlier P5 increment — terminal copies and packing

- `LabelPacking` constructs subsets with prescribed per-label counts between
  a required subset and an allowed pool. `RepresentativePacking` specializes
  it to one representative per occupied class, omitting a specified receiver
  whose class has a vacancy. All capacity bounds are derived internally.
- `TerminalClique` proves terminal copies are good non-corner edges, unique
  in their classes, and have labels distinct from retained corners. When
  all chain terminals lie in the last clique, its selected edges are exactly
  the last corner and selected terminal copies.
- `TerminalPacking.exists_terminal_packing` returns an actual anchor and an
  actual flip path with unchanged occupancies. Exactly the occupied terminal
  copies other than the receiver are selected at the endpoint.
- `ConnectedExchange.exists_reconnecting_edge` finds a receiver in a connected
  target across a deleted bridge. The receiver is absent from the source.
  `exists_connected_edge_exchange` handles equal-size connected graphs too.
- `OccupancyTransfers.reflTransGen_of_occupancy_descent` proves termination of
  exact surplus-to-deficit unit transfers, deriving sum preservation and strict
  decrease of the total deficit. The current increment supplies the actual
  transfer hypothesis; arbitrary transfers are not assumed to preserve
  connectivity.
- `TerminalRepair.one_temporary_edge_repair`, from the Aristotle candidate,
  realizes the exact graph statement: either both direct-transfer tests hold,
  or an absent third pair makes them hold for both consecutive transfers.
  The Boolean distinguishes whether the donor retains another copy.

### Earlier P5 increment — separators and removable edges

The [short separator proof](docs/proofs/COMPONENT_CHAIN_SEPARATOR_LEMMA.md)
records a simplification for the later draft. In a connected ordinary
natural graph with no articulation, every edge of length one or two is
natural. For `n≥3`, no corner chain contains consecutive vertices. Deleting
one chain leaves paths with gaps of at most two. Replacing natural edges
by good paths preserves avoidance of that chain.

- `NaturalSeparators` proves the short-edge consequence of connectedness
  after each vertex deletion, and the converse connectivity statements.
- `IntervalDeletion` supplies the finite path after deleting a set with
  no consecutive vertices; `ChainSeparators` specializes it to retained
  corner chains, for any `CornerFamily` containing the strict edges.
- `QuotientSeparators` proves the induced chain quotient remains connected
  after deletion of any terminal, including the required nonemptiness.
- `RemovableGoodEdges` connects the endpoints of a good non-corner edge
  around that edge through a third chain. It proves actual graph deletion
  preserves connectedness. `exists_third_terminal` gets the third chain
  from the hypothesis that the terminal subtype has cardinality at least 3.
- `exists_connected_anchor_card_avoiding_of_no_articulation` constructs an
  actual connected anchor omitting that edge at every size `n≤k+1` and
  `k+1≤|A*|`. This discharges the previously explicit deletion-connectedness
  hypothesis in the no-articulation case with at least three chains.

The `n≥3` and third-chain qualifications are retained. The two-chain base
is separate. These are graph paths and actual anchor-existence results;
terminal-clique transfers are now verified; component inheritance is unfinished.
No coloring or HRV contraction identity is asserted.

### Verified P5 checkpoints `584d931` / `e45e107` — contraction and sizes

- `ChainQuotient` uses the subtype of actual chain terminals, retaining
  isolated chains. Good copies induce exactly all natural quotient
  adjacencies. Contraction preserves every weak block for edge selections
  containing the retained corners, including actual orientations.
- `GoodEdgeConnectivity` replaces each natural edge by a weak path of good
  edges. The full good-edge and natural graphs have the same weak blocks.
- `CornerForest` proves retained-corner acyclicity. Its small general lemma
  needs only forwardness and unique predecessors: rotate a hypothetical
  cycle to its greatest vertex and compare its two incoming neighbors.
- `EdgeSetGraph` identifies a finite set of natural edges with its simple
  graph, preserves edge counts exactly, and reconstructs any spanning
  subgraph by filtering the original edge set.
- `AnchorSizes.exists_connected_anchor_card_iff` gives actual connected
  anchors of exactly the feasible sizes `n ≤ k+1` and `k ≤ |A*|` when
  `n>0` and the natural graph is connected. Every such anchor retains the
  corner family and therefore has all its corners covering.
- `exists_connected_anchor_card_avoiding` also omits a specified good
  non-corner edge, assuming its deletion leaves the full good-edge graph
  connected and `k+1 ≤ |A*|`. This supplies an actual orientation with
  exact count and absence. The separator result above supplies its deletion
  hypothesis when the natural graph has no articulation and has at least
  three retained corner chains.

These results hold for any retained corner family containing the strict
edges. The quotient is for connectivity; no coloring or HRV contraction
identity is asserted. Terminal-clique transfers and last-/first-clique
inheritance remain unfinished.

The independent component theorem is unfinished. The active goal also
requires a new illustrated draft combining the circular e-expansion and the
ordinary diagram-based component proof in the authors' style; writing has
not started. No old word/scan proof or fundamental-basis route is imported.

The user explicitly invoked the
[combinatorics paper-writing skill](/home/dev/.codex/skills/combinatorics-paper-writing/SKILL.md).
Primary read it and its notation/author-style references. The user also
asked us not to invent terminology without strong motivation. Use established
terms or state the condition itself, follow Robin and the author's diagram
reasoning, and keep implementation/audit details out of the manuscript.
No fundamental-basis or old word/scan argument is used.

### Verified P4 checkpoint `46107c6` — local complete blocks

- `CliqueEdges` proves that every ordered pair of vertices inside a natural
  edge is itself natural, including pairs touching either endpoint.
- `BlockPaths` proves path closure for updated relations with fixed exterior
  and weak-reachability restriction for an image closed under both ends of
  the source relation. No order-convexity of the selected block is assumed.
- `CliqueRestriction` builds the actual complete restriction and the exact
  ambient extension. Core paths lift in `D.undecorated`; existing exact
  marking transport recovers actual orientations and flips in `D`.
  `clique_lift_core_reachable` supplies the actual endpoint with exact
  inside and outside selections, including the original strict markings.
- `CompleteBlock.clique_reachable_of_block` connects two configurations of
  one selected weak block inside a natural clique. The source image is
  exactly one induced weak block; the target core is connected; both
  extreme edges cover; the local selected counts agree; and all exterior
  selected edges agree. Every ambient cover test is derived from source
  block closure, not assumed as an extra unresolved interface.
- `CliquePaths.clique_lift_core_of_block` lifts any actual complete-core
  endpoint. `clique_exists_reachable_of_block` forces reachability between
  an ordered pair in the chosen block, returning exact endpoint exterior.
  These are path and endpoint statements, not whole-component equalities
  or claims that the extreme edge covers at all intermediate states.

Terra independently audited the geometry, path restriction, local theorem
and final endpoint interfaces. All reviews passed. P4 is complete under
its plan's contracts. P5's star/anchor constructions must still supply the
explicit target connectedness, extreme covers, local count and exterior
conditions; those constructions are not claimed here.

P4's earlier checked obligations are: `ForestExtension` (feasible connected
sizes and removable-edge avoidance), `SubsetBands` / `OverlappingPositions`
(subset and sector connectivity), `TwoChainBase.commonCover_connected_of_two_terminals`,
`CompleteConnectivity.complete_reachable` and its strict-corner version,
and `ReachabilityForcing` with adjacent-edge and lower-interval consequences.
The [path implementation history](docs/archive/diagram-reachability-implementation.md)
preserves the detailed `c1e2e8e`, `7b9f5de`, `7d76087` records; the
[earlier complete-diagram history](docs/archive/diagram-complete-clique-implementation.md)
retains CC1--CC6 and interval/chord checkpoints.

### Earlier verified interfaces

- `9d8c4bc`: independent imports, full selections/layers, finite/lifted covers
  and weak-block invariance; affected old consumers compile.
- `3bbb1e4`: source-cover short flips and exact corner marking of whole
  components, both directions/surjectivity, HRV and coloring values.
- `15ec74b`: actual state/component marked K/E bridges and both marked diamonds.
- `bb86b82`: convex restriction and fixed-exterior actual core path lifting.
  The lift is injective, NOT a whole-component equivalence.
- `98f226c`: marked-E fibre signature by nonempty sizes, increasing fibre
  bijections, sink-order relabelings and closure invariance. P0/P2 complete.
- `0871d38`: restored crossing slide for `a<b<c<d`, replacing exactly `ab`
  by `cd` with only `ac,bd` covering initially. User-authorized Claude audit
  led to right-before-left restoration through the shared replay interface.
- `da01755`: ordered corner-chain preparation by actual flips, retaining
  already-good edges, component, total selected count and weak blocks.
- `03c05c4`: P3 complete. Auxiliary short-edge/copy geometry, neighboring and
  arbitrary parallel exchanges, and anchor connectivity at equal occupancies.
  Exact endpoint selection is `A-e+f`; every other edge is restored.
- `8fbbe84`: two-terminal-chain connectivity, forest extension to all feasible
  sizes, removable-edge avoidance, connected-position subset exchanges,
  subset bands and additive feasible-sector connectivity.

The sorted `chainPair` labels all non-retained auxiliary-path positions;
ordered `copyLabel` labels actual anchor copies. Do not conflate them.
Occupancy is NOT asserted invariant on a whole component. Equal occupancies
are a sufficient connectivity condition for anchors. The terminal packing result supplies the last-clique representatives
when the receiver class has a vacancy. Families may retain any maximal corners containing the
strict edges; specialize to `allCorners D` for the proof note's multigraph H.

P1 remains partial: other induced-core geometry and order reversal remain.
The complete-interval and selected-clique-block path lifts are verified.
P4 is complete. P5 is partial; P6--P10 remain open. General component recurrences, endpoint
attachment and the final independent theorem are NOT yet Lean-proved by
this route. The mathematical diagram proof is complete.

### Verification and next step

Focused builds of all new modules and the verification import targets pass
without source warnings. All 438 queries in `DiagramProofVerification.lean`
use only `propext`, `Classical.choice`, `Quot.sound` (or none). The independent
import closure contains 203 project files including verification and excludes
the old word/scan/expansion routes. Source guards (including no `native_decide`),
100-column and whitespace checks pass. Current logs are
`p5-last-core-build.log`, `p5-last-core-axioms.log` and
`p5-last-core-imports.txt`. The terminal-clique checkpoint had
408 queries/197 project files (`p5-terminal-complete-*`). The direct-transfer checkpoint had
393 queries/190 project files (`p5-direct-*`). The repair checkpoint had 374 queries/183 project
files (`p5-repair-*`). The preceding packing checkpoint had 373 queries/182
project files (`p5-terminal-*`). The separator checkpoint had 359 queries/176
project files (`p5-separator-*`). Prior P5 checkpoints have
323 queries/168 project files (`p5-connectivity-*`) and
340 queries/171 project files (`p5-sizes-*`). No compiler, remote task or
subagent remains running.

No broad build, dependency update or mathematical computation ran. Aristotle
was used for the exact graph repair lemma, as requested.
Only primary invokes `lake-workspace`. Lean MCP remains
rooted at RealRooted, so local compiler diagnostics are used. The wrapper's
existing package-path manifest warning remains unchanged.

Next: finish the decorated core geometry and exact exterior restoration, then
assemble P5's four last-clique inheritance steps: make the selected core
connected; sweep, lift and restore;
reach the fixed spanning tree; rearrange extra positions through the shared
edge. The written proof starts near line 4298 of
`COMPONENT_NN_REDISTRIBUTION.md`. Its last step needs the terminal-clique
argument restricted to the stated local pool: same-pair copies elsewhere are
held fixed and must not count toward local capacity. The terminal-clique base,
good-edge connectivity, feasible sizes and removable-edge consequence are
proved; do not repeat them. P1's order reversal is needed before first-clique
inheritance. No general interval-graph library was introduced. Surviving
ambient corners remain corners under arbitrary increasing restriction; the
last-clique hypotheses are needed for the converse, excluding new corners.
A corner-as-maximal-natural-interval characterization would support this
geometry; the current induced diagram does not yet prove it.

For clique reachability, use `clique_lift_core_of_block` to transport the
actual core endpoint and its selected relation. The general lower-interval
preservation theorem remains `ReachabilityForcing.exists_reachable_preserving_lower_weakReach`;
transport its one-way connection guarantee through the concrete core image
when needed. Do not claim equality of induced blocks during hull shrinking.
The written uses are in `COMPONENT_NN_REDISTRIBUTION.md` around 4081--4089
and 4334--4342. P1's remaining induced-core interfaces and P5--P10 are open.
The optional later consolidation of the prefix/general restriction APIs is
recorded in `suggestions/complete-subdiagram-consolidation.md`.

The required independent Astra architecture review was completed before
implementation. Earlier verification logs remain under
`/lake-cache/ai-projects/requests/VerticalStripLLT/diagram-formalization/`.
`p3-packing-*` records 107 axiom checks/106 project files;
`p4-helpers-*` records 120 axiom checks/111 project files;
`p4-prefix-*` records 148 axiom checks/121 project files;
`p4-chain-*` records 164 axiom checks/124 project files;
`p4-interval-*` records 195 axiom checks/131 project files;
`p4-rearrangement-*` records 222 axiom checks/138 project files;
`p4-outer-*` records 234 axiom checks/141 project files;
`p4-chord-step-*` records 244 axiom checks/147 project files;
`p4-complete-*` records 262 axiom checks/152 project files;
`p4-interval-reach-*` records 280 axiom checks/156 project files;
`p4-forcing-*` records 297 axiom checks/161 project files;
`p4-block-*` records 315 axiom checks/166 project files.

## Detailed formalization plan — completed before implementation

The user requested a detailed formalization plan after cleanup checkpoint
`61ff6f8`. The checkout was clean at that HEAD. Read the
[detailed plan](docs/COMPONENT_DIAGRAM_FORMALIZATION_PLAN.md): exact semantic
target, existing source interfaces, proposed modules, theorem obligations,
P0--P10 checkpoints, dependencies, acceptance criteria and focused checks.
At that planning checkpoint, all new Lean checkpoints were unimplemented.
The active implementation status above supersedes that historical status.
The mathematical proof remains complete.

Reuse `Circular.Diagram` with forwardness and actual orientations/flips/
components, keeping vertex-count path induction separate from the final
valuation induction. The review identified necessary small extractions from
`ComponentScalars` and `ForwardHRV` to keep the new imports independent of
word machinery. Component partitioning should also avoid importing
`ComponentCoefficient`. Marked E uses a fibre-coloring relation, not a new
natural diagram. Reduction terms are whole components on the same vertex
set, with common integer coefficients, forwardness and strict decrease.

Independent Astra reviewer `diagram_audit` approved the detailed architecture
after two ordering clarifications: auxiliary short-edge/copy-order geometry
is proved in P3 before the two-chain base; local target-decrease lemmas are
proved in P8 before reduction certificates and reused by P9. Its review
also covers endpoint semantics, corner validity, core lifting and component
multiplicities. It owns no files and is finished.

Primary owns the plan and this handoff. Only these two documentation files
change in the planning checkpoint. Source/interface/import inspection,
27 plan links and `git diff --check` pass. Existing proof notes and Lean
sources are unchanged. No builds or mathematical experiments ran; Lean MCP
is still rooted at RealRooted and was not used. No verification jobs remain.
At implementation start, recheck shared build ownership and begin P0/P1;
the plan proposes early crossing-slide and marked-semantics checks before
the longer path inductions.

## Cleanup audit before formalization — complete

The user requested one cleanup/optimization audit of the completed diagram
proof before Lean formalization. Starting HEAD is `8ccde0e`; the checkout
was clean. Read the [audit and extracted lemmas](docs/proofs/COMPONENT_DIAGRAM_AUDIT.md)
alongside the [assembled proof](docs/proofs/COMPONENT_DIAGRAM_COMPLETION.md).

The mathematical conclusion remains complete. The audit found no gap in
the reviewed completion argument. The assembled proof now chooses its
initial-path/first-block prefix directly from the area sequence: internal
v is an articulation iff a_(v+1)=1. This avoids general block-decomposition
infrastructure for the final recurrence. We also state the required
re-marking before alternating deletion and distinguish total selected-edge
layers from the original normal-edge exponent.

The audit note extracts proved finite forest-extension and subset-band
lemmas, the area-prefix lemma, component isolation by subtraction, and
attachment from a right-marked equality. It records the proposed two-stage
formalization (vertex-count path induction, then valuation induction),
existing Lean interfaces and import-boundary cautions. These are paper
lemmas and implementation guidance; no new Lean formalization is claimed.

Primary owns this handoff, the assembled completion, the new audit note,
and `suggestions/diagram-proof-import-boundary.md`. Existing chronological
proof-note prefixes remain unchanged. Independent Astra reviewer
`diagram_audit` owns no files; it reviewed recurrence, attachment, first-drop
and induction interfaces and approved the final cleanup and extracted lemmas.
This supplies the independent decomposition review required by the project
guide. Primary audited the path-induction side. No builds or mathematical
computations ran; no finite-check replay is claimed for this documentation
audit. Formalization remains the next implementation task.

Final cleanup checks: independent review approved the edited proof and
extracted statements; 21 local links and six Lean file breadcrumbs resolve;
the NN, DN, endpoint and coverage historical files are byte-for-byte
unchanged from `8ccde0e`; `git diff --check` passes. Only the four owned
documentation files listed above enter this checkpoint on `main`.
The reviewer is finished and no verification/build jobs remain running.

## Completed — ordinary component expansion by diagram recurrences

The mathematical goal is complete. The general first-drop NN and forward DN
recurrences now collect whole components with the same signed coefficients
for K and E. DD/ND inherit the same whole component by the proved unmarking
step. The resulting decreasing induction proves the general component
e-expansion for ordinary, non-circular Motzkin/Dyck-path diagrams.

Read the [assembled proof](docs/proofs/COMPONENT_DIAGRAM_COMPLETION.md).
It is independent of the separate word-functional proof and uses no
fundamental-basis calculation. This is a mathematical proof; no new Lean
formalization is claimed. The next requested step is preparation for
formalization through the cleanup audit recorded above.

### What closes the last gap

The new [initial-vertex inheritance](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#initial-vertex-inheritance-through-extra-edge-sectors)
applies when the first corner tails are 0,1. Delete vertex 0. The core loses
exactly the first corner and all remaining chain terminals stay unchanged.
A prepared source state is a core anchor, the retained corner 0a, and a
subset of good extra edges 0v. Each extra has a matching good core edge
ah_v. Their proved crossing slide restores arbitrary exterior.

First slide extras into the core until it is connected. For a fixed extra
set S, all same-size core anchors connect by the smaller-core theorem;
core flips lift because no forward core path can visit 0. Neighboring
extra sets connect by a crossing slide through a core witness omitting
its matching edge. Such witnesses exist when that edge can be removed
from the full good core without disconnecting it. The feasible extra
sets form a connected band of subset sizes.

This supplies a decreasing vertex-count induction for EVERY connected
ordinary natural graph without articulation. If the second corner tail
is greater than 1, use order-dual last-clique inheritance to remove the
initial private vertices. Otherwise use initial-vertex inheritance. Both
cores have fewer vertices and no articulation. Outside the complete and
two-chain bases, the good core quotient has at least three vertices and
no articulation, hence no bridge: every matching edge is removable.

Arbitrary initial paths preserve uniqueness by forced pendant deletion.
For a general connected non-path source, take the prefix consisting of
the initial path and first nontrivial block. It has the required uniqueness.
Use its right-marked full-layer recurrence and attach the arbitrary whole
component to its right. All products are whole; no expansion for the
attachment is assumed. Its first-drop contact is the full source's first
drop. Thus articulations do not require false global uniqueness at a
fixed total edge count or an unproved two-end attachment assertion.

### Whole-component recurrence and final theorem

For the unique connected common-cover component C in prefix layer k,
complete that source layer. Every extra source component reduces
independently by an absent corner, weak-block reordering, or alternating
corner deletion. Subtract these smaller expressions from the full-layer
NN or DN identity. All targets and correction terms are whole components.
The same integer coefficients work for K and E.

The first-drop coverage theorem and DD/ND inheritance supply the contact;
every final output decreases (n, natural area, area moment). Saturated
paths and disjoint natural components give the bases/factorization.
Consequently K(C)=sum_(A in C) e_lambda(A) for every ordinary component,
and restoring its constant normal-edge weight gives t^k(C) times this sum.

The construction chooses the required first-drop contact. It does not
claim a one-to-one correspondence of source and target components, nor
that the uncorrected local image is already a union of whole components.
Those stronger assertions were never needed and earlier counterexamples
remain valid. All former general NN/DN, higher-clique and three-corner
open statuses in the chronological notes are superseded by this proof.

## Verified evidence

All four final source-identical replays passed with exit 0 and empty stderr.
Frozen sources, commands, logs and hashes:
`/lake-cache/ai-projects/requests/VerticalStripLLT/general-diagram-completion-20260930/`.

- Structural audit: all 6916 connected ordinary diagrams on 3..10 vertices,
  including all 2055 without articulation. The decreasing branches are
  8 complete, 618 initial-clique trims, 7 small-chain bases and 1422
  initial-vertex cases. All 6908 non-path prefix/first-drop choices pass.
  Also 1308 actual crossing slides, 6238 flips, up to four extras.
- Initial-vertex audit: all 37 applicable diagrams through seven vertices,
  plus the fourth power of an eight-vertex path (three extras). All 13474
  connected anchors, 1427 core joins / 3944 flips, 200 sector bands and
  214 sector links / 902 flips pass. Exact lift comparison covers 344211
  states and 1420896 directed actual-flip incidences, including states
  where other retained corners are redundant.
- General first-drop audit: 41 feasible layers in seven fixtures, covering
  NN, DN, ND-to-NN, DD-to-DN, three-/four-corner sources and an initial
  path prefix. 20274 survivor states; 2089 whole targets / 42054 states;
  275 block corrections / 1943 states; 948 absent-corner corrections /
  18051 states; 287 alternating sources / 1786 states, giving 6967 whole
  deletion terms. Signed marked HRV identities, whole-output and strict
  induction-order checks pass (5429 positive terms, 4850 negative terms,
  24358 redundancy witnesses).
- Right-attachment audit: all six initial-prefix layers with the two-state
  triangle attached to every term. All 3555 product-component checks pass,
  with 46844 product state visits and exact endpoint fibre data.

These are checks of the stated finite scopes. The unbounded proof is the
written path induction, sector argument, component correction and attachment
argument; it is not extrapolated from enumeration. No computational coloring
identity or basis calculation is claimed. Both K and E identities follow
from the proved common local diagrams and marked maps.

The existing 20000-state component guard is unchanged. Cargo runs were
serialized and reduced-priority; no Lean/Lake build ran. The maintained
Rust workspace is clean and unchanged at
`24559ad73d209077a58eef08278c425301468cdc`. The external consumer reuses the
existing Graph/Poset, actual-flip, crossing-slide and component-correction
APIs. Python only handled files, commands and diagnostic log summaries.

## Ownership, scope and recovery

Primary owns this handoff, `docs/proofs/COMPONENT_DIAGRAM_COMPLETION.md`, the
recurrence outline, APPEND-ONLY continuations of NN redistribution and DN
joint-repair notes, the authorized endpoint/source-addition continuations,
handoff archives and existing external consumers under
`/lake-cache/ai-projects/requests/VerticalStripLLT/diamond-exploration/hrv-bridge/`.
Preserve other ownership and the proof-note prefixes at `a3d076b`.

The original completion used no extra worker/subagent/Claude consultation,
manuscript TeX/PDF/Overleaf edit, maintained Rust edit or Lean build. The
subsequent cleanup's read-only review is recorded above. No account/profile/model
assignment changed. Runtime tools, `codex mcp list`, Cargo metadata, the
Rust guide and relevant existing APIs were inspected. Lean MCP remains rooted
at RealRooted and was unused. There is no external blocker or unfinished
requirement of this mathematical goal.

The [previous handoff](docs/archive/component-handoff-before-general-completion-20260930.md)
preserves `49cb610` with relative links relocated. All earlier proofs and
counterexamples remain intact. The outline now routes to the assembled
completion; dated notes, including the former conditional coverage theorem,
retain their historical wording and should be read with that completion.
The new proof discharges the coverage theorem's explicit NN/DN hypothesis.

The replacement began at account-swap `2511182`. Recent proof checkpoints
were `cf5451e` (pendant inheritance) and `d7da9ab` (last-clique inheritance),
followed by metadata `49cb610`. Completion proof checkpoint `a3d076b` is
committed and pushed to `origin/main`. All four frozen replays, receipt
hashes, preserved prefixes, historical outline body, relocated archive,
new file/heading links, ownership and whitespace checks pass. No verification
jobs remain running. The completion audit verifies the full ordinary scope,
whole smaller outputs, both valuations, well-founded induction and shifted
elementary positivity; no required work remains on this mathematical goal.
