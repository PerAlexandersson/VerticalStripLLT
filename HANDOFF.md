# VerticalStripLLT handoff

## Active implementation — P0/P2/P3 complete, P1/P4 partial

Pushed checkpoint `03c05c4`, based on clean `da01755`, completes P3:
auxiliary short-edge paths, ordered good copies, and unrestricted parallel
rearrangement. `CornerFamily.anchors_connected_of_occupancy` connects any
two anchors with the same per-pair counts by actual flips. Each elementary
exchange has exact endpoint selection `A - e + f`; all other edges are
restored. The full independent component theorem remains unfinished. The active goal
also requires a new illustrated draft after formalization, combining the
circular e-expansion and the ordinary diagram-based component proof in the
authors' style; that writing stage has not started.

Primary owns all `VerticalStripLLT/Components/DiagramProof/` files,
`DiagramProofVerification.lean`, this handoff and plan-status updates.
Primary alone runs Lean builds. Historical proof notes are untouched.
The user explicitly authorized several Luna/Terra agents; all have now
completed and released their lanes. No compiler or consultant is left running
at the checkpoint.

- Luna `two_chain_base` supplied `TwoChainBase.lean`. Primary checked the
  proof after one repair round and removed deprecated syntax. Its later
  read-only complete-clique API audit informs the next-step notes below.
- Terra `copy_audit` found no issue in the copy/packing contracts, then supplied
  `SubsetBands.lean`. Primary checked it after two textual correction rounds.
- Earlier Luna `subset_paths` supplied `FiniteSubsetPaths.lean`. Primary
  adopted its draft, fixed it and completed fixed-label connectivity.

Current P4 verified increment, based on pushed `03c05c4`:

- `TwoChainBase.commonCover_connected_of_two_terminals`: common-cover states
  with the same total selected count connect if the corner terminal map has
  at most two values. Equal terminal values are allowed; connectedness of
  the selected graph is not an extra hypothesis. Uses preparation and the
  single-label anchor theorem; no component-valued formula is inferred.
- `ForestExtension`: extend any required forest in a finite connected graph
  to every feasible connected spanning edge count. If a nonrequired edge
  can be deleted without disconnecting the graph, all sizes up to one less
  than the full edge count have such an extension omitting it. Reuses
  Mathlib's spanning-tree extension, with additive cardinality bounds.
- `OverlappingPositions`: exact exchanges on any connected position relation
  give fixed-size state connectivity; two overlapping covering position sets
  provide that relation. This is an abstract finite path helper, not yet
  the diagram-specific interval opening/closing construction.
- `SubsetBands`: single-element insertion/deletion paths inside a cardinality
  interval of positive width, plus the empty/full singleton extremes. No
  assertion of connectivity for an interior one-level band.
- `SectorPaths.feasibleSector_connected`: the sector formulation with
  `∃ t, r ≤ t ∧ t ≤ m ∧ t + 1 + S.card = s`. It follows from the band theorem
  when `r < m` or the sector universe is empty. Natural subtraction is
  confined to a proved equivalence; the public interface stays additive.

P3 source and exact contracts:

- `CopyGeometry`: maximal-corner boundary geometry, unique edge with given
  tail and head-chain, and separated increasing endpoints for parallel copies.
- `CopyPaths`: unique short-link predecessor/successor, increasing tails,
  next good copy, path through all good copies of an ordered terminal pair,
  and the last copy starting at the smaller terminal.
- `ShortPathClasses`: two non-retained natural edges are in the same auxiliary
  short-link component iff their unordered terminal pairs agree.
- `ParallelMoves`: both neighboring-copy directions are actual restored slides.
- `FiniteSubsetPaths`: exact subset exchange along an auxiliary path, then
  connectivity from fixed label cardinalities, by decreasing set difference.
- `ParallelPacking`: arbitrary parallel-copy exchange and anchor connectivity
  with a fixed occupancy vector. Ordered terminal pairs label full selections;
  diagonal entries count fixed retained corners and are never exchanged.

The sorted `chainPair` labels ALL non-retained auxiliary-path positions,
including terminal-decreasing ones. The ordered `copyLabel` labels actual
anchor copies; its movable positions strictly increase terminal labels.
Do not conflate these notions. Theorems allow arbitrary retained maximal
corner families containing the original strict edges; specialize to
`allCorners D` when identifying the proof note's all-corner multigraph H.
No canonical highest-position packing or capacity formula is claimed.
Occupancy is NOT asserted invariant on a whole component; equal occupancies
are a sufficient connectivity condition for anchors.

Verified implementation checkpoints:

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
  by `cd` with only `ac,bd` covering initially. Right restoration precedes
  left restoration; both reuse the same exact exchange/replay interface.
- `da01755`: full ordered corner-chain preparation. Every actual common-cover
  state reaches an anchor by actual flips, retaining already-good edges,
  component, total selected count and weak blocks. Temporary redundant
  corners are recovered after each chain sweep. No canonical-anchor claim.

P1 remains partial: specific induced-core geometry, swept nonconvex transport
and order reversal remain. P3 is complete at the plan's required interface.
P4 is partial: the two-chain base and some finite helpers are checked;
complete-clique paths, their local lift and reachability forcing remain.
P5--P10 remain open. General component recurrences, endpoint
attachment and the final independent theorem are NOT yet Lean-proved by
this route. The mathematical diagram proof remains complete. No old
word/scan proof or fundamental-basis argument is used.

Verification of the current P4 increment:

- Focused builds of `TwoChainBase`, `ForestExtension`, `OverlappingPositions`
  and `SectorPaths` (including `SubsetBands`) pass without source warnings.
  `DiagramProofVerification.lean` passes all 120 axiom queries, using only
  `propext`, `Classical.choice`, `Quot.sound` (or none).
- Independent import closure: 111 project files including verification;
  no old Word/Mountain/Scan/Cauchy, component-coefficient, old expansion,
  BlockExtractor or BlockCancellation route. Source guards, 100-column
  and whitespace checks pass.
- All builds were focused and serialized with `lake-workspace`. No broad
  build, dependency update, remote proof search or mathematical computation.
  Lean MCP remains rooted at RealRooted; local compiler diagnostics used.
  The wrapper's known package-path manifest warning remains unchanged.
- Logs under
  `/lake-cache/ai-projects/requests/VerticalStripLLT/diagram-formalization/`:
  `p4-helpers-build.log`, `p4-forest-build.log`, `p4-overlap-build.log`,
  `p4-sector-build.log`, `p4-helpers-axioms.log`, `p4-helpers-imports.txt`.
  P3 `p3-packing-*` logs retain 107 axiom checks and its 106-file closure.

Next concrete implementation: use `Diagram.ofIntervalRelation` with `<`
for a complete diagram, and expose canonical edges by endpoints. A designated
extreme corner requires at least two vertices; handle the one-vertex case
separately. Then formalize complete-chain normalization (CC1--CC2), interval
opening/closing (CC3), and chord rearrangement using `OverlappingPositions`.
Existing source-cover outgoing/incoming swaps, weak-block invariance,
forward HRV sink lemmas and `CoreExtension.lift_reachable` are available.
Do not assume the swept nonconvex core automatically satisfies the convex
lift contract. The selected-orientation/SimpleGraph bridge is also absent;
keep normalization in the forward relation unless that bridge is needed.
The four five-vertex paths in `COMPONENT_NN_REDISTRIBUTION.md` around 3628
are explicit paper certificates, still awaiting Lean actual-flip witnesses.
No arbitrary finite component enumeration is an assumption of the plan.

The user-authorized Claude refactor sweep was completed at `0871d38`.
Primary integrated its strongest suggestion: right-before-left restoration,
removing a special exterior transform and extra reference sweep. Trace-based
sweeps share replay proofs. Its uncompiled suggestions were not verification
evidence. The required independent Astra architecture review was completed
previously. Terra's current audit independently checked the new geometry and
packing contracts; primary's local Lean check remains authoritative.

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
