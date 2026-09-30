# VerticalStripLLT handoff

## Active implementation — P0/P2/P3 complete, P1/P4 partial

Continuation began clean at pushed `c1e2e8e`; the previous turn made
verified progress. The current increment proves the incoming-normalization
stage of reachability forcing, including exact induced weak-block and
exterior-edge preservation. Hasse-path hull shortening remains unfinished.

Primary owns all `DiagramProof/` files, `DiagramProofVerification.lean`, this
handoff and the formalization plan, and retains the sole serialized build
slot. Terra returned `UniqueIncomingPaths`; primary repaired, streamlined
and verified it. Primary wrote `RestrictedFlips`, `IncomingNormalization`
and `IntervalReachability`, and extended `IncomingFlip`. Terra independently
reviewed the new interfaces. Luna returned a read-only Hasse-path/API audit.
Both agents are finished; all current source is primary-owned. Historical
proof notes and unrelated ownership remain unchanged.

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

### Current P4 increment — reachability inside an interval

- `IncomingFlip.exists_reverseFlip_of_sourceCovers` supplies the incoming
  exchange as a reverse directed witness, with exact short-edge endpoints.
- `RestrictedFlips.DirectedFlipWithin` records that all three vertices of
  an actual directed flip lie in a specified set. Reverse paths of these
  flips are actual ambient flip paths. They fix every selected edge outside
  that induced set and preserve induced weak blocks in every containing set.
- `IncomingNormalization.exists_leftUnique_covers_within` repeatedly removes
  incoming cover forks inside the specified set. Each reverse flip strictly
  decreases `selectedTailSum`. Strict edges are retained by the actual
  orientation/flip interface. The global version is also proved.
- `UniqueIncomingPaths` proves that a left-unique relation gives common
  ancestors to weakly related vertices. Cover factorization then proves
  that a least vertex of a weak block reaches the whole block when incoming
  covers are unique. `eqvGen_relationCover_iff` extracts the reusable fact
  that replacing selected edges by cover paths preserves weak blocks.
- `IntervalReachability` proves exact convex restriction of paths and
  covers, including induced weak-block preservation under cover refinement.
  `exists_reachable_within_of_minimal` handles a least vertex of an induced
  weak block in any convex set. `exists_reachable_within_interval` specializes
  to a weak path already inside `[u,v]`, producing a state where `u` reaches
  `v` by actual flips confined to that interval.

Terra's independent audit found no gap in flip direction, termination,
preservation, minimality transport or interval semantics. These results
finish the normalization stage of the written reachability argument. They
DO NOT yet shrink an arbitrary Hasse path into its endpoint interval.

### Verified at `c1e2e8e` — complete-diagram connectivity

- `CoverCut.relationCover_of_cut` gives a sufficient cover test: the selected
  edge is the only edge allowed to cross a separating set. Its proof uses
  forward path intervals and applies to arbitrary linearly ordered vertices.
- `FiveVertexPaths` interprets the four written triple lists as actual flip
  paths. Every intermediate state is built from its full selected endpoint
  set. Each step checks the two source covers through finite separating-set
  conditions, then uses the proved incoming/outgoing flip constructor.
  All finite conditions and exact final pair sets are kernel-checked with
  `decide`; no native proof axiom or component enumeration is used.
- `FiveVertexBase` identifies the three possible chords `13,14,24`, proves
  exact endpoint equality with the actual chain states, and combines the
  four paths. `ThreePositionPaths` supplies the abstract eight-subset and
  cardinality case split. Normalization yields `complete_reachable_five`.
- `CompleteConnectivity.complete_reachable` proves, for every `n`, that two
  selected-connected states in `completeDiagram n`, each covering `0n` and
  having the same total selected-edge count, connect by actual flips.
  Strong induction combines `n <= 3`, the explicit `n = 4` base, and the
  interval/chord step for `n >= 5`. There is no remaining smaller-diagram
  assumption in this theorem.
- `complete_reachable_marked` proves the corresponding path in
  `completeCornerDiagram n hn`. The corner `0n` is strict at every state.
  The endpoint active-cover hypotheses are retained; coverhood at every
  intermediate state is not claimed.

Terra independently audited the separating-set interpretation, full endpoint
identities, four finite paths, three-position assembly, strong induction and
marked transport. No gap was found. This completes the complete-clique
connectivity part of P4, not the general ordinary component expansion.

The [implementation history](docs/archive/diagram-complete-clique-implementation.md)
preserves the earlier CC1--CC6, interval and chord checkpoints, including the
corrected intermediate-state issue. Its former unfinished statuses are
superseded here. No earlier mathematical proof-note prefix was changed.

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
are a sufficient connectivity condition for anchors. No canonical highest
packing is claimed. Families may retain any maximal corners containing the
strict edges; specialize to `allCorners D` for the proof note's multigraph H.

P1 remains partial: other induced-core geometry and order reversal remain;
the specific nonconvex complete-interval lift is now proved. P4 remains
partial: localizing the complete theorem to a selected weak block and
Hasse-path hull shortening remain. The incoming-normalization stage of
reachability forcing is now verified. P5--P10 remain open. General component
recurrences, endpoint attachment and the final independent theorem are NOT
yet Lean-proved by this route. The mathematical diagram proof is complete.

### Verification and next step

Focused builds of `IntervalReachability`, the affected complete-diagram
consumer and all verification imports pass without source warnings. All 280
queries in `DiagramProofVerification.lean` pass using only `propext`,
`Classical.choice`, `Quot.sound` (or none). The independent import closure
contains 156 project files including verification and excludes the old
word/scan/expansion routes. Source guards (including no `native_decide`),
100-column and whitespace checks pass. Logs are
`p4-interval-reach-build.log`, `p4-interval-reach-closure-build.log`,
`p4-interval-reach-axioms.log` and `p4-interval-reach-imports.txt` in the
directory below. No compiler or agent job remains running.

No broad build, dependency update, remote proof search or mathematical
computation ran. Only primary invokes `lake-workspace`. Lean MCP remains
rooted at RealRooted, so local compiler diagnostics are used. The wrapper's
existing package-path manifest warning remains unchanged.

Next: finish P4's Hasse-path hull shortening and local complete-block
interfaces.
The reachability proof is in `COMPONENT_NN_REDISTRIBUTION.md` around lines
1557--1595: take a Hasse path between two vertices in one selected weak
block, remove an internal largest/smallest vertex by an incoming/outgoing
cover flip, refine selected edges back to cover paths, and decrease the
containing label interval. The final incoming-fork normalization is now
`exists_reachable_within_interval`; its actual-flip conversion and induced
weak-block preservation are in `RestrictedFlips`.
Record preservation of selected edges internal to a retained lower interval
during upper-hull removal, and preservation of its weak blocks thereafter
(used around lines 4081--4089 and 4334--4342 for clique inheritance).
Do not claim the entire exterior stays fixed during hull shrinking. P1's
order-reversal/induced-core interfaces and P5--P10 remain unfinished.
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
`p4-complete-*` records 262 axiom checks/152 project files.

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
