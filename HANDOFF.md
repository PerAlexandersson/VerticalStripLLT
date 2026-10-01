# VerticalStripLLT handoff

## Active split — Claude owns Lean; Codex owns the writeup

Ownership transfer recorded 2026-10-01, after the two pending P6 modules
passed focused builds and all 649 axiom checks. The persistent Claude worker
`agent-verticalstri-motzki-c-001af720` may now take all `DiagramProof/` Lean
implementation, `DiagramProofVerification.lean`, and the **sole project build
slot**. Begin with issue #8 and continue the remaining diagram formalization.
Serialize builds with other Lean projects. Codex and its subagents will run
no further Lean builds or edit Lean sources after this release.

Codex retains `HANDOFF.md`, mathematical proof prose, formalization source maps,
`docs/drafts/`, figures and manuscript work. Claude should report durable status,
checks, commits and needed proof clarifications in `docs/LEAN_COORDINATION.md`
(new file owned by Claude); Codex will incorporate those reports here.
This transfer releases all earlier Codex source ownership below. All delegated
source tasks have returned. No local compiler or queued build remains active.

The Docker-side supervisor report/tail did not discover the persistent session;
a read-only tmux inspection confirmed Claude was preparing attachment files in
its scratchpad and waiting for this explicit transfer. No input guards were
bypassed. This paragraph is the durable release the worker was instructed to read.

P0–P5 are complete under their contracts; P6 is partial and P7–P10 are open.
The complete mathematical diagram proof and the independent Lean theorem
remain distinct. The older word/scan proof is not imported by this route.

### Writing progress after the transfer

Source/build release is pushed as `b78312c`. The independent issue #8 task
now records the new division. Claude's claim proposal and approximately
1,450 lines of scratchpad candidates remain unverified; its proposal is in
`suggestions/claude-right-attachment-claim.md` (Claude-owned). A read-only
pane inspection showed its bounded handoff watcher and an unsent user prompt;
Codex left the prompt untouched. A later inspection confirmed Claude has
started integrating the four `RightAttachment*.lean` sources and running
focused builds. Those untracked source files belong to Claude; their checks
are ongoing and no attachment theorem is yet recorded as complete.

Writing checkpoint `52afc77` is pushed. Issue #8 was read back and matches
the tracked task after conversion of relative links to repository links.
The new circular section `docs/drafts/CIRCULAR_E_EXPANSION.md` follows the
checked aggregate proof. It separately treats the terminal-contact reduction
(factor `1+q`, doubled area down six) and interior column reversal; the
external manuscript had grouped their geometry. The rank definition is the
sum of proper-ancestor counts times strict-edge lengths, exactly Lean's
`strictRank`. A new column-reversal SVG was rendered in the external cache
and visually inspected. The local boundary checks and DD-contact elimination
remain compressed, and the combined manuscript remains unfinished.
Independent review approved the terminal-pair count, both contact branches,
and the exact rank definition. Local Markdown links and SVG XML pass; issue
#8 was refreshed to match the tracked task.

### Latest verified P6 checkpoint

`lastClique_induced_short_naturalEdges` in `LastCliqueNaturalEdges` preserves
short natural edges in the canonical core on `0,...,c,e`; interior pairs
lift identically, and final pairs lie inside the given crossing edge.
`CornerFamily.commonCover_connected_of_terminal_card_le_two` derives the
existing two-terminal base from the bound on terminal fixed points.
Terra supplied the former and Luna the latter; Codex repaired and verified
both. They remain auxiliary lemmas: the global induction is unfinished.

Checks: 649 axiom queries in exact order, only standard axioms; independent
closure 283 project files; 209 DiagramProof modules pass source/100-column
guards. Logs in the external request directory: `p6-core-short-build.log`,
`p6-two-chain-card-build.log`, `p6-core-geometry-axioms.log`, and
`p6-core-geometry-imports.txt`. No broad build or dependency update ran.

Next P6 integration: preserve short edges under reversal, select the first two
corners (or complete base), use the double reversal of `lastCliqueEmbed` for
the first-clique branch, prove its size decrease, and assemble strong induction.
The initial-vertex branch already discharges matching-edge removability.
For an arbitrary complete natural diagram, audit an identity-embedding bridge
through `cliqueRestrict`/`cliqueExtend` and `complete_reachable`; strict markings
must use the marked variant where required. This is a candidate API route,
not a checked bridge. The initial-path extension also remains open.

## Prior implementation record — before ownership transfer

Continuation from clean pushed `114fe7d` completes the conditional initial-vertex
inheritance theorem. Every feasible initial-extra subset has an actual anchor
witness with the prescribed core. The abstract subset path lifts through the
checked crossing slides. Preparation and its reverse then connect arbitrary
connected common-cover states of the same total selected size.
`commonCover_connected_of_initialVertex_core` assumes only the explicit
smaller-core uniqueness and removable matching-edge hypotheses.
The following increment preserves the exact number of chain terminals and
the short natural edges after deleting zero. With at least three chains,
`commonCover_connected_of_initialVertex_short` discharges removability using
the checked paths around good core edges. Only smaller-core uniqueness remains
to be supplied by induction in this branch.

The global vertex-count induction remains unfinished. P0–P5 are complete under their
planned contracts; P6 is partial and P7--P10 remain open. The independent diagram
e-expansion and complete circular/ordinary draft remain unfinished. A new
ordinary draft section now details initial-vertex inheritance and endpoint
attachment, with two inspected figures. A separate Claude task gives the
exact independent attachment obligations.
The full goal is unchanged.

User reaffirmed that the paper must retain the diagram-style proof and that
this same proof must be formalized. Preserve the written move sequence; graph
lemmas only justify its displayed edge configurations. The formalization plan
now records the correspondence for the last-clique diagrams. Do not substitute
another abstract component argument when writing the draft.

Primary owns all `DiagramProof/` sources, `DiagramProofVerification.lean`,
this handoff, the formalization plan, task suggestions and the authorized
proof notes. Historical ownership and immutable prefixes remain unchanged;
the archive below preserves their exact earlier record.

### Previous P6 work and ownership (superseded by the release above)

Continuation from clean pushed `2a023fd`: Terra owns only new
`LastCliqueNaturalEdges.lean` (canonical core short-edge preservation).
Luna owns only new `TwoChainCardinality.lean` (two-terminal base from at most
two terminal fixed points). Primary owns corner selection, reversal of short
edges and the global induction. Delegates remain build-free; only primary builds.

After pushed `68efc6a`, Terra supplied `InitialVertexChainCount.lean` and Luna
supplied `InitialVertexNaturalEdges.lean`. Primary repaired, integrated and
verified both, and wrote `InitialVertexRemovable`. Their ownership has returned.
All three modules pass focused builds, and all 647 axiom queries pass.
Both delegates remained build-free; primary retains the single build slot.
The independent review approved all three contracts at pushed `f23eac3`:
zero is nonterminal because its retained corner starts there, successor
restriction preserves terminal fixed points, and the existing third-chain
paths supply removability. It also approved the canonical reversed
`lastCliqueEmbed` choice for the next branch. No review remains active.

Terra supplied `InitialVertexSectorWitness.lean`, constructing an anchor with
prescribed initial extras and core. Luna supplied `InitialVertexFeasibility.lean`
for size and room bounds. Primary repaired and verified both and owns
`InitialVertexSectorPaths`, `InitialVertexSectors` and `InitialVertexInheritance`.
All five new modules pass focused builds. All source ownership has returned;
no delegated task or compiler remains active. Primary remains sole build owner.
Issue #8 remains unassigned. The independent assembly review approved the
witnesses, insertion/deletion directions and matching-edge-only hypothesis.
Natural core connectivity is derived from the given connected core, not assumed
as an extra global hypothesis. All 640 axiom queries pass with standard axioms.

Terra supplied `InitialVertexExtension.lean`; Luna supplied
`InitialVertexExtras.lean` and a read-only sector-interface audit. Both files
have returned to primary, which repaired and verified them. Primary wrote
`InitialVertexExchange`, `InitialVertexAdjacent` and `InitialVertexAdjacentPaths`.
All delegates remained build-free. The independent review approved the exact
row/core equations, witness construction and use of target capacity, with no
hidden global uniqueness assumption. The focused build and all 633 axiom
queries pass. The axiom check `67389` completed after waiting for the other
project's compiler to release the slot. No task compiler, queued check or
delegated task remains active. The writing checkpoint is separate.

Primary owns all DiagramProof source files, verification, this handoff, the
formalization plan and the Aristotle ledger, and retains the sole serialized
build slot. All subagent source ownership has returned. Terra supplied
`InitialVertexCorners`; Luna supplied `InitialVertexCopies` and
`InitialVertexConnectivity`. Primary repaired and verified them and
owns `ClosedInducedAnchors`, `InitialVertexRestriction`,
`InitialVertexConnectedCore`, `InitialVertexCounts` and `InitialVertexCorePaths`.
Primary also wrote `InitialVertexMatching`. All nine new modules pass their
focused builds and independent import/source/axiom checks. No delegated task,
compiler or queued check remained active at `69612d1`. The initial native wait `11485`
finished; it let the other project's live compilers release the shared slot
before invoking Lake. Subsequent repairs and checks were serialized.

The independent source review approved successor-closed restriction, the
vacant matching edge argument and the strictly decreasing zero-row count.
The completed proof retains exactly the written crossing slides and core-path
lifts. The smaller-core uniqueness hypothesis is explicit in the fixed-sector
theorem. No whole-component equivalence is asserted for deleting zero.
The final independent P1 acceptance audit also passed: all finite/lifted
covers, exact marking, convex and swept core lifts, strict/corner geometry,
initial-vertex restriction and complete-component reflection are checked.
P1 is complete under its stated contracts; P6 remains partial.

The first-clique checkpoint's independent review approved the reflected
triangle direction, complete-component correspondence and explicit reflected
core hypothesis. Earlier independent architecture review was completed before
implementation. No new architecture choice is pending.

Aristotle's two prior auxiliary proofs (temporary-edge repair and tree with
attached leaves) are integrated and locally verified. There is no live remote
request, CLI watcher or Claude child. See [docs/ARISTOTLE.md](docs/ARISTOTLE.md)
for request identifiers, hashes and independent-review records. User
instructions authorize Aristotle, subagents and Claude; only primary builds.

### Verified P1/P6 increment — initial core and fixed extra sets

- `ClosedInducedAnchors` preserves chain terminals, good edges and anchor
  restriction when the retained vertices are closed under corner successors.
  It also preserves the anchor at a core-replacement endpoint when the exterior
  is restored. It does not require the deleted initial corner to survive.
- `InitialVertexCorners` proves no new maximal corner appears for first corners
  starting at 0 and 1. `initialVertex_corner_retained_iff` records that exactly
  the corner at zero is lost. `InitialVertexRestriction` gives the actual
  restriction, retained terminal formula and convex actual path lift, with
  the original strict markings and exact exterior.
- `InitialVertexCopies` reuses `exists_copySuccessor` to construct the matching
  edge. `InitialVertexMatching` classifies the initial good edges and proves
  the matching edge belongs to the actual core, is normal and good, and has
  the exact crossing-copy relation to the initial extra.
- `exists_initial_vertex_obstruction` finds a selected zero-row edge entering
  a different core block. `exists_initial_core_join` proves its matching edge
  is absent by the two core connections to the matching edge's head.
  `exists_reachable_connected_initialVertex_core` repeatedly applies the actual
  crossing slide. The number of selected edges at zero strictly decreases;
  every completed slide endpoint remains an anchor and globally connected.
- `InitialVertexCounts` splits total size into core and zero-row sizes.
  `initialVertex_reachable_of_same_initial_row` connects two anchors with
  connected restrictions, equal total counts and the same initial row, assuming
  uniqueness only in the smaller core. The core path lifts with every exterior
  edge fixed, and its endpoint is identified with the prescribed target.
- This completes the first two parts of the written initial-vertex argument.
  Witnesses omitting the matching edge and adjacent-sector exchanges are now
  implemented, and the subset-band assembly is now checked too. The global
  path induction remains to be assembled.

### Verified P1/P5 increment — reflection and first-clique inheritance

- `ReversedDiagram` constructs an actual forward diagram from reflected
  natural edges and inherits exactly the reflected strict corners. Corners
  correspond by their extremal endpoint characterization.
- `ReversedRelations` reverses directed paths and cover tests and preserves
  weak connections. `OrderReversal` maps full selections through an edge
  bijection, retaining total counts and giving an orientation equivalence.
  Reflecting a directed triangle flip reverses its direction. This supplies
  both directions of the actual undirected path correspondence.
- `ReversedPaths.reversedOrientation_map_flipComponent` identifies the image
  with the whole reflected component, not just a subset or a one-way lift.
  Common-cover and connectedness hypotheses transport exactly.
- `ReversedEmbedding` reflects an increasing embedding by reversing both its
  domain and range. Its image theorem takes the first retained vertex and
  final interval to the last-clique retained initial interval and final vertex.
- `commonCover_connected_of_firstClique_core` applies last-clique inheritance
  with the reversed second/first corners, then pulls the actual path back.
  Its induction hypothesis names the reflected induced diagram explicitly;
  no uniqueness for the original core is silently substituted. P6's global
  vertex-count induction can supply this hypothesis once decrease is proved.
- All six new modules pass focused checks. The verification file has 590
  axiom queries, with only the standard three axioms or none. Independent
  imports contain 259 project files and exclude the old word/scan proof;
  all 185 DiagramProof source modules pass the source and 100-column guards.
  Logs: `p5-first-clique-build.log`, `p1-reversal-path-build.log`,
  `p1-reversal-axioms.log`, `p1-reversal-imports.txt` in the external
  diagram-formalization request directory. Earlier repair logs can contain
  superseded failures. No broad build or dependency update ran.


### Next obligations and source map

Next: construct the global vertex-count induction. The initial-vertex branch
now retains short edges and chain count and discharges matching-edge removability.
For the first-clique branch, reuse `lastCliqueEmbed` and reversal to avoid
another embedding representation. A last-clique core retains all short edges:
ordinary pairs lift identically; pairs ending at the retained last vertex
start at least at c-1 and lie in the last corner's clique when its tail is < c.
Use `reverseOrderEmbedding_involutive` for the reflected core actually named
by `commonCover_connected_of_firstClique_core`. Prove strict size decrease,
find the first two corners or the complete base, and derive the two-terminal
base from the existing cardinal chain bound. Then close the strong induction.
Ambient short edges must also be transported through reversal. No preservation
of chain count under first-clique trimming is needed if the induction theorem
covers all chain counts and dispatches the two-chain case internally.

The general conditional inheritance theorem retains its removable-edge
hypothesis. The short-edge/three-chain specialization now proves it. Global
induction must supply strictly smaller cores and their uniqueness. First-/last-clique inheritance and the
initial-core preparation, restriction and matching-edge constructions are now
checked and should be reused. Do not assume reflection preserves anchors,
chain terminals, good-edge sets or valuations; the checked path transport
needs none of these claims.


The written source for the current work is
[initial-vertex inheritance](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#initial-vertex-inheritance-through-extra-edge-sectors),
with the staged obligations in
[the formalization plan](docs/COMPONENT_DIAGRAM_FORMALIZATION_PLAN.md).
The same-size missing-edge witness, adjacent-sector paths and full subset
assembly are now checked. Matching-edge removability follows from the retained
short edges and three chains. The global vertex-count induction supplies core uniqueness.

The [assembled mathematical proof](docs/proofs/COMPONENT_DIAGRAM_COMPLETION.md)
and [cleanup audit](docs/proofs/COMPONENT_DIAGRAM_AUDIT.md) are complete as written
mathematics. This does not mean the independent Lean theorem is complete.
The older Lean ordinary/circular component theorem uses another proof and is
not imported into the DiagramProof route. Preserve that distinction.

The full goal also requires a new illustrated draft combining the circular
e-expansion and ordinary component expansion by diagrams, in Robin and the
author's style. The user requested drafting during build waits and a
GitHub task for Claude. The new
[ordinary draft section](docs/drafts/ORDINARY_COMPONENT_DIAGRAM_PROOF.md)
details initial-vertex inheritance and right attachment, with two vector
figures rendered and visually inspected. It summarizes the remaining
component-recursion induction; the circular section and combined manuscript
are not yet assembled. Independent mathematical review approved the core
and fibre-merger arguments; its endpoint and figure clarifications were
incorporated. The [Claude task](docs/DIAGRAM_PROOF_CLAUDE_TASK.md) gives the
exact independent P9 attachment contracts and proposed new files.
[GitHub issue #8](https://github.com/PerAlexandersson/VerticalStripLLT/issues/8)
contains the same detailed task with repository links; its body was read back
and checked. Writing checkpoint `ebb02aa` is pushed. No Claude run is active
and no source ownership has yet transferred. The invoked writing skill is
[combinatorics-paper-writing](/home/dev/.codex/skills/combinatorics-paper-writing/SKILL.md);
its instructions and author-style references have been read. Use first-person
plural mathematical prose and established terminology. Keep audit and compiler
details out of the manuscript, and link each diagram construction to the
corresponding verified lemma in the supporting source map.

### Verification and recovery

Starting checkpoint: `114fe7d` on `main`, clean and pushed at continuation start.
The five inheritance modules and three following geometry/removability modules
pass focused builds. The independent import closure now has 281 project files;
all 207 DiagramProof modules pass source/100-column guards. All 647 axiom
queries pass in order, using only the standard three
axioms or none. Local Markdown links, whitespace and both figure previews
were also checked.
Logs: `p6-initial-inheritance-build.log`, `p6-initial-inheritance-axioms.log`
and `p6-initial-inheritance-imports.txt`, followed by
`p6-initial-removable-build.log`, `p6-initial-removable-axioms.log` and
`p6-initial-removable-imports.txt`. The preliminary geometry and sector logs contain
superseded repairs. Earlier 633/615-query checkpoints and their logs remain
preserved. No broad build or dependency update ran.

External request directory:
`/lake-cache/ai-projects/requests/VerticalStripLLT/diagram-formalization/`.
Only `lake-workspace` is used; no broad build or dependency update is planned.
The existing package-path manifest warning is unchanged. Lean MCP is rooted at
RealRooted, so project diagnostics use the focused compiler. Runtime discovery
and `codex mcp list` were refreshed during the preceding continuation.
Aristotle is available by CLI, not a registered MCP. No new mathematical
computation or shared Rust edit is part of this continuation.

The [complete archived handoff through 607c84e](docs/archive/diagram-implementation-through-first-clique.md)
preserves all earlier proof/implementation status distinctions, exact
verification scopes, ownership and recovery hashes. Historical proof-note
prefixes and unrelated ownership are unchanged. Primary retains ownership of
the assembled completion, recurrence outline, append-only NN/DN/endpoint
continuations and existing external consumers recorded there. Preserve their
prefixes at `a3d076b` and the older archive links.
