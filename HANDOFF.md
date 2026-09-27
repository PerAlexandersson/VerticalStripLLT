# VerticalStripLLT handoff

## Scope and verified results

The ordinary and full aggregate circular HRV expansions and e-positivity are
formalized. The current goal is the stronger HRV identity for **each entire
flip component**, ordinary and circular. That identity remains open.
[The component proof map](docs/FLIP_COMPONENT_STATUS.md) is the entry point;
[the circular completion audit](docs/CIRCULAR_COMPLETION.md) is authoritative
for the completed aggregate theorem.

Verified Lean checkpoint: `18fbb4d`. Public circular declarations, in
`VerticalStripLLT/Circular/Expansion.lean`, namespace `VerticalStripLLT.Circular`:

- `coloringLLT_shifted_eq_eval_shiftedOrientationExpansion`;
- `coloringLLT_shifted_eq_orientation_sum`;
- `coloringLLT_shifted_e_positive`.

They cover every valid circular diagram and finite alphabet, including the
empty alphabet, with no recurrence, acyclicity or no-wrap hypothesis.
The full build passed (1908 jobs); `Verification.lean` checked 2037 inventory
entries using only `propext`, `Classical.choice`, and `Quot.sound`. Logs are
`circular-expansion-{build,full-build,axioms}.log` under the external requests
root. No subsequent Lean changes or builds have occurred in this research lane.
Initialization commits `830cc6b`, `130f7e8` and the immutable references survive.

## Current ownership and checkpoints

Primary owns strategy, all current research notes, external probes, integration,
and the sole global Lean build slot. Only primary may run `lake-workspace`,
after checking no other build is active. No slot transfer has occurred.
The current increment formulates the author's component recurrence and derives
its explicit DN redistribution from the existing local maps. It changes no
Lean, shared Rust, reference, or Overleaf source.

Last pushed checkpoint: `b65b936`, integer-potential reconstruction criterion;
`1cb7420` gives explicit recurrence transport and local nonflip reductions.
Preceding `25a527c` proves exact winding
aggregate and the component-isolation obstruction. Earlier `bca8fb0` proves
forest-component semantics and primitive circular winding reduction. Earlier `1c93849` consolidated the proof notes. Checkpoint `ffa23fd` proves endpoint recovery and multivariate
articulation gluing. Earlier `1a966fb` records the counterexample
to scalar active uniqueness. Primary owns the new proof map, tree-connectivity
note, handoff/archive, index and Aristotle ledger. The pre-existing dirty
Claude-preparation paragraph was primary-owned and is superseded below.

Astra completed the tree, forest-semantic and winding-transport audits. Luna
completed the Rust capability refresh; Terra supplied the winding-lattice
normal form. All read-only lanes are released. No delegate owns an editable file. Earlier endpoint and corner-reduction audits are
recorded in the relevant modular notes.

## Current mathematical progress and next step

Corner selected/unselected branching and always-redundant strict-corner
removal preserve ENTIRE components and decrease area. Endpoint chain attachment
and triangular cancellation prove the doubly marked aggregate identity;
articulation gluing gives separate ascent variables for the natural blocks.
These are audited prose proofs, not newly compiled Lean declarations.

Aristotle's latest return additionally proves corner leaf normalization and
connectivity of all ordinary spanning trees with a fixed interval envelope.
Primary and independent Astra checked the general argument, including strict
edge preservation, actual covers, smaller-envelope induction and base cases.
See [the tree proof](docs/proofs/COMPONENT_TREE_CONNECTIVITY.md).

An auxiliary ordinary proposal is AU_prime: in a saturated ordinary natural
graph without an articulation, at each ascent there is at most one active
connected component.
Activity means every strict corner is a cover somewhere in the component;
witnesses may differ. AU_prime beyond trees remains open. The proved aggregate
block identity plus AU_prime would isolate each ordinary component by induction.
Total-ascent uniqueness without the articulation restriction is false.

A new connected-aggregate extraction now proves the full HRV formula for
ordinary and circular forest components, in prose. For each vertex partition,
refinement-restricted orientation sums factor over induced diagrams. Finite
partition inversion isolates the connected aggregate; its tree coefficient
is one entire component by tree connectivity. Forest products and compatible
lifts give the circular result. See `COMPONENT_CONNECTED_AGGREGATE.md`.

Components containing undirected cycles remain open. Compatible lifts reduce
balanced circular ones to ordinary components. The new integer-lattice
invariant and finite-cover compression reduce every connected unbalanced
component to an ENTIRE primitive circular component (cycle-winding gcd 1),
with K and HRV preserved. Primary developed this reduction, Terra checked
the lattice normal form, and Astra audited the entire-component/HRV transport.
The primitive circular companion remains open. The source-cancellation route
remains auxiliary and open.

The user recalls a component-through-recurrences proof and identifies its
precise formulation as the difficulty. This is now the primary route again:
extract the draft's orientation cases and prove transport preserves both
valuations and constant multiplicities on complete components. AU_prime and
exact winding refinement are auxiliary tools, not necessary assumptions of
that route. Keep exposed corners unmarked until their branches are separated.
Do not start another broad enumeration or Lean scaffolding task in place of
resolving that structural question.

## Consultations

Aristotle project `3fd0ed1d-ba60-404b-8b99-beaaae1c4d08`, task
`c2a21316-805d-489f-a1c7-40f51b40b57c`, is terminal **COMPLETE**. This means the
requested counterexample audit/refinement returned, not that AU_prime or the
component theorem was proved. Native observer `38474` exited successfully.
The extracted return is `projected-source-companion/ordinary-active-final-PROOF.md`
under the external requests root. Audited tree lemmas are recorded in prose;
no generated Lean source was integrated. [The ledger](docs/ARISTOTLE.md)
contains exact payload/result hashes and historical task outcomes.

The bounded Claude Sonnet consultation in native session `57970` is terminal,
exit 0 with a successful response envelope. It did not prove AU_prime. The
valid part is connectivity at every ascent in the saturated distance-two
band graph, by adjacent swaps; aggregate coefficient extraction gives that
family's component formula. Its proposed bootstrap confuses deletion with
saturation and asks for a false whole-region redundancy property. Primary
records the audited outcome in the ledger and active-corner note. No Claude
process remains active from those consultations. The result and exact prompt are retained
under `claude-active-corner/` in the external requests root.

## Computation and records

Luna's refreshed Rust audit found maintained exact primitives in
`/workspace/rust/sym-poly/sym/src/llt.rs`:
`circular_highest_reachable_vertices`,
`circular_vertical_strip_llt_hrv_e_expansion`, and
`directed_graph_llt_symmetric`. Aggregate tests are in
`sym-poly/sym/tests/circular_hrv.rs`.

The ordinary scratch binary `experiments/src/bin/llt_flip_components.rs`
has `flip_component`, `llt_flip_neighbors`, `is_llt_flip_pair`, and
`component_generating_function`. It does not implement the circular lifted
cover rule as a maintained public API. The existing external Rust component
probe therefore remains useful and reuses the maintained circular HRV routine.
The promotion proposal is [flip enumeration](suggestions/flip-enumeration-api.md).
No shared Rust files were edited or rebuilt. The current two targeted
component diagnostics reused the existing Rust binaries and Python model;
receipts are linked in the exact-winding companion note.

External requests root:
`/lake-cache/ai-projects/requests/VerticalStripLLT/`.
Experiment inputs, counts, caps and hashes stay in their detailed proof notes;
finite evidence is not a proof. MCP registry was refreshed: AXLE is available,
Lean MCP is configured for RealRooted, and Aristotle is accessed through its
installed CLI. No missing component MCP is presumed to exist.

The prior long handoff is
[archived through endpoint recovery](docs/archive/flip-component-handoff-through-ffa23fd.md).
Earlier implementation and research chronology remain in the documentation
archive and Git. Current task status belongs here, not in those snapshots.

Consolidation checks: local links in the changed Markdown resolve; the archive
preserves every previous handoff line and the exact old Aristotle ledger
(apart from adjusted relative links). Independent Astra review approved the
tree proof and scope map. `git diff --check` passes. No compilation was needed.

## Current exact-winding companion

Primary owns `docs/proofs/COMPONENT_LATTICE_AGGREGATE.md`, the proof map,
index, winding-note link, this handoff and the external diagnostic receipts.
Astra completed the read-only proof audit; no local delegate or remote proof
process was active at that checkpoint. The preceding increment was `bca8fb0`.

The new proved companion filters selected edges by their undirected signed
walk relation W, compresses each block's compatible lift classes, and applies
the existing aggregate theorem. Finite-poset inversion then proves the HRV
identity for each EXACT W and edge count. W retains the separate cycle
subgroup of each weak block; one global vertical coordinate would merge them.
Astra checked that correction, the compatible natural diagrams, disconnected
subsets, admissibility, actual HRV transport and inversion. This is prose,
not a new Lean declaration or the full component theorem.

Two complete active primitive components in area (3,1,2,3), strict {10,03},
have the same W and ascent but different HRV sums. They have 3 and 4 states;
none is a chain-poset state. The existing Rust component probe and HRV bridge
agree with the old Python flip model; direct all-alphabet coloring identities
verify both component formulas. The stronger obstruction is recorded in the
new note, with exact input and source/result hashes. This rules out isolating
arbitrary components by W, ascent and activity alone, even after discarding
chain-only components. No broad screen or new enumeration engine was used.

The Rust guide, workspace metadata and relevant HRV/flip/SNF APIs were checked
before the diagnostic. Python only assembled fixed inputs and compared existing
outputs; no new graph-potential classifier, polynomial family or component
algorithm was needed. The new theorem and obstruction passed independent
mathematical review. Markdown link and whitespace checks are required before
this checkpoint; compilation is unnecessary for these documentation-only edits.

## Author-steered recurrence formulation

Primary owns the new transport-interface section in the existing
`FLIP_COMPONENT_INDUCTION.md` and the corresponding status-map updates.
Astra approved the integer flip-difference intertwining criterion read-only;
Luna returned the exact author case table for relation (3), and identified
the provisional (8') assertions in `LLT flip/main.tex`, also read-only. No source, Overleaf, or build-slot
ownership is delegated. Primary re-read the draft's transport/packet passages
and original commented sketch; no manuscript changes are being made.

The recurrence note now proves the reconstruction equivalence
`B_target T = H B_source` over the integers and the semantic residual
criterion for both valuations with common T,R,r. It includes the actual
relation-(3) local table and its internal four-state certificate. Exterior
and mixed-flip rows remain to be constructed. Correction generators must
have certified identities, and target measure decrease must be proved.
This sharpens the author's intended proof; it does not replace the missing
recurrence maps by a conditional wrapper or claim the full goal is complete.
Old duplicate reconstruction checklists were removed from the same note;
the failed diamond shortcut remains linked to its detailed audit.

Luna completed the read-only API audit. Primary checked the actual circular
DN code: `DNOrientationBlocks.dn_bottom` sends exterior Q to its adjacent
vertex swap σQ, while `dn_top` retains Q. The aggregate theorem in
`SecondBounceOrientation.lean` reindexes the entire powerset in `hbot`.
The recurrence note now records the resulting signed multiplicities g and
their free target-diamond parameter β. Both valuations are preserved when
source middle multiplicities agree; an explicit unmatched-state residual is
retained otherwise. The internal four-state discussion was corrected to avoid
identifying the two exterior maps.

Astra completed the read-only audit. Nonflip blocks reduce semantically to
closure-degenerate endpoint terms or smaller strict-corner-deletion packets;
the note contains the full path argument and cyclic-state cases. The ordinary
corner quotient gives an exact cover-boundary equation for the component
defect, without requiring redundant fragments to be complete components.
Its boundary diamond has a lower-area residual that must be retained.

Primary owns Aristotle task `16154bfd-ae04-49cd-9549-6d0a931f9309`, accepted
and initially QUEUED in project `3fd0ed1d-ba60-404b-8b99-beaaae1c4d08`.
The request is `component-recurrence/TARGET.md` under the external requests
root; exact input hashes and submission logs are retained there. It asks for
the concrete global regrouping, using these local reductions and the boundary
equation. Luna and Astra completed the read-only target-flip audit; no local
delegate is active or owns editable files. Primary derived the parity change
γ(Q)=(-1)^|Q|β(Q), turning all regrouping equations into integer potential
differences. Reconstruction within this family is equivalent to zero periods
around ALL closed walks of the exterior-index multigraph, including mixed
ascent levels. A fixed spanning forest gives integer-linear transport, with
no denominator. The reviewed proof is in the existing recurrence note.

Primary sent `POTENTIAL_ADDENDUM.md` inline to the SAME running Aristotle task;
the authoritative task list confirms the unchanged ID and IN_PROGRESS status.
The next task is to express its fundamental-cycle period rows through source
flip differences, incorporating the deletion packets and certified corrections.
This vanishing has not been proved; the consultation is not evidence of
completion. Native observer `71315` disconnected and exited zero; the
authoritative task list still reports IN_PROGRESS. Primary reattached native
observer `54512` to this SAME task with a 30-minute process allowance, writing
`component-recurrence/observer-reconnect.log`. The original log is retained.
An observer timeout or disconnect does
not cancel the remote task. On completion, inspect authoritative task status,
download that task's result, and audit the claimed reconstruction before any
Lean port. Primary retains monitoring ownership; no automatic wake-up promise
is made.

## Current recurrence audit increment

The preceding goal turn made progress through `b65b936`. The worktree was
clean at this continuation. Primary retains ownership of the recurrence note,
status map, handoff and remote-request ledger; no source or build changes.
Astra completed a bounded read-only audit of two new uniform flip-graph maps:
the induced 00 graphs are conjugate by the exterior swap, and the induced 11
graphs agree under identity on Q. These use actual lifted covers and
admissibility, not only `orientMono` equalities. The source normal xz and target
normal uw toggle only internally; `hgap` is required on the source side.
The recurrence note records complete arguments and precise scope.

The SAME Aristotle task remains IN_PROGRESS. Its streamed analysis reports
a possible n=6 failure of the restricted β family, even after some deletion
packets. This is unverified remote computation, not an accepted mathematical
obstruction. Primary sent `EXACT_CERTIFICATE_REQUEST.md` inline, asking for
one full input/component/period certificate and the exact preprocessing and
packet space, and supplied the independently checked endpoint flip maps.
Do not attempt to prove unconditional period vanishing until this certificate
is audited. Failure of one transport family would not refute the author's
recurrence route or the component HRV formula.

Primary and Astra also proved an ordinary, linear semantic certificate with
an explicit deletion residual R=Σ(f10−f01)([del00]−[del01]); it no longer
requires paired source multiplicities. The existing saturated five-state
diagnostic gives a hand-checked two-edge period showing that keeping this R
fixed cannot reconstruct target components for ANY β. Thus the next task is
joint transport of the target and deletion packets, not solving a false
unconditional period-vanishing assertion. The recurrence note gives the
exact states, cover flips and contradictory equations. The original paired
family has different hypotheses and is not refuted by this diagnostic.

Terra completed the audit of the shared lower natural graph of source-delete(wz) and
target-delete(ux), with the two remaining corners uw,xz unmarked. The proposed
common diagram has the same doubled area as the source, but resolving either
unmarked corner gives strictly smaller branches. Corner-status invariance
makes the forced sectors unions of ENTIRE components. Primary corrected an
initially mistaken induced-sector limitation in Terra's return; Terra agreed
and rechecked the full component correspondence. The shared diagram is now
a proved component-level induction space, recorded in the recurrence note.
All local read-only lanes are released; the joint reconstruction remains open.
