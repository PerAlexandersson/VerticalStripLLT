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
The current increment consolidates documentation and records an audited
structural theorem; it changes no Lean, Rust, reference, or Overleaf source.

Last pushed checkpoint before consolidation: `ffa23fd`, endpoint recovery and
multivariate articulation gluing. Earlier `1a966fb` records the counterexample
to scalar active uniqueness. Primary owns the new proof map, tree-connectivity
note, handoff/archive, index and Aristotle ledger. The pre-existing dirty
Claude-preparation paragraph was primary-owned and is superseded below.

Astra completed the read-only tree-proof audit. Luna completed the read-only
Rust capability refresh. Both lanes are released; Terra is idle. No delegate
owns an editable file. Earlier endpoint and corner-reduction audits are
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

The remaining ordinary proposal is AU_prime: in a saturated ordinary natural
graph without an articulation, at each ascent there is at most one active
connected component.
Activity means every strict corner is a cover somewhere in the component;
witnesses may differ. AU_prime beyond trees remains open. The proved aggregate
block identity plus AU_prime would isolate each ordinary component by induction.
Total-ascent uniqueness without the articulation restriction is false.

Compatible lifts reduce balanced circular components to ordinary components.
Unbalanced circular components still need a companion argument. The general
source-cancellation route remains auxiliary and open. Neither the structural
tree theorem nor the aggregate theorem proves the full component formula.

Next: audit the pending Claude response on AU_prime; pursue the quotient graph
created by strict-corner deletion. Keep the circular winding obligation visible.
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

One bounded Claude Sonnet consultation is active in native session `57970`,
with a 20-minute process timeout. Its self-contained prompt requests a proof
or exact counterexample to AU_prime. No tools, file access, MCP or Lean build
slot is delegated. Primary owns monitoring and cleanup. Artifacts are in
`claude-active-corner/{PROMPT.md,response.json,stderr.log}` under the external
requests root. The initial invalid empty MCP configuration failed before the
model task began; the corrected invocation uses an empty server map.

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
No shared Rust files were edited and no new computations were run here.

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
