# VerticalStripLLT handoff

## Scope and verified results

The ordinary and full aggregate circular HRV expansions and e-positivity are
formalized. The stronger formula for **each entire flip component**, ordinary
and circular, remains open. [Component proof status](docs/FLIP_COMPONENT_STATUS.md)
is the research entry point; [circular completion](docs/CIRCULAR_COMPLETION.md)
is authoritative for the completed aggregate theorem.

Verified Lean checkpoint: `18fbb4d`. Public declarations in
`VerticalStripLLT/Circular/Expansion.lean`, namespace `VerticalStripLLT.Circular`:

- `coloringLLT_shifted_eq_eval_shiftedOrientationExpansion`;
- `coloringLLT_shifted_eq_orientation_sum`;
- `coloringLLT_shifted_e_positive`.

These cover every valid circular diagram and finite alphabet, including the
empty alphabet, without recurrence, acyclicity or no-wrap hypotheses. The
full build passed (1908 jobs); `Verification.lean` checked 2037 inventory
entries using only `propext`, `Classical.choice`, and `Quot.sound`. External
logs are `circular-expansion-{build,full-build,axioms}.log`. Subsequent component
research is audited prose, not new Lean declarations. Initialization commits
`830cc6b`, `130f7e8` and the immutable reference files are preserved.

## Ownership and checkpoint

Primary owns strategy, research notes, external diagnostics, integration,
and the sole global Lean build slot. Only primary may use `lake-workspace`,
after checking that no other build is active. No slot transfer occurred.
No Lean, shared Rust, reference or Overleaf source changed in this increment.
No compilation was needed or run.

Preceding pushed checkpoint: `ba559d1`, minimum-area realization and the
crossing-corner sweep. That goal turn made progress; this continuation began
with a clean worktree.
The current increment proves signed whole-component corner-deletion recurrences
and a stronger ordinary mixed-cycle cancellation companion. Primary owns
`docs/proofs/COMPONENT_CORNER_DIFFERENCES.md`, linked induction/completion/status
notes, documentation index, consultation ledger and this handoff. The ordinary
quotient proof moved from the long induction note into the new companion;
there is one authoritative copy.

The user authorized parallel brainstorming. Astra supplied the mixed-cycle
involution and independently checked alternating deletion; Terra audited both
and the relative absorption argument. All delegates were read-only and
build-free, their tasks are finished, and no delegate owns editable files.
No build slot was transferred. No new Lean declarations were added.

## Current mathematical result and exact next step

The author's minimum-area component induction remains the main route.
The saturated selected-edge envelope is the unique minimum-area realization
on fixed vertex order, including circular lifted edge orbits. Its exact
area difference and whole-component normalization are in the
[induction note](docs/proofs/FLIP_COMPONENT_INDUCTION.md).

New [corner-difference companion](docs/proofs/COMPONENT_CORNER_DIFFERENCES.md):

- Ordinary strict-corner deletion leaves the normal state set unchanged and
  removes only flips retaining the deleted corner. A complete source component
  therefore decomposes into ENTIRE components of every corner-deletion target.
- Alternating deletion of F⊆S gives a signed smaller-area component recurrence
  if no state covers every corner of F simultaneously. The redundant corner
  may vary with the state; this extends the always-redundant-corner reduction.
- Stronger result: for ANY disjoint ordinary forward edge sets N,F, a cycle in N∪F^op
  makes the alternating difference vanish for both K and E. The E proof is a
  sign-reversing involution preserving the entire highest-reachability map.
  The chosen edge depends on the lexicographically largest (HRV, head) along
  a fixed mixed cycle; the tie-break handles empty intervening paths.
- Consequently the same whole-component signed recurrence applies when EVERY
  state becomes cyclic after reversing its strict corners. A minimum-area
  ordinary counterexample must contain an acyclic reversed-corner state,
  hence a single state witnessing all strict corners as covers.
- Relative path absorption: if A without f=wz and aw has a selected a→z path,
  removing normal aw preserves ∂_f K and ∂_f E. This supplies an idempotent
  ordinary state projection and resolves the double-attachment crossing
  boundary at the level of relative valuations. Its multiplicities have NOT
  been reconstructed into whole target components.

The circular deletion quotient fails without added hypotheses: area (1,2,2),
strict {02,21}, singleton selected {02,21,01}; deleting 21 enters the full
component {02,01}↔{02,12}, whose second state becomes cyclic on reinsertion.
The source chain satisfies HRV; this is an obstruction to the graph map.
The earlier always-redundant-corner lemma still applies circularly. The new
unrestricted recurrence and HRV involution are ordinary, not primitive circular.

The [DN completion graph](docs/proofs/DN_COMPONENT_COMPLETION.md) still provides
certified packet equations. More components can now be subtracted as known
by the new recurrence. Several equations need only span over Q after known
components are removed; the proved torsion-free argument clears denominators.
One active component per packet is sufficient, NOT required. Its uniform
isolation assertion and the more general packet-generation target remain open.

Next: transport the remaining ordinary components, which admit acyclic
reversed-corner states, through valid area/moment-decreasing recurrences.
Use the new signed correction space and relative absorption, but reconstruct
occurrence multiplicities into whole components before applying induction.
For all-corner differences, absorption through crossing corner g leaves an
explicit smaller D\g residual which still requires that reconstruction.
No new conditional Lean scaffold is needed. The full ordinary and primitive
circular component formulas remain open; aggregate circular Lean work is done.

## Consultations and computation

Aristotle project `3fd0ed1d-ba60-404b-8b99-beaaae1c4d08`, task
`16154bfd-ae04-49cd-9549-6d0a931f9309`, is terminal **COMPLETE**. Its return
explicitly does not prove the component theorem. Primary downloaded and
read the full result, verified the corrected five-vertex packet, and recorded
scope/convention corrections in [the ledger](docs/ARISTOTLE.md). Its n=7 scan
was terminated with no result. No active remote task or observer remains.
A new read-only Sonnet consultation, session `90205`, finished with exit 0.
It restated the packet-row criterion and did not prove generation. Primary
recorded the logical corrections and exact prompt/result hashes in the ledger.
All Claude/Aristotle consultations and observers are terminal.

External requests root: `/lake-cache/ai-projects/requests/VerticalStripLLT/`.
Current receipts are in `component-recurrence/`; the completion note gives
input/result hashes and exact scope. For the fixed larger diagram, primary
audited and reused the returned ordinary `dnmodel.py`, first checking exact
component-partition agreement with the old model on both preceding fixtures.
This avoids quadratic diamond deduplication. No new graph enumerator or
polynomial family was introduced. The existing Rust
`component_source_probe` independently checked the three-state inactive and
84-state active components of the boundary diagnostic, using complete caps.

The Rust library guide, cargo metadata and LLT/flip APIs were refreshed before
experiments. Maintained primitives in `sym-poly/sym/src/llt.rs` include
`circular_highest_reachable_vertices`,
`circular_vertical_strip_llt_hrv_e_expansion`, and
`directed_graph_llt_symmetric`. The scratch ordinary flip enumerator is not a
maintained circular lifted-cover API; the existing
[API proposal](suggestions/flip-enumeration-api.md) records that gap. No shared
Rust edit or build occurred. AXLE is registered; Lean MCP targets RealRooted;
Aristotle was accessed through its installed CLI.

## Checks and history

Documentation checks passed: `git diff --check`, focused diff review, and
100 local links (including heading anchors) across seven Markdown files.
Both initialization commits remain ancestors; no Lean/reference/Overleaf
source changed. No build was needed. This handoff accompanies the focused
corner-difference checkpoint on `main`; its exact hash is in Git history.
External diagnostics and read-only delegates from this increment are terminal.

The previous handoff, including winding and recurrence chronology and exact
old observer status, is [archived through DN transport](docs/archive/flip-component-handoff-through-dn-transport.md).
It is historical, not an active work list. Earlier checkpoint history remains
in Git and the linked documentation archive. The current goal is active and
has made progress; neither the full proof nor its Lean formalization is done.
