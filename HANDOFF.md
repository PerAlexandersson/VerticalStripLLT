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

Preceding pushed checkpoint: `4aa6667`, signed corner deletion and mixed-cycle
cancellation. That goal turn made progress; this continuation began clean.
Primary owns the new `docs/proofs/COMPONENT_HRV_DIFFERENCES.md`, linked corner
and proof-status notes, index, consultation ledger and this handoff. Astra and
Terra returned bounded read-only audits; their tasks are finished, and neither
owns editable files. There is no build-slot transfer or new Lean declaration.

## Current mathematical result and exact next step

The author's minimum-area induction remains the main route. The saturated
selected-edge envelope is the unique minimum-area realization on fixed vertex
order. Ordinary deletion of strict corners partitions a whole source component
into ENTIRE smaller target components. Alternating deletion and the proved
mixed-cycle involution solve any component whose every state becomes cyclic
upon reversing strict corners. The remaining ordinary components admit an
acyclic reversed-corner state. These results and the circular limitation are
in [corner differences](docs/proofs/COMPONENT_CORNER_DIFFERENCES.md).

The new [exact HRV differences](docs/proofs/COMPONENT_HRV_DIFFERENCES.md) gives
an explicit coefficient formula for ARBITRARY disjoint forward edge sets N,F:

- A map α is HRV exactly when it is extensive and idempotent, selected edges
  weakly decrease α, and every nonroot has an outgoing same-α edge.
- In Σ_(J⊆F)(−1)^|F\J|[HRV(N∪J)], every map coefficient is 0,+1 or −1.
  Write U for nonroots without an N-outgoing same-α edge. Nonzero coefficients
  require F weakly increasing α, all equal-α F tails in U, and at least one
  equal-α F edge out of every u∈U. The coefficient is (−1)^(|F|+|U|).
- The proof factors choices by outgoing tail. Free optional edges cancel;
  each remaining tail contributes the alternating sum over nonempty subsets.
  Primary and Astra audited the general formula; Terra audited the corner case.
- For strict corners, each nonzero map has a unique realizing J. At a fixed α,
  all normal selections in any component contribute with the SAME sign.
  Its coefficient is that sign times an explicit outgoing-support count.

This supplies the exact HRV side to compare with mixed strict/weak colorings.
The semantic matching and full component theorem remain UNPROVED. Two shortcuts
have exact obstructions in the already-recorded component for areas (0,1,2,2),
strict13,24: its fixed reversed-color fiber can be disconnected, and its
canonical HRV-chain expansion cannot retain each vertex's individual color.
The latter gives counts 2 versus 1 at colors (2,1,3,4). A bijection may
redistribute colors while preserving the commutative monomial.

Next: prove the remaining component residual identity using these explicit
counts, or construct valid area/moment-decreasing recurrence packets which
isolate the component. The DN completion graph and signed smaller-component
corrections remain available; several packet equations may be combined over Q.
Do not assume one active component per packet, fixed-color connectivity,
statewise semantic equality, or arbitrary strict-edge decorations. Strict
edges must be natural corners. A local derivative involving noncorner shorts
needs a separate whole-component reconstruction before applying induction.

No unrestricted circular extension is claimed. The circular corner quotient
can admit target states whose reinsertion is cyclic. Always-redundant-corner
deletion remains valid, while the primitive circular component theorem is open.
The aggregate circular Lean theorem is complete.

## Running consultation and computation

Aristotle project `3fd0ed1d-ba60-404b-8b99-beaaae1c4d08` now has task
`4aa8cbee-7eb5-4d15-ba07-7806c7fa540a`, authoritatively **IN_PROGRESS**.
Native observer `83731` is running; resume this handle with `write_stdin`.
`aristotle tasks` confirmed the same task after both inline updates; do not
submit a replacement merely because an observation yields or times out.

The task seeks the remaining ordinary component residual identity, using the
new signed corner recurrence and explicit HRV coefficients. Four files were
uploaded; exact prompt/snapshot hashes and accepted addendum details are in
[the ledger](docs/ARISTOTLE.md). A file addendum was rejected while running;
the same text was accepted inline into this task. A further reminder makes
explicit that shorts of a deleted long need not be valid strict corners.
No returned proof is yet claimed; inspect the eventual full return.

The preceding task `16154bfd-ae04-49cd-9549-6d0a931f9309` is terminal
**COMPLETE**, explicitly without the component proof. All earlier Claude and
Aristotle consultations are terminal. No new Claude consultation was launched.

External requests root: `/lake-cache/ai-projects/requests/VerticalStripLLT/`.
Current inputs and diagnostic receipt are in `mixed-corner-residual/`.
The canonical-chain predicate probe reused `returned_dnmodel.py` on just three
recorded diagrams; the hand-checkable four-vertex obstruction suffices.
Its receipt hash and exact counts are in the new HRV note. No new enumerator
or polynomial family was created. The Rust capability guide, cargo metadata
and LLT source were checked before this bounded probe; a maintained
vertex-color-preserving component API is absent. The existing
[API proposal](suggestions/flip-enumeration-api.md) remains applicable.
No shared Rust edit or build occurred. AXLE is registered; Lean MCP targets
RealRooted; Aristotle is accessed through its installed CLI. `codex mcp list`
was refreshed. No credentials were printed or committed.

## Checks and history

Documentation checks passed: whitespace, focused diff review and all 96 local
links (including heading anchors) across six Markdown files. Both initialization
commits remain ancestors; Lean/reference/Overleaf sources are unchanged. No
build was needed. This handoff accompanies the focused HRV-map coefficient
checkpoint on `main`; its exact hash is in Git history. The increment makes
progress with an independently audited theorem and exact obstructions, not a
completion claim. The remote task above remains active.

The previous handoff, including winding and recurrence chronology and exact
old observer status, is [archived through DN transport](docs/archive/flip-component-handoff-through-dn-transport.md).
It is historical, not an active work list. Earlier checkpoint history remains
in Git and the linked documentation archive. The current goal is active and
has made progress; neither the full proof nor its Lean formalization is done.
