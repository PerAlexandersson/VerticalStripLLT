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

Preceding pushed checkpoint: `f89251a`, explicit ordinary DN component
completion and its conditional induction. That goal turn made progress.
The current increment follows the user’s minimum-area component induction:
make the saturated-envelope measure exact, allow signed packet combinations
modulo ALL smaller components, and audit crossing-corner boundary transport.
Primary owns
`docs/proofs/DN_COMPONENT_COMPLETION.md`, linked status/index/recurrence notes,
Aristotle ledger, this handoff and its archive.

The user explicitly authorized parallel brainstorming. Astra explored
crossing-corner paths; Terra audited the new crossing sweep and minimum-envelope
proof. Earlier Luna projection notes remain partial. All were read-only
and build-free, and their lanes are released. No delegate owns editable files.
The projection proposal did not solve the gap: statewise redundancy cannot
be treated as an entire inactive component.

## Current mathematical result and exact next step

The user explicitly proposes induction on the smallest-area diagram realizing
an entire component, with strict corners and signed combinations of smaller
components. This is the main route. The
[recurrence note](docs/proofs/FLIP_COMPONENT_INDUCTION.md) now proves that the
saturated selected-edge envelope is the unique minimum-area realization on
fixed vertex order. The proof includes circular lifted edge orbits: delete
absent outer corners to construct the envelope, then strictify its selected
corners. The exact doubled-area difference is 2d+c_H−|S|, with d omitted
natural edges and c_H envelope corners. Both whole-component semantics survive.

Any component with ANY strict corner redundant throughout is known by
smaller-area deletion. For the remaining components, certified recurrence
packet rows need only span over Q. The proved generation lemma clears
denominators and uses torsion-free polynomial coefficients to recover every
individual identity. One unknown component per packet is sufficient but NOT
required. Constructing this uniform generation remains the full proof target.

The [DN completion note](docs/proofs/DN_COMPONENT_COMPLETION.md) supplies one
explicit family of packet rows. Every J-class union transports to whole target
components preserving both K and E. Its stronger isolation proposal, at most
one f-active component per J-class, remains open and auxiliary to the more
flexible signed generation. Ordinary DN decreases M=Σ j*a_j at fixed doubled
area; strict-corner deletion decreases area. Circular wrapping steps and other
recurrences still need their appropriate component transports.

New proved local step: if f=wz is a cover and an actual crossing-corner flip
aw→wb (a<w<b<z) has bz absent, a finite sweep of reverse f-long flips makes
that crossing flip preserve f-cover. The attachment proof checks actual covers,
normality and termination. Astra proposed it; primary and Terra audited it.
The exception bz selected creates both attachments and can lie in a component
active at both corners. No whole-component reduction follows from that local
redundancy. This is the concrete boundary to investigate next.

A single new fixed two-crossing-corner diagram, areas (0,1,2,3,3,4,4,4),
strict {03,15,26,37}, passed J-isolation on all 131072 source states:
1395 source components, 76 f-active, 654 J classes, no active collision.
This is finite evidence only. A broader relaxed-f-exchange graph does not
contain all J-generators, so it cannot replace the DN argument directly.
No broad area-sequence scan or new enumeration engine was introduced.

Next: construct signed component recurrences at minimal envelope area, using
all smaller-component corrections and the crossing sweep. Proving J-isolation
would suffice for its DN step, but do not insist on it if several packet rows
can isolate the component instead. Inactive states must never be confused
with inactive ENTIRE components. No new conditional Lean scaffold is needed.
The general ordinary and primitive circular component formulas remain open;
the aggregate circular formalization is complete.

## Consultations and computation

Aristotle project `3fd0ed1d-ba60-404b-8b99-beaaae1c4d08`, task
`16154bfd-ae04-49cd-9549-6d0a931f9309`, is terminal **COMPLETE**. Its return
explicitly does not prove the component theorem. Primary downloaded and
read the full result, verified the corrected five-vertex packet, and recorded
scope/convention corrections in [the ledger](docs/ARISTOTLE.md). Its n=7 scan
was terminated with no result. No active remote task or observer remains.
Earlier Claude and Aristotle consultations are terminal; no new Claude was
launched. Exact request/result hashes and receipts belong in the ledger.

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

Whitespace, focused-diff and local-link checks passed: 39 links across the
four changed Markdown files resolve. Both initialization commits remain
ancestors of HEAD; no Lean or reference files changed. No build was needed.
Push the coherent checkpoint on `main` and report its commit. All external
diagnostics and read-only delegates from this increment are terminal.

The previous handoff, including winding and recurrence chronology and exact
old observer status, is [archived through DN transport](docs/archive/flip-component-handoff-through-dn-transport.md).
It is historical, not an active work list. Earlier checkpoint history remains
in Git and the linked documentation archive. The current goal is active and
has made progress; neither the full proof nor its Lean formalization is done.
