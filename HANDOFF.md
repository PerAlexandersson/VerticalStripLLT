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

Preceding pushed checkpoint: `6668c6d`, endpoint flip maps and shared corner
correction space. The current increment records explicit ordinary DN component
completion, its conditional induction, exact boundary diagnostics, the audited
Aristotle return, and consolidation of this handoff. Primary owns the new
`docs/proofs/DN_COMPONENT_COMPLETION.md`, linked status/index/recurrence notes,
Aristotle ledger, this handoff and its archive.

The user explicitly authorized parallel brainstorming. Astra audited actual
flip-path issues; Terra audited the completion reconstruction and ordinary
induction measure; Luna explored a projection approach. All were read-only
and build-free, and their lanes are released. No delegate owns editable files.
The projection proposal did not solve the gap: statewise redundancy cannot
be treated as an entire inactive component.

## Current mathematical result and exact next step

The main route remains the author's component-through-recurrences argument.
The [DN completion note](docs/proofs/DN_COMPONENT_COMPLETION.md) defines a
finite graph J on whole source components. Its generators impose the local
middle pairing and the equations required by every actual target flip.
For every union of J-connected classes, explicit signed DN multiplicities
preserve BOTH coloring and HRV sums and are constant on whole target
components. The proof checks every target flip type. Its zero-stratum case
uses both source00→01 and target00→10 cover-preserving lifts.

A sufficient remaining assertion is:

> Each J-connected class contains at most one f-active source component,
> where f-active means the chosen strict corner f is a cover somewhere.

If true, complete an active component C by the other components in its class.
Those are f-inactive, hence known by strict-f deletion. Transport the completed
union and subtract these solved corrections. The ordinary DN target decreases
M=Σ j*a_j at fixed doubled area; inactive deletion lowers doubled area.
Thus lex `(doubledArea,M)` justifies this conditional DN step. Other recurrence
transports and wrapping circular steps still require their own arguments.

Isolation is OPEN. It passed two fixed saturated n=6 fixtures: respectively
116 and 26 source components give 71 and 19 completion classes, with no class
containing two active components and every target image component-constant.
These are exact finite evidence, not a proof. The same fixtures disprove
using only source-middle joins. A Rust-checked boundary example disproves
raw r-absent residual constancy and exhibits an inactive correction.

Next: prove or refute isolation for this SPECIFIC graph. The current path
lift handles exterior 10 paths, but an active path can remove q, pass through
00 states where f remains redundant, and expose f later. This excursion is
unresolved. Do not confuse an inactive state with an inactive whole component.
If isolation fails, retain the more general signed target/deletion framework
and shared corner diagram. Do not restart a broad scan or scaffold conditional
Lean statements in place of proving the structural claim.

The prose forest-component theorem, endpoint/gluing results and winding
reductions remain available; their map is in the status note. AU_prime is
auxiliary, not a prerequisite of the recurrence route. The aggregate circular
formalization is complete; the primitive circular COMPONENT theorem is open.

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
input/result hashes and exact test scope. The bounded Python orchestration
reuses the earlier audited `diamond-exploration/probe.py` model; no new graph
enumerator or polynomial family was introduced. The existing Rust
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

Whitespace and focused-diff checks passed; 91 local links in the eight
changed Markdown files resolve. Both initialization commits remain ancestors
of HEAD, and no Lean or reference diff exists. No Lean build is required for
these documentation-only changes. Push the coherent checkpoint on `main`;
record the successful commit in the final response.

The previous handoff, including winding and recurrence chronology and exact
old observer status, is [archived through DN transport](docs/archive/flip-component-handoff-through-dn-transport.md).
It is historical, not an active work list. Earlier checkpoint history remains
in Git and the linked documentation archive. The current goal is active and
has made progress; neither the full proof nor its Lean formalization is done.
