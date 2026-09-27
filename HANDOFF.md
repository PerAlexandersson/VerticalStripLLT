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
No Lean, shared Rust, reference or Overleaf source changed; no compilation
was needed or run in this increment.

This continuation began clean at pushed `b8a1875` (anchor slides), following
`6b8a952` (strict-chain normalization). Primary owns the new
`docs/proofs/COMPONENT_MIXED_CLOSURE.md`, the normal-long continuation in the
chain-normalization note, and linked handoff/status/index/proof clarifications.
Astra audited the closure coefficient proof and its Boolean fibers. Terra
provided the normal-long endpoint classification and a cover obstruction.
Both tasks finished read-only/build-free; primary checked their results.
No delegate owns editable files, and no new remote task was started.

## Current mathematical result and exact next step

The author's minimum-area induction remains the main route. The saturated
envelope is the minimum-area realization. Ordinary strict-corner deletion
partitions whole source components into ENTIRE smaller target components.
Alternating deletion and mixed-cycle cancellation localize a minimal component
defect on states acyclic after reversing strict corners. Exact HRV-map
coefficients are 0,+1,−1, with the proved outgoing-support conditions. See
[corner differences](docs/proofs/COMPONENT_CORNER_DIFFERENCES.md) and
[exact HRV differences](docs/proofs/COMPONENT_HRV_DIFFERENCES.md).

The [strict-chain normalization](docs/proofs/COMPONENT_CHAIN_NORMALIZATION.md)
uses actual flips and gives deterministic anchors and connected fibers.
The [anchor slides](docs/proofs/COMPONENT_ANCHOR_SLIDES.md) are unconditional
for consecutive chains in chain-max order. Their paired residual diamonds
cancel the intermediate and lower-normal-level terms, leaving signed
smaller-area corrections for both K and E. These corrections separately
fail whole-component reconstruction across a surviving strict-long flip.

New [mixed-closure companion](docs/proofs/COMPONENT_MIXED_CLOSURE.md):

- For arbitrary disjoint FORWARD N,F, a forward normal uv implied by a path
  in N∪F^op can be inserted without changing the FULL alternating HRV-map
  sum or the alternating coloring enumerator. No corner geometry is needed.
- The HRV proof uses the exact map coefficients: in the equal-map case a
  witnessing path must start with an old equal-map normal, so insertion
  cannot change the unsupported-tail set. Support and signs agree in both
  directions, before and after insertion.
- Saturating the allowed normal edges by mixed reachability gives an
  extensive, monotone, idempotent closure preserving both residual valuations.
- For an acyclic closed set C, its fiber is EXACTLY the Boolean interval
  [B,C], where B consists of the forward Hasse edges of the mixed order.
  Every reverse Hasse edge is already supplied by F^op.
- These identities give new common semantic zero relations for redistributing
  smaller-area corrections. Component intersections with a closure fiber
  are counted honestly; whole-fiber or binomial multiplicities are NOT assumed.

The chain-normalization note also records all six normalized endpoint cases
for a normal-long flip. Normalizing its exterior can destroy its cover test.
A hand-checked nonsaturated fixture proves this; the stronger saturated case
is not decided by that diagnostic. Mixed-closure preservation and actual-flip
normalization are separate operations and must not be conflated.

Next: use the mixed-closure zero relations together with normal-long diamonds,
slide corrections and DN packet rows to make the final signed multiplicities
constant on smaller ENTIRE components. Closure fibers alone do not give
component identities. Connections through mixed-cyclic states remain included.
The complete ordinary and primitive circular component formulas remain open;
the aggregate circular theorem is fully formalized. No single-active-component
assertion is required by the signed recurrence approach.

## Consultation outcome and verification provenance

Aristotle project `3fd0ed1d-ba60-404b-8b99-beaaae1c4d08`, task
`4aa8cbee-7eb5-4d15-ba07-7806c7fa540a`, is terminal **COMPLETE**. The full
return explicitly does NOT prove the residual identity or a uniform recurrence.
Primary downloaded and read `RESIDUAL_BRIDGE.md`; exact archive/input/proof
hashes belong in [the ledger](docs/ARISTOTLE.md).

Primary accepted the residual diamond calculus and checked its explicit
obstruction: weighted corner-long pairs in the already-proved K4 tree
component force target multiplicities t,0,1−t along two actual flips.
Thus corner-long pairs alone cannot reconstruct whole smaller components.
The owned HRV note records the proof. Shorts stay NORMAL in the valid
corner-deletion target; they cannot be arbitrarily declared strict.
No generated Lean or experiment source was integrated.

Both observers `83731`, `72078` ended after stream interruptions. Direct SDK
reads revalidated the same remote task and later confirmed its terminal state;
no replacement task was started. The remote reports its n=7 scan timed out
and no enumeration remains. Scans were outside the requested scope from the
start; their claims about small cases are not used as proof. No live remote
task, observer or delegate remains, and no new consultation is queued.

External requests root: `/lake-cache/ai-projects/requests/VerticalStripLLT/`.
This return is in `mixed-corner-residual/`. Earlier bounded local predicate
receipts and Rust capability audits remain documented in the linked notes.
No new computation engine, polynomial family, shared Rust edit or build was
introduced in this increment. The Overleaf recurrence sketches were reread
without edits; their global component regrouping obligations remain open.
AXLE is registered; Lean MCP targets RealRooted; Aristotle uses its installed
CLI/SDK. No credentials were printed or committed.

## Checks and history

This checkpoint changes only seven Markdown files. Proof audits, focused diff
review, `git diff --check`, all 106 local links (including heading anchors),
and both initialization-ancestor checks passed. No new computation
engine, scan, polynomial sequence, Lean source or compilation was introduced.
The previous goal turn made progress (`b8a1875`); this continuation adds a
uniform semantic companion and identifies its exact acyclic closure fibers.
Neither checkpoint claims the full component proof.

The previous handoff, including winding and recurrence chronology and exact
old observer status, is [archived through DN transport](docs/archive/flip-component-handoff-through-dn-transport.md).
It is historical, not an active work list. Earlier checkpoint history remains
in Git and the linked documentation archive. The current goal is active and
has made progress; neither the full proof nor its Lean formalization is done.
