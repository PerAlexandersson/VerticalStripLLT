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

This continuation began clean at pushed `1863bad` (mixed closure). Primary
owns `docs/proofs/COMPONENT_MIXED_POSET.md`, the mixed-closure and
chain-normalization updates, and their linked handoff/status/index changes.
Astra audited optional-edge absorption, the permutation formula and a
closure-fiber obstruction. Terra supplied the saturated cover obstruction.
Both tasks finished read-only/build-free; primary checked all integrated
arguments. No delegate owns editable files and no new remote task was started.

## Current mathematical result and exact next step

The author's minimum-area induction remains available: the saturated envelope
is minimal, ordinary strict-corner deletion partitions whole components into
ENTIRE smaller components, and alternating differences cancel mixed-cyclic
states. The exact HRV-map coefficients, strict-chain normalization, anchor
slides, mixed closure and DN completion remain in the
[component status](docs/FLIP_COMPONENT_STATUS.md) and its linked proofs.

New [labeled mixed-poset companion](docs/proofs/COMPONENT_MIXED_POSET.md):

- If a reversed optional edge is implied by the old mixed graph, inserting
  it changes the full HRV-map alternating sum by a minus sign. The same is
  true for the coloring sum. The coefficient proof works before OR after
  insertion and needs no corner geometry.
- Thus J=(−1)^|F|H and Z=(−1)^|F|K_F depend only on the LABELED mixed
  poset. All non-Hasse edges can be removed with the proved sign rules.
- Both valuations satisfy exact incomparable-pair resolution, so both refine
  as sums over the same linear extensions, each counted once.
- For a total mixed order π, the full signed map J is indexed by partitions
  into contiguous increasing-then-decreasing mountain blocks with decreasing
  maxima. Each block maps to its maximum; the sign is (−1)^(internal descents).
- At elementary level this gives a recurrence at the largest label. If its
  prefix is not increasing, J vanishes. Otherwise, if that label is at r and
  the following decreasing run ends at s, j_π=Σ_(ℓ=r)^s (−1)^(ℓ−r)
  e_ℓ j_(suffix after ℓ). Labels, not just descent sets, matter.
- For each complete ordinary component A, BOTH K(A) and E(A) therefore have
  exact permutation expansions with the SAME multiplicity m_A(π), counting
  source states having π as a linear extension. Their total-order valuations
  are generally different, so this refinement is not the component theorem.

Two stronger shortcuts are now ruled out. In the saturated two-K4 articulation
example, the size-five level of one live Boolean closure fiber splits across
components with block counts (3,2) and (2,3); the states are connected,
nonforest and not pointwise chains. The mixed-closure note records it.
Also, even SATURATED diagrams admit actual normal-long flips whose normalized
long becomes noncover. The new fixture replaces the weaker nonsaturated one
in the chain-normalization note. Saturation does not repair that step.

Next: construct a component-preserving redistribution of compatible
permutations matching the largest-label/mountain recurrence, or use the new
poset identities to regroup corner-recurrence corrections into smaller
ENTIRE components. Keep original component labels and actual intersection
multiplicities throughout. Individual mixed orders or closure fibers are not
solved equality cases. The complete ordinary and primitive circular component
formulas remain open; the aggregate circular theorem is fully formalized.

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

This checkpoint changes only six Markdown files. Proof audits, focused diff
review, `git diff --check`, all 101 local links including heading anchors,
and both initialization-ancestor checks passed.
No new computation engine, scan, polynomial sequence, Lean source or build
was introduced. The previous goal turn made progress (`1863bad`); this
continuation adds the labeled-poset and exact permutation formulas and
rules out two stronger shortcuts. The full goal is not complete.

The previous handoff, including winding and recurrence chronology and exact
old observer status, is [archived through DN transport](docs/archive/flip-component-handoff-through-dn-transport.md).
It is historical, not an active work list. Earlier checkpoint history remains
in Git and the linked documentation archive. The current goal is active and
has made progress; neither the full proof nor its Lean formalization is done.
