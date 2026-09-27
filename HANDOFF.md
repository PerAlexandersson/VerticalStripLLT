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

This continuation began clean at pushed `6b8a952` (strict-chain normalization).
Primary owns `docs/proofs/COMPONENT_ANCHOR_SLIDES.md` and the linked
normalization/status/index/handoff updates. Astra audited the cover tests and
signed semantic slide; Terra audited the two-chain geometry and the final
consecutive-chain proof. Both tasks are finished and were read-only/build-free.
No delegate owns editable files, and no new remote consultation was started.

## Current mathematical result and exact next step

The author's minimum-area induction remains the main route. The saturated
envelope is the minimum-area realization. Ordinary strict-corner deletion
partitions whole source components into ENTIRE smaller target components.
Alternating deletion and mixed-cycle cancellation localize a minimal component
defect on states acyclic after reversing strict corners. The exact HRV-map
coefficients are 0,+1,−1, with the proved outgoing-support count. These remain
in [corner differences](docs/proofs/COMPONENT_CORNER_DIFFERENCES.md) and
[exact HRV differences](docs/proofs/COMPONENT_HRV_DIFFERENCES.md).

The proved [strict-chain normalization](docs/proofs/COMPONENT_CHAIN_NORMALIZATION.md)
processes ALL strict chains, including singleton vertices, by decreasing
maximum. Its explicit idempotent map P replaces each root-decreasing normal
u→v by v→succ_S(u), using actual flips preserving mixed acyclicity. The
processed UNION is absorbing; this controls all cover tests. Every fiber is
connected and has an exact coloring sum with outside-interval constraints.
P is not constant on a whole component, and fiberwise K=E is false.

New [anchor-slide companion](docs/proofs/COMPONENT_ANCHOR_SLIDES.md):

- Normal edges between two chains occupy AB adjacencies in their merged
  vertex order. Consecutive AB slots cross strict corners ac,bd.
- For anchor exterior Q, the slide ab→bc→cd is actual exactly when Q has
  no all-normal paths a→b or c→d. Its middle is mixed-acyclic exactly
  when the mixed exterior has no path c→b. These are distinct tests.
- If the two chains are CONSECUTIVE in the order of all chain maxima,
  both tests hold for arbitrary anchor exterior. Hence any fixed number
  of selected slots can be moved to the first slots by actual slides.
  This proves connectivity of those selections, not component exhaustiveness.
- Subtracting the two residual diamonds gives, for BOTH X=K,E,
  R_X(Q+ab)−R_X(Q+cd)=Φ_ac^X(Q;ab,bc)−Φ_bd^X(Q;bc,cd).
  Both the middle state and the lower-normal-level term cancel. All right-hand
  terms lie in genuine smaller-area corner-deletion diagrams.
- These corrections still fail whole-component reconstruction separately:
  Φ_ac gives coefficients −1,0 at Q+bc,Q+cd, which are neighbors via bd
  in the ac-deletion diagram. The analogous mismatch holds for Φ_bd.
  The signed state identity is not yet a component recurrence.

Next: collect these slide corrections together with normal-long diamonds
and the existing DN packet rows, and prove constant signed multiplicities
on smaller complete components. Connections through mixed-cyclic states
must remain included; a third-chain diagnostic in the new note shows an
actual slide can pass through such a state. The complete ordinary and
primitive circular component formulas are still open. Minimum-area induction
and combinations of certified rows remain the strategy; a single-active-
component assertion is not required. The aggregate circular theorem remains
fully formalized.

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

This checkpoint changes only five Markdown files. Checks passed:
`git diff --check`, focused diff review, all 94 local links including heading
anchors, and both initialization ancestors. The proofs were independently
audited as described above; no Lean formalization is claimed.
The continuation made progress through actual slide connectivity and its
signed smaller-area identity, with the remaining obstruction made explicit.

The previous handoff, including winding and recurrence chronology and exact
old observer status, is [archived through DN transport](docs/archive/flip-component-handoff-through-dn-transport.md).
It is historical, not an active work list. Earlier checkpoint history remains
in Git and the linked documentation archive. The current goal is active and
has made progress; neither the full proof nor its Lean formalization is done.
