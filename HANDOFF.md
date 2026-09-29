# VerticalStripLLT handoff

## Current task — 2026-09-29

Develop an ordinary component e-positivity proof by pushing one complete
component through the recurrences, following the author's photographed
notebook. The user also requested note reorganization.

Start with [Component e-positivity by recurrence](docs/proofs/COMPONENT_RECURRENCE_OUTLINE.md).
It is the main proof outline and dependency map. Its worked NN example shows
split, local diamond repair, collection into whole smaller components, and
the resulting positive elementary expression. The detailed supporting notes
remain intact in the [component catalogue](docs/COMPONENT_NOTE_CATALOGUE.md).

Active goal: prove the general non-circular component e-expansion for
Motzkin/Dyck diagrams by the diagram-bijection/recurrence approach.
Latest continuation proves a uniform middle-state transfer whenever an
actual short-edge exit exposes the retained long. It handles both exit
sides, arbitrary exterior, and arbitrary cycle rank. See
[general exposure](docs/proofs/COMPONENT_CORNER_EXPOSURE.md).
The full recurrence proof is still incomplete; the goal remains active.

The proof target is K(C)=sum_(A in C) e_(lambda(A)). Carry the SAME signed
component recurrence for the coloring sum K and the HRV expression E.
Induction gives K=E; positivity comes from the original sum of elementary
terms, not from the signs of intermediate recurrence coefficients.

## Proved pieces and remaining obligations

- Whole-component corner marking/deletion and saturated-envelope normalization
  are proved. They retain arbitrary exterior and do not require saturation
  of every raw recurrence target.
- The direct NN and DN initial splits, endpoint maps and local diamonds are
  proved. Complete constructions exist for the worked examples; NN reassembly
  is complete in the stated connected unicyclic setting.
- Both left/right local exposure transitions are now proved without a
  unicyclic hypothesis, by a descending incoming cut and its inverse.
  This also settles any middle state with a q-preserving route to exposure.
  It does not control a q-free detour while the corner stays redundant.
- DN has several arbitrary-exterior retained-edge repairs, including the
  five conditions recovered at `c9c0e3a`, a 2m+4-flip selected-suffix
  construction, and reuse of a shorter covering pair of anchors. These
  settle the three displayed old uncovered paths in a general setting.
  The unrestricted retained-edge and left retained-e-prime repairs remain open.
- The key missing lemma takes ONE component to a signed sum of WHOLE smaller
  components, with identical coefficients for K/E. Source additions are
  allowed when each added whole component is independently reduced to a
  smaller diagram. No balance, isolation or cycle-rank prerequisite is imposed.
- The ordinary order (n, number of natural edges, sum_j j*a_j) handles the
  proved NN/DN/DD/deletion targets and subsequent envelope normalization.
  DD now reduces to one-component DN, and ND to one-component NN, by
  unmarking the obstructing corner and keeping the same complete component.
  This requires the general NN/DN steps with unmarked exterior corners.
  Complete recurrence coverage remains; NN/DN/DD alone miss area012333.
  The equal-measure unmarking intermediate is never an induction input.
- That moment order is for FORWARD DN. The notebook uses reverse DN after
  marking a corner: its neutral move increases the moment. Its unmarked
  top row lowers doubled area, but that marking decrease cannot be counted
  again after normalization. Keep directions explicit; coverage is not proved.

The separate ordinary/circular component theorem is already Lean-verified
by the word/finite-companion route. It is not an input to this new proof.
See [the completion audit](docs/COMPONENT_COMPLETION.md). Circular extension
of the recurrence proof requires its own justified reduction/order.

## Notebook and next action

The original sketch is
`/home/paxinum/Dropbox/Apps/Overleaf/LLT flip/llt pics.pdf`.
The [notebook map](docs/proofs/COMPONENT_NOTEBOOK_MAP.md) reconstructs
F(D0)=t F(I)+F(II)+t F(III), matching relation (8') in the archived author
source. It is distinct from our later `dn-local-cases.pdf`. The two corner
identity maps are whole-component bijections. The selected-e-prime sector
is reverse DN, with exact formula (N2). The individual middle-state swap
is false; the paired diamond gives the complete four-vertex proof.
Next collect one exact DN image into complete output components, keeping
the chosen direction and its induction order consistent. Do not count the
reconstructed aggregate top row as a proof of that collection.
For the unmatched middle coefficient, first discard all routes settled by
the new exposure lemma. A possible nonzero coefficient must lose q before
f becomes a cover. The remaining task is to transport through that q-free
excursion, not to redo the final left/right exposing flip or impose a
cycle-rank classification. Left retained-e-prime and full collection remain.

## Ownership and restrictions

Primary retains the academic Astra/high assignment on `main`, with unchanged
profile, role and service tier. Primary owns the outline, notes, documentation
routing, handoffs and external diagnostic. No additional worker or consultant
is authorized; no Lean/Lake builds are authorized. No manuscript proof or PDF
change is currently needed. The combinatorics-paper-writing skill was used
for the outline and note organization.

The reboot terminated the old workers/consultant. Its saved Claude output
was empty; do not relaunch it. The pre-crash dirty retained-edge note was
preserved in full, extended and committed. The full previous handoff,
including its original dirty paragraph, is preserved in the
[recovery-history archive](docs/archive/component-recurrence-handoff-through-recovery-20260929.md).
Only archive-relative link targets were adjusted; all prose was retained.

## Checkpoints and verification

Proof checkpoint: `1b4f794` (general exposure and DD/ND inheritance).
Proof checkpoint: `e1ef5eb` (selected-suffix repair and notebook recurrence).
Pushed: `c9c0e3a` (preserved and extended retained-edge proof), `c458c8e`
(recovered notebook source map), `3eac539` (outline and note organization).
The preceding continuation's suffix row passes all instances
in the fixed n6/n7 fixtures (47 pairs, 196 actual flips) and one explicit
n11 fixture (five-edge suffix, 14 flips, no state-space enumeration).
Its recovered retained-edge note was preserved byte-for-byte as a prefix.
The current general exposure path passes all 801 applicable exits at three
fixed positions (4179 actual flips), plus a nonmaximal-long example and
a fixed ten-vertex state with six simultaneous bypasses (5 and 15 flips).
No larger state space is enumerated. The full proof treats arbitrary exterior.
Current ownership: exposure note, route links in the two old NN notes and
direct DN note, DD/ND inheritance in the DD note, outline, both handoffs,
and the existing external consumer.
No Lean/Lake or manuscript build was run; no new worker or consultant.
Runtime registry and `codex mcp list` were inspected; Lean MCP is rooted at
RealRooted and unused. No model, account, worker or service-tier change.

Earlier exact row checks used the existing external Rust diagnostic on
areas011234 and0112345. All tested r-cover pairs are covered by the proved
conditions;190 neither-cover pairs at n7 lay outside those earlier conditions.
That count predates the new suffix/shorter-anchor results and has not been
recomputed. These are finite coverage data, not a general proof.
Maintained Rust is unchanged at
`d53fb193af3c69adedbd9ec8592f87235d809ffa`.

Recovery receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/dn-crash-recovery-20260929/`.
Outline/archival checks: `/lake-cache/ai-projects/requests/VerticalStripLLT/component-recurrence-outline-20260929/`.
Current source snapshots/checks: `/lake-cache/ai-projects/requests/VerticalStripLLT/dn-notebook-continuation-20260929/`.
Exposure continuation: `/lake-cache/ai-projects/requests/VerticalStripLLT/corner-exposure-20260929/`.
The archive also retains all prior build counts, axiom checks, source hashes,
review boundaries and the established push command. The current task does
not reopen the completed formalization or its builds.
