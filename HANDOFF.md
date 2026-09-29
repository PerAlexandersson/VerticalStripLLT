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

Latest continuation reconstructs the notebook top row and proves its two
whole-component identity sectors, plus an exact reverse-DN initial split.
The retained-edge note now also proves a repair along a selected suffix of
arbitrary length. The full recurrence proof is still incomplete.

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
  Complete recurrence coverage and the componentwise ND step remain to be
  integrated. NN/DN/DD alone miss area012333. Unmarking intermediates are not
  automatically smaller induction inputs.
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

Pushed: `c9c0e3a` (preserved and extended retained-edge proof), `c458c8e`
(recovered notebook source map), `3eac539` (outline and note organization).
This continuation modifies the two proof notes, outline and handoffs, and
the existing external Rust consumer. The suffix row passes all instances
in the fixed n6/n7 fixtures (47 pairs, 196 actual flips) and one explicit
n11 fixture (five-edge suffix, 14 flips, no state-space enumeration).
The recovered retained-edge note is preserved byte-for-byte as a prefix;
all 27 links in the touched notes resolve and `git diff --check` passes.
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
The archive also retains all prior build counts, axiom checks, source hashes,
review boundaries and the established push command. The current task does
not reopen the completed formalization or its builds.
