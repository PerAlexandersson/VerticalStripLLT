# Circular representation and source map

The independent Astra review and primary source/API audit selected this
architecture on 2026-09-26. Completed milestones are now indexed in
[CIRCULAR_STATUS.md](CIRCULAR_STATUS.md); downstream work appears in
[CIRCULAR_GOALS.md](CIRCULAR_GOALS.md). The original dated plan and source
hashes are retained in the [planning archive](archive/completed-plans/circular-initial-architecture.md).

## Source and scope

The author supplied the Overleaf project at
`/home/paxinum/Dropbox/Apps/Overleaf/LLT flip/`. Its current substantive source
is `main.tex`; the earlier `old-main.tex` path is now absent, and `new-main.tex`
is also present. Old line numbers and hashes describe the initial audit, not
the current manuscript. The committed ordinary reference under `references/`
remains immutable.

The aggregate theorem `thm:circular-e-expansion` is proved in Lean; see
[CIRCULAR_COMPLETION.md](CIRCULAR_COMPLETION.md). The complete-component
claim `conj:circular-component-h` is downstream and remains unproved.
The authorized manuscript TODO for the missing neutral-termination argument
was recorded previously; its Lean proof is now complete. Manuscript incorporation
of the completed proofs remains a separate writing task.

## Adopted finite model

- `CircularArea n` stores positive circumference, entries below n, and the cyclic
  area inequality. An edge is its head residue and positive natural length.
  Opposite natural arcs are distinct edge instances.
- `Diagram` restricts strict edges to corners. The coloring polynomial is the
  finite sum over strict-compatible colorings, weighted by normal ascents.
- `Orientation` selects a subset of normal edges; strict edges are always
  selected. Admissibility is acyclicity of this selected directed relation.
- HRV is the greatest reachable endpoint on the integer cover, then projected.
  It is not the maximum residue. Paths may cross a chosen cut several times.
- `XPoly m = MvPolynomial (Fin m) (Polynomial ℤ)` and
  `EExpansion = MvPolynomial ℕ+ (Polynomial ℤ)` reuse the ordinary coefficient
  and elementary-evaluation interfaces. Equalities quantify over every m.
- `shiftedOrientationExpansion` is independently defined from actual HRV fibers.
  It is not a recursive object renamed as the coloring LLT.
- The primary measure is doubled geometric half-square area,
  `2 * sum area - strict.card`. Neutral moves use strict-chain rank second.
  Local DD elimination uses auxiliary contact-count bookkeeping; mixed
  DD/neutral segments use `(strict.card, strictRank)` for termination.
- User clarification: reduce to one-bounce relations before projecting the
  geometry to the circle; genuine strict loops vanish. Do not assume a global
  multi-bounce R4 identity for periodically identified contact tracks.

A general symmetric-functions library, a global ordinary cut, and a no-wrap
hypothesis are not required by this architecture. The weak/complete and
strict/elementary component formulations are related by omega; that finite-degree
translation remains part of the downstream component work.

## Source correspondence

| Manuscript material | Repository interface |
| --- | --- |
| Circular natural graph and strict corners | `Circular/Diagram.lean`, `Coloring.lean` |
| Selected-order expansion | `SubsetExpansion.lean`, `OrientationSum.lean` |
| Lifted highest reachable vertex | `ReachableMaximum.lean`, `HRV.lean` |
| R1, direct NN, direct DN | `CornerDiagram.lean`, `FirstBounceRecurrences.lean`, `SecondBounceRecurrences.lean` |
| Neutral termination and full DN geometry | `NeutralTermination.lean`, `DNRealization.lean`, `GeometricArea.lean` |
| Full aggregate expansion | `Circular/Expansion.lean`; interior overlap closed by `InteriorReversalReduction.lean` |
| Full lifted flips and components | `LiftCover.lean`, `Flip.lean`, `ComponentSemantics.lean`; [scope](CIRCULAR_FLIPS.md) |

Primary owns strategy, integration, and globally serialized `lake-workspace`
builds. Bounded delegated edits have disjoint ownership recorded in HANDOFF;
remote proofs are candidates until locally checked. No reference files are edited.
