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
Latest continuation proves [left defect support on three-cover witnesses](docs/proofs/COMPONENT_DN_DIRECT_OVERLAPS.md#left-defects-vanish-on-three-cover-witnesses).
The required covers can occur at EITHER source endpoint of an actual left
comparison. At a genuine first-drop DN contact, if uw,td,wz cover at one
endpoint, the source preimages are connected. A nonzero left defect
therefore forces a redundant member of these three strict corners at EACH
endpoint; both three-corner alternating valuations vanish. In particular,
no such defect touches a mixed-acyclic source state. This does not imply
that the entire source components are mixed-cyclic or reducible. The
genuine six-vertex example already has a left boundary between distinct
source components, so coefficient repair remains essential outside this
scope. The full recurrence theorem is still incomplete.

The preceding continuation proves a [shared-branch left DN repair](docs/proofs/COMPONENT_INCOMING_EDGE_TRANSFER.md#closing-the-shared-covering-branch).
With uw,td,ut covering, t not reaching x, the stated absent shorts and
at least one covering outer anchor wz,xz, the source states A and
A-ut+tx are connected by actual flips, restoring all exterior. No bound
on cycle rank or competing paths is needed. A proper-arm preparation
and a delayed suffix restoration close the previous shared-branch gap;
an incoming cut exposes the second outer anchor. Cases with both outer
anchors redundant or with the other required covers failing remain open.
The general component theorem is still incomplete.

The preceding continuation proves [exact homogeneous DN completion](docs/proofs/COMPONENT_DN_SOURCE_ADDITIONS.md#completing-one-selected-edge-layer-of-the-direct-dn-image).
At fixed total selected-edge count k, three explicit families of pairwise
equalities determine the smallest source-component union U_k(C) whose
unmodified direct DN image is constant on all output components. The
same K/E identity has whole output components and coefficients 0,+1,-1.
All added source coefficients in this minimal union are forced to +1.
The remaining sufficient statement is independent reducibility of EVERY
extra member of U_k(C), not just the first deletable neighbor. It is open.
This theorem does not cover mixed-degree additions or rule out joint
output diamonds when the homogeneous source-addition route is insufficient.
The [NN companion](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#exact-completion-within-one-selected-edge-layer)
proves the same minimal-union result for V_k(C). Both recurrence types now
have full output reassembly for these explicit source unions. To isolate C
we still need independent reductions of their extra members. The K4
five-state example adds exactly the inactive two-state {fabe,fbce}; its
direct image is complete and subtracting it recovers the earlier example.
The preceding continuation proves the [forced-addition equations](docs/proofs/COMPONENT_DN_SOURCE_ADDITIONS.md#the-unmarked-upper-corner-forces-source-additions)
for the DD boundary exchanging the unmarked upper corner. A universal left
source-path lemma is false there: the two source preimages have opposite
invariant corner status, already in the genuine first-drop example 01222.
The added h-absent components all delete to D-h. Compatibility of their
forced coefficients, and with the remaining boundaries, is still open.
All left retained-e-prime comparisons now reduce to the R10 equations:
R00 has opposite defect, R01 lifts to R10 with the same defect, and
R11 cannot retain the redundant e-prime. This holds with arbitrary exterior.
The preceding continuation proves a [crossing-cover path repair](docs/proofs/COMPONENT_DN_RETAINED_EDGE.md#sliding-the-moving-edge-along-crossing-covers):
the moving short slides along an alternating path of covers across its
middle vertex, with arbitrary exterior and possibly both anchors redundant.
It is exact for paths that retain the full background Q at every step;
existence of that path is an additional hypothesis. The proposed shortcut
of transferring wt to xt is false in general: a five-vertex obstruction
has no x-to-t path and starts in a component active at the strict corner.
The retained-edge comparison itself is not refuted.
The preceding continuation proves an [incoming-arm transfer](docs/proofs/COMPONENT_INCOMING_EDGE_TRANSFER.md#three-covering-anchors-arbitrary-exterior-and-cycle-rank)
with three covering anchors, arbitrary exterior and arbitrary cycle rank.
Its DN corollary settles t10 and corresponding t00 constancy for a stated
class of left retained-e-prime comparisons. The general left repair remains.
The preceding [first-drop coverage](docs/proofs/COMPONENT_RECURRENCE_COVERAGE.md)
closes recurrence choice, forward direction and base cases for every ordinary
diagram. NN/DN whole-component reassembly remains the induction input.
The previous [two-anchor transfer](docs/proofs/COMPONENT_RIGHT_ARM_TRANSFER.md#arbitrary-exterior-transfer-with-two-covering-anchors)
and [DN preparation](docs/proofs/COMPONENT_DN_RETAINED_EDGE.md#clearing-the-obstructing-part-of-an-incoming-cut)
remain available for the local repair work.
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
- A crossing-cover path now gives a direct retained-edge repair of arbitrary
  length, retaining every background edge. The same construction applies to
  the left comparison when its analogous path exists. It permits redundant
  original anchors and other incoming/outgoing edges at the moving vertex.
  The full exterior determines every cover and reachability test.
- With both anchors covering, a covering outgoing arm transfers between
  them by an ordered cut, at arbitrary cycle rank and without adjacent roots.
  A redundant arm also transfers if the competing first neighbors are
  unreachable from the other root. In DN with r covering and t not reaching
  z, this clears all obstructing incoming branches provided their direct
  wv edges are absent. Shared direct branches remain outside this argument.
- With t<w<x<d<z and covers wz,xz,td,tw, the incoming arm tw transfers
  to tx, restoring all exterior. Cuts handle t-to-x and x-to-d paths;
  an incoming cut before suffix borrowing preserves both outer covers.
  In the left DN comparison, this applies after ut->tw [retain uw],
  provided the stated covers hold. A further outgoing cut treats e,f,r,td
  covering initially when w,x do not both reach d. The new shared-branch
  repair removes that reachability restriction and requires only one
  outer anchor covering, with e,td,ut covering and t not reaching x.
  Ordered cuts and delayed restoration handle arbitrary competing paths.
  A four-flip row separately treats
  e,td,wd,xd covering even with BOTH f,r redundant. First-drop saturation
  supplies td but not its cover. Other failed cover cases remain.
- The key missing lemma takes ONE component to a signed sum of WHOLE smaller
  components, with identical coefficients for K/E. Source additions are
  allowed when each added whole component is independently reduced to a
  smaller diagram. No balance, isolation or cycle-rank prerequisite is imposed.
- The direct DN formula now has an exact completion theorem at fixed k.
  Primary equalities lift every target k-edge flip; secondary equalities
  handle exits from target 00 at k-1 edges; deletion equalities handle
  q-removing H flips. These are necessary and sufficient for all output
  coefficients to be component-constant. The minimal union U_k(C) gives
  a proved whole-component recurrence for that UNION. Subtracting its
  other members still requires independent reductions; this is not yet
  a uniform recurrence for the individual C.
- NN has the analogous exact theorem, with two r-selected output layers
  and the r-absent q-exit comparisons. Its minimal union V_k(C) has a
  whole-component identity with unit signed coefficients. Independent
  reduction of all extra components in these NN/DN unions would complete
  the first-drop induction; that general reduction remains unproved.
- In a DD intermediate, a target e-prime-retained flip exchanging the
  unmarked upper corner h forces equal coefficients on an h-absent source
  component I and its paired h-selected component C. I always deletes to
  D-h. For prescribed selected-sector coefficients, this subsystem is
  solvable exactly when every I has a common coefficient among its selected
  neighbors. That compatibility is not yet proved. The 01222 example needs
  I11 added to C1; its complete eight-state target recurrence is verified.
- The ordinary order (n, number of natural edges, sum_j j*a_j) handles the
  proved NN/DN/DD/deletion targets and subsequent envelope normalization.
  DD now reduces to one-component DN, and ND to one-component NN, by
  unmarking the obstructing corner and keeping the same complete component.
  The first strict area drop supplies one of NN/ND/DN/DD in every connected
  saturated natural diagram outside the chain base case. Area012333 is ND.
  It suffices to prove NN/DN collection at these contacts, with at most the
  upper contact corner unmarked and selected by C. The equal-measure
  unmarking intermediate is never an induction input.
- That moment order is for FORWARD DN. The notebook uses reverse DN after
  marking a corner: its neutral move increases the moment. Its unmarked
  top row lowers doubled area, but that marking decrease cannot be counted
  again after normalization. The first-drop proof fixes FORWARD DN throughout;
  it does not use reverse DN as an induction step.

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
Recurrence choice is now settled by the first-drop theorem; do not reopen
it as a separate missing hypothesis or assume NN/DN/DD without ND suffice.
For the unmatched middle coefficient, first discard all routes settled by
the new exposure lemma. A possible nonzero coefficient must lose q before
f becomes a cover. The remaining task is to transport through that q-free
excursion, not to redo the final left/right exposing flip or impose a
cycle-rank classification. The two-anchor transfer now clears a whole set
of incoming obstructions; the residual direct common branch needs a general
repair. Its smallest example has an eight-flip path in the receipt, which
is evidence rather than the arbitrary-exterior proof. For left retained-e-prime,
the incoming-arm theorem now resolves the three-anchor covering case.
Do not infer that the containing strict edge remains a cover after the
initial e-retained flip: a w-to-d path can make it redundant. The new
one-sided cut handles this if x does not reach d. The new proper-arm
preparation and shared-covering-branch repair settle the remaining paths
when e,td,ut and one outer anchor cover. Delay restoring the shared x-arm
until after undoing the borrowed suffix and the competing-x-arm cut.
The direct common-branch row still handles covering wd,xd even when both
outer anchors are redundant. Other failed cover cases, especially redundant
td and both redundant outer anchors, and simultaneous full collection remain.
The new reverse preparation supplies the same conclusion from covers at
the tx endpoint: expose r first, then clear t-to-w paths using td. This
can make f redundant, but r remains covering, which is sufficient. The
remaining genuine-DN left defect is supported only on states with a
redundant member of {uw,td,wz} at both endpoints. Their alternating values
vanish, but a path through zero states can still connect nonzero states
with different coefficients. Do not infer whole-component constancy from
this statewise support restriction. Likewise do not seek a universal left
source path: the old genuine-DN six-vertex I_3/C boundary refutes it.
First check the new crossing-cover path criterion. If it fails, a local
repair must change some background edges; fixed-background searching cannot
help. Do not assume a general wt-to-xt transfer, even with x not reaching t.
The new obstruction is a proved separation, not merely a failed path search.
Identical preparation at both endpoints followed by a crossing-cover path
is also not universal: the basic five-vertex example already has a closed
four-background preparation component without such a terminal. Its ordinary
three-flip repair works by changing backgrounds differently along the path.
The bounded check finds a common preparation for 343 of 576 comparisons
in one fixed K6; do not turn this into a general normalization claim.
For the left DD boundary, stop searching for source paths across h-status.
Use the forced deletable additions and test their compatibility with the
other boundaries. All-sector constancy there reduces to the R10 equations.
The new homogeneous theorem performs that closure explicitly for all DN
boundaries at once. The next task is to prove that any further components
forced into U_k(C) are independently reducible, or to supply additional
output-diamond corrections where this stronger source-addition condition
does not suffice. Do not claim reducibility from the mere existence of the
closure, and do not impose it as a prerequisite on every allowed proof.
Apply the same analysis to the NN classes V_k(C); their output closure is
now proved too. Avoid repeating the bookkeeping or solving a fresh linear
system for each component: the remaining issue is the status of the extra
actual source components forced by the three pair families.

## Ownership and restrictions

Primary retains the academic Astra/high assignment on `main`, with unchanged
profile, role and service tier. Primary owns the outline, notes, documentation
routing, handoffs and external diagnostic. No additional worker or consultant
is authorized; no Lean/Lake builds are authorized. No manuscript proof or PDF
change is currently needed. The combinatorics-paper-writing skill was used
for the outline and note organization.

The preceding continuation added exact homogeneous source-addition sections
for DN and NN, together with their fixed checks and outline routing. Those
proof notes are unchanged in the current increment.

Current continuation owns an append-only incoming-edge transfer extension,
its outline routing, both handoffs and the external diagnostic: proper-arm
preparation, the shared-branch repair and exposure of one outer anchor. The NN/DN
completion notes and the retained-edge note are unchanged in this increment.
No previous independent review is asserted for new arguments.

Current endpoint continuation owns append-only sections of the incoming-edge
and direct-overlap notes, outline routing, both handoffs and the existing
external consumer. It checks the reverse left comparison and the resulting
support restriction on nonzero defects. Earlier proof text will be preserved.

The reboot terminated the old workers/consultant. Its saved Claude output
was empty; do not relaunch it. The pre-crash dirty retained-edge note was
preserved in full, extended and committed. The full previous handoff,
including its original dirty paragraph, is preserved in the
[recovery-history archive](docs/archive/component-recurrence-handoff-through-recovery-20260929.md).
Only archive-relative link targets were adjusted; all prose was retained.

## Checkpoints and verification

Proof checkpoint: `e5fb7eb` (either-endpoint covers and left defect support).
Current endpoint increment: reverse-endpoint left repair and the exact
three-corner support restriction on nonzero genuine-DN left defects.
The external consumer verifies fixed eight-/ten-flip paths with e redundant
at A but covering at B; the latter also starts with r redundant. The t-to-w
sweep makes f redundant in both, testing the need to expose r first.
In fixed area012233, all sixteen actual left comparisons are checked:
six meet the three-cover condition at A, two additional pairs only at B,
and the sole distinct-component pair fails it at both endpoints. Proofs
are uniform and do not use the finite check as a substitute. No Lean/Lake
build, maintained Rust edit, additional worker or independent review.
Both previous proof notes remain verbatim prefixes; the retained-edge note
is unchanged. All 58 local file links and `git diff --check` pass.

Proof checkpoint: `e765523` (shared-branch left DN repair).
Current increment proves the arbitrary-exterior left repair with one outer
anchor covering and exact restored endpoints. Fixed path checks:
nonshared proper arms, 11/21/22 flips; shared branch, 6/18/18 flips at
n=7,10,10; normalization followed by shared repair, 12 flips at n=9;
one redundant outer anchor in either direction, 8 flips each at n=8.
The external consumer checks every flip and strict edge. One bounded
seven-vertex search (587 states) found the six-flip central row; the proof
uses the explicit construction. The weaker claim without outer anchors
is false, with a selected-envelope separation proof in the same note.
The prior incoming-edge note remains a verbatim prefix; the retained-edge
note is unchanged. All 50 local file links and `git diff --check` pass.
No Lean/Lake build,
new worker, consultant, maintained Rust edit or independent review occurred.
Receipts are under `left-common-cone-20260929` in the request cache.

Proof checkpoint: `eb29be7` (exact homogeneous NN/DN completion).
Preceding increment: homogeneous DN and NN closure, minimality, unit output
coefficients and the exact criterion for completion using a specified
collection of independently reduced source components. Existing Rust
`dn_joint_span --component-closure --source-additions=active
--all-corner-deletions --skip-span` checks two fixed diagrams, with no new
computation implementation or build. Area012233: 736 comparisons, three
pair edges, 23 classes among 26 source components; all eleven tested
nondeletable components complete using deletable additions. Area01222:
34 comparisons, two pair edges, 12 classes among 14 components; all four
tested components complete. Every recipe checks exact K/E, full target
components and full deletion images. These checks do not prove general
reducibility of the extra source components.
The NN check uses the existing external consumer with one new bounded
option on K4: 32 states, 15 source components, eight target comparisons,
one pair edge and 14 classes. It verifies complete outputs and exact K/E
for every class, including the five-/two-state example. Its small external
Rust build passed; no Lean/Lake build or maintained Rust edit occurred.
Both old proof-note prefixes, 65 local file links and `git diff --check`
pass. No new independent review is claimed.

Proof checkpoint: `96c0bb0` (left-sector reduction and forced DD source additions).
Preceding increment: arbitrary-exterior R01-to-R10 left-flip lifting and exact
upper-corner source-addition equations. The fixed 01222 source has the two
four-state components with opposite h-status, two checked target flips
(10 and 00), and two oriented R01-to-R10 lifts. The established external
`dn_joint_span --left-repair --skip-span` replay passes all fourteen minimal
left components, with exact K/E and whole-component checks. A separate
fixed five-vertex test proves closure of the four common-preparation
backgrounds; its three undirected edges form the displayed path in the
receipt. These are small fixed checks, not a family scan. General
coefficient compatibility and full reassembly remain open.
Both extended note prefixes, 48 local file links and `git diff --check`
pass. The maintained Rust checkout remains unchanged.

The same target obstruction also occurs for C2 versus I21, of sizes six
and two, with the displayed selected-h representative connected unicyclic
and mixed-acyclic. That check passes; forest and mixed-cycle reductions do
not remove the need for this coefficient repair.

Proof checkpoint: `8f359bd` (crossing-cover lemma and the structural obstruction to
unrestricted outgoing-arm transfer).
Preceding increment: crossing-cover lemma and the structural obstruction to
unrestricted outgoing-arm transfer. The new construction applies to 56 of
576 retained-edge comparisons in a fixed complete six-vertex diagram,
including 10 with both anchors redundant; 168 actual flips pass. A fixed
ten-vertex state with exterior at the moving vertex passes a five-flip
path; no ten-vertex state space is enumerated. The same six-vertex fixture
has 60 failures of the stronger no-path arm-transfer claim, but zero
failures of the original 576 retained-edge comparisons. The five-vertex
separation proof uses a closed smaller-envelope family, independently of
these component counts. Its 15-state closed family and six explicit exposure
flips pass exact checks. Both old note prefixes, 42 local links and
`git diff --check` pass. The unrestricted proof remains incomplete.

Proof checkpoint: `b34b9a7` (arbitrary-exterior incoming-arm transfer and
left DN coefficient repairs). All 142 qualifying states at four fixed
six-vertex positions pass (684 actual flips). Two fixed n=10 states check
multiple suffixes and multiple arm bypasses (10 and 8 flips); no n=10
state space is enumerated. Four one-sided left-DN comparisons pass (22
flips), as do two common-branch rows (8 flips, including one with both
outer anchors redundant). Two further fixed states at n=8,10 check the
left outgoing cut (7 and 9 flips). The old incoming-edge
note is retained verbatim as a prefix; no new independent review is claimed.
Proof checkpoint: `85419e1` (first-drop coverage, local source correspondence,
and conditional completion from NN/DN reassembly). Six fixed diagrams verify all
four contact types, an interior first drop and the chain base case. The
checks include exact edge sets, strict-corner validity, adjacent-interchange
invariance and the decreasing measure. No states or components are enumerated.
Proof checkpoint: `9a209a8` (two-anchor transfer and DN incoming-cut preparation).
Proof checkpoint: `1b4f794` (general exposure and DD/ND inheritance).
Proof checkpoint: `e1ef5eb` (selected-suffix repair and notebook recurrence).
Pushed: `c9c0e3a` (preserved and extended retained-edge proof), `c458c8e`
(recovered notebook source map), `3eac539` (outline and note organization).
The preceding continuation's suffix row passes all instances
in the fixed n6/n7 fixtures (47 pairs, 196 actual flips) and one explicit
n11 fixture (five-edge suffix, 14 flips, no state-space enumeration).
Its recovered retained-edge note was preserved byte-for-byte as a prefix.
The preceding general exposure path passes all 801 applicable exits at three
fixed positions (4179 actual flips), plus a nonmaximal-long example and
a fixed ten-vertex state with six simultaneous bypasses (5 and 15 flips).
No larger state space is enumerated. The full proof treats arbitrary exterior.
The new transfer construction passes all 5328 applicable instances in one
fixed complete six-vertex diagram (11888 actual flips). The 222 instances
outside its hypothesis are not failures or a general coverage conclusion.
Two fixed DN states at n=8 and n=10 check the new preparation at both
endpoints (10 and 24 flips total), reducing to the proved two-cover lemma.
No state space at either larger size is enumerated. Both extended notes
preserve their previous contents verbatim as prefixes.
Current ownership: source-addition and NN redistribution notes, outline,
both handoffs and external consumer/receipts. Both old note contents are
preserved as prefixes. All other proof notes are unchanged.
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
Current receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/left-endpoint-covers-20260929/`.
Shared-branch receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/left-common-cone-20260929/`.
Homogeneous-completion receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/homogeneous-dn-closure-20260929/`.
DD-boundary receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/common-preparation-20260929/`.
Crossing-cover receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/outgoing-no-path-20260929/`.
Incoming-arm receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/incoming-anchor-20260929/`.
Coverage receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/first-drop-coverage-20260929/`.
Two-anchor receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/two-anchor-transfer-20260929/`.
Outline/archival checks: `/lake-cache/ai-projects/requests/VerticalStripLLT/component-recurrence-outline-20260929/`.
Notebook continuation: `/lake-cache/ai-projects/requests/VerticalStripLLT/dn-notebook-continuation-20260929/`.
Exposure continuation: `/lake-cache/ai-projects/requests/VerticalStripLLT/corner-exposure-20260929/`.
The archive also retains all prior build counts, axiom checks, source hashes,
review boundaries and the established push command. The current task does
not reopen the completed formalization or its builds.
