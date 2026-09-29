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
The [general retained-edge r-cover theorem](docs/proofs/COMPONENT_DN_RETAINED_EDGE.md#every-comparison-with-r-covering)
is proved with arbitrary exterior. Together with the earlier f-cover
result, it settles every comparison where either outer anchor covers
at Q+xs. Checkpoints `0cbefcc` and `dd844e9` are pushed to origin/main.

The latest continuation handles a [redundant containing wt](docs/proofs/COMPONENT_DN_RETAINED_EDGE.md#a-redundant-containing-edge-when-every-outer-bypass-passes-through-t).
Assume r,sz cover in Q, t reaches z, every w-to-z path in Q-f passes
through t, and every proper selected incoming ht reached from w has
h>s. Then Q+xs~Q+st even with arbitrary competing bypasses of wt.
Borrow st from the suffix, move xs to ws, and cut the interfering
incoming edges at t. Keep that cut while reversing the borrowed suffix;
only then use the exposed wt and restore the incoming cut. The direct
tz may be absent or redundant, and the incoming ht may be redundant.

The standalone prefix-push lemma cannot simply drop its wt-cover
hypothesis: a four-vertex closed two-state component gives a structural
counterexample. The new retained-edge repair uses its extra outer anchors
and the stated path conditions. Other wt bypasses, background-cover
failures, left comparisons and whole-component reassembly remain open.
The general recurrence proof is still incomplete.

The preceding continuation proves the [three-cover retained-edge theorem](docs/proofs/COMPONENT_DN_RETAINED_EDGE.md#the-lower-reachability-hypothesis-is-no-longer-needed):
wt covering in Q+xs and r=xz,sz covering in Q imply Q+xs~Q+st,
with NO hypothesis on w-to-s reachability, ws, tz or other suffix edges.
The new w-not-reaching-s case uses opposite incoming cuts, a lower
covering anchor, transfers of the prepared arms, and a prefix push.
It matches the complete target preparation before reversing that cut.

Together with the earlier either-outer-cover theorem, any still possible
retained-edge defect must also fail at least one of these three covers.
This is a pointwise support restriction, not independent reducibility
of a whole source component. Other cover failures, the left comparison
and whole-component reassembly remain open. The general recurrence
proof is still incomplete.

The preceding continuation proves [background-anchor transfer with an arbitrary suffix](docs/proofs/COMPONENT_RIGHT_ARM_TRANSFER.md#background-anchor-transfer-with-an-arbitrary-suffix):
if uc,vc cover in Q and neither root reaches d, then Q+ud~Q+vd,
with NO assumption on dc or any other suffix edge. For selected dc,
we transfer the proper incoming arms in increasing order. An obstructing
target branch is either cleared through its outer anchor or used to
advance the shared first endpoint. Each step removes one target arm;
after the transfer, the whole preparation reverses with actual covers.

The [retained-edge corollary (54)](docs/proofs/COMPONENT_DN_RETAINED_EDGE.md#removing-every-suffix-restriction-after-short-extension)
now closes EVERY suffix case when wt covers in Q+xs, w reaches s,
and r,sz cover in Q. Short extension gives Q+xt and the new theorem
gives Q+st. The previous selected-redundant and comparable-incoming-tail
restrictions are removed. The remaining retained-edge work concerns
failures of these lower-prefix or background-cover assumptions; the
left comparison and whole-component reassembly are also still open.
The general recurrence proof is not claimed complete.

The preceding continuation proves a [shared-first-edge suffix lemma](docs/proofs/COMPONENT_RIGHT_ARM_TRANSFER.md#a-shared-first-edge-with-an-arbitrary-suffix):
a redundant arm transfers across two roots when their competing routes
start with a shared covering pair. The suffix beyond that pair may have
arbitrary competing paths. A cut and path prepare dc; four central flips
move the obstructing arm before the preparation is reversed.

This proves [selected-direct-suffix transfer](docs/proofs/COMPONENT_RIGHT_ARM_TRANSFER.md#a-selected-direct-suffix-with-covering-proper-incoming-edges)
when the proper incoming tails reached from d are pairwise incomparable,
equivalently their incoming edges cover. The direct dc may be redundant.
The [retained-edge corollary (53)](docs/proofs/COMPONENT_DN_RETAINED_EDGE.md#a-redundant-tz-with-covering-proper-incoming-suffix-edges)
therefore permits redundant tz under the previous wt, w-to-s and background
r,sz hypotheses when all proper incoming suffix edges cover. Under those
same assumptions, a remaining suffix case needs BOTH redundant tz and
a redundant proper incoming hz. The six-vertex comparable-tail example
in the right-arm note shows why that earlier transfer row stops; the
new one-sided preparation above now resolves it.
This does not settle other failed-cover cases, the left comparison or
whole-component reassembly. The general recurrence proof remains open.

The preceding continuation proves [transfer with covers only in the background](docs/proofs/COMPONENT_RIGHT_ARM_TRANSFER.md#covers-in-the-background-and-an-absent-direct-suffix).
If uc,vc cover in Q, neither root reaches d, and dc is absent, then
Q+ud~Q+vd even with arbitrary d-to-c paths. Different incoming cuts at
the endpoints, followed by increasing covering-arm transfers, meet exactly.

Its [retained-edge corollary](docs/proofs/COMPONENT_DN_RETAINED_EDGE.md#an-absent-tz-with-arbitrary-paths-from-t-to-z)
settles absent tz whenever wt covers, w reaches s, and r,sz cover in Q.
The short extension reaches Q+xt; the new transfer finishes at Q+st.
Together with (51), this originally left selected redundant tz under those
other hypotheses; the latest result above now covers incomparable proper tails. The general both-redundant comparison, the unrestricted
left comparison and whole-component reassembly remain open.

The preceding continuation proves [arbitrary lower-prefix repairs](docs/proofs/COMPONENT_DN_RETAINED_EDGE.md#preparing-an-arbitrary-lower-prefix-inside-ws).
For x<a<s, assume ws,wt,xa,sz,tz cover, w reaches a, and r covers after
xs and xa are deleted. Preparing wa entirely inside [w,s] allows its
full restoration after xt becomes st. The edge wa may be absent or
redundant, with arbitrary competing routes; az need not cover or be selected.

A second [short-extension lemma](docs/proofs/COMPONENT_DN_RETAINED_EDGE.md#extending-xs-to-xt-along-an-arbitrary-lower-prefix)
proves Q+xs~Q+xt whenever wt covers and w reaches s, allowing absent or
redundant ws. With r covering in Q and sz,tz covering, two further flips
finish at Q+st. These results keep the general both-redundant case open
when the post-deletion, containing or suffix cover assumptions fail.
The unrestricted left comparison and whole-component reassembly remain open.

The preceding seven-flip lower-bypass repair is complementary: it requires
az covering and either w not reaching a or wa covering, but it allows
other x-to-z bypasses after xs and xa deletion. Its checkpoints `116254b`
and `629c34e` are pushed to origin/main. The full e-expansion proof remains
unfinished; a nonzero retained-edge defect has f,r redundant at Q+xs and
f redundant at Q+st, without an assertion about r at Q+st.

The [covering-interval construction](docs/proofs/COMPONENT_DN_RETAINED_EDGE.md#a-covering-interval-across-the-incoming-branch)
is now a proved stopping case of this general procedure, not an additional
hypothesis required of the original diagram. Its checkpoints `ccd1c2c`
and `beab543` are pushed to origin/main.

The preceding [r/wt-cover corollary](docs/proofs/COMPONENT_DN_RETAINED_EDGE.md#all-comparisons-with-r-and-wt-covering)
settles every retained-edge comparison with r and wt covering, using
the path-to-s and temporary-tz constructions. Checkpoints `e6d530e`
and `01092e6` are pushed to origin/main. Its temporary-tz restoration is
also used in the generalized terminal step from a to t.

The preceding [multiple-route repair](docs/proofs/COMPONENT_DN_RETAINED_EDGE.md#several-routes-entering-s)
handles selected, possibly redundant ys with arbitrary competing routes
and earlier incoming tails. It is used as a case of the new result.
Proof checkpoint `b4c577d` and metadata `51d0dfe` are pushed to origin/main.

The preceding continuation proves a [shared-branch prefix repair](docs/proofs/COMPONENT_DN_RETAINED_EDGE.md#a-shared-branch-reached-by-an-arbitrary-prefix).
With r,wt,yz covering, w reaching y and every w-to-s path using selected
ys, the retained-edge comparison has a 2m+3-flip repair along any saturated
w-to-y prefix of length m (in the remaining case t not reaching z).
The direct wy may be redundant; competing prefix paths are allowed.
Earlier temporary anchors may also become redundant, but removing ys
before reversing the prefix makes every inverse actual. A truncated
incoming cut permits yz to be initially redundant too. The remaining
s-reaching branch still includes multiple routes with no common selected
final edge, and redundant wt. General component reassembly remains open.

The preceding continuation proves a [reachable-anchor retained-edge repair](docs/proofs/COMPONENT_DN_RETAINED_EDGE.md#an-incoming-covering-anchor-with-a-path-to-t).
With r covering, any covering yz with x<y<t and y reaching t supplies
an actual source path, even if y<s and yt is absent. Stop the path sweep
one edge before t, use the appropriate local repair, and undo the sweep.
A truncated incoming cut also handles the largest obstructing branch
when it reaches t, including selected shared wv and initially redundant vz.
Outside the proved r-cover cases, the last obstructing branch must reach
s but not t, and the absent-direct-arm condition must fail. Cases with both
anchors redundant and general component reassembly remain open. A nonzero
retained-edge defect requires f redundant at both source endpoints, so
their one-corner alternating valuations vanish; this is statewise support,
not an independent reduction of either whole component.

The preceding continuation proves [left defect support on three-cover witnesses](docs/proofs/COMPONENT_DN_DIRECT_OVERLAPS.md#left-defects-vanish-on-three-cover-witnesses).
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
  The new reachable-anchor repair allows a path to t from a covering yz
  even with y<s. The largest obstructing incoming branch is also resolved
  if it reaches t, without requiring its direct wv to be absent.
  If it instead reaches s through a selected edge ys used by every
  w-to-s path, a covering wt now permits an arbitrary w-to-y prefix,
  including a redundant direct shared wy and competing prefix paths.
  The latest construction removes the common-edge condition: selected ys
  may be redundant, and incoming tails may precede y. Temporarily moving
  st to tz permits the full prefix to be restored despite those routes.
  The path-to-s extension removes selected ys as a hypothesis. Together
  these results settle all retained-edge comparisons with r,wt covering.
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
For the right retained-edge comparison, EVERY r-cover case is now proved.
Do not impose a wt cover, a selected ys, a direct shared arm, or an
initial covering-interval criterion. The common-ancestor argument supplies
the required interval, or a terminal at, by fork flips ending at or below
y<t. For B nonempty, expose yz at its largest member; the t-reaching
branch uses the earlier theorem, and the s-reaching branch uses this
new argument. Empty B is already handled by (C1).
The remaining right-hand defect has f and r redundant at Q+xs, and f
redundant at Q+st. We have not proved r redundant at the second endpoint.
Remember that r and wt are generally normal source edges, so their
redundancy alone does not permit whole-component corner deletion.
The new seven-flip lower-bypass row handles ws,wt,xa,az,sz,tz covering
with x<a<s and either w not reaching a or wa covering. Four flips retain
xs and ws, temporarily introduce wx, and restore xa; move wa to at before
this row when wa is initially selected, otherwise afterward. Remove tz
before retaining az to restore it. This permits r redundant even after
xs deletion. Longer w-to-a routes or redundant wa remain outside this row.
A shorter covering xv with t reaching v needs no selected wv.
The new lower-prefix preparation handles arbitrary w-to-a routes and
redundant wa provided r covers after xs and xa are deleted. First use
xs->wx[ws], wx->xt[wt]; prepare covering wa wholly below s, then use
xa->wx[wa], tz->st[sz], xt->tz[r], wx->xa[wa]. Undo the preparation:
its only changed exterior edges xt,st both end above s. No az cover
is needed. The short-extension lemma separately replaces xs by xt when
wt covers and w reaches s, even with ws absent or redundant; its inverse
uses w not reaching x and the other tested tails lying above x. If r
covers in Q and sz,tz cover, the usual two-flip closing row finishes.
These do not remove arbitrary post-deletion or suffix cover failures.
The full constructions remain in the retained-edge note; the general
both-redundant case and whole-component collection remain open.
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

Current containing-bypass continuation owns append-only retained-edge
arguments, fixed external-consumer diagnostics, outline routing and both
handoffs. It investigates a redundant wt while keeping the two background
anchors covering, preserving all prior proof text.

Current no-lower-path continuation owns an append-only retained-edge proof,
fixed external-consumer path checks, outline routing and both handoffs.
It uses different incoming cuts at the endpoints and a prefix push after
transferring the prepared arms. All previous proof text is preserved.

Current comparable-suffix continuation owns append-only one-sided shared-arm
and unrestricted background-anchor proofs, their retained-edge corollary,
fixed external-consumer checks, outline routing and both handoffs. Earlier
proof text will remain a verbatim prefix. The preparation clears a target
branch or advances the shared first endpoint.

Current selected-suffix continuation owns append-only shared-suffix and
selected-direct-suffix proofs in the right-arm and retained-edge notes,
fixed external-consumer checks, outline routing and both handoffs. The
construction restores its suffix only after exchanging the shared arm.
All prior proof text will remain a verbatim prefix.

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

Current retained-edge continuation owns an append-only reachable-anchor
extension and support corollary in the retained-edge note, the outline and
both handoffs. The external consumer checks fixed paths only. Every prior
retained-edge hunk will remain a verbatim prefix.

Current shared-prefix continuation owns an append-only retained-edge branch
lemma with arbitrary w-to-y paths, both handoffs, outline routing and fixed
checks in the external consumer. It preserves the complete prior note.

Current suffix-cover continuation owns append-only proofs in the retained-edge
and right-arm-transfer notes, fixed external-consumer diagnostics, outline
routing and both handoffs. It uses different incoming cuts at the endpoints.

Current lower-prefix continuation owns append-only arbitrary-prefix and
short-extension proofs, six fixed path checks and two bounded n8 discovery
comparisons in the external consumer, outline routing and both handoffs.
It preserves the complete prior retained-edge proof text.

Current both-redundant continuation owns the append-only shorter-suffix
and lower-bypass proofs, three fixed path checks and two bounded n7
comparisons in the external consumer, outline routing and both handoffs.
The complete prior retained-edge note remains a verbatim prefix.

Current common-ancestor continuation owns the append-only terminal-prefix
and common-ancestor lemmas and general r-cover theorem, three fixed
external-consumer checks, reorganized outline routing and both handoffs.
It preserves the complete prior retained-edge proof text.

Current covering-interval continuation owns the append-only retained-edge
lemma, six fixed external-consumer checks, reorganized outline routing
and both handoffs. It preserves the complete prior retained-edge note.

Current s-path continuation owns the append-only retained-edge path lemma
and r/wt-cover corollary, both handoffs, outline routing and fixed external
consumer checks. The full prior proof text remains a verbatim prefix.

Current incoming-s continuation owns the append-only multiple-route
extension of that lemma, outline routing, both handoffs and fixed consumer
checks. All previous retained-edge text remains a verbatim prefix.

The reboot terminated the old workers/consultant. Its saved Claude output
was empty; do not relaunch it. The pre-crash dirty retained-edge note was
preserved in full, extended and committed. The full previous handoff,
including its original dirty paragraph, is preserved in the
[recovery-history archive](docs/archive/component-recurrence-handoff-through-recovery-20260929.md).
Only archive-relative link targets were adjusted; all prose was retained.

## Checkpoints and verification

Current containing-bypass increment: four constructed paths pass 7,15,15,17
flips at n7/n12. They include absent/redundant tz, three competing incoming
edges at t (some redundant), and a three-edge borrowed suffix. Every
actual flip, strict edge and exact endpoint passes; no n12 state space
is enumerated. The four-vertex failed prefix-push extension is checked
by its exact two-state closure. One fixed n7 discovery pair visited 587
states and found the seven-flip row. Prior retained-edge text remains
a verbatim prefix; no Lean/Lake, worker, consultant, maintained Rust edit
or independent review. Proof checkpoint pending.

Current no-lower-path increment: four fixed n12 comparisons pass
21,29,25,33 flips with w not reaching s, absent/redundant tz and
comparable incoming tails. They include a tail between s,t and either
y=w or a lower covering anchor reached along competing prefix paths.
The selected-tz cases create st in the source preparation and xt in
the target preparation. Every actual flip, strict edge, exact prepared
state and final endpoint passes; no state space is enumerated.
The prior retained-edge note remains a verbatim prefix; the right-arm
note is unchanged. No Lean/Lake build, worker, consultant, maintained
Rust edit or independent review. Proof checkpoint: `310f2b7`.
Prior-proof preservation, 82 local file links and git diff --check pass.

Current comparable-suffix increment: two fixed n12 one-sided shared-arm
paths pass 22 flips each, with both root orders, a clearing below h,
an advance, and a later clearing above h. The recorded n6 pair passes
30 flips; two n12 background transfers with a chain/fork of incoming tails
pass 98/48 flips. Two n12 retained repairs pass 44/40 flips, with redundant
tz and a redundant proper incoming edge. Every actual flip, strict edge,
preparation invariant and exact endpoint passes; no state space is enumerated.
Both prior proof notes remain verbatim prefixes. No Lean/Lake build,
worker, consultant, maintained Rust edit or independent review.
Proof checkpoint: `543bd1b`. Prior-proof preservation, all 82 local
file links and git diff --check pass.

Current selected-suffix increment: four fixed n12 shared-suffix paths
pass 14,14,12,12 flips, with both root orders and absent/redundant internal
hd. Two fixed n12 selected-dc transfers pass 28/26 flips; two retained-edge
repairs with redundant tz and absent/redundant ws pass 36/32. Every actual
flip, strict edge, prepared-state equality and exact endpoint is checked.
No state space is enumerated. Prior proof text remains a verbatim prefix;
no Lean/Lake build, worker, consultant, maintained Rust edit or independent
review. Proof checkpoint: `9ee31e8`. All 77 local file links and
git diff --check pass.

Current suffix increment: two fixed n9/n12 background transfers pass
16/32 flips, including nonadjacent roots, multiple suffix paths and redundant
incoming edges. Two fixed n12 retained repairs pass 26/22 flips, with absent
or redundant ws and absent tz despite t reaching z. Every actual flip,
strict edge and exact endpoint passes; no large state space is enumerated.
The selected-dc five-vertex diagnostic has an eleven-flip path (71 states),
but no general selected-redundant-dc theorem is claimed. Both prior proof
notes remain verbatim prefixes. No Lean/Lake build, worker, consultant,
maintained Rust edit or independent review. Proof checkpoint: `d6e777a`.
All 71 local file links and git diff --check pass.

Proof checkpoint: `abd4506` (arbitrary lower-prefix repairs).
Current lower-prefix increment: four fixed n8/n12 paths under (47) pass
12,8,16,10 flips, including absent/redundant wa, competing routes and
redundant az. Two fixed n12 extension paths pass 12,6 flips to Q+xt and
14,8 flips to Q+st, with absent/redundant ws. Every actual flip, strict
edge and exact endpoint is checked; no n12 enumeration. Two n8 discovery
pairs visit 15046/11937 states and find eight-flip paths. No Lean/Lake,
worker, consultant, maintained Rust edit or independent review. Earlier
proof text remains a verbatim prefix.

Proof checkpoint: `116254b` (both-redundant lower-bypass repair).
Current lower-bypass increment: seven-flip arbitrary-exterior rows with
both outer anchors redundant and r redundant after xs deletion. Three
fixed n7/n11 paths pass, including an initially covering wa and exterior
shared descendants. Two fixed n7 discovery pairs visit 90/919 states,
yielding 3/7 flips. Every displayed flip, strict edge and exact endpoint
is checked; no n11 state enumeration. No Lean/Lake build, worker, consultant,
maintained Rust edit or independent review. Prior proof text is preserved.

Proof checkpoint: `0cbefcc` (general retained-edge r-cover theorem).
Current common-ancestor increment closes every retained-edge comparison
with r covering. Three fixed n12 paths have 15,15,17 flips; none has an
initial covering interval of the earlier required type. They test both
fork orders, the interval and terminal stopping cases, redundant selected
ys and missing ys. Every actual flip, strict edge and endpoint passes.
No state enumeration, Lean/Lake build, worker, consultant, maintained
Rust edit or independent review. Prior proof text remains verbatim.

Proof checkpoint: `ccd1c2c` (covering interval below t).
Current covering-interval increment: arbitrary prefix inside av with
r,yz,av covering, a reaching y and v<t reaching t; wt may be redundant.
Four fixed fork checks pass 7,7,7,9 flips, and two n12 interval checks
pass 13,9 flips. The latter include redundant wt,wy,ys and both branches
of the incoming-cut proof. One earlier ys-parking trial fails when v
reaches s; its receipt is retained and the final proof omits that step.
No state enumeration, Lean/Lake build, worker, consultant, maintained
Rust edit or independent review. Prior proof text remains verbatim.

Proof checkpoint: `e6d530e` (all retained-edge comparisons with r and wt covering).
Current s-path increment: a path y-to-s replaces the selected edge ys;
all r/wt-cover comparisons now follow. Three fixed n10/n12 paths have
15,19,19 flips, with suffix lengths 1,3,2. Every actual flip, strict edge
and exact endpoint passes. No state enumeration, Lean/Lake build, worker,
consultant, maintained Rust edit or new independent review. Prior proof
text remains a verbatim prefix. Sources and receipts are external.

Proof checkpoint: `b4c577d` (temporary-tz retained-edge repair).
Current incoming-s increment: arbitrary competing routes and redundant ys,
using temporary tz during prefix restoration. Four fixed n10/n11 paths
have 9,13,11,15 flips. They include an earlier incoming tail, later
incoming edges, and a temporary long that is redundant with st present.
Every actual flip, strict edge and exact endpoint is checked. No state
space is enumerated; no Lean/Lake build, worker, consultant, maintained
Rust edit or independent review occurred. Earlier proof text remains a
verbatim prefix.

Proof checkpoint: `9a164b3` (shared retained-edge branch with arbitrary prefix).
Current shared-prefix increment: arbitrary w-to-y paths in the stated
shared-branch case, with redundant wy and competing prefix paths allowed.
Two fixed n10 examples pass nine-flip paths, including temporarily
redundant earlier anchors. One fixed n11 example includes an initially
redundant yz and the truncated incoming cut; its path has eleven flips.
Every actual flip and exact endpoint is checked. No state space is
enumerated and no Lean/Lake build, worker, consultant, maintained Rust
edit or independent review occurred. The old retained-edge prefix is
preserved in full.
All 54 local file links and `git diff --check` pass.

Proof checkpoint: `08259c0` (retained-edge reachable-anchor repair).
Preceding retained-edge increment: a covering yz and any y-to-t path give
the repair with arbitrary exterior; a truncated incoming cut handles the
largest bad branch reaching t. Three fixed n10 paths (nine flips each)
check last predecessors on both sides of s and an outgoing cut with
absent/redundant hs. One fixed n11 path (eleven flips) has a selected
shared arm and initially redundant auxiliary anchor. Every flip, strict
edge and exact endpoint is checked; no state-space enumeration is used.
The prior retained-edge text remains a verbatim prefix. No Lean/Lake
build, worker, consultant, maintained Rust edit or independent review.
All 52 local file links and `git diff --check` pass. The incoming-edge
and direct-overlap proof notes are unchanged in this increment.

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
Current receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/retained-containing-bypass-20260929/`.
No-lower-path receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/retained-no-lower-path-20260929/`.
General-suffix receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/retained-comparable-suffix-20260929/`.
Incomparable-suffix receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/retained-selected-suffix-20260929/`.
Absent-suffix receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/retained-suffix-covers-20260929/`.
Lower-prefix receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/retained-lower-prefix-20260929/`.
Lower-bypass receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/retained-both-redundant-20260929/`.
General r-cover receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/retained-common-ancestor-20260929/`.
Covering-interval receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/retained-covering-fork-20260929/`.
Path-to-s receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/retained-s-path-20260929/`.
Multiple-route receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/retained-incoming-s-20260929/`.
Shared-prefix receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/retained-shared-prefix-20260929/`.
Reachable-anchor receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/retained-reachable-anchor-20260929/`.
Either-endpoint receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/left-endpoint-covers-20260929/`.
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
