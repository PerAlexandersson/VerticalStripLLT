# VerticalStripLLT handoff

## Current continuation — fixed terminal short with variable adjacent short

Primary resumed from clean pushed `cb218d3`; the preceding turn made
verified progress. Ownership is unchanged: this handoff/outline,
append-only NN/DN notes and existing external Rust consumer. The user's
diagram-only direction is retained. No basis calculation, Lean build,
maintained Rust edit or additional worker.

**New uniform component reduction:** [fixed terminal short](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#when-the-terminal-short-is-fixed).
If r=xz is selected throughout C, f=wz is redundant throughout C, even
when q=wx varies. Otherwise an f-covering state admits a descending
incoming cut at z, retaining f, followed by r->q. That contradicts
constant r. Delete f and mark r to get ONE whole smaller component.
For NN this is its actual target; for DN it is L-f with e,r strict.
The [DN continuation](docs/proofs/COMPONENT_DN_JOINT_REPAIRS.md#dn-components-with-the-terminal-short-always-selected)
records the latter output and its area decrease.

**Second proved reduction, with a necessary stated hypothesis:** if r
is always absent, q varies, and w is LEAST in its selected weak block,
then f is again inactive. From an f-covering state, normalize w to a
pendant vertex, normalize the remaining block leftwards, then use an
incoming cut and a decreasing chain of cover forks to introduce q and r.
Every move keeps f covering. Delete f and absent r to get a whole
component of L-f-r. In particular all fixed-r components at a leftmost
NN contact are now reduced, using the preceding fixed-q theorem too.
The least-vertex hypothesis fails for DN because e=uw is selected.

**Checks:** graph-only `dn_joint_span --nn-fixed-r` constructs 5132
paths / 8346 actual flips in the five NN and six DN fixtures, checking
coverhood of f, strict edges, edge count and component membership at
every step. All 681 claimed deletion images match whole components;
146 have variable q and lie outside the preceding fixed-q class.
Frozen sources, command and receipts:
`/lake-cache/ai-projects/requests/VerticalStripLLT/fixed-r-20260929/`.
All runs finished successfully with empty stderr. Runtime registry and
`codex mcp list` were checked; Lean remains wrong-root and unused.
The existing Rust guide/metadata check was retained, and Graph/Poset
APIs were inspected and reused for weak blocks and reachability.

**Still open:** the general two-variable collection, and the general
fixed-absent-r reduction with incoming vertices before w. The latter
passes these finite fixtures, but is NOT proved. These results do not
prove general active-middle connectivity or the full NN/DN goal, which
remains active. Previous proof-note contents are preserved as prefixes;
128 local file links, frozen receipt hashes and `git diff --check` pass.
Maintained Rust remains clean at
`d53fb193af3c69adedbd9ec8592f87235d809ffa`. No launched process remains.

## Current continuation — fixed-short components reduce uniformly

Primary resumed from clean pushed `099877c`. Ownership is unchanged:
this handoff/outline, append-only NN/DN notes and the existing external
Rust consumer. The user's diagram-only direction remains in force.
No basis calculation, Lean build, maintained Rust edit or new worker.

**Proved with arbitrary exterior:** the
[fixed-short NN theorem](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#components-on-which-the-adjacent-short-is-fixed)
and its [DN consequence](docs/proofs/COMPONENT_DN_JOINT_REPAIRS.md#dn-components-on-which-the-adjacent-short-is-fixed).
Every component on which q=wx has constant selected status maps to ONE
whole smaller component. Sector 00 uses the full endpoint relabeling;
10 deletes the everywhere redundant f and absent r; 11 deletes f and
marks r. In DN the latter output is L-f with e,r strict, not necessarily
the main DN target. All outputs decrease the original induction order.

Sector 01 cannot be an entire component. Whenever two covers enter one
vertex, the right incoming cover can flip left. Such moves strictly
decrease the sum of the selected edges' endpoint labels. At a terminal
state each vertex has at most one incoming cover, so its predecessors
form a chain. Keeping f=wz and r=xz while q is absent contradicts that
property. Thus leftward flips must introduce q. This is a uniform actual
path argument, not an active-middle connectivity theorem; it does not
keep q selected or expose f. An initially contemplated signed recurrence
for a whole 01 sector is unnecessary because that sector cannot occur.

**Verified:** graph-only `dn_joint_span --nn-fixed-short` checks 1319
whole component images (2365 states) among 1862 source components in
five NN and six DN fixtures. It constructs 9081 leftward paths comprising
19873 actual flips, with strict descent at every step. All checks pass;
stderr is empty. Frozen sources, command and receipts:
`/lake-cache/ai-projects/requests/VerticalStripLLT/fixed-short-20260929/`.
Rust capability guide, Cargo metadata/APIs, runtime registry and
`codex mcp list` were checked. Lean MCP is rooted at RealRooted and unused.

**Still open:** uniform collection for components in which q varies,
including arbitrary crossing exterior and empty unmarked corners.
The fixed-short theorem and the previous two-recurrence example do not
close that gap. The full goal remains active. Both previous proof notes
remain verbatim prefixes; 124 local file links, receipt hashes and
`git diff --check` pass. Maintained Rust is clean at
`d53fb193af3c69adedbd9ec8592f87235d809ffa`. No process remains from
the diagnostic run. Proof checkpoint `07012b6` is pushed to `origin/main`.

## Current continuation — two recurrences resolve an empty-corner example

Primary resumed from clean pushed `c34e458`; the preceding turn made
verified progress. Ownership and diagram-only restrictions are unchanged:
this handoff/outline, append-only NN/DN notes and existing external
consumers. No basis/quotient calculation, Lean build or additional worker.

**Proved fixed component recurrences:** [using DN to separate an NN pair](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#using-dn-to-separate-two-surviving-nn-components).
In area 012333 with strict 14,25, the standard seven-edge NN completion
of an empty-03 component C_69 is exactly C_69+C_126. The other component
selects 03. Both survive strict-corner and mixed-cycle reductions. Thus
the previous same-layer inactive-only correction cannot handle this source.
This is not an obstruction to other edge layers or direct RHS diamonds.
Deleting absent 03 from C_69 merely returns the original DN input; do not
count that as a completed DN reduction.

We resolve this example by using BOTH recurrences. In its native DN source
012233, C_69 is the full seven-edge layer except one isolated state.
The DN target has the same 69+1 split, and the singleton states correspond
under the bottom swap. Subtracting them proves C_69 = D_69 in whole
components. In the NN image of C_69+C_126, cancel D_69 using that identity.
The result is a positive sum of eight whole target components for C_126,
with sizes 52,33,29,1,3,4,1,3. The note lists their seeds and gives the
full diagram derivation. Every final diagram decreases the proper original
source order. No component expansion or polynomial comparison is used.

**Uniform extension:** all swaps fix endpoints 0,5, so the proved
endpoint-attachment theorem extends both identities to arbitrary chosen
components attached at BOTH ends. This does not allow crossing exterior.
A fixed two-triangle attachment checks eleven whole products: DN has
276 states on each side, NN 504 on each side.

**Checks:** `dn_joint_span --nn-empty-completion` checks all source joins,
the exact two-component class, common/native mixed-acyclic witnesses,
the two DN layers and singleton swap, every NN target coefficient and
whole component, and the attached products. It uses graph routines only.
Rust capability guide/metadata/APIs, runtime registry and `codex mcp list`
were checked. Frozen sources, commands and receipts:
`/lake-cache/ai-projects/requests/VerticalStripLLT/empty-nn-correction-20260929/`.

The full goal remains active: general NN collection with arbitrary exterior
and the required empty corners is unproved. A universal assertion that
forced additions are always inactive is unavailable. The new example shows
how an independent recurrence can replace deletion; it does not prove that
such a replacement is always available. Direct RHS diamonds remain allowed.
Proof checkpoint `4d8a4ad` is pushed to `origin/main`. Both old proof
notes remain verbatim prefixes; 119 local file links and
`git diff --check` pass. Maintained Rust is clean at
`d53fb193af3c69adedbd9ec8592f87235d809ffa`. All diagnostic runs finished
successfully; no build process remains from this turn.

## Current NN continuation — whole-component certificate and right attachment

Primary resumed from clean pushed `b9239d1`; the prior turn made verified
progress. Ownership is unchanged: this handoff/outline, append-only NN/DN
notes, existing external consumers. The diagram-only direction is retained;
no basis/quotient calculation, Lean build, maintained Rust edit or worker.

**New direct certificate:** the [84-state NN component](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#a-complete-component-certificate-beyond-cycle-rank-one)
in area 01234, strict 04, with seed {01,02,03,04,12,24}, has a checked
recurrence with eight positive whole components in the strict-14 target
and four negative whole components in the same graph with 14 unmarked.
Close its source brackets using the proved NN reconstruction; the twelve
additional whole components all have 04 redundant everywhere. Delete 04,
subtract them, and cancel eight terms by redundant insertion of 14. The
note lists every final component by seed and size. This gives a diagram
certificate for a difficult fixed example previously covered only by the
broader finite collection checks; it is not a new uniform NN theorem.

**Proved extension:** [NN at the fixed right endpoint](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#nn-recurrences-extend-at-the-fixed-right-endpoint).
Any such recurrence extends to arbitrary chosen components attached at
its fixed right endpoint. Whole products, fixed-endpoint coloring identities
and distinguished HRV-fibre data prove the claim, without assuming an
expansion for the attached component. Left attachments moved by the NN
swap and crossing exteriors remain excluded. The 84-state recurrence thus
extends to an arbitrary right attachment. A two-state triangle check gives
168 source states = 198 positive - 30 negative; all thirteen products are
verified whole components.

**Important proof-search correction:** retaining q until an exposure is NOT
always possible, even in a complete five-vertex NN source. The displayed
seed has a singleton q-selected slice; its sole neighbor still has 04
redundant. Two flips leaving q expose 04, and a nine-flip path reaches
its middle mate. The global certificate avoids imposing that extra path
condition. In five fixed diagrams, all 6469 middle states in f-active
components have their middle mate in the same component; 574 need a
q-detour. This is evidence, not the unproved general active-middle lemma.
Do not substitute that optional lemma for the full collection objective.

Checks use graph/actual-flip routines only. The Rust capability guide,
metadata, existing APIs, runtime tools and `codex mcp list` were inspected.
Frozen consumer sources, commands and receipts:
`/lake-cache/ai-projects/requests/VerticalStripLLT/nn-middle-slices-20260929/`.
The remaining main obligation is uniform NN collection, including empty
unmarked corners; DN follows by the preceding proved reduction. Goal active.
Proof checkpoint `d6e7ed7` is pushed to `origin/main`. The previous NN
note remains a verbatim prefix; 107 local links in the three owned files
and `git diff --check` pass. Maintained Rust remains clean at
`d53fb193af3c69adedbd9ec8592f87235d809ffa`. All launched diagnostics
finished successfully; no Lean or other build is running from this turn.

## Current continuation — DN reduces to NN by an empty corner

Primary resumed from clean pushed `060d2e6`. The previous turn made
verified progress; the full goal remains active. Ownership is unchanged:
primary owns this handoff/outline, append-only NN and DN continuations,
and the existing external consumers. The user's diagram-only direction
is retained. No basis calculation, Lean build, new worker or review.

**New proved reduction:** [DN through an empty-corner NN diagram](docs/proofs/COMPONENT_DN_JOINT_REPAIRS.md#dn-through-an-empty-corner-nn-diagram).
Add missing natural corner e'=ux EMPTY and unmark selected e=uw. The
same selected sets form exactly the SAME whole component in an eligible
NN source. No new flip acts, since its new retained corner is absent.
After any NN whole-component collection, the fixed statuses of exposed
corners e',r send each whole output component by identity to the DN target
or a smaller corner-deletion diagram. All final outputs decrease the
original DN order (n,A,M). The initial NN split also recovers the exact
existing DN split by inserting redundant e' and applying its diamond.

**Precise remaining hypothesis:** uniform NN collection at eligible contacts
with arbitrary exterior corner decorations, including this empty unmarked
corner. The enlarged diagram is not saturated and its root may no longer
be the first area drop. We do not invoke induction on this larger diagram,
and the earlier saturated unicyclic NN theorem is insufficient. This is
a proved reduction of the DN obligation, NOT an unconditional proof of
DN or NN. It removes the need for a separate general DN repair if we
finish this NN statement. Continue with the NN component brackets.

**Verification:** `dn_joint_span --dn-via-empty-nn` checks whole source
components and every source adjacency, all four whole-output strata,
NN eligibility, ordinary areas and the final induction decrease in six
fixed DN fixtures (4--8 vertices, including crossing and attached exteriors).
All pass: 164 source components / 1860 source states. No polynomial
calculation is used. Rust capability guide, metadata, graph/component APIs,
runtime registry and `codex mcp list` were checked; maintained Rust remains
unchanged. Frozen sources, command, logs and verification:
`/lake-cache/ai-projects/requests/VerticalStripLLT/empty-corner-dn-20260929/`.
Proof checkpoint `5d4e6d5` is pushed to `origin/main`. Prior proof-note
contents remain verbatim prefixes; 109 local file links and
`git diff --check` pass. Maintained Rust is clean at
`d53fb193af3c69adedbd9ec8592f87235d809ffa`. The sole diagnostic job
finished successfully; no running build is left behind.

## Current direction — follow the notebook diagrams

The user's latest correction is explicit: stay away from basis calculations,
keep the proof simple, and follow how the author and Robin reasoned. We
reread the original one-page notebook PDF and its source map. Continue with
ONE source component, the identity sectors II/III, paired middle diamonds,
endpoint relabeling, and the missing members of whole RHS components.
Do not make quotient calculations or arbitrary-pair collection the argument.

Primary resumed from clean pushed `a43bb75`; ownership is unchanged:
this handoff/outline, append-only NN redistribution and DN joint-repair
notes, and the existing external consumers. Prior proof text remains intact.
No Lean build, maintained Rust edit, additional worker or independent review.

**Proved increment:** the [NN adjacent map](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#following-the-swap-through-a-further-flip)
still transports every q-preserving flip not retaining r after a bypass
is lost. The [two DN maps](docs/proofs/COMPONENT_DN_JOINT_REPAIRS.md#following-the-two-dn-swaps-through-further-flips)
do likewise with the stated retained-corner exclusions. Two diamonds give
an exact rule for the next unmatched pair. Following a spanning tree gives
an integral identity for complete pieces of those restricted graphs.
These pieces are NOT whole RHS components. Closing the excluded flips
and collecting the coupled signed terms remains open for both NN and DN.

**Checks:** full paired-flip correspondences and complete-piece identities
pass in the six earlier fixtures, the first-drop six-vertex case and the
attached eight-vertex DN case. Frozen consumer sources, commands and logs:
`/lake-cache/ai-projects/requests/VerticalStripLLT/coupled-coefficients-20260929/`.
Side coefficient experiments are retained there as exploratory receipts,
not used in the diagram proof or its proposed next step. An initial
basis-mismatched diagnostic failed; its corrected rerun passed. This did
not affect previous diagram identities. No general collection result is
claimed from these computations. The full goal remains active.
Proof checkpoint `f8becf0` is pushed to `origin/main`. Both prior proof
notes remain verbatim prefixes; 106 local file links and `git diff --check`
pass. Maintained Rust is clean at `d53fb193af3c69adedbd9ec8592f87235d809ffa`.
All newly launched checks have finished; the final push was confirmed.

## Active boundary continuation — local descent proved

Primary resumed from clean pushed `b9bc4ae` with unchanged ownership. The
preceding goal turn made verified progress; the full NN/DN tracking goal
remains active and unfinished.

**New proved increment:** every exit of either prepared NN/DN channel has
an exact signed [boundary descent](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#descending-the-prepared-swap-boundary-identities).
For a q-preserving bypass-loss exit, the paired actual flips and two diamonds
move the valuation difference to a pair with one fewer selected edge at
each endpoint. For q insertion, paired actual flips and two diamonds give
a lower-edge pair plus a same-edge pair with strictly greater reachability.
The lexicographic pair (total selected edges, missing reachability relations)
strictly decreases on every resulting pair. The
[DN strict-long exception](docs/proofs/COMPONENT_DN_JOINT_REPAIRS.md#boundary-descent-for-both-prepared-dn-channels)
deletes redundant e' in the full terms and places them in the valid smaller
diagram R-e', retaining r strict. These are arbitrary-exterior proofs.

**Important non-completion distinction:** successor pairs need not themselves
be prepared-sector boundary pairs, or individually be sums of whole components.
A decreasing measure for these permitted steps is NOT yet a closed recursion
for the source component. Next track the lower-edge and q-selected successor
terms together, using the source indicator, and prove whole-component closure.
Do not infer that arbitrary orientation differences can be collected separately.

**Refuted shortcut:** an exposed source anchor does not force adjacent-swap
membership equality. In the required first-drop 012333 example (ND unmarking
03, then NN at 25), a genuine prepared-sector exit gives swapped source
states on opposite selected-03 strata. Both are active at the marked corners,
but their whole components differ. The explicit paired exit and its nonzero
lower-layer replacement are recorded after (B3). A universal source-path
argument cannot dispose of these boundaries.

**Checks:** exact paired flips, diamonds, pruning, reachability inclusion and
strict decrease pass in the six earlier diagrams, the 012333 first-drop
fixture, and the attached eight-vertex DN fixture. For 012333, all 110 source
components also have integral expressions in its 83 whole target components
using the existing local relations and prepared-sector corrections. This is
finite evidence only. Frozen sources, logs and commands are in
`/lake-cache/ai-projects/requests/VerticalStripLLT/prepared-boundaries-20260929/`.
Proof checkpoint `0735f63` is pushed to `origin/main`. Previous proof notes
remain verbatim prefixes; 102 local file links and `git diff --check` pass.
All diagnostic jobs have finished. Runtime discovery and `codex mcp list` were checked; existing Rust
capabilities/consumer were reused. No Lean build, maintained Rust edit, extra
worker, or independent review.

## Current continuation — prepared swaps

Primary resumes from clean pushed `65cc9ac`; the preceding goal turn made
verified progress. The full NN/DN component-tracking goal remains active.
Ownership is unchanged: primary owns this handoff/outline, append-only NN
redistribution and DN joint-repair continuations, and the external consumers.

**New proved component-tracking increment:** the
[prepared adjacent NN swap](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#prepared-adjacent-swaps-and-their-component-boundaries)
is an isomorphism on the induced sector with q absent and two z-bypasses.
For DN there are [two prepared channels](docs/proofs/COMPONENT_DN_JOINT_REPAIRS.md#prepared-dn-swaps-and-sector-components):
an involution with e selected, and an isomorphism from e-absent/u-reaching-w
states to e-selected/e'-redundant states. The latter adds one selected edge.
Both preserve K/E and every internal actual flip, with arbitrary exterior.
Differences of whole induced components give zero corrections that can
alter only q-insertion and specified bypass-loss boundary comparisons.
Induced sector components are NOT claimed to be whole R components.

**Simplified finite repair:** the seven previously difficult complete
five-vertex NN images need only one additional prepared 0/1-swap relation:
[02+03+12+14+24]=[02+12+13+14+24]. Delete redundant strict 14, swap, restore it.
General/distant poset relabeling is unnecessary for those seven repairs.
All 210 source components in the prior six fixed diagrams still collect
integrally using the original local relations plus whole induced-sector
corrections only. This is finite evidence, not the missing uniform theorem.

**Remaining goal:** choose the sector-component corrections and RHS diamonds
uniformly so every q-insertion and bypass-loss boundary cancels. The induced
graph theorem prevents corrections from creating arbitrary internal flip
defects, but does not close these exits. Do not mark NN/DN complete.

Checks: exact state maps, inverse domain/image sets, both directions of
internal flips, valuations and boundary classification in the six fixtures,
a seven-vertex crossing extension, and an eight-vertex attached example
with nontrivial internal flips in both DN channels. Frozen consumer sources,
commands and receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/prepared-swaps-20260929/`.
Proof checkpoint `975ca08` is pushed to `origin/main`. Previous proof text
is preserved verbatim as prefixes; 98 local file links and `git diff --check`
pass. No Lean build,
maintained Rust edit, additional worker, or independent review. All launched
checks have finished. Runtime registry and `codex mcp list` were checked;
Lean MCP remains rooted at RealRooted and unused. The Rust capability check
was repeated before extending the existing bounded diagnostic.

## Active NN/DN continuation — 2026-09-29

The user authorized work on both independent cases. Starting from clean,
pushed `725ee04`, primary owns append-only continuations of the NN
redistribution and DN joint-repair notes, the current outline/handoff, and
the existing external `nn_component_transport` / `dn_joint_span` diagnostics.
Prior restrictions and all other ownership remain unchanged.

**Proved:** every unmatched deletion residual for NN or DN can be moved
into the actual RHS using at most one additional diamond and the eligible
adjacent swap, with arbitrary exterior and arbitrary bypass length. See
[NN elimination](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#eliminating-every-unmatched-term-into-the-actual-rhs)
and [DN elimination](docs/proofs/COMPONENT_DN_JOINT_REPAIRS.md#eliminating-the-dn-deletion-residual).
This is state transport, not yet whole-component collection.

**Proved complete repair:** the left DN four-state C_1 has a direct
[RHS-only recurrence](docs/proofs/COMPONENT_DN_JOINT_REPAIRS.md#a-direct-rhs-only-repair-for-the-left-four-state-component),
C_1 = D_8 - T_3 - 2 T_4 - T_5, for both K and E. Four RHS diamonds,
one internal swap and redundant-edge deletion suffice. Every output is
a complete component; no source additions or component expansion is assumed.
The endpoint-attachment theorem applies to these maps as well.

**Finite evidence:** all 210 source components in six fixed NN/DN diagrams
have integral combinations of whole actual RHS components modulo diamonds,
redundant-edge equalities and sink-order-preserving poset relabelings.
Exact K/E checks pass independently. Seven complete-five-vertex NN images
are outside the span if relabeling is restricted to adjacent swaps which
stay inside R; general poset relabeling closes all seven. This restricted
span failure is not a counterexample to the proposed recurrence.

**Still open:** construct these repairs uniformly and prove all output flip
boundaries close simultaneously. The new residual elimination need not
preserve the old q-preserving coefficient comparisons. Do not infer a
uniform theorem from the finite quotient computations, or native weighted
polynomial recurrence coefficients from the unweighted DN formula.
Next investigate sink-order-preserving relabeling preparations together
with RHS diamonds; the previous adjacent-only restriction was too strong.

External consumer: `dn_joint_span --rhs-only-audit --permuted-closures`.
Frozen sources, exact commands, compiler/check logs and verification are in
`/lake-cache/ai-projects/requests/VerticalStripLLT/rhs-only-elimination-20260929/`.
Proof checkpoint `456753f` is pushed to `origin/main`. Both old proof notes
are preserved verbatim as prefixes; 93 local file links and `git diff --check`
pass. The focused Rust consumer checks pass; maintained Rust is unchanged at `d53fb193af3c69adedbd9ec8592f87235d809ffa`.
Runtime discovery and `codex mcp list` were checked again; Lean MCP remains
rooted at RealRooted and unused. No Lean build, extra worker or independent
review. All launched checks have finished.

## Current direction — direct images of one component

The user has reiterated the four-recurrence argument: start with one complete
left-hand component, apply the recurrence's diagram maps, then use diamonds
and vertex relabeling to collect a linear combination of whole right-hand
components. This is the primary task. Source additions, homogeneous completion
classes and selected-sector uniqueness are optional constructions, not
requirements of the desired theorem or reasons to stop the direct argument.

Continuation starts from clean, pushed `be76843`. Primary additionally owns an
append-only section of `docs/proofs/COMPONENT_NN_REDISTRIBUTION.md` and its
existing external Rust diagnostic. The immediate check simplifies the known
four-vertex example to one RHS diamond and three components of the actual
shortened NN target. Other ownership and the no-worker/no-Lean restrictions
are unchanged.

That check now passes and its proof is appended as
[a shorter RHS-only NN repair](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#a-shorter-repair-entirely-in-the-nn-right-hand-diagram).
The five-state C maps to D1+ D2-T, with component sizes 3,3,1, all in the
actual shortened target with strict 13. One additional RHS diamond and
deletion of its redundant 02 edge give the repair. With normal-selection
weight t, the coefficients are t,1,-1. Exact K/E and complete-component
checks pass; sources and receipts are in `nn-rhs-only-20260929/` under the
external project request directory. No new general reassembly theorem is
claimed. The open direct check is compatibility of RHS repairs with every
output flip, including flips meeting exterior vertices.

Verification: the NN note at `be76843` is preserved verbatim as a prefix;
82 local file links and `git diff --check` pass. The focused external Rust
consumer build and check are complete. No background job, Lean build,
additional worker or new independent review.

## Resumed ownership — 2026-09-29

The replacement primary worker resumes at the user's explicit request from
clean, pushed `2511182138c3f3a27f8f6207a982ec1e28b6c3c7` on `main`.
It owns `HANDOFF.md`, append-only continuations of
`docs/proofs/COMPONENT_RECURRENCE_ENDPOINT_EXTENSION.md` and
`docs/proofs/COMPONENT_DN_SOURCE_ADDITIONS.md`, related outline
routing, and the existing external `hrv-bridge` diagnostic lane. The paused
worker released this lane; all other ownership is preserved. We first audit
the endpoint-marked DN identities and the proposed attached-component fixture.
The general diagram-recursion proof remains unfinished.

**New proved increment:** the
[endpoint-attachment theorem](docs/proofs/COMPONENT_RECURRENCE_ENDPOINT_EXTENSION.md#endpoint-attachment-theorem-completed-audit)
is now proved mathematically. HRV diamonds preserve a multiset of full HRV
maps; internal DN swaps preserve endpoint fibre data. Any completed recurrence
using these endpoint-preserving maps extends to arbitrary components attached
at the two ends, with whole output components and the same decreasing measure.
No component expansion for the attachments is assumed. In particular all
fourteen rows of the five-vertex left DN table extend.

The fixed `dn_joint_span --endpoint-attachments` check passes all fourteen
attached rows, including 16/32/16 in the C_1 row. It checks actual complete
components, strict edges and signed endpoint HRV profiles; the nine-vertex
checks visit 128/88/64 distinct L/R/J states without global enumeration.
The small external Rust consumer build passed. Receipt and frozen sources:
`/lake-cache/ai-projects/requests/VerticalStripLLT/endpoint-attachments-20260929/`.
Maintained Rust remains unchanged at `d53fb193af3c69adedbd9ec8592f87235d809ffa`.

**Second proved increment:** the
[full-layer selected-corner criterion](docs/proofs/COMPONENT_DN_SOURCE_ADDITIONS.md#isolating-one-selected-corner-sector-by-a-full-layer)
isolates C when it is the unique component in its selected-corner sector and
total-edge layer. All added components omit a specified corner and delete
independently. This gives a signed whole-component DN recurrence for every
component of the saturated square of a path on n>=5 vertices, including
crossing prefix edges. Its targets are the complete R layer minus the complete
corner-deletion J layer. This is a new recurrence proof, not a new claim that
the square-path expansion was previously unknown.

All eighteen fixed rows at n=5,6,7 pass exact K and E checks, actual-component
checks and independent deletion-image checks. Receipt/frozen-source directory:
`/lake-cache/ai-projects/requests/VerticalStripLLT/square-path-layers-20260929/`.
Equation (EA6) in the endpoint note also proves that homogeneous forced source
classes factor exactly under endpoint attachments; they create no new additions.

**Remaining general gap:** when several components survive the available
reductions in a selected-corner sector, the full-layer identity gives only
their sum. We have not excluded or uniformly resolved that case. Independent
reducibility of every extra member of the minimal NN/DN completion class is
still unproved. The endpoint theorem settles the first historical resume item,
and the square-path recurrence settles a restricted crossing family. Neither
settles arbitrary crossing exteriors or the NN endpoint-moving swap.

Endpoint proof checkpoint `df1ea28` is pushed to `origin/main`; the original
endpoint note is preserved byte-for-byte as a prefix, 65 local file links and
`git diff --check` pass. The second increment preserves the source-addition
note at that checkpoint verbatim as a prefix. No new independent review is
claimed for either increment.

The full-layer/forced-union proof checkpoint `b316d41` is also pushed to
`origin/main`. Both proof-note prefix checks, 78 local file links and
`git diff --check` pass. All launched diagnostics have finished; no background
job needs monitoring or restarting. The maintained Rust checkout is clean.
No Lean source, manuscript or external Overleaf file changed. The mathematical
results above have not been formalized in new Lean declarations.

Runtime tools and `codex mcp list` were inspected. Lean MCP is rooted at
RealRooted, not this project. No Lean build is currently needed; no additional
worker or consultation is authorized or launched. The following account-switch
status is retained as the starting record; new proved results will be recorded
above it. The actual final swap checkpoint is `2511182`; `ae4c3a2` below was
its preceding proof/handoff checkpoint.

## Account-switch checkpoint — 2026-09-29

**Paused at the user's request for an account swap. The general recurrence
proof is unfinished.** No account, model, role or service-tier change was
made here. Last assignment: academic Astra/high, primary strategy/source
owner, on `main`. Resume only in the user's chosen session; do not launch
or relaunch any worker or consultation.

Latest mathematical direction from the user: **focus on the recursion of
whole components; proving the same recursion for colorings is usually easy.**
The requested proof uses the author's diagram bijections and recurrences.
The already-complete Lean word-functional proof is not a substitute.

Start with the [proof outline](docs/proofs/COMPONENT_RECURRENCE_OUTLINE.md),
then the [unfinished endpoint-attachment continuation](docs/proofs/COMPONENT_RECURRENCE_ENDPOINT_EXTENSION.md).
The complete prior handoff, including ownership and receipts, is preserved
in the [account-switch history](docs/archive/component-recurrence-handoff-before-account-switch-20260929.md).
Only relative Markdown links were adjusted in that archive. Original
crash-recovery dirty text is also preserved in the earlier recovery archive.

## What is established

- The [notebook PDF map](docs/proofs/COMPONENT_NOTEBOOK_MAP.md) decodes I/II/III,
  their positive weighted coefficients, the two identity sectors and the
  endpoint maps. The middle states require a paired diamond, not the proposed
  individual poset map. The smallest notebook example is fully proved.
- Whole-component corner deletion/envelope normalization and the
  [first-drop induction order](docs/proofs/COMPONENT_RECURRENCE_COVERAGE.md)
  are proved. DD/ND reduce to the NN/DN component problem.
- [Homogeneous DN completion](docs/proofs/COMPONENT_DN_SOURCE_ADDITIONS.md#completing-one-selected-edge-layer-of-the-direct-dn-image)
  and its [NN companion](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#exact-completion-within-one-selected-edge-layer)
  identify the minimal forced unions U_k(C), V_k(C) whose outputs are whole
  components. Independent reduction of every extra source component is open.
- Both minimal five-vertex pictures and the displayed six-vertex example
  have complete signed component recurrences. See
  [joint repairs](docs/proofs/COMPONENT_DN_JOINT_REPAIRS.md) and
  [source additions](docs/proofs/COMPONENT_DN_SOURCE_ADDITIONS.md).
- The retained-edge repair has arbitrary exterior whenever either f or r
  covers at Q+xs. With r,sz covering in Q, theorem (58) also allows wt
  covering with no suffix restriction. Theorem (65) allows redundant wt
  when J=K, using matched endpoint preparations.
- New local theorem (69), at the end of the
  [retained-edge note](docs/proofs/COMPONENT_DN_RETAINED_EDGE.md#interleaving-the-two-incoming-cuts),
  permits J not contained in K: assume t reaches z, all J tails exceed s,
  and J intersects H trivially. Interleave the incoming t/z cuts by decreasing
  tail, then use the matched preparations. Fixed paths pass 21,33,35,29
  flips, including extra incoming z-tails below and above t. No state
  enumeration was used for these path checks. This is a proved local repair,
  not the general component recursion.

Here J is the set of proper selected incoming z-tails reached from w;
K the corresponding tails reached from t; H the selected incoming t-tails
strictly between s,t reached from w. Full hypotheses are in the proof note.

## What to resume

1. Audit the candidate endpoint-attachment extension in the new note. It
   aims to extend the known whole-component DN recursion to arbitrary
   components attached at its two ends. The component product is established;
   the endpoint-marked identity argument and 16/32/16-state example have
   NOT yet been completed or checked. Do not cite this extension as proved.
2. Return to whole-component reassembly with crossing exterior edges.
   Source unions alone do not isolate C unless their extra components have
   independent smaller-diagram recurrences. Do not infer this from one
   orientation with a redundant corner or a vanishing alternating valuation.
3. Remaining local retained cases include common incoming forks ht,hz,
   lower incoming z-tails, and failures of background covers. The general
   left repair also remains open. Universal left source connectivity is
   false; it needs coefficient corrections/whole source additions.

Two bounded component-profile checks inform the choice of recursion:
area 01222 has 14 source and 15 target components, so a universal one-to-one
DN component correspondence is impossible. The established signed recursion
is the appropriate model. Area 012233 has matching HRV-profile multisets
for its 26 source and 26 target components; this is finite evidence only.
Neither check proves a general bijection or component formula.

## Restrictions, ownership and processes

- No Lean/Lake builds. No Claude, subagents or other workers without new
  explicit user authorization. The old crashed consultation has no useful
  durable result and must not be relaunched.
- Preserve all prior proof text. This increment leaves the retained-edge
  note's previous HEAD as a verbatim prefix. Historical status is archived,
  not discarded. Manuscript TeX and PDFs are unchanged.
- All diagnostic/compiler jobs launched in this continuation have finished.
  No background task needs monitoring or restarting. Primary is releasing
  this source lane after the clean, pushed handoff checkpoint.
- No maintained Rust edits. Its HEAD remains
  `d53fb193af3c69adedbd9ec8592f87235d809ffa`.
- Existing external consumer:
  `/lake-cache/ai-projects/requests/VerticalStripLLT/diamond-exploration/hrv-bridge/`.
  The task changed only its `first_join_tree_lifts.rs` and `dn_joint_span.rs`
  diagnostics; frozen copies accompany the receipts below. Reuse them.

## Verification and recovery

Prior pushed checkpoints: `d6c755a` (rejoining bypass), `ed60dcc` (paired
suffix, removes upper-tail guard), `9b622b0` (metadata). The final account-swap
checkpoint is `ae4c3a2`, pushed to origin/main. Archive preservation, 208 local
file links and git diff --check pass. No new independent review claimed.

Receipt directories under
`/lake-cache/ai-projects/requests/VerticalStripLLT/`:

- `retained-interleaved-incoming-20260929/`: current four exact paths.
- `component-dn-matching-20260929/`: two fixed profile comparisons.
- `retained-paired-suffix-20260929/`: earlier 17,39,41,29-flip paths.
- `account-switch-handoff-20260929/`: raw pre-cleanup handoffs, final snapshots,
  archive-preservation checks, commands, verification and checksums.

Overleaf current metadata:
`/home/paxinum/Dropbox/Apps/Overleaf/LLT flip/HANDOFF.md`.
Its complete previous version is retained beside it as
`HANDOFF-history-before-account-switch-20260929.md`.
The original diagram source remains `llt pics.pdf` in that folder.
