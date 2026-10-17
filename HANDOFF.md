# VerticalStripLLT handoff

## Public repository preparation (2026-10-17)

The host supervisor owns only `README.md` and this handoff entry for the
user-requested GitHub visibility change. The README now gives a short result
summary, links the two independent formalized component proofs, and cites the
Alexandersson--Sulzgruber and Hwang papers. No Lean or manuscript source was
edited. The README checkpoint `b1a13d8` is pushed to `origin/main`, and GitHub
reports `PerAlexandersson/VerticalStripLLT` as public; the public page returned
HTTP 200. Read-only checks found a clean `main`, no credential-like tracked
filenames in current or historical paths, and no credential-pattern matches in
current text files. The local `PartitionDivision` audit project is separate;
it has no Lean package or GitHub remote and must not be described as formalized.
The host supervisor releases both files after this status checkpoint.

## Current status and routing

On 2026-10-16, the user moved the chromatic P-array RSK and proper-coloring
crystal work to `/workspace/projects/chromatic-crystals/`.  Its four research
notes and standalone Rust crate are canonical there.  This repository retains
the source history through `d6a14b8`; the chronology below is historical and
does not authorize new chromatic work under `VerticalStripLLT`.

No Lean source, LLT/HRV computation, circular-LLT file, or manuscript file was
part of the migration.

## Historical chromatic-crystal chronology (migrated)

On 2026-10-16, at the user's request, the Chromatic P-array RSK worker
reclaimed `docs/chromatic-p-array-rsk/`,
`experiments/chromatic-p-array-rsk/`, and its focused `HANDOFF.md` entry to
replace the completed global P-Knuth rank map by a local reversible insertion
rule.  The primary lane owns all edits and builds.  Authorized read-only
assessments cover the exact Kim--Pylyavskyy forward algorithm, rank-six
ladder-climber defects, and coherent dual-equivalence/growth-diagram rules.
Lean builds and sources, marked-coloring/HRV, circular LLTs, and manuscript
files remain excluded.

The Rust semistandard involution has been corrected to the genuine
Schuetzenberger--Lusztig involution, using the triangular Bender--Knuth word
`t1 (t2 t1) ...`.  The previous longest-permutation reduced word was an
involutive content reversal, but Bender--Knuth moves do not satisfy braid, so
it did not intertwine Kashiwara operators.  A new exhaustive tableau test
through size five verifies involutivity, reversed content, compatibility with
standard evacuation, and `eta f_i = e_{k-i} eta`.  All existing bijection and
crystal tests still pass with the corrected map.

Rank-eight probes also corrected two assumptions in the local KP graph.  A
candidate now uses the reversed input P-descent set rather than raw
`Des(Q)`, and a recording-defect anchor handles raw outputs with valid `P`
but nonstandard `Q`.  Exact regressions use code `(1,2,4,6,6,7,7,8)`, word
`82156743`, and code `(2,4,5,6,7,8,8,8)`, word `73156842`.  The first order's
112 defects now match perfectly in the old window.  The second still leaves
24 of 437 defects unmatched until the window is enlarged.  Code
`(3,4,6,6,6,8,8,8)` requires two occupancy changes and three recording moves,
and has four exact ties even after the old total-cost/profile tie-breaker.
Thus the rank-seven local rule is not canonical in rank eight.  The CLI
`--kp-uniform-code` reports these failures without asserting completeness.
Shortest P-Knuth distance separates the four sampled ties (total 60 versus
63), whereas lexicographically minimal shortest paths depend on direction;
the global Garsia--Milne endpoints lie outside both tied matchings.

On the crystal side, no uniformly bounded-support intrinsic rule is possible:
on every odd path with alphabet two, normality forces `f_1` to exchange the
two alternating proper colorings and hence recolor every vertex.  A carrier
or scanning rule remains viable.  Every Garsia--Milne transition preserves
the full P-descent set and therefore lifts at fixed content, but the raw-good
branch is not stable under the transported crystal operators.

The recording part of the genuine crystal now has an exact carrier.  For the
final semistandard tableau `Q`, let `S=std(Q)`.  Evacuation cancellation shows
that the KP recording columns are the reversed rows of `S`.  A Kashiwara move
has a constant-size token `(row,col,alpha,beta)` and applies one interval cycle
of standard labels directly to those columns; swapping `alpha,beta` gives the
inverse.  The release `--kp-carrier 5` census verifies all 198,720 directed
moves on 56,993 colorings through rank five.  There are 96 directed moves
landing in repaired targets and 20 directed raw/repaired crossings.  Raw
inverse works when the moved
endpoint is raw-good; a repaired endpoint uses a Garsia--Milne reverse trace.
Thus the only remaining nonlocal part is endpoint ownership resolution.

For local insertion, exact-Q partial stages are now known unsafe: a rank-eight
6-by-6 component has maximum exact-Q matchings that cannot extend perfectly.
The replacement prototype uses nested graphs and seals only entire perfectly
matched components.  Independent exhaustive probes seal respectively
`112`; `407+30`; and `934+354+0+144` defects on codes `12466778`, `24567888`,
and `34666888`, with no cost/profile ties.  Rust exposes the same experiment
as `--kp-uniform-code CODE adaptive`.  A terminal all-rank schedule must relax
all bounds and use proved invariant-fiber balance or append the global
Garsia--Milne endpoint edges; locality in the worst case remains open.
The Rust completion now uses a simpler proved fallback: each candidate edge
is checked to preserve reversed P-descent and P-inversion, local perfect
components are removed, and any residual is paired lexicographically inside
these balanced coarse fibers.  This is an all-rank finite bijection with a
global fallback; components beyond the 128-bit local optimizer are simply
deferred to it.  Its inverse reconstructs the same deterministic catalog,
recognizes corrected targets there, and otherwise uses checked raw KP
deletion/replay.  The sampled rank-eight orders use zero fallback pairs.

The adaptive standard map now has a semistandard coloring lift and a genuine
transported crystal.  The recording interval carrier is independent of the
choice of standard baseline, so locally sealed adaptive endpoints use the
adaptive inverse rather than a Garsia--Milne ownership trace.  On defective
code `335566`, the exhaustive regression checks 12,000 six-color proper
colorings and 49,040 directed Kashiwara moves, including forward/inverse,
ascent/inversion, and raising/lowering inverse identities.

The global carrier census now runs through rank six: 2,278,499 colorings and
10,028,100 directed moves.  Exactly 9,925 moves land in repaired endpoints,
1,750 cross the raw/repaired boundary, and the longest GM reverse trace is 10.
There are 114 repaired standard endpoints over 13 affected orders.  At rank
six all 112 missing endpoints have valid `Q` and only a `P` defect.  A
two-row/two-column ownership signature plus full shape has a raw/repaired
collision, so a tiny fixed guard is already insufficient.

The complete rank-six ownership hierarchy is nevertheless local.  Among the
112 repaired standard endpoints, 76 use one `P` transposition, 20 a
three-cycle, two a double transposition, eight a four-cycle, and six a
three-entry `P` move together with one outer-corner `Q` move.  All lie in two
rows and four consecutive columns.  Actual raw replay, raw-image exclusion,
and the asymmetric P-Knuth reading certificate leave 112 disjoint edges, all
equal to the Garsia--Milne edges.  A Rust regression now verifies equality of
the adaptive and GM standard maps on every permutation for all 132 rank-six
orders.

The exact Kim--Pylyavskyy Algorithms 1--3 and dualized inverse are now
implemented with a reversible event trace.  The rank-five repair is
recording-aware: only the two fibers `125/34` and `135/24` over the repaired
tableau `213/54` are first restored to `312/54` before published deletion;
the three existing valid fibers are unchanged.  Exhaustive checks through
rank five prove exact target coverage and inverse reconstruction.
After standard-tableau evacuation corrects the reversed recording-descent
convention, this standard map is composed with the existing coloring
standardization.  The resulting weight- and ascent-preserving chromatic map,
its inverse, and all transported Kashiwara lowering/raising inverses pass on
every fixed-alphabet coloring through rank five.

The rank-six census covers 132 orders and 95,040 permutations.  Exactly the
12 ladder-climbing orders fail, with 112 invalid insertion tableaux, no bad
recording tableaux, and no raw pair collisions.  The unique missing target in
each P-Knuth-component/recording-descent fiber gives ten coordinate actions;
106 preserve `Q`, while six change both shape and `Q`.  Seventy-seven source
signatures and 77 target signatures give conflict-free actions.  Reverse
recognition also requires raw deletion--insertion replay: the other guards
alone admit two false positives.  The full bidirectional finite rule recovers
exactly all 112 corrections.  It is not yet an all-rank local insertion.

Two durable obstructions delimit the next step.  The BEPS Section 5 chain
interchange fails Yang--Baxter first at rank six, even on KP-eligible orders,
and one witness forces different insertion shapes, so it cannot be a
memoryless growth rule.  KP Example 7.11 at code `(2,4,5,6,6,7,7)` and word
`3156742` has raw column heights `(2,3,1,1)`, so an all-rank correction must
accept arbitrary column arrays.  Detailed conventions and results are in
`docs/chromatic-p-array-rsk/LOCAL_KP_INSERTION.md`.

Twenty unit tests, Clippy with warnings denied, formatting, and the diff
check pass.  Release `--kp-carrier 6` checks 10,028,100 directed moves.  The hard
adaptive rank-eight run on code `34666888` matches all 1,432 defects with
sealing profile `[934,354,0,144]`, zero optimum ties, and zero fallback pairs.
The rank-six adaptive regression exhaustively checks forward/inverse
reconstruction and exact target coverage.  No Lean source or build,
marked-coloring/HRV file, circular-LLT file, or manuscript file was touched.
The verified rank-six carrier and adaptive-crystal checkpoint is `446cd9b`.
The worker retains its three owned paths for the next carrier/ownership
experiment.

The rank-seven arbitrary-column experiment is complete.  Across 429 orders
and 2,162,160 words, exactly the 84 ladder-climbing orders fail.  There are
5,162 bad insertion arrays, 142 bad recording arrays, and no raw pair
collisions.  The 142 bad recording arrays are exactly the nonpartition
composition `(2,3,1,1)`.  Fiberwise correction within a P-Knuth component and
recording descent gives exact target coverage.  It keeps `Q` on 4,702 defects;
460 change both shape and `Q`.  The finite rule has 133 insertion actions and
135 pair actions.

Unlike rank six, rank seven has 541 defect fibers of size greater than one,
with maximum five, and 352 nontrivial subgroups after fixing the entire
recording array and first-column height.  The earlier lexicographic ranking is
now replaced by a symmetric minimum-motion assignment.  For each source and
target, it records the number and Manhattan distance of moved entries in
`P` and `Q`; it minimizes the total cost and then the decreasing list of
individual pair costs.  The total cost has 32 tied groups, with at most three
optima, and the individual-cost profile resolves every tie.  The rule also
uniquely allocates the nine unbalanced exact-`Q` groups and the two nontrivial
height-only groups.  Final residual fibers have size at most one.  The map is
therefore choice-free and reverses by the same matching rule through rank
seven.  It uses 73 insertion and 73 pair actions, down from 133 and 135 for
lexicographic ranking.  It remains fiber-global: computing it still requires
the missing-target set rather than a local insertion recurrence.

An independent Astra Python sweep confirmed all 343 balanced exact-`Q`
groups.  It also showed that shortest P-Knuth distance resolves only eight of
the 32 total-cost ties, while the decreasing individual-cost profile resolves
all of them.  The release `--kp-raw 7` and `--kp-correct 7` censuses, all
thirteen unit tests, Clippy with warnings denied, formatting, and the diff
check pass.  The rank-seven raw-census checkpoint is `68318b7`; the
minimum-motion implementation checkpoint is `aa661f5`.

The 73 minimum-motion pair actions now have bidirectional finite guards.
The forward guard takes the leftmost, then topmost, row/shape violation and
reads the centered three-row window from one column left through four columns
right, together with the two adjacent complete recording columns.  It gives
2,532 signatures and no action conflicts on all 5,162 defects.  Its normalized
motions are translation-invariant; global shape, absolute boundary position,
and `Des(Q)` are unnecessary.  Exact recording gaps remain necessary: keeping
only relative recording order leaves 132 conflicts.  A same-raw-`P`,
same-`Des(Q)` witness is recorded in `LOCAL_KP_INSERTION.md` and the tests.

The inverse top-three-row/first-five-column guard with full `Q` gives 2,693
signatures, no conflicts, and no false recognition among all 2,162,160
rank-seven targets.  More locally, trying the four observed boundary positions
gives 5,850 candidates; the forward guard rejects 140 and actual dual KP
deletion--reinsertion rejects 548, leaving exactly the 5,162 corrected targets,
with no missed, false, or multiple inverse.  The Rust release census
independently reproduces `recognized=5162, missing=0, false=0, ambiguous=0`.
Sixty-two actions preserve shape and eleven change it; every support lies from
one column left to four columns right of the first bad boundary.  This is an
explicit reversible finite rule through rank seven, applied without consulting
the missing-target set.  A uniform case rule and overlap/confluence proof are
still required for an intrinsic all-rank insertion.  The boundary-guard
implementation checkpoint is `d6961ae`.

The first uniform action case is implemented.  All 78 arrays whose first
defect is the shape pattern `(2,3,1,1)` use the same five-entry path move and
one recording-entry move; the release census reports zero failures.  The other
64 malformed arrays have an earlier row defect.  A greedy nearest-repair rule
cannot handle the row sector: 83 staged assignments are strictly nonminimal
for their individual source, and 35 remain nonminimal even after restricting
to the 66 observed motions, the correct P-Knuth component, and targets excluded
from the raw KP image.  The obstruction is assignment competition, first at
code `(2,4,5,6,7,7,7)`.  A new rank-seven regression also composes the
corrected standard map with coloring standardization on this defective order
and checks weight, `asc=inv_G`, inverse reconstruction, and Kashiwara
lowering/raising inverses over a three-letter alphabet.  The uniform
shape-branch checkpoint is `b9645bd`.

All thirteen transposition actions are also replaced by one rule.  At a row
defect `(j,r)`, try swaps with offsets `(2,0)`, `(3,0)`, `(4,0)`, `(2,-1)`,
and `(2,1)`, keep valid targets which are not in the raw KP image, and require
a P-Knuth path after restricting both column words to the changed-position
interval plus one unchanged letter at each end.  The certificates have length
five, six, or seven and use at most 16 elementary moves.  The release census
finds exactly 2,779 cases, with no ties or failures, and no candidate on the
other 2,383 defects.  Together with the 78 shape-first cases, uniform branches
now cover 2,857 of 5,162 repairs without a whole-component oracle.  The
combined uniform-branch checkpoint is `b9645bd`.

The remaining action table has now been removed at rank seven.  From each raw
defect, the Rust implementation enumerates partition-shaped targets differing
by at most one cell inside the centered five-row/six-column defect window,
valid insertion fillings fixed outside that window, and standard recording
fillings moving at most two entries and preserving `Des(Q)`.  It retains an
edge exactly when the changed column words have a P-Knuth certificate on the
changed interval with two preceding and one following letter, and actual KP
deletion--reinsertion shows that the target is absent from the raw image.  The
enumerator uses neither the 73 actions nor P-Knuth component labels.

Across all 429 rank-seven orders, the generated graph has 6,877 edges and
exactly 5,162 target vertices; components have at most five sources and five
targets.  Three-stage maximum-cardinality matching (same `Q` and first height,
then first height, then unrestricted) selects 4,702, 458, and 2 pairs.  It
minimizes total four-coordinate motion cost and then the decreasing list of
edge costs.  Twenty-eight components tie in total cost, and the profile
resolves all of them.  The resulting 5,162 assignments agree exactly with the
earlier fiberwise catalog.  Thus the standard-word bijection through rank
seven is explicit, reversible, deterministic, and table-free; inversion
currently recomputes the finite graph rather than using an on-demand local
component closure.

The rank-seven direct standard catalog now builds from this graph map itself.
The defective-order three-letter coloring regression therefore transports the
ordinary semistandard Kashiwara operators through the table-free map and checks
weight, `asc=inv_G`, both directions, and all lowering/raising inverse pairs.

Every selected edge has a P-Knuth certificate with at most two symmetric
margin letters: the minimal-margin counts are `(210,4014,938)`, with maximum
shortest-path lengths `(14,26,38)`.  The asymmetric two-before/one-after rule
loses no selected edge.  The 460 shape-changing recording moves have 318
unique descent-preserving rim candidates and 142 two-candidate cases.  The
release `--kp-correct 7` census, all fifteen tests, Clippy with warnings
denied, formatting, and the diff check pass.  The table-free graph checkpoint
is `1b2532f`.

There is now also a full all-rank Garsia--Milne repair which extends raw
Kim--Pylyavskyy insertion.  Let `B` be the proved BEPS component-rank
bijection and `R` the injective raw KP map on the words where its output is a
valid pair.  From a bad word `x`, alternate `B(x)` with the unique raw owner
`R^{-1}(B(x))` until `B(x)` is not raw-occupied.  The partial transition is
injective and takes values in the raw-good words, so a path starting at a bad
word cannot enter a cycle; reversing the alternating trace gives the inverse.
Both maps preserve P-descent and P-inversion, so the hybrid does also.
Standardization therefore extends it to proper colorings with weight and
`asc=inv_G` preserved, and genuine type-A crystals transport in the usual
way.

The Rust `--kp-gm` census covers every order through rank six.  At rank five
it preserves 5,038 raw pairs and corrects two, with maximum alternating length
two.  At rank six it preserves 94,928 raw pairs and corrects 112, covers all
95,040 targets, and has maximum alternating length ten.  The dedicated test
also transports the coloring crystal through the hybrid.  This completes the
all-rank bijection requested by the user, but not the stronger all-rank local
insertion problem: each `B` step still enumerates a full P-Knuth component.
The Garsia--Milne checkpoint is `c0331c8`.

On 2026-10-16, the Chromatic P-array RSK worker completed a direct bijection
which avoids inverse Kostka.  The new primary source is paper-cache 354,
Blasiak--Eriksson--Pylyavskyy--Siegl, arXiv:2211.03967v2.  In each standard
P-Knuth component and P-descent fiber, their Theorems 3.9--3.10 give equal
numbers of words and pairs `(P-tableau,SYT)`; fixed lexicographic rank gives
an explicit bijection.  Color complementation, decreasing-chain block
standardization, tableau transposition/destandardization, and the ordinary
semistandard Schuetzenberger--Lusztig involution extend it to all proper
colorings, preserving weight and `asc=inv_G`.  Both directions and the
transported Kashiwara operators are implemented.  The construction and proof
are in `docs/chromatic-p-array-rsk/DIRECT_MAP.md`.

The complete census covers every natural unit interval order through rank
five: 55,125 fixed-alphabet rank-five colorings, exact target coverage, and
96,968 lowering edges with raising inverses.  At ranks four and five there
are respectively 187/188 and 1,820/1,849 P-Knuth components/P-tableau
anchors; only one and 21 components need splitting.  The direct rank-five
map differs from the Allen--Celano--Mason signed map on 39,666 colorings, so
it is a third crystal gauge.  Six unit tests, Clippy with warnings denied,
formatting, `git diff --check`, and the full release census pass.
The verified checkpoint is `70699d8`, merged and pushed to `main`.  The
worker has released `docs/chromatic-p-array-rsk/`,
`experiments/chromatic-p-array-rsk/`, and its focused `HANDOFF.md` entry.

The three authorized read-only assessments agree that locality is now the
remaining problem.  On the forbidden order `(2,4,4,5,5)`, Kim--Pylyavskyy
insertion is valid on 17 vertices of the 19-vertex exceptional component.
Only `35241` and `34521` collide at the invalid tableau `312/54`; replacing
it by the valid tableau `213/54`, whose column word is `52413`, fills exactly
the missing shape-`(3,2)` fiber.  A standalone crystal-compatible
inverse-Kostka differential is impossible already from
`m_(2)=s_(2)-s_(1,1)`.  The next local experiment is therefore the complete
Kim--Pylyavskyy trace with this ladder-climber correction, followed by the
rank-six overlap/confluence census.  The worker touched no Lean source or
build, marked-coloring/HRV file, circular LLT file, or manuscript file.

On 2026-10-16, the Chromatic P-array RSK worker implemented the exact
Loehr--Mendes reverse inverse-Kostka involution as a second oracle and threaded
it through the complete Garsia--Milne coloring bijection.  The source is now
paper-cache 353, *Bijective matrix algebra*, with searchable full text.  The
implementation uses the Section 7.3 palindromic Bender--Knuth normalization,
the modified Egecioglu--Remmel move, and the Section 7.5 carrier.  It asserts
the carrier's strict-dominance-chain invariant and checks that every reverse
run has the reversed primitive trace with pushes and pops interchanged.

Astra independently reviewed the representation and proof decomposition and
reproduced the published rank-six endpoint without using repository code.  Its
review caught the essential architectural point: the existing stable
bubble-sort normalization has the right content but can give a different
tableau, so the Loehr--Mendes word remains a separate map.  The regression
suite includes this discrepancy, the rank-two fiber, Example 54, and the
published rank-six distinction from Allen--Celano--Mason.

The resulting coloring map is an explicit weight- and
ascent/inversion-preserving bijection onto the same pairs `(T,Q)`.  Exact full
fixed-alphabet checks through rank five cover 55,125 rank-five colorings.  At
rank five, 210 of 376 inverse-Kostka endpoints, 4,211 coloring images, 15,655
of 220,500 lowering-operator tests, and 2,780 of 220,500 simple reflections
differ from the Allen--Celano--Mason gauge.  The first map and `f_i`
differences occur at rank four; the first `S_i` difference occurs at rank five.
Thus replacing inverse Kostka produces another normal type-A coloring crystal,
but does not select a canonical or more local one.

The verified checkpoint is `fc004bd`.  All five unit tests, Clippy with
warnings denied, formatting, `git diff --check`, and the 27.8-second full
release census pass.  No Lean source or build, marked-coloring/HRV file,
circular LLT file, or manuscript file was touched.  The worker has released
`docs/chromatic-p-array-rsk/`, `experiments/chromatic-p-array-rsk/`, and its
focused `HANDOFF.md` entry.

On 2026-10-15, the Chromatic P-array RSK worker and an Astra reviewer audited
alternative inverse-Kostka proofs without changing code.  Mason's
noncommutative tunnel-hook formula (Allen--Mason, arXiv:2207.05903) is already
the foundation of the implemented Allen--Celano--Mason `psi/theta`
construction; the positive dual-immaculate-to-Young-quasisymmetric-Schur
insertion instead adds composition-tableau/DIRT recording data and does not
give the required reverse `K^{-1}K` cancellation.  The best genuinely
different full endpoint involution is Loehr--Mendes's bijective-matrix-algebra
conversion of the Egecioglu--Remmel `KK^{-1}` map.  It is a useful candidate
for a second finite oracle, but no improved locality follows from that proof.

There is also a universal rank-two obstruction to repairing crystal locality
by merely replacing this cancellation.  For `nu=(2)` and `mu=(1,1)`, the
signed fiber consists only of the positive row tableau `12` and negative
column tableau `1/2`, so every cancellation must pair them.  Ordinary
Kashiwara `f_1` sends the row tableau to `22` but is undefined on the column
tableau.  Thus no sign-reversing involution on the present common signed set
can commute strictly with the ordinary crystal operators.  A different
inverse-Kostka proof may change the transported coloring gauge, but an
intrinsic crystal construction needs either an enlarged state space or a
different target correspondence.  The audited paths remain released; no
Lean, Rust, HRV, circular-LLT, or manuscript file was touched.

On 2026-10-15, the Chromatic P-array RSK worker reclaimed only
`docs/chromatic-p-array-rsk/`, `experiments/chromatic-p-array-rsk/`, and its
focused `HANDOFF.md` entry to study the weight- and ascent-preserving
correction `C_i=S_i^P R_i` between the genuine transported reflection and the
natural component-signature/Ehrhard reflection.  The goal is an exact finite
census of its support, order, locality, and relation to braid and
inverse-Kostka defects.  All previous exclusions and the absence of a Lean
build slot remained in force.  This task is complete at checkpoint `e5a2bb5`,
and the three paths are released again.

The correction is a content- and ascent-preserving fiber permutation, with
`C_i^{-1}=R_iS_i^P` and `R_iC_iR_i=S_i^PC_iS_i^P=C_i^{-1}`.  Through rank
five it fixes 197,212 of 226,008 state/root pairs; nontrivial cycle lengths
range from 2 through 20 with gaps.  Of the 28,796 nontrivial states, 3,036
retain the source insertion tableau and 25,760 cross insertion tableaux, so
inverse-Kostka traversal is a major but not exclusive source of the gauge.
The flattened detailed inverse-Kostka `psi/theta` word is now replayable:
content plus the word reconstructs `(lambda,Q)`, and adding `T` gives a formal
reversible certificate.  Replay was asserted on all 56,993 full-alphabet
colorings through rank five.

For adjacent roots the weak braid holonomy is `D=(R_iR_j)^3`, and the exact
correction identity is `LD=M`, where `L` and `M` are the three appropriately
conjugated correction factors.  On all 1,296 rank-six `(3,2,1)` cases the
cycle inventory of `D` is 1,258 fixed points, eleven 3-cycles, and one
5-cycle.  More generally, on the path with `n=2a`, the content/ascent fiber
`(a,a-1,1),a-1` is explicitly indexed by the position of its unique color
three.  The induced holonomy is one `(2a-1)`-cycle for odd `a`, and has cycle
lengths `a/2,a-1,a/2` for even `a`; hence weak braid-defect order is
unbounded.  The exact formula and its reversal/color-complement proof are in
`SIGNED_SETS.md`, with Rust checks through `a=10`.  Two colorings can also
have identical complete ordered colored component words for both roots but
different holonomy, so separate odd-component signatures omit essential
cross-root interleaving.  Four unit tests, Clippy with warnings denied,
formatting, `git diff --check`, and the 22.8-second full release census pass.
No Lean, marked-coloring/HRV, circular LLT, or manuscript file was touched.

On 2026-10-15, the Chromatic P-array RSK worker reclaimed only
`docs/chromatic-p-array-rsk/`, `experiments/chromatic-p-array-rsk/`, and its
focused `HANDOFF.md` entry to study the total simple-reflection action
transported from the SSYT crystal.  The immediate tasks are to implement the
Lusztig/Kashiwara string reflections on colorings, verify involution,
weight-swap, commutation, and braid relations through rank five, and compare
them exactly with the Shareshian--Wachs odd-component color switches.  All
previous exclusions and the absence of a Lean build slot remain in force.
This task is complete at checkpoint `21ee7d2`, and the three paths are
released again.

The prototype now implements the total transported crystal reflections
`S_i^P=Phi^{-1} S_i Phi`.  On all fixed-alphabet graphs through rank five it
checks 226,008 state/root pairs, 169,016 adjacent braid identities, and
167,155 distant commutations, as well as involution, weight swap, properness,
and ascent preservation.  The reflections agree with SW odd-component
switches in 169,220 cases; the SW switches themselves have 7,236 braid
failures.  Classical tableau Bender--Knuth agrees with the crystal reflection
in 199,316 cases but has 13,330 braid failures after transport, so neither
content switch should be identified with the genuine Weyl action.

The natural signature repair—order odd two-color components, cancel their
majority signs, and flip only the excess unmatched components—passes every
rank-five braid test only for structural reasons.  Astra identified rank-six
content `(3,2,1)` as the first genuine test.  Across all 132 natural unit
interval orders, every basic order/cancellation convention has 38 failures
among 1,296 colorings of that content and 228 among 16,020 total braid tests.
For Hessenberg code `(1,2,4,5,6,6)`, increasing order and `+-` cancellation
give the exact certificate `121321 -> 133232` under `S_1 S_2 S_1` but
`121321 -> 233231` under `S_2 S_1 S_2`.  Astra's independent implementation
of Ehrhard's alignment agrees with this signature reflection on all 2,592
single-reflection checks in that orbit; the witness is therefore also a
concrete braid failure for Ehrhard's weak operators.  The 18.7-second release
census, four unit tests, Clippy with warnings denied, formatting, and
`git diff --check` pass.

On 2026-10-15, at the user's request, the Chromatic P-array RSK worker
reclaimed only `docs/chromatic-p-array-rsk/`,
`experiments/chromatic-p-array-rsk/`, and its focused `HANDOFF.md` entry to
expose the conjugated Kashiwara operators as explicit coloring-level
functions and verify their normal type-A structure.  The insertion tableau
must remain fixed, ascent must remain constant, and the finite checks must
cover string parameters and highest-weight/component behavior, not merely
partial inverse identities.  The marked-coloring/HRV, circular LLT, Lean,
and manuscript lanes remain excluded, and this worker still holds no Lean
build slot.  This task is now complete and those paths are released.

The checkpoint `4b906e3` adds explicit coloring-level `e_i` and `f_i`, a
complete fixed-alphabet crystal-graph constructor and DOT exporter, string and
highest-weight checks, and an inverse-Kostka/Kashiwara defect census.  For all
64 natural unit interval orders through rank five, the complete `k=n` graphs
have 56,993 vertices, 99,360 directed edges, and 2,065 components in total;
every component is a fixed-`T` copy of `B_k(lambda)`.  At rank five alone the
counts are 55,125 vertices, 96,968 edges, and 1,849 components.  The highest
coloring in the component indexed by `T` is exactly
`R_lambda^{-1}(T)`.  The one-empty-color census checks 292,322 rank-five
string identities and 120,659 lowering edges.

Astra independently assessed the locality data.  This particular transported
crystal is global even for a chain: in one-based colors
`f_1(112)=221`, `f_1(132)=322`, and the colorings `1134`, `1143` have the same
weight, ascent, and labeled `1/2` restriction but map to `2134`, `4321`.
Thus fixed reading-word signatures, Ehrhard-style two-row moves, active-pair
component switches, and naive standardization are all excluded for this map.
The Shareshian--Wachs involution commutes with the recording-tableau operator;
the first obstruction is the rank-two failure to commute with the reverse
inverse-Kostka involution.  Through rank five, 309 of 1,120 tested
inverse-Kostka/operator pairs are defects (226 definedness, 83 unequal value).
The next focused experiment is a marked-trace classification of those defects
by Allen--Celano--Mason `psi/theta` event words.  Tests, Clippy with warnings
denied, the 12.9-second full release census, DOT smoke output, and
`git diff --check` all passed.

On 2026-10-15, the Chromatic P-array RSK bijection worker completed a separate
research lane for an explicit weight- and ascent/inversion-preserving map from
proper colorings/P-arrays of natural unit interval orders to pairs of a
P-tableau and an ordinary semistandard tableau.  During the task it owned only
`docs/chromatic-p-array-rsk/`, `experiments/chromatic-p-array-rsk/`, and its
focused updates to `HANDOFF.md`, on branch `chromatic-p-array-rsk` in an
isolated worktree; those paths are now released.  The first milestone was
mathematical: identify the exact
Shareshian--Wachs/Gasharov and LGV signed sets, involutions, and any
Garsia--Milne alternating-path certificate before writing executable code.
Only after that audit may the worker add the bounded Rust prototype and test
natural unit interval orders beginning with `n <= 5`.  It does not own or
touch the marked-coloring/HRV e-positivity project, Lean sources, circular LLT
work, or manuscript files, and it holds no Lean build slot.

The mathematical audit has fixed the common signed set in
`docs/chromatic-p-array-rsk/SIGNED_SETS.md`.  The source-side `asc` statistic is
first converted to the Shareshian--Wachs array `des` statistic by color
complement followed by their odd-component Bender--Knuth switches; a second
such normalization sends an arbitrary packed content `mu` to the partition
`mu^+`.  On the common signed set, the first involution must realize the
historically harder reverse inverse-Kostka identity, while the second is the
Shareshian--Wachs array involution conjugated by those normalizations.  Thus a
bare LGV tail switch is not enough: it proves Jacobi--Trudi locally, but does
not itself supply the required `K^{-1}K` cancellation.  The implemented
replacement is Allen--Celano--Mason Algorithm 5.4, translated by
`sigma=pi^{-1}` and conjugated by ordinary tableau Bender--Knuth maps.  The
note also records explicitly that Ehrhard's operators
are only weight-shifting partial inverses, not normal type-A Kashiwara
crystals.  Astra's completed read-only audit confirmed the inverse-Kostka
orientation and conjugated-involution closure, supplied the exact import of
Allen--Celano--Mason Algorithm 5.4, and showed that Kim--Pylyavskyy extends to
repeated colors by block standardization on its avoidance class.

The bounded Rust prototype and its durable report are now in
`experiments/chromatic-p-array-rsk/` and
`docs/chromatic-p-array-rsk/COMPUTATION.md`.  It exhaustively verifies all 64
natural unit interval orders through `n=5`, all 13,701 packed proper
colorings, every weight/q fiber, both involutions, all forward and reverse
alternating paths, and exact target coverage.  It separately verifies all 376
reverse inverse-Kostka endpoints through rank five.  The longest fully local
trace has 120 events.  The Kim--Pylyavskyy avoidance test identifies 63
eligible orders and
13,437 eligible colorings; the sole excluded rank-five order has Hessenberg
code `(2,4,4,5,5)`, namely `P_(3,1,1),5`.  The smallest fixed-shape LGV and
same-cut obstruction is the exact `n=2`, `mu=(1,1)`, `nu=(2)` fiber; a naive
all-tail exchange first changes q at `n=4` for `m=(1,3,3,4)` and
`G={{2,3}}`.  The map also handles weak contents in a fixed alphabet: 67,682
rank-five cases with one inserted empty color class were checked.  Transported
ordinary Kashiwara operators on `Q` were verified to be partial inverses that
preserve properness and `asc`, with the expected simple-root weight changes.
No Lean source, Lean build, marked-coloring/HRV file, circular LLT file, or
manuscript file was touched.

The signed-set checkpoint is `1ec0ea3`; the verified Rust/report checkpoint
is `f77cd34`.  The branch is `chromatic-p-array-rsk`, pushed to `origin`.
On 2026-10-15 the user asked this worker to resume ownership of the same three
paths until the finite lexicographic matching had been replaced by a full
constructive bijection.  That milestone is complete: the local
Allen--Celano--Mason trace is integrated into every forward and inverse
Garsia--Milne path, and no global fiber matching remains.  The same exclusions
and absence of a Lean build slot remained in force.  The verified constructive
checkpoint is `e9b44d4`; the worker has released its three owned paths again.

On 2026-10-13, the Lilan revision integration worker completed the
author-requested Overleaf upload and email notification.  The current main TeX
file, bibliography, seven section files, and verified PDF were synchronized to
`/home/paxinum/Dropbox/Apps/Overleaf/LLT flip/paper/`; byte comparisons confirm
that they match GitHub.  Older Overleaf drafts, archives, project notes, and
already-identical manuscript files were untouched.  A fresh external build
from the synchronized snapshot in
`/tmp/verticalstripllt-overleaf-verify-Z4Vveb` produced the same 28-page PDF,
with no TeX, bibliography, reference, citation, or box warnings, and passed
`qpdf --check`.  An email summarizing the revision and linking GitHub was
successfully delivered to the Nankai address Lilan used for UID 88, with the
current PDF attached.  The worker has released `HANDOFF.md` and all external
manuscript files.

On 2026-10-13, the Lilan revision integration worker completed the
author-approved wider page geometry from Lilan's revision.  The main file now
uses letter paper with 2 cm top/bottom and 3 cm left/right margins (and a 2 cm
margin-note width), reducing the manuscript from 37 to 28 pages without any
prose or mathematical change.  The manuscript was built only in
`/tmp/verticalstripllt-wide-pages-Dly3PP`; the final build has no BibTeX,
LaTeX, reference, or box warnings and passes `qpdf --check`.  All pages were
inspected at thumbnail scale, with the title, dense figure/proof pages,
Section 7.3, and bibliography additionally inspected at full size.  The
rebuilt `paper/llt-flip-classes.pdf` has SHA256
`6e3104e75767ad1b927ab1819d5570a470b18d416eb554ac45b174517c9188ea`.
The Overleaf tree remained read-only, and no Lean source or Lake command was
used.  The worker has released `HANDOFF.md`, `paper/llt-flip-classes.tex`, and
`paper/llt-flip-classes.pdf`.  The verified layout checkpoint is `b3fe6b5`.

On 2026-10-13, the Lilan revision integration worker completed the
author-approved comparison of Hwang's and the LLT flips, Section 5 readability
pass, and Section 7.3 literature clarification.  The preliminaries now state
Hwang's local move precisely: it reverses a source or sink fork in an acyclic
orientation, whose outer vertices are nonadjacent.  The LLT move instead acts
inside a triangle, retains its long edge, and uses covers in the
ascending-and-strict-edge posets.  Section 7.3 explains that OpenAI's aggregate
chromatic theorem does not settle Hwang's classwise conjecture, while this
paper proves the LLT classwise analogue, and it asks for a relation between the
two genuinely different component decompositions.

The registered `arxiv-symmetricfunctions` index, Hwang's exact v2 manuscript,
and the current OpenAI manuscript were checked.  Searches for later work on
Hwang's local flips and for a bijection matching this paper's highest-reachable
component theorem found no general resolution; known special cases of Hwang's
conjecture do not settle the question stated here.  Section 5 received only
short strategy paragraphs before its complete-graph, deletion, last-clique,
and first-vertex arguments; no proof step or notation changed.

The manuscript was built only in
`/tmp/verticalstripllt-section57-9peFpB`.  The final 37-page build has no
BibTeX, LaTeX, reference, or box warnings, passes `qpdf --check`, and the
changed pages were inspected.  The rebuilt `paper/llt-flip-classes.pdf` has
SHA256
`875b2d6c1bfa4d2d5967338e06cd0142395dbf640df9ced6376524f654391f18`.
The verified flip-comparison and readability checkpoint is commit `5131de0`.
No Lean source or Overleaf file was touched.  The worker has released
`HANDOFF.md`, `paper/sections/preliminaries.tex`,
`paper/sections/connectivity.tex`, `paper/sections/consequences.tex`, and
`paper/llt-flip-classes.pdf`.

On 2026-10-13, the Lilan revision integration worker completed the
user-requested arXiv-index cross-check and literature update in
`paper/sections/introduction.tex` and `paper/references.bib`.  The registered
`arxiv-symmetricfunctions` API was current through 2026-10-13 and confirmed
the metadata and publication status of all eleven arXiv records checked.  This
supplied missing arXiv identifiers for AS22, the Ellzey FPSAC paper and Hikita,
and Hwang's published DOI.  The introduction now distinguishes Hikita's
numerical nonnegativity for each fixed positive real `q` (with `q=0` by
specialization) from OpenAI's later coefficientwise theorem in `N[q]`, citing
the exact Corollary 1.2 and Theorem 1.1.

The `paper-cache` full-text archive endpoint was unavailable because its
archive database is not mounted in this container; the exact cached Hikita v2
source and OpenAI's official September 24 manuscript were checked instead.
An external `latexmk` build has zero BibTeX, LaTeX, reference, or box warnings;
the 37-page PDF passes `qpdf --check`, and the revised introduction and final
bibliography page were inspected.  The rebuilt `paper/llt-flip-classes.pdf`
has SHA256
`9b7636a5eb49decfc36f63f27d0b579f1e3e1670bcd76a99d37db660193a85a6`.
The verified literature checkpoint is commit `16771e0`.
No Lean source or Overleaf file was touched.  The worker has released
`HANDOFF.md`, `paper/sections/introduction.tex`, `paper/references.bib`, and
`paper/llt-flip-classes.pdf`.

On 2026-10-13, the Lilan revision integration worker completed the requested
bibliography-metadata cleanup in `paper/references.bib`.  The Abreu--Nigro and
Lee preprints now use their published journal records; the Ellzey FPSAC paper
uses its official SLC citation; genuine arXiv/preprint items use suitable entry
types; and the Hikita paper is recorded as electronically published, without
inventing volume or page data.  An external `latexmk` build has zero BibTeX,
LaTeX, reference, or box warnings; the 36-page PDF passes `qpdf --check`, and
the bibliography pages were inspected.  The rebuilt
`paper/llt-flip-classes.pdf` has SHA256
`1366c6e313fa65c8e5e0f7b21cb78a184e9b3e24fae137e903d91d62dad85310`.
No Lean source or Overleaf file was touched.  The worker has released
`HANDOFF.md`, `paper/references.bib`, and `paper/llt-flip-classes.pdf`.  The
verified bibliography checkpoint is `53af2c9`.

On 2026-10-13, the Lilan revision integration worker adopted the manuscript
revision after the former Claude owner session was confirmed absent by
`supervisor-tool report`.  During this bounded task, the worker owned `HANDOFF.md`,
`paper/llt-flip-classes.tex`, `paper/llt-flip-classes.pdf`,
`paper/references.bib`, and the seven files under `paper/sections/` for the
task of reconciling Lilan Dai's UID 88 comments with the current GitHub
manuscript.  The attachments were inspected only in an external `/tmp`
directory, and the Overleaf tree remained read-only.  No Lean source, Lean
build slot, deployment, print job, or external correspondence was in scope.

The UID 88 reconciliation is complete.  Comments 1--11 and 13--36 were
applied or adapted to the current notation and architecture.  Comment 12 was
already satisfied by the newer GitHub contact figure and caption.  Comment 37
was not applied: its `geometry` override is presentation-only and predates the
newer GitHub figures.  The postscript about unspecified recent work was
deferred because it identifies no paper or citable claim.  In particular, the
revision keeps the later GitHub figures and notation rather than copying the
older magenta Overleaf source wholesale.  Section 5 now states the
occupied/vacant exchanges, the four restoring flips, the edge-count bounds and
the exceptional-cardinality argument explicitly.

The manuscript was built only in
`/tmp/verticalstripllt-lilan-uid88-FK61nC/build`.  The 36-page PDF has SHA256
`253f3e6892f8f79c8ece148a5bad48638e5e8e88b7ebc372491c6541d65a0fff`.
The final LaTeX log has no LaTeX, reference, overfull or underfull warnings;
`qpdf --check` passes, `git diff --check` passes, and the revised pages were
visually inspected.  BibTeX retains eight incomplete-metadata warnings,
including the page-free electronic Hikita journal record.  No Overleaf file
was modified and no Lean build was run.
The verified manuscript checkpoint is `8010a2b`; the integration worker has
released all adopted files.

The active author-directed manuscript remains the **component-first** `paper/`,
per `paper/PLAN.md` and `docs/LEAN_COORDINATION.md`.  The former Claude
ownership is superseded by the adoption above; the older `docs/drafts/`
sources and the aggregate-first descriptions below are retained history, not
the current manuscript architecture.

Codex reviewed `paper/` at `3a28bc1`, including the figures/examples at
`8af0161`, without editing it. See
[the review](docs/proofs/CLAUDE_MANUSCRIPT_REVIEW_2026-10-01.md) for exact fixes:
admissible versus acyclic orientations in Theorem B; a missing cover hypothesis
in one connectivity paragraph; an overbroad Lean-verification claim; and
smaller wording/presentation follow-ups. The two independent read-only reviews
found no substantive gap in the ordinary or circular component arguments.
The isolated 33-page TeX build passes without warnings or box errors; all 79
labels and 156 references check. Codex owns only this review and handoff update.
The review agents have finished and hold no files. No Lean build was run.

## Earlier Codex manuscript checkpoints

The AS22 case audit after `8eb8550` found an exposition omission in the
aggregate direct NN/DN orientation proof. The four-selection HRV identity
replaces the finer AS22 orientation tables, but its assembly was too terse.
The manuscript now gives separate source/target edge tables, the NN target's
two states, both DN triangles, exterior-selection reindexing for the empty
local selection, and transitive-closure matching for the full local selection.
Independent read-only review checked this against
`Circular/FirstBounceOrientation.lean`, `FirstBounceOrientationMatching.lean`,
`DNOrientationBlocks.lean` and `SecondBounceOrientation.lean`.
No Lean source or build was touched. The rebuilt PDF is 46 pages, with no
warnings or box overflows; source hashes and all references were checked.
Codex owns these manuscript/handoff edits; `bounce_case_audit` has finished
its read-only review and holds no files.

After `9702fef`, the introduction explicitly distinguishes the AS22 diagram
method and cited background from proof dependencies: we prove the required
circular local identities and recover the ordinary expansion without assuming
the AS22 expansion or uniqueness theorem. The component identity further
refines both cases. Also repaired two malformed internal manuscript links caused
by the preceding notation pass. The rebuilt manuscript has 45 pages and no
LaTeX warnings or box overflows. Ownership and mathematical scope are unchanged.

The author's diagram and exposition revision after `e4c7159` is complete.
The six-section outline is recorded in
[REVISION_OUTLINE](docs/drafts/REVISION_OUTLINE.md): introduction and both main
theorems; circular aggregate expansion; ordinary component recurrence;
connectivity by flips; circular components; cumulants. The long connectivity
proof remains in the main text, now in `ORDINARY_FLIP_CONNECTIVITY.md`, after
its precise statement and role in the ordinary recurrence. Its already-proved
initial-path extension is explicit in the statement.

The manuscript states the original Alexandersson--Sulzgruber four relations,
then their shifted forms and exact induction orders. The source uniqueness
proof uses the height of the FIRST east step. The ordinary component proof
uses vertex count, total natural area and area moment; the circular aggregate
proof has its separate two-statistic order. Auxiliary DD derivations are
explicitly distinguished from outer induction calls.

Gray denotes the exterior of the path. Generic diagrams use zigzags for
arbitrary intervening portions and adjacent steps for consecutive vertices.
The author-supplied Robin-source snapshot and earlier Alexandersson--Dai TikZ
pictures were consulted read-only. A new three-vertex flip figure explains
a full component and its elementary contribution in the introduction.
Path steps use typewriter letters, evaluations use sans-serif K/E, and
unnecessary indexed states and proof-stage names have been removed.

Codex owns this handoff, manuscript/figures and proof maps. Bounded agents
`diagram_spacing_audit` and `notation_audit` have released their files.
At that earlier checkpoint, Claude worker
`agent-verticalstri-motzki-c-001af720` owned all Lean sources, verification
entry points, `docs/LEAN_COORDINATION.md`, and the sole Lean build slot
(transfer at `b78312c`).  The session no longer exists; this manuscript-only
task did not adopt any of those Lean files or invoke the build slot.

Check Git status and HEAD before edits; Claude commits on shared `main`.
Stage only owned files. Preserve the pre-author-edit tag and its original PDF.
No external Overleaf file was edited and the revised PDF has not been printed.
The author/AI statement correction at `e4c7159` remains: no cumulant
formalization caveat in the manuscript; the published attribution remains.
Internal scope is unchanged: no new Lean theorem is claimed for that corollary.

## Verified mathematical scope

See [DIAGRAM_PROOF_COMPLETION](docs/DIAGRAM_PROOF_COMPLETION.md).

- `f2f396f` completed the ordinary diagram induction; `1b6d13e` exported and
  audited it. `55cfaf5` streamlined attachment and shared local lemmas.
- `77cabb9` derives the circular component theorem from this diagram proof
  through the finite circular companion. The compatible preimage is a union
  of complete ordinary components, possibly several, not an assumed single
  component. Independent review approved the public scope and this reduction.
- `98ad880` separates the older word proof into `WordProof/` and removes dead
  diagram modules. The circular theorem's 360-file closure is unchanged and
  contains no word/scan theorem. The ordinary and circular public contracts
  have no recurrence certificate, balance or assumed semantic-bridge premise.
- `1a9eb1f` gives the diagram theorems the plain names
  (`component_strict_eq_elementary`, `..._of_forward` and relatives); the word
  proof's theorems end in `_by_words`, and the interim `_by_diagrams` names are
  deprecated aliases. The 215 diagram modules sit in 13 proof-step folders
  under `DiagramProof/`, described in `Components/DiagramProof.lean`.
  Docstrings and linter fixes changed no statement.
- Latest full library build passes: **2367 jobs**, `full-build-1a9eb1f.log`;
  the only warnings are seven unused hypotheses in public `WordProof`
  statements. All **815** dedicated axiom queries and the 2814
  `Verification.lean` queries use only standard Lean axioms or none. The
  preceding 860-query audit at `77cabb9` also passed; the difference is unused
  helpers.

Logs live under
`/lake-cache/ai-projects/requests/VerticalStripLLT/claude-right-attachment/logs/`.
Immutable copies `axioms-77cabb9.log`, `axioms-98ad880.log`,
`axioms-1a9eb1f.log` and `verification-1a9eb1f.log` have hashes in the
completion report. The working log `axioms-4.log` was reused; do not infer
its contents from an older count. A
[workflow suggestion](suggestions/commit-stamped-axiom-logs.md) records this.

The circular aggregate theorem has its separate
[CIRCULAR_COMPLETION](docs/CIRCULAR_COMPLETION.md) audit. Both aggregate and
component results concern the actual coloring and integer-cover HRV semantics.

## Manuscript and diagram macros

Canonical prose and source correspondence:
[docs/drafts/README.md](docs/drafts/README.md). The introduction is followed by
`CIRCULAR_E_EXPANSION.md`, `ORDINARY_COMPONENT_DIAGRAM_PROOF.md`,
`ORDINARY_FLIP_CONNECTIVITY.md`, `CIRCULAR_COMPONENTS.md` and `CUMULANTS.md`. The latter include explicit
HRV deletion cancellation, the full finite coefficient argument, actual
cover-preserving flips and the compatible-lift union of ordinary components.
We do not claim each circular bounce/reversal restricts to a single component.

The revised manuscript is **46 pages with 14 vector figures**. The original
tagged baseline was 35 pages. The general
[llt-diagrams.sty](docs/drafts/tex/llt-diagrams.sty) and its
[usage guide](docs/drafts/tex/README.md) implement diagrams as restricted sums:
optional/selected/absent/forbidden/strict edge restrictions, cover conditions,
fixed-size layers, component restrictions and endpoint colors. The four-recurrence
figure uses actual north/east/diagonal boundary paths; other restricted sums
use the shared sparse TikZ renderer. Individual path states
are the fully specified special case. Native TeX sources generate all SVGs.
No external Overleaf manuscript was edited.

Rebuild with `python3 docs/drafts/build_manuscript.py --output /external/path`.
Python performs document conversion only. The assembler creates a PDF,
self-contained TeX source bundle and SHA256 input manifest. Build products
remain external:

`/lake-cache/ai-projects/requests/VerticalStripLLT/diagram-formalization/manuscript-revision/`

Files: `manuscript.pdf`, `manuscript.tex`, `manuscript-source.zip`,
`source-manifest.json`. Figure inspection images are in `figure-review/`;
PDF page previews are alongside the manuscript. The author metadata matches
the earlier Alexandersson--Dai draft.

Verification: the 46-page manuscript and four-page macro guide compile
without warnings or box overflows. The 171 labels are unique, all 130
references resolve, and all 26 source inputs match the bundle manifest.
There are 5 theorems, 27 lemmas, 10 propositions, 13 definitions, 2 corollaries,
2 examples and 43 proofs. The new introduction, original and shifted
recurrences, induction table and ordinary proof strategy were visually
inspected, as were all 14 figures. All SVG previews were regenerated.
Independent reviews checked the original-source correspondence, induction
orders, moved connectivity dependency, diagram spacing and notation changes.
`git diff --check` passes. The complete Lean proof is unchanged.

The revision PDF SHA256 is
`dd15b8d858532c459908e21013fac95cffb577f823b14f202bd1e0b4fdce2683`.
Paper-cache entries 496 (AS22), 497 (Hwang) and 498 (Dołęga--Kowalski)
contain exact-version PDFs, source archives and extracted text; precise
locators are in the draft README. The paper-cache database discovery call
`query_arxiv_sf` was unavailable because `pymysql` is missing; a web metadata
lookup located Hwang's arXiv ID, after which all source reading used the cache.


## Baseline for author revisions

Annotated GitHub tag `draft-v1-before-author-edits` points to `80c106d`, the
verified two-part draft produced with the combinatorics paper-writing skill.
Preserve this tag for comparison with the user's revisions and later skill
improvements. Compare tracked prose and figures with
`git diff draft-v1-before-author-edits -- docs/drafts/`.
If revisions are made to exported TeX, rebuild the tagged canonical sources
to recover the baseline TeX before comparing. The tag precedes the subsequent Lean refactoring and this author-requested
revision. The baseline 35-page PDF was submitted to R211 under receipt
`20261001T094755-e431ded0d3cb`; this revision has not been printed.

## Follow-up

The requested formalization and new draft are delivered. Further author
editing, selecting publication formatting, or editing the external Overleaf
copy would be subsequent tasks. Continue using the
[combinatorics paper-writing skill](/home/dev/.codex/skills/combinatorics-paper-writing/SKILL.md)
and preserve the two-part architecture and diagram proof correspondence.

The [handoff archive through `0c87ed0`](docs/archive/diagram-writing-through-native-figures.md)
preserves earlier proof work, ownership transfers and verification history.
Its unfinished-formalization statements are superseded here. Lean MCP is
rooted at RealRooted; the designated owner uses focused `lake-workspace`
commands. Aristotle remains available through the CLI when useful.
