> Historical planning record. Superseded by the [current documentation](../../README.md).

# Circular LLT and flip-component formalization plan

Architecture decision at the planning checkpoint, 2026-09-26. Current
implementation progress is in `HANDOFF.md` and `CIRCULAR_GOALS.md`; the milestone
descriptions below retain their planning meaning. The ordinary expansion remains complete.
Primary `/root` synthesized an independent read-only Astra review with its
own manuscript and pinned-Mathlib audit. The user prioritizes completing the
circular argument in the existing outline; components require further detail.

## Source and scope

The working source is the author's Overleaf project
`/home/paxinum/Dropbox/Apps/Overleaf/LLT flip/old-main.tex`, titled
*Circular Vertical-Strip LLT Polynomials*. Its sibling `main.tex` was empty
at the initial audit; it now contains the rewritten draft.
We use this substantive manuscript provisionally, together with its
`EDITORIAL-AUDIT.md`. The separate `LLT-flips/llt-flips.tex` is an earlier
ordinary flip-component draft. The original source files remain unchanged.
On 2026-09-26 the user explicitly authorized a TODO addition to current
`LLT flip/main.tex` for the missing neutral-bounce termination lemma; primary
added it beside the strict-chain discussion. Details and hash are in HANDOFF.md.

Hashes at the audit date, relative to the Overleaf directory:

| File | SHA256 |
| --- | --- |
| `LLT flip/old-main.tex` | `287b5017072d50505f8fa0849c0ecefc52aac6536bb881015ab9cbe1c8611ce0` |
| `LLT flip/EDITORIAL-AUDIT.md` | `5ee9f60e660944c882660a1da4cfe2a2b6c07282f50ae7259fbe73f894a539a3` |
| `LLT-flips/llt-flips.tex` | `d2b20fe9f59d556a483647e04ad4669fda754fc98e27d76a51bb56a75d9107d8` |
| `LLT-flips/computational-evidence.md` | `35e6b9def983d52e5d96f8e9a7e2443de7d0581bcaf03447105994752719c624` |

The circular aggregate formula is stated as `thm:circular-e-expansion`,
with explicit outstanding steps in its proof. The complete-component formula
is labelled `conj:circular-component-h`. These are formalization targets;
neither is currently a theorem of this repository. The outline supplies the
first proof strategy, not an assumption to insert into the final statement.

The weak P-partition/complete homogeneous formulation and the strict
P-partition/elementary formulation are related by omega. This is a translation
lemma, not a separate mathematical obstacle. The source's current weak
convention and the older draft's strict convention must be named consistently.
Cumulants and other circular conjectures remain outside this plan.

## Architecture decision

Add small modules under `VerticalStripLLT.Circular`; retain the existing Lean
package, coefficient ring `Q := Polynomial ℤ`, finite-alphabet `XPoly m`, and
formal `EExpansion`. Do not redesign the proved ordinary development or start
a general symmetric-functions library.

1. `CircularArea n` includes `0 < n`, `a i < n`, and the cyclic area inequality
   `a (i+1) ≤ a i + 1`. Use the manuscript's terminal-vertex convention.
   A natural `Edge` is a head and a positive length at most its area entry;
   its tail is obtained modulo n. Keep edge instances: two opposite natural
   arcs between a pair of vertices are distinct choices.
2. `Diagram` has a strict subset of admissible corner orbits. A row's corner
   is allowed precisely when `0 < a i` and `a (i+1) ≤ a i`.
   Coloring semantics can be defined for arbitrary strict subsets, but the
   expansion theorem must retain the corner restriction.
3. `Orientation` chooses a Boolean on each non-strict edge. Its selected
   relation contains every strict edge and each naturally oriented non-strict
   edge. `Admissible` means this projected relation is acyclic. It is not a
   condition on the entire oriented multigraph.
4. Lift vertices to integer positions and each natural edge to its positive
   displacement. Define `liftReachable`, its greatest endpoint `liftedHRV`,
   and `hrv` by projection. Acyclicity bounds path length by n−1 and displacement
   by (n−1)². A finite bounded search therefore suffices; no infinite maximum
   is needed. Translation equivariance proves lift independence.
5. Define `coloringLLT` directly from finite colorings, strict on the strict
   edges, weighted by ascents on non-strict natural edges. Independently define
   `shiftedOrientationExpansion` as the admissible orientation sum with weights
   q^asc and products of elementary generators for nonempty HRV fibers.
   Fiber sizes avoid unnecessary sorting into partitions.
6. Define finite `strictOrderEnumerator` and `weakOrderEnumerator` for the
   selected poset. Implement omega on fixed-degree coefficient data, using
   fundamental descent-set complementation/P-partition reciprocity. On the
   symmetric expressions it sends h_lambda to e_lambda. Apply this before
   finite-alphabet specialization; no general stable-function library is
   required. Mathlib's `MvPolynomial.hsymm` supplies complete evaluation.
7. Define flips by the full lifted cover relations in the manuscript. Normalize
   one lift to a fundamental period to obtain finite witnesses. Use a finite
   graph of admissible orientations and complete reachability components.
   Never substitute projected covers or covers computed only inside a chosen
   local window. Individual order enumerators need not be symmetric; omega's
   order-enumerator translation precedes the component symmetry conclusion.

Reuse the elementary evaluation, shift, positivity, and degree proof patterns.
Existing `Orientation`/`coloringLLT` are path-specific, so introduce adapters
rather than silently widening their hypotheses. Existing maximum-residue HRV
and increasing-vertex path lemmas are not circular HRV lemmas.

## Manuscript-to-declaration map

Names below are proposed within `VerticalStripLLT.Circular`, not existing APIs.
Line numbers refer to the hashed `old-main.tex`.

| Source | Proposed declarations and proof boundary |
| --- | --- |
| 245–389, area sequences and corner cells | `CircularArea`, `Edge`, `IsCorner`, `Diagram`, rotation equivalence |
| 480–552, colorings and admissible orientations | `coloringLLT`, `Orientation`, `selected`, `Admissible`, `asc` |
| 554–649, cover and HRV fibers | `liftReachable`, `reachable_span_le`, `liftedHRV`, `liftedHRV_translate`, `hrv`, `hrvFiber_card_sum` |
| Coloring expansion into selected relations | `shifted_coloringLLT_eq_strictOrder_sum`; prove directly by subset expansion |
| 1435–1498, `lem:no-wrap` | `periodic_strict_cycle_zero`, then the stronger `wrappedBounce_zero` with a same-state certificate |
| 1500–1532, `thm:circular-e-expansion` | `coloringLLT_shifted_eq_eval_shiftedOrientationExpansion`, then coefficient positivity and degree |
| 1597–1613, weak K convention | `weakOrderEnumerator`, `strictOrderEnumerator`, `omega_weakOrderEnumerator` |
| 1703–1728, K diamond | `weakOrderEnumerator_diamond`; local identity, not yet a component identity |
| 1939–1972, circular flips | `Flip`, `flipGraph`, `component`; full lifted covers and global connectivity |
| 1974–1986, component conjecture | `component_weak_eq_complete`, `component_strict_eq_elementary` via omega |
| 1988–2000, binary-word ordinary family | `chainGapFamily_component_eq_ascentFiber`, component identity by coefficient extraction |
| 2002–2048, invariants and factorization | `Flip.asc_eq`, `Flip.weakBlocks_eq`, `component_block_factorization` |
| 2342–2373, singleton argument | `singleton_selected_disjointChains`, `singleton_component_expansion`; first audit the geometric fork lemma |
| 2453–2495, zero non-strict area | `zeroArea_selected_chains_or_cycle`, `zeroArea_expansion` |
| 2530–2595, fragment reassembly | `Packet`, `BranchMultiplicity`, `reassembles_of_flip_invariant` |
| 3060–3095, simultaneous signed reduction | `ComponentReductionCertificate`, `component_expansion_of_reductions`; constructing certificates is separate |

## First slices and milestone boundaries

**C1: finite circular semantics and actual wrapping examples.** Implement the
first three data modules and finite coloring sums. For n=2 and a=(1,1), keep
both opposite natural arcs. With neither strict, four orientation choices
give three admissible orientations and the expected identity

    LLT(x;q+1) = e₁² + 2q e₂.

With one arc strict the polynomial is e₂; with both strict it is zero and the
admissible orientation set is empty. These are proposed all-alphabet tests,
not already checked Lean results. They exercise multiplicities, strictness,
cycles, and the existing elementary evaluation. All flip components here are
singletons; this slice does not test a nontrivial flip.

**C2: lifted HRV and unconditional orientation semantics.** Prove acyclic
path bounds, translation/rotation invariance, and the cut-to-ordinary bridge
when the data have an ordinary cut. Prove, independently of the HRV theorem,

    LLT_D(x;q+1) = Σ admissible θ, q^(asc θ) K_strict(selected θ).

Expand each coloring's (1+q) ascent factors into edge subsets; selected cycles
contribute zero. This gives an unconditional semantic checkpoint even while
the circular bounce proof is in progress. Also prove the general zero
non-strict-area family: disjoint directed chains give products of elementary
functions, and a full strict cycle contributes zero.

**C3: finish the aggregate circular HRV proof.** Transport the ordinary local
relations with precise cyclic geometry, prove the retained-state bounce
invariant and termination, then identify projected terminal orientation terms.
Obtain the unconditioned all-diagram/all-alphabet HRV identity, positivity,
degree n, and alphabet specialization. This is the first main target; it does
not depend on the general flip-component result.

**F1: component foundations and proved families.** This can overlap C3 through
bounded independent work after C2 interfaces settle. Prove flip symmetry,
ascent invariance, and weak-block invariance. Prove local K diamonds and the
omega translation. Check a nontrivial ordinary triangle flip, then the
binary-word family `n n d^(n−2) e e`. Establish zero-area components and, after
checking the fork argument, singleton and disconnected-factor cases.

**F2: complete-component transport.** Formalize fragments with exterior state,
packet multiplicities, and the criterion for reassembly into complete target
components. Prove the actual manuscript reductions preserve both K and HRV
expressions with the same coefficients. Induct to the general component
identity and its strict/e-positive formulation. Keep any conditional
certificate theorem separate from the eventual construction of certificates.

Each milestone ends at a small usable theorem. Circular total positivity and
component positivity are separate deliverables; a total sum identity alone
cannot isolate components sharing an ascent count. Coefficient extraction
works in the binary-word family because there is one component per count.

## Proof details to fill in

### Circular bounce: pursue the supplied outline first

The elementary fact is that a periodic strict coloring cannot contain a
selected path from a vertex to a positive translate of itself. The missing
bridge is that returning a bounce marker forces such a path **inside one
retained coloring state**. Relations from different intermediate branches
cannot simply be concatenated. Use an explicit branch state recording the
coloring transport, distinguished lift, and accumulated forced inequalities;
prove this invariant for each local move.

Crossing a cut is not itself a contradiction. The manuscript gives the
acyclic example n=4, a=(3,3,3,3), with selected edges 1→4→3→2 and lifted
positions 1→4→7→10. A proof must detect repetition of a residue in the required
same-state path, not merely crossing one or several cuts.

The outer measure is non-strict area. For neutral bounces the manuscript
proposes a strict-chain weighted-length rank J (2375–2452), with decrease −k
for a full ordinary bounce with k contacts. Its circular analogue requires
proof of chain separation, correct contact counting, and lift normalization.
Alternatively use a bounded-progress invariant on retained bounce states.
Do not reuse ordinary first-east height without defining a suitable cut.
Prove a genuine well-founded measure before defining a recursive invariant.
Proving any such invariant equals the coloring LLT remains a separate theorem.

### Components: global compatibility beyond local diamonds

The source already records obstructions to naive local arguments. Exterior
paths can destroy a presumed cover, and external flips can connect different
local states (2596–2612). Keep boundary orientations and lift identifications
in fragment data. Reassembly requires branch multiplicity to agree across
every target flip, including flips meeting or lying outside the local window.

Nor does every source component transfer as a linear combination of target
components alone: the example at 3007–3055 requires a solved source-component
correction. Use the proposed simultaneous signed reductions: for a positive
integer m_C, the same integer coefficients express both m_C K_C and m_C H_C
in smaller-diagram components plus already solved source components.
Characteristic-zero cancellation then closes the induction. Finding an
H-vector relation alone does not prove its K counterpart. Component size and
directed-flip normal forms are not established induction measures.

For disconnected reductions, vertex count can precede area and a proved
secondary bounce rank. The existence of the required reductions is part of
the mathematics to supply, not a field to assume on all diagrams.

## API, delegation, and verification

Pinned Mathlib already provides `Relation.TransGen`/`ReflTransGen`, finite
`SimpleGraph.ConnectedComponent` infrastructure, and `MvPolynomial.hsymm`
with map/rename/symmetry lemmas. Finset fiber-cardinality proofs from
`OrientationDegree` apply to any finite HRV map. A direct finite reachability
component is sufficient initially; no quotient-heavy public API is required.

Keep primary as strategy/integration/source-build owner. Once interfaces and
file ownership are recorded in `HANDOFF.md`, useful parallel, build-free lanes
are: Luna for finite edge/coloring adapters; Terra for bounded reachability
or a source/API audit; Aristotle for explicit cycle-zero, translation,
diamond, or multiplicity-constancy proof lemmas. A bounded Claude review can
inspect the retained-state invariant or packet argument with exact source
excerpts. No worker should be asked to prove an unspecified whole conjecture.
Use a few independent tasks, with candidate proofs or focused commits, and
integrate before assigning dependent work.

Only primary invokes Lean, after checking no global build is active, using
`lake-workspace` and external caches. Batch source changes, run focused checks
at interfaces, and run broad checks at theorem checkpoints. Remote candidates
require local verification and axiom/source guards. No builds or TeX
compilation are needed for this planning checkpoint. No new computation was
performed; any later enumeration must first audit the shared Rust APIs.

Acceptance: unchanged ordinary theorems and immutable references; independent
circular coloring and HRV definitions; unconditional final expansion; complete
global components; all-alphabet identities with degree and positivity; no
proof placeholders, custom axioms, or conjectures hidden in final hypotheses.
