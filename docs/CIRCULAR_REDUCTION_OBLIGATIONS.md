# Circular reduction obligations

This note records the exact remaining route from the general selected-order
identity to the full circular elementary expansion.  It is based on
`/home/paxinum/Dropbox/Apps/Overleaf/LLT flip/old-main.tex`, especially the
ordinary relations at lines 743--1433, `lem:no-wrap` at 1435--1498, the
circular theorem and its proof at 1500--1532, and the proposed neutral-bounce
rank at 2399--2452.  The source itself labels the central bridge as missing.
The corresponding editorial caveats are therefore mathematical obligations,
not Lean elaboration work.

## Target to prove

For every circular area sequence `a`, corner-restricted strict set `S`, and
finite alphabet, the full statement sought is

\[
  \operatorname{LLT}_{a,S}(x;q+1)
    = \sum_{A\subseteq E(a)\setminus S\atop S\cup A\text{ acyclic}}
        q^{|A|} K_{S\cup A}(x),
\]

followed by the independent identification of the total selected-order sum
with the lifted-HRV elementary sum.  The first equality is already the right
general semantic statement: `A` contains exactly the non-strict natural edges
made strict by the subset expansion.  It does **not** require an unproved
circular recurrence.  What remains is the full circular recurrence proof of
the HRV identification, not another small example.

Here an edge is represented by its terminal/head residue `h` and length
`r`, with lift `h-r -> h`; a strict edge is the maximal edge in a corner row.
Thus every proposed local operation below must be stated on head-based data
`(a,S)` and prove that its altered strict edges are still corner edges.

## Author's geometric area and direct termination proposal

The author prefers A_geom = sum a_i - |S|/2, counting each strict corner as
half a square. The branch decreases for R1/R2/R3/R4/R8 are respectively
(1, 1/2), (1), (0), (1, 2), and (1/2, 3/2, 2). Thus doubled geometric area
is a suitable integer primary measure. Terminal strict-only diagrams can
have positive geometric area; their already proved formula is a stopping
case independently of the value of that measure.

The author recalls a contradiction proof: an indefinitely continued forward
neutral-bounce procedure forces a directed cycle of strict edges. Formulate
and prove the precise marked forward procedure and the cycle in one reached
diagram. Its entire polynomial vanishes, and the neutral identities propagate
vanishing backwards. This would establish termination on nonzero diagrams
without requiring J as the reader-facing argument. Lilan may have a handwritten
proof. A user-authorized TODO now records this missing lemma in current
Overleaf main.tex. It is not yet a proved replacement for the obligations below.

## Area bookkeeping and current implementation

The author reiterated that the circular proof should follow the draft's
ordinary area-reduction relations. We retain that as the primary route.
For the displayed ordinary local configurations, the non-strict area changes
in the ordered right-hand branches are:

| Relation | Target area minus source area |
| --- | --- |
| R1 | −1, −1 |
| R2 | −1 |
| R3 | 0 |
| R4 | −1, −2 |
| R8 | −1, −2, −2 |

These counts do not by themselves establish a valid circular move: the lifted
exterior-incidence and corner conditions below still need proofs. Relation R3
explains why area alone is insufficient and why the draft introduces J.
The circular R1 coloring and HRV recurrences are now proved independently in
`Diagram.xQShift_coloringLLT_corner` and
`Diagram.shiftedOrientationExpansion_corner`. Their current Lean reduction uses
edge-count² + normal-edge-count. That is the termination measure for this
corner-only reduction, not the proposed full-bounce (area_ns, J) induction.

On 2026-09-26 primary supplied the exact relations, area-first strategy,
proposed J calculation, and exterior-incidence mechanism to the existing
Aristotle continuation via INSTRUCT. The task was already active; no separate
project or duplicate base-case task was launched. Exact message is retained
externally as `circular-expansion/RELATIONS_STEERING.md`.

## The actual local transitions

Write `t = q - 1`, as in the manuscript. After representing the affected local
boundary by a lifted word and retaining its full periodic exterior, the needed equations are
exactly the following positive equations (source lines 2498--2518):

\[
\begin{aligned}
 R_1:&\quad F_{U n e V}=F_{U e n V}+tF_{U d V},\\
 R_2:&\quad F_{U n.n V d.e W}=(1+t)F_{U n.n V e.d W},\\
 R_3:&\quad F_{U d.n V d.e W}=F_{U n.d V e.d W},\\
 R_4:&\quad F_{U n.d V d.e W}
       =tF_{U n.d V e.d W}+(t+1)F_{U d.n V e.d W},\\
 R_8:&\quad F_{U n.n e V e.d W}
       =tF_{U d.n V d.e W}+tF_{U d.n V e.d W}
          +F_{U e n.n V e.d W}.
\end{aligned}
\]

The source derives `R_8` from `R_3` and two uses of `R_1`; it explicitly
warns at 1277--1293 that the displayed signed equation in the opposite
direction raises non-strict area and cannot be used for induction.

For a formal circular transition, do not encode these only as word rewrites.
The operation needs a witness record

```
LiftedLocalMove (a S) (a' S')
```

containing a starting lift `c : Z`, a finite local window, the boundary-word
data in that window, one of `R1 | R2 | R3 | R4 | R8`, and proofs that:

1. its periodic head/length edges outside the displayed window agree;
2. every changed edge has the head and length read from the changed word;
3. `S'` is the old strict set with precisely the diagonal/corner edges of the
   target word inserted or removed; and
4. each inserted strict edge has length `a' head` and
   `a' (head+1) <= a' head`.

A general circular diagram need not have a cut giving a complete ordinary
Schroder path. The local witness must therefore retain crossing exterior arcs;
it cannot assume the existence of such a global ordinary cut. Transporting a
proved ordinary identity requires proving the necessary exterior-incidence
symmetries, not merely decoding the displayed local word.

This is the precise head-based answer to “which corner moves?”: a diagonal
step at lifted coordinates `(i,j)` represents the corner edge
`i -> j`, whose head is `j mod n` and whose length is `j-i`; the replacement
word says whether that edge is deleted, retained, or replaced by the next
diagonal edge.  The two simple ordinary graph descriptions already proved in
the repository show the required form.  In the first-bounce base, the source
strict edge is `low -> top` and the successor strict edge is `mid -> top`,
while `low -> mid` is the distinguished normal edge.  For the second bounce,
the source strict edges are `corner -> low` and `low -> top`; the target ones
are `corner -> mid` and `mid -> top`.  See
`FirstBounceGraph.lean:firstBounce_source_strict` through
`firstBounce_succ_strict`, and
`SecondBounceGraph.lean:secondBounce_source_strict` through
`secondBounce_target_strict`.  These are reusable graph-level local facts;
the circular adapter must lift their vertex indices and prove that none of
the relevant endpoints is identified modulo the selected window.

`R_1` removes the diagonal corner at `(i,j)` in its `d` branch and resolves it
to the two adjacent `n,e` or `e,n` cells.  The full bounce cases replace the
distinguished terminal strict edge by its next strict edge along the lifted
bounce path.  Consequently the implementation should not postulate a global
“circular recurrence certificate”: prove each `LiftedLocalMove` directly by
transporting the ordinary edge-set identities, then establish the coloring
identity by the same local swap/bijection used in the ordinary files.

## Exact admissibility and coloring obligations

For every branch of a local move, the statement must quantify over a selected
set, rather than merely over a diagram:

```
selected G A = G.strict union A
```

where `A` ranges over the branch's non-strict edges.  The needed theorem has
three alternatives for each source selected state:

1. an explicit transport of selected edges and a weight-preserving bijection
   of colorings, including the changed strict inequality;
2. an explicit partition into target selected states with the coefficient in
   `R1`--`R8`; or
3. a proof that this state has zero contribution.

The last case is only justified by a strict cycle in the **same coloring
state**.  Projected acyclicity is the definition of an admissible orientation
and is required only for surviving orientation terms.  It cannot, by itself,
prove no-wrap: the source gives an acyclic `n=4`, `a=(3,3,3,3)` orientation
with lifted path `1 -> 4 -> 7 -> 10` at 1470--1498.  Several crossings of a
fundamental cut are harmless.

The following is the minimal sufficient invariant for a repeated neutral
bounce.  A retained state consists of

```
(D, A, c, marker, markerLift, forced)
```

where `D` is the current lifted local diagram, `A` is the chosen ascending
edge set, `c` is one coloring transported through all prior local bijections,
`markerLift` is a lift of the distinguished strict edge, and `forced` is a
lifted directed path all of whose edges are either strict in `D` or members
of `A`.  It must satisfy:

* every edge of `forced` is imposed strictly by this same `c`;
* the terminal vertex of `forced` is the tail of the current marker (or the
  designated next bounce point, with a fixed convention);
* one local bounce extends `forced` by the strict edge that replaces the old
  marker, after applying the branch's coloring transport; and
* the lifted marker head strictly advances along the chosen lifted bounce
  path.

The desired theorem is then concrete:

```
wrappedBounce_zero:
  retainedState s -> markerResidue s = initialMarkerResidue ->
  coloringWeight of s = 0
```

The proof is not “it crossed a cut.”  Strict advance and equality of residues
give a positive translate of the initial marker endpoint.  `forced` then
projects to a directed closed walk whose inequalities hold for the *single*
retained coloring `c`; transitivity gives `c(v) < c(v)`.  This reduces to the
already available generic cycle-zero argument once the retained-state path is
shown to project into `strict union A`.

The manuscript does not provide the inductive preservation clause above.  It
only says each bounce replaces the marker by the next strict edge (1439--1445)
and explicitly requests a proof that every wrapped reduction creates the
chain in one retained coloring state (1458--1464).  This is a missing
derivation, not a contradiction: ordinary local coloring transports strongly
suggest it is true, but concatenating inequalities from different terms is
invalid.  The most promising remedy is to define branchwise coloring
transports first and retain a source coloring as data; cancellation or a
linear combination must never be used to join paths from different branches.

## Termination at fixed non-strict area

Use lexicographic induction on

\[
  (\operatorname{area}_{ns}(a,S), J).
\]

Area is the cardinality of non-strict edge instances, so the `R_8`
area-reducing branches must prove a strict decrease of that finite cardinality
after the head-based change.  For a full neutral bounce with `k` intermediate
diagonal contacts, the manuscript's proposed rank is

\[
 J=\sum_{\text{strict chains }v_0\to\cdots\to v_r}
      \sum_{j=1}^r j\ell_j,
\]

where `ell_j` is the positive circular length of the strict edge.  Its source
calculation gives `Delta area_ns = 0` and `Delta J = -k` (2404--2445).

The circular proof must first establish the exact hypotheses that make this a
function:

* the selected strict digraph used for a neutral move is acyclic;
* its strict edges decompose into directed chains, or `J` is redefined over a
  canonical path decomposition independent of choices;
* the full reverse bounce exposes all consecutive `d.d` contacts, not merely
  the one-bounce endpoint; and
* the altered chain interiors have the stated positive lifted lengths after
  projection.

The source's stuck word example at 2428--2445 shows why stopping at a
consecutive `d.d` contact is not an alternative terminal case.  Continue the
full ordinary bounce; then either a branch lowers area or a neutral move lowers
`J`.  If chain separation is awkward, the equivalent finite-state remedy is
to use the retained state above plus a bounded progress measure consisting of
the next contact index and the lifted marker position before a full bounce is
closed.  That remedy still needs a proof that the finite bound is reached
before a nonzero branch can return to its original residue; `wrappedBounce_zero`
removes the only return case.

## HRV obligations after the recurrence transitions

The recurrence cannot be used as a definition of the desired HRV expression.
For each local branch, separately prove an HRV transport statement for the
aggregate selected-order expansion.  The ordinary reusable ingredients are
the explicit edge-set changes and swap invariants in `FirstBounceGraph.lean`
and `SecondBounceGraph.lean`, plus the already formalized ordinary orientation
bounce identities.  Their circular use needs a lift-respecting analogue:

1. transport the complete selected relation outside the window by a periodic
   swap of two consecutive lifts;
2. show it is an isomorphism of lifted reachability relations, not merely of
   projected edge sets;
3. map terminal lifted vertices to terminal lifted vertices, so HRV fiber
   cardinalities agree; and
4. prove that every target selected state appears once with exactly the
   coefficient prescribed by `R1`--`R8`.

The manuscript gives the useful exterior-incidence mechanism at 2779--2805:
with `b_i=i-a_i` nondecreasing, a terminal strict edge followed by east gives
`b_z=p` and `b_(z+1)>=p+2`, excluding an exterior row beginning at `p+1`.
This is sufficient for the displayed one-bounce row/column swap, but it is
not yet the full recurrence transition theorem.  Formalize it as a local
`outsideWindow_fixed` lemma and make it an explicit premise of the first
lifted adapter; then discharge that premise from the `b` inequalities for
each of `R2`--`R4` and the constituent moves of `R8`.

## Executable next sequence

1. Define a lifted word/window representation and prove a decoder from a
   local word change to head/length `EdgeData`; include a proof that changed
   strict edges are corners.  Do not quotient a path by rotation prematurely.
2. Port the ordinary first- and second-bounce edge identities as integer-lift
   identities.  The existing base/strict/normal/swap lemmas identify the exact
   edges to replace.
3. Define retained coloring states and prove one-step preservation for each
   local branch.  This is the missing no-wrap theorem's only new semantic
   content.
4. Prove `wrappedBounce_zero`, then run the full reverse bounce until an
   area-decreasing branch or a `J`-decreasing neutral successor occurs.
5. Prove the selected-order and HRV transport identities branchwise and close
   the lexicographic induction.

This supplies the proposed full-statement route. Its new arguments include
periodic exterior geometry and HRV transport, the branchwise retained-coloring
invariant, and the full-bounce chain/rank calculation. They must be proved,
not accepted as a recurrence certificate or folded into the final theorem's
hypotheses.
