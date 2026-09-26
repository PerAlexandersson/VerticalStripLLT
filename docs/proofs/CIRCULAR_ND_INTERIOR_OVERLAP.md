# Interior contact overlap and the one-bounce reduction

The root-alias reduction is proved, but its complement is not automatically
the ordinary R4 case. The terminal upper contact can meet an interior main
contact even when it differs from the root. The following obstruction was
derived independently by the primary worker and the Astra reviewer. It is
manually verified proof-route evidence, not a claimed Lean theorem or a new
example-formalization milestone.

Take circumference five, areas `(2,3,3,3,3)`, and strict heads `1,2,3,4`.
These are all the corners. Their strict graph is the acyclic chain

```
0 → 3 → 1 → 4 → 2.
```

Root `t=4` is eligible: `b(4)=1`, `b(5)=3`, and its east gap is one.
Reverse search visits `4,1,−2,−5`. The first two contacts are DD, and the
terminal `x=−5` is ND: row residue zero is nonstrict, row residue one is
strict, and `b(−5)=b(−4)=−7`. The root residue is four, so it differs from
the terminal upper residue one. But that upper residue occurs inside the
main contact path.

The proposed ordinary R4 successors fail:

- Shortening the root replaces `1→4` by `2→4`, producing the strict cycle
  `2→4→2`.
- Moving the terminal strict head left replaces `3→1` by `3→0`, producing
  `0→3→0`; shortening the root does not remove this cycle.

Both target coloring polynomials vanish. The source admits a strictly ordered
coloring of its five-vertex chain and has a nonzero coloring polynomial.
Therefore the ordinary two-target R4 identity is false for this configuration.
This does not refute the circular HRV formula.

The primary worker found a second saturated configuration at circumference
seven: areas `(3,4,4,3,4,4,3)`, strict heads `1,2,4,5,6`, root `t=12`, and
terminal `x=0`. The strict components are `0→4→1→5→2` and `3→6`.
Thus the issue is not confined to a single strict component containing every
vertex. The reviewer checked this configuration independently.

This invalidates only the direct projection of the ordinary multi-bounce R4
formula. It does not establish a gap in the author's one-bounce argument.
The user explicitly clarified that preliminary local reductions must be
performed first. Their changed diagrams can create an earlier positive-gap
restart, so the failed direct projection is not the intended proof route.
The two test diagrams satisfy the actual circular coloring–HRV identity under
independent exact Rust evaluation (details below).

For genuinely disjoint contacts, the intended targets are root shortening
(doubled-area drop two) and terminal-head lowering followed by root shortening
(drop four). Generalized NN/DN and four R1 identities yield the expected R4
coefficients once the intermediate contact transports are proved. The generic
`LowerStrict` constructor remains valid without any claim of acyclicity or
polynomial recurrence.

## Structural route under investigation

Write the lower contacts as p_0,...,p_(r−1), upper contacts q_i=next(p_i),
and root p_r. If q_0=p_j with 1≤j≤r, strict-edge uniqueness joins the two
paths into a whole strict component w_0,...,w_(r+j−1), with p_i=w_i and
q_i=w_(i+j). Acyclicity makes this walk injective. Hence next(w_i)=w_(i+j)
for i<r. Indices modulo j describe j physically consecutive blocks, with
sizes differing by at most one. The proved root-alias case is j=r.
This shape argument is audited mathematics, not yet a Lean declaration.

External interactions obstruct simple factorization. In the seven-vertex
configuration, every pair between C=(0,4,1,5,2) and B=(3,6) is normal, but
its direction changes along C. For vertices 0,1,2, edges go C→3 and 6→C;
for vertices 4,5, they go 3→C and C→6. The ascent contribution depends on
interleaving the two strictly ordered color lists.

The checked forced-set APIs can remove internal forward/backward normal
edges while retaining every external interaction. Their output is a restricted
pair graph/orientation sum. Reconstructing a smaller valid circular diagram
from that shape was an alternative approach; it is not a prerequisite for
the intended local elimination and restart proof.

## Local resolution of the displayed witnesses

For the five-vertex diagram, the checked DD resolution gives
`q F(D) = F(R) − F(E)` in the shifted variable. Here

- R has areas `(2,3,4,3,2)` and strict heads `2,3,4`;
- E is deletion of the parallel strict corner at head 2;
- the change at old root 4 creates positive east gap at row 3 in R;
- restart at row 3 gives a direct NN contact at rows 0 and 1.

The direct NN target T and E both have doubled area `doubledArea D − 1`.
Thus `q F(D) = (q+1) F(T) − F(E)` reduces the semantic equality to smaller
area by cancellation. The seven-vertex witness has the same resolution,
with R areas `(3,4,5,3,4,3,3)` and restart at row 4. Primary and independent
Astra review agree on these traces. These specific traces are not new Lean
example milestones.

In general, if q_0=p_j is an interior collision and ℓ=r−j, the local DD
resolution creates a positive gap at p_ℓ. Its first contacted row p_(ℓ−1)
has upper neighbor c=p_(r−1), whose strict flag was removed. The restart
therefore has no DD contacts: it is NN if ℓ=1 and DN otherwise. The uniform
`DDLocalData.exists_oneBounce_restart_of_interior_overlap` in
[InteriorRestart](../../VerticalStripLLT/Circular/InteriorRestart.lean) now proves
this conclusion, deriving every row exclusion from the actual search and strict
acyclicity. Its proof propagates the contact identification using uniqueness of
strict successors, excludes the length-one root, and verifies the new positive
gap and zero-DD terminal directly. No additional no-wrap hypothesis is used.

The DN branch is neutral at the auxiliary area level `doubledArea D + 1`.
Its rank decreases, but the global proof must account for that auxiliary
level before invoking the outer area induction. This is an unfinished proof
obligation, not a counterexample to the one-bounce reduction strategy.

## Independent exact check

The existing Rust helper `assert_hrv_matches_direct_strict_llt` in
`/workspace/rust/sym-poly/sym/tests/circular_hrv.rs` was run on both witnesses,
using the library's direct coloring enumerator, q↦q+1 substitution, elementary
conversion, and independent circular HRV enumeration. Both equalities pass.
The five-vertex result is `(q+1)^4 e_5`; the seven-vertex result has terms
`e_(5,2)`, `e_(6,1)`, and `e_7`, so it does not factor into separate chain terms.

Rust source commit: `d53fb193af3c69adedbd9ec8592f87235d809ffa`; relevant files
were clean. The bounded caller is external at
`/tmp/verticalstrip-llt-interior-check/`, with output in this project's external
`interior-overlap-exact-check.log`. It includes the existing helper directly;
no LLT algorithm or polynomial-family generator was reimplemented. These
finite checks corroborate the theorem in the witnesses and do not prove the
uniform theorem.
