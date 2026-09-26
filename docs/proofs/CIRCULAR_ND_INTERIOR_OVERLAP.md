# Interior contact overlap in the circular ND branch

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

The next reduction must distinguish genuinely disjoint contacts from all
periodic overlaps, including interior collisions. The checked root-alias
theorem and NN/DN separation remain valid. A new reduction, or an additional
uniform semantic family covering the interior case, is required before the
final induction can be assembled. No false separation lemma is assumed in
the Lean source.

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
from the consecutive-block shape remains the substantive missing step.
