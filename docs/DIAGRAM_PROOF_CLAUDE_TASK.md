# Claude task: formalize the right-endpoint attachment in the diagram proof

The requested result is the **same diagram argument used in the paper**.
The written ordinary component proof is complete; its independent Lean route
is not. The older completed word/scan component theorem is not an input.

The recommended independent task is the right-attachment part of P9. It can
be implemented before P6's remaining common-cover induction is assembled.
It must not assume that an arbitrary attachment already satisfies K = E.

## Read first

- [Project instructions](../AGENTS.md) and [current ownership/status](../HANDOFF.md).
- [New draft proof, with figures](drafts/ORDINARY_COMPONENT_DIAGRAM_PROOF.md),
  especially “Keeping the right endpoint” and “Attaching an arbitrary component”.
- [Complete mathematical proof](proofs/COMPONENT_DIAGRAM_COMPLETION.md).
- [Detailed plan](COMPONENT_DIAGRAM_FORMALIZATION_PLAN.md), P2 and P7–P10.
- [Endpoint continuation](proofs/COMPONENT_RECURRENCE_ENDPOINT_EXTENSION.md),
  **the later sections** “Full-layer recurrences preserve the right endpoint”
  and “Arbitrary right-hand attachments”. Its opening preserves an earlier
  unfinished status; the dated continuations contain the completed argument.

## Current division of work

At pushed checkpoint `b78312c` (2026-10-01), the Codex worker completed and
verified the two pending P6 lemmas and explicitly released all `DiagramProof/`
Lean sources, `DiagramProofVerification.lean` and the sole project build slot
to the persistent Claude worker `agent-verticalstri-motzki-c-001af720`.
The current [HANDOFF](../HANDOFF.md) is authoritative.

Claude begins with the attachment task below, then continues the remaining
formalization. Codex retains mathematical prose, figures, source maps and the
top-level handoff. Claude reports progress, checks and blockers in
`docs/LEAN_COORDINATION.md`, which it owns. The prepared attachment drafts in
the external request cache are uncompiled candidates until checked locally.

Proposed attachment files:

1. `VerticalStripLLT/Components/DiagramProof/RightAttachmentDiagram.lean`;
2. `VerticalStripLLT/Components/DiagramProof/RightAttachmentPaths.lean`;
3. `VerticalStripLLT/Components/DiagramProof/RightAttachmentValues.lean`;
4. `VerticalStripLLT/Components/DiagramProof/RightAttachment.lean`.

**Only Claude holds the project build slot after this transfer.** Builds must
still serialize with other Lean projects, use `lake-workspace` and focus on
needed targets. Separate worktrees do not make concurrent builds safe.

P6 now includes all feasible-extra-set paths, conditional initial-vertex
inheritance, preserved chain count, matching-edge removability, canonical
last-clique short edges and the two-chain cardinal base. Its global vertex-count
induction remains unfinished. P7–P10 are still open.

## Exact mathematical input

Let L occupy [0,c] and R occupy [c,d], with c counted once. Both are actual
ordinary decorated natural diagrams. In their union G there is no natural
edge from below c to above c. Strict edges are inherited exactly. Let P and T
be whole flip components of L and R.

For a selected state A, K(A) is the strict-coloring sum of its selected relation.
E(A) is the strict-coloring sum of the increasing chains on its **actual HRV
fibres**, equivalently its elementary HRV monomial. Keep the color beta at c
fixed on both sides. The ordinary maximum of the prefix, and ordinary minimum
of the attachment, are essential hypotheses.

We want a transfer theorem with this input, for one finite list of integers
z_i and whole components P_i on the **same prefix vertex set**:

    componentMarkedK P c m beta = sum_i z_i * componentMarkedK P_i c m beta
    componentMarkedE P c m beta = sum_i z_i * componentMarkedE P_i c m beta

for every alphabet size m and beta in Fin m. The output is the corresponding
two **unmarked** identities for P*T and P_i*T, with the same z_i, together
with whole-component identification. Prefix diagrams may vary with i; each is
glued to the same attachment at the same endpoint.

## 1. Construct the actual diagram and restriction/union equivalence

Use the established interval-relation model and search the existing induced
diagram APIs before defining another representation. One convenient indexing
is a left diagram on Fin (p+1), right diagram on Fin (q+1), and union on
Fin (p+q+1), with embeddings i ↦ i and j ↦ p+j. The images meet exactly at p.
Alternatively start from one diagram and an explicit separating cut, then
realize its two induced diagrams. Choose the smaller API after inspection.

Prove exact correspondence of natural edges and inherited strict edges.
An edge belongs to one factor because it cannot cross the two interiors;
there are no loops at the shared vertex. Show the construction is a valid
forward ordinary diagram and preserves strict-corner legality.

Restriction and selected union are inverse maps on **actual orientations**.
Preserve full selected relations, not just normal-edge sets or graph adjacency.
The shared-vertex case p=0 or q=0 must be included.

Useful sources: `InducedDiagram.lean`, `InducedDecorations.lean`,
`InducedRestriction.lean`, `Basic.lean`, and the finite cover interfaces in
`RelationPaths.lean`/`PathTransport.lean`.

## 2. Prove the whole-component product by actual flips

Every natural triangle lies in one factor: its long edge cannot cross the
cut. A forward selected path with both endpoints on one side cannot leave
that side and return. This proves both directions of the cover equivalence
used by a factor triangle.

Conclude:

    Flip_G (A,B) (A',B') iff
      (Flip_L A A' and B=B') or (A=A' and Flip_R B B').

Use the orientation equivalence to state this without treating pairs as
orientations by definition. Derive the corresponding actual-path equivalence
by projecting a glued path and lifting the two factor paths successively.
Then prove the **entire** `flipComponent` is the image of the Cartesian
product of the two entire factor components. One-way inclusion is insufficient.

Useful sources: `Basic.lean`, `FiniteCoverPaths.lean`, `WeakBlocks.lean`,
`RestrictedFlips.lean` and `PathTransport.lean`.

## 3. Establish the exact HRV fibre merger

If a left vertex u has H_A(u)<c, its HRV stays H_A(u). If H_A(u)=c, its glued
HRV is the embedded H_B(c). Every right vertex retains the embedded H_B value.
Prove this from actual reachability, including zero-length paths.

Thus exactly the left fibre of c and the right fibre containing c merge;
their intersection is the shared vertex. All other fibres remain unchanged.
The merged increasing chain is the concatenation of the two increasing chains
at c. Its size is p_fibre+q_fibre-1.

Do not replace this step with equality of unmarked partitions: gluing needs
the marked fibre and its ordered endpoint. The draft's Figure 2 depicts the
specific chain merger to formalize.

## 4. Glue fixed-color sums without dividing by a variable

The existing actual semantics is in `MarkedValues.lean`:
`markedK`, `markedE`, `componentMarkedK`, `componentMarkedE`, `fibreRelation`,
`sum_markedK`, and `sum_markedE`.

Define the attachment's endpoint-omitted coloring weight as the product over
vertices other than its minimum. Use that weight in both its selected-relation
sum and its canonical-fibre-chain sum. It is not polynomial division by x_beta.

Restriction and union give a bijection between a glued coloring and a pair
of factor colorings agreeing at c. Prove, state by state:

    K(A*B) = sum_beta markedK(A,c,beta) * omittedMarkedK(B,c,beta)
    E(A*B) = sum_beta markedE(A,c,beta) * omittedMarkedE(B,c,beta).

The second equality uses the exact fibre merger from step 3. Sum over the
whole-component product from step 2 to obtain the component versions.

Boundary checks: a singleton attachment has omitted weight 1 at each fixed
color; an empty alphabet has no beta and every positive-degree unmarked sum
vanishes. No assertion comparing K(T) and E(T) is needed or allowed as a premise.

## 5. Transfer the marked recurrence and its decrease

Multiply each given marked K identity by the attachment's omitted marked K
sum, and sum beta. Do the same separately for E with its omitted marked E sum.
Finite distributivity produces the same integer list z_i on both sides.
Do not equate the two attachment factors.

The output components are whole by step 2. Gluing the same right attachment
to prefix diagrams on the same vertex set adds the same vertex, natural-area
and area-moment contributions. Prove this last equality directly from the
chosen diagram model, and deduce preservation of the lexicographic decrease.
It is acceptable to return the semantic transfer first and the measure lemma
as a second focused checkpoint.

## Acceptance and return format

- Every statement concerns the existing selected-coloring and actual HRV
  semantics, with explicit forwardness and endpoint hypotheses.
- Exact strict marking, both directions of component correspondence,
  the marked fibre merger, and both zero/singleton boundaries are covered.
- No P6 uniqueness theorem or expansion for an equally large component is
  assumed. The task is conditional on the **marked recurrence**, not on the
  final component theorem.
- No fundamental basis, word/scan proof, or old completed component-expansion
  theorem enters the import closure. Reuse low-level semantics only.
- No `sorry`, `admit`, new axioms or `native_decide`. Use `lia`, not `omega`.
- Return the exact edited files, theorem signatures, focused targets and axiom
  queries to add, along with any remaining obligations. Do not mark P9 or the
  full formalization complete after finishing only this attachment subtask.

The next independent work after attachment is P7's smaller-component
corrections and P8's right-marked layer recurrences. The global proof then
uses first-drop coverage and well-founded induction as described in P9–P10.
