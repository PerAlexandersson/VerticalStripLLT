# VerticalStripLLT handoff

## Active continuation: interior circular ND

The full circular coloring–HRV equality remains open. The checked outer
induction now has exactly one remaining input: `InteriorNDInductionStep`.
Follow the author's one-bounce elimination strategy. Genuine strict cycles
make both actual expressions vanish; contact overlap alone is not a cycle.
No flip-component work or new examples in this increment.

Latest pushed source checkpoint `372619c` adds the checked uniform
strict-corner adjacency equivalence.
Previous pushed source checkpoint: `78c07c3` (full separated-contact ND), following
`8c8e8b5` (outer induction) and its handoff `0e5b104`.
Exact interfaces:

- `Diagram.exists_nd_separated_reduction`: valid actual targets with doubled-area
  drops two/four and both polynomial identities, for arbitrary counted depth.
- `NDSeparatedHyp.dS_admissible_iff`: paired-chain conjugacy shows the lowered
  and shortened intermediates are cyclic together, allowing coincident outer
  endpoints. All inner-path separation follows from source hypotheses.
- `Diagram.expansion_of_nd_separated` and `separatedNDInductionStep`: the semantic
  induction step, using only smaller areas, discharges the separated input.
- `Diagram.expansion_of_interior_nd_step`: the entire equality follows from the
  sole remaining interior step. This is explicitly conditional, not completion.

Luna ported six appended `NDSeparated` modules. Primary repaired the local
relation API, checked exact declaration parity (159 declarations), and added
`NDSeparatedRecurrences`. Independent Astra review approved exact hypotheses,
concrete targets, cyclic vanishing and seven-equation cancellation. No returned
prefix was imported or existing mathematical definition changed.

Checks: full default build 1865 jobs; axiom inventory 1754 declarations, only
propext, Classical.choice, Quot.sound. Source guards and new-source line lengths
pass. External logs `circular-strict-corner-checkpoint-build.log` and
`circular-strict-corner-checkpoint-axioms.log`. Previous checkpoint logs remain.
Initialization commits `830cc6b` and `130f7e8` and immutable reference files
remain intact. The axiom run waited for a RealRooted build to finish; no local
Lean builds were run concurrently.

## Ownership and active remote work

Primary owns all source, strategy, integration, remote jobs and the sole
serialized local build slot. All delegated lanes are released; no build-slot
transfer occurred. Use only `lake-workspace`, checking for other Lean/Lake
processes before each invocation. Delegates remain build-free.

Terra's bounded strict-corner adjacency task returned without a candidate;
the lane is released and no new file was created. Astra completed read-only
audits of a possible chain-plus-isolated-vertex base and the author's strict-loop
clarification. No local build was needed for these audits.

Primary completed `Circular/StrictCornerAdjacency.lean`, using two edge lengths
based at a common endpoint. Exact declarations: `length_le_of_strict_same_tail`,
`naturalPairs_across_strict_corner_iff`, `normalPairs_across_strict_corner_iff`.
Astra independently approved the hypotheses and lift argument. All delegated
lanes are released; the build slot remains with primary. Luna's corrected API
audit identifies `increasingColoringSum_eq_esymm`,
`sum_strictMono_sigma_colorings_eq_prod_esymm`, and
`rooted_chain_coloring_sum_eq_prod_esymm` as existing coloring infrastructure.
Only the isolated-color insertion-gap partition needs new enumeration machinery.

The strict-loop clarification is recorded in `CIRCULAR_ND_ASSEMBLY.md`:
repetition within one strict walk forces zero, whereas the remaining interior
contact identifies vertices of two offset tracks without closing a walk.
The one-bounce restart is already checked; its auxiliary-area exit is open.

Potential uniform base, mathematically audited but not formalized: a strict
chain c_1,...,c_L and one isolated strict vertex v. Put a_j=[c_j→v normal],
b_j=[v→c_j normal], I=#forward internal normal edges, M=sum_{j<L} a_j,
A=I+M, r=M+b_1+a_L. Strict-corner geometry gives a_j=b_{j+1} for j<L.
The coloring expression is q^A*(e_L*e_1+r*(q-1)*e_(L+1)); the independent
shifted HRV expression is (1+q)^A*(e_L*e_1+r*q*e_(L+1)). For external selected
sets U,V, admissibility says j<h for every j in U,h in V. Nonempty V or
L in U gives one HRV fiber; otherwise the strict continuation dominates each
external shortcut on the integer cover, giving fibers L and 1. This may
supply a terminal base, but no theorem says every interior case reaches it.

Read-only Claude Sonnet consultation 97026 finished normally without a proof.
External prompt, JSONL output and `Review.md` are in `claude-interior-review/`.
Primary and Astra audited it: defect transfer is valid existing algebra, while
the proposed unrestricted no-repeat theorem fails on the already audited
rotation route. A strategy stopping at semantic bases could avoid that cycle,
but its termination is still unproved. No Lean changes follow from this review.

Active Aristotle interior-overlap project:
`65c4cfed-a912-4dc7-9dfc-1901c5f810a7`, task
`c4f22d47-e2f8-4545-9ba5-9edb35be49e9`. Reconnected observer session **43360**.
The original wait/downloader 87017 exited after a server-connection interruption;
the same remote task was confirmed running on reconnection. Observer 95345
also lost its connection; replacement 10741 again confirmed the same task
running. Observer 10741 also lost its connection; `aristotle tasks` confirmed
the same task IN_PROGRESS before replacement 43360. No resubmission.
Read `observer-reconnect-3.log` for current events. This observer does not download:
after authoritative completion, use `aristotle download` for the same project,
with destination `circular-interior-expansion/result.tar.gz`.
External directory `circular-interior-expansion/` under
`/lake-cache/ai-projects/requests/VerticalStripLLT/`. Observe this same handle;
do not resubmit. The request includes 182 locally checked modules, the exact
unchanged target, source hashes, `DoubleCornerReduction`, full separated ND,
and proof-route notes retaining known failed shortcuts. Its source snapshot is
`0e5b104` plus the checked new separated modules, pinned by exact hashes.
The CLI may exit zero on API errors: inspect its log as well as exit status.

Primary sent INSTRUCT steering to this same project after the corner checkpoint.
`STRICT_CORNER_STEERING.md` and `strict-corner-steering.log` retain the exact
message and accepted submission. It supplies the checked corner lemma and
the independently audited, still unformalized chain-singleton formula while
preserving the exact interior target. It explicitly does not assume that every
interior configuration reaches this proposed base.

Target `Diagram.expansion_of_nd_interior_overlap`: saturated, acyclic source,
actual eligible counted interior ND search, and semantic IH below
`(doubledArea, strictRank)` imply the actual coloring–HRV equality. No recurrence
assumption, no-wrap condition or semantic redefinition is permitted.

Completed separated-ND project `361812e0-b73e-48b9-9ad7-dffe103615f6`, task
`e58bd214-3a7c-4d47-ab01-e58521c293ad`, observer 45949 finished. Its original
175-module prefix came from `0fc4d07`. Returned files and review provenance
remain in `circular-separated-nd/`; see `docs/ARISTOTLE.md`.

## Next step and mathematical limits

1. Finish the interior-overlap exit argument, then instantiate
   `expansion_of_interior_nd_step` without hypotheses.
2. Transfer the independently proved HRV positivity and degree to coloring.

Already complete: full NN/DN, direct and root-alias ND, separated ND, strict-cycle
vanishing, normal-comparability base, alphabet stability, two-corner auxiliary
exit, and outer induction. Exact source links: `docs/CIRCULAR_STATUS.md`.
Remaining obligations and failed shortcuts: `docs/CIRCULAR_GOALS.md` and
`docs/proofs/CIRCULAR_ND_ASSEMBLY.md`.

The unresolved interior DD child has doubled area D+1. Mixed DD/neutral
termination omits R1 strictification and does not prove exit existence.
Two missing corners provide a checked exit below D, but one missing corner
can lead to same-area strictification without smaller strict rank. Neither
changing the root alone nor a component-partition refinement closes every case.
The active request asks for this mathematical argument, not more conditional
assembly. Full NN/DN handle their larger-area auxiliaries by contact-count
induction rather than incorrectly applying outer IH.

Earlier checkpoints include `eb11c69` (alphabet/two-corner), `0fc4d07` (full DN),
`3c7f3d4` (comparable base), `1d5005d` (direct ND/full NN), and `130efc2`
(interior restart/mixed termination). Older history remains in
`docs/archive/HANDOFF_THROUGH_INTERIOR_RESTART.md` and Git.

Overleaf `LLT flip/main.tex` and `new-main.tex` are present; `old-main.tex` is
absent. No Overleaf edits in this continuation. Author-supplied files under
`references/alexandersson-sulzgruber-2022/` remain immutable.
