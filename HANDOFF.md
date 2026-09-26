# VerticalStripLLT handoff

## Active continuation: deeper interior circular ND

The full circular coloring–HRV equality remains open. The checked outer
induction retains the explicit input `InteriorNDInductionStep`. First-contact
interior overlap is now proved; deeper contacts remain. Follow the author's
one-bounce elimination strategy. Strict cycles make both actual models vanish;
overlap between offset contact tracks alone is not a cycle. No flip work.

This checkpoint adds:

- `DDLocalData.oneBounce_restart_of_interior_overlap_at`, identifying the
  actual restart root and terminal. The older existential theorem is a wrapper;
  its public signature is preserved and its duplicated proof removed.
- `Diagram.expansion_of_nd_interior_overlap_first_contact`: the full actual-model
  bridge when the terminal upper vertex aliases the first contact. Both leaves
  have doubled area D−1; no saturation or strict-rank hypothesis is needed.
- `ChainSingletonData`: an exhaustive vertex equivalence and exact strict
  relation, deriving acyclicity, strict coloring constraints and cross incidence.
- `ChainSingletonData.coloringLLT_reindex`: a bijective reindexing of the actual
  coloring sum, retaining its actual ascent count.
- `ChainSingletonData.ascentCount_eq_base_add_gaps`: actual ascent count equals
  a fixed internal/cross contribution plus occupied insertion-gap indicators.
- `isolated_with_insertion_correction_sum`: the uniform weighted gap sum is
  a two-term elementary expression. This is NOT yet the full chain-singleton
  semantic bridge; polynomial assembly and the HRV calculation remain.

Previous source checkpoints: `372619c` (strict-corner adjacency), `78c07c3`
(full separated ND), `8c8e8b5` (outer induction). The ordinary theorem remains
fully proved. Initialization commits `830cc6b`, `130f7e8` and immutable references
are preserved.

Checks: full default build 1871 jobs; axiom inventory 1788 declarations, only
propext, Classical.choice, Quot.sound. Source guards, changed-source line lengths
and diff whitespace pass. External logs `circular-first-contact-checkpoint-build.log`
and `circular-first-contact-checkpoint-axioms.log` under
`/lake-cache/ai-projects/requests/VerticalStripLLT/`. All local builds serialized.

## Ownership

Primary owns all source, strategy, integration, remote jobs and the sole build
slot. All delegated lanes are released. Use only `lake-workspace`; check no
other Lean/Lake process is active before every invocation. No build-slot transfer.

Luna supplied insertion-coloring sums, cross-ascent algebra and the first-contact
port. Terra supplied the coloring equivalence/reindexing. Primary repaired APIs,
connected actual graph counts, deduplicated restart geometry, and verified all
integrated source locally. Astra independently approved the strict-corner lemma,
chain-singleton mathematical plan and the first-contact return. No remote prefix
or unfinished target was imported into local source.

## Aristotle requests

The interior-overlap request finished COMPLETE_WITH_ERRORS:
project `65c4cfed-a912-4dc7-9dfc-1901c5f810a7`, task
`c4f22d47-e2f8-4545-9ba5-9edb35be49e9`. Its final target retains one sorry and
was excluded. The two completed appended lemmas were integrated as described
above. External directory `circular-interior-expansion/` retains
`completed-result.tar.gz`, `returned-Request.lean`, `returned-ARISTOTLE_SUMMARY.md`
and observer/steering provenance. No active task remains there; do not poll it
as live. Transient observer reconnects never resubmitted the task.

A narrower uniform chain-singleton semantic request is prepared in
`circular-chain-singleton-expansion/`, not yet submitted. Its dependency closure
has 70 modules (6526 prefix lines): compatible existing foundation proofs and
six new locally checked modules. It includes no area/bounce assumptions or
unfinished interior theorem. Exact new-source hashes, input module list and
prefix provenance are retained. The target is the actual coloring–HRV equality
for every `ChainSingletonData D k` and every finite alphabet, not a claim that
all interior configurations reach this family.

Completed separated ND: project `361812e0-b73e-48b9-9ad7-dffe103615f6`, task
`e58bd214-3a7c-4d47-ab01-e58521c293ad`. Its verified port has actual targets with
area drops two/four and simultaneous cyclic vanishing of the paired intermediates.
See `docs/ARISTOTLE.md` for provenance.

## Mathematical route and next step

1. Finish the uniform chain-singleton bridge using the checked gap machinery
   and an independent HRV selection calculation; use it only where justified.
2. Prove an exit for deeper interior contacts, then discharge the outer
   induction input without extra assumptions.
3. Transfer the independently proved HRV positivity and degree to coloring.

For a chain c_1,...,c_L and isolated strict vertex v, let a_j=[c_j→v normal],
b_j=[v→c_j normal], I=#forward internal normals, M=sum_(j<L) a_j,
A=I+M and r=M+b_1+a_L. Strict-corner geometry proves a_j=b_(j+1).
The audited candidate formulas are q^A*(e_L*e_1+r*(q−1)*e_(L+1)) for coloring
and (1+q)^A*(e_L*e_1+r*q*e_(L+1)) for shifted HRV. External selections U,V
are acyclic iff each j in U is smaller than each h in V. Nonempty V or L in U
gives one HRV fiber; otherwise strict continuation dominates cross shortcuts,
giving fibers L and 1. The full formulas remain unformalized.

Known limitation: a DD resolved child has area D+1. A one-bounce DN restart
preserves that auxiliary area. Strictifying a single exposed corner can return
to area D without decreasing strict rank; unrestricted rewrite cycles do not
imply strict cycles. Two missing corners give a checked smaller-area exit.
The comparable-normal-endpoint base is also checked, but does not cover every
interaction between strict components. The earlier read-only Sonnet proposal
added no valid general termination argument. No theorem gap or counterexample
to the full HRV formula has been established.

Exact checked interfaces: `docs/CIRCULAR_STATUS.md`. Remaining obligations and
failed shortcuts: `docs/CIRCULAR_GOALS.md`, `docs/proofs/CIRCULAR_ND_ASSEMBLY.md`.
History is retained in Git and `docs/archive/`. Overleaf `LLT flip/main.tex` and
`new-main.tex` are present; no Overleaf edits in this continuation. The reference
files under `references/alexandersson-sulzgruber-2022/` remain immutable.
