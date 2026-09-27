# Proof streamlining audit

The second cleanup pass follows the user's request for an independent Claude
audit. The audit was read-only, with source-search tools and no compiler access.
Primary implemented the recommendations and retained every existing public
statement and parameter name. Independent Astra review found no semantic or
public-signature regression and confirmed that the helpers add no import dependencies.

## Shared facts

| Helper | Reuse |
| --- | --- |
| `Circular.componentClass_mk_eq_iff_mem` | Quotient fiber identification and flip-closed component grouping. |
| `Components.mountainScan_succ_of_lt` | HRV extraction and Cauchy-product pairing. |
| `Components.mul_central_left_comm` | Six central-scalar rewrites across word conjugation and commutator coefficients. |

The first identifies a quotient class with the full component of its chosen
representative. The second moves the existing private scan-step proof to its
owning module. The third factors a repeated consequence of centrality, retaining
its ring assumptions. Each helper has multiple actual callers.

## Simplifications

- Four component valuation transports use Mathlib's `Finset.sum_image` with
  the existing injectivity proofs. No new reindexing abstraction is needed.
- Flip-closed sums compute the quotient decomposition once and reuse it for
  both functions. The closure hypothesis is the undirected `Flip` relation;
  the comment now says so explicitly.
- Three Cauchy induction proofs use `List.forall_mem_cons` and Lean's handling
  of dependent hypotheses. The forward inverse-product proof reuses the local
  conjugation theorem at the identity element.
- First-block cancellation rewrites its compatibility condition once before
  splitting cases. Primary supplied the explicit summand needed for elaboration.
- Tail-sum congruence uses function extensionality; factorization uses the
  existing congruence, scalar and cross-block lemmas. Primary normalized the
  private carrier predicate in an explicit hypothesis before applying the theorem.

Across the 13 edited component modules, source length falls from 1845 to 1731
lines: **114 fewer lines**, including the new helpers. The earlier cleanup removed
41 lines. These are source-size measurements, not compiler-performance benchmarks.

## Kept explicit

The actual HRV root/nonroot split remains. Replacing an inserted-root/fiber
condition by equality with an erased fiber is invalid when the fiber is empty.
The signed cancellation and component closure hypotheses remain visible.
Historical block-list modules are retained, although the final proof uses the
literal scan route. No theorem is weakened or replaced by a recurrence assumption.

## Verification and provenance

Focused builds and the full **2074-job** library build pass. The expanded
`Verification.lean` inventory has **2803 entries**, using only `propext`,
`Classical.choice` and `Quot.sound`. Existing public headers, 100-column Lean
widths, source guards and diff checks pass. Existing linter/deprecation warnings
remain. Current ownership is recorded in [HANDOFF](../HANDOFF.md).
The audit response and build logs live
under `/lake-cache/ai-projects/requests/VerticalStripLLT/streamlining-audit/`:
`claude-audit-result.md`, `component-grouping-build.log`, and the
`claude-recommendations-build` logs, `library-build.log` and `axioms.log`.
The complete statements remain documented
in [the component completion audit](COMPONENT_COMPLETION.md).
