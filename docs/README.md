# Formalization documentation

## Current results and work

- [Ordinary completion audit](COMPLETION.md): unconditional expansion,
  positivity, degree, and alphabet compatibility.
- [Ordinary source and representation map](FORMALIZATION.md).
- [Verified circular results](CIRCULAR_STATUS.md).
- [Remaining circular obligations](CIRCULAR_GOALS.md): the active proof agenda.
- [Circular architecture and source map](CIRCULAR_FORMALIZATION_PLAN.md).
- [HANDOFF](../HANDOFF.md): current ownership, checks, remote task, and next step.

## Proof explanations

- [Reverse bounce search](proofs/CIRCULAR_BOUNCE_SEARCH.md).
- [Neutral-bounce termination](proofs/NEUTRAL_BOUNCE_TERMINATION.md).
- [Direct DN recurrence](proofs/CIRCULAR_DN_RECURRENCE.md).
- [DD propagation](proofs/CIRCULAR_DD_PROPAGATION.md): completed NN elimination
  and remaining DN assembly.
- [Direct ND](proofs/CIRCULAR_DIRECT_ND.md): the completed seven-relation proof.
- [Remaining ND assembly](proofs/CIRCULAR_ND_ASSEMBLY.md): disjoint transport,
  cyclic intermediates and interior-restart exit accounting.
- [ND overlap obstruction](proofs/CIRCULAR_ND_OVERLAP.md) and
  [uniform root-overlap reduction](proofs/CIRCULAR_ND_ALIAS_REDUCTION.md).
- [Interior ND overlap](proofs/CIRCULAR_ND_INTERIOR_OVERLAP.md): an additional
  case with a proved one-bounce restart; final assembly remains.

## Retained qualifications and provenance

- [Sufficient recurrence certificate](REDUCTION_CERTIFICATE.md): the proved
  route used by the ordinary expansion.
- [Restricted ordinary recurrence audit](RESTRICTED_BOUNCE_AUDIT.md): a separate
  open claim, unused by the proved ordinary expansion.
- [Circular flip interfaces](CIRCULAR_FLIPS.md): downstream component scope.
- [Aristotle ledger](ARISTOTLE.md): request IDs, candidates, and local verification.
- [Historical plans](archive/completed-plans/README.md): superseded implementation
  outlines and the original architecture audits. They are not active work lists.

Completed plans no longer duplicate the active agenda. The Lean declarations
and local verification establish the results; explanatory notes record the
mathematical arguments and their precise remaining boundaries.
