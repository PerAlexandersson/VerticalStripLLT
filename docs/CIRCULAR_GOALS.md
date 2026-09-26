# Remaining circular proof obligations

The full theorem is still open:

```lean
theorem coloringLLT_shifted_eq_eval_shiftedOrientationExpansion
    {n : ℕ} (D : Diagram n) (m : ℕ) :
    xQShift m (D.coloringLLT m) =
      evalElementary m (shiftedOrientationExpansion D)
```

This is a target, not an exported declaration. Both sides are independently
defined. The eventual theorem must have no recurrence or semantic assumptions,
and must include every finite alphabet, including the empty alphabet.
[Verified results](CIRCULAR_STATUS.md) and [current ownership](../HANDOFF.md)
are recorded separately.

## Complete the reduction to one-bounce relations

The user clarified the intended route: use the ordinary local elimination
argument to reach one-bounce configurations. A genuine directed strict loop
has zero polynomial, handled by the existing vanishing theorems. Counts and
contact lists are auxiliary bookkeeping; a projected multi-bounce R4 identity
is not a prerequisite and must not be assumed.

Transport the ordinary paired-child argument: the ordinary and raised child
equations come from an auxiliary induction on the bounce prefix, then the
unicellular and one-bounce identities cancel to give the desired reduction.
The raised child need not have smaller area. See the exact `hOrdIH`,
`hRaisedIH`, and `dd_step` mapping in the ND assembly note. The task does not
require a no-loop theorem for arbitrary sequences of diagram rewrites.
The original shortened-root target in any interior overlap is now proved
cyclic, so both of its actual expressions vanish (`InteriorShortenCycle`).
Use that zero term where it occurs; the remaining child equations still need
the actual restarted contacts, rather than unchanged separated-case contacts.

Direct and full NN/DN, direct ND, root-alias ND and separated ND are proved
for both actual models. Their declarations are catalogued in
[CIRCULAR_STATUS.md](CIRCULAR_STATUS.md); they are not new work items.

Only deeper interior ND exits remain. The explicit-index theorem
`DDLocalData.oneBounce_restart_of_interior_overlap_at` gives a one-bounce
restart in the DD-resolved child of doubled area D+1. If the terminal upper
vertex aliases the first main contact, the restart is NN and both resulting
leaves have area D−1. That entire case is proved by
`Diagram.expansion_of_nd_interior_overlap_first_contact`.

For every deeper contact the restart is DN: this is now proved by
`DDLocalData.exists_oneBounceDNData_of_interior_overlap`. Its constructor
uses the independently defined DN successor and its checked identities;
the move preserves the raised auxiliary area. Prove a justified exit to
smaller outer measure or an independent semantic
base. Mixed DD/neutral termination is checked, but does not include R1
strictification or assert that a suitable next move exists. A single exposed
corner can strictify back to area D without decreasing strict rank. Two distinct
exposed corners already provide a checked smaller-area exit.

The chain-plus-isolated-vertex semantic base is now proved uniformly by
`ChainSingletonData.coloringLLT_shifted_eq_expansion`. It compares both actual
models for every finite alphabet. Use it where its exact graph hypothesis is
established; even a saturated deeper-interior source can have two isolated
vertices, so this base does not by itself discharge the general interior step.

Use the [ND assembly note](proofs/CIRCULAR_ND_ASSEMBLY.md) for the exact
obligations and failed shortcuts. In particular, strict-loop vanishing does not
identify overlapping offset tracks with a cycle. Rotation invariance alone
cannot close an excursion whose side defects vanish: DD, neutral DN and R1
strictification preserve q^(strict.card) times the semantic defect. A valid
branching cancellation or an independently solved endpoint is still needed.
Zero-row preservation for concrete DD/DN moves is now checked: these moves
cannot create an ordinary cut from a positive-area source. The checked
zero-cut interval lemmas do not discharge that remaining case.

## Final induction and corollaries

The outer induction on `(doubledArea, strictRank)` is checked in
`Diagram.expansion_of_nd_induction_step`. Corner reduction handles nonsaturated
sources; strict cycles and no-normal-edge diagrams supply bases; complete
reverse search covers NN, DN and ND. R1 and NN decrease area, and full DN
preserves area while decreasing strict rank.

`Diagram.expansion_of_interior_nd_step` now has exactly one open input:
`InteriorNDInductionStep`. The separated input of the earlier assembly is
discharged by `separatedNDInductionStep`; direct ND and root alias are discharged
internally. Prove the interior input to instantiate the checked induction.
This conditional declaration does not assert the full theorem and does not
replace either independently defined polynomial by a recursive object.

After the semantic bridge, transfer the independently proved HRV coefficient
positivity and degree to the coloring polynomial. The last-variable
alphabet-specialization interface is already proved directly from coloring
semantics. The neutral-termination lemma, selected
subset expansion, HRV construction, and direct recurrences are completed
results, not new work items.

Complete flip-component expansions and omega translation remain downstream;
see [the retained component interfaces](CIRCULAR_FLIPS.md). They are not
prerequisites for the aggregate circular theorem. No new examples or general
symmetric-functions library are planned.
