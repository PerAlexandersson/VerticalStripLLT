# VerticalStripLLT handoff

## Active continuation: full circular expansion

Current pushed checkpoint `377ae36` (2026-09-26): the overlapping ND reduction
is locally proved for the actual coloring and HRV expressions, including the
complete area-induction step. Full default build: 1818 jobs. Axiom inventory:
1307 declarations, only propext, Classical.choice, Quot.sound. Source guards,
100-column limit, Markdown links, and immutable reference hashes pass.
Primary owns all source, strategy, integration, remote jobs, and the sole local
build slot. All local delegated edit lanes are released.

Earlier pushed checkpoints: `79016bb` direct DN; `c6f48dd` DD resolution and
deleted child; `9224524` completed-plan cleanup. Detailed completed results are
indexed in `docs/CIRCULAR_STATUS.md`; remaining goals are kept separately.

Checked DD increment (`c6f48dd`): all eleven new modules compile, root imports
include them, and the full default build passes (1809 jobs). All 1095 axiom
checks pass with only propext, Classical.choice, Quot.sound. Logs:
`circular-dd-complete-build.log`, `circular-dd-complete-axioms.log`.

Exact DD interfaces:
- `Diagram.exists_ddLocalData` realizes the actual eligible counted DD contact.
- `DDLocalData.coloring_resolution` and `orientation_resolution` prove the
  actual q-weighted last-DD resolution independently for both models.
- `Diagram.delete_dd_child` supplies the actual deletion child: smaller count,
  eligibility, unchanged terminal type, and strict acyclicity.
- `DDLocalData.resolved_area`, `resolved_boundary_rows`, and
  `resolved_strictAt_iff` describe the other child exactly.
- `Diagram.dnSuccessor_strictAt_iff` gives the reusable strict-row DN formula.

Luna's bounded candidates were adopted and repaired by primary. Terra returned
without a candidate. Every edit lane is released; all files and the sole local
build slot are primary-owned. No build-slot transfer occurred.
The remaining DD argument is in `docs/proofs/CIRCULAR_DD_PROPAGATION.md`.

User-requested documentation cleanup: `docs/README.md` routes to one current
circular status table and one remaining-goals file. Completed ordinary plans,
old circular routes, and chronological handoff text are archived. Restricted
ordinary uniqueness remains explicitly open in the retained audit/certificate.
Relative Markdown links and diff whitespace checks pass. No manuscript or
immutable reference files were changed.

Aristotle direct-DN project `a768ca01-7392-49a9-b695-339de82ec027`, task
`847a2439-f8d6-4124-8cb3-222377ca36f9`, is complete and integrated. Final result
and provenance are in external `circular-dn-orientation/` and `docs/ARISTOTLE.md`.
Overlapping ND is now locally proved. Primary integrated the Aristotle result
from project `eb5bc1c3-b026-45aa-9acb-6d3927797294`, task
`55de8e35-31e7-4ff2-a476-f26ac24fe345`, after independent read-only Astra audit.
Exact public interfaces in `AliasRecurrences.lean`:
- `Diagram.exists_nd_alias_reduction`: actual coloring factor q, actual shifted
  HRV factor q+1, and doubled-area decrease six.
- `AliasContacts.target_admissible_iff`: strict acyclicity is preserved.
- `AliasContacts.shifted_coloring_identity`, `expansion_of_target`.
- `Diagram.expansion_of_nd_alias`: complete area-induction step.
All nine new modules and root import pass (1818 jobs); all 1307 axiom checks
pass with only standard axioms. Logs: `circular-nd-alias-complete-build.log`,
`circular-nd-alias-complete-axioms.log`. Primary owns all source; lanes released.
DD checkpoint `c6f48dd` and documentation cleanup `9224524` are pushed.

Only active remote job: Aristotle project
`9dedc3e9-472c-4e5e-aa74-14f185dc95e1`, task
`e598f460-d1cc-4c7c-add6-cccf40042f96`, resolved DD child.
External request and native observer: `circular-dd-resolved-child/`.
The exact final theorem combines raised-root eligibility, smaller count,
terminal flags, and acyclicity. Do not resubmit or change accounts.

Next: complete explicit DD child transformations and contact transport, then
apply contact-count induction separately to both models. Nonoverlap ND
and final `(doubledArea, strictRank)` induction remain.
The full circular expansion is still open; preserve the active goal.

Overleaf path drift: `old-main.tex` is absent; `main.tex` holds the former long
draft and `new-main.tex` is present. No Overleaf edits in this continuation.
The author-supplied committed ordinary reference remains immutable.

Earlier completed assignments and checks: [archived handoff](docs/archive/HANDOFF_THROUGH_DIRECT_DN.md).
