# VerticalStripLLT handoff

## Resumed ownership — 2026-09-29

The replacement primary worker resumes at the user's explicit request from
clean, pushed `2511182138c3f3a27f8f6207a982ec1e28b6c3c7` on `main`.
It owns `HANDOFF.md`, append-only continuations of
`docs/proofs/COMPONENT_RECURRENCE_ENDPOINT_EXTENSION.md` and
`docs/proofs/COMPONENT_DN_SOURCE_ADDITIONS.md`, related outline
routing, and the existing external `hrv-bridge` diagnostic lane. The paused
worker released this lane; all other ownership is preserved. We first audit
the endpoint-marked DN identities and the proposed attached-component fixture.
The general diagram-recursion proof remains unfinished.

**New proved increment:** the
[endpoint-attachment theorem](docs/proofs/COMPONENT_RECURRENCE_ENDPOINT_EXTENSION.md#endpoint-attachment-theorem-completed-audit)
is now proved mathematically. HRV diamonds preserve a multiset of full HRV
maps; internal DN swaps preserve endpoint fibre data. Any completed recurrence
using these endpoint-preserving maps extends to arbitrary components attached
at the two ends, with whole output components and the same decreasing measure.
No component expansion for the attachments is assumed. In particular all
fourteen rows of the five-vertex left DN table extend.

The fixed `dn_joint_span --endpoint-attachments` check passes all fourteen
attached rows, including 16/32/16 in the C_1 row. It checks actual complete
components, strict edges and signed endpoint HRV profiles; the nine-vertex
checks visit 128/88/64 distinct L/R/J states without global enumeration.
The small external Rust consumer build passed. Receipt and frozen sources:
`/lake-cache/ai-projects/requests/VerticalStripLLT/endpoint-attachments-20260929/`.
Maintained Rust remains unchanged at `d53fb193af3c69adedbd9ec8592f87235d809ffa`.

**Second proved increment:** the
[full-layer selected-corner criterion](docs/proofs/COMPONENT_DN_SOURCE_ADDITIONS.md#isolating-one-selected-corner-sector-by-a-full-layer)
isolates C when it is the unique component in its selected-corner sector and
total-edge layer. All added components omit a specified corner and delete
independently. This gives a signed whole-component DN recurrence for every
component of the saturated square of a path on n>=5 vertices, including
crossing prefix edges. Its targets are the complete R layer minus the complete
corner-deletion J layer. This is a new recurrence proof, not a new claim that
the square-path expansion was previously unknown.

All eighteen fixed rows at n=5,6,7 pass exact K and E checks, actual-component
checks and independent deletion-image checks. Receipt/frozen-source directory:
`/lake-cache/ai-projects/requests/VerticalStripLLT/square-path-layers-20260929/`.
Equation (EA6) in the endpoint note also proves that homogeneous forced source
classes factor exactly under endpoint attachments; they create no new additions.

**Remaining general gap:** when several components survive the available
reductions in a selected-corner sector, the full-layer identity gives only
their sum. We have not excluded or uniformly resolved that case. Independent
reducibility of every extra member of the minimal NN/DN completion class is
still unproved. The endpoint theorem settles the first historical resume item,
and the square-path recurrence settles a restricted crossing family. Neither
settles arbitrary crossing exteriors or the NN endpoint-moving swap.

Endpoint proof checkpoint `df1ea28` is pushed to `origin/main`; the original
endpoint note is preserved byte-for-byte as a prefix, 65 local file links and
`git diff --check` pass. The second increment preserves the source-addition
note at that checkpoint verbatim as a prefix. No new independent review is
claimed for either increment.

The full-layer/forced-union proof checkpoint `b316d41` is also pushed to
`origin/main`. Both proof-note prefix checks, 78 local file links and
`git diff --check` pass. All launched diagnostics have finished; no background
job needs monitoring or restarting. The maintained Rust checkout is clean.
No Lean source, manuscript or external Overleaf file changed. The mathematical
results above have not been formalized in new Lean declarations.

Runtime tools and `codex mcp list` were inspected. Lean MCP is rooted at
RealRooted, not this project. No Lean build is currently needed; no additional
worker or consultation is authorized or launched. The following account-switch
status is retained as the starting record; new proved results will be recorded
above it. The actual final swap checkpoint is `2511182`; `ae4c3a2` below was
its preceding proof/handoff checkpoint.

## Account-switch checkpoint — 2026-09-29

**Paused at the user's request for an account swap. The general recurrence
proof is unfinished.** No account, model, role or service-tier change was
made here. Last assignment: academic Astra/high, primary strategy/source
owner, on `main`. Resume only in the user's chosen session; do not launch
or relaunch any worker or consultation.

Latest mathematical direction from the user: **focus on the recursion of
whole components; proving the same recursion for colorings is usually easy.**
The requested proof uses the author's diagram bijections and recurrences.
The already-complete Lean word-functional proof is not a substitute.

Start with the [proof outline](docs/proofs/COMPONENT_RECURRENCE_OUTLINE.md),
then the [unfinished endpoint-attachment continuation](docs/proofs/COMPONENT_RECURRENCE_ENDPOINT_EXTENSION.md).
The complete prior handoff, including ownership and receipts, is preserved
in the [account-switch history](docs/archive/component-recurrence-handoff-before-account-switch-20260929.md).
Only relative Markdown links were adjusted in that archive. Original
crash-recovery dirty text is also preserved in the earlier recovery archive.

## What is established

- The [notebook PDF map](docs/proofs/COMPONENT_NOTEBOOK_MAP.md) decodes I/II/III,
  their positive weighted coefficients, the two identity sectors and the
  endpoint maps. The middle states require a paired diamond, not the proposed
  individual poset map. The smallest notebook example is fully proved.
- Whole-component corner deletion/envelope normalization and the
  [first-drop induction order](docs/proofs/COMPONENT_RECURRENCE_COVERAGE.md)
  are proved. DD/ND reduce to the NN/DN component problem.
- [Homogeneous DN completion](docs/proofs/COMPONENT_DN_SOURCE_ADDITIONS.md#completing-one-selected-edge-layer-of-the-direct-dn-image)
  and its [NN companion](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#exact-completion-within-one-selected-edge-layer)
  identify the minimal forced unions U_k(C), V_k(C) whose outputs are whole
  components. Independent reduction of every extra source component is open.
- Both minimal five-vertex pictures and the displayed six-vertex example
  have complete signed component recurrences. See
  [joint repairs](docs/proofs/COMPONENT_DN_JOINT_REPAIRS.md) and
  [source additions](docs/proofs/COMPONENT_DN_SOURCE_ADDITIONS.md).
- The retained-edge repair has arbitrary exterior whenever either f or r
  covers at Q+xs. With r,sz covering in Q, theorem (58) also allows wt
  covering with no suffix restriction. Theorem (65) allows redundant wt
  when J=K, using matched endpoint preparations.
- New local theorem (69), at the end of the
  [retained-edge note](docs/proofs/COMPONENT_DN_RETAINED_EDGE.md#interleaving-the-two-incoming-cuts),
  permits J not contained in K: assume t reaches z, all J tails exceed s,
  and J intersects H trivially. Interleave the incoming t/z cuts by decreasing
  tail, then use the matched preparations. Fixed paths pass 21,33,35,29
  flips, including extra incoming z-tails below and above t. No state
  enumeration was used for these path checks. This is a proved local repair,
  not the general component recursion.

Here J is the set of proper selected incoming z-tails reached from w;
K the corresponding tails reached from t; H the selected incoming t-tails
strictly between s,t reached from w. Full hypotheses are in the proof note.

## What to resume

1. Audit the candidate endpoint-attachment extension in the new note. It
   aims to extend the known whole-component DN recursion to arbitrary
   components attached at its two ends. The component product is established;
   the endpoint-marked identity argument and 16/32/16-state example have
   NOT yet been completed or checked. Do not cite this extension as proved.
2. Return to whole-component reassembly with crossing exterior edges.
   Source unions alone do not isolate C unless their extra components have
   independent smaller-diagram recurrences. Do not infer this from one
   orientation with a redundant corner or a vanishing alternating valuation.
3. Remaining local retained cases include common incoming forks ht,hz,
   lower incoming z-tails, and failures of background covers. The general
   left repair also remains open. Universal left source connectivity is
   false; it needs coefficient corrections/whole source additions.

Two bounded component-profile checks inform the choice of recursion:
area 01222 has 14 source and 15 target components, so a universal one-to-one
DN component correspondence is impossible. The established signed recursion
is the appropriate model. Area 012233 has matching HRV-profile multisets
for its 26 source and 26 target components; this is finite evidence only.
Neither check proves a general bijection or component formula.

## Restrictions, ownership and processes

- No Lean/Lake builds. No Claude, subagents or other workers without new
  explicit user authorization. The old crashed consultation has no useful
  durable result and must not be relaunched.
- Preserve all prior proof text. This increment leaves the retained-edge
  note's previous HEAD as a verbatim prefix. Historical status is archived,
  not discarded. Manuscript TeX and PDFs are unchanged.
- All diagnostic/compiler jobs launched in this continuation have finished.
  No background task needs monitoring or restarting. Primary is releasing
  this source lane after the clean, pushed handoff checkpoint.
- No maintained Rust edits. Its HEAD remains
  `d53fb193af3c69adedbd9ec8592f87235d809ffa`.
- Existing external consumer:
  `/lake-cache/ai-projects/requests/VerticalStripLLT/diamond-exploration/hrv-bridge/`.
  The task changed only its `first_join_tree_lifts.rs` and `dn_joint_span.rs`
  diagnostics; frozen copies accompany the receipts below. Reuse them.

## Verification and recovery

Prior pushed checkpoints: `d6c755a` (rejoining bypass), `ed60dcc` (paired
suffix, removes upper-tail guard), `9b622b0` (metadata). The final account-swap
checkpoint is `ae4c3a2`, pushed to origin/main. Archive preservation, 208 local
file links and git diff --check pass. No new independent review claimed.

Receipt directories under
`/lake-cache/ai-projects/requests/VerticalStripLLT/`:

- `retained-interleaved-incoming-20260929/`: current four exact paths.
- `component-dn-matching-20260929/`: two fixed profile comparisons.
- `retained-paired-suffix-20260929/`: earlier 17,39,41,29-flip paths.
- `account-switch-handoff-20260929/`: raw pre-cleanup handoffs, final snapshots,
  archive-preservation checks, commands, verification and checksums.

Overleaf current metadata:
`/home/paxinum/Dropbox/Apps/Overleaf/LLT flip/HANDOFF.md`.
Its complete previous version is retained beside it as
`HANDOFF-history-before-account-switch-20260929.md`.
The original diagram source remains `llt pics.pdf` in that folder.
