# Reduce repair builds for delegated Lean candidates

Build-free candidate ports have repeatedly omitted namespace opens, changed
inductive parameters in constructor results, or skipped dependent word
normalization. These errors add avoidable serialized compilation rounds.

Proposal: require each bounded handoff to list completed declarations and
known gaps explicitly, and include a textual preflight of imports, namespace
closure, inductive indices, goal bullets, and changed dependent types. For
parameter specialization, simplify a small coefficient equality separately
instead of traversing whole path/HRV expressions. Keep builds with the primary.

The 2026-09-27 restart also exposed a reversed adjacent-swap equivalence in a
build-free candidate. Check each proposed equivalence against a single forward
edge before writing its proof. Include canonical-residue simplifications and
implicit argument order in the preflight: both caused repair rounds in the
cover adapters. For relation exchanges, prove prefix/suffix compatibility
separately, then use `simp` and `grind` on the finite local conditions; applying
`grind` to the entire expanded word exceeded its default split limit.
