# Reduce repair builds for delegated Lean candidates

Build-free candidate ports have repeatedly omitted namespace opens, changed
inductive parameters in constructor results, or skipped dependent word
normalization. These errors add avoidable serialized compilation rounds.

Proposal: require each bounded handoff to list completed declarations and
known gaps explicitly, and include a textual preflight of imports, namespace
closure, inductive indices, goal bullets, and changed dependent types. For
parameter specialization, simplify a small coefficient equality separately
instead of traversing whole path/HRV expressions. Keep builds with the primary.
