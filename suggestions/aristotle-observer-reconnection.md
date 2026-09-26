# Reconnect Aristotle observers without restarting tasks

Observed: `aristotle show PROJECT --task TASK` repeatedly loses its stream
after several minutes and exits zero with an error message. The remote task
continues. This has required repeated manual status checks, new observer
sessions and handoff-only commits.

Suggested improvement to the owning Aristotle tooling: add a monitored observer
that retains the exact project/task IDs, checks authoritative task status after
stream failure, and reconnects with bounded backoff while that task is queued
or running. It must never resubmit, cancel, or start a task because a stream
ended. Preserve events across reconnections, report terminal task status
separately from observation errors, and download only after confirmed completion.

This is a tooling proposal, not an installed watcher or active policy.
