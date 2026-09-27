# Serialize Lean builds in the shared wrapper

Independent project owners can both observe an idle process list and then
start a build. Process inspection alone therefore has a race. In this batch,
an additional orchestration mistake also launched a short check before its
process-check output had been inspected; we stopped further local launches.

Proposed infrastructure follow-up: make `lake-workspace` acquire a common
advisory lock under `/lake-cache/ai-projects` before a build or compiler command,
and release it when that command exits. Record the owning PID and project for
read-only status. Keep long-lived editor servers outside the build lock.
All projects must use the same lock; a project-specific lock is insufficient.

Until the shared wrapper is changed and tested, inspect process output in a
separate decision before launching, and wait for any active batch to finish.
This is a proposal only; no shared wrapper was edited here.
