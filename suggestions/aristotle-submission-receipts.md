# Check remote submission receipts explicitly

Observed: `aristotle submit` reported an active-project capacity error while
returning exit status zero. Treating exit zero as successful submission could
leave a nonexistent proof job recorded as running.

Proposal: an eventual shared submission helper should require a returned
project ID, query its task ID once, and record both in a receipt. Until then,
inspect submission output and never invent a job ID or automatically retry a
capacity rejection. The current rejected orientation-column request is saved
outside the checkout and has no remote ID.
