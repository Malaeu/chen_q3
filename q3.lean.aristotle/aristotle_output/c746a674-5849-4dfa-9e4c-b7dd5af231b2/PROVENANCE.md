# Local Git provenance

- Aristotle project:
  `c746a674-5849-4dfa-9e4c-b7dd5af231b2`
- Dashboard:
  `https://aristotle.harmonic.fun/dashboard/requests/c746a674-5849-4dfa-9e4c-b7dd5af231b2`
- Downloaded archive:
  `../c746a674-5849-4dfa-9e4c-b7dd5af231b2.tar.gz`
- Archive SHA-256:
  `f2618a8fa6c9f3cbc254aa1b3acc08dc2d457b989048910d1ba18f74c7ba1618`
- Local notarization date: `2026-07-27`

The official Aristotle result archive did not contain a `.git` directory, and
the public Aristotle API does not expose the cloud worker's internal Git
remote.  This repository was therefore initialized locally from the exact
downloaded snapshot.  Its commits are local archival commits, not a
reconstruction of Aristotle's private commit hashes or remote history.

At download time the project was in an active follow-up run.  The snapshot
contains three hole-free theorems from the completed run and two later draft
declarations with `sorry`.  Local `lake build` completed successfully; the
separate `AxiomAudit.lean` records the theorem-axiom audit.

No Git worktree was created for this archive.
