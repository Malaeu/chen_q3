# Repository topology decision v1

Decision: keep one proof monorepo and enforce semantic boundaries. Do not create
a new repository now. No repository setting, branch rule, file extraction, or
Route B mathematical object is changed by this decision.

This topology decision is not a completion claim. There is no unconditional RH
proof. The public canonical export remains conditional and open, the default
target remains conditional-compiled, and Route B remains `CHALLENGER / NOT_RH`.

- Public core stays in the monorepo behind the executable import firewall.
- Route B stays in the monorepo while its same-family source locks and live bus
  are active; it remains `CHALLENGER / NOT_RH`.
- Proof certificates remain atomically colocated with their Lean consumers.
- Q3 Discovery remains a shadow sidecar. Extraction is reconsidered only after
  a stable independent API, blinded holdout value, zero live-route writes, and
  a positive maintenance case are evidenced.
- Legacy remains quarantined in place. A read-only archive repository is
  reconsidered only after zero active imports/exports, frozen content, and a
  history-preserving migration plan are evidenced.

The single-authority invariant is part of every future extraction boundary.
Public-core, Route B, or Discovery extraction requires a completed state-
authority migration, zero selector writes to the superseded authority, and a
single-lifecycle validator pass. A second state lifecycle is not authorized.

The Route B decision is bound directly to the pinned Goal 058 selector and its
`STOP: TWO_DIFFERENT_FAMILIES_USED` contract, plus the pinned
`CanonicalRHRouteSkeleton.lean` same-cofinal guard and its proof receipt. It is
not inferred from a prior topology verdict.

The import firewall currently separates the public canonical slice from legacy
and challenger declarations. This supports the monorepo choice; it does not
claim that GitHub branch protection or required checks have been configured.
If the firewall cannot remain enforceable on the canonical branch, the
decision requires a new evidence-bound review of minimal public-core
extraction. Repository count alone is not treated as a semantic boundary.
The P9 foreign dirty snapshot is carried into the P10 receipt and rechecked by
path, object type, permission mode, bytes, and size before acceptance.
