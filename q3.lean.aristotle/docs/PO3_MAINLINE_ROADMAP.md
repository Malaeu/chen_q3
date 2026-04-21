# PO3 Mainline Roadmap

Updated: 2026-04-21

## Role

This file is the canonical execution roadmap for the `PO3` subroute inside the
public `H-bridge` mainline.

It is the place to read the status-aware ladder:

- which `PO3` nodes are already closed,
- which node is the current live mathematical wall,
- which downstream packets stay conditional until that wall falls.

It is not the manuscript typing map and not the session log.

## Canonical Status Rule

If `PO3` status language disagrees across files, resolve conflicts in this
order:

1. `PROJECT_ORCHESTRATOR.md`
2. this file
3. generated address/status artifacts such as `ACTIVE/pipeline/oracle_questions/BY_ADDRESS.md`
4. `docs/INSIGHTS.md`

`docs/PAPER_MAINLINE_TRACKER.md` stays paper-facing and may use broader
gate-level language; it does not override the execution status of the `PO3`
subroute.

Generated address/status artifacts can lag the real mathematical state. The
canonical truth for `PO3` is therefore top-down, not bottom-up.

## Current Canonical Summary

- Public route remains `H-bridge`.
- `PO3` remains the live lower-shell gateway inside `H1^f`.
- The closed lower-shell feeder is:
  `PO3-shell.5/.6 -> PO3a-A2-real -> PO3a.4-real -> PO3-rig.1b.cert-real -> PO3-tail.1-real -> PO3-square.2d0a/.1/.2`.
- The unique current live mathematical wall is `PO3-square.2d3`.
- `PO4/PO5 -> H2^f -> H3^f -> H4^f -> RH` stay conditional consumers after the
  wall.

## Status-Aware Ladder

| Node | Status | Purpose | Output | Kill Criterion / Invalidation |
| --- | --- | --- | --- | --- |
| `PO3-shell.5` | done, frozen feeder | Name the first-zeta kernel family at the shell level | Family-level predicate for the local packet kill-layer | n/a; reopen only if the shell family API is shown incomplete |
| `PO3-shell.6` | done, frozen feeder | Export the direct anti-diagonal bridge for that named family | Family-level contradiction form against one-variable filtered candidates | n/a; reopen only if downstream consumers need a different shell interface |
| `PO3a-A2-real` | done, frozen feeder | Package the filtered `(+,-)` defect into named packets | Manuscript-facing `corner + row + column + mixed` packet decomposition | n/a; reopen only if the filtered `(+,-)` packetization is mathematically wrong |
| `PO3a.4-real` | done, frozen feeder | Strip the outer layer and feed rigidity back to the closed shell | Outer-transport cancellation gives the scalar coordinate profile law | n/a; reopen only if outer stripping fails on the real Q3-side data |
| `PO3-rig.1b.cert-real` | done, frozen feeder | Freeze the honest outer-transport coordinate certificate | Direct `PO3Cert` bridge from transported cancellation data to one scalar window law | n/a; reopen only if the real certificate needs extra data not covered by the current contract |
| `PO3-tail.1-real` | done, frozen feeder | Compress tail law, decay, sampling rescaling, and square repackaging | Honest Q3-side certificate bridge to `∀ r > N, squareReceiver (r^2) = 0` | n/a; reopen only if the real Q3-side tail/sampling packet is incompatible with the current contract |
| `PO3-square.2d0a` | done, support shell | Transfer square-tail zero to bilateral transform-tail zero | Clean zero-transfer shell after the square-to-transform reduction | not a live blocker; support packet only |
| `PO3-square.2d1` | done, support shell | Freeze the exact post-reduction target | Named wall target: even transform-side receiver with bilateral integer-tail zeros | not a live blocker; support packet only |
| `PO3-square.2d2` | done, support shell | Freeze the contradiction shell for signed-dominance vs vanishing mirror | If main tower is eventually bounded below and mirror tends to zero, the wall contradicts itself | not a live blocker; support packet only |
| `PO3-square.2d3` | current live wall | Prove signed rightmost dominance versus mirror suppression for the real one-sided Gamma tower | Eventual lower bound on the signed main tower strong enough to activate `PO3-square.2d2` | if the real tower admits a genuine infinite-support signed self-cancellation that defeats rightmost dominance, record a route kill before reopening `PO3` |
| `PO3` lower-shell closure | conditional consumer after `2d3` | Synchronize the lower-shell interface once the wall is killed | Honest closure of the `PO3` lower-shell gate inside `H1^f` | invalidated only by a genuine non-cap obstruction after the wall |
| `PO4/PO5` | conditional consumers | Pass the now-closed lower shell into the next filtered operator packets | Synchronized finite/cap transfer above `PO3` | invalidated only if `PO3` closes in a form incompatible with the frozen `PO4/PO5` packet interfaces |
| `H2^f -> H3^f -> H4^f` | conditional consumers | Reactivate the frozen upper `H-bridge` chain once `PO3` is honest | Suzuki tail/cap reduction -> filtered gap transfer -> Suzuki endpoint to RH | invalidated only by a new obstruction above `PO3`; until then they are not current blockers |
| `RH` | final endpoint | Finish the public `H-bridge` route | RH through `H4^f` | invalidated only if the public `H-bridge` route itself is killed and the project rolls back to another frozen branch |

## Support-Shell Note

The packets `PO3-square.2b*`, `PO3-square.2c*`, and
`PO3-square.2d0a/.1/.2` are part of the same square-side support shell around
`PO3-square.2d3`.

They are useful and frozen, but they are not separate mainlines and they do not
replace the current wall.

## Post-Wall Reactivation Rule

If `PO3-square.2d3` is closed honestly, do not invent a new architecture.
Immediately reactivate the frozen consumer chain:

`PO3 lower-shell closure -> PO4/PO5 -> H2^f -> H3^f -> H4^f -> RH`.

If `PO3-square.2d3` dies honestly, record the kill certificate in
`ACTIVE/graphs/ROUTE_KILL_REGISTRY.md` and roll back at the route level from
`H-bridge`, rather than opening a new improvised `PO3` branch.
