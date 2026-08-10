# Route B live bus protocol

Status: `ACTIVE`
Version: `v4-live`, 2026-08-06
Canonical directory: `docs/routeB_bus/`

This protocol describes the bus that is actually consumed by
`routeb_status.py`. The former `routeB_twolevel_spectral_ladder/bus/`
protocol is a frozen historical snapshot.

## Identity and lifecycle

- A standing root uses a three-digit id such as `056` or `057`.
- A shift-sized child may append a lowercase lane suffix, for example `056u`.
- Files are `<id>_<stem>.goal.md` and `<id>_<stem>.answer.md` with the same
  id and stem.
- The newest numeric root is the current bus family. Older roots are history
  and cannot preempt it merely because an old answer is absent.
- A matching answer closes that physical goal. The next numeric root is
  selected only by an explicit standing direction; Codex does not infer a
  theorem or create a forbidden Bus 010 from numbering alone.

## Canonical machine header

The first fenced YAML block in an answer contains:

```yaml
GOAL: <three-digit standing root>
PHASE: <optional phase within the root>
NODE: <exact node name>
STATUS: CLOSED
EXACT_RESULT: <exact result code>
```

Historical answers may use `RESULT` or `SUCCESS` instead of `EXACT_RESULT`,
and a terminal closed subtype such as `CLOSED_PHASE0`. New answers use
`EXACT_RESULT`. `SEARCH_FLAGS` belongs in this same header when a search was
performed.

`MYTHOS_PROSHKA_HANDOFF`, `ACTIONS LOG`, and `# STATUS:` are historical prose
contracts, not parallel machine headers. Evidence, hashes, commands, plants,
and validation remain required in the answer body whenever the goal contract
requires them.

## Standing invariants

- `CHALLENGER / NOT_RH` remains explicit.
- `BUS_010: VOID` and `GOAL_055: HOLD` remain unchanged.
- G2/CCM stays frozen unless a later delegated strategic review explicitly
  reopens it.
- `PX_RH_CLAIM` is the sole owner gate. Promotion and any RH claim are
  forbidden without that gate.
- Closed goals are immutable; later corrections use a new child or addendum.
- Canon and mirror land in one scoped commit. `ROUTE_B_STATE.md` is written
  last for a mathematical gate.

## Validator

```bash
python3 q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py --check
```

`CHECK: OK` means that the newest live bus family, its answer headers, the
current execution state, and registered source pins agree. It does not prove
the mathematics recorded by an answer and does not promote Route B.
