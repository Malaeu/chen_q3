WATCH TICK — READ ONLY. You were woken by a timer because origin/rh_clean moved
ahead of the local HEAD. Mechanics: docs/Codex/WATCH_LOOP_FOR_CODEX.md.

Your chain is AGENTS.md -> docs/CODEX_CONTROL.md -> SESSION_ENTRY.md. CLAUDE.md
is the observer's file; do not read it as policy.

## This tick may not write the repository or worktree

FORBIDDEN in this tick, without exception:

```
any repository or worktree edit, create or delete
git pull / add / commit / push / rebase / reset / checkout
lake build, lake env lean, any writing refresh (spine.py --refresh,
  inventory.py, kb migrators)
sending anything outside the machine
```

The wrapper already fetched origin and launched this turn with
`--sandbox read-only`. The writing path is different: `three_body_loop.py
launch` carries at-most-once, the writer lock and the pins. If this tick
concludes that a write is needed, it reports the exact pending action and stops.

## What to do

1. Confirm the branch and run
   `git rev-list --count HEAD..origin/rh_clean`. Do not fetch or pull again.
2. Read the remote-only delta with `git log HEAD..origin/rh_clean`,
   `git diff --name-status HEAD..origin/rh_clean`, and
   `git show origin/rh_clean:<path>`. A judge verdict has the `[Proshka]`
   prefix.
3. Classify it in one line each:
   - which node it admits, kills or authorizes;
   - whether it names a task for this body;
   - whether it contradicts a verdict already on the branch.
4. Do not interpret this read-only wake as permission to compete with a writer.
   Report any dirty worktree or branch divergence and stop.
5. Report. That is the whole deliverable of a read-only tick.

## What NOT to conclude

A verdict that authorizes a Lean transaction does not authorize this tick to
start it. It authorizes the next writing wake-up, which the owner or the
launcher begins.

Kernel green is not admission. Three statuses exist and only the third may be
consumed: `SOURCE_WRITTEN` -> `KERNEL_GREEN` -> `SEMANTICALLY_ADMITTED`.

## Standing boundaries, carry into every report

```
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
ARISTOTLE: false
PX_RH_CLAIM: do not touch
```

## Traps already paid for — do not rediscover them

`pgrep -f` matches its own command line and will tell you a dead process is
alive. Check by `comm`.

Never decide "the remote changed" by comparing hashes: you will wake on your
own pushes. The condition is `git rev-list --count HEAD..origin/rh_clean` being
greater than zero.

Never pipe a gate into another command: `$?` becomes the last stage's code and
a red gate reads as green. Use `${PIPESTATUS[0]}`.

A `BASE_HEAD` is copied from live `git rev-parse HEAD` output, never
reconstructed and never carried over from a directive — a judge commit can land
between the directive and the execution.

## If there is nothing new

Say so in one line and exit. A quiet tick is a correct tick.
