# TASK 2026-08-23 — repair the default `q3_check.sh` gate

```yaml
task_id: 2026-08-23-q3-check-default-gate-repair
written_by: LINUX_CLAUDE
authorized_by: OWNER_DIRECT_REQUEST_2026_08_23
authorization_scope: TOOLING_REPAIR_NO_MATHEMATICS_NO_LIVE_ROUTE
defect_found_during: H2A_4_1B_3C_1_11_SELECTED_FERRERS_PACKET_VARIATION (W2)
```

## Read first (your chain, not mine)

```
AGENTS.md  ->  docs/CODEX_CONTROL.md  ->  SESSION_ENTRY.md
```

`CLAUDE.md` is the observer's file. Do not read it as policy and do not let it
into your control header — `spine.py::validate_codex_bootstrap` checks
`AGENTS.md` only, and the `BEHAVIOR_BODY_MULTIROLE` latch fails validation if
the two chains merge.

## Why this task exists

Project rule: **a defect found while doing other work is repaired first.** A
filed defect keeps returning wrong answers while everyone reads around it.
This one was found on 2026-08-23 during the W2 Lean tact and is filed here
because repairing it is not part of that tact.

## The defect, already reproduced — do not spend a turn re-deriving it

```bash
./scripts/q3_check.sh          # no arguments -> exit 1
```

```
lean Q3/Proofs/PSD_CenteredCardinalBSpline.lean
Q3/Proofs/PSD_CenteredCardinalBSpline.lean:1:0: error: object file
'.../Q3/Proofs/PSD_BSplineAnalyticModel.olean' of module
Q3.Proofs.PSD_BSplineAnalyticModel does not exist
```

Observations already on disk (verified, not recalled):

1. With no arguments the script checks three hardcoded targets:
   `PSD_CenteredCardinalBSpline`, `PSD_CenteredCoeffEntryHboxImport`,
   `PSD_CenteredCoeffCertifiedBlockImport`.
2. All three `.lean` sources exist. None of the three has an `.olean`, and
   neither do their dependencies.
3. `grep` for these modules in the root `Q3.lean` returns **0** — they are
   outside the root import graph, so a plain `lake build` never builds them.
   `lake build` itself is green (7817 jobs).
4. Repairing one missing dependency by hand
   (`lake build Q3.Proofs.PSD_BSplineAnalyticModel`) moves the failure to the
   next missing dependency. It is a class of defect, not one file.
5. Passing an explicit target works today:
   `./scripts/q3_check.sh q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersPacketVariation.lean`
   → `q3_check ok`, exit 0.

So: the script's argument mode is healthy; its **default** mode names targets
the build system does not maintain.

## What to decide (this is the judgement, and it is yours)

Pick one and justify it in the report. Do not pick by convenience — pick by
what the gate is *for*.

| Option | What it means | Cost |
|---|---|---|
| A. Default builds its targets first | script runs `lake build <module>` for each default target before `lake env lean` | slow default; honest |
| B. Default list is stale, replace it | the three PSD files no longer represent what the gate must protect; name the current targets | needs a defensible choice of targets |
| C. Bring the modules into the graph | add them to the root import graph so `lake build` maintains them | changes what the whole build carries |

Whatever you pick, the answer must survive this question: *after your change,
does a broken file in the protected set still fail the gate?* A default that
passes because it checks nothing is worse than the current failure — the
current failure at least announces itself.

## Hard boundaries

```
Q3 mathematics source edit:        FORBIDDEN
docs/routeB_bus/** write:          FORBIDDEN
AGENTS.md / CODEX_CONTROL.md edit: FORBIDDEN
removing the hole-marker scan:     FORBIDDEN
removing the new-axiom diff scan:  FORBIDDEN
weakening any check to green it:   FORBIDDEN
sorry / admit / native_decide:     FORBIDDEN
PX_RH_CLAIM:                       DO NOT TOUCH
```

Write list:

```
scripts/q3_check.sh
docs/cartographer/TOOLS.yaml          (only if the tool's record changes)
q3.lean.aristotle/Q3.lean             (only under option C)
docs/Codex/REPORT_2026-08-23_q3_check_default_gate_repair.md
```

## Gates — all three must pass, pasted verbatim into the report

```bash
# 1. the repaired default
./scripts/q3_check.sh                     ; echo "EXIT=$?"

# 2. the argument mode still works
./scripts/q3_check.sh q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersPacketVariation.lean ; echo "EXIT=$?"

# 3. the build is still green
cd q3.lean.aristotle && lake build       ; echo "EXIT=$?"
```

Plus one **negative control** you write yourself: temporarily break a file in
the protected set, show the repaired default gate rejects it, restore the
file. A gate that has never been seen to fail has not been tested.

## Report contract

`docs/Codex/REPORT_2026-08-23_q3_check_default_gate_repair.md`, containing:

- `BASE_HEAD` copied from the live output of `git rev-parse HEAD` — **copy the
  string, never reconstruct it.** A fabricated SHA already caused one receipt
  FAIL on this project (3C.1.7).
- which option you chose and why the other two were rejected;
- the three gate outputs verbatim, with exit codes;
- the negative control, with the failure it produced;
- `CLOSES:` / `OPENS:` — if your fix opens a new input, name it. A proposal
  that only opens is a debt, not a proposal.

## Commit

One commit, message prefix `[Codex][rh_clean]`, no AI attribution lines, no
co-author lines. Push only after the owner approves the exact payload — the
per-action approval requirement does not lapse for tooling work.

## Boundary echo (carry these into your report)

```
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
ARISTOTLE: false
```
