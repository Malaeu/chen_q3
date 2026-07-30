# The conductor — design, state machine, lanes

The conductor is Claude Code (Fable/Mythos) running as the **transport**. It never
decides math (red line). It senses state, dispatches to lanes, harvests, detects
completion, advances, and self-schedules until a goal closes.

## Blackboard (files = single source of truth)

Everything is files, so a crash/restart resumes from disk. On the Mac, next to the live
bus (or a sibling `orchestrator/state/`):

```
state.json     # in-flight nodes: [{lane, target, sentAt, expect, chatUrl|jobId}], goal phase, cycle
log.jsonl      # append-only events
queue/         # prepared prompts per lane (codex/aristotle/proska/mythos)
inbox/         # harvested answers (proska/, mythos/, aristotle/) → parsed → advance
```

## Lanes (who does what, how driven)

| Lane | Where | Drive | Completion | Notes |
|---|---|---|---|---|
| **Codex** | CLI | `codex exec -m gpt-5.6-sol -c model_reasoning_effort=xhigh -C <repo> <prompt>` (background) | task-notification (push) | dispatcher + implementer; can also browse/download |
| **Aristotle** | CLI + dashboard | `aristotlelib` prove-from-file (async) | poll `Project.from_id().status`; scan holes | see `ARISTOTLE.md`; only on trigger |
| **Proška** | ChatGPT Pro (browser) | `select_page` + fill composer + Enter | `detect_complete.js` (HOURS) | judge; verdict = one md `# STATUS:` + codes |
| **Mythos** | claude.ai Co-Work (browser) | `select_page` + fill + Enter | `detect_complete.js` (minutes) | orchestrator-brain; writes the distribution |
| **conductor** | Claude Code | — | — | ME: senses, routes, harvests, schedules |

Harvest browser lanes with `harvest_conversation.js` (conversation-JSON, not DOM).

## State machine (per goal)

Derived from the live bus + `list_pages` + harvested inbox. Phases:

- `AWAITING_JUDGE` — a goal posted, no Proška verdict yet → relay to Proška, poll.
- `AWAITING_DISTRIBUTION` — verdict in hand, no Mythos distribution → relay to Mythos, poll.
- `DISPATCHING` — distribution parsed → run each block (Codex/Aristotle/Proška) per its order.
- `AWAITING_EXECUTOR` — Codex/Aristotle running → await notification / poll.
- `AWAITING_ACCEPT` — executor output bundled → relay to Proška for acceptance audit.
- `CLOSED` — Proška `ACCEPT_*` → mark goal closed, advance to next / stop.

## The cycle (one wake)

1. **SENSE**: `list_pages` (find agent tabs); read the live bus + `state.json`; for each
   in-flight browser node run `detect_complete.js`; check Codex notifications / Aristotle
   status. Compute each goal's phase.
2. **HARVEST**: for any node that just completed, `harvest_conversation.js` → parse verdict
   codes (Proška) or distribution blocks (Mythos) → write to `inbox/`.
3. **ROUTE + DISPATCH** (non-blocking): per phase, send the next prompt to the right lane
   (browser relay or `codex exec` background or `aristotlelib` submit). Always write the
   branch (`rh_clean`) + full tree URLs into browser briefs.
4. **VERIFY/ADVANCE**: on executor output, run the goal's validation gate + adversarial
   check before treating anything as done. Update `state.json` + the bus. **Push only the
   mirror** per CHANNEL_RULE; anything else needs Ylsha's go.
5. **CHECKPOINT + SLEEP**: log; schedule the next wake.

## Cadence (event-driven, not real-time)

- Proška: hours → poll `~15 min`.
- Mythos: minutes → poll `~2–3 min`.
- Codex: push-notifies on completion → no polling.
- Aristotle: minutes–hours → poll matched to the job.
- Self-schedule via `ScheduleWakeup` / `CronCreate`. One overnight run = a handful of
  deep cycles, not hundreds of ticks.

## Guardrails (unattended safety)

- **Red line**: conductor never decides/drafts math. Judge = Proška; brain = Mythos;
  Codex/Aristotle implement. No weaker-than-Pro model invents proof architecture.
- **Push scope**: on a closed goal, push the mirror **and the canonical bus together**
  (owner decision 2026-07-30, CHANNEL_RULE updated). The old "mirror only" form was
  obeyed literally and left canon uncommitted; Mythos reads GitHub at dispatch time,
  diagnosed off a stale repo and issued goal 037 task B for work already done. Pushing
  both on the same trigger keeps them from drifting. Lean sources and anything that
  would raise Route B status still need an explicit Ylsha go. No force-push, no merge
  into `main`.
- **Adversarial gate** before any `PROVED`/`ACCEPT` is trusted (validation gate + plants).
- **Fail-closed**: unclear phase, unparsable verdict, or uncertain hole-freeness →
  escalate to Ylsha, don't guess.
- **Spend caps**: max Codex cycles / Aristotle jobs / tokens per run; log any cap hit.
- **Termination**: goal closed (Proška `ACCEPT`) → stop + alert. Never run past the goal.

## Current concrete work-item (goal 034)

Proška ruled `REPAIR_034_BEFORE_CODEX`; Mythos issued a 4-такт CODEX dispatch (035 source
lock n=0..61, 036 FiniteCell257ToothAtomicDetector, cheap pair r=196/257 first). Aristotle
not engaged unless `lake build` fails twice. First live dispatch = Mythos's **ДЛЯ CODEX**
block, ТАКТ 0. Verdict + distribution captured in
`/tmp/.../scratchpad/proshka_verdict_034_2026-07-30.md` and `mythos_distribution_034_...md`
(Linux scratch — re-materialize on the Mac from the chats or these files).
