# Codex internal cycle — reconstruction (2026-08-05)

Built from a 3-agent sweep: runtime config (`~/.codex` Linux slice) · interaction cycle (orchestrator
loop) · real behavior (H2b transaction export + `PROSHKA_REASONING_TIME_LOG` + commit cadence). Purpose:
capture the part of Codex's cycle we deliberately keep OUT of GitHub, so `CODEX_CONTROL.md` (P9) can be
written from fact, and so the owner knows exactly which GAPS to have Codex fill at home (Mac body).

## 1. Runtime config (Linux slice — Mac differs, see GAPS)

| Param | Value | Meaning |
|---|---|---|
| model / effort / verbosity | `gpt-5.6-sol` / `xhigh` / `low` (+ concise summaries) | max reasoning, terse output |
| approval_policy / sandbox | `never` / `danger-full-access` | fully autonomous, no human gate, danger-banner suppressed |
| provider / tier / personality | `chatgpt-http` (WebSockets OFF) / `priority` / `pragmatic` | routes via ChatGPT backend; WS off dodges ~75s stall |
| MCP | `chrome-devtools` (stealth headless Chrome) | the ONLY MCP — how Linux body reads Proshka verdicts via browser |
| notify/hooks | **ABSENT** | Codex does NOT signal completion; orchestrator polls (`detect_complete.js`) |
| features / repo cap | multi_agent+steer+collaboration / `.codex/config.toml`: max_threads=6, depth=1 | sub-agents capped for Q3 |
| sub-agent personas | `q3-worker` (exec) · `q3-researcher` (oracle/search) · `q3-lean-worker` (Lean/Aristotle) | 3 tightly-scoped bodies |

⚠️ **Bug link:** `q3-worker` persona's entry-chain is `SESSION_ENTRY → PHASE_MONITOR/SPRINT_MONITOR →
AGENT_PROTOCOL` — but `PHASE_MONITOR` = PARKED-zombie, `SPRINT_MONITOR` = DONE (per SYSTEM_SPEC). Codex
sub-agents navigate by FROZEN pointers. Fixing them (P1b) also cleans Codex's own start-chain.

## 2. Interaction cycle (5 stages, event-driven)

`SENSE → HARVEST → ROUTE+DISPATCH → VERIFY/ADVANCE → CHECKPOINT+SLEEP`, one per wake.
Per-goal state machine: `AWAITING_JUDGE → AWAITING_DISTRIBUTION → DISPATCHING → AWAITING_EXECUTOR →
AWAITING_ACCEPT → CLOSED`. Channels: browser (chrome-devtools MCP — `harvest_conversation.js` fetches the
chat's API JSON, not DOM) primary; `packet.py` link-free clipboard fallback for repo-less heads. Proshka
asymmetry: inbound automated (she reads the `docs/routeB_bus/` mirror via GitHub connector — briefs give a
LINK), outbound manual (verdict lifted from chat by hand). Cadence: Proshka ~15min poll (thinks hours),
Mythos ~2-3min, Codex push-notifies. Goal-close duties (Codex, post-conductor-retirement):
answer.md+certs → ROUTE_B_STATE last-step → mirror refresh + MANIFEST rebuild → **commit+push canon+mirror
ONE commit**. Guards: BUS_010 VOID · no force-push · no merge→main · owner-go for Lean/promotion.

## 3. Real cadence + the Proshka chat antipattern (measured)

- **~2-4 commits/node, ~2-3 commits/Proshka verdict.** A node every ~10-25 min; overnight ~35 nodes,
  23:16→06:48 nonstop. Triad per node: `Start/Record adjudication` → `Select/Ratify gate` → `Prove`
  (+ occasional Repair/Audit). A goal closes when its `.answer.md` lands — **closure ≠ solved** (054
  closed `RECEIVER_PARTIAL`, an inventory verdict, then spawned 054.1 / 054.1-v2).
- **Consults Proshka only at undecided theorem-shape forks** (next node / surrogate-vs-production /
  fork); owner-OK reserved for definition-mint / promotion / front-switch / Aristotle-submit / FATAL.
  When a fork was already assigned, Codex deliberately did NOT re-ask (good — avoids waste).
- **🔴 The antipattern, confirmed by data:** all 14 entries in `PROSHKA_REASONING_TIME_LOG.md` are
  stamped "**Fresh project chat**", each **re-uploading a full context pack** (one is 276,937 bytes),
  each pinned to a different HEAD. Reasoning-time per verdict: mean ≈ **21 min** (range 11-37), wall up
  to **53m41s** (polling lag); `answer_now_clicked: false` throughout. So ~14 fresh chats + 14 full
  context re-uploads in one day = the exact EUR cost driver. Fix already speced (batch-per-PHASE, one
  living chat) but NOT yet in any file Codex reads → still happening.

## 4. Emergent / non-GitHub cycle parts (what the owner wanted captured)

Behaviors invented live and only partially written down — these are the "off-git" cycle:
1. **Standing goal lived 22h27m ONLY in Codex's UI session** — the single biggest off-git control artifact;
   materialized to repo only after the owner surfaced it (`CODEX_RUNTIME_CONTOUR_FOR_MYTHOS_2026-08-04.md`
   + `CODEX_SESSION_BOOTSTRAP_CONTOUR`). Prime example of contour-loss risk.
2. **Fresh-chat + full-context re-upload per node** (§3) — emergent, real EUR cost, undocumented until the
   Aug-5 10:34/12:00 commits.
3. **`PROSHKA_REASONING_TIME_LOG.md`** — created ad-hoc 8/4 22:45 in response to token/cost pain; its
   "never click Answer now" + "measure send→completion" is local convention, not a pre-existing rule.
4. **`Preserve … review reasoning time` commits** — emergent instrumentation (banking timing measurements).
5. **SITE BATON / `ACTIVE_SITE: MAC|LINUX`** — the whole Mac⇄Linux "push = baton, park the other platform"
   topology was invented live this session. Visible in git: `[MacOS]` = autonomous math body, `[Linux]` =
   owner-driven docs/audit body.
6. **PARENT address-inheritance naming** (054 → 054.1 → 054.1.a/.b → 054.1-v2, 055 = 054.2) — adopted
   mid-session because free names ("WR"/"Schur") were untrackable; drifted from the owner's own rule.
7. **Journal (STATE) lag during autorun** — ~25 daytime + a full night of math commits with NO
   ROUTE_B_STATE rows (stuck "IDLE 2026-08-03"); STATE updates only at Docs gates in master-DAG mode.
8. **"Disk wins" fail-closed reflex** — Codex refuses pasted chat text as a trigger; only the on-disk
   `NNN_*.goal.md` triggers; leaves route-state deliberately untouched when a goal forbids mutation.
   Enforced by `routeb_status.py --check`, not by any single rule doc.
9. **Aristotle surrogate hazard (C04)** — Aristotle, given raw text, reconstructed the CCM definitions and
   "proved" the correctly-named theorem about a FAKE object (cosh-kernel, width exactly 10⁻⁸⁸ because
   self-constructed). Caught at gate 0. Mitigation ("every Aristotle draft carries ONLY-via-Codex-fill
   banner + real imports") invented in-session → formalized as the `054.1b` repair path.

Data hygiene note: the 054 verdict + the H2b export carry benign zero-width spaces (ZWSP) in the math
notation — OCR/paste artifacts, not injection.

## 5. Mac-only GAPS — resolved from the primary Mac body (2026-08-05)

This is a machine-local capability snapshot, not semantic project policy. It contains no credentials,
tokens, cookies or browser-session material.

### GAP 1 — Mac `~/.codex/config.toml`

- Model/runtime: `gpt-5.6-sol`, reasoning effort `xhigh`, tool-output limit `25000`, personality
  `pragmatic`, service tier `default`.
- Host authority: `sandbox_mode = "danger-full-access"`, `approval_policy = "never"`; trusted project
  roots are `/Users/emalam`, `/Users/emalam/GitHub`, `/private/tmp`, and the canonical Q3 checkout.
- Native completion notification is present. `notify` invokes the bundled Sky Computer Use client with
  event `turn-ended`; this is the Mac push-notification path that the Linux slice lacks.
- MCP/runtime surfaces: `chrome-devtools` is enabled against `127.0.0.1:9222`; Playwright and the bundled
  `node_repl` are configured; RepoPrompt and the standalone `computer-use` MCP stanza are disabled. This
  does **not** mean the app lacks browser/desktop control: Codex.app also exposes its authenticated in-app
  browser plus the installed Browser, Chrome and Computer Use plugins. The real Mac therefore has both
  `chrome-devtools` and the embedded authenticated browser; one did not replace the other.
- Enabled connector/artifact plugins at this snapshot: Google Calendar, Gmail, GitHub, Google Drive,
  Documents, Spreadsheets, Presentations, PDF, Chrome, Template Creator, Computer Use, Visualize, Sites,
  and Browser.
- Native features: goals, memories and Chronicle are enabled; idle sleep prevention is enabled; desktop
  follow-ups use `steer`; links default to the in-app browser and repo paths open in Ghostty.

### GAP 2 — desktop-driving stack

The canonical local adapter is `orchestrator/desktop_app.sh` (`codex` and `claude` lanes), with the older
`orchestrator/codex_app.sh` retained as the Codex-only predecessor:

1. `osascript` activates the `ChatGPT` or `Claude` process, reads window geometry, and performs atomic
   Cmd-key shortcuts.
2. `cliclick` clicks a composer coordinate derived from current window geometry and presses Return only
   after verification. It is not used to type text or to hold modifier keys.
3. `pbcopy`/`pbpaste` carry the complete payload, including Cyrillic, independently of keyboard layout.
4. Every mutation is `focus -> read existing composer -> paste replacement -> read back exact bytes ->
   send`. A nonempty or ambiguous owner draft means hands off, not overwrite.
5. Ghostty must have Accessibility permission **and be relaunched after the permission change**; screen
   recording is used for visual diagnosis when coordinates are uncertain.

The current Codex.app can additionally drive its in-app browser and desktop apps through bundled plugins,
but those capabilities do not weaken the read-before-write and read-back-verification rule.

### GAP 3 — authentication pathway

- ChatGPT/Codex/Proshka use the owner's signed-in Codex.app and embedded/in-app browser session. The app
  keeps its OAuth material in machine-local Codex state; no ChatGPT token or cookie belongs in the repo.
- The production Aristotle path is the CLI/API workflow from the project venv, authenticated by the
  machine environment variable `ARISTOTLE_API_KEY`. The app/browser lane may inspect a separately
  signed-in Aristotle web session, but it is not the canonical submit/download path.
- `OPENAI_API_KEY` is also machine-local environment state. Neither key value nor local auth files are
  copied into Git, the Spine, context packs or reports.

### GAP 4 — standing goal and session bootstrap

The standing goal is a native Codex task-runtime object, not a Markdown monitor. On this Mac it is stored
outside Git in `~/.codex/goals_1.sqlite` and keyed to a Codex thread. While its status is `active`, Codex
continues the same objective across turns and automatic continuations; it stops only on the native terminal
states such as `complete`, `blocked`, `paused`, or a resource limit. The current plan, cursor and in-flight
tool state remain more ephemeral than the standing objective.

The exact long-running objective created at `2026-08-04T00:15:14+02:00` was:

```text
Drive the Q3 canonical-roof closure loop directly with Proshka: finish and
ratify the materialized D0.7e.5a closeout, then repeatedly select, implement,
Lean/source-validate, document, and return the smallest executable
source-locked nodes across G2/H2a, G3/H2b, G5/S1, and G6/S2, preserving
CHALLENGER / NOT_RH and Bus 010 VOID, until every roof supplier is discharged
and the canonical roof theorem is instantiated, or a genuine
theorem-shape/source blocker requires the owner's decision.
```

The local runtime recorded `20,786,139` tokens and `128,469` seconds before that goal moved to `blocked`
at `2026-08-05T12:24:29+02:00`. This objective is only a persistence envelope: every continuation first
re-enters through `AGENTS.md -> SESSION_ENTRY.md`, reconciles the live checkout, scoped selector, physical
bus and current stop code, and lets disk authority override stale runtime intent. The recovery copy is
`docs/routeB_bus/CODEX_RUNTIME_CONTOUR_FOR_MYTHOS_2026-08-04.md`; the full reproducible entry map is
`docs/routeB_bus/CODEX_SESSION_BOOTSTRAP_CONTOUR_FOR_MYTHOS_2026-08-04.md`.

### GAP 5 — exact chat open/continue trigger observed before P9

The behavior actually observed earlier on 2026-08-05 was:

```text
substantive Proshka proof transaction requiring a theorem-shape verdict
  -> open a fresh idle chat in the same Q3 project
  -> upload a new source-locked high-recall context pack
  -> keep that conversation only while its one answer is generating and harvested
  -> the next substantive transaction opens another fresh chat
```

A commit, elapsed time, or bus number was not by itself the trigger; dispatch of a new substantive
Proshka adjudication was. Busy chats were never reused for a second send, and `Answer now` was never
clicked. This paragraph records historical reality so the reconstruction is honest. It is **not active
policy**: the later ratified P9 behavior kernel supersedes it with one living chat per precommitted phase,
continued across ordinary goals, commits, session restarts and Mac/Linux batons; a fresh chat is legal
only after a materialized phase change.

## 6. Feeds P9 (CODEX_CONTROL.md)

This reconstruction is the input for `CODEX_CONTROL.md` (P9): ONE control file = source of truth for Codex
behavior, `AGENTS.md` demoted to a thin pointer, symmetric with Fable's kernel and Proshka's protocol. It
must codify: the corrected chat discipline (one living chat per phase, continue not re-open, verdicts at
owner-boundaries), the goal-close duties, the SITE-BATON topology, the disk-wins reflex, the Aristotle
anti-surrogate banner, and a clean start-chain (no frozen PHASE/SPRINT_MONITOR pointers). Anti-orphan
clause applies: it names its own trigger-owner + Spine wiring. GAPS above filled by the Mac body.
