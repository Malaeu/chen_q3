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

## 5. Mac-only GAPS — for the owner to have Codex write at home

The Linux body is a slice; the Mac (primary) body is not visible here. Codex should fill:
- The full Mac `~/.codex/config.toml`: model/effort/approval/sandbox/projects/plugins/**notify** (Mac may
  have a native-notification hook Linux lacks); whether `chrome-devtools` MCP is present or replaced by the
  Codex.app embedded authenticated browser.
- Desktop-app driving stack (`osascript`/`cliclick`/Ghostty Accessibility; Codex.app + Claude Desktop as
  GUI, clipboard-paste) — how the Mac actually drives the heads.
- Auth pathway (Mac embedded logged-in session vs Linux token) — for Aristotle + ChatGPT.
- The **standing-goal / session-bootstrap contour** as Codex actually runs it (the 22h off-git artifact) —
  the authoritative version, not the owner-surfaced snapshot.
- The **exact chat open/continue trigger** Codex uses today (so CODEX_CONTROL codifies reality, then
  corrects it to one-living-chat-per-phase).

## 6. Feeds P9 (CODEX_CONTROL.md)

This reconstruction is the input for `CODEX_CONTROL.md` (P9): ONE control file = source of truth for Codex
behavior, `AGENTS.md` demoted to a thin pointer, symmetric with Fable's kernel and Proshka's protocol. It
must codify: the corrected chat discipline (one living chat per phase, continue not re-open, verdicts at
owner-boundaries), the goal-close duties, the SITE-BATON topology, the disk-wins reflex, the Aristotle
anti-surrogate banner, and a clean start-chain (no frozen PHASE/SPRINT_MONITOR pointers). Anti-orphan
clause applies: it names its own trigger-owner + Spine wiring. GAPS above filled by the Mac body.
