# ORCHESTRATION_DESIGN.md — Autonomous conductor for the Route B RH loop

Status: DESIGN v0.2 (2026-07-30). Supersedes v0.1 (which mis-modeled the system as
the Q3/Aristotle chain + a from-scratch bus). This version is written against the
**real** system: the Route B Lamport bus that already exists and runs.

> **v0.3 note (2026-07-30 evening):** pipe proven live end-to-end
> (Codex → Proška REPAIR_034 → Mythos distribution). Last blockers solved: full browser
> visibility/control via **`chrome-devtools-mcp`** (`list_pages` sees ALL tabs, dissolving
> the tab-group limit) and reliable harvest via **conversation-JSON fetch** (bypasses DOM
> virtualization). Runnable setup + operation guide now in **`orchestrator/`**
> (`README.md`, `CONDUCTOR.md`, `harvest_conversation.js`, `detect_complete.js`,
> `ARISTOTLE.md`). The Co-Work relay (§3) is superseded by chrome-devtools-mcp driving any
> tab directly. This doc remains the design rationale.

Authored from the Linux clone reading `origin/rh_clean` (fetched 2026-07-30, head
`91b78ddf`). The **live** repo, browser Proška, Codex, Aristotle and Co-Work all run
on Ylsha's **Mac** — so paths/behaviour below must be validated there before wiring.

Goal: remove Ylsha as the "press GO + relay Proška" human bus. Make the loop run
itself until a goal set closes, with the human touched only for genuine math
red-line calls.

---

## 0. The system that already exists (Route B)

**Working directory (source of truth):**
`full/q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/` (~447 files).
On `rh_clean` the prefix is `q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/`.
"Lamport" = it is deliberately a distributed-style message bus.

**Flat mirror for Proška:** `docs/routeB_bus/` — a one-level copy of the
Proška-relevant files, so Proška reads them herself through the GitHub connector.

**Message protocol (the bus):**
- `NNN_<name>.goal.md` — a goal posted by the dispatcher.
- `NNN_<name>.answer.md` — Proška's verdict. First line `# STATUS: ...`, then a
  machine-readable code block (bus automation parses it): `PROVED` / `KILL` /
  `INCONCLUSIVE` / `CHALLENGER` / `BUS_010_VOID` / scope + verifier tags.
- Goals 001..034 cycled; **034 `tooth_sign` is the current OPEN front** (goal posted,
  no answer yet). `RESULT.md` = `RIEMANN_BOUNDARY_CELL_BRIDGE_PROVED`.

**Roles already defined and running** (visible in the goal 034 header):
- **Dispatcher** — posts goals.
- **Codex** — assembles goal formulations from prior inputs; writes certificate
  scripts; has its own browser pane + a persistent long-running goal ("runs for days").
- **Aristotle** — the Lean bridge (`aristotle_bridge/`, `ARISTOTLE_TASK_*.md`).
- **Proška / judge** — adjudicates (ChatGPT Pro, browser-only); on conflict the
  judge has priority over Mythos. System prompt: `PROSHKA_SYSTEM_PROMPT_v2.md`
  (adversarial judge; kill or repair; numerics are evidence not quantifiers).
- **Mythos / Fable** — solver/decider; runs the KERNEL-9 + FAST-PATH + INTERNAL-TRIAD
  math protocol. Solver and judge prompts are near-mirrors (player vs judge — K1
  "build the judge before the player").

**Outbound to Proška is ALREADY automated:** `sync_proshka_github_channel.py`
refreshes the mirror, rebuilds `MANIFEST.md` (sha256 per file), commits **only**
`docs/routeB_bus/`, and pushes. Goal 014 = `PROSHKA_CHANNEL_LIVE`. Manual zips to
Proška are gone.

**Per-goal artifacts:** `<goal>_certificate.py` + `check_<goal>.py` + `*_CERT.json`,
`*_PROBE.{md,csv}`, `proshka/*` directives/verdicts.

**Guards baked into the bus (must be preserved):** `BUS_010_VOID` (bus 010 stays
void unless the owner creates it); scope tags (`ABSTRACT|FINITE_CELL|COFINAL_FAMILY`);
verifier tags (`LEAN|ARB_INTERVAL|PAPER|CONDITIONAL`); source-hash locks; "no RH
overclaim from an intermediate goal"; only ever touch `docs/routeB_bus/`; no new
branches/worktrees; no force-push; `PASS` only from lower envelope `L>=0`, `KILL`
only from upper envelope `U<0`.

---

## 1. Where Ylsha is still the slave — exactly two gaps

Everything else (outbound channel, checkers, Codex long-goal, Aristotle, Codex's
browser for downloads) is already autonomous. Two things are not:

1. **The dispatcher LOOP is manual.** Ylsha sequences by hand: pick next goal → have
   Codex assemble it → run `check_*.py` → run Aristotle → integrate → sync/commit/push
   → pick next. Every step is a capable agent; he is the GO-sequencer between them.
2. **The Proška INBOUND relay is manual.** Proška reads context from GitHub
   (automated), but her verdict lives in the browser chat, and Ylsha copies it into
   `NNN_<name>.answer.md` and commits. The answer never returns to the bus by itself.

The conductor targets exactly these two.

---

## 2. The conductor — one agent loop over the existing bus

**Where it lives:** on the **Mac**, as a Claude Code CLI agent (Fable/Mythos) on a
timer (`/schedule` or cron), plus **Co-Work** as the Proška relay worker (Ylsha's
choice). This Linux box can author the code; it cannot run the live loop (mirror
only, no browser Proška here).

**State is derived from the filesystem** (idempotent — a crash resumes from files).
For the current/next goal `NNN`, compute its phase:

| Phase | Condition | Owner |
|---|---|---|
| `AWAITING_FORMULATION` | prev goal closed, next `.goal.md` not yet drafted | Codex (dispatcher) |
| `AWAITING_PROSKA` | `.goal.md` exists, no `.answer.md` | **Co-Work relay** |
| `AWAITING_VERIFY` | `.answer.md` exists, cert/Lean not yet green | Codex + Aristotle |
| `CLOSED` | answer + `check_*.py` pass + integrated + mirrored | conductor → next |

### Cycle

1. **SENSE** — scan the working dir; classify the goal's phase; read the verdict
   codes if an answer exists. Termination check: if a goal's answer is a decisive
   `PROVED`/`KILL` that closes the tracked Route B target (owner-defined, NOT the
   conductor's call), stop and alert Ylsha — never auto-escalate an RH claim.
2. **ROUTE** by phase (table above).
3. **ACT** (non-blocking where possible):
   - `AWAITING_FORMULATION` → Codex assembles the next `NNN.goal.md` from the named
     prior inputs (as goal 034 was "assembled by Codex from inputs 031 and 033").
     Conductor may sanity-check the statement, but **the judge has priority** and
     math content is never invented by the conductor.
   - `AWAITING_PROSKA` → (a) run `sync_proshka_github_channel.py` so the GitHub mirror
     is fresh; (b) hand the goal to the **Co-Work relay** (§3); (c) sleep — do not block.
   - `AWAITING_VERIFY` → run `<goal>_certificate.py` + `check_<goal>.py`; run the
     Aristotle contract in `aristotle_bridge/` if a Lean obligation exists; scan Lean
     output for `sorry|exact?|admit`; on green, integrate. **Adversarial gate**
     before accepting a `PROVED`: a Codex/panel skeptic re-checks that the certificate
     really certifies the claimed statement and the guards (scope, no-overclaim) hold.
   - `CLOSED` → run the CHANNEL_RULE handoff: `sync_proshka_github_channel.py` →
     rebuild `MANIFEST.md` → commit **only** `docs/routeB_bus/` → push `rh_clean`.
     Advance to the next goal.
4. **CHECKPOINT + SLEEP** — write a cycle snapshot + log line; schedule the next
   wakeup. Event-driven and slow: Proška and Aristotle take minutes–hours, so the
   shape is "do all local work → push to Proška → sleep long → wake to harvest".
   Codex runs its own persistent-goal loop in parallel meanwhile.

---

## 3. The Proška relay via Co-Work (the one new capability)

This is the only genuinely new automation. Co-Work runs on the Mac with full
Mac + browser access — driving a browser chat is literally its purpose.

> **PREREQUISITE — Co-Work must have the actual repo connected via "Add folder",
> NOT a cloud Project.** Lesson from the goal-034 run (Co-Work session "Proshka
> pole subtraction", Fable 5 Max, 2026-07-29): the task was attached to the cloud
> **Project `RH_2026_06`**, not to the `chen_q3` git folder. So the agent ran
> **blind to the bus** — it could not read the real artifacts (031/027/033, hashes,
> the `routeB_lamport_rh_closure/` working dir) or write into the bus. It did honest
> sandbox work (paper reduction 034-R + a 26/26 standalone checker + emitted Aristotle
> tasks) and saved **6 files into the Project `claude/` workspace + Google Drive**,
> then asked to "Add folder". Repo-dependent plants were EMITTED, not run
> (P1/P5/P7-backend), and it warned that consumption in the repo may surface
> `SCALED_EDGE_OBJECT_MISMATCH` (unverified hashes 030/031/033, scope 027). It also
> re-derived everything cold (one "Go" timed out; the run was slow) precisely because
> no repo state was there to reuse.
>
> So: a cloud Project as Co-Work context = a blind sandbox that produces stranded
> files. For the relay (and for any repo-wired Co-Work run) the chen_q3 folder MUST
> be connected via **Add folder** in the desktop app, so Co-Work reads
> `docs/routeB_bus/` + the working dir and writes the answer straight into the bus.
> Without it, its output has to be hand-carried into the repo — the exact manual
> relay pain we are removing.

**Decoupled via the blackboard (same pattern as the rest of the bus):**
- When the conductor sets a goal to `AWAITING_PROSKA`, it drops a relay request into
  a `proshka_relay/inbox/NNN.request.md` (goal id + the minimal ask).
- **Co-Work** watches `proshka_relay/inbox/` (standing instruction or short schedule).
  For each request it:
  1. opens the Proška chat,
  2. sends the tiny trigger: *"GO — read goal NNN from `docs/routeB_bus/` on GitHub
     (rh_clean) and post your verdict per `PROSHKA_SYSTEM_PROMPT_v2.md`."*
     (Context is already on GitHub, so this is a trigger + scrape, NOT a paste of
     material — that is what makes it robust.)
  3. waits for the verdict (minutes),
  4. scrapes the verdict text,
  5. writes it verbatim to `NNN_<name>.answer.md` in the working dir,
  6. commits + lets the conductor pick it up; clears the inbox flag.

**Why this respects the red line:** the relay moves **Proška's own verdict** into a
file. No weaker-than-Pro model decides math architecture — Proška is still the judge,
Mythos still decides. Automating the *delivery* of her verdict is transport, not
adjudication.

**Fallback (`one-GO + watcher`):** if the Mac is asleep or the Proška session has
expired, the conductor pings Ylsha with the goal link; he clicks **one** GO in the
browser; a watcher detects the new verdict and files it. Bulletproof, no ToS-grey,
minimal human touch. Keep this as the automatic degradation path when Co-Work can't act.

---

## 4. Guardrails (unattended safety)

- **Red line:** the conductor never decides or drafts math architecture. Judge =
  Proška (Pro); decider = Mythos; Codex only assembles/implements. No substitute
  mathematician (rejected 2026-07-30).
- **Push scope:** auto-push is limited to `docs/routeB_bus/` per CHANNEL_RULE / goal
  014 (the bus's own designed behaviour). Any push touching Lean / the working dir
  beyond the mirror needs explicit Ylsha approval. No force-push, no new branches/
  worktrees, only touch `docs/routeB_bus/` for the mirror.
- **Adversarial gate** before any `PROVED` is accepted into the chain (§2.3).
- **Guards from the goal files are enforced, not re-interpreted:** `BUS_010_VOID`,
  scope tags, source-hash locks, "no RH overclaim from an intermediate goal".
- **Spend caps:** max Codex cycles / Aristotle jobs / tokens per night; log any cap
  hit (no silent truncation).
- **Fail-closed on ambiguity:** unclear frontier, uncertain hole-freeness, or a
  verdict the parser can't classify → escalate to Ylsha, do not guess.
- **Retained reasoning** (principle): the bus already persists rationale
  (`proshka/*`, `D0_*` decomposition contracts, `*_DIRECTIVE.md`); keep feeding them
  so each cycle does not re-derive cold. Run Codex via its own harness (retains
  reasoning + compaction), not a stateless call. Do not hand-truncate context;
  summarize.

---

## 5. Build order (deferred until Ylsha says go, and run on the Mac)

1. **Read-only conductor (dry-run):** on the Mac, a single-cycle script that SENSEs
   the current goal's phase and prints the plan + the next action — no dispatch, no
   push. Validate the phase detection against the real working dir.
2. **Local lane:** wire `AWAITING_VERIFY` (run `check_*.py`, Aristotle, adversarial
   gate) and `CLOSED` (CHANNEL_RULE handoff). Still no Proška.
3. **Co-Work relay:** implement the `proshka_relay/` handshake + the Co-Work standing
   instruction; test on one live goal end-to-end (034), with Ylsha watching.
4. **Formulation lane:** let Codex assemble the next `.goal.md` (dispatcher role).
5. **Timer + fallback:** put the conductor on a schedule; wire the `one-GO + watcher`
   degradation path. Only now is it truly unattended.

Ship autonomy one lane at a time; never all at once. Every lane logs what it did and
what (if anything) it capped or skipped.

---

## 6. Open items

- Exact working-dir path differs by branch (`full/…` on main vs `q3.lean.aristotle/…`
  on rh_clean) — pin the canonical path on the Mac.
- Where the conductor + `proshka_relay/` live relative to the bus (inside the working
  dir vs a sibling `orchestrator/`), so the mirror rule (`only docs/routeB_bus/`) is
  not violated by conductor state files.
- Co-Work trigger mechanism: standing watch vs short schedule vs conductor-invoked.
- Verdict parser: formalize the `# STATUS:` + code-block grammar the answers already
  use, so the conductor classifies verdicts deterministically.
