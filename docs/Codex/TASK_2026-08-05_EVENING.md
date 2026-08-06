# CODEX TASK — 2026-08-05 evening (Mac body)

Read this file first, then execute the tasks in order. Ask the owner for OK before each write,
as usual. Nothing here overrides Proshka's verdict of 2026-08-05.

## Standing constraints (unchanged, do not violate)

- `EXECUTION_AUTHORIZED_NOW: false`, `REPO_WRITE_AUTHORIZED_NOW: false`,
  `ARISTOTLE_AUTHORIZED: false` — these apply to the **G6/S2 mathematical front**.
  Task 1 and Task 3 below are procedural/infra and are explicitly permitted by the verdict's
  own procedural appendix ("P5 semantic-index infrastructure inside the ratified contour,
  owner-controlled execution, no separate mathematical verdict needed").
- `GOAL_055: HOLD` · `BUS_010: VOID` · G2/CCM frozen files untouched · no route promotion ·
  no RH claim · no Aristotle submission.
- Do **not** define canonical `Pstar` from PL2, do not transfer H2a/H2b between different `C`
  objects, do not call the 1468-window scan a cofinal theorem.

---

## Task 1 — fill the five Mac-only GAPS  (highest value, ~20 minutes)

File: `docs/CODEX_CYCLE_RECONSTRUCTION_2026-08-05.md`, section **§5 Mac-only GAPS**.

It was written from the Linux slice on 2026-08-05 and has not been touched since. Only your
machine can answer these. Write the answers **into §5**, replacing each bullet with the fact:

1. Your full `~/.codex/config.toml`: model, effort, approval mode, sandbox, projects, plugins,
   and especially **notify** — Linux has no native-notification hook and we cannot see whether
   you do. Also: is `chrome-devtools` MCP present, or replaced by the Codex.app embedded
   authenticated browser?
2. The desktop-driving stack: `osascript` / `cliclick` / Ghostty Accessibility — how do you
   actually drive Codex.app and Claude Desktop (clipboard paste, GUI automation, both)?
3. The auth pathway for Aristotle and ChatGPT: embedded logged-in session vs token file.
4. The **standing-goal / session-bootstrap contour** as you actually run it — the ~22h off-git
   artifact. We only have the owner-surfaced snapshot; write the authoritative version.
5. The **exact chat open/continue trigger** you use today. Write reality first; correcting it
   to one-living-chat-per-phase is a later step (P9), not this one.

Why it matters: P9 `CODEX_CONTROL.md` is supposed to codify how you really work. Written from
our guesses it would codify a fiction.

---

## Task 2 — the G2 owner fork: produce the certificate data

Node: `OWNER_FORK_G2_CCM_054_1_SEVEN_REPRESENTATIVE_RELATIVE_WR_INTEGRAL_ENCLOSURES`.
Proshka's authorization is `false` **pending owner-supplied data** — that data is what this
task produces. Computing it is not a Lean edit, not a bus write, not an Aristotle run.

Deliver **one** of the two forms she accepts, source-locked to the seven literal integrals and
the frozen final-entry orientation:

- **(A)** rational derivative and Taylor bounds for the removable extension, plus a rational
  quadrature partition with checked remainder bounds; or
- **(B)** a direct kernel-checkable whole-expression interval certificate whose verifier proves
  the seven relative inequalities without inventing component balls.

Either form must include: exact mode representative · exact change of variables · endpoint-limit
certificate · all interval boundaries and junctions · coverage-completeness proof · directed
rounding convention · lower and upper rational result · source and certificate hashes.

Hard prohibition from the verdict: **do not** derive an "integral interval" by subtracting
independently rounded component intervals from the final-entry JSON.

Deliverable: the data plus a short note on which form you chose and why. Show it to the owner;
do not submit anything to the bus.

---

## Task 3 — start using `knowledge.db` (built on Linux today, 2026-08-05)

Everything the project knows about *what was already tried, killed or proved* is now one
SQLite base with a CLI, instead of ~20 markdown journals in incompatible formats.

```bash
./orchestrator/kb.py ask "<term>"        # search kills + moves + journal + dossiers (~44 ms)
./orchestrator/kb.py list --unit-type wall
./orchestrator/kb.py excluded            # what was deliberately NOT migrated, and why
./orchestrator/kb.py census              # judge: sources vs rows, 0 drift expected
./orchestrator/kb.py add --unit-type route --subject "..." --reason "..." [--rollback-target ...]
```

Contents: 59 kills · 26 moves · 1784 journal entries · 168 dossiers · 1 postmortem ·
113 registered exclusions.

**What changes for you:**

- **Before creating any new object** (Lean file, Aristotle input, goal, brief) — run
  `kb.py ask` on its key terms. Today this exact gap cost us: `Gammaℝ` was already in Mathlib
  and `riemannXi_eq_completedRiemannZeta` already in `ClassicalXiInterface.lean`, and we nearly
  rewrote both.
- **New kills go through `kb.py add`**, not by editing the atlases. These five are FROZEN with
  banners: `ROUTE_KILL_REGISTRY.md`, `Q3_OBSTRUCTION_ATLAS.md`, `S5_FAILURE_ATLAS.md`,
  `FAILED_STRATEGIES.yaml`, `FAILURE_ATLAS.json`. Also frozen: `RH_TRICK_ATLAS.md`,
  `TRICKS_LIBRARY.md`, `ERRORS_DESTROYER.md`.
- **Keep writing normally** into `INSIGHTS.md`, `ARSENAL_CARDS_v1.md` and `docs/insights/` —
  these are marked MIRROR, not frozen, precisely so your loop is not broken. The base re-reads
  them; re-run `./orchestrator/kb_migrate_journal.py` (and `_dossiers`, `_moves`) on a phase
  boundary.

**If you disagree with any of this, say so instead of working around it** — the contour was
ratified by Proshka and Mythos, but neither of them writes Lean on your machine.

---

## Task 4 (optional, only if 1–3 are done and you are waiting)

`./orchestrator/kb.py excluded --klass unreviewed` lists 33 files nobody has read; 2 more are
`pending_read` verdicts whose KILL is stated only in prose. If you have idle time, read the
largest and either migrate the knowledge with `kb.py add` or record why it is not knowledge.

---

## Also worth knowing

Your system prompt for Proshka was out of sync: `docs/routeB_bus/PROSHKA_SYSTEM_PROMPT_v2.md`
was still the pre-arsenal version, missing the STANDING REPO FETCHES block — so she would never
have pulled `ARSENAL_CARDS_v1.md` or the mandate. Fixed 2026-08-05 (`5d85dabf`); all three
working copies are now byte-identical, the old text survives only as
`_backups/PROSHKA_SYSTEM_PROMPT_v2_working_2026-08-04_pre-arsenal.md`.
