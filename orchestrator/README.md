# RH Orchestrator — setup + operation (master guide)

Purpose: run the multi-agent RH (Riemann Hypothesis) loop **unattended** so Ylsha is
off the screen. Roles: **Codex** (CLI dispatcher/implementer) · **Proška** (ChatGPT
Pro judge) · **Mythos** (Fable 5 orchestrator-brain, writes the distribution) ·
**Aristotle** (Lean prover) · **conductor = Claude Code (Fable/Mythos), the transport**.

Proven live end-to-end on 2026-07-30 (Codex → Proška REPAIR_034 → Mythos distribution).
This guide is how to stand the environment up and run it.

> **WHERE IT RUNS:** in the canonical checkout on the host that owns the live bus.
> Resolve the checkout with `git rev-parse --show-toplevel`; the bus path below is
> repository-relative. Host-specific checkout locations belong in untracked local
> configuration, never in committed state.

---

## 1. Chrome setup (one-time)

1. Use your normal Chrome (keeps logins). Enable remote debugging:
   - Open `chrome://inspect/#remote-debugging` → tick **"Allow remote debugging for
     this browser instance"**. Confirm it says **`Server running at: 127.0.0.1:9222`**.
   - This toggle intentionally 404s the legacy `/json` HTTP endpoints and rejects raw
     WebSockets — that is expected. The sanctioned client is `chrome-devtools-mcp`.
2. Stay logged in on the agent sites:
   - **Proška** = ChatGPT Pro, project **RH_März_2026** (chatgpt.com). New chats there
     bootstrap the judge from `PROSHKA_SYSTEM_PROMPT_v2.md`. Do NOT use the superpowergpt
     `RH_solver` plugin persona — it's a solver, not the judge.
   - **Mythos** = claude.ai **Co-Work project RH_2026_06** (model Fable 5 Max). Its
     Instructions = the KERNEL prompt; it reads the verdict + writes the distribution.
   - **Aristotle** = `aristotle.harmonic.fun/dashboard` (for visibility; CLI is primary,
     see `ARISTOTLE.md`).
3. Open the agent tabs once (order/groups don't matter — `list_pages` sees them all).

## 2. MCP servers needed (Claude Code)

Essential — full browser visibility + control across ALL tabs/windows (dissolves the
claude-in-chrome tab-group limit):

```bash
claude mcp add chrome-devtools -s user -- npx -y chrome-devtools-mcp@latest --autoConnect
claude mcp list   # expect: chrome-devtools ... ✔ Connected
```
`--autoConnect` attaches to the toggle-enabled Chrome (Chrome 144+, stable channel
user-data-dir). If it fails to attach, fall back to
`--wsEndpoint ws://127.0.0.1:9222/devtools/browser/<id>` (id from
`<user-data-dir>/DevToolsActivePort`, line 2).

Useful (research / already present): `perplexity-ask`, `brave-search`, WebSearch,
`xapi` (X). `claude-in-chrome` is **no longer needed** — chrome-devtools-mcp supersedes it.

Codex CLI (dispatcher/implementer): `codex exec -m gpt-5.6-sol -c model_reasoning_effort=xhigh`.
Aristotle: `aristotlelib` in the repo `.venv` (see `ARISTOTLE.md`).

## 3. How the conductor operates (browser side)

- `list_pages` → match each agent by URL:
  - Proška: `chatgpt.com/g/g-p-...RH_März...`
  - Mythos: `claude.ai/cowork/project/019eb151-...` (or its spawned `claude.ai/chat/<id>`)
  - Aristotle dashboard: `aristotle.harmonic.fun/dashboard`
- `select_page {pageId}` → make it the active context.
- **Send a prompt**: `select_page`, then fill the composer + submit. Multi-line: set the
  visible composer, then Enter (single logical line) — see `CONDUCTOR.md` §relay.
- **Harvest reliably**: `evaluate_script` with `harvest_conversation.js` — fetches the
  conversation JSON from the app's own endpoint. This BYPASSES DOM virtualization
  (claude.ai/ChatGPT only mount a window of messages; DOM reads miss off-screen turns).
- **Detect completion**: `evaluate_script` with `detect_complete.js` (no streaming
  indicator + text stable). Proška runs for HOURS, Mythos minutes — poll, don't watch.

## 4. GitHub branch discipline (the K3 channel fix)

- Default branch is now **`rh_clean`** (set in repo Settings). This fixes the connector
  "landing in January `main`".
- In EVERY brief to Proška/Mythos, still write the branch explicitly — `branch rh_clean`
  — and give **full tree URLs**: `https://github.com/Malaeu/chen_q3/tree/rh_clean/docs/routeB_bus/...`.
- Do NOT force-push or merge `rh_clean` into `main` (January `main` carries old
  Linux-machine lanes). Keep them separate.

## 5. First run (do together at home, on the Mac)

1. `git fetch` + verify default branch, MCP `✔ Connected`, `list_pages` shows all agents.
2. Dry-run the conductor: SENSE only (list_pages + read the live bus state) → print the
   plan, no dispatch. Validate it identifies goal 034's REPAIR state + Mythos's distribution.
3. Execute Mythos's **ДЛЯ CODEX** block, ТАКТ 0 first (source-range verify of catch b).
4. Wire one full cycle with a human watching, then put it on a timer (`CONDUCTOR.md` §cadence).

Files: `CONDUCTOR.md` (design + state machine), `harvest_conversation.js`,
`detect_complete.js`, `ARISTOTLE.md`. Design rationale: `../ORCHESTRATION_DESIGN.md`.
