# ORG UPDATE — CONDUCTOR ROLE RETIRED, CODEX ABSORBS TRANSPORT

Date: 2026-07-30
Decision by: owner (Ылша), verbal, relayed to Mythos in chat
Materialized by: Mythos (owner decisions go to disk)

## Decision

The conductor role is retired, effective immediately. Codex absorbs the conductor's
transport and repository duties. Nobody re-litigates past conductor artifacts; history
is not rewritten.

## New duty map

- Mythos (unchanged): issues NNN_*.goal.md on the bus; writes directives/notes in
  proshka/; scores predictions; keeps the front map; does not execute, does not judge.
- Codex (extended): everything it did before (answers, code, certificates, ledgers,
  ROUTE_B_STATE last-step updates) PLUS git commit and push, mirror docs/routeB_bus/
  rebuild, MANIFEST refresh, SUPERSEDED/status markings on bus artifacts, and
  materialization of operational audits.
- Ылша (owner): relays Proshka in both directions (she still reads GitHub herself and
  answers in chat only); submits Aristotle contracts via browser when the cloud queue is
  unlocked; last word on everything.
- Proshka (unchanged): judge; no write access; reads the rh_clean mirror; verdicts are
  extracted from chat by the owner and materialized by Mythos in proshka/.

## Rules retained

- Force-push forbidden; merging rh_clean into main forbidden.
- Canon + mirror travel in one commit (transaction).
- Mythos write zone unchanged: NNN_*.goal.md + proshka/ only; Mythos never touches
  *.answer.md, code, or git.
- Goal numbers reserved by Mythos are not taken by anyone else.
- BUS_010 stays VOID until the owner explicitly creates it.
- Markers in Mythos chat output remain: [→CODEX] [→PROSHKA] [→YLSHA] [→WAIT].
  [→ARISTOTLE] is dormant while the cloud queue is locked; the submission path after
  conductor retirement is: Mythos writes the contract file, owner submits via browser.

## Rules void

- "Only the conductor commits and pushes" — void; Codex commits and pushes.
- Conductor-only mirror ownership — void; mirror is Codex's.

## New rule (from today's cross-channel miss)

CROSS_CHANNEL_SELF_CONTAINMENT: any brief leaving this workspace (to Proshka, to
Aristotle, to anyone external) must be self-contained — full paths, inline hashes,
explicit branch; no references like "see above" that point into a chat the recipient
cannot see. Violation class: K3 transfer-audit failure.

## Immediate consequence

Pending conductor tasks are reassigned to Codex via Goal 041
(041_conductor_handover_and_mirror_sync.goal.md).
