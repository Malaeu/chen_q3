# RULE NAMING DISAMBIGUATION — label "Rule 0" retired
Date: 2026-07-31 · Author: Mythos (materialized by Codex; Filesystem bridge down)
Trigger: Proshka verdict GOAL_040_CORRECTIONS_RATIFIED_PENDING_PIN exposed a name
collision: the label "Rule 0" pointed at two different rule-objects in two channels.
No formulation was wrong; the LABEL was ambiguous (K3 transfer-audit class).

## Rule A — RULE_INVENTORY_FIRST (Aristotle usage protocol amendment)
Canonical texts (equivalence claimed between A1 and A2 ONLY):
A1 (Mythos): Before ANY run — not only deep runs — inventory the own repository and
pinned Mathlib. A run on an already-proved theorem is a protocol failure, not progress.
A2 (Proshka, 2026-07-30): "cloud search stops when an exact local theorem already
closes the interface"; it is forbidden to submit an Aristotle theorem already proved
in canon merely because the contract predates the local search result.
Scope: Aristotle/cloud submissions. Home: proshka/ARISTOTLE_PROTOCOL_MYTHOS_RATIFICATION.md
(its internal heading "Rule 0" is to be read as RULE_INVENTORY_FIRST; file text left
intact as history).

## Rule B — RULE_SEND_DISCIPLINE (control plane, dispatch of prepared texts)
Live formulation (owner channel, as quoted by Proshka 2026-07-31): "по умолчанию
сообщение агенту показывается владельцу, а не отправляется; прямое отправление
разрешено только после явного «отправь»; адресат и канал указываются однозначно."
Ratification criteria (Proshka, verbatim):
R0.1 DEFAULT_SHOW: подготовка текста не является разрешением на отправку.
R0.2 EXPLICIT_SEND_AUTHORITY: отправка разрешена только явной текущей командой
владельца; старое общее "go" или факт готовности goal не считается разрешением.
R0.3 RECIPIENT_AND_CHANNEL_LOCK: перед действием однозначно названы адресат и канал.
Adopted by Mythos immediately; compliance mapping:
- Marker blocks in Mythos chat output are PREPARED TEXTS shown to the owner (R0.1);
  nothing auto-sends.
- Dispatch happens only by the owner's explicit current action: launching Codex on a
  goal file (Codex, CLI), pasting a brief to Proshka (Proshka, browser), submitting an
  Aristotle contract (Aristotle, browser) — recipient and channel named (R0.2, R0.3).
- Goal files on the bus are preparation, not dispatch.

## Non-equivalence statement
Rule A and Rule B are DIFFERENT rules. No equivalence is claimed between them.
Ratification requests are separate: Rule A (A1 ≡ A2) and Rule B (live text ≡ R0.1–R0.3).

---
MATERIALIZATION NOTE (deviation, honest provenance): executed by conductor-CLI
(Claude Code, Linux) on the owner's direct order of 2026-07-31, because the owner
chose same-day execution; Codex was not invoked. Text above is verbatim from the
Mythos message; only this note is added.
