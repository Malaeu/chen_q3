# Q3 Claude executor bootstrap

Canonical executor behavior: `docs/CODEX_CONTROL.md`.

Read it completely, then enter through `SESSION_ENTRY.md`. This file is a thin
pointer only and contains no independent executor policy. If the canonical
control is unavailable, ambiguous, non-`ACTIVE`, or fails strict Spine
validation, stop with `CODEX_CONTROL_UNAVAILABLE_OR_AMBIGUOUS`.

## Карта проекта — читать при входе

```
docs/Progress_Log.md             развилки: что происходило и ПОЧЕМУ
docs/GENEALOGY.md                откуда взялась каждая линия (A / PSD / Route B)
docs/cartographer/TOOLS.yaml     реестр инструментов: включено / снято / сломано
docs/RECORDING_RULES.md          как писать: 4 правила, 8 граф записи
docs/GLOSSARY.md                 словарь обозначений для не-математика
docs/cartographer/brief.py       состояние графа из базы   (python3)
docs/cartographer/cheap.py       очередь незакрытых шагов по цене
```

Правило реестра: инструмент без записи в `TOOLS.yaml` считается несуществующим.
Правило записи: развилку писать в момент выбора, не постфактум.

## Phase, then batch — how the four of us divide the work

We enter a phase and grind it ourselves. Whatever hits a dead end or cannot be checked from
here is **not sent off one at a time** — it accumulates in `docs/routeB_bus/PROSHKA_QUEUE.md`
until two to four questions have gathered that genuinely block progress. Then one batch goes.

Proshka spends twenty minutes or more on a batch and answers with an adjudication rather than
a reply. Four related questions in one batch produce a verdict that moves the front; four
separate batches produce four answers we then have to stitch together ourselves.

Who gets what:

| Channel | What it is for | What it costs |
|---|---|---|
| **us** | disk checks, the base, literature retrieval, numerical probes, mechanics, bugs | seconds — so anything answerable here must never be delegated |
| **Proshka** | adjudication, kills, reading primary sources we do not have, architectural forks, kill-passes on our own construction | 20+ min per batch — hence cumulative |
| **Mythos** | reconnaissance, idea generation, zoomed maps | real money — spend on breadth, not on lookups |
| **Codex** | Lean | one live transaction at a time |

**Claims about a primary source get checked first** — `./ask.sh`, the literature review, a
search. Only what survives as genuinely unverifiable is written into an artifact marked
`relay, не верифицировано`, is **never used as a premise of an inference**, and goes into the
queue as a candidate for the next batch.

That last rule exists because on 7 August two relayed claims were repeated by me as premises
and both turned out false — that `δ_N(ξ)=1` is an L² normalization, and that the numerator
carries the prolate deficit's rate. Disk checks I ran and they held; claims about a paper we
cannot read I could not run, and I did not mark them hard enough.

## Anything that looks odd gets written down before it is explained

A number that sits where you did not expect it, a function that is flatter than it should
be, a check that passes for the wrong-looking reason — **write it into the working journal
at the moment you notice it**, with what you think it might mean and what would settle it.
Not after the run finishes, not once you understand it.

Two reasons. An observation held only in conversation is lost at the next context boundary,
and the one thing worse than a wrong explanation is a forgotten symptom. And writing it down
forces the question "what outcome would distinguish my two readings of this?" — which is
usually cheaper to answer than the thing being computed.

Phase 0 produced three of these: the removable 0/0 at r = B that silently poisoned every
early run, the "conditional convergence" claim that the exact kernel later refuted, and
psi_arch coming out nearly constant. The first two were noticed, not written, and cost a
rerun each. The third was written immediately — see PHASE0_RESULTS_2026-08-07.md R5 — with
both readings and the discriminating outcome stated before the number arrived.

## A bug found is a bug fixed first

When a defect surfaces during other work — a tool that lies, a check that cannot pass, a
status field contradicting its own file — **fix and verify it before returning to the
mathematics or to the conversation**. Do not file it and move on: a filed defect is a defect
that keeps producing wrong answers while everyone reads around it.

The three false greens of 6 August each survived weeks precisely because they were noticed
and postponed: `routeb_status.py --check` printing OK against a frozen bus,
`P9_STRICT_PASS` named for a strictness it does not add, and a verify in
`IMPLEMENTATION_PLAN.md` that cannot pass by construction. Every one of them was cheap to
repair and expensive to leave.

If the defect is in a file held under someone else's write lock, the fix does not stop —
it moves: write it into `docs/Codex/TASK_*.md` with the reproduction, and say so.

## Ask the shelf first

Before saying "we do not have this", before an external search, and before creating
anything new: **`./ask.sh <term>`**. One entry point over every store we keep —
`knowledge.db`, the literature review, Lean declarations, the specs. It prints
`НЕ НАЙДЕНО НИГДЕ` with the list of stores it checked when the thing genuinely is not here,
so "we do not have it" becomes a checked statement rather than a guess.

This exists because on 6–7 August the same failure repeated three times in two days: the
instrument existed, the knowledge sat inside it, nobody looked. `H2aPenaltyCoercivity.lean`
was absent from the map; `kb_migrate_verdicts.py` was written and never triggered; a paper
was fetched, filed and flagged in the litreview while we went to search for it on the web.
The cause is not forgetfulness — it is four stores with four different commands, where
asking one and finding nothing reads as "nowhere".

Linux-body hand-off and repository-map references:

- `docs/Codex/README.md`
- `docs/Codex/TASK_2026-08-06_07.md`
- `specs_docs/ENTRY_SPEC.md`
- `specs_docs/TOOLS_SPEC.md`

The linked documents carry the mechanics and current work order; this bootstrap
remains a pointer and does not duplicate them.
