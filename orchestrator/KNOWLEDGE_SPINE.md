# KNOWLEDGE SPINE — единый механизм памяти проекта

Date: 2026-07-31 · Owner zone: executor (`orchestrator/`) · Status: v2, live

Задача: у проекта ≥13 поверхностей памяти (kills, стратегии, инсайты, трюки,
работа над ошибками), но они разрознены, частично протухли и не читаются перед
прыжком. Spine НЕ переписывает источники (зоны записи неприкосновенны) —
он агрегирует их adapter-паттерном (ScientistOne, §5: unify artifacts, then
audit) в один генерируемый вид.

## Механизм

```
sources (canonical, чужие зоны)          adapter (моя зона)         readers
─────────────────────────────────        ──────────────────         ───────
knowledge.db + canonical ledgers       ┐
sensor JSON + AUTOPSY wall map         │
observability.db + timing ledger       ├─→ orchestrator/spine.py ─→ SPINE_STATE.json
three behavior-control kernels         │      (sole entrypoint)   ├─→ SPINE_VIEW.md
phase-chat runtime + semantic plants   │                          └─→ META_CORPUS.json
arsenal + insights + bus M3 blocks     ┘
```

- `spine.py` запускается Codex/executor на session start, после каждого
  закрытого гола, после материализации вердикта и при site baton.
- `SPINE_STATE.json`, `SPINE_VIEW.md` и `META_CORPUS.json` — не источники
  истины, а машинный, человеческий и corpus-регистровый взгляды. Править только
  источники.
- Staleness warnings в шапке — это сигналы на обслуживание, не декорация:
  просроченный governor или неслитые M3-блоки = разомкнутая петля памяти.

## Роли и обязанности записи (без изменений зон)

| Слой | Канонический файл | Кто пишет | Когда |
|---|---|---|---|
| Object-kills | `ACTIVE/pipeline/FAILURE_ATLAS.json` | Codex | при route-kill с Lean-декларацией |
| Strategy-kills | `ACTIVE/FAILED_STRATEGIES.yaml` | Codex | при `EscapeLoop`/`RouteKill`; **соль из M3-блоков Прошки — переносить сюда** |
| M3 iteration blocks | вердикты на шине | Прошка | каждый вердикт (уже делает) |
| Process errors | `docs/ERRORS_DESTROYER.md` | любой + owner | после ошибки процесса |
| Trick cards (K9) | `q3.lean.aristotle/docs/ARSENAL_CARDS_v1.md` | Codex + Proshka | новый переносимый приём после проверки |
| Insights / деревья | `docs/INSIGHTS.md` | Codex/CC | по Branching Protocol |
| Aristotle failure harvest | answers на шине → M3/atlas | Codex | каждый ран, удачный или нет |

## Связь с синтезом (SYNTHESIS_JUMPS_COE_2026-07-31.md)

- SPINE_VIEW = материализация **SENSE LEDGER** (K10 draft): прыжок Mythos
  обязан якориться в зарегистрированной аномалии — теперь все аномалии в одном
  файле, а не в 13.
- Замыкание CoE-цепочки: `forbidden_future_move` из вердиктов теперь виден
  всем головам автоматически, а не тонет в истории шины.
- I1-аналог (score verification): staleness-таблица = проверка, что память
  вообще обновляется.

## P9 — active behavior control and bounded exploration

The behavior-control switch and full P4 One-Spine adapter are active. Exactly
one kernel per body is registered in
`orchestrator/BEHAVIOR_CONTROL_REGISTRY.json`; strict Spine validation rejects
missing, duplicate, ownerless, unwired or mirrored-drift controls.

```yaml
BEHAVIOR_CONTROL_P9:
  status: ACTIVE
  control: docs/CODEX_CONTROL.md
  trigger_owner: Codex
  trigger_events: [SESSION_START, GOAL_DISPATCH, GOAL_CLOSE,
                   DELEGATED_STRATEGIC_REVIEW, PX_RH_CLAIM, SITE_BATON]
  runtime: orchestrator/state/CHANNEL_RUNTIME.json
  runtime_writer: Codex
  durable_memory: q3.lean.aristotle/aristotle_db/knowledge.db
  spine_section: behavior_control_and_bounded_exploration
  fail_closed_code: EXPLORATION_CONTOUR_ORPHANED

  mathematical_authority:
    codex_proshka: ALL_EXCEPT_PX_RH_CLAIM
    owner_only: PX_RH_CLAIM
    forbidden: MATHEMATICAL_OWNER_DEFERRAL_OUTSIDE_PX_RH

  exploration_retention:
    active_runtime:
      candidates_max: 5
      cycle_summaries_max: 12
      latest_validated_delta_max: 1
      prior_close_summary_max: 1
    durable_close:
      journal_rows_per_episode: 1
      kind: exploration_close
      boundary: EXPERIMENTAL_NOT_PROMOTED
      links: [cites, applies_move, autopsy_of, same_source, supersedes]
    forbidden_durable_noise:
      - speculative_candidate_prose
      - raw_chat_transcript
      - repeated_builds
      - cosmetic_rewrites
      - unvalidated_hypotheses
```

`orchestrator/spine.py` validates the active control registry and runtime schema, then
renders one compact section: active exploration identity, gate, blocker,
candidate/cycle/review counters, selected route, rollback, latest validated
delta, operational pending state, and latest durable closeouts. It never
renders full brainstorm prose.

Closeout writes use exactly one transaction:

```bash
python3 orchestrator/kb.py record-exploration-close ...
```

The command inserts one `journal_entry`, optionally links it only to existing
durable records, and never overwrites kills, invents moves/walls, mutates the
schema, or records every cycle. Tests must redirect `Q3_KNOWLEDGE_DB_PATH` to a
temporary database; the production database is not a fixture.

## Database boundary — separation is intentional

There are four SQLite layers, not competing project memories:

| Database | Role | Spine treatment |
|---|---|---|
| `q3.lean.aristotle/aristotle_db/knowledge.db` | Canonical semantic project memory: kills, moves, dossiers, postmortems, exclusions, reviewed journal | Read-only adapter; compact semantic closeouts may be written only by the explicit `kb.py` transaction |
| `q3.lean.aristotle/aristotle_db/aristotle_proofs.db` | Proof/artifact inventory: documents, lemma status, specs, Aristotle provenance | Separate metadata index; never promoted to Lean/kernel truth |
| `q3.lean.aristotle/aristotle_db/observability.db` | Atomically rebuilt projection of holes, dependencies, taint, numeric checks and Proshka timing rows | Read-only summary; raw observations never become decisions or proof truth |
| `~/.codex/memories_1.sqlite` | Native Codex memory-generation jobs and local episodic recall | Machine-local runtime only; not a project source and not ingested wholesale |

`PROJECT_DATABASES_MUST_NOT_BE_MERGED`. A reviewed fact may cross a boundary only
through a named adapter with provenance. Spine is the read/view junction; it is
not a schema merge, a cross-database foreign-key graph, or a new truth source.

The observability adapter is `orchestrator/observability.py`; its birth
contract, trigger owner and existing gates are declared in
`orchestrator/OBSERVABILITY.md`. Only a reviewed belief-changing conclusion may
cross from observability into the compact `knowledge.db` journal.

Refresh only the event-scoped transaction. The direct sensor command remains
available for dry-run diagnosis:

```bash
python3 orchestrator/sensors.py refresh --dry-run
python3 orchestrator/spine.py --refresh --strict --reason step-close
python3 orchestrator/spine.py --refresh --strict --reason goal-close
python3 orchestrator/spine.py --refresh --strict --reason semantic-index-refresh
```

## Быстрый старт

```bash
python3 orchestrator/spine.py            # regenerate view
python3 orchestrator/spine.py --stdout   # print to terminal
python3 orchestrator/spine.py --strict --reason session-start --stdout
python3 orchestrator/spine.py --refresh --strict --reason step-close  # memory + stale-only q3_docs
python3 orchestrator/spine.py --refresh --strict --reason goal-close  # full transaction
```

The remaining degraded state is explicit rather than hidden: numeric checks
have zero configured coverage, legacy AUTOPSY lines are unclassified, and any
semantic-index plant failure is surfaced in `SPINE_STATE.json`.
