# DRAFT [→CODEX] — RH_PROVEN_RENAME: снять мину самообмана в именах (M4; ваш же диагноз §0.1)

```yaml
STATUS: DRAFT   # исполнять только после per-action OK владельца
CLASS: LEAN_RENAME_ONLY / NO_NEW_MATH / NO_PROOF_BODY_CHANGES
BRANCH: rh_clean
TIP_AT_DRAFT: d78a18e   # переприннить fresh HEAD при старте
SOURCE_AUDIT: claude/MYTHOS_REPO_AUDIT_chen_q3_rh_clean_2026-08-27.md (находка M4)
STANDING_MANDATE: это НЕ новая идея аудита — это ваш собственный неисполненный долг:
  q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/STRATEGIC_CONTEXT.md:117
  («Имя RH_proven_clean — мина самообмана», §0.1 rename / docstring warning) и :237.
  Правило «Найденный баг чинится первым» (CLAUDE.md) здесь нарушено с той эры.
W9: CLOSES [M4_NAMING_MINE_RH_PROVEN, STRATEGIC_CONTEXT_0_1_DEBT]; OPENS []
```

## Мотив

Grep внешнего читателя (рецензент, журналист, чужая модель) находит
`theorem RH_proven : Q3.RH` за секунду — и вся честная архитектура проекта
(NOT_RH, PX_RH_CLAIM, вердикты) обесценивается одним легаси-именем.
`RH_proven` висит на аксиомах (`Q3.Weil_criterion`,
`prime_term_le_at_t_critical_axiom`); `RH_proven_clean` по вашему же
STRATEGIC_CONTEXT зависела от `sorryAx` — «proven» с sorry в зависимостях.
Докстринги честные, но grep читает имена, не докстринги. Прецедент политики:
ложный hole-marker от слова «admitted» → правило «писать ratified».

## Полная инвентаризация вхождений (git grep @ d78a18e, вне archive)

### Lean-декларации (4 сайта)

| Файл | Строка | Имя | В сборке? |
|---|---|---|---|
| `q3.lean.aristotle/Q3/MainTheorems.lean` | 53 | `RH_proven` | ДА (lean_lib Q3, globs ["Q3"], defaultTargets) |
| `q3.lean.aristotle/Q3/Clean/MainClean.lean` | 48 | `RH_proven_clean` | ДА (внутри Q3-глоба); STRATEGIC_CONTEXT:88 утверждал «не компилируется» — ПРОВЕРИТЬ фактически |
| `q3.lean.aristotle/MainTheorems.lean` | 46 | `RH_proven` | НЕТ по lakefile.toml (корневой дубль вне Q3-глоба) — подтвердить |
| `q3.lean.aristotle/Clean/MainClean.lean` | 48 | `RH_proven_clean` | НЕТ (корневой дубль) — подтвердить |

### Ссылки в живых md (правка = append-only датированная пометка, не переписывание)

- `q3.lean.aristotle/ARCHITECTURE.md`: строки 8, 18
- `q3.lean.aristotle/ACTIVE/aristotle/ARISTOTLE_QUEUE.md`: строка 34
- `q3.lean.aristotle/ACTIVE/aristotle/queue/sorry_Q3_Clean_MainClean_lean/NODE_BRIEF.md`: строка 6

### НЕ трогать (история)

- `docs/Paper_RH/2025-12-19 19-11-7-Triangle_inequality_issue.md` (чат-экспорт)
- `q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/STRATEGIC_CONTEXT.md` (сам диагноз)
- всё под archive/

## Предлагаемые имена (выбор за владельцем; дефолт — ваш же §0.1)

1. `RH_proven` → `RH_of_tier1_axioms_legacy` (стиль честных имён цепи: `RH_of_…`).
2. `RH_proven_clean` → `RH_conditional_on_Gate_clean` — имя, предложенное вашим
   же STRATEGIC_CONTEXT:197; либо симметричное `RH_of_tier1_axioms_clean_legacy`.

Без deprecated-alias: цель — чтобы grep по дереву больше не находил теорему,
НАЗВАННУЮ «proven». В докстринг каждой добавить строку
«Renamed from RH_proven( _clean) 2026-08-27; conditional — see #print axioms.»

## Шаги

1. Переименовать 4 декларации + все внутрифайловые упоминания (`#print axioms`
   в комментариях/докстрингах тех же файлов).
2. `git grep -n "RH_proven"` → должны остаться ТОЛЬКО history-файлы из списка
   «НЕ трогать» и docstring-строки «Renamed from…».
3. В три живых md добавить датированную пометку в конце соответствующего блока:
   «2026-08-27: RH_proven→RH_of_tier1_axioms_legacy, RH_proven_clean→…» —
   append-only, по прецеденту коррекций 08-26.
4. Сборка: `lake build Q3` (и явная проверка, компилируется ли
   `Q3/Clean/MainClean.lean`; если STRATEGIC_CONTEXT:88 прав и файл битый —
   СТОП, отдельный отчёт владельцу: чинить или карантинить — не решать молча).
5. `#print axioms` переименованных теорем — список аксиом ДО = ПОСЛЕ (снять до
   переименования, сравнить).
6. Hole-scan (`q3_check`) — без новых совпадений.
7. Коммит-манифест владельцу (per-action OK), push после OK.

## Явные запреты

Тела доказательств не менять; аксиомы не добавлять/не удалять; корневые дубли
(`MainTheorems.lean`, `Clean/`) не УДАЛЯТЬ в этой транзакции (дедупликация —
отдельное решение владельца; здесь только rename для консистентности grep).
