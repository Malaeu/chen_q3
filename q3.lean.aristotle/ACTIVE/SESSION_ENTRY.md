# Session Entry (2026-03-08)

Это главный session-entry файл для Q3. Начинать новую сессию надо с чтения
именно его.

## Кто мы и что делаем

Мы ведём один проект:

- `/Users/emalam/Documents/GitHub/rh_lean_01_2026`

Цель сейчас не “заявить доказательство RH”, а максимально быстро двигать
вперёд **правдоподобный и математически честный route** внутри Q3:
текст, Lean, control-plane и embeddings должны оставаться синхронными.

## Обязательный read order

1. `SESSION_ENTRY.md`
2. `q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`
3. `IMPLEMENTATION_PLAN.md`
4. `q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md`
5. `q3.lean.aristotle/docs/INSIGHTS.md`

Если работаешь с embeddings / incoming notes, потом ещё:

6. `q3.lean.aristotle/docs/EMBEDDING_INGEST_WORKFLOW.md`

Если работаешь с Aristotle:

6. `q3.lean.aristotle/ACTIVE/aristotle/ARISTOTLE_WORKFLOW.md`
7. `q3.lean.aristotle/aristotle_input/ARISTOTLE_PROMPT_GUIDELINES.md`

## Текущий public mainline

Текущий публичный маршрут проекта:

`T0-pd -> H-bridge -> H4 -> RH`

Где

- `H-bridge` = Suzuki/Yoshida generalized form-pair bridge
  `H1 -> H2 -> H3 -> H4`;
- `H1` = построить `S_{a,M}` и `J_a` так, чтобы strongest finite Q3 block
  `T_M[P_A]-T_P^{(M)}` pulled back to the Suzuki operator side as a
  generalized form pair;
- preferred first-pass candidate for `H1`:
  filtered Volterra bridge with
  `J_a=(I_0^{(a)})^*I_0^{(a)}`,
  `I_0^{(a)}S_{a,M}=U_a M_{1+z}|_{P_M}`,
  and pullback metric
  `B_M=S_{a,M}^*J_aS_{a,M}=T_M[|1+z|^2]`;
- semilocal cyclic/Jacobi machinery stays useful, but only as a secondary
  basis/Gram supplier for `H1`, not as a new RH endgame.

Точный theorem stack, который сейчас заморожен как primary live route:

- `H1` exact/asymptotic pair-intertwining
- `H2` Galerkin / recovery on the generalized pair
- `H3` kernel-exclusion transfer
- `H4` RH via Suzuki Theorem 1.4

Что сейчас не является public mainline:

- `S1/S2/S3/S4` — правильный, но diagnostic-only compact-truncation package;
- `PSD-pd` — честный fallback Weil-side route, если `H1` stalled.

## Самые важные правила мышления

1. Не чинить то, что уже переведено в background-only.
2. Не возвращать broad-cone `W_K / W` как публичный RH-contract.
3. Не притворяться, что проект уже замкнут.
4. Не открывать новый архитектурный pivot без явного theorem memo и sync в control docs.
5. Самый быстрый путь — тот, который:
   - математически честен,
   - повторно использует уже доказанные модули,
   - не плодит новые необязательные слои.

## Что сейчас source of truth

При конфликте файлов порядок такой:

1. `q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`
2. `q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md`
3. `IMPLEMENTATION_PLAN.md`
4. `q3.lean.aristotle/docs/INSIGHTS.md`

Коротко:

- orchestrator решает frontier и gate-state;
- tracker решает paper typing / theorem map;
- implementation plan решает ровно текущую очередь;
- insights ничего не переопределяет.

## Как работать по сессии

### Если задача математическая / theorem-level

1. Прочитать `PROJECT_ORCHESTRATOR.md`.
2. Найти active gate в `IMPLEMENTATION_PLAN.md`.
3. Проверить, не решён ли уже этот кусок в `docs/INSIGHTS.md` или `docs/insights/`.
4. Только потом писать новый theorem note / manuscript patch / Lean patch.
5. После значимого шага:
   - `lake env lean Q3/Main.lean`
   - `#print axioms Q3.Main.RH_of_Weil_and_Q3`
   - если менялся paper: `latexmk -pdf full/RH_Q3.tex`

### Если задача про incoming notes / embeddings

Сначала проверь статус inbox:

```bash
cd /Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle
./scripts/ingest_incoming_notes.py status
```

Если inbox пуст:
- ничего не инжестить;
- это значит, что raw inbox уже разобран или заархивирован;
- ждём новый материал.

Если inbox не пуст, canonical loop такой:

```bash
./scripts/ingest_incoming_notes.py prepare docs/incoming_notes/<file-or-zip>
python3 -u ./scripts/refresh_q3_docs.py
python3 -u ./scripts/research_oracle.py query "<query>" -c q3_docs -n 5
```

Но важно:

- raw никогда не идёт в embeddings напрямую;
- только reviewed note с
  - `review status: reviewed`
  - `safe for embeddings: yes`
- после review raw уходит в archive, не удаляется.

Для этого есть локальный skill:

- `/Users/emalam/.codex/skills/q3-note-ingest/SKILL.md`

## Repo map (только живой минимум)

### Control plane

- `q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`
- `IMPLEMENTATION_PLAN.md`
- `q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md`
- `q3.lean.aristotle/docs/INSIGHTS.md`

### Manuscript

- `full/RH_Q3.tex`
- `full/sections/Main_closure.tex`
- `full/sections/Weil_pack.tex`
- `full/sections/Weil_linkage.tex`
- `full/sections/Notation/qstar_contract.tex`
- `full/sections/A1prime.tex`

### Lean entry

- `q3.lean.aristotle/Q3/Main.lean`

### Active pipeline / KB

- `q3.lean.aristotle/ACTIVE/KNOWLEDGE_BASE.md`
- `q3.lean.aristotle/docs/EMBEDDING_INGEST_WORKFLOW.md`
- `q3.lean.aristotle/scripts/ingest_incoming_notes.py`
- `q3.lean.aristotle/scripts/refresh_q3_docs.py`
- `q3.lean.aristotle/scripts/research_oracle.py`

## Проверки, которые надо помнить

### Lean

```bash
cd /Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle
lake env lean Q3/Main.lean
printf 'import Q3.Main\n#print axioms Q3.Main.RH_of_Weil_and_Q3\n' | lake env lean --stdin
```

Ожидаемый current profile:

- `propext`
- `Classical.choice`
- `Quot.sound`
- `Q3.Weil_criterion`
- `Q3.prime_term_le_at_t_critical_axiom`

### TeX

```bash
cd /Users/emalam/Documents/GitHub/rh_lean_01_2026/full
latexmk -pdf RH_Q3.tex
```

### Embeddings

```bash
cd /Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle
./scripts/ingest_incoming_notes.py status
python3 -u ./scripts/refresh_q3_docs.py
python3 -u ./scripts/research_oracle.py query "<query>" -c q3_docs -n 5
```

## Что не делать

- Не опираться на старый broad-cone route как на public RH contract.
- Не возвращать в mainline T5/Acceptance/legacy status narratives.
- Не засовывать raw chats или zip extracts напрямую в `q3_docs`.
- Не создавать новый архитектурный pivot без sync в manuscript + control plane.
- Не коммитить skill-файлы из `~/.codex/skills` в repo.

## Текущий практический next step

Если нет нового user redirect, текущий честный frontier такой:

- candidate construction of `S_{a,M}` and `J_a` in RKHS/Gram language;
- filtered Volterra refinement of that candidate:
  `J_a=(I_0^{(a)})^*I_0^{(a)}`,
  `I_0^{(a)}S_{a,M}=U_a M_{1+z}|_{P_M}`,
  `B_M=T_M[|1+z|^2]\le 4I`,
  and the next exact target becomes
  `S_{a,M}^*G_g[a]S_{a,M}=\kappa(a)Q_M+F_{a,M}`;
- semilocal-assisted refinement after that:
  finite-prime packet states `\eta_m^{(S,a)}`, Gram matrix
  `\Gamma_{a,M}^{(S)}`, and normalized synthesis
  `\widetilde S_{a,M}^{(S)}`;
- затем exact matrix-element comparison for
  `S_{a,M}^* G_g[a] S_{a,M}` against `\kappa(a)(T_M[P_A]-T_P^{(M)})`;
- packet route держать как fallback verification layer;
- compact scalar package держать только как diagnostic reduction;
- incoming notes прогонять через `q3-note-ingest` и не путать historical memos с live source of truth.
