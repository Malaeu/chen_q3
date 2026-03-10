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
  `H1^f -> H2^f -> H3^f -> H4^f`;
- `H1^f` = filtered bulk bridge on the symmetric two-sided tail package, so
  that the strongest finite Q3 block is compared not to raw `Q_M`, but to the
  filtered tail section `\widetilde Q_{M,N}`; the exact identity is now treated
  as the zero-defect special case, while the live working theorem-shape is
  filtered intertwining modulo a joint finite-rank cap defect after the right
  joint basis / Gram projection;
- preferred first-pass candidate for `H1^f`:
  two-sided filtered Volterra bridge with
  `J_a=(I_0^{(a)})^*I_0^{(a)}`,
  tail model space `\mathcal P_{M,N}`,
  symmetric filtered shift `\Delta_{M,N}`,
  packet states `\phi_n^\pm[a]`,
  synthesis `S_{a,M,N}`,
  exact pullback metric
  `B_{M,N}=S_{a,M,N}^*J_aS_{a,M,N}=\Delta_{M,N}^*\Delta_{M,N}`,
  and preferred filtered bridge-object
  `\widetilde Q_{M,N}=\Delta_{M,N}^*Q_{M+1}\Delta_{M,N}`;
- semilocal cyclic/Jacobi machinery stays useful, but only as a secondary
  finite-prime basis/Gram supplier for `H1^f`, not as a new RH endgame.

Точный theorem stack, который сейчас заморожен как primary live route:

- `H1^f` filtered intertwining modulo finite-rank cap defect
- `H2^f` Suzuki tail/cap reduction
- `H3^f` filtered gap transfer
- `H4^f` RH via Suzuki Theorem 1.4

Что сейчас не является public mainline:

- `S1/S2/S3/S4` — правильный, но diagnostic-only compact-truncation package;
- `PSD-pd` — честный fallback Weil-side route, если `H1` stalled.

## Текущий практический next step

Если нет нового user redirect, текущий честный frontier такой:

- symmetric two-sided filtered H-bridge:
  `\mathcal P_{M,N}`, `\Delta_{M,N}`, `\phi_n^\pm[a]`, `S_{a,M,N}`,
  `B_{M,N}=\Delta_{M,N}^*\Delta_{M,N}`,
  `\widetilde Q_{M,N}=\Delta_{M,N}^*Q_{M+1}\Delta_{M,N}`;
- next live blocker:
  filtered bulk classifier on the two primary families `(+,+)` and `(+,-)`,
  with preferred theorem shape
  `M_{mn}^{\sigma\tau}(a)=\kappa(a)\widetilde q_{mn}^{\sigma\tau}+F_a^{\sigma\tau}`,
  where `F_a` is tested as a structured small-rank correction;
  the diagnostic classes are now
  `exact / exact+structured small-rank correction / dead`,
  and the current numerics strongly favor the middle class,
  where on the Section 8 side
  `Q_M^{raw}=T_M[P_A]-\Pi_M`,
  `\Pi_M=(2M+1)T_P^{Ray}(t,M)=\iota_M^*T_P^{Ray}(t)\iota_M`,
  and
  `q_{rs}=\langle Q_M^{raw} e_s,e_r\rangle
   =A_{r-s}-\sum \lambda_n e^{2\pi i(s-r)\xi_n}`,
  `\lambda_n=(2\Lambda(n)/\sqrt n)\Phi_{B,t}(\xi_n)`,
  with `\kappa_{A3}=1`,
  and
  `w_{rs}(a)=W(\chi_s[a]*\widetilde{\chi_r[a]})` on the Suzuki side;
- raw diagnostic layer:
  the raw identity `w_{rs}(a)=\kappa(a)q_{rs}` is rejected as an exact theorem
  shape, because the raw Q3 matrix is Toeplitz with constant diagonal while the
  Suzuki raw Weil matrix in the `\chi_n[a]` basis has diagonal growth of order
  `\log|n|`;
- derived filtered consequence:
  the remaining filtered blocks `M^{-+}, M^{--}` are obtained from
  `M^{++}, M^{+-}` by conjugation/self-adjoint symmetry;
- current numerical classifier verdict:
  filtered mismatch is compatible with small-rank structure but not with a
  purely low-mode-supported defect; in the canonical case
  `a=1.25, M=4, zeros=20`, the `++` residual has rank-2 relative residual
  `~6.32e-3` and the `+-` residual has rank-2 relative residual `~1.99e-3`,
  while low-mode union-mask residuals stay large
  (`++`: `~7.81e-1`, `~5.96e-1`, `~4.04e-1`;
   `+-`: `~9.97e-1`, `~9.85e-1`, `~9.32e-1`
   for unions of the first `1/2/3` rows-columns);
  the stronger cap-defect classifier now shows a sharper verdict:
  toy `M=2` runs are misleadingly tiny and give trivial rank-2 agreement,
  but on real bulk-size runs (`M>=3`) the `++` and `+-` defect spaces are only
  partially aligned, not identical; in the canonical case
  `a=1.25, M=4, zeros=20`, cross-family column/row alignment is only
  `~0.606 / ~0.606`, with transfer residual `++ -> +- ~2.69e-2` and reverse
  transfer `+- -> ++ ~6.79e-1`, so the current honest live verdict is
  `structured small-rank defect yes`, but `one obvious shared cap-space`
  not yet established at rank `2`;
  however, a stronger joint-basis test with `defect-rank=3` already looks much
  more promising: in the canonical run `a=1.25, M=4, zeros=20`, the shared
  cap-defect candidate gives `proj_rel_resid ~7.88e-3` for `++` and
  `~1.10e-3` for `+-`, and in the second real bulk-size run
  `a=1.0, M=4, zeros=20` it gives `~1.92e-2` for `++` and `~1.67e-3` for `+-`;
  on the canonical run the rank-`3` gap proxy is already nontrivial
  (`sigma_4/sigma_3 ~1.66e-1` for `++`, `~3.48e-1` for `+-`), and the shared
  projector keeps the third principal angle moderate rather than chaotic
  (`++`: `~26.1°/23.1°`, `+-`: `~17.6°/17.6°`);
  so the honest live freeze is now:
  filtered intertwining modulo joint finite-rank cap defect after the right
  basis / Gram projection, with working conjectural target `rank <= 3`;
- after the filtered bulk match:
  separate finite-dimensional Suzuki cap positivity;
- semilocal-assisted refinement after that:
  finite-prime packet states `\eta_m^{(S,a)}`, Gram matrix
  `\Gamma_{a,M}^{(S)}`, and normalized synthesis
  `\widetilde S_{a,M}^{(S)}` only as engineering support for the same `H1^f`.

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

## Правило для Прошки

Если готовим пакет для Прошки, не рассчитываем, что он будет читать наши
локальные `.tex` или произвольные text files как source of truth.

Правильный формат по умолчанию:

- один короткий self-contained markdown/prompt;
- все ключевые формулы, константы и target identity вписаны прямо внутрь;
- архивы с source files можно давать только как secondary attachment, не как
  основной carrier смысла.
- имена таких пакетов делать с понятным topic-prefix и точным timestamp suffix,
  например
  `proshka_q3_rh_route_state_YYYY_MM_DD_HHMM.md`
  и
  `proshka_q3_rh_route_state_YYYY_MM_DD_HHMM.tar.gz`,
  чтобы новые пакеты не перетирали старые и их было легко различать глазами.

Для H1 это означает:

- в prompt напрямую вставлять `Q_M^{raw}`, `\Pi_M`, exact `q_{rs}`,
  `\kappa_{A3}=1`, raw mismatch diagnostic, и direct filtered target on
  `(++),(+-)`;
- не ожидать, что Прошка сам восстановит normalization из старых A3 файлов.
- для локального быстрого check использовать:
  ```bash
  cd /Users/emalam/Documents/GitHub/rh_lean_01_2026
  source .venv/bin/activate
  python src/h1_raw_bulk_match.py --a 1.0 --M 3 --B 0.2 --t 0.15 --zeros 50
  ```
- для текущего live bulk-frontier использовать уже filtered checker:
  ```bash
  cd /Users/emalam/Documents/GitHub/rh_lean_01_2026
  source .venv/bin/activate
  python -u src/h1_filtered_bulk_match.py --a 1.0 --M 2 --B 0.2 --t 0.15 --zeros 10
  ```
- для первого diagnostic sweep:
  ```bash
  cd /Users/emalam/Documents/GitHub/rh_lean_01_2026
  source .venv/bin/activate
  python -u src/h1_filtered_bulk_match.py --sweep --B 0.2 --t 0.15
  ```
  Скрипт теперь печатает не только bucket-статистики, но и SVD-based
  classifier signal:
  `rank-1 rel residual`, `rank-2 rel residual`,
  `sv1 share`, `sv1+sv2 share`,
  а также low-mode support signal:
  `union<=1/2/3 rel resid` и `share`,
  чтобы быстро отличать low-rank structured correction от genuinely
  low-mode-supported defect.
- для cap-defect classifier на canonical case:
  ```bash
  cd /Users/emalam/Documents/GitHub/rh_lean_01_2026
  source .venv/bin/activate
  python -u src/h1_filtered_bulk_match.py --a 1.25 --M 4 --B 0.2 --t 0.15 --zeros 20 --defect-rank 2
  ```
  Здесь уже смотрим не только `rank-2 residual`, но и
  cross-family defect-basis report:
  `col_align`, `row_align`, `transfer_rel_resid`,
  чтобы понять, похож ли найденный small-rank defect на один и тот же
  конечномерный cap-space для `++` и `+-`.
- для joint shared-cap candidate на rank `3`:
  ```bash
  cd /Users/emalam/Documents/GitHub/rh_lean_01_2026
  source .venv/bin/activate
  python -u src/h1_filtered_bulk_match.py --a 1.25 --M 4 --B 0.2 --t 0.15 --zeros 20 --defect-rank 3
  ```
  Здесь смотрим уже блок `[shared cap-defect candidate]` и сравниваем
  `proj_rel_resid` между `++` и `+-`: если обе семьи хорошо сидят на одном
  joint projector, значит theorem shape “filtered intertwining modulo
  finite-rank cap defect” реально становится живым.

## Python / src rule

Если пишем executable sanity-check или numerical bridge probe, код кладём в
`/Users/emalam/Documents/GitHub/rh_lean_01_2026/src/`, а запуск в новых сессиях
делаем из корня repo после активации `.venv`. CSV и прочие одноразовые
diagnostic outputs по умолчанию писать в
`/Users/emalam/Documents/GitHub/rh_lean_01_2026/tmp/`, не в tracked docs.

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

### Python sanity / code location

Новый Python-код для быстрых sanity-check / numerical audit по Q3 держим в:

- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/src`

Запускать такие проверки надо от repo-root и через локальную `.venv`:

```bash
cd /Users/emalam/Documents/GitHub/rh_lean_01_2026
source .venv/bin/activate
python src/h1_raw_operator_sanity.py
```

Для текущего H1 bulk-normalization brick canonical script такой:

```bash
cd /Users/emalam/Documents/GitHub/rh_lean_01_2026
source .venv/bin/activate
python src/h1_raw_operator_sanity.py --M 4 --M-big 7 --B 0.2 --t 0.15
```

Этот скрипт проверяет three-in-one:

- scaling identity `\Pi_M=(2M+1)T_P^{Ray}(t,M)`;
- raw entry formula for `Q_M^{raw}`;
- stability of the raw entries under `M -> M_big`.

Для текущего live `H1^f` brick canonical filtered checker такой:

```bash
cd /Users/emalam/Documents/GitHub/rh_lean_01_2026
source .venv/bin/activate
python -u src/h1_filtered_bulk_match.py --a 1.0 --M 2 --B 0.2 --t 0.15 --zeros 10
```

Для рабочего `rank <= 3` theorem-shape canonical case теперь такой:

```bash
cd /Users/emalam/Documents/GitHub/rh_lean_01_2026
source .venv/bin/activate
python -u src/h1_filtered_bulk_match.py --a 1.25 --M 4 --B 0.2 --t 0.15 --zeros 20 --defect-rank 3
```

А для честного Gate A stability harness:

```bash
cd /Users/emalam/Documents/GitHub/rh_lean_01_2026
source .venv/bin/activate
python -u src/h1_filtered_bulk_match.py \
  --sweep \
  --sweep-a-values 0.8,1.0,1.25,1.5 \
  --sweep-M-values 4,5,6,7 \
  --sweep-zero-values 20,40,80 \
  --defect-rank 3
```

Здесь уже надо смотреть не только `rank-k residual`, но и:

- `sigma_next/sigma_rank` как rank-stability proxy;
- principal angles в cross-family/shared-basis comparisons;
- `[shared cap-defect candidate]` для same-space test;
- `embedded-shared-basis transfer` для `M -> M+1` consistency.

Этот скрипт уже не проверяет убитый raw-target `w_{rs}(a)=\kappa(a)q_{rs}`, а
сравнивает именно live filtered families `(++),(+-)`:

- `M_{mn}^{++}(a)` vs `\kappa(a)\widetilde q_{mn}^{++}`;
- `M_{mn}^{+-}(a)` vs `\kappa(a)\widetilde q_{mn}^{+-}`.

## Что не делать

- Не опираться на старый broad-cone route как на public RH contract.
- Не возвращать в mainline T5/Acceptance/legacy status narratives.
- Не засовывать raw chats или zip extracts напрямую в `q3_docs`.
- Не создавать новый архитектурный pivot без sync в manuscript + control plane.
- Не коммитить skill-файлы из `~/.codex/skills` в repo.

## Текущий практический next step

Если нет нового user redirect, текущий честный frontier такой:

- symmetric two-sided filtered H-bridge:
  `\mathcal P_{M,N}`, `\Delta_{M,N}`, `\phi_n^\pm[a]`, `S_{a,M,N}`,
  `B_{M,N}=\Delta_{M,N}^*\Delta_{M,N}`,
  `\widetilde Q_{M,N}=\Delta_{M,N}^*Q_{M+1}\Delta_{M,N}`;
- Proshka-facing raw operator hack:
  use
  `Q_M^{raw}=T_M[P_A]-\Pi_M`,
  `\Pi_M=(2M+1)T_P^{Ray}(t,M)`,
  with
  `q_{rs}=\langle Q_M^{raw}e_s,e_r\rangle`;
- next live blocker:
  defect-aware filtered bulk bridge
  `M_{mn}^{++}(a)=\kappa(a)\widetilde q_{mn}^{++}+F_a^{++}` and
  `M_{mn}^{+-}(a)=\kappa(a)\widetilde q_{mn}^{+-}+F_a^{+-}`,
  with one joint finite-rank cap defect as the honest target and exact
  equality retained only as the zero-defect special case;
- raw diagnostic layer:
  `q_{rs}=A_{r-s}-\sum \lambda_n e^{2\pi i(s-r)\xi_n}`,
  `\lambda_n=(2\Lambda(n)/\sqrt n)\Phi_{B,t}(\xi_n)`,
  `\kappa_{A3}=1`,
  and `w_{rs}(a)=W(\chi_s[a]*\widetilde{\chi_r[a]})`
  remain frozen only as normalization/reference data;
- rejected theorem shape:
  `w_{rs}(a)=\kappa(a)q_{rs}` cannot be the exact bulk bridge because the raw
  Q3 matrix is Toeplitz with constant diagonal while the raw Suzuki matrix has
  diagonal growth of order `\log|n|`;
- derived filtered consequence:
  the remaining filtered blocks follow from `(++),(+-)` by
  conjugation/self-adjoint symmetry;
- after the bulk match:
  separate finite-dimensional Suzuki cap positivity;
- semilocal-assisted refinement after that:
  finite-prime packet states `\eta_m^{(S,a)}`, Gram matrix
  `\Gamma_{a,M}^{(S)}`, and normalized synthesis
  `\widetilde S_{a,M}^{(S)}` only as engineering support for the same `H1^f`;
- packet route держать как fallback verification layer;
- compact scalar package держать только как diagnostic reduction;
- incoming notes прогонять через `q3-note-ingest` и не путать historical memos с live source of truth.
