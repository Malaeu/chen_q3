# Goal 057 · CCM penalty Phase 2B: fixed-q beta*_480, Aitken Delta^2, parity ledger

```yaml
STATUS: CLOSED_PASS
VERDICT: CONV_Q2PLUS
RUN_ID: RUN_DELTA_N480_AITKEN
DECISION_RULE_SOURCE: frozen registration 2026-08-09 (batch rank 1 dispatch, verbatim)
ROUTE: CHALLENGER_NOT_RH
PROMOTION: FORBIDDEN
BUS_010: VOID
GOAL_055: HOLD
PX_RH_CLAIM: NOT_MADE
```

## Precommit исполнен буквально

```yaml
lambda: sqrt(13)
m: 13
N0: 120
N: 480
dimension: 961
q: SAME fixed q in E_120 as Phase 2 (exact Phase-1 rational J-even projection)
embedding: literal zero-padding only; no profile re-optimization
precision_dps: [180, 360]
beta_initial_bracket: [0, 1e-48]
beta_search_tolerance: max(1e-100, 2^-40 * current_upper_bracket)
production_eigensolver: Arb vdhoeven_mourrain
independent_eigensolver: Arb rump (полный повтор обеих N=480 precision cells)
aitken_inputs: stored Phase-2 360-dps enclosures beta*_120, beta*_240 (SHA-pinned)
schedule_freeze: K6/C09 — расписание объявлено и скрипт закоммичен (e1561e9) ДО первого числа N=480
```

Ни один параметр не менялся после просмотра какого-либо результата N=480. Скрипт
инструмента закоммичен и запушен (`e1561e9`) до завершения первой ячейки N=480 —
проверяемый по git-истории свидетель отсутствия пост-hoc подстройки.

## Странности, записанные при входе (до результатов)

1. **Названные в диспетче файлы регистрации отсутствуют в этом клоне**:
   `MYTHOS_POSITION_COMPARATIVE_ROUTES_2026-08-09.md` и
   `SYNTHESIS_FINAL_ROUTES_CONSENSUS_2026-08-09.md` в `docs/routeB_bus/` нет.
   Есть `SYNTHESIS_ROUND1_ROUTES_2026-08-09.md` (коммит `1d4fab2`), несущий те же
   замороженные числа (r2=0.81085; power-law r3=0.811±0.03; q=1: r3~0.883,
   beta_inf~1.900e-55; q=2: r3~0.942, beta_inf~2.285e-55; decision rule
   pre-committed, no drift) и ссылающийся на MYTHOS_POSITION @ c72bbe7.
   Исполнение шло по дословному правилу из диспетча, совпадающему с ROUND1.
   Что бы это разрешило: push двух файлов с Mac.
2. **python-flint 0.9.0 здесь против 0.8.0 в Phase 2.** Закрыто контрольными
   ячейками: N=120@180 и N=240@360 пересчитаны в этой среде; интервалы a,
   beta*, tau_required перекрываются с сохранёнными Phase-2, видимые цифры
   совпадают до печатной точности.
3. **Тело исполнителя — CLAUDE_CODE_LINUX (cloud), ветка
   `claude/phase-2b-n480-aitken-jlic1a`**, а не Mac thread 2: так маршрутизирован
   этот батч владельцем. Тег коммита из диспетча `[MacOS][rh_clean]` заменён на
   фактические OS+ветку по обязательному правилу CODEX_CONTROL §16.2.

## Реализация и trust class

| Артефакт | SHA-256 |
|---|---|
| `phase2b_scripts/ccm_beta_n480_aitken.py` | `308015434c9125eab5b31d21e471a74d884a9ad5ddcda4a12440e1dcca34a52e` |
| `phase2b_results/ccm_fixed_q_beta_n480_aitken.json` | `923fc33265bffcf47ffc66eda96d36b5d2aaff44838a87fd2100b56f0d04305d` |
| pinned Phase-2 script | `851db5963b4ad012cc3746b2827931b1beedad0b931676d2b40f4cb9ca774f72` |
| pinned Phase-2 results (источник x0, x1) | `204e441ee807938335a3826257e1b77cb186fb9aa5416eec66b46cd54b69ff4b` |
| pinned Phase-1 builder | `1be57db69683652ed4f6d56dba6fc3b70c186f429fbb7f5bef978cd84f08ed0d` |
| pinned q source | `0e5239355c54103859b22d7f753d8cd6765c2c41bcd3ec7f86b20beccc907a88` |

Вся сборка матриц, вложение q, Householder, floors, Schur и LDL^T импортируются
из SHA-запиненного Phase-2 скрипта — транскрипции формул нет. Оба eigensolver'а —
интервальные алгоритмы Arb; float64-вердикт отсутствует. Каждый выход — enclosure.
Среда: Linux (cloud), python-flint 0.9.0, `ctx.threads=1` в каждой ячейке.

## Retained 360-dps результат, N=480 (production vdhoeven_mourrain)

| N | controlling sector | a | beta*_N | beta*_N − a | tau_required |
|---:|---|---:|---:|---:|---:|
| 480 | odd | `4.7199799795094300e-59` | `2.3069968069169595e-55` | `2.3065248089190086e-55` | `2.3067425159607899e-55` |

Полная лестница fixed-q профиля (Phase 2 сохранённая + Phase 2B):

| N | beta*_N (retained 360 dps) | источник |
|---:|---:|---|
| 120 | `3.0559133975151657e-55` | Phase 2, stored |
| 160 | `2.7228638920503397e-55` | Phase 2, stored |
| 200 | `2.6230059967905176e-55` | Phase 2, stored |
| 240 | `2.4778868595077980e-55` | Phase 2, stored |
| 480 | `2.3069968069169595e-55` | **Phase 2B, этот прогон** |

- Ширина enclosure beta*_480: `~2.4e-338` (допуск 2^-40 выполнен с запасом).
- `a < safe beta < beta*_480` интервально; `tau_required < 1` интервально;
  full even LDL^T и odd LDL^T проходят на обоих precision и обоих алгоритмах.
- **Зеро-паддинг буквальный**: координаты q при n>120 — точные нули (проверено
  `is_zero()` покомпонентно), и `a` инвариантно: интервал a_480 перекрывается
  со stored a_120 и a_240, видимые цифры совпадают до печатной точности.
- Per-sector floors (360 dps): odd `2.3069968069169595e-55` (binding);
  even q-perp compression `1.0235747238545100e-51`.

## Aitken Delta^2 и r3 — по замороженному правилу

Вход (никакой подгонки; x0, x1 — сохранённые Phase-2 enclosures, x2 — retained
ячейка этого прогона):

```text
x0 = beta*_120 = 3.0559133975151657e-55   (stored ball, width ~4.3e-338)
x1 = beta*_240 = 2.4778868595077980e-55   (stored ball, width ~4.3e-338)
x2 = beta*_480 = 2.3069968069169595e-55   (this run,   width ~2.4e-338)
```

Результаты (enclosures):

```text
r2 = x1/x0 = [0.8108498302087439691604882345029830911297 +/- 1.12e-41]   — совпадает с зарегистрированным 0.81085
r3 = x2/x1 = [0.9310339566412714599698925561091594775966 +/- 3.06e-41]
Aitken beta_inf = x2 − (x2−x1)^2/(x2−2·x1+x0)
                = [2.235268010504566231119944768468298545090e-55 +/- 1.77e-96]
знаменатель x2−2·x1+x0 = [4.071364854165291808795106089323063765383e-56 +/- 1.66e-96]  (нуля не содержит)
```

(Печать — сертифицированные decimal balls Arb `.str(40)`; радиус поглощает
обрезание печати. Внутренние радиусы: r2/r3 ~e-283, Aitken/знаменатель ~e-337;
полные строки — в results json.)

Замороженное правило (дословно):

```text
r3 <= 0.84         => POWER_LAW_WITNESS_DECAY
0.86 <= r3 <= 0.90 => CONV_Q1      (beta_inf ~ 1.900e-55)
r3 >= 0.92         => CONV_Q2PLUS  (beta_inf ~ 2.285e-55)
otherwise          => TRANSIENT    -> schedule N=960, same spec
```

**Применение: r3 = 0.93103…, весь enclosure сертифицированно в полосе
`r3 >= 0.92` => `CONV_Q2PLUS`.** (Сравнение с границами полос — точное
рациональное, через exact integer scaling endpoints ×100.)

Справочно из регистрации: power-law предсказывал r3 = 0.811±0.03 — наблюдение
вне этой полосы с запасом ~4 её ширины; q=1 предсказывал ~0.883; q=2+
предсказывал ~0.942. Наблюдённый r3 = 0.93103 и Aitken beta_inf = 2.2353e-55
против зарегистрированного ориентира q=2+ beta_inf ~ 2.285e-55: полоса выбрана
правилом по r3; расхождение точечного ориентира beta_inf (~2.2%) остаётся
Mythos'у для скоринга, здесь не интерпретируется.

## Parity ledger

- **Binding sector при N=480: odd — как ожидалось** (expected: odd competitor).
  Все пять точек лестницы (120…480) держат odd binding.
- **Нижний вектор even-сектора** (bottom eigenvector of `K^+|q_perp`, 360 dps,
  сертифицированно вещественный, знак каждой из 481 компонент разрешён):
  - масса на чётных модах n: `0.508898…`, на нечётных: `0.491102…`
    (почти паритет, лёгкий чётный перекос);
  - 81 сертифицированная перемена знака, 0 неразрешённых компонент;
  - доминирующие моды: n = 3, 4, 2, 0 (низкомодовая концентрация);
  - ортогональность к q сертифицирована: `<q, v>` ∋ 0, ширина ~1e-292.
- **Нижний вектор odd-сектора** (binding competitor, 480 компонент):
  - масса чёт/нечёт: `0.499460…` / `0.500540…` (паритет);
  - 45 сертифицированных перемен знака, 0 неразрешённых;
  - доминирующие моды: n = 2, 3, 1, 4.
- **Interlacing против N=240** (`odd_240` — главная 240×240 подматрица
  `odd_480`, элементы матрицы N-независимы; Коши): все пять нижних собственных
  значений строго упали, сертифицированно:

| k | lambda_k(odd, N=480) | lambda_k(odd, N=240) | строгое 480 < 240 |
|---:|---:|---:|---|
| 1 | `2.3069968069e-55` | `2.4778868595e-55` | да |
| 2 | `3.1569743214e-48` | `3.4340620451e-48` | да |
| 3 | `1.5426847081e-41` | `1.7142602721e-41` | да |
| 4 | `1.1739989320e-35` | `1.3126388902e-35` | да |
| 5 | `7.6241015289e-30` | `8.4492712488e-30` | да |

- Монотонность even q-perp floor: `1.0236e-51 (480) < 1.1171e-51 (240, stored)`
  сертифицированно строго.

Записанная странность (до объяснения): нижняя odd-мода изолирована от
остального спектра на ~7 порядков (`e-55` против `e-48` у k=2). Два чтения:
(а) подлинная почти-нулевая мода конечной family; (б) артефакт фиксированного
E_120-witness окна. Различитель: трек bottom-2 на N=960 — расходятся ли k=1 и
k=2 дальше (а) или сближаются (б).

## Кросс-проверки

- **Два независимых eigensolver'а**: production `vdhoeven_mourrain` + полный
  независимый повтор обеих N=480 precision cells алгоритмом `rump`. Полное
  согласие: на обоих precision rump независимо сертифицирует (pass, odd
  binding), и все интервалы — a, beta*, beta*−a, tau_required, оба floor'а,
  контрольные элементы матрицы — перекрываются с production.
- **Precision doubling 180→360**: интервалы a, beta*, beta*−a, tau_required,
  floors и контрольных элементов перекрываются у обоих алгоритмов.
- **Воспроизведение среды** (flint 0.9.0 против 0.8.0): N=120@180 и N=240@360
  пересчитаны здесь; a, beta*, tau_required перекрываются со stored — PASS.
- Тайминги (эта среда, single-thread на ячейку): N=480@180 vdh 783 s;
  N=480@360 vdh 1699 s; N=480@180 rump 11715 s; N=480@360 rump 23425 s
  (rump ≈ 14–15× vdhoeven на этой размерности — на N≤240 в Phase 2 это не
  проявлялось); vectors 850/884 s; N=240@360 221 s.

## Что это говорит и чего не говорит

Положительность fixed-q профиля продолжается до N=480, odd sector остаётся
bottleneck, `a` неизменно — контроль зеро-паддинга держит. Замороженное правило
даёт `CONV_Q2PLUS`: последовательность отношений r2=0.811 → r3=0.931
поднимается к 1, что и есть зарегистрированная сигнатура сходимости к
положительному пределу, а не степенного распада witness'а.

Но это остаётся конечной fixed-q family diagnostics: не `SlotH2a`, не continuum
transfer, не all-lambda input A, не uniform operator gap, не Route B и не RH.
Aitken-оценка beta_inf — экстраполяция по трём точкам со строгой интервальной
арифметикой поверх них, но без доказанной модели сходимости; она не занимает
квантор. Никаких Lean-правок; никаких заявлений о закрытии goal. Границы без
изменений: `CHALLENGER_NOT_RH`, `BUS_010 VOID`, `GOAL_055 HOLD`,
`PX_RH_CLAIM NOT_MADE`.

Сырой файл результатов возвращается владельцу для Mythos-скоринга против
замороженной регистрации:
`docs/routeB_bus/phase2b_results/ccm_fixed_q_beta_n480_aitken.json`
(в нём — все восемь ячеек целиком: enclosures, тайминги, кросс-чек солверов).
