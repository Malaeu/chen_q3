# Маршрут 058 — контракты ворот: вход, выход, свойства, соединение

Спутник устава `058_realzero_ground_diagonal_to_xi.goal.md`. Здесь не «что делать», а
**что каждые ворота потребляют, что выдают и чем сцепляются с соседними**.

Адреса получены прогоном
`python3 docs/cartographer/atom_describe.py --chain REALZERO_GROUND_DIAGONAL_TO_XI`
и сверены с деревом 2026-08-12. Разбор в `docs/cartographer/route058_objects.json`.

**Провенанс каждого имени** классифицирован по таксономии вердикта
`..._HERMFACT1_AUDIT_2026-08-11`, и это не украшение: тот же прогон в первой редакции
притянул `epsilon` к `Ordinal/Veblen.lean`, а `xi` — к `RKHS_rescaling.lean`. Оба отвергнуты
как локальные связанные переменные. Правдоподобно неверный адрес хуже отсутствия адреса.

```
LEAN_DECL        16   настоящая декларация, адрес выдан
LOCAL_HYPOTHESIS  6   связанная переменная в сигнатуре, адреса НЕТ и быть не может
PAPER_THEOREM     1   доказано в статье, в дереве отсутствует
PLACEHOLDER       1   имя ещё не написанного объекта
PROSE             6   пометка в записи, а не имя
```

Классификатор проверяем: `atom_describe.py --selftest` гоняет 14 имён с известным
ответом, включая все три случая, на которых он ломался. Инструмент, который нельзя
проверить, нельзя и починить.

---

## Сквозная логика: что течёт по маршруту

Одна величина проходит через все ворота и в конце становится RH:

```
конечная CCM-матрица  ─G1→  её нижний собственный вектор ξ  (простой, чётный, нормированный)
                      ─G2→  лагранжев многочлен строки ξ имеет только вещественные нули
                      ─G2b→ преобразование Prop-5.9 ТОЙ ЖЕ строки имеет только вещественные нули
                            ⇒ F_j целая, Z(F_j) ⊂ ℝ
                      ─G3→  F_j отслеживает projected trial
                      ─G3c→ projected trial отслеживает continuum trial
                      ─G4→  continuum trial → Ξ
                            ⇒ F_j → Ξ локально равномерно
                      ─G5→  Гурвиц: Z(Ξ) ⊂ ℝ  ⇒  RH
```

**Строка `ξ` — единственный носитель.** Она входит в `G1` и не меняется до `F_j`. Как только
в цепочке появляется вторая строка (например `kTrial`), маршрут останавливается по
`STOP: TWO_DIFFERENT_FAMILIES_USED`.

---

## G0 · объект, координата, нормировка `GAP` частично

**Вход.** Ничего — это фиксация системы координат.

**Выход.** Согласованные: целые узлы источника, полюсы преобразования, кофинальное
расписание пар `(m_j, N_j)`, невырожденная нормировка.

**Свойства и адреса.**

```
LEAN_DECL  ccmModeFinite        CCMFiniteWeilSourceMatrix.lean:23     целая метка моды
LEAN_DECL  proposition59Pole    Proposition59EntireTransform.lean:13  видимый полюс 2πk/L
PROSE      кофинальное расписание                                     не закреплено
PROSE      нормировка                                                 не закреплена
```

**Соединение.** Даёт `G1` и `G2b` общую координату. **Здесь и ломается всё остальное, если
узлы многочлена и полюсы преобразования окажутся в разных координатах** — шаг 6 схемы
доказательства `G2b` (`P(−Lz/2π) = 0`) есть в точности пересчёт одной координаты в другую.

**Чего не хватает.** Двух вещей, обе прозой: расписания и нормировки. Первая нужна `G3`
(кофинальность), вторая — `G2b` (невырожденность множителя).

---

## G1 · кофинальный конечный simple-even ground-пакет `GAP` главный спектральный фронт

**Вход.** Конечная CCM-матрица `ccmWeilMatFinite mProject N` для пары из расписания `G0`.

**Выход.** Пакет из шести объектов — **все шесть суть связанные переменные потребителя, а не
теоремы**:

```
LOCAL_HYPOTHESIS  epsilon      собственное значение
LOCAL_HYPOTHESIS  xi           собственный вектор — НОСИТЕЛЬ всей цепочки
LOCAL_HYPOTHESIS  heig         M *ᵥ ξ = ε • ξ
LOCAL_HYPOTHESIS  hbottom      ∀x, ε(x⬝x) ≤ x⬝(M *ᵥ x)
LOCAL_HYPOTHESIS  hsimple      finrank (eigenspace M ε) = 1
LOCAL_HYPOTHESIS  hnormalized  η ⬝ᵥ ξ = 1
```

`hxiEven` в список **не входит** — внешняя обёртка выводит чётность сама.

**Что уже есть.**

```
LEAN_DECL  H2a_SimpleEvenGround_FromPenaltyCoercivity  H2aPenaltyCoercivity.lean:395
```

Абстрактный движок: из penalty-сертификата даёт разом нижнее обобщённое собственное
значение, минимум, зазор, простоту и J-чётность. Над `ℂ` для пары `(K,G)`.

**Шесть поставщиков-кандидатов**, ни один не доведён: penalty-сертификат · блочное
расщепление чётности · GLOWER/Yoshida · Schur/Feshbach · ранг-инерция · внешняя теорема.

**Соединение.** Выдаёт `ξ` в `G2`. Всё остальное — `ε`, `heig`, `hbottom`, `hsimple`,
`hnormalized` — тоже уходит в `G2` как гипотезы одного вызова.

**Наработки, сведённые нами 2026-08-11.** `hsimple` эквивалентен счёту:
`rank(M − εI) = 2N` (`probes/Probe_Inertia_SimpleAsCount.lean`), и расщепляется чётностью на
два условия размерности `N` (`probes/Probe_Parity_KernelSplit.lean`). Ни одно из двух не
доказано.

### Дно дополнения раскалывается по чётности — вердикт Мифоса 2026-08-14

Источник: `q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/`
`GOAL058_G1_COFINAL_COMPLEMENT_FLOOR_MYTHOS_VERDICT_2026-08-14.md`,
`STOP_CODE: ODD_TAIL_AND_M13_RECEIVER_DO_NOT_SPECIALIZE_TO_COMPLEMENT_FLOOR_…`

Оператор коммутирует с чётностью, поэтому `q⊥` распадается `J`-инвариантно, а форма
`B = Q(K − aI)Q` блочно-диагональна по чётности. Отсюда точное разложение:

```
β на q⊥  =  min( чётная нога , нечётная нога )
```

Заполнены они несимметрично:

```
НЕЧЁТНАЯ  поставщик  sourceWeilOddTailAmbientCoercive_explicit   ∀i, настоящий
          приёмник   привязан к m=13, модальность iff — знака нет
ЧЁТНАЯ    ПУСТО      ни поставщика, ни приёмника
```

**Два убийства, проверять перед любой попыткой обойти.**

```
F1  «коммутирует + простой ⇒ чётное основное состояние»   ЛОЖНО
    Fin 2, J = swap, K = [[0,1],[1,0]]: основное состояние нечётно и просто.
F2  «нечётный tail floor ⇒ complement floor»              УБИТО
    Fin 3 collapse plant ⊕ I_n: хвост коэрцитивен, а в q⊥ остаётся
    второй нулевой уровень — любое β > 0 отвергается.
F3  подмена сдвига между ногами                           УБИТО
    курс обмена 1:1 против β — единица расхождения сдвига съедает единицу дна.
```

**Ход, снимающий страх за знаменатель** (`C3` у Мифоса). Дно не доказывается вдоль всей
последовательности: оно берётся **один раз** при фиксированном сдвиге `a*` как константа
`β* > 0`, затем переносится по близости Рэлея `|a_j − a*| ≤ β*/2` через точное тождество
`B(a_j) = B(a*) − (a_j − a*)Q`, давая `β_j ≥ β*/2`. После этого `невязка_j/β_j → 0`
следует из `невязка_j → 0` при фиксированном знаменателе. Замер обязан быть получен
**независимо** от утверждения о сходимости к `Ξ`, иначе доказательство закольцовывается.

**Очередь Мифоса и её состояние на 2026-08-17.**

```
1  sourceWeilOddTailInverseWeightedCorrection_quadraticForm_le   ЗАКРЫТА
   D0PstarSourceWeilOddTailCorrectionBound.lean:35
2  sourceWeilEvenTailAmbientCoercive_explicit                     ОТКРЫТА ← фронт
3  even-head Gram-certificate schedule family                     ОТКРЫТА
```

**Цена чётного близнеца, снята с диска 2026-08-17.**
`D0PstarSourceLowBandModeDecay.lean` содержит двенадцать теорем, из них две не знают о
чётности вовсе — `norm_fourier_logWindowZeroExtendedMode_le_lowBand_inv` (:132) и
`sum_support_inv_nat_shift_sq_le` (:368). Ядро переиспользуется как есть; десять
остальных суть обёртки над `Odd`-модами и требуют механического близнеца. Новая
математика остаётся ровно в одном месте: дно чётной головы при фиксированном сдвиге.

---

## G2 · вещественность нулей лагранжева многочлена `READY` условно на G1

**Вход.** Полный пакет `G1`.

**Выход.** `ZerosRealOn Set.univ (fun z => ((sourceLagrangePolynomial …ξ).map (algebraMap ℝ ℂ)).eval z)`

**Свойства и адреса.**

```
LEAN_DECL  ZerosRealOn                       ZeroEscapeLogic.lean:13
           ∀ z ∈ S, f z = 0 → z.im = 0
LEAN_DECL  sourceLagrangePolynomial          RankOneCorrectionLagrangePolynomial.lean:12
           Σ_k C(ξ_k) · ∏_{j≠k} (C(λ_j) − X)
LEAN_DECL  ccmSourceLagrangePolynomial_complex_zerosRealOn_of_bottomRayleigh_simple_normalized
                                             CCMFiniteWeilParity.lean:161
```

**Это ворота-потребитель, и он уже доказан.** Внешняя обёртка: `hxiEven` выводит внутри,
базис фактора устраняется автоматикой (`probes/Probe_QuotientBasis_Auto.lean`).

**Соединение.** Его выход — посылка `G2b`. Обратите внимание: `G2` говорит о
**многочлене**, `G2b` — о **преобразовании**. Это разные функции с общей строкой `ξ`.

---

## G2b · перенос множества нулей на преобразование `GAP` ДЕШЁВЫЙ ФРОНТ

**Вход.** Вещественная корневость многочлена строки `ξ` (выход `G2`).

**Выход.** `F_j` целая и `Z(F_j) ⊂ ℝ`.

**Свойства и адреса — все объекты в дереве, нет только теоремы.**

```
LEAN_DECL  proposition59RawTransform  Proposition59EntireTransform.lean:84
           (√L)⁻¹ · Σ_{k∈S} ξ_k · proposition59PoleKernel L k z
LEAN_DECL  proposition59PoleKernel    Proposition59EntireTransform.lean:33
           dslope (proposition59Numerator L) (proposition59Pole L k)
LEAN_DECL  dslope                     Mathlib DSlope.lean:35
PLACEHOLDER Proposition59GroundLagrangeZeroSetBridge   ← писать
```

Числитель — `2·sin(zL/2)`, производная `L·cos(zL/2)` (`:36`).

**Схема доказательства, семь шагов.**

```
1. z — устранимый включённый полюс        ⟹ z вещественный
2. вне конечных полюсов раскрыть:
     rawFplus(z) = scale · sin(Lz/2) · Σ_k ξ_k/(z + 2πk/L)
3. синус-множитель нулевой                ⟹ z на вещественной решётке
4. иначе нулевая сумма Коши
5. умножить на конечный знаменатель
6. получить  P(−Lz/2π) = 0                ← здесь работает координата из G0
7. вещественная корневость P              ⟹ Im z = 0
```

**Верная структура — разложение МНОЖЕСТВА нулей, не равенство:**

```
Z(F_{m,N}) = Z(P_{m,N}) ∪ Z(Λ_{m,N})       Λ — вещественный решёточный множитель
```

**УБИТО:** `Pstar = c_N · многочлен`. У преобразования бесконечно много внешних нулей на
синус-решётке, у ненулевого конечного многочлена — конечное число.

**Соединение.** Выдаёт `F_j` — объект, который дальше не меняется до самого `G5`.

---

## G3 · та же `F_j` отслеживает projected trial `GAP` ГЛАВНАЯ СТЕНА

**Вход.** `F_j` из `G2b`; projected prolate trial.

**Выход.** `‖F_j/нормировка − T_j‖ → 0` локально равномерно на компактах полосы.

**Свойства.**

```
PLACEHOLDER  FiniteGroundTransformToCCMTrialLocallyUniform   ← главная недостающая
PROSE        истинный зазор, невязка
```

**Направление вынужденное.** Переносится **сходимость на `F_j`**, а не вещественность на
`T_j`. Вещественность нулей неустойчива к возмущению: у `z² + ε` при `ε<0` два вещественных
нуля, при `ε>0` — сопряжённая пара. Никакая точность приближения её не переносит.

**Шесть решений-кандидатов:** невязка/истинный зазор · Feshbach-граф · penalty-overlap ·
defect-Gram · low/high split · norm-resolvent Galerkin. **Убито:** exact ground equals trial.

**Соединение.** Единственные ворота, где встречаются обе семьи — и именно поэтому здесь
стоит стоп-код. `F_j` остаётся носителем; `T_j` служит эталоном предела и в выход не входит.

---

## G3c · projected trial отслеживает continuum trial `GAP`

**Вход.** Projected prolate trial (конечный срез).

**Выход.** Сходимость к континуальному пробнику CCM.

**Свойства.**

```
LEAN_DECL  kTrial               D0CanonicalApproximation.lean:35   ПОЛЕ структуры
           CoefficientFamily.kTrial : PairIndex → ℤ → ℂ
LEAN_DECL  centeredPstarFamily  D0CanonicalApproximation.lean:62
           (centeredXi 0 / rawFplus 0) * rawFplus z
PROSE      проекционный хвост
```

*Первая редакция этого документа объявляла `kTrial` заглушкой: поиск умел находить только
`theorem|def|…` и не видел полей структур. Дефект устранён 2026-08-12, поле находится и
несёт владельца.*

---

## G4 · CCM Lemma 7.3: continuum trial → Ξ `GAP` доказано в статье

**Вход.** Континуальное trial-преобразование.

**Выход.** Сходимость к `centeredXi` локально равномерно на замкнутых подполосах.

**Свойства.**

```
PAPER_THEOREM  CCM_Lemma_7_3       в дереве ОТСУТСТВУЕТ, доказано в статье
LEAN_DECL      centeredXi          ClassicalXiInterface.lean:17
PROSE          локально равномерная сходимость
```

**Это тот самый объект, за который стоял doc-alias `hermfact1`:** статус `PAPER_PROVED`,
Lean-порт `OPEN`. Имени `hermfact1` в дереве нет и не должно быть.

**Соединение.** Вместе с `G3` и `G3c` даёт `F_j → Ξ`.

---

## G5 · zero-escape → RH `READY` логическое ядро доказано

**Вход.** `Z(F_j) ⊂ ℝ` (из `G2b`) и `F_j → Ξ` (из `G3`+`G3c`+`G4`) — **на одной и той же
семье**.

**Выход.** `Q3.RH`.

**Свойства и адреса — всё доказано.**

```
LEAN_DECL  rh_of_canonical_strip_slots  CanonicalRHRouteSkeleton.lean:145
LEAN_DECL  ZerosApproachOn              ZeroEscapeLogic.lean:18
LEAN_DECL  sameCofinalGuard             CanonicalRHRouteSkeleton.lean:69
LEAN_DECL  Q3.RH                        Basic/Defs.lean:177
```

`sameCofinalGuard` — механическая защита инварианта: не позволяет подставить независимую
диагональ вместо одной семьи.

**Соединение.** Замыкает маршрут. Гурвиц читает нули **предела**, а не переносит их вдоль
последовательности — поэтому оба входа обязаны прийти от одной семьи.

---

## Сводка: где что лежит

| ворота | статус | несущий объект | адрес |
|---|---|---|---|
| G0 | `GAP` частично | координаты | `CCMFiniteWeilSourceMatrix.lean:23` · `Proposition59EntireTransform.lean:13` |
| G1 | `GAP` главный | пакет из шести гипотез | движок `H2aPenaltyCoercivity.lean:395` |
| G1-дно | `GAP` **чётная нога пуста** | `β = min(чётная, нечётная)` | нечётная `D0PstarSourceWeilOddTailExplicitCoercivity.lean`; чётной нет |
| G2 | `READY` | потребитель вещественности | `CCMFiniteWeilParity.lean:161` |
| G2b | `GAP` дешёвый | `Proposition59GroundLagrangeZeroSetBridge` | писать; объекты `Proposition59EntireTransform.lean:33,84` |
| G3 | `GAP` **стена** | `FiniteGroundTransformToCCMTrialLocallyUniform` | писать |
| G3c | `GAP` | `centeredPstarFamily` | `D0CanonicalApproximation.lean:62` |
| G4 | `GAP` бумага | `CCM_Lemma_7_3` | в дереве нет |
| G5 | `READY` | `rh_of_canonical_strip_slots` | `CanonicalRHRouteSkeleton.lean:145` |

Живое состояние — в базе, не здесь: `brief.py` · `cheap.py` ·
`kb_migrate_route058.py --check`.
