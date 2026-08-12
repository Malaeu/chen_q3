# MAP.md — Единая карта Route B (навигатор проекта)

*Живой файл. Одна точка правды для имён и статусов. Обновляется после каждого хода.*
Последняя картография: 2026-08-07 (4 агента-картографа прошли роф / Мюнц / спектр / шину
по диску; сведено развилкой `maps/ROUTEB_FORK_2026-08-07_THE_GAP.md`, пин `7dbfb431`).
Предыдущая: 2026-08-03 — она устарела системно, см. §6 и §7.
Route B = **CHALLENGER / NOT_RH**, `BUS_010: VOID`, `GOAL_055: HOLD`,
`PX_RH_CLAIM: NOT_MADE`. RH официально НЕ заявлена.

Легенда статусов: ✅ доказано (Lean) · ⏳ условно/kill-pass (ещё не Lean) · 🔓 открыто · ☠️ poisoned (легально только после закрытия подпорки) · 🧩 принято как гипотеза (не выведено) · ⛔ убито судьёй (форма цели снята).

---

## 1. Как читать эту карту (30 секунд)

Цель одна — **RH**. Под ней **крыша** (собрана, дырок нет, но условная). У крыши **7 ворот G1–G7**, каждое = один слот. Ворота кормятся из **двух независимых веток** + одна отдельная стена:

```
                              R H   (цель)
                                │
                КРЫША  rh_of_canonical_strip_slots   (собрана, hole-free, условная)
                                │
     G7 компилятор (G1..G6 ⟹ RH) ✅ ─── склеивает всё ниже
                                │
   ┌────────────┬──────────────┼──────────────────┬────────────────┐
  G1 H1 ✅     G4 anchor ✅   G5 S1 🔓           G2→G3 (H2a→H2b)    G6 S2 🔓
 (голоморфн.) (equality z=0   сузился до ОДНОГО  ВЕТКА «СПЕКТР»    ВЕТКА «МЮНЦ»
               + centeredXi   входа:             G2: 0 поставщиков коробка T5 4/4 ✅
               0 ≠ 0 ✅)      CenteredTrial      слота, но есть    gauge ✅, константа ✅
                              CriticalMoment     доказанный        идентификация
                              Ratio 🔓           конечный движок   D.limit = c·Ξ·γ 🔓
                                                 H2aPenalty        цепочка D0Pstar*
                                                 Coercivity ✅     до SlotS2 НЕ дотянута
                                                   │
                                             M0 + M1✅→M2→M3→[M4]
```

**Где мы сейчас (одной строкой):** закрыты G1, условная крыша G7, G4 **полностью**
(equality в z=0 плюс `centeredXi 0 ≠ 0`) и все 4 винта Мюнца; открыты **ровно 4 фронта** —
G2 (H2a: слот без поставщика, движок есть), G3 (concrete H2b supplier: поставщиков ноль),
G5 (сузился до одного входа), G6 (полная S2-стена Мюнц→S2, плюс необорванная цепочка
`D0Pstar*`). M1 теперь в Lean, но это по-прежнему один keystone G3, не закрытие H2b.

**Две ветки простыми словами:**
- **Спектр (H2-ветка):** `selectedFamily_realZeros` уже является условной Lean-теоремой из H1 + H2a + `h510`; открытым остаётся concrete supplier `Theorem510RealZeroBridge` — **у него на диске ноль поставщиков, есть только определение**. Его движок требует M0–M3 и, для полного Fourier/Hurwitz corollary, M4.
- **Мюнц:** коробка `T5` даёт аналитическое продолжение окна. 4 входа-винта **все закручены (4/4)**, но это ещё не S2: для каждого ненулевого cluster нужны same-family, cofinal, normalization и locally-uniform tail control при фиксированном zero-free gauge. **Ни один Lean-файл серии 056 не тянет `SlotS2`/`ClusterData`** — ребра нет, см. §5.

**Крыша нигде не инстанцирована:** `rh_of_canonical_strip_slots` не потребляется ни одним
внешним файлом. Проектных аксиом Route B не тянет — грязь (`Q3.Weil_criterion`,
`prime_term_le_at_t_critical_axiom`) вся в легаси Route A, вне импорт-замыкания.

---

## 2. Конвенция имён (чтобы не теряться)

Каждый объект имеет **человеческое имя** (главное) + короткий **ID для ссылок**. ID-схема:

| Префикс | Значит | Пример |
|---|---|---|
| **G-NNN** | задача на шине (порядковый номер, историю не трогаем) | G-051 |
| **T-…** | теорема-цель (крупный узел дерева) | T-H2b, T-Muntz, T-Roof |
| **L-…** | лемма-кирпич; всегда с пометкой **⊳ куда подключается** | L-M1 ⊳ T-H2b |
| **IN-…** | вход-гипотеза (винт в коробку) | IN-hRm ⊳ T-Muntz |
| **SLOT/GATE** | слот/ворота крыши | GATE-G3 = SLOT-H2b |

Старые мнемоники (`β8d`, `hRm`, `M1`) **не отменяются** — они переведены в словаре §4. Смотришь сюда — и никогда не гадаешь, что за буква.

---

## 3. Дерево целей со статусами

```
T-Roof  rh_of_canonical_strip_slots  ✅ (условная Lean-теорема на G1..G6; нигде не потреблена)
│
├─ GATE-G1  SLOT-H1   голоморфность семейства на полосе            ✅
├─ GATE-G4  SLOT-anchor  equality в z=0; floor; centeredXi 0 ≠ 0   ✅ ЗАКРЫТО ПОЛНОСТЬЮ
├─ GATE-G7  компилятор G1..G6 ⟹ RH (Hurwitz)                      ✅ (conditional)
│
├─ GATE-G5  SLOT-S1   локальная ограниченность (вход Монтеля)      🔓  сузился до ОДНОГО входа
│    └─ CenteredTrialCriticalMomentRatio                            🔓 `D0CenteredCriticalMoment.lean:86`
│         ├─ ⟶ Montel-gate   ✅ `D0CriticalMomentMontelGate.lean:15`
│         └─ ⟶ ненулевой cluster ✅ `D0CriticalMomentCanonicalCluster.lean:9`
│
├─ ВЕТКА СПЕКТР ────────────────────────────────────────────────
│   ├─ GATE-G2  SLOT-H2a  нижнее собств. значение простое+чётное   🔓  поставщиков слота НОЛЬ
│   │    └─ движок H2a_SimpleEvenGround_FromPenaltyCoercivity      ✅  `H2aPenaltyCoercivity.lean:395`
│   │         └─ SIEG_of_penalty (инстанциация на семейство)        🔓  не написан (файл сам это говорит)
│   └─ GATE-G3  selectedFamily_realZeros                            ✅  условная Lean-теорема из H1 + H2a + h510
│        └─ concrete Theorem510RealZeroBridge supplier              🔓  H2B_TRANSFORM_LAYER_OPEN, поставщиков НОЛЬ
│             ├─ L-M0  инстанцировать форму Q(11), вывести β1/β2/β3 🔓
│             ├─ L-M1  weighted self-adjoint → Hermitian (гол 051)  ✅  `PosDefSelfAdjointRealSpectrum.lean:18`
│             ├─ L-M2  вырожденная форма → фактор с PosDef-метрикой 🔓  частичный scaffold есть
│             ├─ L-M3  определитель → форма Лагранжа → вещ. корни   🔓
│             └─ L-M4  Фурье + сокращение полюсов + Гурвиц (опция)  🔓
│
└─ ВЕТКА МЮНЦ ──────────────────────────────────────────────────
    └─ GATE-G6  SLOT-S2  опознание кластера как c·Ξ·γ₀ (главная стена) 🔓
         ├─ gauge: xiGauge_ne_zero_of_mem_strip                     ✅  `S2GaugeNonvanishing.lean:34`
         ├─ ненулевая якорная константа: limit_at_zero_ne_zero      ✅  `S2GaugeNonvanishing.lean:101`
         ├─ идентификация D.limit = c·Ξ·γ                           🔓  ЕДИНСТВЕННОЕ, что открыто в самом слоте
         ├─ коробка T-Muntz (T5 shell, window identity)             ✅ доказана
         │    ├─ IN-hG   окно Gwin аналитично                       ✅ (гол 047)
         │    ├─ IN-hRp  правый хвост Rplus аналитичен              ✅ (гол 046)
         │    ├─ IN-hRm  левый хвост Rminus аналитичен              ✅ (2 авг, MacOS)
         │    └─ IN-habs абсолютная сходимость / тождество Меллина   ✅ (Goal 052, 3 авг)
         └─ цепочка D0Pstar* (056-серия) → SlotS2                    🔓 РЕБРА НЕТ, см. §5
```

**Открытые фронты (ровно 4):** G2 (H2a) · G3/движок (M0, M2, M3, M4 — M1 уже ✅) · G5 (один вход) · G6 (полная S2-стена + необорванная цепочка).

---

## 4. Словарь-переводчик (что за буква = что человеческим языком)

### 4a. Крыша — слоты, ворота, supply-узлы

| Имя (старое) | ID | Человеческим языком | Статус | Где |
|---|---|---|---|---|
| `rh_of_canonical_strip_slots` | T-Roof | Итоговая крыша: из слотов+мостов собирает RH на полосе | ✅ условная Lean-теорема; нигде не инстанцирована | `Q3/Proofs/RouteB/CanonicalRHRouteSkeleton.lean:145` |
| SlotH1 | SLOT-H1 / GATE-G1 | Голоморфность нормированного семейства | ✅ | `D0CanonicalApproximation.lean:177` |
| SlotH2a | SLOT-H2a / GATE-G2 | Нижнее собств. значение простое, изолированное, чётное (ВХОД, не теорема) | 🔓 **поставщиков ноль**; движок есть, см. §4d | слот `CanonicalRHRouteSkeleton.lean:52` |
| selectedFamily_realZeros | часть SLOT-H2b / GATE-G3 | У выбранного семейства вещественные нули из H1 + H2a + `h510` | ✅ условная Lean-теорема | `CanonicalRHRouteSkeleton.lean:131` |
| Theorem510RealZeroBridge | (concrete supplier H2b) | Точный мост Th.5.10: детерминант/самосопряжённость → вещ. нули | 🔓 `H2B_TRANSFORM_LAYER_OPEN`; **на диске только определение, поставщиков ноль** | `CanonicalRHRouteSkeleton.lean:114` |
| SlotAnchor | SLOT-anchor / GATE-G4 | Равенство anchor в z=0; central/raw anchor floor | ✅ **закрыто полностью** | `D0CanonicalApproximation.lean:182` |
| `centeredXi_zero_ne_zero` | часть GATE-G4 | `centeredXi 0 ≠ 0` — ненулевой якорь | ✅ **доказан** (коммит `3df5a887`) | `CenteredXiZeroNonzero.lean:361` |
| SlotS1 | SLOT-S1 / GATE-G5 | Локальная ограниченность (вход Монтеля) | 🔓 сузился до одного входа | `MontelNormalFamilies.lean` |
| `CenteredTrialCriticalMomentRatio` | (единственный вход G5) | Критическое моментное отношение центрированного пробника — из него **одного** производятся и Montel-gate, и ненулевой cluster | 🔓 **единственное, что осталось открыто в G5** | `D0CenteredCriticalMoment.lean:86` |
| `exists_refined_montelAnchorGate_of_criticalMomentRatio` | (потребитель G5) | Ratio ⟹ refined Montel anchor gate | ✅ | `D0CriticalMomentMontelGate.lean:15` |
| `exists_refined_clusterData_of_criticalMomentRatio` | (потребитель G5) | Ratio ⟹ непустой `ClusterData` на уточнении | ✅ | `D0CriticalMomentCanonicalCluster.lean:9` |
| SlotS2 | SLOT-S2 / GATE-G6 | Опознание ненулевого кластера как c·Ξ·γ₀ («главная стена») | 🔓 **не «typed only»**: gauge ✅ + константа ✅, открыта только идентификация | слот `CanonicalRHRouteSkeleton.lean:122` |
| `xiGauge_ne_zero_of_mem_strip` | S2-L2 (gauge) | Калибровка не обращается в ноль на полосе | ✅ | `S2GaugeNonvanishing.lean:34` |
| `limit_at_zero_ne_zero` | S2-L4′ (anchored limit) | Якорная константа `c` предела ненулевая | ✅ | `S2GaugeNonvanishing.lean:101` |
| G7 HURWITZ_XI_RH_ROOF | GATE-G7 | Компилятор: G1..G6 ⟹ RH | ✅ (conditional) | `CanonicalRHRouteSkeleton.lean:145` |
| `selfAdjointCharDetRealZeros` | — | Ядро: нули charполинома эрмитовой матрицы вещественны | ✅ | `aristotle_output/output-final_aristotle/RequestProject/Main.lean:311` |
| `evenNonrealZeroPlant` (R9) | — | Контрпример z²+1: чётность ≠ вещ. нули | ✅ plant | `CanonicalRHRouteSkeleton.lean:194` |
| POISON_MAP_7_FALSE_10_HONEST | — | Карта: 7 ложных-как-сформулировано + 10 честных условных holes в legacy-скелете | ☠️ активна | `ROUTE_B_STATE.md:206` |

> Два кодирования крыши: канон `CanonicalRHRouteSkeleton.lean` (hole-free условный DAG, аксиомы чистые) и legacy design-α `RequestProject/Main.lean` (весь sorry, к нему poison map). Рабочий — канон.

> **Граница G4 снята.** Equality в `z=0`, central/raw anchor floor и `centeredXi 0 ≠ 0` — всё доказано. Пятого фронта G4 не образует, nonzero-cluster supply остаётся в G5 и там сузился до одного входа.

### 4b. Ветка Мюнц — коробка T5 и 4 винта

| Имя (старое) | ID | Человеческим языком | Статус | Где |
|---|---|---|---|---|
| `continued_window_identity_*` (T5) | T-Muntz | Оконное тождество: продолжает окно на Re s>−1/2, окно = ζ·Mellin − Rminus − Rplus | ✅ | `muntz_v3/RequestProject/MuntzV3Unconditional.lean:18` |
| `gwin_analyticOnNhd_…v3Class` | IN-hG | Центральное окно Gwin аналитично | ✅ гол 047 | `MuntzV3GwinExactClass.lean` |
| `rplus_analyticOnNhd_…v3Class` | IN-hRp | Правый (верхний) хвост Rplus аналитичен | ✅ гол 046 | `MuntzV3RplusExactClass.lean` |
| `rminus_analyticOnNhd_…v3Class` | IN-hRm | Левый (нижний) хвост Rminus аналитичен | ✅ 2 авг | `MuntzV3RminusExactClass.lean:178` |
| `habs_of_IccZero_IcoLipschitz` | IN-habs | Абсолютная сходимость / тождество Меллина при Re s>1/2 | ✅ commit-labeled Goal 052 (bus-card отсутствует) | `MuntzV3HabsExactClass.lean:259` |
| `continued_window_identity_v3Class` | (мост) | Финал: разряжает все 4 входа, выдаёт тождество | ✅ commit-labeled Goal 052 (bus-card отсутствует) | `MuntzV3ExactClassClosure.lean:13` |
| PL1 mass-blowup | plant | Фальсификатор: ненулевая масса ⇒ ‖ζ·Mellin‖→∞; ветка держит настоящий witness | ✅ гол 042 | `MuntzV3PL1MassBlowupWitness.lean` |
| PL2 raw-pole | plant | Сырое ζ·Mellin разрывно в 1 (deriv −1/12) ⇒ нужна pole-subtracted версия | ✅ гол 040 | `MuntzV3PL2RawPoleMismatch.lean:13` |
| PL3 triangular Lipschitz | plant | Третий контрактный плант | 🔓 не локализован (Lean-файла нет) | goal 039 текст |
| R6Export | certificate | Запечатанный 7-файловый R6-экспорт (исходный поставщик wrapper-ов, потом обойдён v3-классом) | ✅ sealed | `muntz_v3/RequestProject/R6Export/` |
| v3 class | (класс) | Точный класс носителя: Measurable + supp⊂Icc 0 b + Lipschitz на Ico 0 b + zero-mass + 0≤b | ✅ locked | `MuntzV3ExactClassClosure.lean:13` |
| **K8-контракт** (Мюнц→Галёркин crosswalk) | K8 | Контракт фазы 4B: object-first перекрёстка остатка | ✅ **написан И разряжен безусловно** | `D0PstarMuntzGalerkinResidualCrosswalk.lean:209` |
| мост Мюнц→SLOT-S2 | (промоушен) | Полная S2-стена: каждый ненулевой cluster = c·Ξ·γ₀ с fixed zero-free gauge; нужны same-family, cofinal, normalization и locally-uniform tail control | 🔓 gauge и константа закрыты; идентификация и ребро к `SlotS2` — нет | §5 |

> **Ветка независима от спектральной.** Мюнц даёт аналитическое продолжение (слот S2); H2b даёт спектральную положительность (слот H2b). Разные слоты, разные файлы.

> **Мёртвый груз.** Порт `MuntzV3/` — 14 модулей (056b–056i). Из него файлами `D0Pstar*` потребляются **ровно два имени**: `prolateCombination` и голый `def Gwin`. Вся полезная нагрузка 4/4 — `continued_window_identity*`, `v3Class`, `habs`, `hRm`, `hRp`, `hG` — имеет **ноль ссылок**. Порт купил определение и заранее разложил теоремы для моста, который не написан.

### 4c. Ветка спектр — движок H2b, леммы M0–M4, β-строки

| Имя (старое) | ID | Человеческим языком | Статус | Где |
|---|---|---|---|---|
| CvS Thm 6.1 / 5.6 | (движок) | Простое+чётное нижнее собств. значение ⇒ нули Фурье вещественны | ⏳ (на H2a) | paper arXiv:2511.23257 |
| M0 | L-M0 | Инстанцировать: построить Q(11), вывести β2/β3, построить γ (β1) | 🔓 | не написан |
| M1 | L-M1 | Самосопр. относительно PosDef Q ⇒ вещ. спектр (Q=S², H=SDS⁻¹ эрмитова) | ✅ **в Lean**, sorry-free, коммит `0f2128c7` | `PosDefSelfAdjointRealSpectrum.lean:18` (`posDefSelfAdjoint_exists_hermitian`) |
| M2 | L-M2 | Вырожденная форма → фактор по radical с PosDef-метрикой; здесь входит H2a | 🔓 частичный scaffold | `QuotientByRadicalSelfAdjoint.lean` |
| M3 | L-M3 | Определитель → форма Лагранжа → вещ. корни P(s) | 🔓 | не написан |
| M4 | L-M4 | Фурье + сокращение полюсов + предел Гурвица (для полного двигателя) | 🔓 | не написан |
| β1 | — | Градуирующая инволюция γ (γ²=Id, Qγ=γQ) | 🔓 объекта нет | часть M0 |
| β2 | — | Коммутатор DQ−QD=\|β⟩⟨η\|−\|η⟩⟨β\| | 🧩 принят как `hcomm` | `RankOneCorrectionWeightedSymmetry.lean:32` |
| β3 | — | QDξ=−β | 🧩 принят как `hTDxi` | там же :35 |
| β4 | L-β4 | D′ самосопряжён относительно формы Q (T·D′=D′ᵀ·T) | ✅ | `rankOneCorrection_weightedSymmetric` `…WeightedSymmetry.lean:27` |
| β5a | — | Нормировка ⟨η,ξ⟩=1 ⇒ D′ξ=0 | ✅ | `rankOneCorrection_kills_vector:15` |
| β5b | — | D′ спускается на фактор по ℝ∙ξ (без метрики) | ✅ | `RankOneCorrectionQuotientDescent.lean:29` |
| β5c | — | radical(Q)=ℝ∙ξ (одномерно ⇐ простота) | 🔓 | часть M2 |
| β6 | — | D″ самосопряжён на евклидовом E ⇒ вещ. собств. значения | 🔓 | часть M2 (примитив Mathlib есть; M1 теперь его питает) |
| β7 | — | Треугольный Det(D′−s) = −s·∏(λⱼ−s) | 🔓 | часть M3 |
| β8a/β8b | — | Matrix-det лемма (резольвентная + adjugate форма) | ✅ | `RankOneCorrectionDeterminant.lean:11`, `RankOneCorrectionAllSpectralPoints.lean:82` |
| β8c | — | Свести к Σξⱼ/(s−j)=0, отождествить с P(s) | 🔓 | часть M3 |
| β8d | — | Вещ. собств. значения ⇒ вещ. нули charpoly (для эрмитовой M) | ✅ | `zerosRealOn_of_hermitian_charpoly_mul` `HermitianDeterminantRealZeros.lean:31` |
| β9 | — | Нули Фурье ξ̂ вещественны + предел Гурвица | ⏳ частичный | `periodicScalingDet_zerosRealOn` `HermitianDeterminantRealZeros.lean:12` |
| α4 controls | — | Негативные контроли: без эрмитовости/unit вещественность ломается | ✅ falsifiers | `HermitianDeterminantRealZeros.lean:60,77` |
| гол 051 | G-051 = L-M1 | Формализовать M1 ТОЛЬКО: мост weighted self-adjoint → Hermitian; M0/M2/M3/M4 остаются | ✅ закрыт | `051_*.goal.md`+`.answer.md` |

> **M1 = только мост weighted self-adjoint → Hermitian, питающий β6.** Он теперь **написан**: `Q3/Proofs/RouteB/PosDefSelfAdjointRealSpectrum.lean` создан, sorry-free. β8d уже доказан для эрмитовой матрицы. Это НЕ закрывает H2b: остаются M0, M2, M3 (и M4 для полного корollary). H2b условен на H2a — открыто и у Connes.

### 4d. Забытый инструмент: конечный движок H2a

| Имя | Человеческим языком | Статус | Где |
|---|---|---|---|
| `H2a_SimpleEvenGround_FromPenaltyCoercivity` | Из **одного конечного PSD-сертификата** `K − βG + τ(Gq)(Gq)* ⪰ 0` при `a < β` выдаёт: существование нижнего собств. значения с `λ₁ ≤ a` и минимальностью, **простоту** (эйгенспейс одномерен), **чётность** (всякий нижний вектор `J`-чётный) и **явную щель `λ₂ − λ₁ ≥ β − a`** | ✅ доказано, 0 sorry, конечномерно, базис-инвариантно | `H2aPenaltyCoercivity.lean:395` |
| `SIEG_of_penalty` | Инстанциация движка на семейство: построить `(G_j, K_j, J_j, q_j)` + верифицированный сертификат для каждого `j`, разрядить `RHRoute.supply_H2a` | 🔓 **не написан** — файл сам называет его следующей леммой (строки 430–443) | — |

**Почему это стоит держать на карте.** `SlotH2a` (GATE-G2) — единственный слот крыши, у
которого **ноль поставщиков**. Движок, который выдаёт ровно требуемое (простота + чётность),
у нас доказан и до 2026-08-07 **не был упомянут в этой карте ни разу**. Недостающее звено —
`SIEG_of_penalty`, инстанциация. Сертификат — не аналитика, а конечная матричная проверка
`⪰ 0`: та технология, что отлажена на 054 (Arb-энклоужеры → Lean); Goal 055 (`SectorCell13N2`,
HOLD вне шины) уже спроектирован как импортёр `H2aPenaltyCoercivity`.

**Честные ограничения, файл говорит их сам:** это generic receiver, **не** RH-теорема и
**не** инстанциация Route B; конечномерка — до щели полного оператора дотягиваться через
галёркинский пролёт.

**Внешний контекст (гипотеза о связи, не результат).** В цепи Конна `A ∧ B ∧ C ⇒ RH`
(карта `maps/ROUTEB_CHAIN_LOGIC_2026-08-06.html`, Мифос, пин `6d4dd03`; мостов 4/4, входов
0/3) вход **A** — простота и чётность нижнего состояния формы Вейля — открыт, а щель `Δ_λ`
не оценена ни в одной из шести центральных работ кластера. Форма Вейля на галёркинском
усечении — эрмитова матрица на `2N+1` модах, ровно тот объект, который наша теорема ест.
**Матрицы Конна в оригинале никто из нас не читал, только через пересказ.** Проверка стоит
одну смену; порядок ходов — в развилке `maps/ROUTEB_FORK_2026-08-07_THE_GAP.md` §7.
Анатомия инструмента: `maps/h2a_penalty_coercivity_instrument_anatomy.svg`.

### 4e. Кто есть кто, полномочия и законы

| Имя | Роль | Область | Где |
|---|---|---|---|
| **conductor** (= Claude Code) | Транспорт петли: состояние, коммиты, Aristotle CLI. Математику НЕ решает («красная линия») | CLI Linux/Mac | `orchestrator/CONDUCTOR.md` |
| **Mythos / Fable** | Диспетчер-мозг: выпускает goal'ы, пишет директивы, скорит предсказания. Не судит, не исполняет | claude.ai (браузер, на работе НЕТ GitHub/FS) | `MYTHOS_ORCHESTRATION_ADDENDUM.md` |
| **Proshka** | Судья: read-only, читает зеркало на GitHub, вердикт одним md + коды. Write-доступа нет | ChatGPT Pro (браузер) | `proshka/PROSHKA_SYSTEM_PROMPT_v2.md` |
| **Codex** | Исполнитель: Lean, сертификаты, + git/mirror/MANIFEST после ретайра кондуктора | CLI (gpt-5.6-sol) | `ORG_UPDATE_CONDUCTOR_RETIRED_2026-07-30.md` |
| **Aristotle** | AI-доказатель (облако), дорожка спит пока очередь заблокирована | CLI + dashboard | `orchestrator/ARISTOTLE.md` |
| **Ылша** | Владелец: релеит Прошку, сабмитит Aristotle, держит `PX_RH_CLAIM` | чат | — |

**Полномочия (важно, карта раньше читалась строже, чем правила).**
`mathematical_authority_mode = CODEX_PROSHKA_FULL_EXCEPT_PX_RH_CLAIM`
(`orchestrator/state/CHANNEL_RUNTIME.json`, `orchestrator/state/SPINE_STATE.json`).
То есть **математические решения Codex и Прошка принимают полностью сами**; единственный
owner-гейт — **`PX_RH_CLAIM`, и он `NOT_MADE`**. Отдельно и независимо действует
per-action owner OK на исходящие тексты, коммиты и пуши — это про транспорт, не про
математику.

| Закон | Смысл |
|---|---|
| **CLOSED_GOAL_IMMUTABLE** | Закрытый/выпущенный goal править нельзя — только новый goal |
| **source-lock** | Объект (h, коэффициенты, SHA) жёстко фиксирован; supplier обязан совпадать с точным семейством |
| **taint = 0** | Проверка без побочных допущений — условие приёма сертификата |
| **standard axiom triple** | Аксиомы ровно `propext, Classical.choice, Quot.sound` — никаких проектных |
| **per-action owner OK** | Любой исходящий текст/commit/push ПОКАЗЫВАЕТСЯ владельцу, отправка — только явной командой |
| **PX_RH_CLAIM — единственный owner-гейт** | Заявить RH может только владелец; статус `NOT_MADE` |
| **CHALLENGER / NOT_RH · Bus 010 VOID** | Route B — челленджер, RH не заявляется, промоушен в mainline запрещён |

---

## 5. Цепочка G6/S2 как она есть: снизу вверх

Всё с диска, пин `7dbfb431`.

```
SlotS2 (строгий)                                        `CanonicalRHRouteSkeleton.lean:122`
  ↑  ⛔ СВЯЗИ НЕТ — ни один Lean-файл серии 056 не импортирует SlotS2/ClusterData;
     во всех D0Pstar* `SlotS2` встречается только в комментариях «no SlotS2 claim here»
безусловное затухание нормированного остатка                `D0PstarGalerkinResidualDecay.lean:58`
  ↑ требует ОБЕ посылки
SelectedProjectionTailDecay  ∧  SelectedTrialNormalizerBounded
  ↑ только ЛЕВЫЙ конъюнкт имеет поставщика:
    `D0PstarPhysicalFourierEnergyControl.lean:179`
SelectedPhysicalFourierEnergyControl ∧ SelectedPhysicalBandwidthCofinal   ← ОТКРЫТО
SelectedTrialNormalizerBounded  (`D0PstarGalerkinResidualDecay.lean:42`)  ← ОТКРЫТО, поставщиков НОЛЬ
существование хоть одного ProlateCanonicalSourceData                      ← ОТКРЫТО с 056a
```

**`SelectedTrialNormalizerBounded`** — единственная стена на этой цепочке, к которой **не было
ни одной попытки**: имя встречается ровно трижды, все три раза в собственном файле (`:42`
определение, `:61` гипотеза, `:72` использование). Ни один файл её не производит.

Параллельно закрыто и стоит рядом с цепочкой:
- **полнота базиса** — `D0LogWindowVNMCompletenessBridge.lean`: унитарий `logWindowL2Equiv` (:143), гильбертов базис `V_n_m_hilbertBasis` (:483) и — ключевое — `V_n_m_hilbertBasis_apply` (:491), доказывающее, что базис есть **литеральное производственное семейство**, а не фазово-подкрученный двойник;
- **контракт 4B (K8) разряжен безусловно** — `D0PstarMuntzGalerkinResidualCrosswalk.lean:209`;
- **новые измеримые величины** — физическая угловая частота, энергия коэффициентов, первая опущенная частота: `D0PstarPhysicalFourierEnergyControl.lean:25`, `:47`, `:81`.

---

## 6. Леджер убийств 2026-08-06 (карта обязана это нести)

Одиннадцать вердиктов судьи за сутки, фазы 4B–4L, все с блоком `iteration:`.
Файлы: `proshka/PROSHKA_VERDICT_GOAL056_*_2026-08-06.md`.

### 6.1 Универсальная ∀S-форма затухания — УБИТА ДВАЖДЫ ⛔

Фаза 4I (`…PROLATE_SOURCE_N_COHERENCE…`), заголовок вердикта дословно:

> `# STATUS: OPEN — CURRENT UNIVERSAL TAIL THEOREM SHAPE KILLED; SAME-(m) SOURCE REPAIR SELECTED`

```yaml
CURRENT_UNIVERSAL_TARGET:
  theorem: selectedProjectionTailDecay
  quantifier: "forall S : ProlateCanonicalSourceData"
  fate: KILLED_AS_CURRENT_SOURCE_UNSUPPORTED_THEOREM_SHAPE
  mathematical_negation_proved: false
  classification: OVERSTRONG_AND_UNDERDETERMINED
```

**Оговорка судьи, её нельзя терять: это убийство формы цели, а не опровержение утверждения.**
«The theorem shape is killed as the current production target, not refuted as an abstract
proposition.» Фаза 4L (`…PHYSICAL_FOURIER_ENERGY_RECEIVER…`) подтверждает и обобщает:
`∀S, SelectedProjectionTailDecay S` «not derivable from the current interface. Its negation
has not been proved.»

### 6.2 Контрпример к `PairCofinal` как теореме о полосе

```
m_k = 2^((k+1)²),   N_k = k+1
```

Обе координаты кофинальны, но `N_k / log m_k → 0`. Отсюда: физическая полоса
`physicalFourierBandwidth = 2π(N+1)/L_m` из `PairCofinal` **не следует**, и
**`PairCofinal` — не теорема о полосе**. Определения: `D0PstarPhysicalFourierEnergyControl.lean:47`
(полоса) и `:81` (`SelectedPhysicalBandwidthCofinal`).

**Правило, действующее независимо от всего остального: константа — не расписание.**
Любой численный или Lean-зонд на этом фронте обязан держать `N(m)` с `N/log m → ∞`.
Прогон 2026-08-06 держал `N_BOUND = 120` константой при растущем `m` — условие затухания
было нарушено по построению.

### 6.3 Стоячие запреты (`forbidden_future_move`, по одному на вердикт)

| Фаза | Карточка | Запрещённый ход |
|---|---|---|
| 4B | 056k | `define_or_infer_the_object_residual_from_the_coordinate_difference` |
| 4C | 056l | `duplicate_the_logarithmic_change_of_variables_under_a_new_orientation` |
| 4D | 056m | `replace E_m_N with an isomorphic auxiliary Fourier span` |
| 4E | 056n | `define_the_projected_coordinate_from_rawFplus_or_rewrite_cpow_outside_the_positive_window` |
| 4F | 056o | `define_an_object_coordinate_from_the_desired_scalar_Gwin_or_use_integral_linearity_without_integrability` |
| 4G | 056p | *(разряжен безусловно — K8)* |
| 4H | 056q | `replace_the_literal_residual_by_a_scalar_coordinate_or_reselect_the_sequence` |
| 4I | 056r | `restate_projection_tail_as_source_data_or_reselect_parent_extract` |
| 4J | 056s | `add_V_n_m_completeness_as_source_data_or_choose_target_dependent_weights` |
| 4K | 056t | `postulate_completeness_or_use_an_equivalent_nonliteral_basis` |
| 4L | 056u | `use_projected_energy_or_reselect_parent_extract` |

Человеческим языком: не добавлять желаемый хвост или полноту как поле источника; не
переизбирать расписание/последовательность задним числом; энергия считается на **полном**
объекте, не на проекции; базис — **литеральное** производственное семейство; один транспорт
логарифмической замены на всё, не два под разными ориентациями.

### 6.4 Что судья при этом отказался убивать

Фаза 4F: «Kill full route | Rejected | No sign, type, source, or normalization
contradiction exists.» Фаза 4C: «C — kill the route | Rejected | There is no contradiction.»
Маршрут жив; убиты формы целей, не маршрут.

---

## 7. Реестр голов 001–056 (одна строка = один гол)

Ветки: **roof** (цепь пером/anchor) · **spec** (спектральная лестница) · **Müntz** (v3-supplier) · **meta** (канал/оркестрация).

| Гол | Что закрыл | Ветка |
|---|---|---|
| 001–003 | kTrial: носители → E*-цепь → coefficient-bind заперты | roof |
| 004 | Диагностика: sampled inf>δ без компенсации (S1-gap открыт) | roof |
| 005–006 | Центрированный Pstar + strip-roof; anchor-floor | roof |
| 007–008 | Факторизация до проекции; приёмник anchor-ratio | roof |
| 011 | Source-lock конкретного hTrial | roof/meta |
| 012–013 | Оконный Меллин crosswalk; верхняя кромка (знак не меняется) | spec |
| 014 | Канал Прошки через GitHub настроен | meta |
| 015 | Клон Мюнца из облака — 403 | Müntz |
| 016–017 | Слой пролатов; подготовка порта Мюнца | spec/Müntz |
| 018–021 | Знак полного окна убит фазой (+ dual prolate, coordinate lock, canonical) | spec |
| 022–024 | Адъюдикация кандидатов (всё ещё floor); ladder shift | spec |
| 025–027 | Legendre tail; Λ-bracket; hΛ outer-lobe gate | spec |
| 028–029 | Finite-core theta order; K-эскалация (DualThetaDominance открыт) | spec |
| 030–031 | Отклик полной суммы; band zero убит, priority-budget доказан | spec |
| 032–033 | Реверификация моста; positive-part budget (m=257) | roof/spec |
| 034–035 | Edge-sliver: редукция закрыта, материализация | spec/meta |
| **036** | `CLOSED / ABSORBED_AS_FINITE_SUPPLIER_A_REHEARSAL / NOT_EXECUTED`: поздняя директива 038 запретила исполнять старую формулировку как critical-path goal; конечный harness сохранён только как rehearsal, не cofinal premise | `036_tooth_sign.answer.md` |
| 037 | Müntz R6 harvest + canon sync | Müntz |
| 038 | Scaled outer sign barrier 4/3 — неубедительно | spec/Müntz |
| 038A–039 | v3 семантический аудит; потребление v3, T4a закрыт | Müntz |
| 040 | PL2 raw-pole witness (deriv −1/12) | Müntz |
| 041 | Handover кондуктора → Codex (SUPERSEDED_BY_039) | meta |
| 042 | PL1 mass-blowup witness (mass 1/2) | Müntz |
| 043 | hRm первая попытка — LEAN_BUILD_FAIL | Müntz |
| 044–045 | R6 export + wrapper hRm/hRp под R6-гипотезами | Müntz |
| 046 | **hRp** на точном v3-классе (ратифицирован) ✅ | Müntz |
| 047 | **hG** gwin_entire на v3-классе ✅ | Müntz |
| 048 | habs T2 inventory (import-closure) | Müntz/spec |
| 049 | E* bounded sqrt — fail-closed (b≤0 gap, Lean контрпример) | spec |
| 050 | E* bound repaired (0≤b guard) ✅ | spec |
| **051** | **M1** PosDef-самосопр.⇒вещ.спектр — **Lean написан** ✅ `PosDefSelfAdjointRealSpectrum.lean:18` | spec |
| **052** | **habs** supplier ✅ + **hRm** closed (2 авг) ⇒ Мюнц 4/4 ✅; commit-labeled, отдельная bus-card отсутствует | Müntz |
| **053** | ARSENAL: материализация колоды C01–C12 + KERNEL v3 (байт-точные копии от Fable) ✅ | meta |
| **054** | SectorCell13N2 Phase-0 enclosure-receiver inventory (RULE_INVENTORY_FIRST) — `RECEIVER_PARTIAL` | spec/G2 |
| **054.1** | **G2/CCM owner fork:** cell 13/2 — antipodal class crosswalk, W02 seven-class normal form, prime-kernel seven-class, finite von-Mangoldt weighted sum, nonintegral-constant normal form, seven-class layout consumer, Aristotle receiver journal. `G2_CLOSED: false`, `H2A_CLOSED: false` | spec/G2 |
| **055** | (= 054.2) SectorCell13N2 Lean materialization — **`HOLD`, ратифицирован как черновик ВНЕ шины**; материализуется только после интеграции `ccmCell13N2_wr_enclosures` (054.1-v2). Проектируется как импортёр `H2aPenaltyCoercivity` | spec/G2 |
| **056** | K8 Müntz-v3 → strict SlotS2 bridge — **22 карточки, все CLOSED**, см. подтаблицу ниже | Müntz/roof |

### 7.1 Гол 056 — 22 карточки (все CLOSED)

| Карточка | Фаза | Что закрыла |
|---|---|---|
| `056_k8` | 0 | K8 Müntz-v3 → strict SlotS2 bridge, раскладка |
| `056a` | 1 | XW.8 prolate→kTrial provenance contract |
| `056b` | 2 | Müntz-v3 production export closure audit |
| `056c` | 3A | Müntz-v3 production core Batch A |
| `056d` | 3B | production supplier Batch B |
| `056e` | 3C | production supplier Batch C |
| `056f` | 3D | production supplier Batch D |
| `056g` | 3E | production supplier Batch E |
| `056h` | 3F | production supplier Batch F |
| `056i` | 3G | production receiver Batch G |
| `056j` | 4A | D0 Pstar → Müntz centered coordinate lock (XW.6) |
| `056k` | 4B | named object-first Galerkin residual contract |
| `056l` | 4C | логарифмический транспорт меры + ортонормальность мод |
| `056m` | 4D | конечная ортогонально-проекционная реконструкция |
| `056n` | 4E | selected projected Mellin coordinate |
| `056o` | 4F | full Mellin/Gwin crosswalk |
| `056p` | 4G | residual Mellin linearity + **разрядка контракта (K8)** |
| `056q` | 4H | selected residual L² decay, двухпосылочный ресивер |
| `056r` | 4I | prolate source N-coherence repair — **⛔ убийство ∀S-формы** |
| `056s` | 4J | generic Hilbert-basis weighted tail |
| `056t` | 4K | literal `V_n_m` completeness bridge |
| `056u` | 4L | selected physical Fourier-energy receiver — **⛔ второе убийство ∀S-формы** |

Пропуски: гол 009 не локализован; гол 010 = намеренно void bus-slot (`BUS_010: VOID`).

---

## 8. Pinned-валидация Müntz и статус журнала

По pinned-source + committed-validation-ledger audit Müntz-ветка = **4/4**: `hRm` закрыт commit-ом `d3ca3c9e`, а `habs` и exact-class assembly — commit-ом `79d80630` (commit-labeled Goal 052; отдельной пары `052_*.goal.md` / `052_*.answer.md` в `MANIFEST.md` нет). На точке закрытия зафиксирован full standalone v3 build на **8050 jobs**, production hole scan пуст, project axioms отсутствуют; четыре public declaration зависят только от стандартных `propext`, `Classical.choice`, `Quot.sound`. Иными словами: `sorry`/`admit`-free — YES; project-axiom-free — YES; literally axiom-free — NO; standard Lean axioms only — YES. Локальный `lake build` в этой сессии не перезапускался. Журнал впоследствии догнан Linux-коммитом.

**Верификация Мифоса (2026-08-03, @807341e7):** независимо прочитал MAP.md против репо, грепнул
`sorry/axiom` в Lean-файлах hRm/habs → **Müntz 4/4 подтверждён вторым каналом**; line-refs словаря
(§4) сошлись; «расхождений сверх §6 не найдено». Его 4 карты — в `maps/` (`2026-08-03_*`). Его
FLAG-зеркало устранён: `docs/routeB_bus/muntz_v3/RequestProject` досинхронизирован с каноном
(31=31 файлов, Rminus/Habs/Closure теперь видны Прошке).

**Долги по контуру на 2026-08-07** (не математика, но без этого знание снова разъедется):
`S2GaugeNonvanishing.lean` — единственный роф-смежный файл **без `#print axioms`**, чистота
держится на сообщении коммита `bb0e1d2b`; `orchestrator/state/CHANNEL_RUNTIME.json` отстаёт
на три фазы (`last_boundary_id` = 4I при закрытых 4J/4K/4L), и три несовместимых счётчика
вызовов к судье (рантайм 9, карточка 056u 12, бриф Мифоса 7).

---

## 8b. Маршрут 058 — `REALZERO_GROUND_DIAGONAL_TO_XI` (заведён 2026-08-12)

Этот раздел добавлен позже остальных и **старше их по приоритету**: он объявляет, какая
именно последовательность несёт оба нужных свойства. Фронты §9 — узлы внутри него.

**Устав:** `058_realzero_ground_diagonal_to_xi.goal.md`
**Источник:** `proshka/PROSHKA_MASTER_ROUTE_REALZERO_GROUND_DIAGONAL_TO_XI_2026-08-11.md`, пин `b124fba1`
**Цепь в базе:** `REALZERO_GROUND_DIAGONAL_TO_XI` · мигратор `orchestrator/kb_migrate_route058.py`

**Несущий инвариант — нарушение останавливает гол.** Последовательность одна:

```
G_j  transform конечного ground-вектора   несёт ВЕЩЕСТВЕННОСТЬ НУЛЕЙ
T_j  transform пролатного пробника        несёт СХОДИМОСТЬ к Ξ
мост переносит СХОДИМОСТЬ на G_j — не вещественность на T_j
```

Обратное направление невозможно, а не трудно: вещественность нулей неустойчива к
возмущению (`z² + ε` — два вещественных нуля при `ε<0`, сопряжённая пара при `ε>0`).
Гурвиц читает нули **предела**. Цепь «trial сходится, ground вещественен, значит RH»
использует две разные семьи и **запрещена** — `STOP: TWO_DIFFERENT_FAMILIES_USED`.

```
G0 объект/координата/нормировка  →  G1 ground-пакет  →  G2 вещественные нули многочлена
   →  G2b перенос множества нулей  →  F_j целая, нули вещественны
   →  G3 та же F_j отслеживает trial  →  G3c  →  G4 Lemma 7.3  →  F_j → Ξ
   →  G5 zero-escape  →  RH
```

Статусы **не дублируются здесь** — они протухают. Живое: `brief.py`, `cheap.py`,
`kb_migrate_route058.py --check`.

**Дешёвый следующий шаг:** `G2b`, теорема `Proposition59GroundLagrangeZeroSetBridge` —
перенос множества нулей с многочлена на преобразование той же строки. Схема из семи шагов в
уставе; все объекты в дереве; судейского решения не требует.

**Убито и не подлежит возврату:** `Pstar = c_N · многочлен` (у преобразования бесконечно
много нулей на синус-решётке, у многочлена конечное число) · `exact ground equals trial` ·
артефакты GLOWER как поставщик odd-блока до леммы-моста компрессии.

---

## 9. Куда смотреть дальше (4 открытых фронта)

| Фронт | Что закрыть | Готовность |
|---|---|---|
| **G2 / H2a** | Простое+чётное нижнее собств. значение (SIMPLE_EVEN) для слота | 🔓 у слота **ноль поставщиков**, но конечный движок `H2aPenaltyCoercivity.lean:395` доказан; недостаёт `SIEG_of_penalty` — инстанциации на семейство. Это самый дешёвый ход на карте |
| **G3 / concrete H2b supplier** | M0 + M2 + M3 и при необходимости M4 → `Theorem510RealZeroBridge` | 🔓 `selectedFamily_realZeros` уже ✅ conditional; **M1 закрыт в Lean** (гол 051); у `Theorem510RealZeroBridge` на диске **ноль поставщиков** |
| **G5 / concrete S1/Montel supply** | Один вход: `CenteredTrialCriticalMomentRatio` | 🔓 из него **одного** уже выведены и Montel-gate (`D0CriticalMomentMontelGate.lean:15`), и ненулевой cluster (`D0CriticalMomentCanonicalCluster.lean:9`). Самый узкий фронт |
| **G6 / полная S2-стена Мюнц→S2** | Идентификация `D.limit = c·Ξ·γ` + связка цепочки `D0Pstar*` со `SlotS2` | 🔓 gauge ✅ и ненулевая константа ✅ (`S2GaugeNonvanishing.lean:34,101`), K8-контракт разряжен ✅; открыты `SelectedTrialNormalizerBounded` (поставщиков ноль), физический хвост/полоса и существование `ProlateCanonicalSourceData`; ребра к `SlotS2` нет |

**Чего НЕ делать (из §6):** не пытаться доказывать `∀S`-форму `SelectedProjectionTailDecay`
— убита дважды, с контрпримером; не выводить полосу из `PairCofinal`; не гонять численные
зонды с фиксированным `N`; не считать энергию на проекции; не постулировать полноту и не
подменять базис нелитеральным; не трогать G2/CCM — там owner fork, нужны данные владельца
(семь относительных WR-неравенств на представителях (−2,−2), (−2,−1), (−2,0), (−2,1),
(−1,−1), (−1,0), (0,0)), а не решение исполнителя.

*Граница гола 051: `Q3/Proofs/RouteB/PosDefSelfAdjointRealSpectrum.lean` материализует только
M1 (weighted-self-adjoint → Hermitian bridge); это не закрытие CvS §5, H2b, H2a, Route B или RH.*

*Route B остаётся `CHALLENGER / NOT_RH`. `BUS_010: VOID` · `GOAL_055: HOLD` ·
`PX_RH_CLAIM: NOT_MADE`. RH не заявляется.*
