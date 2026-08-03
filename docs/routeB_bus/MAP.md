# MAP.md — Единая карта Route B (навигатор проекта)

*Живой файл. Одна точка правды для имён и статусов. Обновляется после каждого хода.*
Последняя картография: 2026-08-03 (4 агента-картографа прочитали крышу / Мюнц / спектр / шину).
Route B = **CHALLENGER / NOT_RH**, Bus 010 VOID. RH официально НЕ заявлена.

Легенда статусов: ✅ доказано (Lean) · ⏳ условно/kill-pass (ещё не Lean) · 🔓 открыто · ☠️ poisoned (легально только после закрытия подпорки) · 🧩 принято как гипотеза (не выведено).

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
   ┌────────────┬──────────────┼───────────────┬────────────────┐
  G1 H1 ✅     G4 anchor ✅   G5 S1 🔓        G2→G3 (H2a→H2b)    G6 S2 🔓
 (голоморфн.) (нормировка)  (Montel+знак)   ВЕТКА «СПЕКТР»      ВЕТКА «МЮНЦ»
                              знак-supplier   движок нулей       коробка T5
                              открыт           🔓                 4 винта ✅ 4/4
                                                │                  но стыковка
                                          H2a 🔓 → H2b ⏳          к S2 🔓
                                                │
                                          M1(гол 051)⏳→M2→M3→M4 (+M0)
```

**Где мы сейчас (одной строкой):** закрыты G1, G4, G7 и все 4 винта Мюнца; открыты **4 фронта** — G2 (H2a), G3 (H2b, туда идёт M1), G5 (S1-знак), G6 (стыковка Мюнц→S2). Следующий ход: дать OK Codex'у на Lean-файл M1 (гол 051).

**Две ветки простыми словами:**
- **Спектр (H2-ветка):** движок «почему нули вещественны». Упирается в H2a (простое+чётное нижнее собств. значение) → выдаёт H2b. Кирпичи — M1..M4.
- **Мюнц:** коробка `T5` даёт аналитическое продолжение окна. 4 входа-винта **все закручены (4/4)**. Осталось формально вставить её результат в слот S2 крыши.

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
T-Roof  rh_of_canonical_strip_slots  ⏳ (собрана, условна на G1..G6)
│
├─ GATE-G1  SLOT-H1   голоморфность семейства на полосе            ✅
├─ GATE-G4  SLOT-anchor  нормировка Hⱼ(i/4)=Ξ(i/4)≠0               ✅
├─ GATE-G7  компилятор G1..G6 ⟹ RH (Hurwitz)                      ✅ (conditional)
│
├─ GATE-G5  SLOT-S1   локальная ограниченность (вход Монтеля)      🔓  ядро Montel ✅, знак-supplier открыт
│
├─ ВЕТКА СПЕКТР ────────────────────────────────────────────────
│   ├─ GATE-G2  SLOT-H2a  нижнее собств. значение простое+чётное   🔓  (открыто и у Connes)
│   └─ GATE-G3  SLOT-H2b  у каждого Hⱼ только вещественные нули     ⏳  условно на H2a
│        └─ мост Theorem510RealZeroBridge (H2B_TRANSFORM_LAYER)    🔓  ← сюда входит движок M1..M4
│             ├─ L-M0  инстанцировать форму Q(11), вывести β1/β2/β3 🔓
│             ├─ L-M1  PosDef-самосопр. ⇒ вещ. спектр (гол 051)     ⏳  Прошка kill-pass, Lean не написан
│             ├─ L-M2  вырожденная форма → фактор с PosDef-метрикой 🔓  частичный scaffold есть
│             ├─ L-M3  определитель → форма Лагранжа → вещ. корни   🔓
│             └─ L-M4  Фурье + сокращение полюсов + Гурвиц (опция)  🔓
│
└─ ВЕТКА МЮНЦ ──────────────────────────────────────────────────
    └─ GATE-G6  SLOT-S2  опознание кластера как c·Ξ·γ₀ (главная стена) 🔓 typed only
         └─ коробка T-Muntz (T5 shell, window identity)             ✅ доказана
              ├─ IN-hG   окно Gwin аналитично                       ✅ (гол 047)
              ├─ IN-hRp  правый хвост Rplus аналитичен              ✅ (гол 046)
              ├─ IN-hRm  левый хвост Rminus аналитичен              ✅ (2 авг, MacOS)
              ├─ IN-habs абсолютная сходимость / тождество Меллина   ✅ (гол 052, 3 авг, MacOS)
              └─ мост Мюнц→SLOT-S2 (промоушен, «C3»)                🔓 K8: контракт не написан
```

**Открытые фронты (ровно 4):** G2 (H2a) · G3/движок (M0,M1,M2,M3,M4) · G5 (S1-знак) · G6 (стыковка Мюнц→S2).

---

## 4. Словарь-переводчик (что за буква = что человеческим языком)

### 4a. Крыша — слоты, ворота, supply-узлы

| Имя (старое) | ID | Человеческим языком | Статус | Где |
|---|---|---|---|---|
| `rh_of_canonical_strip_slots` | T-Roof | Итоговая крыша: из слотов+мостов собирает RH на полосе | ⏳ | `Q3/Proofs/RouteB/CanonicalRHRouteSkeleton.lean:145` |
| SlotH1 | SLOT-H1 / GATE-G1 | Голоморфность нормированного семейства | ✅ | `D0CanonicalApproximation.lean` |
| SlotH2a | SLOT-H2a / GATE-G2 | Нижнее собств. значение простое, изолированное, чётное (ВХОД, не теорема) | 🔓 | `SectorIsolationRadius.lean`; slot `CanonicalRHRouteSkeleton.lean:52` |
| SlotH2b | SLOT-H2b / GATE-G3 | У каждого Hⱼ только вещественные нули на полосе | ⏳ (на H2a) | slot `CanonicalRHRouteSkeleton.lean:130` |
| Theorem510RealZeroBridge | (мост H2b) | Точный мост Th.5.10: детерминант/самосопряжённость → вещ. нули | 🔓 `H2B_TRANSFORM_LAYER_OPEN` | `CanonicalRHRouteSkeleton.lean:114` |
| SlotAnchor | SLOT-anchor / GATE-G4 | Нормировка семейства в i/4 (защита от коллапса лимита) | ✅ | `D0AnchorFloor.lean` |
| SlotS1 | SLOT-S1 / GATE-G5 | Локальная ограниченность (вход Монтеля); знак-supplier открыт | 🔓 | `MontelNormalFamilies.lean` |
| SlotS2 | SLOT-S2 / GATE-G6 | Опознание ненулевого кластера как c·Ξ·γ₀ («главная стена») | 🔓 typed only | slot `CanonicalRHRouteSkeleton.lean:122` |
| G7 HURWITZ_XI_RH_ROOF | GATE-G7 | Компилятор: G1..G6 ⟹ RH | ✅ (conditional) | `CanonicalRHRouteSkeleton.lean:145` |
| `selfAdjointCharDetRealZeros` | — | Ядро: нули charполинома эрмитовой матрицы вещественны | ✅ | `RequestProject/Main.lean:311` |
| `evenNonrealZeroPlant` (R9) | — | Контрпример z²+1: чётность ≠ вещ. нули | ✅ plant | `CanonicalRHRouteSkeleton.lean:194` |
| POISON_MAP_7_FALSE_10_HONEST | — | Карта: 7 ложных-как-сформулировано + 10 честных условных holes в legacy-скелете | ☠️ активна | `ROUTE_B_STATE.md:180` |

> Два кодирования крыши: канон `CanonicalRHRouteSkeleton.lean` (hole-free условный DAG, аксиомы чистые) и legacy design-α `RequestProject/Main.lean` (весь sorry, к нему poison map). Рабочий — канон.

### 4b. Ветка Мюнц — коробка T5 и 4 винта

| Имя (старое) | ID | Человеческим языком | Статус | Где |
|---|---|---|---|---|
| `continued_window_identity_*` (T5) | T-Muntz | Оконное тождество: продолжает окно на Re s>−1/2, окно = ζ·Mellin − Rminus − Rplus | ✅ | `muntz_v3/RequestProject/MuntzV3Unconditional.lean:18` |
| `gwin_analyticOnNhd_…v3Class` | IN-hG | Центральное окно Gwin аналитично | ✅ гол 047 | `MuntzV3GwinExactClass.lean` |
| `rplus_analyticOnNhd_…v3Class` | IN-hRp | Правый (верхний) хвост Rplus аналитичен | ✅ гол 046 | `MuntzV3RplusExactClass.lean` |
| `rminus_analyticOnNhd_…v3Class` | IN-hRm | Левый (нижний) хвост Rminus аналитичен | ✅ 2 авг | `MuntzV3RminusExactClass.lean:178` |
| `habs_of_IccZero_IcoLipschitz` | IN-habs | Абсолютная сходимость / тождество Меллина при Re s>1/2 | ✅ гол 052 | `MuntzV3HabsExactClass.lean:259` |
| `continued_window_identity_v3Class` | (мост) | Финал: разряжает все 4 входа, выдаёт тождество | ✅ гол 052 | `MuntzV3ExactClassClosure.lean:13` |
| PL1 mass-blowup | plant | Фальсификатор: ненулевая масса ⇒ ‖ζ·Mellin‖→∞; ветка держит настоящий witness | ✅ гол 042 | `MuntzV3PL1MassBlowupWitness.lean` |
| PL2 raw-pole | plant | Сырое ζ·Mellin разрывно в 1 (deriv −1/12) ⇒ нужна pole-subtracted версия | ✅ гол 040 | `MuntzV3PL2RawPoleMismatch.lean:13` |
| PL3 triangular Lipschitz | plant | Третий контрактный плант | 🔓 не локализован (Lean-файла нет) | goal 039 текст |
| R6Export | certificate | Запечатанный 7-файловый R6-экспорт (исходный поставщик wrapper-ов, потом обойдён v3-классом) | ✅ sealed | `muntz_v3/RequestProject/R6Export/` |
| v3 class | (класс) | Точный класс носителя: Measurable + supp⊂Icc 0 b + Lipschitz на Ico 0 b + zero-mass + 0≤b | ✅ locked | `MuntzV3ExactClassClosure.lean:13` |
| мост Мюнц→SLOT-S2 | (промоушен) | Формальная вставка window-identity в слот S2 крыши | 🔓 K8: контракт не написан | — |

> **Ветка независима от спектральной.** Мюнц даёт аналитическое продолжение (слот S2); H2b даёт спектральную положительность (слот H2b). Разные слоты, разные файлы.

### 4c. Ветка спектр — движок H2b, леммы M0–M4, β-строки

| Имя (старое) | ID | Человеческим языком | Статус | Где |
|---|---|---|---|---|
| CvS Thm 6.1 / 5.6 | (движок) | Простое+чётное нижнее собств. значение ⇒ нули Фурье вещественны | ⏳ (на H2a) | paper arXiv:2511.23257 |
| M0 | L-M0 | Инстанцировать: построить Q(11), вывести β2/β3, построить γ (β1) | 🔓 | не написан |
| M1 | L-M1 | Самосопр. относительно PosDef Q ⇒ вещ. спектр (Q=S², H=SDS⁻¹ эрмитова) | ⏳ Прошка kill-pass, Lean нет | гол 051 |
| M2 | L-M2 | Вырожденная форма → фактор по radical с PosDef-метрикой; здесь входит H2a | 🔓 частичный scaffold | `QuotientByRadicalSelfAdjoint.lean` |
| M3 | L-M3 | Определитель → форма Лагранжа → вещ. корни P(s) | 🔓 | не написан |
| M4 | L-M4 | Фурье + сокращение полюсов + предел Гурвица (для полного двигателя) | 🔓 | не написан |
| β1 | — | Градуирующая инволюция γ (γ²=Id, Qγ=γQ) | 🔓 объекта нет | часть M0 |
| β2 | — | Коммутатор DQ−QD=|β⟩⟨η|−|η⟩⟨β| | 🧩 принят как `hcomm` | `RankOneCorrectionWeightedSymmetry.lean:32` |
| β3 | — | QDξ=−β | 🧩 принят как `hTDxi` | там же :35 |
| β4 | L-β4 | D′ самосопряжён относительно формы Q (T·D′=D′ᵀ·T) | ✅ | `rankOneCorrection_weightedSymmetric:27` |
| β5a | — | Нормировка ⟨η,ξ⟩=1 ⇒ D′ξ=0 | ✅ | `rankOneCorrection_kills_vector:15` |
| β5b | — | D′ спускается на фактор по ℝ∙ξ (без метрики) | ⏳ частичный | `RankOneCorrectionQuotientDescent.lean:29` |
| β5c | — | radical(Q)=ℝ∙ξ (одномерно ⇐ простота) | 🔓 | часть M2 |
| β6 | — | D″ самосопряжён на евклидовом E ⇒ вещ. собств. значения | 🔓 | часть M2 (примитив Mathlib есть) |
| β7 | — | Треугольный Det(D′−s) = −s·∏(λⱼ−s) | 🔓 | часть M3 |
| β8a/β8b | — | Matrix-det лемма (резольвентная + adjugate форма) | ✅ | `RankOneCorrectionDeterminant.lean:11`, `…AllSpectralPoints.lean:82` |
| β8c | — | Свести к Σξⱼ/(s−j)=0, отождествить с P(s) | 🔓 | часть M3 |
| β8d | — | Вещ. собств. значения ⇒ вещ. нули charpoly (для эрмитовой M) | ⏳ нужен мост M1 | `zerosRealOn_of_hermitian_charpoly_mul` `HermitianDeterminantRealZeros.lean:31` |
| β9 | — | Нули Фурье ξ̂ вещественны + предел Гурвица | ⏳ частичный | `periodicScalingDet_zerosRealOn:12` |
| α4 controls | — | Негативные контроли: без эрмитовости/unit вещественность ломается | ✅ falsifiers | `HermitianDeterminantRealZeros.lean:60,77` |
| гол 051 | G-051 = L-M1 | Формализовать M1 ТОЛЬКО (β6/β8d); M0/M2/M3/M4 остаются | ⏳ | `051_*.goal.md`+`.answer.md` |

> **M1 = только β6/β8d.** Гол 051 не закрывает H2b (нужны ещё M0, M2, M3). H2b условен на H2a — открыто и у Connes. Целевой Lean-файл `Q3/Proofs/RouteB/PosDefSelfAdjointRealSpectrum.lean` ещё НЕ создан.

### 4d. Кто есть кто + законы

| Имя | Роль | Область | Где |
|---|---|---|---|
| **conductor** (= Claude Code) | Транспорт петли: состояние, коммиты, Aristotle CLI. Математику НЕ решает («красная линия») | CLI Linux/Mac | `orchestrator/CONDUCTOR.md` |
| **Mythos / Fable** | Диспетчер-мозг: выпускает goal'ы, пишет директивы, скорит предсказания. Не судит, не исполняет | claude.ai (браузер, на работе НЕТ GitHub/FS) | `MYTHOS_ORCHESTRATION_ADDENDUM.md` |
| **Proshka** | Судья: read-only, читает зеркало на GitHub, вердикт одним md + коды. Write-доступа нет | ChatGPT Pro (браузер) | `proshka/PROSHKA_SYSTEM_PROMPT_v2.md` |
| **Codex** | Исполнитель: Lean, сертификаты, + git/mirror/MANIFEST после ретайра кондуктора | CLI (gpt-5.6-sol) | `ORG_UPDATE_CONDUCTOR_RETIRED_2026-07-30.md` |
| **Aristotle** | AI-доказатель (облако), дорожка спит пока очередь заблокирована | CLI + dashboard | `orchestrator/ARISTOTLE.md` |
| **Ылша** | Владелец: релеит Прошку, сабмитит Aristotle, последнее слово | чат | — |

| Закон | Смысл |
|---|---|
| **CLOSED_GOAL_IMMUTABLE** | Закрытый/выпущенный goal править нельзя — только новый goal |
| **source-lock** | Объект (h, коэффициенты, SHA) жёстко фиксирован; supplier обязан совпадать с точным семейством |
| **taint = 0** | Проверка без побочных допущений — условие приёма сертификата |
| **standard axiom triple** | Аксиомы ровно `propext, Classical.choice, Quot.sound` — никаких проектных |
| **per-action owner OK** | Любой исходящий текст/commit/push ПОКАЗЫВАЕТСЯ владельцу, отправка — только явной командой |
| **CHALLENGER / NOT_RH · Bus 010 VOID** | Route B — челленджер, RH не заявляется, промоушен в mainline запрещён |

---

## 5. Реестр голов 001–052 (одна строка = один гол)

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
| 036 | Tooth-sign сертификат (goal issued, answer не найден) | spec |
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
| **051** | **M1** PosDef-самосопр.⇒вещ.спектр — Прошка kill-pass, Codex authorized ⏳ | spec |
| **052** | **habs** supplier ✅ + **hRm** closed (2 авг) ⇒ Мюнц 4/4 ✅ | Müntz |

Пропуски: гол 009 не локализован; гол 010 = намеренно void bus-slot.

---

## 6. Рассинхрон журнала (важно)

На **диске (HEAD)** Мюнц-ветка = **4/4** (hRm 2 авг, habs гол 052 3 авг, коммиты [MacOS]). Но `ROUTE_B_STATE.md` goal-log **обрывается на 051** — строки hRm-close и гол 052 в него ещё не внесены. То есть **математика на диске впереди журнала**. Полная сборка (`lake build`) в этой сессии не перепроверялась — на диске чисто (sorry/axiom = 0), но зелёный билд стоит подтвердить перед любым промоушеном.

**TODO журнала:** внести в `ROUTE_B_STATE.md` строки для hRm-close и гола 052 (с проверкой билда).

**Верификация Мифоса (2026-08-03, @807341e7):** независимо прочитал MAP.md против репо, грепнул
`sorry/axiom` в Lean-файлах hRm/habs → **Müntz 4/4 подтверждён вторым каналом**; line-refs словаря
(§4) сошлись; «расхождений сверх §6 не найдено». Его 4 карты — в `maps/` (`2026-08-03_*`). Его
FLAG-зеркало устранён: `docs/routeB_bus/muntz_v3/RequestProject` досинхронизирован с каноном
(31=31 файлов, Rminus/Habs/Closure теперь видны Прошке).

---

## 7. Куда смотреть дальше (4 открытых фронта)

| Фронт | Что закрыть | Готовность |
|---|---|---|
| **G3 / движок H2b** | L-M1 (гол 051) → Lean-файл | ⏳ вооружён: Прошка одобрила, директива Codex готова, ждёт OK |
| **G2 / H2a** | Простое+чётное нижнее собств. значение (SIMPLE_EVEN) | 🔓 настоящая открытая математика (открыто и у Connes); дозье собрано |
| **G6 / стыковка Мюнц→S2** | Формальный мост window-identity → SlotS2 | 🔓 supplier готов 4/4, контракт промоушена не написан (K8) |
| **G5 / S1-знак** | Знак-supplier для Монтеля | 🔓 ядро Montel ✅, знак открыт |

*Ближайший конкретный ход: OK Codex'у на Lean M1 (гол 051), целевой файл `Q3/Proofs/RouteB/PosDefSelfAdjointRealSpectrum.lean`.*
