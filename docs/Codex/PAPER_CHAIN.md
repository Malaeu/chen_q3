# Бумажная цепь до RH — что закрыто на бумаге, что открыто

Собрано 2026-09-25 (Claude Code, owner order) из: Goal058, `ROUTE058_GATE_CONTRACTS.md`,
`PROSHKA_MASTER_ROUTE_REALZERO_GROUND_DIAGONAL_TO_XI_2026-08-11.md`, reviewed note Fokas 22.09,
`REPORT_2026-09-22_FOKAS_RMINUS_CROSSWALK.md`, Fokas-запрос 23.09, `RECHECKABLE_RESEARCH_DEBTS.json`,
CCM arXiv:2511.22755. Правится при каждом закрытом звене (см. `NEXT.md`, «Конец фазы»).

Крыша: `Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi` — одна семья F с hzeros, hentire, hconv ⇒ RH.
F = selected Ferrers tracked ground transform вдоль одного tail reindex, c = 2πm, m = N = k+2.
Несущий инвариант: одна и та же F везде (`STOP: TWO_DIFFERENT_FAMILIES_USED`).

Статусы бумаги: PAPER_PUBLISHED (статья) · PAPER_OWN (наш текст; «rev» = проверен независимо) ·
PROSHKA_ONLY (вердикт без перепроверки) · LEAN (доказано в Lean = закрыто и на бумаге) · OPEN.

| Звено | Что утверждается | Объект = F? | Бумага | Lean |
|---|---|---|---|---|
| G0 | объект, координата s = −Lz/2π, нормировка, расписание m=N=k+2 | F | OPEN частично: нормировка в контрактах «не закреплена» (contracts:64) | семья определена в TailReindex |
| G1 · hfloorEv | trial-complement floor ≥ β eventually | F | **OPEN** (DB:203-207: KILLED_RECHECKABLE, не опровергнуто) | условный приёмник есть |
| G1 · hratioEv | residualEnergy/β² < 1 eventually | F | **OPEN** (DB:294-296) | условный приёмник есть |
| G1 · hoddEv | нечётный floor β₀‖x‖² ≤ Re⟨x,(K−a)x⟩ | F | **OPEN как факт семьи; производен при независимом hfloorEv и odd mass < 1/2** (мост ниже). Действующие поставщики hfloorEv используют hoddEv, поэтому их нельзя замкнуть этим мостом. | условный приёмник есть |
| G2 | нули лагранжева многочлена строки вещественны | строка F | закрыто через Lean, условно на G1 | LEAN `CCMFiniteWeilParity.lean:161` |
| G2b | перенос вещественности на Prop-5.9 transform той же строки | F | закрыто через Lean (контракты устарели) | LEAN `Proposition59GroundLagrangeZeroSetBridge.lean:231` |
| hentire | каждая F k целая | F | закрыто через Lean | LEAN `G6N1SelectedFerrersTrackedGroundTransform.lean:761` |
| G3 | та же F трекает projected trial: нормировка × kernelL2 × √ratio → 0 на компактах | F | **OPEN — главная стена, RH-уровень** (master:1278). Прогресс: paired-window тождество PAPER_OWN rev — только представление, не оценка (FN:91-92) | нет формулировки |
| hmode | sup‖w_m − D_n‖ ≤ C_n/m, центр-нормировка 1/h0(0), 3/h4(0) | F | **PAPER_OWN rev + PROSHKA PROVED_PAPER** для выбранных мод 0/4 и полного окна; независимая сверка пакета и цепи 25.09. Формальная реализация источника не сертифицирована. | hmode⇒W5/N2 в кандидате; сам hmode не Lean |
| hχ / hθ | из hmode | F | **PAPER_OWN rev** как следствия проверенной hmode-цепи | hχ кандидат; формализация следствий не завершена |
| G3c | projected trial → continuum trial (projection tail) | trial | **OPEN** («PROSE проекционный хвост», contracts:267,280) | нет |
| G4 | CCM Lemma 7.3: преобразование k_λ → Ξ равномерно на полосах | trial | **PAPER_PUBLISHED** arXiv:2511.22755 §7, Lemma 7.3, p.31 (препринт); crosswalk h_λ ↔ hTrial_m OPEN (master:994-1004) | импорт отсутствует |
| G5 | одна семья: вещественные нули + F → Ξ ⇒ RH (Гурвиц) | F | закрыто через Lean | LEAN `Goal058DirectGroundZeroEscape.lean:27`, аксиомы 3 (проверено 25.09) |
| Сборка | tail reindex + G3 + G3c + G4 ⇒ hconv для той же F | F | **OPEN** | нет |

Итого 14 звеньев: закрыто на бумаге 7 (G2, G2b, hentire, G5 — Lean; G4 — статья; hmode и hχ/hθ — проверенная бумага),
открыто 7 (G0 частично, hfloorEv и hratioEv плюс производный hoddEv в G1,
G3, G3c, сборка) + crosswalk для G4.

## Главное наблюдение
Сами Connes–Consani–Moscovici в §8 arXiv:2511.22755 (p.32) называют ровно два недостающих шага своей программы:
«prove that its smallest eigenvalue … is simple and that its corresponding eigenvector ξλ is even» — это наш G1;
«establish that kλ provides a sufficiently accurate approximation to (a scalar multiple of) ξλ» — это наш G3 (+G3c).
Сопоставление с нашими объектами — вывод читателя, crosswalk матриц не записан. Значит: G1 и G3 — ядро RH,
всё остальное — сантехника цепи.

## Проверенный hmode, открытые звенья и следующий ход

**hmode (бумага закрыта).** Прошка проверила точный пакет
`PROSHKA_REQUEST_HMODE_QUASIMODE_20260922.txt` (SHA-256 `377af64b2e9df0689f8f55f8e3c64dc46bf00b5584df42ed2a725e6f1a311bb2`)
и дала `PROVED_PAPER` для полного окна выбранных Ferrers-мод 0/4; ответ в существующем
[чате Прошки](https://chatgpt.com/g/g-p-6aafae55d09481919c5971b73d862184-sort-rh-marz-2026/c/6aafb38a-a7a4-83eb-9940-84a574eae168),
message `f31e0cc4-f520-4aa5-84c5-fb0dc0c55e5b`. Независимая сверка не нашла первого неверного
перехода в form core → carrier → even gap → quasimode → Fourier upgrade → center anchor;
спектральный зазор выведен до hχ, без круга. Исходная бумажная сборка: RPT:1120-1220.
Это не Lean-подтверждение естественной спектральной реализации, не CCM-floor и не RH.

**G4 crosswalk + G3c (сантехника, своими силами).** Нужно: h_λ ↔ hTrial_m, скаляр и фаза, C = 2πλ², координата
преобразования (master:994-1004); отдельно доказать projection tail (master:1222). Своя попытка на бумаге.

**G1 · независимый hfloorEv.** Нужен положительный trial-complement floor с одним `β>0`
на выбранном кофинальном хвосте и при точном Rayleigh-сдвиге. Действующие пути через секторные floors
уже требуют hoddEv: их обратная подстановка в мост ниже циклична. Ищем прямую коэрцитивность полного
дополнения либо signed head-tail Feshbach с положительным Schur-запасом (DB:203-207).

**Бумажная атака на FLOOR, остановка 25.09.** Фиксируем один
`P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData` и его уже выбранный tail shift
`φ_P(j)=preAnchorTailStart(P)+j`; тогда `i_j=(selectedFerrersCofinalSourceData P).index j`
и `m_j=N_j=φ_P(j)+2`. На буквальном носителе `CCMModeFinite N_j` положим
`K_j=sourceCCMFiniteMatrix i_j`, `q_j=selectedFerrersFiniteCCMRow P j` (`q_j* q_j=1`),
`a_j=Re(q_j* K_j q_j)`, `r_j=(K_j−a_j I)q_j`. Условие `y⊥q_j` означает
`q_j* y=Σ_u conj(q_j(u))y(u)=0`, со всеми комплексными коэффициентами.
Для `ν_u=u−N_j`, `b_u=ccmBetaFinite m_j N_j u` и
`H_uv=0` при `u=v`, иначе `1/(ν_u−ν_v)`, точная источниковая Loewner-формула даёт

`Re[y*(K_j−a_j I)y] = Σ_u (K_j(u,u)−a_j)|y_u|² + 2Σ_u b_u Re(conj(y_u)(Hy)_u)`.

Алгебра здесь закрыта (`CCMFiniteWeilSourceCommutator.lean:282-341`,
`G6N1SelectedFerrersHilbertPairing.lean:171-224`). Первый **недоказанный знак** —
единая eventual-нижняя граница этой полной правой части `≥βΣ|y_u|²` для всех `q_j* y=0`.
Нулевая сумма невзвешенных Hilbert-весов не задаёт знак при переменных `b_u`;
диагональный канал также нельзя выбросить. `hmode` относится к другому оператору и не даёт эту оценку.

Конкретный необходимый краевой тест без sector floor: выбрать `u` с `ν_u=±N_j` и
`|q_j(u)|<1` (хотя бы один из двух краёв годится), положить
`y=e_u−conj(q_j(u))q_j`. Тогда `q_j*y=0`, `‖y‖²=1−|q_j(u)|²`, и FLOOR требует

`K_j(u,u)−a_j−2Re(conj(q_j(u))r_j(u)) ≥ β(1−|q_j(u)|²)`.

Вклад `W₀₂` в `K_j(u,u)` на `|ν_u|=N_j=m_j` строго отрицателен:
`32L sinh²(L/4)(L²−16π²N_j²)/(L²+16π²N_j²)²<0`, `L=log m_j`.
Знак полного выражения после `−Wℝ−Prime`, сдвига и residual-поправки не доказан;
это не контрпример к FLOOR. Имеющаяся high-mode оценка начинается за cutoff `R_j>N_j`
(`D0PstarSelectedFerrersEvenTailCutoffObstruction.lean:78`) и не покрывает эту конечную матрицу.
Узкий запрос Прошке отправлен одним вложением
`docs/session_protocols/PROSHKA_REQUEST_GOAL058_INDEPENDENT_COMPLEMENT_FLOOR_20260925.txt`
(SHA-256 `79207d2da49851bc31ff0899f1053aa0571955dac80f2395a11b7d255e6fbb1f`)
в существующий чат 25.09 в 13:58; интерфейс показывает, что ответ ещё генерируется.
Вердикт не получен. Lean и runtime для этой атаки не запускались.

**G1 · hratioEv.** После выбора того же `β` нужна субкритическая оценка
`residualEnergy/β²<1` eventually (DB:294-296). Нельзя заменять её оценкой одной части остатка.

**G1 · hoddEv (производное при мосте ниже).** Если hfloorEv получен независимо и odd mass `<1/2`
на той же семье, бумажное неравенство ниже даёт `β₀=β`; hratioEv для самого этого вывода не нужен.
Это пока не закрытый факт выбранной семьи. Если прямой hfloorEv не удастся, отдельный путь к hoddEv —
source-derived odd coercivity или signed odd head-tail Feshbach из вердикта 30.08.
Убито: F1 «коммутирует + простой ⇒ чётное основное», F2 «нечётный tail floor ⇒ complement floor»,
F3 (contracts:137-145); GLOWER без моста компрессии не поставщик (Goal058:149-157).

**G3 (ядро, стена).** Нужно: C_K(m,N)‖r‖/Δ + Tail + NormalizationError → 0 (master:1284-1289), т.е. равномерный decay
joint defect r = (A/Z)[(K−aI)b − (K−aI)e] (RQ:52-54 — это тождество, не оценка), Z > 0. Убито: «exact ground = trial»
(как необязательное, не опровергнуто), «⟨Kq,q⟩ мало ⇒ ‖(K−a)q‖ мало», прямой Satz9/Fuchs (DB:21-25), контроль P₂
(ℋ(1/2) = −2/5). Живые механизмы: Fokas 1 (Mellin/Abel–Plana) или 2 (граничный член Штурма–Лиувилля), BRIEF:44-51;
контроль t−V = 3√2/4 (источник вывода не найден — UNVERIFIED). Ответ Прошки на Fokas-запрос в bus не сохранён — UNVERIFIED.

**Сборка → hconv.** После G3/G3c/G4: одна теорема для той же F вдоль tail reindex.

Порядок основного фронта после бумажного hmode: **независимый complement floor (hfloorEv) → hratioEv → G3**.
При выполненных условиях моста hoddEv выводится, а не ищется как отдельный источник.
G4 crosswalk и G3c ведём параллельно; после закрытия этих входов — сборка одной семьи.
Lean — после бумаги, кроме проверки, без которой математический шаг нельзя принять.

## Условный мост complement floor → odd floor (25.09, PAPER)

Для точной выбранной строки положим `q = selectedFerrersFiniteCCMRow P j`,
`K = sourceCCMFiniteMatrix`, `a = Re⟨q,Kq⟩`, `A = K-aI`,
`J = ccmComplexReflectionMatrix`, `η = ‖(I-J)q/2‖²`.
Источник доказывает `‖q‖=1`, `K=K*`, `J=J*=J⁻¹` и `KJ=JK`
(`G6N1SelectedFerrersFiniteCCMSourceRow.lean:219`,
`D0PstarCCMFiniteSourceResidual.lean:221`,
`G6N1SelectedFerrersH2aSourceQuantities.lean:94,107,122`).
Пусть `β>0` — **уже независимо доказанный** trial-complement floor
`⟨y,Ay⟩≥β‖y‖²` для `y⊥q`, и `η<1/2`.

Разложим `q=u+v` по чётному/нечётному секторам: `‖u‖²=s=1-η`,
`‖v‖²=η`. Из `⟨q,Aq⟩=0` и `AJ=JA` следует
`⟨u,Au⟩=-d`, где `d=⟨v,Av⟩∈ℝ`. Для любого нечётного `x`
вектор `y=x-(⟨v,x⟩/s)u` ортогонален `q`, поэтому floor даёт

`⟨x,Ax⟩-(|⟨v,x⟩|²/s²)d ≥ β(‖x‖²+|⟨v,x⟩|²/s)`.

Подстановка `x=v` показывает
`d(1-2η)/s² ≥ βη/s`, значит `d≥0` при `η<1/2`.
Повторное применение неравенства даёт `⟨x,Ax⟩≥β‖x‖²`
для **всех** нечётных `x`; случай `η=0` включён. Таким образом,
независимый hfloorEv и eventual `η<1/2` дают hoddEv с `β₀=β`.
Для выбранной семьи `η→0` пока доказано лишь условно на недостающие
`hmode/hχ` (`G6N1SelectedFerrersOddMassDecay.lean:1169`).

Это **не** самостоятельное закрытие G1. Действующие поставщики
`G6N1SelectedFerrersH2aSourceQuantities.lean:503` и
`G6N1SelectedFerrersWeightedResidualComplementFloor.lean:174` строят
complement floor из odd floor; подставить в них эту обратную лемму — круг.
Мост полезен только при новом независимом доказательстве complement floor.
Независимый reviewer проверил усиленный вывод и обнаружил, что `K=K*`
необходимо: без него первоначальная более слабая формулировка ложна;
для выбранной CCM-матрицы это условие уже доказано. hratioEv остаётся
отдельным входом tracking consumer. Вопрос отправлен Прошке в существующий
чат; Прошка подтвердил бумажный мост и усиление `β₀=β`, но не доказал входы для выбранной семьи.
