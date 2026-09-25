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
| G1 · hoddEv | нечётный floor β₀‖x‖² ≤ Re⟨x,(K−a)x⟩ | F | **OPEN, источника нет** (DB:115-116) | условный приёмник есть |
| G1 · hratioEv | residualEnergy/β² < 1 eventually | F | **OPEN** (DB:294-296) | условный приёмник есть |
| G2 | нули лагранжева многочлена строки вещественны | строка F | закрыто через Lean, условно на G1 | LEAN `CCMFiniteWeilParity.lean:161` |
| G2b | перенос вещественности на Prop-5.9 transform той же строки | F | закрыто через Lean (контракты устарели) | LEAN `Proposition59GroundLagrangeZeroSetBridge.lean:231` |
| hentire | каждая F k целая | F | закрыто через Lean | LEAN `G6N1SelectedFerrersTrackedGroundTransform.lean:761` |
| G3 | та же F трекает projected trial: нормировка × kernelL2 × √ratio → 0 на компактах | F | **OPEN — главная стена, RH-уровень** (master:1278). Прогресс: paired-window тождество PAPER_OWN rev — только представление, не оценка (FN:91-92) | нет формулировки |
| hmode | sup‖w_m − D_n‖ ≤ C_n/m, центр-нормировка 1/h0(0), 3/h4(0) | F | **PAPER_OWN, внутренний review «coherent, no circularity»** (RPT:1188-1220); Прошке не отправлено — оркестратор дал HOLD (RPT:1228-1235) | hmode⇒W5/N2 в кандидате |
| hχ / hθ | из hmode | F | hχ: Lean в кандидате (RPT:633); hθ: PAPER (RPT:635) | hχ кандидат |
| G3c | projected trial → continuum trial (projection tail) | trial | **OPEN** («PROSE проекционный хвост», contracts:267,280) | нет |
| G4 | CCM Lemma 7.3: преобразование k_λ → Ξ равномерно на полосах | trial | **PAPER_PUBLISHED** arXiv:2511.22755 §7, Lemma 7.3, p.31 (препринт); crosswalk h_λ ↔ hTrial_m OPEN (master:994-1004) | импорт отсутствует |
| G5 | одна семья: вещественные нули + F → Ξ ⇒ RH (Гурвиц) | F | закрыто через Lean | LEAN `Goal058DirectGroundZeroEscape.lean:27`, аксиомы 3 (проверено 25.09) |
| Сборка | tail reindex + G3 + G3c + G4 ⇒ hconv для той же F | F | **OPEN** | нет |

Итого 14 звеньев: закрыто 5 (G2, G2b, hentire, G5 — Lean; G4 — статья), наполовину 2 (hmode — наш текст без
внешней проверки; hχ/hθ), открыто 7 (G0 частично, три floors G1, G3, G3c, сборка) + crosswalk для G4.

## Главное наблюдение
Сами Connes–Consani–Moscovici в §8 arXiv:2511.22755 (p.32) называют ровно два недостающих шага своей программы:
«prove that its smallest eigenvalue … is simple and that its corresponding eigenvector ξλ is even» — это наш G1;
«establish that kλ provides a sufficiently accurate approximation to (a scalar multiple of) ξλ» — это наш G3 (+G3c).
Сопоставление с нашими объектами — вывод читателя, crosswalk матриц не записан. Значит: G1 и G3 — ядро RH,
всё остальное — сантехника цепи.

## Открытые звенья: что не хватает и следующий ход

**hmode (дешёвый выигрыш).** Бумага есть (RPT:1188-1220), внешней проверки нет. Ход: отправить уже
подготовленный hmode-пакет Прошке на review (пакет и review-plan: RPT:1228-1235) — сейчас без оркестратора.

**G4 crosswalk + G3c (сантехника, своими силами).** Нужно: h_λ ↔ hTrial_m, скаляр и фаза, C = 2πλ², координата
преобразования (master:994-1004); отдельно доказать projection tail (master:1222). Своя попытка на бумаге.

**G1 · hoddEv (ядро, начать здесь).** Нужно одно явное равномерное нижнее ограничение для буквальной выбранной
нечётной компрессии или signed head-tail Feshbach с положительным Schur-запасом (DB:116). Убито: F1 «коммутирует
+ простой ⇒ чётное основное», F2 «нечётный tail floor ⇒ complement floor», F3 (contracts:137-145); GLOWER как
прямой поставщик без моста компрессии запрещён (Goal058:149-157). Ход: своя попытка → alias-hunt → Прошка.

**G1 · hfloorEv, hratioEv.** Нужно: равномерная чётная коэрцитивность при выбранном сдвиге или head-tail Feshbach
(DB:207); для ratio — субкритическая оценка взвешенного residual (DB:294-296; к какому из двух floors относится этот
долг — не ясно). Ход: после hoddEv, тем же инструментарием.

**G3 (ядро, стена).** Нужно: C_K(m,N)‖r‖/Δ + Tail + NormalizationError → 0 (master:1284-1289), т.е. равномерный decay
joint defect r = (A/Z)[(K−aI)b − (K−aI)e] (RQ:52-54 — это тождество, не оценка), Z > 0. Убито: «exact ground = trial»
(как необязательное, не опровергнуто), «⟨Kq,q⟩ мало ⇒ ‖(K−a)q‖ мало», прямой Satz9/Fuchs (DB:21-25), контроль P₂
(ℋ(1/2) = −2/5). Живые механизмы: Fokas 1 (Mellin/Abel–Plana) или 2 (граничный член Штурма–Лиувилля), BRIEF:44-51;
контроль t−V = 3√2/4 (источник вывода не найден — UNVERIFIED). Ответ Прошки на Fokas-запрос в bus не сохранён — UNVERIFIED.

**Сборка → hconv.** После G3/G3c/G4: одна теорема для той же F вдоль tail reindex.

Порядок: (1) hmode → Прошке на проверку, параллельно (2) G4 crosswalk + G3c своими силами; основное время —
(3) hoddEv, (4) hfloorEv/hratioEv, (5) G3; затем (6) сборка. Lean — после бумаги (см. `NEXT.md`, «Стратегия»).
