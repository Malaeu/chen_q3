# ROUTE B — THEOREM CONTRACT v2 (исправленный финальный контракт Новой дороги)

Дата: 2026-07-10 (поздняя ревизия) · Автор: Mythos · Ревизия по read-only плану Codex (принят с одной арифметической поправкой, см. §3).
Статус: contract — целевая теорема + реестр обязательств; НЕ утверждение о доказанности. Подчинён `ROUTE_B_STATE.md` + `loop_state.json`. NOT_RH.
Маршрут: `ALPHA_ROUTE_REMAINS_CHALLENGER`; Старая дорога (T0-pd → H-bridge) не затрагивается; смешивание цепей запрещено.
Заменяет: `docs/ROUTE_B_THEOREM_CONTRACT_v1.md` (помечен SUPERSEDED).

---

## 1. Δ против v1 (восемь ремонтов — для контрподписи голом 008)

1. H4 заменён на **QuantitativeSafeWitness** с явной степенной арифметикой (§3).
2. **SafeAlphaUpper оценивает каноническую α, а не μ₁**; связка α ↔ a₁ — доказываемый crosswalk, не определение.
3. Финальный экспорт — ТОЛЬКО через ZEO 2.2; узел 2.1 — независимая перекрёстная проверка вне главной цепи.
4. Введён режим конечной размерности: **N = N(λ) либо явная лемма конечно-континуального моста**; все спектральные объекты несут N в типе.
5. **PO-11 (ZEOExportSoundness) получает статус OPEN_CRITICAL** и поднимается до уровня 1: пока стрелка «Dictionary ∧ Witness ⟹ нули Ξ вещественны» не разбита на конечные леммы, тяжёлые перья не покупаются.
6. Ранний **SAFE feasibility gate** (аудит theorem-shapes пяти листьев) — до уравнения хвоста.
7. Зонд переименован: r₁₃ → **rGap13**; зафиксирована коллизия имён с локальным r1 = θ₁/λ₁(G_even) ≈ 9.51e−32 — это РАЗНЫЕ объекты; 50-порядковый судья НЕДЕЙСТВИТЕЛЕН до source audit. Наблюдённое μ₁/(μ₃−μ₁) ≈ 2.66e−8 — PROVISIONAL_COINCIDENCE_SIGNAL (в полосе coincidence-сценария), провенанс не заверен.
8. Степенная арифметика ИСПРАВЛЕНА: строгое условие **rΔ − rα > 2q_b + 1** (в read-only плане пропущен вклад явного множителя λ; поправка +1).

## 2. Словарь H0 — ExactDetectorDictionary (тип гипотезы)

Обязательные строки (расширение A1–A8):
- единственная каноническая **α(λ) ≥ 0**, выбранная из существующих реализаций {raw, projected, opt} с доказанным crosswalk к каноническому a₁ = s_λ²·QW(g_λ);
- α ≥ 0 — следствием min–max/Rayleigh-структуры, НЕ численного знака;
- **Δe(λ) := μ₃(λ) − μ₁(λ) > 0 строго** (кратности исключены леммой), same-parity выбор доказан; trial-вектор живёт в том же чётном секторе;
- оператор M_λ: матрица, пространство, базис, Gram-конвенция, зависимость от N; режим N = N(λ) или мост в континуум;
- **b(λ)**: формула + двусторонняя граница 0 < c_b ≤ |b(λ)|·λ^(−q_b) ≤ C_b на Λ;
- детектор: W′(λ)² = |b(λ)|²·λ·α(λ)/Δe(λ);
- квантор: кофинальная Λ = {λ : λ² ∈ ℕ} (достаточность для liminf доказана; для контуров Руше — PO-11).

## 3. Центральная количественная лемма (QuantitativeSafeWitness)

Пусть на Λ:
```text
|b(λ)| ≤ C_b·λ^(q_b)
0 ≤ α(λ) ≤ C_α·λ^(r_α)·e^(−4πλ²)      [SafeAlphaUpper]
Δe(λ) ≥ c_Δ·λ^(r_Δ)·e^(−4πλ²)          [SafeGapLower]
```
Тогда
```text
W′(λ) ≤ C·λ^( q_b + (1 + r_α − r_Δ)/2 ).
```
Строгое достаточное условие W′ → 0 на Λ:
```text
r_Δ − r_α > 2·q_b + 1        (запас δ := r_Δ − r_α − 2q_b − 1 > 0 фиксируется явно)
```
Поправка к read-only плану: множитель λ в W′² даёт «+1»; условие «r_Δ − r_α > 2q_b» недостаточно на границе.

## 4. Цепь вывода (форма финальной сборки; каждая стрелка — отдельная теорема)

```text
H0 (словарь, §2)
Supply-цепь: ProjectedProlateDefectEquation → Gate 6 (6A–6D)
   → G04DefectGramBridge / узел 3.3 (B* ≤ 25) → G3a → DetectorBridge
   → SafeAlphaUpper (финальная форма: 0 ≤ α ≤ C_α λ^{r_α} e^{−4πλ²})
Parity-clean spectral theorem → SafeGapLower
SafeSignAndB (α ≥ 0 структурно; Δe > 0 строго; b двусторонне)
SafeRateAssembly (r_Δ − r_α > 2q_b + 1, запас δ > 0)
   ⟹ QuantitativeSafeWitness: ∃ λ_j ∈ Λ, λ_j → ∞, W′(λ_j) → 0
ZEOSoundness (PO-11): локально-равномерная сходимость нормированных
   конечных функций; контуры Руше на дискретной Λ; отсутствие escaping
   zeros; невырожденность b; точная идентификация предельной Ξ
   ⟹ все нули Ξ вещественны
XiRealIffRH ⟹ RH.
```
DetectorBridge обязан ЗАКАНЧИВАТЬСЯ оценкой α в форме SafeAlphaUpper (или точной промежуточной, из которой она следует отдельной леммой) — абстрактного E_spec недостаточно.

## 5. Вердикт нециркулярности сейфа (перенос из v1, в силе)

`SAFE_MECHANISM_CANDIDATE_NAMED`. Готовой безусловной теоремы для листьев нет; ДОКАЗАНО (OBJECT_LOCK §3), что определительного моста α ≤ κ_λ|a₁| с субэкспоненциальным κ не существует — сейф нерезервируем внутри G3a. Кандидат-механизм листа SafeGapLower: возмущение против полиномиально разделённой Fuchs-диагонали (Вейль/Дэвис–Кахан); входы безусловны. Самая вероятная стена всей дороги — **SafeGapLower** (совпадающий диагноз Mythos + Codex). Перевороты вердикта — как в v1 §5.

## 6. Анти-циркулярные статьи (без изменений против v1)

Эпистемический файрвол (BFM запрещён; Гонек/twisted — замены); K7 (вычисление не занимает квантор); запрет tau0-подмены (`docs/trackB/WEIL_SQUARE_CLASS_SPEC.md`); классификация импортов THEOREM/CONDITIONAL/CONJECTURE/HEURISTIC с sha-сверкой.

## 7. Реестр обязательств v2 (уровни; внутри уровня — любой порядок)

```text
УРОВЕНЬ 0 (ZERO compute / контрольная плоскость)
PO-0  Contract v2 crosscheck + синхронизация STATE↔loop + провенанс
      источников (вкл. rGap13 source audit и физическое размещение
      ALPHA_DEMAND_AUDIT / OBJECT_LOCK)                [гол 008, Codex]
УРОВЕНЬ 1 (kill-гейты до тяжёлой аналитики)
PO-1  Словарь H0 (§2): выбор канонической α, crosswalk, N-режим,
      строгая щель, b двусторонне                      [перо M → гейт C]
PO-2  Чётность: ParityLeakSourceAudit → ParityProjectedOperatorLock;
      до PASS запрещены аргументы от W′/gap/rGap13     [гейты C]
PO-11 ZEOExportSoundness (OPEN_CRITICAL): стрелка Witness ⟹ Ξ-real
      разбита на конечные леммы; коды провала:
      ROUCHE_QUANTIFIER_GAP / XI_LIMIT_IDENTIFICATION_GAP /
      FINITE_TO_UNIVERSAL_GAP / ZEO_EXPORT_NOT_DERIVED [перо M + Sol]
PO-12a SAFE feasibility: theorem-shapes пяти листьев
      (AlphaUpper/GapLower/BUpper/Sign/Rate); после чётности —
      дешёвый falsifier (может убить, не может доказать)
      PASS: SAFE_RATE_SHAPE_LOCKED, SAFE_CANDIDATE_SURVIVES_FALSIFIER
      KILL: SAFE_*_NO_SOURCE / SAFE_IS_RH_REPACKAGING  [перо M + гейт C]
УРОВЕНЬ 2 (только после уровня 1)
PO-3  ProjectedProlateDefectEquation (bulk + коммутатор + граница +
      полюс + середина; статусы каналов; 007-факты фиксированы:
      C_mid PRESENT_EXACT, C_pole PRESENT_EXACT, C_right ABSENT) [перо M]
PO-4..6  Gate 6A/6B/6C отдельными голами; един X_λ; выход обязан
      кормить SafeAlphaUpper; kill: G3_NORMALIZED_DEFECT_MATRIX_
      POLY_BOUND_FATAL                                  [перо M + гейты C]
PO-7  Гейты 3–5 (radical-window, Poisson-факторизация, ε↓0)   [перо M]
PO-8  Узел 3.3: Rayleigh/Gram-мост, B* ≤ 25; STOP-коды:
      RAYLEIGH_BRIDGE_NOT_DERIVED / UNIT_LEDGER_MISMATCH /
      BUDGET_25_EXCEEDED / CHANNEL_STATUS_UNCLASSIFIED  [перо M + гейт C]
PO-9  Сборка G3a единым леджером (шаблон 007)           [перо M + гейт C]
PO-10 DetectorBridge → финальная форма SafeAlphaUpper   [перо M + Sol]
УРОВЕНЬ 3 (сейф)
PO-12 Четыре листа: SafeAlphaUpper, SafeGapLower, SafeSignAndB,
      SafeRateAssembly → QuantitativeSafeWitness        [все каналы]
УРОВЕНЬ 4
PO-13 Lean: request-local definitions/signatures module (не импортируется
      в Q3.Main); один sorry = один адрес обязательства; закрытие тел
      после self-attack + Прошка + source audit + falsifier;
      `lake env lean` после каждого узла; скан sorry|admit|exact?;
      check_axioms; приёмка: zero sorry, zero unexpected axioms,
      zero tau0, zero RH-conditional imports, один объект в статье
      и в Lean                                          [C]
```

Закрыто к дате v2: 6D; Λ-достаточность для liminf; нерезервируемость сейфа (O2); шаблон точного леджера (007, 2.2e−89); ядро словаря G3_0; кросс-подтверждение H2-ветки (006-G1 ↔ G3_0).

## 8. Условия расторжения (расширены)

(а) SAFE_IS_RH_REPACKAGING доказан; (б) SAFE_GAP_LOWER_NO_SOURCE после честного feasibility-аудита и falsifier; (в) G3_NORMALIZED_DEFECT_MATRIX_POLY_BOUND_FATAL; (г) ZEO_EXPORT_NOT_DERIVED неремонтируем. Резервы: Route C «pair, don't multiply»; Cayley–Li Orbifold detector.

## 9. Приёмка

Контракт исполнен ⟺ PO-0…PO-13 закрыты в порядке уровней и `#print axioms` финального экспорта чист. До этого: RH — OPEN; тяжёлые перья уровня 2 не покупаются, пока уровень 1 не PASS.
