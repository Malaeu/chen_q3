# LINUX PREFLIGHT — SELECTED TRIAL NORMALIZER ROUTE (GOAL058)

DATE: 2026-08-26
TASK_ID: GOAL058_SELECTED_TRIAL_NORMALIZER_ROUTE_PREFLIGHT
MODE: PAPER_AND_SOURCE_READ_ONLY (Lean не редактировался, нумерики нет)
PARENT_VERDICT: f9b9c169 (REQ-2026-08-26-G)

## EXACT_IDENTITIES_TO_LOCK — заперты с диска

1. `selectedTrialNormalizer S k = sTrial_m_N i h hLp hNZ` и
   `sTrial_m_N … = ‖gTrial_m_N i h hLp‖⁻¹`
   (D0PstarMuntzCenteredCoordinateLock.lean:64, D0KTrialStage3.lean:33-39).
   Нормализатор — буквально обратная норма отобранной конечной проекции.
2. `norm_selectedNormalizedGalerkinResidual_eq` (D0PstarGalerkinResidualDecay):
   ‖нормализованный резидуал‖ = ‖normalizer‖ · (ненормализованный хвост). Точно, committed.

## PRIMARY_DISCRIMINATOR — исход

**ВЫБРАН R1, в усиленной source-форме.** Полнообъектный norm-floor + треугольник
даже не нужен: в источнике уже лежит более сильный механизм.

### Механизм (все три ножки committed)

- `inner_V0_gTrial_m_N_eq` (D0AnchorFloor.lean:20): ортопроекция СОХРАНЯЕТ
  V₀-overlap: ⟨V₀, gTrial_m_N⟩ = ⟨V₀, gTrial_m⟩.
- ‖V₀‖ = 1 (D0PstarInversionCoefficientCrosswalk.lean:241).
- Cauchy–Schwarz ⟹ ‖gTrial_m_N‖ ≥ |⟨V₀, gTrial_m⟩|.

Следствие: `SelectedTrialNormalizerBounded S` ⟸ eventual floor
`c ≤ |⟨V₀, gTrial_m i'_k (prolateCombination pair_k)⟩|`, c > 0.
Хвост (SelectedProjectionTailDecay) в этой ножке НЕ участвует — маршрут
чище, чем R1-треугольник вердикта; сабсеквенций нет; литеральный резидуал
не подменяется (факторизация п.2 остаётся единственным мостом).

### Почему floor существует на этой семье (source-анализ)

Центральный overlap = (нормированный) интеграл лог-представителя E*-комба.
По F72.5 (`selectedFerrers_zeroMassCylinderPacketRate_of_modeAndChiRates`)
масштабированный пакет равен `explicitCCMLimitH` с sup-ошибкой C/λ² на окне.

(a) **Ошибка умирает**: |⟨V₀, E*(pkt − H-scaled)⟩| ≤ (1/√L)·∫₀ᴸ √u·(card ≤ λ/u)·
    (C/λ²) dx = (C/λ)·∫u^{−1/2}dx ≤ 2C/√λ → 0 — та же комб-механика, что уже
    построена в W5-сборке (счёт card ≤ λ/u, ∫u^{−1/2}dx ≤ 2√λ).

(b) **Главный член не нулевой и растёт**: «zero-mass» пакета — это
    `ZeroPositiveMass` (∫₀^∞ H = 0, плоский вес; проверено:
    (π/2)[2π·3/(8π²) − 3/(4π)] = 0 — гард ζ-континуации). Но центральная
    V₀-координата живёт на весе Mellin-½ (√u-конвенция E* + du/u), а там
    масса H НЕ нулевая:
    M_H(1/2) = ∫₀^∞ H(y)·y^{−1/2} dy = ¼π^{−1/4}[2Γ(9/4) − 3Γ(5/4)]
             = −⅛·π^{−1/4}·Γ(5/4) ≠ 0
    (Γ(9/4) = (5/4)Γ(5/4); конечная Γ-алгебра, не нумерика).
    Комб-структура: ∫_{1/λ}^{λ} u^{−1/2} Σ_n H(nu) du =
    Σ_n n^{−1/2}·∫_{n/λ}^{nλ} v^{−1/2}H(v)dv; для средней полосы n ∈ [√λ, λ]
    внутренние интегралы ≈ M_H(1/2) с ОДНИМ знаком ⟹ главный член
    ~ 2√λ·M_H(1/2): по модулю растёт как √λ/√L. Floor c > 0 — слабейшее
    следствие; фактический темп сильнее (кандидат: |⟨V₀,gTrial⟩| ≳ √λ/√log·|s|⁻¹).

(c) **Масштабы под контролем**: |scaleL73⁻¹| ≤ 8 committed (7d27b5ad);
    переход Lemma72Scale ↔ Lemma73Scale — конечная algebra на якорях
    (оба в ZeroMassCylinderPacket/FactorFourPortRate, non-vanishing committed).

### Что НЕ найдено (границы честности)

- Готового eventual floor'а на ⟨V₀, gTrial⟩ в репо НЕТ: `SelectedAnchorRatioData`
  (D0SelectedCentralFloor) — абстрактный пакет с ratio-полем, для
  production-семьи НЕ инстанцирован. Это и есть недостающий узел.
- Оконная Mellin-machinery для главного члена есть
  (EStarWindowedMellinCrosswalk: `mellin_E_star_eq_riemannZeta_mul`,
  windowedMellin-разложение с хвостами), но связка «комб-центр ↔
  ζ(1/2)·M_H(1/2)» на отобранной семье не собрана. ζ(1/2) ≠ 0 при
  необходимости выводима через η-ряд (η(1/2) > 0 alternating,
  1 − 2^{1/2} < 0 ⟹ ζ(1/2) < 0); в критическом узле она НЕ обязательна —
  комб-версия (b) работает частичными суммами, без ζ.

## ПРЕДЛАГАЕМЫЙ МИНИМАЛЬНЫЙ УЗЕЛ (следующая Lean-транзакция, если авторизуешь)

Одна публичная теорема:
`selectedTrialNormalizerBounded_of_selectedFerrersW5RateLedger`
(те же замороженные входы, что у admitted-сборки; вывод —
`SelectedTrialNormalizerBounded S`), внутри:
(i) центральный overlap-floor по (a)+(b) — БЕЗ новых аналитических гипотез;
(ii) committed overlap-preservation + ‖V₀‖ = 1 + Cauchy–Schwarz.
Вместе с admitted-хвостом это замыкает
`selectedNormalizedGalerkinResidual_norm_tendsto_zero_of_tail_and_bounded`
— литеральный нормализованный резидуал уровня маршрута.

CLOSES(candidate): SELECTED_TRIAL_NORMALIZER_BOUNDED_OR_DIRECT_WEIGHTED_PRODUCT (ветвь R1)
OPENS(candidate): [] — та же замороженная семья входов.

## R2 — статус

Не требуется, если (b) выдерживает kill-pass. Запасной путь остаётся живым:
темпы обеих сторон уже в репо (хвост ≤ √(8π)·C_k/√bandwidth из ресивера;
normalizer-рост ограничивается тем же центральным членом), прямое
произведение выводимо той же механикой — но это более длинный узел.

## FORBIDDEN COMPLIANCE

Boundedness из поточечного TrialNonzero НЕ выводится (floor строится из
масс, не из nonzero-свидетелей); сабсеквенций нет; литеральный резидуал
не подменён; fixed-carrier проекция не импортируется (V₀ живёт в движущемся
H_m i'_k, overlap-лемма индексная); новых owner-гипотез нет; нумерики нет
(Γ-тождества — точная алгебра).

SUCCESS_CODE: SELECTED_TRIAL_NORMALIZER_FULL_NORM_FLOOR_ROUTE_READY
