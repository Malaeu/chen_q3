# CODEX DIRECTIVE

Один следующий локальный target:

```text
D0CenteredDensityAutocorrelationFactorization
```

## Цель

Найти явную amplitude row `a_(m,N)` и доказать точное тождество

```lean
theorem centeredTrialDensity_eq_neg_normSq
    (m N ...) (t : ℝ) :
    centeredTrialDensity m N t
      =
    -(1 / Real.sqrt (L_m m)) *
      ‖centeredTrialAmplitude m N t‖ ^ 2
```

с точной repo-нормировкой.

## Обязательные corollaries

```lean
centeredTrialDensity_re
centeredTrialDensity_nonpos
centeredTrialDensity_ne_zero
centeredTrialDensity_integral_neg
c0_neg
rawFplus_zero_ne
```

## Proof route

```text
exact definition of c_n
→ exact shifted coefficient (-1)^n c_n
→ finite autocorrelation identity
→ finite sum rearrangement
→ norm-square factorization
→ sign and central nonvanishing.
```

## Forbidden

```text
no sampled-grid proof;
no mpmath as theorem;
no “projection preserves positivity” shortcut;
no fitted global phase;
no changing coefficient convention;
no use of RH.
```

## Failure report

```text
CENTERED_DENSITY_NOT_EXACT_FEJER:
- exact coefficient mismatch;
- whether factorization holds only before projection;
- first non-autocorrelation term;
- weakest repaired unprojected factorization.
```

После этого следующий математический target, не одновременно:

```text
UnprojectedRelativeCriticalTail
```

------


(Гол 007 извлечён Mythos из вердикта Прошки 2026-07-27-b. Прекондиция: точная repo-нормировка centeredTrialDensity — сверить множитель и знак с D0CenteredCriticalMoment.lean ДО доказательства. GIBBS-проба (N-удвоение) продолжается параллельно; её результат — в поле failure report «factorization only before projection». Следующий математический таргет ПОСЛЕ 007: UnprojectedRelativeCriticalTail — не одновременно.)
