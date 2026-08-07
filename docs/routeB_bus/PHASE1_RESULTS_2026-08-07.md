# Goal 057 · CCM penalty Phase 1 control cell

```yaml
STATUS: CLOSED_PASS
VERDICT: CCM_CONTROL_CELL_CERT_INTERVAL_PASS
CONTROL_CELL: {m: 13, lambda: sqrt(13), N: 120, dimension: 241}
ROUTE: CHALLENGER_NOT_RH
PROMOTION: FORBIDDEN
BUS_010: VOID
GOAL_055: HOLD
PX_RH_CLAIM: NOT_MADE
```

## Результат

Для source-locked CCM-матрицы

```text
K = W_0_2 - W_R - W_prime,
G = I,
J(c)_n = c_-n
```

получен строгий интервальный сертификат

```text
K - beta I + tau q q*  ≻  0,
beta = 10^-56,
tau = 1,
q* q = 1,
J q = q,
a = q* K q < beta.
```

Это доказывает условие конечного penalty engine для одного CCM truncation
`(m,N)=(13,120)`. Это **не** закрытие `SlotH2a`, не all-lambda input A, не uniform
operator gap, не перенос к пределу и не утверждение RH.

## Source lock и проба

| Артефакт | SHA-256 |
|---|---|
| `q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/out/portable_k_coeffs_lambda_sq_13_N_120.json` | `0e5239355c54103859b22d7f753d8cd6765c2c41bcd3ec7f86b20beccc907a88` |
| `phase1_scripts/ccm_control_cell_penalty.py` | `1be57db69683652ed4f6d56dba6fc3b70c186f429fbb7f5bef978cd84f08ed0d` |
| `phase1_results/ccm_control_cell_m13_N120_interval.json` | `8da8757f106f90e67f217226ce657869f398e62a23ab06bd096aba847e4d8512` |

Исходный packet имеет сопряжённо-симметричные комплексные коэффициенты. Требуемая
`J`-чётная проба определена без float-подмены:

1. десятичные `re(c_n)` читаются как точные рациональные числа;
2. берётся точная проекция `s_n = (re(c_n)+re(c_-n))/2`;
3. `q=s/sqrt(sum_n s_n^2)`.

По построению `q` ненулевой, вещественный, `Jq=q`, `q*q=1`. Это объясняет отличие
нового Rayleigh value от прежнего packet-truth значения для непроецированного
комплексного вектора: объекты близки, но не тождественны.

## Интервальная сборка

Матрица не берётся из старого double-precision Schur cache. Каждый элемент строится
заново в `python-flint 0.8.0` / Arb по source-side формулам CCM. Удалимые особенности
двух интегралов переписаны в аналитические integrands до вызова Arb quadrature.

Чётность используется как точное разложение:

```text
even dimension = 121,
odd dimension  = 120,
q lives in the even block,
odd block receives only -beta I.
```

PSD проверяется интервальным no-pivot `LDL^T`. Успех означает, что нижняя граница
каждого pivot строго положительна; это directed-rounding certificate, а не approximate
eigenvalue search.

## Числа

На `240 dps`:

```text
a = 4.71997997950943000721230732036854316235703024426659263920269359...e-59
beta - a
  = 9.95280020020490569992787692679631456837642969755733407360797306...e-57
even LDL: 121 / 121 pivots strictly positive
odd  LDL: 120 / 120 pivots strictly positive
```

Обязательный precision-doubling был информативным:

| dps | even | odd | смысл |
|---:|---|---|---|
| 120 | sign lost at pivot 42 | sign lost at pivot 39 | `INSUFFICIENT_PRECISION`, не отрицательный verdict |
| 240 | 121/121 positive | 120/120 positive | `INTERVAL_POSITIVE_DEFINITE` |

Скалярные интервалы `a`, `beta-a` и четырёх независимо контролируемых элементов `K`
пересекаются между 120 и 240 dps. Дополнительный read-only повтор `180 -> 360 dps`
дал `INTERVAL_POSITIVE_DEFINITE` на обеих точностях и тот же интервал `a`.

## Семантический итог

Penalty certificate достаточен, поэтому для этого конкретного конечного CCM cell
получены простота, `J`-чётность и изоляция нижнего собственного значения с
сертифицированным floor `beta-a`. Ветка `failure_of_one_penalty_certificate_does_not_negate_even_simple`
не активировалась: сертификат найден.

Следующий разрешённый шаг — Phase 2 fixed-`q` beta_N profile. Его `lambda`, `N`-ladder,
`N0`, zero-padding, precision levels и search tolerance должны быть записаны до первого
нового matrix value.
