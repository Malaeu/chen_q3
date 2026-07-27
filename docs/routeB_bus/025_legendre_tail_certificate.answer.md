# ОТВЕТ 025 — LEGENDRE RECESSIVE TAIL CERTIFICATE

`G3_COARSE_EIGENVALUE_INTERVAL_MISSING`

Статус: `CHALLENGER / NOT_RH`. Проверка остановлена на первом отсутствующем
proof-grade входе. `STATE` не изменён; `BUS_010_VOID` соблюдён.

## 1. Source-lock и crosswalk

| объект | источник | результат |
|:---|:---|:---|
| locked parameters | `025...goal.md:14-19` | order `0`, degree `n∈{0,4}`, `G=γ²`, `Θ=Λ+G` |
| `p_k,r_k,B_k,d_k` | `PROSHKA_PEN_GO...md:26-33`; DLMF 30.8.2–30.8.4 | формулы совпали |
| условие `K₀` | `PROSHKA_PEN_GO...md:35-36` | точное |
| cone/contraction/diameter | `PROSHKA_PEN_GO...md:38-48` | точная алгебра подтверждена |
| хвостовые бюджеты | `PROSHKA_PEN_GO...md:50-55` | точные условные оценки подтверждены |
| finite-core constructor | `PROSHKA_PEN_GO...md:57-60` | требует внешнего интервала `Λ` |

Первичный внешний источник формул:
[DLMF §30.8](https://dlmf.nist.gov/30.8).

## 2. Точная алгебра сертификата

Пусть `N=N_k≥5`. Тогда

```text
(2N−3)(2N−1) − 3N(N−1) = N²−5N+3 > 0,
(2N+3)(2N+5) − 4(N+1)(N+2) = 4N+7 > 0,
(2N−1)(2N+3) − 4(N(N+1)−1) = 1.
```

Следовательно,

```text
0 < p_k ≤ G/3,
0 < r_k ≤ G/4,
B_k ≥ N(N+1)−G/2.
```

Из условия `N(N+1)−Λ₊≥31G/24`:

```text
d_k ≥ 19G/24,
d_k−r_k x ≥ 19G/24−G/8 = 2G/3       для x∈[0,1/2],
T_k(x)=p_k/(d_k−r_k x) ∈ [0,1/2],
|T_k′(x)| ≤ (G/3)(G/4)/(2G/3)² = 3/16.
```

Чувствительность к ширине `Λ`:

```text
(3/(4G))/(1−3/16) = 12/(13G),
diam I_{K₀+1}
  ≤ (1/2)(3/16)^L + (12/(13G))(Λ₊−Λ₋).
```

Хвост при `N=n+2K`:

```text
Σ_{j≥1}|a_{K+j}| ≤ |a_K|,
‖R_K‖∞ ≤ |a_K|,
‖R_K‖₂² ≤ 2|a_K|²/[3(2N+5)],
‖R_K′‖∞ ≤ |a_K|(N²+8N+24),
|∫_{−1}¹ R_K(t)e^{iωt}dt| ≤ 2|a_K|.
```

Здесь использованы точные суммы
`Σ2⁻ʲ=1`, `Σj2⁻ʲ=2`, `Σj²2⁻ʲ=6` и ортогональность Лежандра.

## 3. Gate `Λ`

Инвентаризация допустимых поставщиков:

| файл | что есть | почему не является входом |
|:---|:---|:---|
| `Q3/Proofs/RouteB/ProlateLayer.lean` | типовой слой и скалярные поля `chi0`,`chi2` | нет теоремы об интервале собственного значения |
| `E_STAR_CANDIDATE_ADJUDICATION.json` | high-precision конечные characteristic values и residual estimates | нет outward-rounded enclosure точной бесконечной моды |
| `PROLATE_SAME_MODE_LOCK.csv` | float same-mode diagnostics | нет интервала `Λ` |
| `G3_INTERVAL_FOURIER_CERT_AUDIT.json` | регистрация прежнего exact-mode gap | не поставщик границ |

Не материализованы ни Rayleigh/Temple-вилка, ни
Gershgorin+tail-resolvent-вилка, ни interval-Sturm-вилка для степеней `0` и
`4`. Поэтому `K₀` нельзя выбрать из сертифицированного `Λ₊`; tail-ratio
interval, конечное ядро и нормировочный шар не формировались.

## 4. Обязательства

| шаг | результат |
|---:|:---|
| 1. точная рекурсия | `SOURCE_LOCKED` |
| 2. `K₀` из certified `Λ` | `BLOCKED_INPUT` |
| 3. конус `[0,1/2]` | `EXACT_CONDITIONAL` |
| 4. сжатие `3/16` | `EXACT_CONDITIONAL` |
| 5. interval continued fraction | `NOT_FORMED` |
| 6. хвостовые оценки | `EXACT_CONDITIONAL` |
| 7. finite core с interval final row | `NOT_FORMED` |
| 8. finite-plus-tail normalization | `NOT_FORMED` |

## 5. Планты

| плант | результат | свидетель |
|:---|:---|:---|
| tail interval → `{0}` | `FIRES_SYMBOLICALLY` | последняя диагональ `d_K−r_Kρ_{K+1}` меняется, поскольку `r_K>0` |
| `n=4` → `n=2` | `FIRES_SOURCE_LOCK` | `ProlatePair` фиксирует `h0↔chi0`, `h4↔chi2`; поля degree `2` нет |
| удалить `L2`-хвост | `FIRES_SYMBOLICALLY` | нормировка DLMF содержит бесконечную положительную weighted-square сумму |
| расширить `Λ`-интервал | `FIRES_SYMBOLICALLY` | диаметр строго растёт на `(12/(13G))·Δwidth` |

## 6. Гварды

```text
terminal ratio := 0                         НЕ использован
finite eigenpair = infinite exact mode      НЕ утверждалось
mu := 1                                     НЕ использовано
float -> zero-width ball                    НЕ делалось
sign grid                                   НЕ запускался
```

Следующий минимальный вход: source-locked outward-rounded
`[Λ₋,Λ₊]` для degree `0` и `4`, полученный независимо от усечённого
eigenvalue-as-point. После него текущая точная алгебра непосредственно даёт
`K₀`, cone и contraction и разрешает строить interval continued fraction.

## ACTIONS LOG

```text
.venv/bin/python \
  q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/legendre_tail_certificate_audit.py
```

Машиночитаемые артефакты:

```text
LEGENDRE_RECESSIVE_TAIL_CERTIFICATE_AUDIT.json
LEGENDRE_RECESSIVE_TAIL_CERTIFICATE_AUDIT.csv
```
