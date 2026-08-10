# PROSHKA REQUEST — аудит кода и измерений Phase 4

```yaml
TRANSACTION: PHASE4_CODE_AND_MEASUREMENT_AUDIT
CLASS: DELEGATED_CODE_AND_RESULT_REVIEW
CHAT: SAME_LIVING_PHASE_CHAT
PREDECESSOR_VERDICTS:
  - PROSHKA_VERDICT_GLOWER_EXACT_CLOSURE_2026-08-09
  - PROSHKA_VERDICT_GLOWER_TAIL_THEOREM_AND_HEAD_DRIFT_2026-08-10
  - PROSHKA_VERDICT_GLOWER_FULL_RESIDUAL_BETA_MOMENT_2026-08-10
MODE: READ_ONLY_NUMERICAL_PREFLIGHT
LEAN_EDITS: NONE
REPO_WRITES: NONE_BEYOND_JOURNAL_AND_SCRIPTS
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
G2_CCM: FROZEN
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
BIRMAN_SCHWINGER: NOT_ACTIVATED
```

## Что просим

Проверить **код и результаты** Phase 4 и сказать, что они означают. Мы приводим только
измерения и ссылки на файлы; интерпретацию не даём намеренно — часть наших прежних
выводов оказалась неверной, и мы не хотим повторять это в третий раз.

Конкретно:

1. Считает ли каждый скрипт то, что заявлено в его docstring.
2. Верны ли измерения, и если нет — где именно ломается.
3. Что означает расхождение между результатами (перечислено в конце).
4. Какие из них артефакты метода, а какие — факты о задаче.

Всё воспроизводимо одной командой из корня репозитория; окружение — `.venv`
(`python-flint 0.8.0`, `mpmath 1.4.1`).

---

## Файлы

### Источник матрицы (не менялся)

| файл | что делает |
|---|---|
| `docs/routeB_bus/phase1_scripts/ccm_control_cell_penalty.py` | `CCMArbBuilder`: source-side `w02 − wr − prime`, `parity_blocks()` → even/odd, `interval_ldlt()`. Все скрипты Phase 4 импортируют его, а не копируют формулы |

### Скрипты Phase 4

| файл | что считает | результат |
|---|---|---|
| `phase4_scripts/glower_tail_floor_probe.py` | `K_odd[n₀:,n₀:] ⪰ μI` по срезам | `R(μ=1) = 70` |
| `phase4_scripts/glower_corrected_head.py` | `B_c − d⁻¹R_c*R_c ⪰ 0` при `R = 70` | PASS при `N = 120…960` |
| `phase4_scripts/glower_head_drift_ledger.py` | ledger Мифоса: профиль + табличная мажоранта | `γ = 1.869492e-55` при `S = 480` |
| `phase4_scripts/glower_full_residual_prefix.py` | `r_k = E_k + Σ D_c(k,m)Y_m`, `k > 480` | `Σ‖r_k‖² = 7.583235e-02` |
| `phase4_scripts/glower_gram_form_check.py` | `B_480 − d⁻¹Σ r_k r_kᵀ` через `interval_ldlt` | NONPOSITIVE_PIVOT, пивот 55/70, `−1.0699` |
| `phase4_scripts/glower_low_spectrum_preflight.py` | спектр `B_480`, `‖P·G·P‖` по размерностям | таблица ниже |
| `phase4_scripts/glower_relative_form_check.py` | `max eig(B⁻¹G)` | `mu_max = 1.049387747` |
| `phase4_scripts/glower_beta_cocycle_check.py` | коцикл `τ(k,n)(k−n)+τ(n,m)(n−m)−τ(k,m)(k−m)` | `~1e-62` при масштабе `τ ~ 1e-1` |
| `phase4_scripts/yoshida_analytic_N.py` | цепочка Yoshida [33, Lemma 3] для `m = 13` | `N > 1.5488372e+34` |

### Логи и профили

```
phase4_results/glower_ledger_960.log
phase4_results/glower_ledger_960_profile.csv
phase4_results/residual_prefix_960.log
phase4_results/residual_prefix_960_profile.csv
phase4_results/low_spectrum_preflight.log
phase4_results/relative_form.log
```

### Журнал и материалы

```
docs/routeB_bus/proshka/PROSHKA_VERDICT_GLOWER_EXACT_CLOSURE_2026-08-09.md
docs/routeB_bus/proshka/PROSHKA_VERDICT_GLOWER_TAIL_THEOREM_AND_HEAD_DRIFT_2026-08-10.md
docs/routeB_bus/proshka/PROSHKA_VERDICT_GLOWER_FULL_RESIDUAL_BETA_MOMENT_2026-08-10.md
docs/routeB_bus/PHASE4_RESULTS_2026-08-10.md          R1…R10
docs/routeB_bus/phase4_scripts/CODEX_RUNCARD_glower_ledger_2026-08-10.md
docs/routeB_bus/litreview/SUZUKI_ASPECTS_2206_USAGE_CARDS.md
docs/routeB_bus/litreview/YOSHIDA_HERMITIAN_1992_USAGE_CARDS.md
docs/routeB_bus/litreview/pdfs/2206.03682.pdf
docs/routeB_bus/litreview/pdfs/yoshida_hermitian_forms_1992.pdf
```

---

## Измерения

Параметры везде: `m = 13`, сектор `ODD`, `c₀ = 1e-58`, `d = 1 − c₀`, голова `R = 70`.

### Вход 1 — хвостовой пол

```
R(μ=1) = 70          n₀ = 69 fail, n₀ = 70 PASS, шаг сетки 1
устойчиво:           N = 120 → 70,  N = 240 → 70,  N = 90/180 → 72 (сетка 4)
минимальный пивот при переходе:
  N = 240   0.7342389581660078168603269624116358064253
  N = 480   0.7342389581660078168603269624116358064253   (совпадает до 40-й цифры)
```

### Вход 2 — corrected head

```
N      мин. пивот B_c − d⁻¹R_c*R_c      вердикт
120    2.79613402533503557887e-10       PASS
240    2.76873186711502600072e-10       PASS
480    2.72855901228750818199e-10       PASS
960    2.69234436224724184746e-10       PASS

‖R_c‖_F ≤ 7.49e-285        штраф d⁻¹‖R_c‖² ≤ 5.61e-569
```

### Ledger (скрипт Мифоса)

```
S = 240   NONPOSITIVE       S = 360   NONPOSITIVE       S = 480   PASS
γ = 1.869492e-55,  τ = 0.5,  для срезов N' ∈ (480, 960]
при N = 240:  S* ≤ 180,  γ = 1.398238e-55
```

### Полная невязка, префикс

```
Σ_{480<k≤960} ‖r_k‖²  = 7.583235e-02
Σ_{480<k≤960} ‖E_k‖²  = 5.312379e-02
построчно ‖E_k‖²/‖r_k‖²:  0.60 … 1.36
профиль сырой строки:  k²‖E_k‖² = 45.5 (k=200), 53.0 (400), 51.0 (600), 47.9 (959)
```

### Спектр `B_480` и проекция Грама

```
λ[0]  = 2.3059968e-55      λ[6]  = 6.3898217e-20
λ[1]  = 3.1569743e-48      λ[7]  = 1.5633464e-15
λ[2]  = 1.5426847e-41      λ[8]  = 2.2123841e-11
λ[3]  = 1.1739989e-35      λ[9]  = 8.1709083e-8
λ[4]  = 7.6241015e-30      λ[10] = 2.6538305e-4
λ[5]  = 7.3717715e-25      λ[11] = 9.0730583e-2
                           λ[69] = 5.2492112

dim    λ[dim-1]      ‖P·G·P‖      ‖P·G·P‖/λ
  1    2.306e-55     3.65047e-56    0.158303
  2    3.157e-48     3.81714e-49    0.120911
  3    1.543e-41     1.26169e-42    0.081785
  4    1.174e-35     6.00349e-37    0.051137
  5    7.624e-30     3.09649e-31    0.040615
  6    7.372e-25     3.18915e-26    0.043262
  7    6.390e-20     4.17357e-21    0.065316
  8    1.563e-15     1.42102e-16    0.090896
  9    2.212e-11     2.86994e-12    0.129721
 10    8.171e-8      1.32670e-8     0.162368
 11    2.654e-4      5.41642e-5     0.204098
 12    9.073e-2      1.79039e-2     0.197330

след полного Грама = 0.075832354
```

### Три формы штрафа на одних данных

```
B_480 сам по себе                        INTERVAL_POSITIVE_DEFINITE
B_480 − p·I,  p = 7.583e-02              провал
B_480 − d⁻¹·Σ_k r_k r_kᵀ  (interval LDLᵀ) NONPOSITIVE_PIVOT, пивот 55/70, −1.0699
max eig(B⁻¹G)                            mu_max = 1.049387747
                                         mu_min = −2.686161087e-194
```

### Проверка source identity вашего последнего вердикта

Коцикл `τ(k,n)(k−n) + τ(n,m)(n−m) − τ(k,m)(k−m)` на нашей `tau_entry`:

```
(k,n,m)        невязка        масштаб τ
(5,3,1)        3.889e-62      1.05e-01
(10,7,2)       0.000e+00      1.26e-01
(20,11,4)      1.945e-62      7.41e-03
(31,17,5)      1.167e-61      4.39e-02
(37,23,13)     7.779e-62      1.18e-02
(12,9,6)       1.556e-61      3.88e-01
```

### Цепочка Yoshida для сравнения

```
C₁(a₀) = 5.19027975     C₂(a₀) = 9  (список 2,3,4,5,7,8,9,11,13)
C > μ + C₁ + 2C₂ = 24.19027975
t₀ ≈ 1.7419251e+11      C₃ ≈ 4.6470562e+34      N > 1.5488372e+34
```

---

## Расхождения, которые просим объяснить

1. **`B_480 − d⁻¹Σ r_k r_kᵀ`**: `interval_ldlt` даёт NONPOSITIVE_PIVOT с пивотом `−1.0699`;
   `max eig(B⁻¹G)` даёт `1.0494`. Обусловленность `B_480` равна `5.2492/2.3060e-55`.

2. **`‖P·G·P‖/λ`** лежит в `0.04…0.20` на всех двенадцати проверенных размерностях, при
   `mu_max = 1.0494`.

3. **Ваш п. 44** (matrix-valued Gram останется жизнеспособным) против п. 3 наших измерений
   выше.

4. **`‖r_k‖² > ‖E_k‖²`** в сумме (`7.583e-02` против `5.312e-02`) при построчном отношении
   `0.60…1.36`.

5. **`S*` растёт с `N`**: `≤180` при `N = 240`, `=480` при `N = 960`, при том что `γ`
   вырос с `1.398e-55` до `1.869e-55`.

6. Ваш п. 26 требует `|B₀| < 4.736e-27`; мы `B₀` **не считали** — просим указать, считать
   ли его до вашего ответа.

Наш журнал `PHASE4_RESULTS_2026-08-10.md` содержит наши прочтения этих чисел. Они могут
быть неверны; проверять просим числа и код, а не наши формулировки.
