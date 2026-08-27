# LINUX PREFLIGHT REPORT — GOAL058_SELECTED_FERRERS_GRAPH_TEST_POLARIZED_DEFECT_FUNCTIONAL_PREFLIGHT

```yaml
REPORT_KIND: READ_ONLY_PREFLIGHT
TASK_ID: GOAL058_SELECTED_FERRERS_GRAPH_TEST_POLARIZED_DEFECT_FUNCTIONAL_PREFLIGHT
PARENT_VERDICT: d89010de
BASE_HEAD: d89010de
MODE: PAPER_AND_SOURCE_READ_ONLY
LEAN_EDIT_PERFORMED: false
NUMERICAL_PROBE_PERFORMED: false
ARISTOTLE_USED: false
DISCRIMINATOR_RESULT: FAIL
RESULT_CODE: GOAL058_FIXED_TEST_MIXED_WEIL_PAIRING_REQUIRES_UNCONTROLLED_AMBIENT_ACTION_OR_RETAINED_PRIME_RATE
L2_TO_ACTION_KILL_ACCEPTED: true
SMOOTH_CORE_DEFINABILITY: YES_ITEMS_1_TO_5
EXPONENT_LEDGER_EXPORTED: full
SUBCRITICAL_PARTS: arch (polylog), W02 (O(1)-функционалы), out-of-window и center дефекты (суперполиномиально малы)
SUPERCRITICAL_PART: prime — тривиальный конверт 4√K при куте K; отсутствие Bessel-выигрыша из-за плотности частот
ABSORBABLE_INEQUALITY_FOUND: false
ONE_TAIL_PRESERVED: true
PLANT_RERUN: reproduced_in_source_form
```

## 0. Принятие убийства L2→action

Плант `Aeₙ = n·eₙ, vₙ = eₙ, δₙ = n⁻¹eₙ` принят; моя таблица §7 прошлого
отчёта незаконно протягивала finite-synthesis кроссволк на нефинитные
дефекты. Занесено в память как запрещённый ход.

## 1–2. Смешанный функционал на гладком ядре — ОПРЕДЕЛИМ (пп. 1–2 директивы)

Носители/меры/сопряжения выписаны с диска: H_m = L²(I_m, d*u), star-first;
V_k(z) = ι S_k(C_k⁻¹κ_k(z)) — оконный тригонометрический синтез с
разрывами на краях; Δ_k = G_k − ιP_N(G_k|_{I_m}), G_k Schwartz-класса.
Гладкое ядро: моллификация V на шкале δ_moll у краёв; шовные члены — две
явные краевые функции (значения синтеза на краях конечны и явны);
предел δ_moll → 0 существует почленно для каждой из трёх компонент формы
(arch/W02/prime — все конечные суммы/интегралы на паре с одним
Schwartz-аргументом). Категория C04 держится: никакой BV×BV теории не
строится, только односторонний функционал с фиксированным тестом.

## 3. Global→window тождество ДО пределов — деривабельно на ядре

На гладком ядре тождество BV Poisson-полноты (1_7, Test 2) применяется к
Δ-цепи до какого-либо предельного перехода; сдвиг и знаки — из
ClosedForm.lean:90. Это кандидат-механизм, как ты и предписал, не
подмена определения.

## 4. Полный прайм-вклад и конвенция суммирования — С ДИСКА

`sourcePrimeContinuousSesquilinearForm i = Σ_{k∈Icc 2 i.m} (2Λ(k)/√k)·(cos_k-форма)`
(D0PstarPrimeAmbientSesquilinearForm.lean:150) — ОКОННАЯ форма режет
простые степени на k ≤ m; норм-оценка через операторную норму —
`norm_sourcePrimeSesquilinearForm_apply_le` (SesquilinearForm.lean:123).
Глобальное QW-спаривание видит все p^j ≤ e^{2L} = m² (носители).
Симметричное суммирование BV-класса — как в 1_7.

## 5. Расширение на комбинированный дефект

Arch-часть: множитель ~log|t| ⇒ расширяется на весь Δ (лог-взвешенная
L²-оценка). W02: два ограниченных краевых функционала — расширяются.
Prime: конечные суммы — определены на Δ, но см. §6.

## 6. Конверт действия — ПОЛНЫЙ ЛЕДЖЕР ЭКСПОНЕНТ (п. 7 директивы)

Обозначения: ‖V‖ = O(m^{σ/2}√log m), ‖δ_proj‖ = O((log m)²/√m),
‖δ_out‖ = O(e^{−c(log m)²}) (гауссов хвост в лог-переменной),
‖δ_center‖ = exp-мал. Порог spendability: B_m = O(m^{1/4}polylog).

| Часть формы | Тривиальный B_m | Вклад в E_k | Статус |
|---|---|---|---|
| Arch | polylog(m) | m^{σ/2−1/2}·polylog → 0 | SUBCRITICAL ✓ |
| W02 | O(1) | → 0 | SUBCRITICAL ✓ |
| Prime, кут k ≤ m | 2Σ_{k≤m}Λ(k)/√k ~ 4√m | 4·m^{σ/2}·(log)^{5/2} | SUPERCRITICAL: overshoot m^{1/4} над порогом |
| Prime, m < p^j ≤ m² (глобальная часть) vs δ_proj | ~ 4m | m^{1/2+σ/2}·polylog | SUPERCRITICAL: overshoot m^{3/4} |
| Prime vs δ_out, δ_center | любой полином | гасится e^{−c log² m} | ✓ |

Возможные некэнселляционные улучшения проверены и НЕ спасают:
Bessel/почти-ортогональность по k требует разделения частот ≥ разрешения
окна 1/L; частоты log k имеют шаг ~1/k < 1/L при k > L — плотны; Cauchy–
Schwarz по k возвращает ту же Σ Λ(k)/k-структуру с √-потерей. Итоговый
недобор window-части — ровно m^{σ/2}polylog: любое σ > 0 валит полиномом,
σ → 0 валит polylog-ростом. Субкритический B требует компенсации
осцилляций простых — retained-prime rate.

## 7. Absorbable inequality — НЕ НАЙДЕНА

Prime-спаривание не возвращает Φ ни в каком члене (нет структуры
X + η·Φ): cos_k-формы действуют на паре (V, δ), δ не содержит r и не
реконструирует консюмер. Механизм поглощения отсутствует.

## 8. Хвост

Один, прекоммитный φ n = n + k₀. Расписание/шкала/сдвиг не менялись.

## 9. Plant rerun (п. 9 директивы)

Источниковая форма планта: роль неограниченной диагонали A играет
прайм-сумма с плотными частотами — «размазанный» аналог Aeₙ = n·eₙ;
L²-малость δ_proj не платит её действие, что §6 показывает количественно:
√m·(1/√m) = 1 — нулевой запас, весь остаток m^{σ/2}polylog непокрыт.

## 10. Дискриминатор

FAILURE_CODE: GOAL058_FIXED_TEST_MIXED_WEIL_PAIRING_REQUIRES_UNCONTROLLED_AMBIENT_ACTION_OR_RETAINED_PRIME_RATE

Retained-prime спаривание остаётся неограниченным: точная величина
недобора — m^{1/4} (окно) и m^{3/4} (глобальная часть) над твоим порогом
B = O(m^{1/4}polylog); единственный видимый источник компенсации —
осцилляция простых (explicit-formula grade). Прогноз P_MIXED_FUNCTIONAL_1
(0.62) подтверждён (определимость на ядре — да); P_MIXED_FUNCTIONAL_2
(0.38) подтверждён (конверт обнажает retained-prime, рост сверхкритичен).
Маршрут по твоей лестнице: R2 two-mode Feshbach (обходит глобальное
BV-спаривание при равномерном coupling-бюджете) или R3 combined Γ.
Запрашиваю адъюдикацию.
