# LINUX PREFLIGHT REPORT — GOAL058_SELECTED_FERRERS_RAYLEIGH_EXCESS_COMPACT_RATE_PREFLIGHT

```yaml
REPORT_KIND: READ_ONLY_PREFLIGHT
TASK_ID: GOAL058_SELECTED_FERRERS_RAYLEIGH_EXCESS_COMPACT_RATE_PREFLIGHT
PARENT_VERDICT: 809b776b (Rayleigh-excess representation selected)
BASE_HEAD: 809b776b
MODE: PAPER_AND_SOURCE_READ_ONLY
LEAN_EDIT_PERFORMED: false
NUMERICAL_PROBE_PERFORMED: false
DISCRIMINATOR_RESULT: FAIL
RESULT_CODE: GOAL058_RAYLEIGH_EXCESS_LOWER_ENVELOPE_SOURCE_NOT_AVAILABLE
GENERIC_PORT_STATUS: PAPER_READY
KEY_FINDING: FLOOR_ROUTED_EXCESS_IS_TEMPLE_EQUIVALENT_TO_RESIDUAL_ENERGY
FILES_READ_PER_DIRECTIVE: all_five
SHELF_ASKED: ground-eigenvalue-lower-bound, rayleigh-excess, temple, Schur-complement, PSD-certificate
```

## 1. Точные объекты на одном хвосте — ЕСТЬ

- `ε_k`: нижнее собственное значение `sourceCCMFiniteMatrix` на выбранном
  индексе; извлекается floor-пакетом (`gtt_ground_extraction` /
  `sourceCCMFinite_simpleGround_gap_tracking_of_complementFloor`,
  `CCMProposition59ComplexTrialComplementSpectral.lean:285`).
- `a_k`: `selectedFerrersFiniteCCMRayleigh P k` — та же матрица, та же строка,
  тот же хвост. Одно точное семейство, без пересборки.
- `sourceCCMFiniteMatrix i = (ccmWeilMatFinite i.m i.N : ℂ)` — конечная
  матрица ВЕЙЛЯ (`D0PstarCCMFiniteSourceResidual.lean:94`). Нижний конверт
  для ε_k есть квантитативная почти-позитивность растущих окон Вейля —
  это определяет всю цирклярную геометрию ниже.

## 2. Generic-порт — ГОТОВ (прогноз 0.98 подтверждён)

`weighted_projective_defect_le_rayleigh_excess_div_gap`
(`WeightedRayleighProjectiveDefect.lean:43`, чистое, 61 строка файла):
инстанцирование — спектральные веса `w_i = |⟨v_i,q⟩|²` в собственном базисе,
`level_i = μ_i − ε_k`, `gap = β − a_k` (поставляется penalty-пакетом:
`H2a_SimpleEvenGround_FromPenaltyCoercivity` даёт `μ − λ₁ ≥ β − a`),
`α = a_k − ε_k` — спектральное разложение рэлеевского значения. Выход:

    1 − |⟨ξ_k, q_k⟩|² ≤ (a_k − ε_k)/(β − a_k)

Порог: с центрирующим портом и P59-конвертом (`kernelL2² ≤ C_σ·λ^{2σ}·L`,
оба PAPER_READY из 406d4988) и phase-alignment трансфером:

    sup_{|Im z|≤σ} ‖G_k(z) − P_k(z)‖² ≤ C_{σ,β} · λ^{2σ} · L_k · (a_k−ε_k)/(β−a_k)

Один L, как ты и предсказал. Инстанцирование — сборка, новой аналитики нет.

## 3. КЛЮЧЕВАЯ НАХОДКА: floor-маршрут excess эквивалентен остатку

Разложение единичного `x = c·q + w`, `w ⊥ q`:

    ⟨x,Kx⟩ = |c|²·a + 2Re(c̄·⟨w, r⟩) + ⟨w,Kw⟩

потому что `⟨q,Kw⟩ = ⟨Kq,w⟩ = ⟨r,w⟩` при `w ⊥ q` — перекрёстный член
q-линии ЕСТЬ остаток (твой §5 в точности). Минимизация под полом
`⟨w,Kw⟩ ≥ β‖w‖²` даёт Temple:

    δ_k := a_k − ε_k ≤ E_k/(β − a_k)

и это уже в корпусе: `rayleigh_excess_le_residual_sq_div_gap_sub`,
`rayleigh_excess_le_two_mul_residual_sq_div_gap`
(`WeightedSpectralTempleCore.lean:81,90`). Обратно
`weighted_residual_sq_ge_rayleigh_excess_mul_gap_sub` даёт двустороннее
сравнение. Вывод: **при действующем complement-floor входе excess и
резидуальная энергия — rate-эквивалентные объекты** (с точностью до gap- и
L-множителей). Дуал экономит один L в консюмере, но источниковый вопрос —
та же стена: поставщика `E_k`-распада нет (ратифицировано 6a47f79c).

## 4. Полочный аудит поставщиков нижнего конверта (все четыре класса)

| Класс | Что есть | Статус для δ_k |
|---|---|---|
| Temple | `WeightedSpectralTempleCore` 81/90, `TempleResidualGapEnvelopeTransfer` 15/56 | маршрутизирует в E_k — убитая стена |
| Penalty | `H2a_SimpleEvenGround_FromPenaltyCoercivity` (`H2aPenaltyCoercivity.lean:395`) | РЕСИВЕР: PSD-сертификат `K − βG + τ(Gq)(Gq)* ⪰ 0` в ГИПОТЕЗАХ; поставщиком не является |
| Sector-floor | odd-sector коэрцитивность (`D0PstarSourceWeilOddTailExplicitCoercivity`), parity-разложение | грунт лежит в ЧЁТНОМ секторе; нечётная коэрцитивность чётный excess не ограничивает |
| Сдвиговый PSD | `ccmShiftedWeilMatFinite_posSemidef_of_bottomRayleigh` | тавтология (сдвиг на нижнее с.з. всегда PSD) |
| Perturbative gap | `PerturbativeTrueGapLower` | оценка ЗАЗОРА, не низа |
| Schur / finite certificate | журнал 2026-08-11: точные Schur-эксперименты `EXPERIMENTAL_NOT_PROMOTED`; kill «full_matrix_gram_existence_as_supplier»; финальный Schur-узел в FINITE_CERTIFICATE_PRINCIPLE помечен «будущий узел» | теоремы НЕТ |

Отрицательное утверждение проверено `./ask.sh` (СТЫКОВКИ) по пяти запросам,
не grep-ом.

## 5. Аудит цирклярности

- (a) Temple-путь: не цирклярен, но упирается в E_k — killed wall.
- (b) Кофинальный PSD-сертификат `K_k − (a_k−δ_k)I ⪰ 0` растущих окон Вейля:
  файрвол срабатывает — семейство таких сертификатов с ratem И ЕСТЬ
  целевая позитивность (заключение в маскировке). Единственная
  потенциально нецирклярная форма — фиксированный конечный блок.
- (c) Fixed-block Schur: низкополосный блок ФИКСИРОВАННОГО (не зависящего
  от k) размера + независимая хвостовая коэрцитивность + контроль
  interaction-блока. Хвост: нечётная часть есть; чётный хвост — открытая
  стройка. Interaction-блок — прайм-моды; стоит kill 2026-08-10:
  «entrywise до cancellation ломает `n·β(k) − k·β(n)`» — контроль блока
  снова требует сохранённой прайм-компенсации. Нецирклярно, но упирается
  в ту же прайм-стену в операторно-нормной форме.
- Глобальная позитивность Вейля, RH, искомая сходимость, `W_k → 0` — нигде
  не использованы и не понадобились ни в одном из путей выше.

## 6. Сравнение с Γ-маршрутом (retained-prime)

Под действующими floor-гипотезами: `δ_k ≤ E_k/(β−a)` и `E_k ≤ L·G_k/c*` —
дуал потребляет ТОТ ЖЕ аналитический объект уровнем выше. Выигрыш дуала:
один L в консюмере и отсутствие производной. Проигрыш: floor-маршрут не
открывает независимого источника. Независимым дуал становится ТОЛЬКО с
floor-независимым сертификатом (c) — а его interaction-блок и есть
прайм-действие. Честный итог: **обе дороги стоят перед одной стеной —
сохранённая прайм-осцилляция; дуал делает стену на один L тоньше.**
Твой прогноз P_RAYLEIGH_EXCESS_SOURCE_1 (0.62) подтверждён с уточнением:
первый источниковый вопрос — нижний конверт, но при текущих входах он
Temple-эквивалентен остатку.

## 7. Два ремонта представления (FAIL-ветка)

**REP-A — fixed-block Schur finite certificate (PRIMARY).**
Довести архитектуру FINITE_CERTIFICATE_PRINCIPLE до теоремы: (i) чётная
хвостовая коэрцитивность высокополосных мод (симметричный аналог нечётной,
та же техника Bonami–Karoui/PSWF-сепаратора); (ii) контроль
interaction-блока С СОХРАНЕНИЕМ прайм-компенсации (суммарно, не entrywise —
уважая kill 2026-08-10); (iii) низкополосный блок фиксированного размера —
один сертификат кофинально, без нумерики в кофинальном кванторе.
Kill-power 10/10 (в обе стороны: либо сертификат, либо прайм-стена получает
финальное имя в операторной норме), cost 9/10, route-fit 9/10.

**REP-B — retained-prime Γ-маршрут (RUNNER-UP, твой R2).**
Cancellation-preserving оценка прямо на `Γ_k = D_k r_k` c W02 endpoint
trace. Kill-power 10/10, cost 10/10, route-fit 9/10.

## 8. Код

FAILURE_CODE: GOAL058_RAYLEIGH_EXCESS_LOWER_ENVELOPE_SOURCE_NOT_AVAILABLE

Generic-порт §2 (PAPER_READY) сохраняю в леджере: он нужен обоим ремонтам.
Запрашиваю адъюдикацию REP-A против REP-B.
