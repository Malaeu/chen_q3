# STATUS: TRY_CCM_REALIFICATION_CLASS_TRANSFER
```yaml
OPERATIVE_CLASS: TRY_CCM_REALIFICATION_CLASS_TRANSFER
ARTIFACT_TYPE: PAPER_TRANSFER_WITH_EXACT_SCALAR_CHECKS
AUTHOR: Proshka
DATE: 2026-09-20
REPO: Malaeu/chen_q3
BRANCH: rh_clean
BASE_HEAD: e3419c9c78e11c7a64d4d18f2ab891186fb828a3
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
BOUNDARY: OWNER_REQUESTED_EXECUTION_OF_PREVIOUS_CACHE_TRANSFER
PRODUCTION_REQUEST_BINDING: NO_NEW_REGISTERED_TXT
PRODUCTION_LEAN_TRANSACTION: HOLD
SCOPE: FINITE_CELL
VERIFIER: PAPER
IMPORTED_VERIFIER: ARB_INTERVAL
IMPORTED_FULL_CERTIFICATE_RERUN: false
EXACT_CACHE_TRANSFER: PROVED_FROM_PINNED_CERTIFICATE
COMPLEX_CACHE_PRESERVED: true
ANALYTIC_SOURCE_TRANSFER: NOT_PROVED
COFINAL_FAMILY_CERTIFICATE: NOT_PRODUCED
CELL: [13, 120]
FULL_DIMENSION: 241
CERTIFICATE_GAMMA: 1e-56
CERTIFICATE_TAU: 1
MATRIX_UPPER_ENVELOPE: 3000
RAW_NORM_SQUARED_LOWER: 99/100
DISCARDED_REAL_ODD_PLUS_IMAGINARY_MASS_UPPER: 3e-60
ANGULAR_LOSS_UPPER: (100/33)*1e-60
CACHE_RAYLEIGH_UPPER: (2011/220)*1e-57
TRANSFER_LOWER: (113/132)*1e-57
PUBLISHED_COMPLEMENT_FLOOR: 8e-58
EXACT_CHECKS_PASSED: 27
EXACT_CHECK_EXIT_CODE: 0
NEW_ARBITRARY_PRECISION_EIGENSOLVER_RUN: false
LEAN_PATHS: []
LEAN_CHECKED: false
EXPECTED_AXIOM_PROFILES: {}
CLOSES: []
OPENS: []
CATALOG_SUPPLIER_ADDED: false
PROGRESS_CLASS: REPRESENTATION_PROGRESS
PROJECT_COFINAL_PROOF_PROGRESS: false
ROUTE_PROMOTION: false
RH_CLAIM: false
BUS_010_POLICY: VOID
STATE_FILES_CHANGED: false
```

## 1. Что выполнено

[FINITE_CELL | PAPER, с импортом закреплённого ARB_INTERVAL-сертификата]
Закрыт перенос на **нормированный неизменённый комплексный десятичный кэш**.
Мнимая часть и нечётная часть его вещественных коэффициентов сохранены.
Для полного оператора на 241 моде доказано

\[
\forall y\perp q_{\rm cache}:\quad
 y^*(K-a_{\rm cache}I)y\ge8\cdot10^{-58}\|y\|^2. \tag{1}
\]

Это новый вывод из старого полного сертификата, а не новый запуск Arb.
Все числовые неравенства нового переноса проверены точно, через Python
`Fraction`. Ни регрессия, ни округлённое собственное значение не используются.

**Не закрыт** переход от точных десятичных чисел к точному аналитическому
пролатному пробнику. Никакая оценка ошибки его генератора не выдумана.
`CLOSES/OPENS` относятся к каталогу проекта: новых каталогизированных
Lean-поставщиков этот бумажный пакет не объявляет.

## 2. Закреплённые входы

Все пути ниже читаются на `BASE_HEAD`.

| Вход | Git blob |
|---|---|
| `docs/routeB_bus/phase1_results/ccm_control_cell_m13_N120_interval.json` | `3aa72dd98e730847e9799019a82383aed0c46eee` |
| `docs/routeB_bus/phase1_scripts/ccm_control_cell_penalty.py` | `a906f34afaa1bf4e002d5aebd409148f7385d621` |
| `q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/out/portable_k_coeffs_lambda_sq_13_N_120.json` | `67dfbce6c8adff67858a83fc7755a93d175276fd` |
| `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrixN1.lean` | `960f1de9d00e9ca4b309a99fe98be48db40cdb31` |

SHA-256 кэша: `0e5239355c54103859b22d7f753d8cd6765c2c41bcd3ec7f86b20beccc907a88`.
`source_extract.json` сохраняет точные использованные строки двух входных
файлов. Это выдержка, не копия всего кэша и не результат нового его генератора.

[FINITE_CELL | ARB_INTERVAL — импорт сохранённой квитанции, не новый запуск]
При 240 dps сохранённый контроль имеет 121 положительный чётный и 120
положительных нечётных LDL-пивотов и устанавливает

\[
 K-\gamma I+vv^T\succeq0,\qquad \gamma=10^{-56},\quad\|v\|=1,
 \qquad 0<a_v=v^TKv<5\cdot10^{-59}. \tag{2}
\]

Здесь K — та же полная вещественная симметричная CCM-матрица, а
`v = normalize(P_even Re(z))`, где z — исходный десятичный кэш.
Сохраняются G=I, порядок мод -120,...,120, отражение J и ориентация
`W02 - WR - Prime`. Никакого импорта результата для одного чётного блока
как результата для всей матрицы нет.

Доверительная граница явная: исходный Arb-контроль и его источниковое
отождествление используются как ранее сохранённый математический вход.
Новые рациональные проверки не заменяют его повторное исполнение.

## 3. Переход, который устраняет линейную потерю

[ABSTRACT | PAPER]
Пусть K — вещественная симметричная матрица, J — вещественная ортогональная
инволюция и KJ=JK. Пусть для вещественного чётного единичного v выполнены
(2) с произвольными gamma, tau>=0, то есть
`K-gamma I+tau vv^T >= 0`. Предположим независимо K<=M I и 0<=a_v.

Рассмотрим **все** ненулевые комплексные строки

\[
 z=x+u+iw,\quad x=c v,\ c>0,\quad Ju=-u,\quad Jx=x,
 \quad x,u,w\text{ вещественны}.
\]

Положим s=||x||², t=||u||²+||w||², q=z/sqrt(s+t), delta=t/(s+t).

Точное тождество вещественной формы:

\[
 z^*Kz=x^TKx+u^TKu+w^TKw. \tag{3}
\]

Доказательство: для вещественной симметричной K смешанные слагаемые между
Re(z) и Im(z) сокращаются; x^TKu=0 следует из KJ=JK и разных чётностей.
Вещественность K и инвариантность секторов здесь обязательны.

Из (3) следует

\[
 a_q=q^*Kq\le(1-\delta)a_v+M\delta
 \le a_v+M\delta. \tag{4}
\]

Кроме того,

\[
 |v^*q|^2=\frac{s+(v^Tw)^2}{s+t}\ge1-\delta,
 \qquad D:=1-|v^*q|^2\le\delta. \tag{5}
\]

Для любого y перпендикулярного q исходный сертификат даёт

\[
 y^*(K-a_qI)y\ge(\gamma-a_q-\tau D)\|y\|^2.
\]

Действительно, |v*y|²<=D||y||² по ортогональной проекции и
Коши--Буняковскому. Поэтому одновременно для всего описанного класса

\[
\boxed{\beta(q)\ge\gamma-a_v-(M+\tau)\delta.} \tag{6}
\]

Более точный вариант правой части: gamma-a_v-(M-a_v+tau)delta.
В этом пакете достаточно более грубой (6).

Это **не** линейная оценка вида `2||K|| ||q-v||`. Цена восстановленной
мнимой/нечётной примеси квадратична. Это также не заявление, что невязка
равна нулю. Занулились конкретные смешанные члены, а не собственное уравнение.

## 4. Источниковая верхняя оценка K<=3000 I без нового спектра

[FINITE_CELL | PAPER, при входе (2)]
Докажем её из диагональных формул CCM на m=13, N=120. L=log13,
`5/2 < L < 3`, число мод d=241. По формулам источника K действительно
вещественна, симметрична и инвариантна при одновременной замене n,m на -n,-m.

### 4.1 W02

Диагональные W02(n,n) неположительны при n!=0: L²<9 и 16 pi² n²>144.
Для нулевой моды

\[
 W02(0,0)=32\sinh^2(L/4)/L<10,
\]

поскольку `sinh²(L/4)=(sqrt13+1/sqrt13-2)/4<3/4` и L>5/2.
Следовательно, tr(W02)<10.

### 4.2 Архимедова часть

Положим

\[
 C=\gamma_E+\log(24\pi/7)>2,\qquad
 h(x)=e^{x/2}(1-x/L),\quad 0\le x\le L.
\]

Для C>2 достаточно gamma_E>=0, pi>3 и e<3.
Максимум h достигается в x=L-2 и равен `2 sqrt13/(e L)<11/10`:
использованы `sqrt13<11/3`, `e>8/3`, `L>5/2`.

Из буквального интеграла источника

\[
 -WR(n,n)=-C+
 \int_0^L\frac{2(1-h(x))}{e^x-e^{-x}}dx+
 \int_0^L\frac{2h(x)(1-\cos(2\pi n x/L))}{e^x-e^{-x}}dx.
\]

Первый интеграл <=1: 1-h(x)<=x/L и e^x-e^-x>=2x.
Для n!=0 второй не больше `(11/10) J(2 pi |n|)`, где

\[
 J(T)=\int_0^T(1-\cos t)/t\,dt.
\]

На [0,1] интеграл <=1/4. На [1,T], при T=2 pi |n|,

\[
 \int_1^T \cos(t)/t\,dt
 =-\sin1+\int_1^T\sin(t)/t^2\,dt>-2.
\]

Поэтому `J(T)<log T+9/4<7+9/4`: T<960<e^7.
Отсюда для n!=0

\[
 -WR(n,n)<-1+(11/10)(37/4)=367/40.
\]

Для n=0 второй интеграл нулевой и -WR(0,0)<-1. В сумме
`tr(-WR)<-1+240*(367/40)=2201`.
Все интегралы у нуля имеют устранимый предел; оценки применяются на (0,L]
и затем интегрируются. Никакая обрезка архимедова хвоста не введена.

### 4.3 Простые степени

Обозначим

\[
 S=\sum_{k=p^a\le13}\frac{\log p}{\sqrt k}
       \left(1-\frac{\log k}{L}\right).
\]

Член k=13 равен нулю. Поскольку |cos|<=1, `-Prime(n,n)<=2S`.
Точная рациональная оценка из приложенного скрипта даёт S<8/5.
Она использует положительный ряд

\[
 \log k=2\sum_{j=0}^{J-1}\frac{t^{2j+1}}{2j+1}+R_J,
 \quad t=(k-1)/(k+1),\quad
 0\le R_J\le\frac{2t^{2J+1}}{(2J+1)(1-t^2)}
\]

и рациональные нижние границы sqrt(k), проверяемые возведением в квадрат.
Для exp(7)>960 достаточно конечной положительной суммы ряда экспоненты.

Следовательно,

\[
 \operatorname{tr}K<10+2201+2\cdot241\cdot8/5=14911/5.
\]

Из (2) K+vv^T положительна. Поэтому

\[
 \lambda_{\max}(K)\le\lambda_{\max}(K+vv^T)
 \le\operatorname{tr}(K+vv^T)<14916/5<3000. \tag{7}
\]

Мы **не** предполагали K>=0 и не использовали диагональный максимум как
оценку нормы. Здесь существенно сначала получить положительность K+vv^T
из полного сохранённого сертификата и только затем ограничивать его спектр
следом. Для (4) нужна лишь верхняя оценка K, а не модуль его спектра.

## 5. Подстановка неизменённого комплексного кэша

[FINITE_CELL | PAPER]
Для raw cache z определим x=P_even Re(z), u=P_odd Re(z), w=Im(z).
Именно x/||x|| есть v из Phase 1; ничего нового не проецируется вместо q.

Из сохранённых интервальных агрегатов

\[
 \|w\|^2\le2.95565061857647\cdot10^{-60}+2.80\cdot10^{-75},
\]

\[
 A_{\rm asym}\le3.45786\cdot10^{-110}+8.82\cdot10^{-126},
 \qquad\|u\|^2\le(241/4)A_{\rm asym}^2.
\]

Точное сложение даёт t<3e-60. Для нормировки не используется напечатанная
строка `norm=1.0`: семь точных вещественных коэффициентов из кэша дают

\[
 \|z\|^2>0.5399^2+2(0.4741^2+0.3183^2+0.1583^2)
 =0.99378119>99/100.
\]

Все семь полных десятичных значений сохранены в `source_extract.json`.
Следовательно,

\[
 \delta<\delta_*=(100/33)10^{-60}.
\]

С (4)--(7) получаем строгие рациональные верхние границы

\[
 U_D=\delta_*,\qquad
 U_a=5\cdot10^{-59}+3000\delta_*
 =(2011/220)10^{-57}.
\]

И финальную нижнюю оболочку

\[
\boxed{L=10^{-56}-U_a-U_D=(113/132)10^{-57}
 >8\cdot10^{-58}>0.}\tag{8}
\]

Это доказывает (1). Более того, тот же вывод верен **для всех** z из класса
§3 с этим направлением x, `||z||²>=99/100` и `t<=3e-60`, а не только для
одного списка коэффициентов. Эти неравенства не имеют универсальных кванторов
по m,N: это отдельная явно ограниченная область.

## 6. Самоатака, зарегистрированные проверки и предел результата

[ABSTRACT | PAPER]
Три предохранителя были проверены рациональными моделями:
1. Если K не коммутирует с J, реальный even/odd cross term не обязан исчезать.
2. Если K только эрмитова, но не вещественна, cross term Re/Im не обязан исчезать.
3. Если выбросить angular loss tau D, можно получить ложный плюс при
   отрицательной энергии на новом q-перпендикулярном направлении.
Нулевая примесь восстанавливает прежний запас, а не ломает нормировку.

`registration.json` записана до запуска `exact_checks.py`. Все четыре
предсказания оценены: P_TRACE — CONFIRMED; P_CACHE — CONFIRMED с явно
импортированным старым сертификатом; P_REALIFICATION — CONFIRMED;
P_SCOPE — CONFIRMED, точный аналитический источник не накрыт.
Выполнено 27 проверок, exit code 0; полный вывод приложен.
Предварительное чтение источников и пробная арифметика не объявлены
зарегистрированными задним числом. Исторические ставки не изменены.

**Среда:** python-flint здесь не установлен; установка через uv остановилась
на DNS, получение wheel также не удалось. Поэтому никакого нового Arb-запуска
не было. Вместо переноса задачи человеку использован аналитический trace-bound
и точная рациональная арифметика. Lean/lake отсутствуют, Lean не запускался.

[FINITE_CELL | CONDITIONAL]
Для точного аналитического q_source нужна доказанная связь с z. Малость
разности двух квадратур, число dps и точность записи десятичных цифр такую
связь не поставляют. Не доказано, что real-even часть q_source имеет точно
направление x, и не доказана её ошибка относительно этого направления.
Нельзя применить класс §3, просто назвав генератор спектральным.

## 7. K9: переход между представлениями вместо сетки

[ABSTRACT | PAPER]
**BRIDGE_KIND=FORM_IDENTITY.** Реализация комплексной эрмитовой формы
вещественной K на Re(H) плюс Re(H) имеет вид diag(K,K). Дополнительное
расщепление J даёт точный нулевой real-even/real-odd cross term. Сохраняются
форма, нормы, носитель, сдвиг и полная размерность. Это вещественная изометрия,
не заявление о комплексно-линейном унитарном переплетении.

**VANISHING IDENTITY.** (3) уничтожает смешанные члены, а не остаток
собственного уравнения. Два указанных plant показывают границы применимости.

**COLLAPSE OBJECT.** Для семейства тот же механизм потреблял бы согласованные
сертификаты и source-error bounds, обеспечивающие
`gamma_j-a_vj-(M_j+tau_j)delta_j>0`, с отдельным бюджетом преобразования.
Общая формула доказана; нужные семейные входы НЕ доказаны. Для более общей
ошибки real-even направления надо дополнительно сохранить её смешанный член,
а не заменить его нулём. Это выбранное представление для следующего анализа,
не разрешение масштабировать вычисления на m=23/43/83.

Два кандидата для ещё открытого аналитического переноса:
- **Структурное разбиение ошибки генератора.** Отдельные certified bounds для
  real-even shape, real-odd и imaginary error; вторые две цены квадратичны.
  Алгебра мала, сила высокая; аналитическая цена определения source enclosure
  остаётся неизвестной. Проверять сначала уже имеющиеся доказательства генератора.
- **Прямой residual/energy-weighted enclosure.** Сохранить смешанное
  `<(K-a_v I)v,error>` вместо потери `||K||*||error||`; затем проверить (T)
  предыдущего пакета. Алгебра мала, требуются настоящие ошибки источника.
  Если слабая оценка не проходит, это не смерть маршрута.

**DISCRIMINATOR:** для literal source построить действительные Ua, UD и
проверить `gamma-Ua-tau UD>0`. При неположительной нижней оболочке — только
INCONCLUSIVE; отрицательный вывод требует конкретного y и U<0. Не запускать
подбор N до появления плюса и не называть совпадение экспоненциальных фитов
семейной теоремой.

## 8. Закрытие, эпистемика и воспроизведение

Закрыто: перенос старого полного сертификата на неизменённый комплексный
десятичный кэш и весь указанный класс примесей. Вместо нового eig появилась
доказанная верхняя оценка K и конечная рациональная проверка.
Не закрыто: enclosure точного аналитического пробника, семейный spectral floor,
скорость преобразованной ошибки или RH. Одно-cell grinding здесь остановлено.

```yaml
DOWNSTREAM_CONSUMER: Q3.RouteB.sourceCCMComplexTrialComplementFloor
CURRENT_PROVED_TARGET: same_floor_shape_for_exact_complex_decimal_cache
CONSUMER_SOURCE_IDENTIFICATION: STILL_REQUIRED
ACTUAL_CONSUMER_REQUIREMENT: positive_floor_for_unchanged_analytic_source_same_K_metric_shift
ORIGINAL_REQUESTED_OBJECT: explicit_Ua_UD_from_new_matrix_vector_run
ORIGINAL_OBJECT_IS: NOT_NECESSARY_FOR_CACHE_TRANSFER
KNOWN_WEAKER_INTERFACES:
  - realification_form_identity_plus_saved_certificate_plus_trace_bound_imply_8
  - same_class_source_enclosure_would_specialize_6_to_analytic_source
FAILURE_TYPE_FOR_ANALYTIC_APPLICATION: NO_DERIVATION
EPISTEMIC_STATUS_FOR_ANALYTIC_APPLICATION: RESEARCH_DEBT
NOVELTY_AXIS: realification_and_trace_bound_replace_new_full_matrix_computation
MATHEMATICAL_NOVELTY_CLAIM: false
REOPEN_TRIGGER: certified_analytic_coefficient_error_in_the_same_realification_coordinates
KILL_SCOPE: NONE
ROUTE_FAMILY_DEATH: false
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 3
```

Из любой директории, для извлечённых рядом файлов:

```bash
python /path/to/exact_checks.py
```

В репозитории, из его корня, команда без заполнителей:

```bash
python docs/routeB_bus/proshka/ccm_realification_transfer_2026-09-20/exact_checks.py
```

`/path/to/exact_checks.py` обозначает фактический путь к скрипту, например
`/mnt/data/ccm_exec/result/exact_checks.py`. Дополнительные пакеты не нужны.
Успех проверяет новый рациональный расчёт; он НЕ означает повтор исходного
Arb-контроля. `result.json` явно сохраняет `arb_rerun:false`.

Публикация: один новый пакет в
`docs/routeB_bus/proshka/ccm_realification_transfer_2026-09-20/`, одним коммитом
`[Proshka]`. Старые сертификаты, источники, статусы и протокол не меняются.
После записи проверяются состав diff и Git blobs. SHA коммита сообщается
владельцу после доставки, не вписывается в само-хеширующий артефакт.
Новых Lean-файлов нет, kernel handoff неприменим. Codex не запускался:
проверку этого пакета выполнила Прошка.
