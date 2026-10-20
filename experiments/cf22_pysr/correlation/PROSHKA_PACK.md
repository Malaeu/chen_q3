# PROSHKA EVIDENCE PACK
Generated: 2026-10-20 12:44:58
Repo: /Users/emalam/GitHub/rh_lean_01_2026

EVIDENCE PACK ONLY. This is not the authoritative Proshka request, not a dispatch payload, and not a transport/front door. The exact request must be a separately source-locked UTF-8 .txt validated by workflow_runtime.py review-plan in the existing living phase chat.


## Scope of this pack

New files: experiments/cf22_pysr/correlation/. Continuation pointer: docs/Codex/NEXT.md.
Historical input commit: f1993ec6a7933418c38c305a13a3221037b9447a.
The source range below describes the prior experiment; the included working-tree
report describes the new decomposition. Unrelated working-tree status is omitted.
Complete interval and per-pair data remain in summary.json, verification.json
and decomposition.json.gz in the same directory; they are not inlined here.

## rh_clean...origin/rh_clean
 M CLAUDE.md
 M docs/Codex/NEXT.md
 M docs/Progress_Log.md
?? 1653edc4-9853-46db-bd37-73595b48bfc8-aristotle.tar.gz
?? docs/literature/openai_math_2026-10-07/RH_PROPERTY_COMBINATION_SCREEN_2026-10-08.md
?? docs/literature/openai_math_2026-10-07/RH_PROPERTY_COMBINATION_SOURCES_2026-10-08.json
?? docs/session_protocols/team-record-event-055ee7e4e26f127ab67b8a0f47f4d5e885b6928ac1bea330ce6f55aef109b6e3.json
?? docs/session_protocols/team-record-event-1d97444ac486c060a38d50b3b5d33b42c3f4ae19595735f937f25eb14b46662d.json
?? docs/session_protocols/team-record-event-389a5c4f89ec6da4ce0270c7bd2a7316fead82658605fa04b0fb6ab739f46a37.json
?? docs/session_protocols/team-record-event-3e06872f472fe0700f175339568ad62c2d6556707707da3735cc09974dee086c.json
?? docs/session_protocols/team-record-event-41914a46be214ce2bb0e621f31853f60fd1036ce47aa8790de172d4cd180311d.json
?? docs/session_protocols/team-record-event-490334702230f961527794a8ffaa16f196cf293159a07c94ac27a83fd4bc23fd.json
?? docs/session_protocols/team-record-event-4f4162246f609dbe887bde745ee81a8f77a48f3fdaf2af820968e322f5137771.json
?? docs/session_protocols/team-record-event-67d5d6dedf97a160c314e8376b066c8e85d9635f5687d37e9a2165ed18b7f4f6.json
?? docs/session_protocols/team-record-event-79510168fa1b50f96f6893f9fd6954a5adf851894909486dbb9d29ca5a0cdb81.json
?? docs/session_protocols/team-record-event-bd3b02662ea9bd9345db19bed21eca207ed6f59840bded472da73eba43c83b76.json
?? docs/session_protocols/team-record-event-da0a4ed616968a741f8fa49910a7259786301f6e92082fb16e71780bb8c76e07.json
?? docs/session_protocols/team-record-event-db7c63bd1405028e90f0f7e757d7af65f66314f3e921cfbfc8c553dba0c81784.json
?? docs/session_protocols/team-record-event-f32345579a30293d8f5d124ea149151ce196234e32df11f97f68fbc843e451e4.json
?? experiments/cf22_pysr/correlation/
?? graphify-out/
?? orchestrator/state/knowledge.db
?? q3.lean.aristotle/EnvDumpRun_niy6d214.lean
?? q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersCutoffGreen.lean
?? q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFokasCenteredResidual.lean
?? q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFokasGreenSourceBridge.lean
?? q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFokasGreenTrackingBudget.lean
?? q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFokasTrackingBudget.lean
?? q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFokasWindowResidual.lean
?? q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersJointGreenMatrixDefect.lean
?? train-preview.png


## Git log

f1993ec6 [Mac rh_clean] Measure full CF22 nonunit mask response with exact periodic sums


## File: experiments/cf22_pysr/correlation/RESULT.md

# §6 выполнен: три подписанных вклада сохранённой C

Дата: 2026-10-20. Источник: `f1993ec6a7933418c38c305a13a3221037b9447a`.
**FINITE_SIGNED_DECOMPOSITION — 20 конфигураций, обратная сборка проверена.**
Новых сырых сумм: **0**. Новых PySR fits: **0**. CF22 не улучшена; RH не доказана.

## Результат для Прошки

Разбор подтверждает, что масочный отклик не описывает всю C. Нетронутые
колонки дают ненулевой вклад, а перекрёстный вклад может быть главным
положительным слагаемым. Например, при **U64,P13**:

```
нетронутые / нетронутые       +2.289643268113
нетронутые / затронутые      +10.370283579123
затронутые / затронутые       -0.178685229776
                            ----------------
полная C                    +12.481241617461
```

Это три статьи одного подписанного баланса. Отрицательный вклад последней
группы не перекрывает две положительные. Отбрасывание перекрёстной группы
потеряло бы основной положительный вклад именно в этой конфигурации.

В отличие от предыдущего масочного разбора, теперь сохранены вклады каждой
пары, её полный период, примитивный проводник и общий нулевой фактор.

## Определение групп и таблица

RR: обе колонки P-грубые, то есть не имеют простого идеального делителя нормы
<=P. RA: ровно одна такая колонка; обе ориентации упорядоченной пары уже
включены множителем 2Re. AA: обе колонки затронуты масками. Исходная диагональ
исключена ровно один раз. Все значения ниже округлены из наружных Arb-интервалов.

| U | P | Колонки R/A | C_RR | C_RA | C_AA | Сумма = прежняя C |
|---:|:---|:---:|---:|---:|---:|---:|
|48|P0|21/0|-3.043293550251|0|0|-3.043293550251|
|48|7|16/5|-10.461646059497|0*|-1.678903857534|-12.140549917030|
|48|13|16/5|-17.435270146014|0*|-0.708129128359|-18.143399274373|
|64|P0|33/0|+2.838486049901|0|0|+2.838486049901|
|64|7|25/8|+1.374306151769|+6.000890690801|-0.768533197845|+6.606663644725|
|64|13|25/8|+2.289643268113|+10.370283579123|-0.178685229776|+12.481241617461|
|96|P0|54/0|+4.401724968931|0|0|+4.401724968931|
|96|7|36/18|+4.377460618073|+4.123193960253|-0.864401294512|+7.636253283814|
|96|13|31/23|+6.685097714725|+6.564219540547|-1.404153857881|+11.845163397391|
|48|49|14/7|-59.264796414489|-0.014195765056|-8.502664093661|-67.781656273206|

Обе ориентации вычислены: это 20 конфигураций, но 10 различных числовых
сценариев, поскольку вещественные энергии сопряжённых ориентаций совпадают.
Суммы округлённых чисел могут отличаться в последнем знаке; проверки используют
полные интервалы.

`0*` — структурный ноль, а не обнуление малого интервала. В каждой из этих
конфигураций все 80 перекрёстных пар имеют различные характеры на группе шести
единиц. Полные единичные орбиты сокращаются точно: rho радиален, шестистепенная
свобода и маски сохраняются при умножении на единицу. Сохранённые сырые пары
равны нулю как целые числа. Для остальных интервалов сам факт включения нуля
не объявляется тождеством. При P0 группы RA/AA пусты.

## Что именно меняют маски

Дополнительно для каждой группы вычислена разность относительно A(P) копий
физической суммы без масок **при тех же P и H**. Это не разность между новой
конфигурацией и P0: при изменении P меняется и исходное среднее.

На RR эта поправка тождественно нулевая, поскольку A_P(nm)=A(P), хотя сама
C_RR почти всегда ненулевая. При U64,P13:

| Изменение от масок | Вклад в полную поправку |
|:---|---:|
| RR | 0, тождественно |
| RA | -4.631264893832 |
| AA | +2.676406300057 |
| Сумма | -1.954858593774 |

Маски здесь уменьшают положительный перекрёстный вклад, но не устраняют его.
Затронутая группа одновременно получает положительную поправку, хотя её
окончательный вклад C_AA остаётся отрицательным. Это разные величины.

При U48,P49 полная масочная поправка +4.493758340844 раскладывается на
+0.000887235296 в RA и +4.492871105548 в AA. Прежний смешанный член
+0.150013200881 сохранён внутри полного расчёта. Через парную формулу также
воспроизведён прежний h(p*pbar). Все 20 полных масочных поправок совпали с
сохранёнными ранее значениями; никакие взаимодействия не отброшены.

## Периоды: какой режим охвачен

Для каждой пары сохранены факторизации и нормы:

```
g = gcd(n,m)                         общий нулевой фактор
D = (n/g)(m/g)                       примитивный проводник фазы
Q = lcm(n,m) = g D                   полный период с нулевыми масками
```

Это утверждение для наших хороших бесквадратных колонок с mu!=0. Локальные
показатели фазы +eps и -eps также сохранены. Общие простые исчезают из фазы,
но не из условия зануления. Для произвольных степеней эта формула проводника
не утверждается.

Фактические отношения H/Q по всем ненулевым колонкам и всем их различным
парам, включая пары с нулевым вкладом:

| Часть панели | Минимум H/Q | Максимум H/Q |
|:---|---:|---:|
| Исходное P0, единичный усилитель | 0.002591737 | 0.2729299 |
| Независимые P=7,13,49 | 168.3682 | 1.042986e9 |

Это подтверждает различие режимов на сохранённой панели. Разбиение не создало
конфигураций, одновременно сочетающих неединичный усилитель и трудный
производственный режим длинных периодов. Общая асимптотическая граница для
T_H из приложения здесь заново не доказывалась и не использовалась для замены
сохранённых сырых сумм.

## Точное равенство и проверка

Пусть V_ij=sum_u rho*2Re(chi_i conjugate chi_j), а R_ij — сохранённый
целочисленный `pair_2re[i][j]`. Для i<j вычисляли

```
C_ij = mu_i mu_j W_i W_j/L * [A_P(n_i n_j) V_ij - A(P) S_rho R_ij/N_H].
```

A_P считали по всем хорошим усилителям, включая степени. Для каждой пары
целочисленно проверено включение–исключение; при P49 сохранены все 17
усилителей. Для RR точно проверено A_P=A. Суммы RR, RA, AA возвращают полную C.

Сохранены **13 434 неупорядоченные пары по всем 20 конфигурациям**. Это число
включает повторные пары разных конфигураций и ориентаций, не число независимых
арифметических наблюдений. Артефакт gzip содержит все пары без усечения.

Проверки:

- Все 20 парных сумм и их три группы совпали с прежней полной C; отдельно
  совпали физическая и вычитаемая сырая внедиагональные части.
- Наибольшая ширина остатка обратной сборки — **4.23834e-52** (округлено вверх).
- Независимый вычислитель собрал энергии групп напрямую через квадраты сумм
  колонок и их перекрёстный член, затем вычел сохранённые сырые части.
  **460 интервальных сравнений пройдены**, максимальная ширина их остатков
  меньше **9.884e-52**, при допуске 1e-30 и 192 битах Arb.
- 4 целевых автоматических теста пройдены; независимый обзор без оставшихся
  существенных замечаний. Отдельно проверены 20 масочных возвратов и четыре
  структурных перекрёстных нуля.
- Исходные код и данные закреплены по Git blobs и SHA-256; старые файлы не
  изменялись. Сырые парные матрицы переиспользованы, сырые шары не пересчитывались.

Совпадение означает перекрытие сертифицированных интервалов с узким остатком,
содержащим ноль, а не обязательное вложение нового интервала внутрь старого.
Суммы модулей пар сохранены отдельно как диагностика; они не подставляются
вместо исходного подписанного выражения. Lean-проверка не выполнялась.

## Вывод для следующего математического шага

§6 дал различающий результат: одного закона для затронутых колонок
недостаточно, а перекрёстный член нельзя считать малым автоматически.
На U64/P13 он существенно больше каждой из двух остальных подписанных частей.
При U48/P49, наоборот, основная отрицательная часть находится в RR.
Универсальное доминирование одной группы эта панель не устанавливает.

Дальнейшая оценка должна контролировать полный подписанный баланс в исходном
режиме, сохраняя RR и RA вместе с AA. Отдельная малость каждой группы не
объявляется необходимой. Лемма (3) из ответа Прошки остаётся недоказанной;
положительного чистого степенного выигрыша не получено.

Всё готово для передачи Прошке. Автоматическая отправка не выполнялась.
Воспроизведение: README.md. Данные: decomposition.json.gz и summary.json.
Независимая проверка: verification.json; дополнительные сверки:
mask_return_checks.json; обзор: REVIEW.md.


## File: experiments/cf22_pysr/correlation/README.md

# Full signed pair decomposition of the saved nonunit panel

Scope: owner-requested §6 of `OWNER_REQUEST.txt`. Reuse all 20 saved
configurations in `../nonunit/main.json` and `../nonunit/heldout.json` at
`f1993ec6a7933418c38c305a13a3221037b9447a`. No new raw disk summation or fit.
Only the small physical sums are recomputed. Old files remain unchanged.

## Definition and exact return

All source columns are good squarefree ideals with nonzero Möbius coefficient
in the same strict W support. Column order is reconstructed from the pinned
source enumerator and checked against the saved raw matrix dimensions.
Let c_i=mu(n_i)W(q_i/L)/sqrt(L), with the real fixed profile used in the pilot.
For each **unordered** pair i<j compute

```
V_ij = sum_(sixthfree u) rho(q_u/U) * 2 Re(chi_i(u) conjugate(chi_j(u)))
R_ij = saved pair_2re[i][j]
a_ij = #{good a: q_a<=P and (a,n_i*n_j)=1}
D_ij = c_i*c_j * [a_ij V_ij - A(P)*S_rho*R_ij/N_H].
```

The factor 2 accounts for the two ordered off-diagonal terms. The diagonal
has already been removed and is not added back. The sum of D_ij is the original
C: expanding each masked energy gives coefficient a_ij on its physical pair,
and the original raw mean has coefficient A(P). Every amplifier, including
prime powers, is counted separately. Inclusion-exclusion independently gives
`a_ij = sum_(d|rad(n_i*n_j)) mu(d) A(P/q_d)`.

A column is P-rough exactly when it has no prime ideal divisor of norm <=P.
The partition consists of rough/rough (RR), exactly one rough (RA, both orders
already included), and neither rough (AA). These disjoint classes exhaust all
unordered pairs. If a column is rough, all allowed amplifiers are coprime to it.
Hence a_ij=A on RR pairs. Their mask-induced physical correction
`c_i*c_j*(a_ij-A)*V_ij` is identically zero, but D_ij need not vanish.
The correction is measured at the same P,H; it is not a difference against P0,
which changes the raw radius and mean.

Each group's physical term, subtracted raw term, signed D and mask correction
are retained. Absolute pair sums are optional diagnostics, not replacements for
C and not claims about its asymptotic upper bound. Verification requires interval
overlap with the saved C and with its physical/raw off-diagonal components;
residual intervals must contain zero and meet the stated precision tolerance.
This is numerical agreement of certified enclosures, not an assertion that the
new enclosure must be a subset of an older narrower enclosure.

## Period, primitive conductor and shared zero factor

For these squarefree columns put g=gcd(n_i,n_j). The full zero-extended period
is lcm(n_i,n_j), norm Q=q_i*q_j/q_g. The primitive quotient character has local
exponent +1 on n_i/g, -1 on n_j/g (reversed for the other orientation), and zero
on g. Each remaining local character is nontrivial modulo a good prime ideal,
so its primitive conductor is (n_i/g)*(n_j/g), norm q_i*q_j/q_g^2.
The canceled common primes still impose the zero factor g. Thus
`Q = norm(primitive conductor) * norm(shared zero factor)`.

This conductor description is restricted to the squarefree source used here;
it is not a formula for arbitrary higher exponents. Distinct columns imply a
nontrivial quotient conductor. The primitive character must not replace the
full zero-extended pair in a sum. Each saved pair retains the three ideal
factorizations, not just their norms.

H/Q is recorded for each pair using the actual H of its configuration. A
large H/Q diagnostic and a production configuration with small H/Q are distinct
regimes; decomposing this panel does not create a sample with both nonunit
amplification and production-scale long periods. CF22 remains unproved.

## Reproduce and inspect

Use the existing Python 3.12 / python-flint 0.9.0 environment. From repo root:

```sh
PY=/tmp/cf22-pysr-venv/bin/python
$PY -m unittest discover -s experiments/cf22_pysr/correlation -p 'test_*.py' -v
$PY experiments/cf22_pysr/correlation/decompose.py --output /tmp/cf22-pair-replay.json.gz
$PY experiments/cf22_pysr/correlation/verify_groups.py --decomposition /tmp/cf22-pair-replay.json.gz --output /tmp/cf22-pair-verification-replay.json
```

Output files must not already exist. The historical source/data pin is checked
against Git blobs; execution HEAD may be later. Input and implementation hashes
are checked for changes during calculation. No Julia, PySR, clang or native raw
counter execution is needed. `decomposition.json.gz` is deterministic compressed
JSON containing every pair, not a sample. `summary.json` provides compact group
intervals without per-pair expansion; `RESULT.md` provides the Russian report.

`verify_groups.py` independently computes masked group energies: |R|² and |A|²
minus their respective diagonals, and |R+A|²-|R|²-|A|² for the cross term.
It does not reuse the producer's physical pair assembly. It then subtracts each
group's saved raw contribution. `verification.json` retains every comparison.
`check_mask_return.py` compares the full correction against the old mask result
and checks the exact unit-phase distinction behind the U48/P7,P13 cross zeros.
`summarize.py` creates the compact summary. Derived-output scripts refuse to
replace existing files; preserve the shipped outputs when replaying.

The owner attachment is preserved verbatim, including its original Markdown
spacing and links. The linked sandbox-only full analysis was not available in
this local task. This implementation follows §6 of the supplied text and the
pinned source; it does not claim an independent audit of that full attachment.


## File: experiments/cf22_pysr/correlation/REVIEW.md

# Independent review record — 2026-10-20

Integrator saved the returned read-only reviews; reviewers did not edit source.

A Luna mathematical audit verified the off-diagonal unordered-pair formula,
2Re normalization, exhaustive RR/RA/AA partition, amplifier powers and exact
inclusion-exclusion. For squarefree good source columns it verified primitive
conductor D, full period Q and shared zero factor g with Q=gD. The general
asymptotic period-cell bound was not independently proved in this review.

Astra reviewed producer and independent direct-energy verifier. Before the
full panel, three integration issues were fixed: the old pilot plan validator
was incorrectly used for the nonunit plan, group Arb values needed interval
serialization, and a correction field name differed across scripts. The first
full verifier attempt also rejected a request-path mismatch before numerical
work; the old plan now checks its old nonunit request, while the new request is
hashed separately. The decomposition data were not modified to address these.

Final review: PASS, no remaining material findings. All 20 configurations pass
independent verification; artifact/source hashes match, and all 13,434 unordered
configuration-pairs are retained. Reassembly residual width is at most
4.23833067915453e-52. U64/P13 and U48/P49 signed triples reconstruct C.

U48/P7 and U48/P13 each have 80 cross pairs with distinct unit characters and
exact raw zero entries. Full unit orbits support structural cancellation;
other near-zero values need interval-qualified wording. The artifacts preserve
the finite scope and make no asymptotic CF22 claim. Review did not rerun the
full computation or any raw disk sums.


## File: experiments/cf22_pysr/correlation/mask_return_checks.json

{
  "status": "PASS",
  "input_sha256": {
    "correlation/decomposition.json.gz": "74e888523228566fbb5140ed24dd8b9abbd33a07af9eba72519802dd18e9f38d",
    "nonunit/main.json": "5986f2f5fbd8cc87116befb1ac3d08222804ec3f79c1ceb4e0408182c943bdcb",
    "nonunit/heldout.json": "87b6ed649621fb428e71276fcc62701501140afc2a9bff320337ee54596c6cfe",
    "evaluate.py": "06c48c3075335205aeb80cdc7a142d1b0868e82a7f2a1006391764222112faeb"
  },
  "checker_sha256": "8b623f32c21c050b7f767336985265ec9684b2941afc5df72984f3d9e2c5f9c4",
  "old_mask_correction_matches": [
    "U48_Pproduction_o1",
    "U48_Pproduction_o-1",
    "U48_P7_o1",
    "U48_P7_o-1",
    "U48_P13_o1",
    "U48_P13_o-1",
    "U64_Pproduction_o1",
    "U64_Pproduction_o-1",
    "U64_P7_o1",
    "U64_P7_o-1",
    "U64_P13_o1",
    "U64_P13_o-1",
    "U96_Pproduction_o1",
    "U96_Pproduction_o-1",
    "U96_P7_o1",
    "U96_P7_o-1",
    "U96_P13_o1",
    "U96_P13_o-1",
    "U48_P49_o1",
    "U48_P49_o-1"
  ],
  "unit_cross_zero_checks": [
    {
      "id": "U48_P7_o1",
      "cross_pairs": 80,
      "all_unit_quotient_characters_nontrivial": true,
      "all_saved_raw_pairs_exact_zero": true,
      "structural_zero": "Full six-unit orbits with radial weights, sixthfree support and unit-invariant masks."
    },
    {
      "id": "U48_P7_o-1",
      "cross_pairs": 80,
      "all_unit_quotient_characters_nontrivial": true,
      "all_saved_raw_pairs_exact_zero": true,
      "structural_zero": "Full six-unit orbits with radial weights, sixthfree support and unit-invariant masks."
    },
    {
      "id": "U48_P13_o1",
      "cross_pairs": 80,
      "all_unit_quotient_characters_nontrivial": true,
      "all_saved_raw_pairs_exact_zero": true,
      "structural_zero": "Full six-unit orbits with radial weights, sixthfree support and unit-invariant masks."
    },
    {
      "id": "U48_P13_o-1",
      "cross_pairs": 80,
      "all_unit_quotient_characters_nontrivial": true,
      "all_saved_raw_pairs_exact_zero": true,
      "structural_zero": "Full six-unit orbits with radial weights, sixthfree support and unit-invariant masks."
    }
  ]
}


## File: experiments/cf22_pysr/correlation/TEST_RESULTS.txt

Command run by root:
/tmp/cf22-pysr-venv/bin/python -m unittest discover -s experiments/cf22_pysr/correlation -p 'test_*.py' -v

PASS: test_coefficient_two_matches_direct_physical_energy_expansion
PASS: test_pair_partition_is_exhaustive_and_disjoint
PASS: test_saved_pair_sum_matches_existing_full_c_and_h49
PASS: test_shared_prime_is_full_period_zero_mask_not_quotient_conductor
Ran 4 tests in 0.170s; OK.

Full output verification is recorded separately in verification.json:
20 configurations, 460 interval comparisons, PASS.
Additional old mask-return and unit-orbit checks: mask_return_checks.json.
