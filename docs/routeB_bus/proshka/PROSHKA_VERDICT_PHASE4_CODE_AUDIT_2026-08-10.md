# STATUS: OPEN — FINITE PHASE 4 RESULTS MOSTLY VALID; CONSTANT-FLOOR RESIDUAL CERTIFICATE KILLED; RESOLVENT-WEIGHTED SCHUR SELECTED

```yaml
PRIMARY: KILL_CONSTANT_FLOOR_RESIDUAL_GRAM_KEEP_EXACT_SCHUR
PRIMARY_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  PIN_SHORT: b076f97b
  PIN_FULL: b076f97bc63a1558cf65eed7d24c7fa45c68073f
  REQUEST_PATH: docs/routeB_bus/PROSHKA_REQUEST_PHASE4_CODE_AUDIT_2026-08-10.md
  REQUEST_BLOB_SHA: 3456f0ebac86d259a229455d846f09eeb670313b
  PHASE1_SOURCE_BLOB_SHA: a906f34afaa1bf4e002d5aebd409148f7385d621
  COMMUTATOR_LEAN_BLOB_SHA: 6d1379ff343e2b22602c07175fbd39a2b976e258
  JUDGE_RERAN_PYTHON_FLINT_NUMERICS: false
  REASON: python_flint_unavailable_in_judge_runtime
  INTERNAL_ARITHMETIC_CROSSCHECK: passed

ARSENAL:
  MANDATE_ACCEPTED: true
  DECK_FETCHED: true
  DECK_CONTENT_SHA256_RECOMPUTED_BY_JUDGE: false
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C07_PROBABILITY_WEIGHTED_ESTIMATE
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

CODE_AUDIT:
  glower_tail_floor_probe:
    status: CORRECT_FINITE_COMPRESSION_ONLY
  glower_corrected_head:
    status: CORRECT_FINITE_SCHUR_ONLY
  glower_head_drift_ledger:
    status: CORRECT_FINITE_MAJORANT_WITH_S_SEMANTIC_MISLABEL
  glower_full_residual_prefix:
    status: CORRECT_FINITE_PREFIX_WITH_DISPLAY_INDEX_OFF_BY_ONE
  glower_gram_form_check:
    status: CORRECT_CONSTANT_FLOOR_SUFFICIENT_TEST_NONPORTABLE
  glower_low_spectrum_preflight:
    status: BUG_MAX_ENTRY_REPORTED_AS_OPERATOR_NORM
  glower_relative_form_check:
    status: MIDPOINT_DIAGNOSTIC_ONLY_NONPORTABLE
  glower_beta_cocycle_check:
    status: REDUNDANT_AND_OVERSTATED
  yoshida_analytic_N:
    status: HEURISTIC_OCR_RECONSTRUCTION_NOT_CERTIFICATE

ARTIFACT_AUDIT:
  glower_ledger_960_log:
    status: MISSING_AT_PIN
  glower_ledger_960_profile_csv:
    status: PRESENT
    blob_sha: bc942c1a05780812d869de3a204508682fc3592c
  residual_prefix_960_log:
    status: PRESENT
    blob_sha: 5ff39fbfc7e943098458f708560dff91b153b9b3
  low_spectrum_preflight_log:
    status: PRESENT
    blob_sha: 0ab80092389bd2b90d9952c7a4abc7a7ea23d143
  relative_form_log:
    status: PRESENT
    blob_sha: b05db3da9e43ad7838a777f0405718c7a6b58cd9
  gram_form_raw_log:
    status: MISSING_AT_PIN

DISCREPANCIES:
  D1:
    code: LDLT_AND_GENERALIZED_EIGENVALUE_AGREE
  D2:
    code: PROJECTED_OPERATOR_NORM_NOT_COMPUTED
  D3:
    code: P_M2_REFUTED_FOR_D_INVERSE_GRAM_ONLY
  D4:
    code: OUTER_RESIDUAL_REINFORCEMENT_CONFIRMED
  D5:
    code: SSTAR_IS_MOVING_HEAD_PARAMETER_NOT_FIXED_R_DECAY_CUTOFF
  D6:
    code: DEFER_B0_UNTIL_MOMENT_CONSTRAINED_CORRECTOR

FINITE_RESULTS:
  tail_floor_R70:
    status: FINITE_EVIDENCE
    infinite_tail_theorem: false
  corrected_head_N120_240_480_960:
    status: FINITE_INTERVAL_PASS_RELAY
  table_majorant_S480_N960:
    status: FINITE_INTERVAL_PASS_RELAY
  source_beta_offdiag_identity:
    status: LEAN_PROVED
  exact_finite_Schur_at_N960:
    status: ALIVE
  infinite_constant_floor:
    status: OPEN

KILL:
  code: CONSTANT_FLOOR_RESIDUAL_GRAM_CERTIFICATE_KILLED
  object:
    B_480_minus_d_inverse_times_residual_prefix_Gram
  direction: SUFFICIENT_LOWER_CERTIFICATE_FAILED
  scope: FINITE_CELL
  verifier: CONDITIONAL_ON_RELAYED_ARB_RUN
  does_not_kill:
    - exact_resolvent_weighted_Feshbach
    - odd_floor_target_c0
    - GLOWER_route

SELECTED_REPRESENTATION:
  name: NESTED_SCHUR_RESOLVENT_WEIGHTING
  exact_outer_correction:
    formula: R_out_star_times_C_out_inverse_times_R_out
  forbidden_surrogate:
    formula: d_inverse_times_R_out_star_times_R_out

NEXT_TARGET:
  code: GLOWER_NESTED_SCHUR_RESOLVENT_LOSS_AUDIT_480_960
  mode: READ_ONLY
  B0_in_this_batch: false
  N1920_in_this_batch: false
  Birman_Schwinger_activation: false

REGISTERED_PREDICTION:
  exact_relative_loss:
    expected_interval: [0.12, 0.30]
  constant_floor_relative_loss:
    observed_midpoint: 1.049387747
  prediction_fixed_before_test: true

ALTERNATIVE_REPRESENTATIONS_IF_NEEDED:
  - name: MOMENT_CONSTRAINED_CORRECTOR
    kill_power: HIGH
    cost: MEDIUM_HIGH
  - name: BIRMAN_SCHWINGER_INERTIA
    kill_power: HIGH
    cost: HIGH

PROGRESS_CLASS:
  - FALSIFICATION_PROGRESS
  - REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
G2_CCM: FROZEN
ROUTE_PROMOTION: false
RH_CLAIM: false
LEAN_EDITS: NONE
REPO_WRITE_AUTHORIZED_BY_THIS_VERDICT: false
```

## ROUTE MAP

### Термины

1. **Finite compression** — конечное сжатие бесконечного оператора на первые Fourier-моды.

2. **Schur complement** — дополнение Шура после точного исключения одного блока матрицы.

3. **Residual** — невязка внешних строк после применения конечного корректора \(Y\).

4. **Gram matrix** — матрица
\[
G=\sum_k r_k^{*}r_k.
\]

5. **Constant-floor penalty** — оценка внешней поправки матрицей
\[
d^{-1}G.
\]

6. **Resolvent-weighted penalty** — точная поправка
\[
R_{\mathrm{out}}^{*}C_{\mathrm{out}}^{-1}R_{\mathrm{out}}.
\]

7. **Generalized eigenvalue** — число \(\mu\), которое удовлетворяет
\[
Gv=\mu Bv.
\]

8. **LDLᵀ pivot** — диагональный элемент исключения в разложении \(LDL^{T}\).

9. **Operator norm** — максимальное растяжение вектора оператором.

10. **Moment** — конечная взвешенная сумма строк корректора.

11. **Source-beta identity** — точная формула разделённых разностей через \(\beta_n=n\tau(n,0)\).

### Задача

12. Определить, какие результаты Phase 4 являются фактами, и выбрать следующий доказательный объект.

### Измерения

13. **[relay][FINITE_CELL][ARB_INTERVAL]** Скрипт `glower_tail_floor_probe.py` сообщает порог строки \(70\) при \(\mu=1\).

14. **[доказано][FINITE_CELL][PAPER]** Скрипт проверяет только конечную матрицу `odd[70:,70:]`.

15. **[relay][FINITE_CELL][ARB_INTERVAL]** Скрипт `glower_corrected_head.py` сообщает PASS при \(N=120,240,480,960\).

16. **[доказано][FINITE_CELL][PAPER]** Скрипт строит точное конечное дополнение Шура для каждого выбранного \(N\).

17. **[relay][FINITE_CELL][ARB_INTERVAL]** Журнал сообщает
\[
\gamma=1.869492\cdot10^{-55}
\]
для \(S=480\) и \(N=960\).

18. **[relay][FINITE_CELL][ARB_INTERVAL]** Журнал сообщает
\[
\sum_{480<k\le960}\|r_k\|^2=7.583235\cdot10^{-2}.
\]

19. **[relay][FINITE_CELL][ARB_INTERVAL]** Журнал сообщает
\[
\sum_{480<k\le960}\|E_k\|^2=5.312379\cdot10^{-2}.
\]

20. **[доказано][FINITE_CELL][PAPER]** Их отношение равно
\[
1.42746.
\]

21. **[relay][FINITE_CELL][CONDITIONAL]** Скрипт Грама сообщает отрицательный \(LDL^T\)-пивот `−1.0699`.

22. **[relay][FINITE_CELL][CONDITIONAL]** Скрипт относительной формы сообщает
\[
\mu_{\max}=1.049387747.
\]

23. **[доказано][FINITE_CELL][PAPER]** Матрица \(B_{480}\) имеет обусловленность около
\[
2.28\cdot10^{55}.
\]

24. **[relay][FINITE_CELL][CONDITIONAL]** Скрипт низкого спектра сообщает
\[
\lambda_0(B_{480})=2.3059968\cdot10^{-55}.
\]

25. **[relay][FINITE_CELL][CONDITIONAL]** Скрипт низкого спектра сообщает
\[
\lambda_{69}(B_{480})=5.2492112.
\]

26. **[доказано][FINITE_CELL][LEAN]** Lean доказывает:
\[
\tau(k,n)=\frac{\beta_k-\beta_n}{k-n}
\qquad(k\ne n).
\]

27. **[relay][FINITE_CELL][CONDITIONAL]** Скрипт Yoshida сообщает
\[
N>1.5488372\cdot10^{34}.
\]

28. **[доказано][ABSTRACT][PAPER]** Значение пункта 27 не является сертифицированной константой Yoshida.

## Анализ

29. Скрипт `glower_tail_floor_probe.py` соответствует своему docstring.

30. Скрипт `glower_corrected_head.py` соответствует своему docstring.

31. Оба скрипта явно ограничивают вывод конечным срезом.

32. Эти два PASS не занимают бесконечный квантор.

33. Скрипт `glower_full_residual_prefix.py` считает заявленную конечную невязку.

34. Строка массива `k=480` соответствует физической моде \(481\).

35. Поэтому печать диапазона имеет off-by-one в обозначении моды.

36. Числовая сумма при этом использует правильные \(480\) внешних строк.

### Расхождение 1

37. Отрицательный \(LDL^T\)-пивот и \(\mu_{\max}=1.049387747\) означают один результат.

38. Для \(B\succ0\) выполняется:
\[
B-d^{-1}G\succ0
\iff
\lambda_{\max}(B^{-1/2}GB^{-1/2})<d.
\]

39. Здесь \(d=1-10^{-58}\).

40. Поэтому \(\mu_{\max}>d\) запрещает положительность проверяемой матрицы.

41. Пивот `−1.0699` не является собственным значением.

42. Обусловленность объясняет большой масштаб пивота после исключения.

43. Отрицательный интервальный пивот всё равно убивает данный certificate.

### Расхождение 2

44. Скрипт `glower_low_spectrum_preflight.py` не вычисляет \(\|PGP\|_{\mathrm{op}}\).

45. Скрипт вычисляет максимальный модуль элемента проецированной матрицы.

46. Эти величины совпадают только в размерности \(1\).

47. В размерности больше \(1\) таблица не является операторной оценкой.

48. Скрипт также не учитывает связь \(PG(I-P)\).

49. Поэтому отношения `0.04…0.20` не противоречат \(\mu_{\max}=1.0494\).

50. Исправленный объект имеет вид:
\[
\lambda_{\max}
\left(
\Lambda_d^{-1/2}U_d^TGU_d\Lambda_d^{-1/2}
\right).
\]

### Расхождение 3

51. Прогноз о жизнеспособности матричного Грама опровергнут для матрицы \(d^{-1}G\).

52. Этот результат убивает код:
```text
CONSTANT_FLOOR_RESIDUAL_GRAM_CERTIFICATE
```

53. Этот результат не убивает точное дополнение Шура.

54. Точная внешняя поправка равна:
\[
H_{\mathrm{exact}}
=
R_{\mathrm{out}}^{*}
C_{\mathrm{out}}^{-1}
R_{\mathrm{out}}.
\]

55. Из \(C_{\mathrm{out}}\succeq dI\) следует:
\[
H_{\mathrm{exact}}\preceq d^{-1}G.
\]

56. Обратное неравенство отсутствует.

57. Провал большей матрицы не доказывает провал меньшей матрицы. **[C10]**

58. Конечный PASS при \(N=960\) показывает, что точная конечная поправка остаётся допустимой.

### Расхождение 4

59. Неравенство
\[
\sum\|r_k\|^2>\sum\|E_k\|^2
\]
не является ошибкой кода.

60. Корректор \(Y_{480}\) обнуляет строки только внутри мод \(71,\ldots,480\).

61. Внешние строки \(481,\ldots,960\) не входят в уравнение для \(Y_{480}\).

62. На внешних строках два слагаемых могут усиливать друг друга.

63. Измерение опровергает утверждение «\(Y_{480}\) гасит полный хвост».

64. Измерение не опровергает точное resolvent-weighted дополнение Шура.

### Расхождение 5

65. В ledger параметр \(S\) изменяет размер головы.

66. При \(S>70\) код заново строит \(A,D,E\) с головой размера \(S\).

67. Печать «голова \(R=70\) не меняется» не соответствует коду.

68. Поэтому \(S^*\) не является cutoff одного фиксированного корректора.

69. \(S^*\) является параметром нового разбиения матрицы.

70. Рост \(S^*\) и рост \(\gamma\) не противоречат друг другу.

71. Большая голова сохраняет больше точной структуры.

72. Меньший хвост упрощает диагональную миноранту.

73. Результат остаётся строгим только для указанного конечного диапазона.

74. Результат не даёт uniform cutoff для \(N\to\infty\).

### Расхождение 6

75. Число \(B_0\) не является следующим решающим измерением.

76. Конечный префикс уже убивает scalar penalty и constant-floor Gram penalty.

77. \(B_0\) нужен для другого корректора с принудительным занулением моментов.

78. Такой корректор ещё не выбран.

79. Не вычисляйте \(B_0\) в следующем batch.

80. При последующем расчёте используйте exact source normalization \(\beta_0=0\).

81. Не используйте реконструкцию скрипта с произвольным условием \(\beta_1=0\).

### Дополнительные ошибки аудита

82. Три диагностических скрипта используют абсолютный путь `/mnt/hdd01/...`.

83. Эти скрипты не фиксируют SHA исходного builder-файла.

84. Поэтому их числовые выводы пока имеют статус **[relay]**.

85. Файл `glower_ledger_960.log` отсутствует на коммите `b076f97b`.

86. Число \(\gamma\) дублируется в журнале, но сырой лог не source-locked.

87. Raw log для `glower_gram_form_check.py` также отсутствует.

88. Скрипт cocycle проверяет midpoint-значения, а не interval inclusion нуля.

89. Exact Lean theorem уже делает этот численный тест ненужным.

90. Слово «Loewner» в выводе cocycle-скрипта неверно.

91. Divided-difference identity не доказывает положительность Loewner matrix.

92. Скрипт Yoshida использует OCR-восстановленные формулы.

93. Скрипт заменяет максимум \(C_0\) значением в одной точке \(t_0\).

94. Скрипт не доказывает условие для всех \(|t|\ge t_0\).

95. Поэтому число \(1.5488372\cdot10^{34}\) является scale diagnostic.

96. Это число нельзя использовать как theorem cutoff.

## STRONGEST ATTACK

97. Самое сильное возражение утверждает, что full residual имеет масштаб \(10^{-2}\).

98. Возражение сравнивает residual norm с head floor масштаба \(10^{-55}\).

99. Такое сравнение использует глобальный inverse bound \(C^{-1}\preceq d^{-1}I\).

100. Глобальный bound уничтожает спектральную жёсткость внешнего хвоста. **[C07]**

101. Требуемый объект содержит \(C_{\mathrm{out}}^{-1}\), а не единичную матрицу.

102. Поэтому текущее поражение относится к representation, а не к исходному floor target.

103. Второе возражение касается точности midpoint generalized eigensolver.

104. Это возражение не меняет interval kill матрицы \(B-d^{-1}G\).

105. Midpoint-вычисление нужно только для локализации опасного направления.

## FINAL PROPOSAL

### Действие

106. Заморозьте finite PASS для `B_120`, `B_240`, `B_480` и `B_960`.

107. Удалите из active route constant-floor residual certificate.

108. Не запускайте \(N=1920\).

109. Не вычисляйте \(B_0\) в следующем batch.

110. Не активируйте Birman–Schwinger сейчас.

111. Выполните один nested-Schur audit на уже построенной матрице \(N=960\).

112. Сравните точную внешнюю поправку с грубой матрицей \(d^{-1}G\).

113. После audit выберите theorem:
```text
OddTailGradedResolventBound13
```

114. Теорема должна сохранять divided-difference cancellation до применения нормы.

115. Теорема должна ограничивать inverse-weighted Gram, а не raw residual norm.

### CODEX DIRECTIVE

```text
TARGET:
  GLOWER_NESTED_SCHUR_RESOLVENT_LOSS_AUDIT_480_960

MODE:
  READ_ONLY_NUMERICAL_PREFLIGHT
  NO_REPO_WRITE
  NO_LEAN_EDIT

PIN:
  b076f97bc63a1558cf65eed7d24c7fa45c68073f

FROZEN:
  m: 13
  sector: ODD
  c0: 1e-58
  R: 70
  S: 480
  N: 960

SOURCE_GATES:
  - use repository-relative paths only
  - record full HEAD
  - record SHA256 of every imported script and source payload
  - stop on any mismatch
  - write physical mode labels explicitly

TASK:
  1. Build the source odd matrix once at Arb precision 200 and 400.
  2. Build B_480 from modes 1..70 and internal modes 71..480.
  3. Build B_960 directly from modes 1..70 and tail modes 71..960.
  4. Partition the transformed outer block after eliminating modes 71..480.
  5. Construct:
       C_out = C - F*D_mid^(-1)*F^T
       R_out = E_out - F*D_mid^(-1)*E_mid
  6. Solve:
       C_out*X = R_out
  7. Construct:
       H_exact = R_out^T*X
  8. Verify the nested identity:
       B_480 - H_exact = B_960
     by interval overlap and direct interval LDLT.
  9. Construct the crude matrix:
       H_floor = d^(-1)*R_out^T*R_out
 10. Compare H_exact and H_floor in Loewner order where intervals permit.
 11. Compute midpoint diagnostics at 200 and 400 digits:
       rho_exact =
         lambda_max(B_480^(-1/2)*H_exact*B_480^(-1/2))
       rho_floor =
         lambda_max(B_480^(-1/2)*H_floor*B_480^(-1/2))
 12. Compute the correct projected generalized norms for dimensions 1..12.
 13. Compute the normalized cross-block coupling to the complement.
 14. Report the generalized eigenvector coordinates in the B_480 eigenbasis.

REGISTERED_PREDICTION:
  rho_exact in [0.12, 0.30]
  rho_floor equals the existing value near 1.049387747
  nested identity passes

SUCCESS:
  CONSTANT_FLOOR_SURROGATE_KILLED_RESOLVENT_ROUTE_ALIVE

STOP:
  SOURCE_HASH_MISMATCH
  NESTED_SCHUR_IDENTITY_FAIL
  RESOLVENT_MARGIN_TOO_SMALL
  PRECISION_NOT_STABLE

FORBIDDEN:
  hardcoded absolute repository path
  N=1920
  B0 computation
  fitted decay exponent
  minimum LDL pivot interpreted as eigenvalue
  max matrix entry reported as operator norm
  Birman-Schwinger activation
  route promotion
  RH claim

REQUIRED_OUTPUT:
  one JSON file
  one raw log
  one read-only markdown report
  all source hashes
  full precision ledger
```

### META CLOSEOUT

116. Неизвестность уменьшилась до resolvent-weighted внешней поправки.

117. Убит constant-floor residual certificate.

118. Убит прогноз `P-M2` для \(d^{-1}G\).

119. Убит смысл таблицы `‖PGP‖` как operator norm.

120. Убита трактовка \(S^*\) как fixed-\(R\) decay boundary.

121. Нельзя повторять raw residual versus head-floor comparison.

122. Нельзя повторять cocycle numerics вместо exact Lean theorem.

123. Текущий smallest named gap:
\[
\boxed{\texttt{OddTailGradedResolventBound13}.}
\]

124. Следующий дешёвый decisive test является nested-Schur audit.

125. Зарегистрированный прогноз matrix-Gram survival получил статус `REFUTED_AS_STATED`.

126. Repaired prediction утверждает survival exact resolvent-weighted correction.

```yaml
iteration:
  target: infinite_odd_sector_floor
  status: PROGRESS
  failed_strategy: constant_floor_residual_Gram
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: OddTailGradedResolventBound13
  invariant_learned: preserve the transformed outer resolvent before taking norms
  forbidden_future_move: replace C_out_inverse by d_inverse_identity and interpret failure as target kill
  next_decisive_test: nested_Schur_resolvent_loss_480_960
  progress_class: FALSIFICATION_AND_REPRESENTATION_PROGRESS
  route_score: 5
```

### Ограничение

127. Этот verdict не доказывает бесконечную коэрцитивность хвоста.

128. Этот verdict не доказывает \(Q_{13}^{\mathrm{odd}}\succeq10^{-58}I\).

129. Этот verdict не подтверждает число \(R=70\) как theorem cutoff.

130. Этот verdict не сертифицирует \(\mu_{\max}=1.049387747\).

131. Этот verdict не использует отсутствующий raw ledger log как источник.

132. Этот verdict сохраняет `CHALLENGER_NOT_RH`.

133. Этот verdict сохраняет `BUS_010: VOID`.

134. Этот verdict сохраняет `GOAL_055: HOLD`.

135. Этот verdict не разрешает route promotion.

136. Этот verdict не содержит утверждение RH.
