# STATUS: OPEN — SOURCE-BETA REPRESENTATION FOUND; SCALAR RESIDUAL HOOK REQUIRES A MOMENT TEST

```yaml
PRIMARY: RUN_GLOWER_FULL_RESIDUAL_BETA_MOMENT_PREFLIGHT_N480
PRIMARY_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  CCM_SOURCE_SCRIPT_BLOB: a906f34afaa1bf4e002d5aebd409148f7385d621
  CCM_COMMUTATOR_LEAN_BLOB: 6d1379ff343e2b22602c07175fbd39a2b976e258
  PRIOR_GLOWER_VERDICT_BLOB: faf4fec05d271802fd9cbb26cfb932ba15362668

ARSENAL:
  MANDATE_ACCEPTED: true
  CARDS_APPLIED:
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

MEASUREMENT_INPUT:
  raw_row_profile:
    relation: norm_E_k_squared_times_k_squared_approximately_constant
    observed_constant_range: [45.5, 53.0]
    provenance: OWNER_RELAY_NOT_PINNED
  raw_scalar_tail_estimate:
    value: approximately_0_10
    role: DIAGNOSTIC_ONLY
  reported_head_floor_gamma:
    value: 1.869e-55
    provenance: OWNER_RELAY_NOT_PINNED
    role: THRESHOLD_DIAGNOSTIC_ONLY

EXACT_REPRESENTATION:
  beta_n: n_times_tau_n_0
  odd_entry:
    formula: 2_times_n_beta_k_minus_k_beta_n_over_k_squared_minus_n_squared
  residual:
    formula: sum_n_1_to_480_Kodd_k_n_times_Z_n
  leading_moment:
    name: B0
    formula: sum_n_1_to_480_beta_n_times_Z_n
  asymptotic:
    formula: k_times_r_k_tends_to_minus_2_B0

PRIMARY_DECISION:
  first_test: COMPUTE_INTERVAL_B0_A0_B1_A1
  scalar_penalty:
    status: UNRATIFIED
    expected_fate: LIKELY_TOO_LOOSE
  matrix_gram_penalty:
    status: PRE_REGISTERED_REPAIR
    object: d_inverse_times_sum_rk_star_rk
  birman_schwinger:
    status: HOLD

PASS:
  code: FULL_RESIDUAL_FESHBACH_PASS_AT_N480
  condition:
    - source_beta_identity_verified
    - full_tail_gram_upper_enclosure_constructed
    - lower_envelope_of_B480_minus_tail_gram_is_nonnegative

KILL:
  code: N480_FINITE_CORRECTOR_KILLED
  condition:
    - rigorous_finite_prefix_gram_already_exceeds_B480_on_one_Ritz_vector
  note: failure_of_scalar_pI_does_not_kill_matrix_gram_or_GLOWER

STOP:
  - SOURCE_BETA_IDENTITY_MISMATCH
  - CORRECTOR_SOURCE_HASH_MISMATCH
  - BETA_SCALAR_ENVELOPE_MISSING
  - MOMENT_INTERVAL_TOO_WIDE

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
REPO_WRITE_AUTHORIZED: false
```

## Термины

1. **[доказано][ABSTRACT][LEAN] Beta scalar** — скаляр \(\beta_n=n\,\tau(n,0)\), который определяет все внедиагональные элементы.

2. **[доказано][ABSTRACT][PAPER] Residual** — невязка \(r_k\), оставшаяся после применения конечного корректора \(Y\).

3. **[доказано][ABSTRACT][PAPER] Moment** — конечная взвешенная сумма строк корректора, которая задаёт коэффициент асимптотического разложения.

4. **[доказано][ABSTRACT][PAPER] Gram matrix** — матрица Грама \(\sum r_k^*r_k\), сохраняющая направления невязки.

5. **[доказано][ABSTRACT][PAPER] Scalar penalty** — скалярный штраф \(pI\), который заменяет матрицу Грама её следовой оценкой.

6. **[доказано][ABSTRACT][PAPER] Loewner order** — порядок Лёвнера для сравнения эрмитовых матриц по положительной полуопределённости.

## Задача

7. **[доказано][COFINAL_FAMILY][CONDITIONAL]** Построить строгую огибающую полной невязки для всех \(k>480\) и проверить нижнюю границу corrected head.

## Измерения

8. **[измерено][FINITE_CELL][CONDITIONAL]** Владелец сообщает:
\[
k^2\|E_k\|^2\in[45.5,53.0]
\]
для \(k=200,400,600,959\).

9. **[измерено][COFINAL_FAMILY][CONDITIONAL]** Сырая оценка даёт:
\[
\sum_{k>480}\|E_k\|^2\approx \frac{50}{480}\approx0.104.
\]

10. **[измерено][FINITE_CELL][CONDITIONAL]** Владелец сообщает certified-head scale:
\[
\gamma=1.869\cdot10^{-55}.
\]

11. **[доказано][FINITE_CELL][LEAN]** Источник строит odd entry как:
\[
K^-_{kn}=\tau(k,n)-\tau(k,-n).
\]

12. **[доказано][ABSTRACT][LEAN]** Lean доказывает для \(k\ne n\):
\[
\tau(k,n)=\frac{\beta_k-\beta_n}{k-n}.
\]

13. **[доказано][ABSTRACT][PAPER]** Точная reversal symmetry даёт:
\[
\beta_{-n}=-\beta_n.
\]

14. **[доказано][ABSTRACT][PAPER]** Поэтому:
\[
\boxed{
K^-_{kn}
=
\frac{2(n\beta_k-k\beta_n)}{k^2-n^2}.
}
\]

## Анализ

15. **[доказано][ABSTRACT][PAPER]** Старое утверждение: три компонента надо отдельно ограничить как \(O(1/k)\).

16. **[доказано][ABSTRACT][PAPER]** Новое утверждение: полную матрицу надо сначала свернуть через source-beta identity.

17. **[доказано][ABSTRACT][PAPER]** Причина замены: отдельные абсолютные оценки уничтожают межкомпонентное сокращение, которое должен использовать \(Y\). **[C10]**

18. **[доказано][FINITE_CELL][PAPER]** Определим строки corrected basis:
\[
Z_n=
\begin{cases}
e_n,&1\le n\le70,\\
Y_{n,:},&71\le n\le480.
\end{cases}
\]

19. **[доказано][COFINAL_FAMILY][PAPER]** Для каждого \(k>480\):
\[
r_k=\sum_{n=1}^{480}K^-_{kn}Z_n.
\]

20. **[доказано][COFINAL_FAMILY][PAPER]** Следовательно:
\[
r_k=
2\beta_k\sum_{n=1}^{480}\frac{nZ_n}{k^2-n^2}
-
2k\sum_{n=1}^{480}\frac{\beta_nZ_n}{k^2-n^2}.
\]

21. **[доказано][FINITE_CELL][PAPER]** Определим моменты:
\[
A_\ell=\sum_{n=1}^{480}n^{2\ell+1}Z_n,
\qquad
B_\ell=\sum_{n=1}^{480}\beta_n n^{2\ell}Z_n.
\]

22. **[доказано][COFINAL_FAMILY][PAPER]** Для \(k>480\) геометрический ряд даёт:
\[
\boxed{
r_k=
2\beta_k\sum_{\ell\ge0}\frac{A_\ell}{k^{2\ell+2}}
-
2\sum_{\ell\ge0}\frac{B_\ell}{k^{2\ell+1}}.
}
\]

23. **[доказано][COFINAL_FAMILY][PAPER]** При source-derived bound \(\beta_k=O(\log k)\):
\[
kr_k\longrightarrow-2B_0.
\]

24. **[доказано][FINITE_CELL][PAPER]** Для сырого \(E_k\):
\[
k^2\|E_k\|^2\longrightarrow4\sum_{n=1}^{70}\beta_n^2.
\]

25. **[предположено][FINITE_CELL][CONDITIONAL]** Измеренный диапазон \(45.5\)–\(53.0\) должен совпасть с правой частью пункта 24.

26. **[доказано][COFINAL_FAMILY][PAPER]** Первый решающий объект равен:
\[
\boxed{
B_0=\sum_{n=1}^{480}\beta_n Z_n.
}
\]

27. **[доказано][FINITE_CELL][CONDITIONAL]** При relay-значении \(\gamma\) scalar route требует ориентировочно:
\[
\|B_0\|<\frac12\sqrt{480\gamma}
=
4.736\cdot10^{-27}.
\]

28. **[доказано][COFINAL_FAMILY][PAPER]** Пункт 27 является диагностикой, а не сертификатом.

29. **[доказано][COFINAL_FAMILY][PAPER]** Строгий сертификат должен учитывать конечный префикс и остаток moment series.

30. **[доказано][ABSTRACT][PAPER]** Источник даёт грубую beta-envelope:
\[
|\beta_k|
\le
C_\beta+
\frac{\sqrt{13}}{2\pi}\log(2\pi k).
\]

31. **[доказано][ABSTRACT][PAPER]** Пункт 30 следует из source central column, \(|\sin x|\le\min(1,|x|)\) и \(e^x-e^{-x}\ge2x\).

32. **[доказано][COFINAL_FAMILY][PAPER]** Для \(K_0>480\) положим:
\[
q=\left(\frac{480}{K_0+1}\right)^2<1.
\]

33. **[доказано][COFINAL_FAMILY][PAPER]** После \(J\) моментов remainder удовлетворяет:
\[
\|R_J(k)\|
\le
\frac{2}{1-q}
\left(
\frac{L_{B,J}}{k^{2J+1}}
+
\frac{B_\beta(k)L_{A,J}}{k^{2J+2}}
\right).
\]

34. **[доказано][FINITE_CELL][PAPER]** В пункте 33:
\[
L_{B,J}=\sum_{n=1}^{480}|\beta_n|n^{2J}\|Z_n\|,
\]
\[
L_{A,J}=\sum_{n=1}^{480}n^{2J+1}\|Z_n\|.
\]

35. **[доказано][COFINAL_FAMILY][PAPER]** Пункты 22–34 дают замкнутую source-derived analytic envelope.

### ROUTE MAP

36. **[доказано][FINITE_CELL][CONDITIONAL]** Ранг 1: вычислить interval moments \(B_0,A_0,B_1,A_1\).

37. **[доказано][COFINAL_FAMILY][CONDITIONAL]** Ранг 2: посчитать Arb-prefix \(481\le k\le K_0\).

38. **[доказано][COFINAL_FAMILY][CONDITIONAL]** Ранг 3: закрыть хвост moment remainder и степенные суммы.

39. **[доказано][ABSTRACT][CONDITIONAL]** Birman–Schwinger остаётся на HOLD до провала matrix-valued Feshbach certificate.

### STRONGEST ATTACK

40. **[доказано][ABSTRACT][PAPER]** Scalar penalty использует:
\[
p=d^{-1}\sum_{k>480}\|r_k\|^2,
\qquad
B_{480}-pI.
\]

41. **[доказано][ABSTRACT][PAPER]** Точный directional object имеет вид:
\[
P_{\mathrm{tail}}
=
d^{-1}\sum_{k>480}r_k^*r_k.
\]

42. **[доказано][ABSTRACT][PAPER]** Всегда выполняется:
\[
P_{\mathrm{tail}}\preceq pI.
\]

43. **[доказано][ABSTRACT][PAPER]** Обратная оценка обычно ложна и может терять 55 порядков в одном направлении.

44. **[доказано][ABSTRACT][PAPER]** Поэтому scalar failure не убивает residual Feshbach route.

45. **[доказано][ABSTRACT][PAPER]** Правильный repair проверяет:
\[
\boxed{
B_{480}-P_{\mathrm{tail}}\succeq0.
}
\]

46. **[доказано][ABSTRACT][PAPER]** \(P_{\mathrm{tail}}\) является constructed Gram remainder, требуемым атакой **C10**.

47. **[предположено][COFINAL_FAMILY][CONDITIONAL]** Зарегистрированный прогноз: scalar \(pI\) будет слишком рыхлым.

48. **[предположено][COFINAL_FAMILY][CONDITIONAL]** Зарегистрированный прогноз: matrix-valued tail Gram сохранит жизнеспособность residual route.

## Действие

### FINAL PROPOSAL

49. **[доказано][FINITE_CELL][PAPER]** Не считайте сначала тысячи полных строк \(r_k\).

50. **[доказано][FINITE_CELL][PAPER]** Сначала вычислите четыре interval moments и проверьте source-beta identity.

51. **[доказано][COFINAL_FAMILY][PAPER]** После проверки используйте finite prefix и moment envelope.

52. **[доказано][COFINAL_FAMILY][PAPER]** Стройте matrix-valued tail Gram параллельно scalar diagnostic.

### CODEX DIRECTIVE

53. **[доказано][FINITE_CELL][PAPER]** Выполните следующий read-only target.

```text
TARGET:
  GLOWER_FULL_RESIDUAL_BETA_MOMENT_PREFLIGHT_N480

MODE:
  READ_ONLY
  NO_REPO_WRITE
  NO_LEAN_EDIT

SOURCE:
  docs/routeB_bus/phase1_scripts/ccm_control_cell_penalty.py
  q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceCommutator.lean
  docs/routeB_bus/phase4_scripts/glower_corrected_head.py

FROZEN:
  m: 13
  R: 70
  N: 480
  c0: 1e-58
  Y: interval solution of Dc*Y=-E
  source hashes: mandatory

TASK:
  1. Define beta_n = n*tau(n,0) from the source builder.
  2. Verify beta_-n = -beta_n on all finite control modes.
  3. Verify:
       Kodd(k,n)
       =
       2*(n*beta_k-k*beta_n)/(k^2-n^2)
     on interval controls.
  4. Build Z = vertical_stack(I_70,Y).
  5. Compute Arb enclosures for:
       B0 = sum beta_n Z_n
       A0 = sum n Z_n
       B1 = sum beta_n n^2 Z_n
       A1 = sum n^3 Z_n
  6. Check the raw identity:
       4*sum_{n=1}^{70} beta_n^2
     against the existing k^2*s_k profile.
  7. Compute direct full residual rows for selected k>480.
  8. Compare direct rows with the beta formula.
  9. Build finite-prefix Gram:
       P_prefix = d^(-1)*sum r_k^T r_k.
 10. Report both:
       scalar trace(P_prefix)
       matrix P_prefix.
 11. Do not classify the infinite tail before the analytic remainder exists.

REQUIRED OUTPUT:
  source hashes
  interval moments
  direct-versus-beta overlap
  raw-profile identity check
  finite-prefix Gram eigenvalue enclosures
  one decision code

DECISION CODES:
  BETA_MOMENT_SCALAR_ROUTE_PLAUSIBLE
  SCALAR_RESIDUAL_BOUND_TOO_LOOSE_MATRIX_GRAM_ALIVE
  N480_FINITE_CORRECTOR_KILLED_BY_PREFIX_RITZ
  SOURCE_BETA_IDENTITY_MISMATCH
  MOMENT_INTERVAL_UNRESOLVED

KILL RULE:
  Use one rigorous Ritz vector v.
  KILL only if:
    upper(v^T*(B480-P_prefix)*v) < 0.

FORBIDDEN:
  raw_E_column_ledger_as_residual
  componentwise_W02_WR_prime_absolute_sum_as_final_envelope
  midpoint_only_classification
  compare_penalty_to_minimum_LDL_pivot
  fit_a_decay_exponent
  change_R_N_c0_or_Y
  interrupt_any_running_process
```

### META CLOSEOUT

54. **[доказано][ABSTRACT][PAPER]** Неизвестность уменьшилась с «найти огибающую \(r_k\)» до четырёх interval moments и одного remainder formula.

55. **[доказано][ABSTRACT][PAPER]** Убит componentwise absolute-envelope route.

56. **[доказано][ABSTRACT][PAPER]** Нельзя снова использовать raw \(E_k\) как полную невязку.

57. **[доказано][ABSTRACT][PAPER]** Текущий smallest named gap:
\[
\boxed{
\texttt{FullResidualBetaMomentEnvelopeN480}.
}
\]

58. **[доказано][FINITE_CELL][PAPER]** Следующий cheapest decisive test — interval enclosure для \(B_0\).

59. **[доказано][ABSTRACT][PAPER]** Судьба старого прогноза «нормировка будет первым багом» остаётся `CONFIRMED`.

60. **[предположено][COFINAL_FAMILY][CONDITIONAL]** Новый прогноз scalar-failure зарегистрирован до вычисления \(B_0\).

```yaml
iteration:
  target: full_residual_tail_envelope
  status: PROGRESS
  failed_strategy: componentwise_absolute_decay
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: FullResidualBetaMomentEnvelopeN480
  invariant_learned: preserve the full source divided-difference cancellation before taking absolute values
  forbidden_future_move: replace the residual Gram by a raw-column scalar ledger
  next_decisive_test: interval_B0_and_prefix_Gram
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```

## Ограничение

61. **[доказано][COFINAL_FAMILY][PAPER]** Этот verdict не доказывает конечность полной residual penalty.

62. **[доказано][COFINAL_FAMILY][PAPER]** Этот verdict не доказывает \(B_{480}-P_{\mathrm{tail}}\succeq0\).

63. **[доказано][COFINAL_FAMILY][PAPER]** Профиль \(1/k^2\) сырой строки не определяет профиль полной невязки.

64. **[доказано][COFINAL_FAMILY][PAPER]** Провал scalar \(pI\) не убивает matrix-valued Gram certificate.

65. **[доказано][ABSTRACT][PAPER]** `CHALLENGER_NOT_RH`, `BUS_010: VOID` и `GOAL_055: HOLD` остаются без изменений.
