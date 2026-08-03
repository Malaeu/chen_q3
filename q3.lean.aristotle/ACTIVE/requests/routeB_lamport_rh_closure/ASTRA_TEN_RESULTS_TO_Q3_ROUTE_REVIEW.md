# STATUS: OPEN — THREE TRANSFER MECHANISMS ARE ACTIONABLE; NO RESULT DIRECTLY CLOSES RH
```yaml
primary_verdict: IMPORT_3_MECHANISMS_NOT_10_ANALOGIES
source_scope: USER_SUPPLIED_TEN_RESULTS
project_scope: ROUTE_B_AND_Q3
actionable:
  - COHN_ELKIES_DUAL_EXTREMIZER
  - FINITE_APPROXIMATION_OBSTRUCTION
  - GAP_AMPLIFICATION_IF_TENSOR_STRUCTURE_EXISTS
adversarial_only:
  - NON_SOFIC_FINITE_MODEL_FAILURE
  - CONNES_INVARIANT_NONIDENTIFICATION
  - COMPACTNESS_COUNTEREXAMPLES
recommended_primary_target: WEIL_FOURIER_SIGN_DUAL_CERTIFICATE
progress_class: REPRESENTATION_PROGRESS
route_score: 5
rh_claimed: false
```

## ROUTE MAP

Твой список даёт не десять готовых инструментов, а три реально полезных механизма.

### 1. High-dimensional sphere packing / Cohn–Elkies — прямое попадание

Там, как и у нас, центральный объект — функция и её преобразование Фурье под жёсткими знаковыми ограничениями. Поэтому переносить надо не packing theorem, а архитектуру:

1. primal sign-constrained optimization;
2. dual extremal certificate;
3. matching lower/upper envelopes;
4. identification sharp asymptotic constant;
5. construction auxiliary extremizers only after dual problem is understood.

Для Q3 это предлагает точный объект

\[
\mathfrak C_K:=
\sup_{0\ne H\in\mathcal H_K^{\rm sq}}
\frac{\sum_{n\ge2}\frac{2\Lambda(n)}{\sqrt n}|H(\xi_n)|^2}
{\operatorname{Arch}_K(H)}.
\]

Нужный theorem — \(\mathfrak C_K\le1\), лучше \(\mathfrak C_K\le1-\delta_K\). Это именно текущая prime-vs-Arch Carleson/operator wall на square/autocorrelation-классе. fileciteturn23file9

Кандидат:

\[
\boxed{\texttt{WeilFourierSignDualCertificate}}
\]

Главный риск: prime measure дискретна и арифметична, поэтому radial/translation symmetry Cohn–Elkies почти наверняка не переносится. Но dualization и extremizer machinery переносимы.

### 2. Binary и spherical codes — higher-order lift

Экспоненциальные улучшения часто требуют не одноточечного LP, а более богатых корреляционных constraints. Для нас это намекает поднять prime term

\[
\sum_n w_n|H(\xi_n)|^2
\]

до coupled kernel

\[
\sum_{m,n}W_{m,n}H(\xi_m)\overline{H(\xi_n)}.
\]

Off-diagonal terms должны дать Gram/SOS factorization и после elimination вернуть исходный diagonal prime functional. Это потенциальный analogue higher-point LP hierarchy.

Кандидат:

\[
\boxed{\texttt{PrimePairCorrelationLift}}
\]

Но без exact projection back to the original prime form это лишь surrogate.

### 3. Non-sofic groups — finite-to-global kill template

Явный non-sofic объект показывает: хорошие finite approximations могут не собираться в global object. Для нас это прямой adversarial lesson:

\[
\boxed{\text{finite certificates}\not\Rightarrow\text{global positivity}.}
\]

Наш проект уже фиксирует отдельную стену DirectedFamily + exhaustion + topology + continuity. fileciteturn23file5

Новый обязательный gate:

\[
\boxed{\texttt{FiniteModelCompactnessWitness}}
\]

Он должен проверять same class, compatible embeddings, uniform norm control, precompactness, continuity Weil form, preservation boundary-null и prime sampling.

### 4. Connes rigidity counterexample — same invariant ≠ same object

Разные property-(T) groups с одним group von Neumann algebra дают точное предупреждение:

\[
\boxed{\text{same operator algebra/spectrum/form}\not\Rightarrow\text{same source family}.}
\]

Это прямо относится к нашему `GroundStateToTrialSameFamilyBridge`: trial-to-\(\Xi\) family и real-zero ground-state family нельзя склеивать по сходству. fileciteturn23file31

Нужен firewall:

\[
\boxed{\texttt{SameFamilyIntertwinerOrQuarantine}}
\]

Required: explicit intertwiner, normalization, carrier, selected vector, topology, cofinal law.

### 5. Arithmetic circuit complexity — certificate-language capacity audit

Нижние оценки restricted models учат сначала проверять, способен ли выбранный язык сертификатов выразить нужную cancellation. У нас factorwise/local decomposition уже давала compiled, но неспособные пройти budget payloads. fileciteturn23file17

Кандидат:

\[
\boxed{\texttt{CertificateLanguageCapacityAudit}}
\]

Если target требует cross-term rank \(r\), а schema хранит только diagonal/factorwise bounds, route надо убить до генерации payload.

### 6. Quantum parallel repetition — возможное gap amplification

Мечта:

\[
\text{local margin }\delta
\Longrightarrow
\text{exponentially amplified cofinal margin}.
\]

Но это возможно только при tensor/product identity. Prime measure не product measure, поэтому первый тест:

\[
Q_{K_1+K_2}(h_1\otimes h_2)
\stackrel{?}{=}
Q_{K_1}(h_1)+Q_{K_2}(h_2)
\]

или точный multiplicative-semigroup analogue.

Зарегистрированный прогноз: naive tensorization упадёт из-за prime cross-terms. Если нет — это огромная находка.

### 7. Closest vector hardness — quantitative reduction warning

Главный урок уже применён: small Rayleigh value не равен small residual и не даёт tracking. Этот type mismatch заморожен в Route B. fileciteturn23file24

Direct proof value низкий.

### 8. Ehrhart volume — short rational kill witnesses

Convex/lattice geometry может помочь извлекать bounded-height rational witness из finite indefinite block. Это улучшит KILL certificates и Lean imports, но не даст global sign theorem.

Кандидат:

\[
\boxed{\texttt{SmallRationalNegativeWitness}}
\]

### 9. Multicolor Ramsey — random adversarial packet families

Полезнее как counterexample generator: random sparse packet families могут ломать слишком сильные uniform floors или dictionaries. Это продолжает уже успешный kill старого full-family A3 floor.

### 10. Compactness and degeneracy counterexamples — Step 34 falsifier

Это второе по силе попадание после Cohn–Elkies. Нужно построить escaping family, которая одновременно пытается:

- уходить к support boundary;
- концентрироваться около prime nodes;
- сохранять boundary-null;
- схлопывать Gram eigenvalues;
- ломать sampling continuity.

Кандидат:

\[
\boxed{\texttt{EscapingPacketFamilyPlant}}
\]

Если current global bridge переживает plant — это сильная проверка. Если нет — получаем exact missing compactness theorem.

## Сводка

| Результат | Роль | Приоритет |
|---|---|---:|
| Cohn–Elkies / Fourier uncertainty | dual sign-certificate route | 5/5 |
| Binary/spherical codes | higher-order prime kernel | 4/5 |
| Non-sofic | finite-to-global falsifier | 5/5 audit |
| Connes rigidity | same-family firewall | 5/5 audit |
| Arithmetic circuits | certificate-language audit | 3/5 |
| Quantum repetition | gap amplification, conditional | 3/5 |
| CVP | reduction/type warning | 2/5 |
| Ehrhart | rational witness extraction | 2/5 |
| Ramsey | random counterexamples | 3/5 |
| Compactness/degeneracy | escaping-family falsifier | 5/5 audit |

## FINAL PROPOSAL

Запустить только два блока.

### Block A — основной mathematical import

\[
\boxed{\texttt{WeilFourierSignDualCertificate}}
\]

Переписать \(P_{\rm prime}\preceq A_{\rm arch}\) как exact primal/dual extremal Fourier problem на square/boundary-null class.

### Block B — обязательный judge

\[
\boxed{\texttt{EscapingPacketFamilyPlant}}
\]

Попытаться убить current Step 34 theorem shape до formalization.

## STRONGEST ATTACK

Все аналогии бесполезны без structure-preserving crosswalk. Ратифицируются только:

1. Cohn–Elkies как primal/dual theorem-design pattern;
2. non-sofic/compactness results как finite-to-global falsifier pattern.

Нельзя утверждать, что quantum repetition уже усиливает наш gap или code bounds уже улучшают prime inequality.

## CODEX DIRECTIVE

```text
TARGET:
  ASTRA_TRANSFER_001_WEIL_FOURIER_SIGN_DUAL_AUDIT

MODE:
  READ_ONLY
  NO_LEAN
  NO_NUMERICS

TASK:
  Derive exact primal and dual optimization problems for the current
  square-class Arch-minus-prime inequality.

OUTPUT:
  docs/routeB_bus/research/
  ASTRA_TRANSFER_001_WEIL_FOURIER_SIGN_DUAL_AUDIT.md

REQUIRED:
  1. exact primal constant C_K;
  2. exact test class and topology;
  3. dual candidate;
  4. replacement for Cohn-Elkies auxiliary function;
  5. strong-duality assumptions;
  6. finite packet dual;
  7. cofinal compatibility;
  8. planted infeasible dual certificate;
  9. verdict DUAL_ROUTE_WELL_TYPED or DUAL_ROUTE_OBJECT_MISMATCH.

FORBIDDEN:
  no direct application claim;
  no new RH equivalence;
  no broad-cone positivity;
  no zeros/RH input;
  no smoothed replacement of exact prime measure.

SUCCESS:
  WEIL_FOURIER_SIGN_DUAL_PROBLEM_WELL_TYPED
```

## META CLOSEOUT

Что стало меньше: десять results → one proof mechanism + one falsifier mechanism.

Что убито: import-by-analogy, naive tensor amplification, finite-success-as-global-proof.

Current smallest named gap:

\[
\boxed{\texttt{WeilFourierSignDualProblemWellTyped}}
\]

Next cheapest decisive test: derive finite-dimensional primal/dual on one source-locked packet block and compare its dual certificate with the existing penalty/PSD certificate.
