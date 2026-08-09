# STATUS: OPEN — EXACT LOWER-BOUND CLOSURE CONTRACT SELECTED
```yaml
PRIMARY: RUN_GLOWER_ODD_YOSHIDA_RESIDUAL_FESHBACH
PRIMARY_COUNT: 1

TARGET:
  cell_m: 13
  log_length: log(13)
  centered_half_length: log(sqrt(13))
  sector: ODD
  requested_floor:
    c0: 1e-58
    relation_to_given_a: c0 > 4.719980e-59
  desired_conclusion:
    - inf_spec_K_odd_infinity >= c0
    - forall_N_beta_star_N >= c0
    - L >= c0 > 0

CLOSURE_CHAIN:
  - EXACT_ODD_COMPRESSION_CROSSWALK
  - YOSHIDA_HIGH_MODE_COERCIVITY
  - RESIDUAL_FESHBACH_FINITE_HEAD_CERTIFICATE
  - COMPRESSION_TRANSFER_TO_ALL_FINITE_N

PASS:
  code: GLOWER_ODD_CONSTANT_FLOOR_PROVED
  condition: rigorous_lower_envelope_of_corrected_head_matrix_is_nonnegative
  direction: LOWER_ENVELOPE
  scope: COFINAL_FAMILY
  verifier: PAPER_PLUS_ARB_INTERVAL_THEN_LEAN

KILL:
  code: GLOWER_TARGET_C0_KILLED
  condition: rigorous_Ritz_upper_envelope_below_c0
  direction: UPPER_ENVELOPE
  scope: FINITE_CELL_TO_ABSTRACT_TARGET
  verifier: ARB_INTERVAL

SELECTED_REPRESENTATION:
  name: YOSHIDA_TAIL_PLUS_RESIDUAL_FESHBACH
  absolute_row_sums: FORBIDDEN
  N_extrapolation: FORBIDDEN
  Aitken: FORBIDDEN
  pointwise_multiplier_positivity: FORBIDDEN
  finite_PSD_as_global_proof: FORBIDDEN

NEXT_MINIMAL_GAPS:
  - OddSourceWeilCompression13
  - YoshidaTailCoercivity13Explicit
  - OddResidualFeshbachLower13

REGISTERED_PREDICTION:
  tail_supplier: PASS_AFTER_EXPLICIT_CONSTANT_EXTRACTION
  corrected_head_c0_1e58: POSITIVE
  likely_failure_point: normalization_or_residual_tail_budget
  no_retroactive_target_change: true

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## Прямой ответ

**\(L\ge0\) доказывает не ещё один расчёт \(\beta_N\), а следующая бесконечномерная теорема:**

\[
\boxed{
Q_{13}^{\mathrm{odd}}(f)\ge c_0\|f\|_2^2
\qquad
\forall f\in\mathcal D(Q_{13}^{\mathrm{odd}})
}
\]

с фиксированным рациональным

\[
\boxed{c_0=10^{-58}>4.719980\cdot10^{-59}.}
\]

После точного отождествления конечных нечётных матриц со сжатиями этой формы автоматически:

\[
x^*K_N^{\mathrm{odd}}x
=
Q_{13}^{\mathrm{odd}}(\mathcal S_Nx)
\ge
c_0\|\mathcal S_Nx\|^2
=
c_0\|x\|^2
\]

для **каждого** \(N\). Поэтому

\[
\beta_N^*\ge c_0
\quad\forall N,
\qquad
L=\inf_N\beta_N^*\ge c_0>0.
\]

Это закрывает не только \(L\ge0\), а сразу нужную постоянную границу выше \(a\).

`[COFINAL_FAMILY][CONDITIONAL]`

## Почему этот объект уже наш, а не новый surrogate

Репозиторий уже доказывает точное равенство трёхкомпонентной исходной формы

\[
W_{0,2}+W_{\mathrm{arch}}-W_{\mathrm{prime}}
\]

и матричной формы `ccmWeilMatFinite`; знаки, Fourier-нормировка, von-Mangoldt cutoff и ordered slots сохранены буквально. fileciteturn53file0

Отдельно уже source-locked:

- **CCM \(q\)-kernel** как точная cosine-correlation zero-extended мод. fileciteturn47file0
- **\(W_{0,2}\)** как точный one-sided source integral. fileciteturn48file0
- **архимедова часть** как \(-\,\mathrm{ccmWR}\) на всех модах. fileciteturn52file0
- **prime-часть** с внешним минусом только в полном Weil-ledger. fileciteturn50file0

Следовательно, новый шаг не меняет матрицу. Он добавляет только недостающий **infinite-form consumer** и доказывает знак этой же формы.

`[ABSTRACT][LEAN]`

## Теорема, которая реально закрывает стену

Пусть

\[
\mathcal H^-=
H_R\oplus T_R
\]

— нечётное пространство, где

\[
H_R=\operatorname{span}\{s_1,\dots,s_R\},
\qquad
T_R=\overline{\operatorname{span}}\{s_{R+1},s_{R+2},\dots\}.
\]

Для целевого пола \(c_0\) запишем форму \(Q_{13}^{\mathrm{odd}}-c_0I\) блоками:

\[
\begin{pmatrix}
A_c&E^*\\
E&D_c
\end{pmatrix},
\qquad
A_c=A-c_0I,
\qquad
D_c=D-c_0I.
\]

### Вход 1 — настоящий хвостовой пол

Нужно доказать:

\[
\boxed{
D_c\ge dI
}
\]

с явным \(d>0\).

Это не новая гипотеза из воздуха. У Yoshida/Suzuki уже есть unconditional finite-codimension mechanism: для любого фиксированного диапазона \(0<a\le a_0\) и любого \(\mu>0\) существует Fourier cutoff \(R\), после которого локализованная Weil/screw-форма имеет пол не меньше \(\mu\). Доказательство использует Parseval и подавление низкочастотной массы high-mode функций, а не абсолютные суммы строк. Для нашей клетки надо только извлечь явные константы при

\[
a_0=\log\sqrt{13}
\]

и перенести их через точный centered-coordinate crosswalk. citeturn792316search1turn151916view0

Выбираем, например,

\[
\mu=1,
\qquad
d=1-c_0.
\]

`[COFINAL_FAMILY][PAPER_TO_BE_EXPLICITIZED]`

### Вход 2 — finite corrected-head certificate

Выбираем явный оператор

\[
Y:H_R\to T_R,
\]

который приближает решение хвостового уравнения

\[
D_cY=-E.
\]

Определяем:

\[
R_c:=E+D_cY,
\]

\[
B_c:=
A_c+E^*Y+Y^*E+Y^*D_cY.
\]

Тогда достаточно одного конечномерного сертификата:

\[
\boxed{
B_c-d^{-1}R_c^*R_c\succeq0.
}
\]

Это и есть правильная замена «посчитать ещё один большой eigenvalue».

### Почему сертификат достаточен

Для \(h\in H_R\), \(z\in T_R\) и \(t=Yh+z\):

\[
\begin{aligned}
(Q_{13}^{\mathrm{odd}}-c_0I)(h+t)
&=
\langle B_ch,h\rangle
+
2\Re\langle R_ch,z\rangle
+
\langle D_cz,z\rangle\\
&\ge
\langle B_ch,h\rangle
-d^{-1}\|R_ch\|^2\\
&=
\left\langle
\left(B_c-d^{-1}R_c^*R_c\right)h,h
\right\rangle.
\end{aligned}
\]

Последняя строка неотрицательна по finite certificate. Значит

\[
Q_{13}^{\mathrm{odd}}\ge c_0I.
\]

Это доказательство нижней границы. Здесь нет предельной экстраполяции и нет подмены universal quantifier конечным расчётом.

`[ABSTRACT][PAPER]`

## Что конкретно обходит старые проблемы

### 1. Interlacing больше не является стеной

Interlacing используется только после доказательства:

\[
K_N^{\mathrm{odd}}\succeq c_0I
\quad\forall N.
\]

Он больше не должен угадывать знак предела.

`[COFINAL_FAMILY][PAPER]`

### 2. Логарифмическая расходимость absolute row sums не важна

Мы не оцениваем

\[
\sum_j|K_{ij}|.
\]

Хвост доказывается в **Fourier/form norm**, как в Yoshida–Suzuki high-mode theorem. Сокращения divided differences сохраняются.

`[ABSTRACT][PAPER]`

### 3. Не нужен \(N=480\)

\(N=480\) — ещё один upper witness. Он не добавляет universal lower statement.

В выбранном маршруте вычисляется не \(\beta_{480}\), а:

\[
\lambda_{\min}^{\mathrm{Arb}}
\left(
B_c-d^{-1}R_c^*R_c
\right).
\]

Это непосредственно lower envelope нужного бесконечного объекта.

`[FINITE_CELL][ARB_INTERVAL]`

### 4. Не нужна ложная pointwise positivity символа

Полный Fourier multiplier может менять знак. Мы не требуем его pointwise nonnegativity.

Положительность получается из:

```text
high-mode coercivity
+ finite low-mode correction
+ exact residual budget.
```

`[ABSTRACT][PAPER]`

### 5. W02 не обязан быть положительной частью

Отрицательный rank-one \(W02^{\mathrm{odd}}\) просто остаётся внутри точной формы и finite corrected-head matrix. Его не надо переименовывать в \(P\).

`[ABSTRACT][PAPER]`

## Три точных proof-lock

### Lock A — `OddSourceWeilCompression13`

Теорема:

```text
для каждого N и каждого odd coefficient vector x:

  source odd Weil form (odd synthesis x)
    =
  x* · K_odd(13,N) · x.
```

Она должна быть получена из уже доказанного full finite-form crosswalk плюс точная parity isometry.

**Стоимость:** низкая.  
**Результат:** finite matrices становятся буквальными compressions одной формы.

`[FINITE_CELL][LEAN]`

### Lock B — `YoshidaTailCoercivity13Explicit`

Теорема:

\[
\exists R,d>0,\quad
Q_{13}^{\mathrm{odd}}(t)-c_0\|t\|^2
\ge d\|t\|^2
\quad
\forall t\in T_R.
\]

Нужно извлечь constants из proof Theorem 4.3, а не импортировать слово «существует».

**Стоимость:** средняя.  
**Результат:** бесконечный хвост закрыт раз и навсегда.

`[COFINAL_FAMILY][PAPER_THEN_LEAN]`

### Lock C — `OddResidualFeshbachLower13`

Абстрактная Lean-теорема:

```text
D_c >= d I
B_c - d⁻¹ R_c* R_c >= 0
--------------------------------
full_block_operator >= c0 I
```

После неё Arb импортирует только конечную corrected-head matrix и rigorous residual norm.

**Стоимость:** низкая для abstract theorem, средняя для source instantiation.  
**Результат:** полный оператор получает constant floor.

`[ABSTRACT][LEAN_PLUS_ARB_INTERVAL]`

## Самый дешёвый решающий тест

Не строить пока Lean-файл и не считать \(N=480\).

Сначала один read-only preflight:

```text
1. Извлечь явную формулу R = R(a0, μ) из Suzuki/Yoshida tail proof
   при a0 = log(sqrt(13)), μ = 1.

2. Построить один corrected-tail map Y для head H_R.

3. Считать Arb lower enclosure:
     λ_min(B_c - d⁻¹ R_c*R_c)
   при c0 = 1e-58.

4. PASS только если lower endpoint >= 0.
```

**Зарегистрированный прогноз:**

```text
tail coercivity:
  PASS.

corrected-head floor at c0=1e-58:
  PASS.

вероятный первый баг:
  centered normalization или неполный residual tail,
  а не отрицательный true floor.
```

Нельзя после результата менять \(c_0\), parity normalization или definition of \(Y\).

`[FINITE_CELL][CONDITIONAL]`

## Если первый corrected-head representation нулесогласован

Протокол требует не наращивать размер вслепую. Две заранее разрешённые re-representations:

### Re-representation 1 — exact form-orthogonal Yoshida head

Вместо произвольного \(Y\) использовать **Weil-orthogonal projection** low modes на coercive tail. Тогда \(R_c=0\), и остаётся чистая finite Schur matrix.

- **Kill-power:** очень высокий.
- **Стоимость:** средняя/высокая.
- **Преимущество:** исчезает residual penalty.

### Re-representation 2 — Birman–Schwinger inertia at \(c_0\)

Выбрать положительный reference tail \(A_0\) и доказать:

\[
\|A_0^{-1/2}VA_0^{-1/2}\|<1
\]

или сертифицировать отсутствие eigenvalue \(1\) compact Birman–Schwinger operator.

- **Kill-power:** высокий.
- **Стоимость:** высокая.
- **Преимущество:** проверяет число отрицательных направлений, а не tiny raw eigenvalue.

**Дискриминатор:** sign of the lower enclosure of the corrected finite operator. Результат, содержащий ноль, без одной из этих двух смен представления считается незавершённым.

## STRONGEST ATTACK

Самое сильное возражение:

> Suzuki/Yoshida tail theorem может относиться к соседнему классу \(K_N(a)\), а не к нашему odd CCM tail.

Правильный ответ — не слова, а exact crosswalk:

\[
[0,\log13]
\longleftrightarrow
[-\log\sqrt{13},\log\sqrt{13}],
\]

\[
V_n
\longleftrightarrow
e^{\pi inx/a},
\]

\[
c_{-n}=-c_n
\longleftrightarrow
\text{odd sector},
\]

с тем же \(L^2\)-нормированием и той же Weil-form convention.

Если этот crosswalk не компилируется, текущий route останавливается кодом:

```text
YOSHIDA_TAIL_WRONG_OBJECT
```

Не разрешено заменять его «похожим» tail theorem.

Второе возражение:

> Finite \(Y\) может скрывать необработанную бесконечную часть residual.

Именно поэтому certificate использует полный norm bound \(\|R_c\|\), а не residual внутри выбранной матрицы. Если full residual bound отсутствует, PASS запрещён.

## CODEX DIRECTIVE

```text
TARGET:
  GLOWER_ODD_YOSHIDA_RESIDUAL_FESHBACH_PREFLIGHT

MODE:
  READ_ONLY_MATH_AND_NUMERICAL_PREFLIGHT
  NO_REPO_WRITE
  NO_LEAN_EDIT

SOURCE:
  repo: Malaeu/chen_q3
  branch: rh_clean
  cell: m=13
  target_floor: c0=1e-58

TASK_A — exact object:
  1. Locate the full finite source-Weil crosswalk.
  2. Derive the normalized odd parity synthesis.
  3. State OddSourceWeilCompression13 exactly.

TASK_B — tail:
  1. Read Suzuki arXiv:2206.03682, Theorem 4.3 and its proof.
  2. Extract every constant in the N^(-1/2) low-frequency estimate.
  3. Specialize to a0=log(sqrt(13)), μ=1.
  4. Return an explicit integer R and d=1-c0.
  5. No asymptotic O-notation may remain.

TASK_C — residual Feshbach:
  1. Construct one source-faithful tail corrector Y.
  2. Bound the FULL tail residual R_c=E+(D-c0 I)Y.
  3. Build an Arb enclosure of
       B_c - d^(-1) R_c*R_c.
  4. Report its smallest-eigenvalue interval.

PASS:
  lower endpoint >= 0
  code GLOWER_ODD_CONSTANT_FLOOR_PREFLIGHT_PASS

STOP:
  object crosswalk mismatch
  unexpanded Yoshida constant
  incomplete full-tail residual
  interval contains zero

FORBIDDEN:
  N=480 extrapolation
  Aitken
  absolute row sums
  fitted weights
  moving c0
  finite residual reported as full residual
  pointwise multiplier positivity
  RH-dependent zero sum
  repo edits
  Lean edits
```

## META CLOSEOUT

**Что стало меньше?**

Старая фраза

```text
prove L >= 0 somehow
```

сжалась до одного finite lower-envelope certificate:

\[
\boxed{
B_c-d^{-1}R_c^*R_c\succeq0.
}
\]

**Что убито?**

- дальнейшая экстраполяция \(\beta_N\);
- \(N=480\) как proof step;
- absolute-row-sum G1;
- W02 как positive part;
- pointwise positivity полного symbol.

**Что нельзя повторять?**

Нельзя снова считать principal eigenvalues и надеяться, что монотонность сама выдаст нижнюю границу.

**Текущий минимальный named gap:**

\[
\boxed{\texttt{YoshidaTailCoercivity13Explicit}}
\]

после него:

\[
\boxed{\texttt{OddResidualFeshbachLower13}}.
\]

**Следующий решающий тест:**

Arb sign of

\[
B_{10^{-58}}-d^{-1}R_{10^{-58}}^*R_{10^{-58}}.
\]

**Fate of prior prediction:**

```text
"weighted/graded row-norm repairs raw G1":
  REFUTED AS FINAL METHOD.

"cancellation-preserving operator norm repairs G1":
  CONFIRMED AND STRENGTHENED:
  the correct repair is Yoshida high-mode form coercivity
  plus residual Feshbach, not a weighted row sum.
```

```yaml
iteration:
  target: constant_odd_sector_lower_bound
  status: OPEN
  failed_strategy: extrapolate_nested_finite_eigenvalues
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: YoshidaTailCoercivity13Explicit
  invariant_learned: finite odd matrices must be treated as compressions of one exact continuum form
  forbidden_future_move: use another finite N as a universal lower-bound argument
  next_decisive_test: corrected_head_Arb_lower_envelope_at_c0_1e58
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```
