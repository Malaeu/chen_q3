# STATUS: OPEN — SUPPLIER_A_038_DIRECTIVE_RATIFIED
```yaml
primary_verdict: SUPPLIER_A_038_DIRECTIVE_RATIFIED
current_smallest_gap: ScaledOuterSignBarrierFourThirds
next_gap_after_success: RelativeBoundaryCellProductBound

route_state: CHALLENGER_NOT_RH
bus_010: VOID
state_promotion: false
rh_claimed: false
repository_writes_performed: false
computations_run_by_judge: false

scope:
  supplier_A: COFINAL_FAMILY
  regression_m257: FINITE_CELL
  tooth_036: FINITE_CELL_REHEARSAL_ONLY

bootstrap:
  requested_nested_alias: docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md
  nested_alias_status: MISSING
  canonical_root_protocol: docs/routeB_bus/PROSHKA_SYSTEM_PROMPT_v2.md
  canonical_root_protocol_status: LOADED

post_035:
  transaction_034: COFINAL_EDGE_SLIVER_REDUCTION_PROVED
  transaction_035: EDGE_SLIVER_034_MATERIALIZED
  cofinal_outer_lobe: NOT_PROVED
  outer_lobe_027_scope: FINITE_CELL_m_13_53_257
  lean_034R: PENDING_NOT_CONSUMED
  muntz_v3: PENDING_NOT_CONSUMED

prediction_score:
  P034_1_radius_driven: REFUTED_AT_TESTED_MUTATIONS
  P034_2_sampled_response_intrinsic: STRENGTHENED_NOT_PROVED_COFINALLY
  P034_3_A_edge_four_thirds: PARTIAL_M257_ONLY
  P034_4_reduction_then_one_wall: HALF_REDUCTION_PROVED_TWO_WALLS_REMAIN
  P034_5_teeth_outside_moment: CONFIRMED
  P035_1_hashes_match: CONFIRMED
  P035_2_radius_driven: MISS
  P035_3_scope_027_finite: CONFIRMED

tooth_036:
  decision: ABSORB_AS_FINITE_SUPPLIER_A_REHEARSAL
  standalone_critical_path_goal: false
  may_be_used_as_cofinal_premise: false
  execute_existing_goal_as_written: false

transition_object:
  authoritative: a_intrinsic_m
  definition: infimum_of_outer_a_e_nonnegativity_region
  tooth_aligned_identity_a_eq_m_over_r: UNPROVED_AND_FALSE_IN_GENERAL
  certificate_cutoff_r195: REGRESSION_ONLY
```

## ROUTE MAP

| Узел | Судейский статус | Что разрешено потреблять | Tags |
|---|---|---|---|
| **034-R** | Закрыт как sharp abstract reduction; \(m=257\) реализован с точным запасом \(1/65\). Supplier A и Supplier B остались открытыми. fileciteturn17file0L134-L199 fileciteturn18file0L70-L99 | Формулу edge-sliver и её sharpness | `[ABSTRACT][PAPER]` |
| **035** | Материализация завершена: replay \(26/26\), P5/P7 сработали, хэш-цепь совпала, Route B не повышен. fileciteturn21file0L3-L40 | Канонические артефакты 034 и post-035 ledger | `[FINITE_CELL][PAPER]` |
| **P1 radius mutation** | \(r_{\rm cert}=195\), argmax \(225\) и число 62 не изменились при \(\rho/2,\rho,2\rho\); менялась только амплитуда. fileciteturn22file0L3-L13 | Только отрицательный результат против radius-driven prediction | `[FINITE_CELL][ARB_INTERVAL]` |
| **031 Jacobi identity** | Divided-difference identity и полный Green ledger доказаны, terminal term оставлен живым. Но опубликованный scope 031 — только \(m=257\), не кофинальная семья. fileciteturn24file0L14-L16 fileciteturn24file0L49-L102 | Seed для parametric lift, не готовый cofinal theorem | `[FINITE_CELL][PAPER]` |
| **027 outer lobe** | \(E_\star\le0\) на \([1,\lambda]\) доказано лишь для \(m\in\{13,53,257\}\). fileciteturn25file0L5-L9 fileciteturn25file0L57-L72 | Finite regressions; не 034-D на кофинальной семье | `[FINITE_CELL][ARB_INTERVAL]` |
| **Supplier A** | Требуется \(\mathscr S_m(a)\ge0\) a.e. на \([4/3,m]\). При отдельном cofinal outer-lobe theorem Jacobi-домен сокращается до \([4/3,\sqrt m]\). fileciteturn18file0L36-L50 fileciteturn18file0L107-L135 | Только parametric identity + независимый sign proof | `[COFINAL_FAMILY][CONDITIONAL]` |
| **036 tooth sign** | Сам файл уже помечает себя конечной фоновой репетицией двигателя Supplier A и признаёт, что teeth не входят в Lebesgue budget. fileciteturn23file0L3-L10 fileciteturn23file0L18-L24 | Regression/plant harness для Green engine | `[FINITE_CELL][CONDITIONAL]` |

### Счёт прогнозов без ретроактивного ремонта

| Прогноз | Итог | Судейская запись |
|---|---|---|
| **P034-1 / P035-2:** cutoff predominantly radius-driven | **REFUTED_AT_TESTED_MUTATIONS / MISS** | Новый флаг `P1_RADIUS_INTRINSIC_SUSPECT` — это новая post-test гипотеза, не спасение старого прогноза. `[FINITE_CELL][ARB_INTERVAL]` |
| **P034-2:** transition определяется sampled response, не голым нулём \(\Psi_m\) | **STRENGTHENED** | P1 убрал простое radius-объяснение; P3 точно показывает, что знак sampled sum не эквивалентен знаку \(\Psi\). Но cofinal transition theorem ещё отсутствует. `[FINITE_CELL][CONDITIONAL]` |
| **P034-3:** \(A_{\rm edge}=4/3\) переживает cofinal audit | **PARTIAL** | Для \(m=257\): \(257/195<4/3\) с запасом \(1/65\). Для cofinal family — OPEN. `[FINITE_CELL][PAPER] [COFINAL_FAMILY][CONDITIONAL]` |
| **P034-4:** reduction закрывается, остаётся product wall | **HALF** | Reduction закрыт. Поправка подтверждена: сначала Supplier A sign barrier, затем Supplier B product ledger. `[ABSTRACT][PAPER]` |
| **P034-5:** teeth вне момента | **CONFIRMED** | Конечное множество teeth не меняет Lebesgue integral. `[FINITE_CELL][PAPER]` |
| **P035-1:** materialized hashes совпадут | **CONFIRMED** | Все принятые артефакты и оба Proshka-входа совпали по заявленным SHA-256. fileciteturn21file0L85-L115 `[FINITE_CELL][PAPER]` |
| **P035-3:** 027 останется finite-cell | **CONFIRMED** | Scope явно \(m\in\{13,53,257\}\). `[FINITE_CELL][PAPER]` |

## FINAL PROPOSAL

### 1. Goal 038 ратифицируется

Канонический target:

\[
\boxed{\texttt{ScaledOuterSignBarrierFourThirds}}
\]

с финальным заключением

\[
\boxed{
\forall m\in\mathcal M,\qquad
\mathscr S_m(a)\ge0
\quad\text{для почти всех }a\in[4/3,m].
}
\]

`[COFINAL_FAMILY][CONDITIONAL]`

Допустимы ровно два способа закрытия домена:

\[
\boxed{
\mathscr D_m(a)\ge0
\quad\text{a.e. на }[4/3,m]
}
\]

без использования 027, либо

\[
\boxed{
\mathscr D_m(a)\ge0
\quad\text{a.e. на }[4/3,\sqrt m]
}
\]

вместе с отдельно доказанным

\[
\boxed{
\texttt{CofinalOuterLobeGate}:
\quad
\mathscr S_m(a)\ge0
\quad\text{a.e. на }[\sqrt m,m].
}
\]

`[COFINAL_FAMILY][CONDITIONAL]`

Finite-cell 027 не занимает второй слот. Это было бы прямым finite-to-cofinal shortcut.

### 2. Primary Jacobi route требует parametric lift

031 даёт seed-identity

\[
\mathscr S_m(a)
=
\frac{\Theta_{4,m}-\Theta_{0,m}}2\,
\mathscr D_m(a),
\qquad
\Theta_{4,m}-\Theta_{0,m}>0,
\]

но опубликованный theorem/certificate имеет scope \(m=257\). Поэтому первая содержательная обязанность 038:

\[
\boxed{
\texttt{ParametricScaledJacobiProfileIdentity}
}
\]

для каждого admissible \(m\in\mathcal M\), с exact forcing term, нижним boundary term и живым terminal term. `[COFINAL_FAMILY][CONDITIONAL]`

Sign theorem разрешён только после этого identity:

\[
\boxed{
\texttt{ParametricScaledJacobiDiscriminatorNonneg}:
\quad
\mathscr D_m(a)\ge0.
}
\]

### 3. Исправление объекта перехода

Авторитетный intrinsic object:

\[
\boxed{
a_{\mathrm{intr}}(m)
:=
\inf\left\{
A\in[1,m]:
\mathscr S_m(a)\ge0
\text{ a.e. на }[A,m]
\right\}.
}
\]

Supplier A эквивалентно требует

\[
a_{\mathrm{intr}}(m)\le\frac43
\]

на выбранной кофинальной семье. `[COFINAL_FAMILY][CONDITIONAL]`

После этого можно определить индекс локальной полосы

\[
r_{\mathrm{intr}}(m)
:=
\left\lfloor\frac{m}{a_{\mathrm{intr}}(m)}\right\rfloor,
\]

но равенство

\[
a_{\mathrm{intr}}(m)=\frac{m}{r_{\mathrm{intr}}(m)}
\]

**не разрешено** без отдельной theorem о tooth-alignment. Обычно имеется только bracket

\[
\frac{m}{r_{\mathrm{intr}}(m)+1}
<
a_{\mathrm{intr}}(m)
\le
\frac{m}{r_{\mathrm{intr}}(m)}.
\]

`[ABSTRACT][PAPER]`

Дискриминатор перехода:

\[
\boxed{
\Gamma_m(A)
:=
\operatorname*{ess\,inf}_{a\in[A,m]}
\mathscr D_m(a).
}
\]

Тогда:

- PASS Supplier A только из \(\Gamma_m(4/3)\ge0\);
- KILL только из certified interval \(J\subset[4/3,m]\) положительной меры с \(U(\mathscr D_m|_J)<0\);
- \(0\in[L,U]\) означает `ZERO_CONSISTENT_DISCRIMINATOR`, не PASS и не KILL.

`[COFINAL_FAMILY][CONDITIONAL]`

### 4. \(\Psi_m\)-positivity остаётся разрешённым достаточным маршрутом

Доказательство

\[
\Psi_m(t)\ge0,
\qquad
t\in\left[\frac4{3m},1\right],
\]

немедленно даёт \(\mathscr S_m(a)\ge0\) на \(a\ge4/3\). Но его провал не убивает Supplier A: 034 уже зафиксировал exact P3 trap, где \(\Psi(t)=t^2-\tfrac13\) меняет знак, а sampled tooth functional остаётся положительным. fileciteturn18file0L126-L131 `[ABSTRACT][PAPER]`

### 5. Решение по 036

\[
\boxed{
\texttt{036}
\ \longrightarrow\
\texttt{FINITE\_SUPPLIER\_A\_GREEN\_ENGINE\_REHEARSAL}
}
\]

036 **не является самостоятельным critical-path goal** и не исполняется в текущей формулировке с первичным verdict `FULL_WINDOW_TOOTH_NONNEGATIVITY_PROVED`. `[FINITE_CELL][PAPER]`

Внутри 038 из него потребляется только rehearsal harness:

- exact 031 alias;
- forcing orientation;
- нижний boundary zero;
- живой terminal boundary;
- 179 controls и 62 zero-compatible cases;
- sign-flip и terminal-drop plants.

Даже полный успех rehearsal не является premise кофинального theorem. `[FINITE_CELL][CONDITIONAL]`

### Зарегистрированные прогнозы 038

```text
P038-1:
  031 identity потребует настоящего parametric-m lift;
  m=257 certificate не займёт cofinal quantifier.

P038-2:
  whole Green expression, включая terminal boundary,
  будет сильнее componentwise forcing-only sign check.

P038-3:
  a_intr(m) не окажется автоматически tooth-aligned;
  m/r_* допустим только как conservative tooth envelope.

P038-4:
  отрицательность Ψ_m где-либо не убьёт Supplier A;
  sampled-response/Jacobi route останется жизнеспособным.

P038-5:
  без нового CofinalOuterLobeGate доказательная область
  останется полной [4/3,m], а не [4/3,sqrt(m)].
```

`[COFINAL_FAMILY][CONDITIONAL]`

**Самый дешёвый решающий тест:** извлечь из source 031 exact \(\mathscr D_m(a)\), заменить все hard-coded \(257\) на symbolic \(m\) и проверить, остаётся ли exact Green identity верной до любой sign estimate. `[COFINAL_FAMILY][CONDITIONAL]`

## STRONGEST ATTACK

Главное возражение:

> Вы пытаетесь получить кофинальный sign theorem из двух конечных импортов: Jacobi 031 при \(m=257\) и outer-lobe 027 при трёх \(m\). Одновременно вы называете переход \(a_\ast=m/r_\ast\), хотя sampled response может менять знак внутри одной полосы.

Это реальный тройной finite-to-cofinal/type mismatch. `[COFINAL_FAMILY][PAPER]`

Последняя часть убивается exact P3-family. Возьмём

\[
\Psi(t)=t^2-\frac13,
\qquad
\int_0^1\Psi(t)\,dt=0.
\]

На полосе с фиксированным \(r\):

\[
S_r(z)
=
\sum_{n=1}^{r}
\left((nz)^2-\frac13\right).
\]

На левом и правом краях полосы:

\[
S_r\!\left(\frac1{r+1}\right)
=
-\frac{r}{6(r+1)}
<0,
\]

\[
S_r\!\left(\frac1r\right)
=
\frac{3r+1}{6r}
>0.
\]

Следовательно, по непрерывности точный нуль лежит **строго внутри**

\[
\left(\frac1{r+1},\frac1r\right).
\]

То есть transition sampled response не обязан лежать на tooth \(z=1/r\), а scaled transition не обязан иметь вид \(m/r\). `[ABSTRACT][PAPER]`

Слабейший ремонт:

1. сначала определить \(a_{\mathrm{intr}}(m)\) через a.e. sampled-response sign;
2. отдельно доказать parametric Jacobi identity;
3. либо доказать Jacobi sign на полном \([4/3,m]\), либо добавить настоящий cofinal outer-lobe theorem;
4. считать \(m/r\) только tooth-envelope, пока alignment theorem не доказан.

## CODEX DIRECTIVE

```text
TARGET:
  038_ScaledOuterSignBarrierFourThirds

PRIMARY THEOREM:
  scaledOuterSignBarrierFourThirds

ROUTE STATUS:
  CHALLENGER / NOT_RH
  BUS_010_VOID
  no STATE promotion
  scope = COFINAL_FAMILY

FINAL STATEMENT:
  For the source-locked admissible cofinal family M,

    ∀ m ∈ M,
      S_scaled_m(a) ≥ 0
      for Lebesgue-a.e. a ∈ [4/3, m].

  Here:
    lambda_m = sqrt(m)
    z = a/m
    u = a/lambda_m
    r_m(a) = floor(m/a)

    S_scaled_m(a)
      = sum_{n=1}^{r_m(a)} Psi_m(n*a/m)

  off teeth, with the source midpoint/star convention on teeth.

ACCEPTANCE MODES — EXACTLY TWO:

  MODE FULL:
    prove the Jacobi discriminator sign on [4/3, m].
    Do not use 027.

  MODE SPLIT:
    prove the Jacobi discriminator sign on [4/3, sqrt(m)]
    AND prove a separate theorem

      cofinalOuterLobeGate :
        S_scaled_m(a) ≥ 0 a.e. on [sqrt(m), m]

    for every m ∈ M.

  The finite 027 theorem for m ∈ {13,53,257}
  cannot occupy cofinalOuterLobeGate.

────────────────────────────────────────
STEP 0 — SOURCE AND OBJECT LOCK
────────────────────────────────────────

Required sources:
  docs/routeB_bus/031_priority_band_positive_part.answer.md
  docs/routeB_bus/027_hlambda_outer_lobe_gate.answer.md
  docs/routeB_bus/034_cofinal_scaled_edge_sliver_moment.answer.md
  docs/routeB_bus/035_edge_sliver_materialization.answer.md
  docs/routeB_bus/PROSHKA_033_AND_MUNTZ_POLE_SUBTRACTED_v2.md
  docs/routeB_bus/PROSHKA_034_EDGE_SLIVER_CONTRACT.md
  exact 031 generator/certificate/checker pair
  exact Psi_m / delta_q coefficient source

Verify all source hashes against MANIFEST before proof work.

Prove or stop on the exact scaled crosswalk:

  E_star(h_{lambda_m}, a/lambda_m)
    = -C_m * sqrt(a) / lambda_m^(3/2) * S_scaled_m(a)

with C_m > 0.

Failure:
  SCALED_EDGE_OBJECT_MISMATCH

────────────────────────────────────────
STEP 1 — PARAMETRIC JACOBI LIFT
────────────────────────────────────────

The published 031 result has finite scope m=257.
Do not import it as a cofinal theorem.

Construct the exact parametric theorem:

  parametricScaledJacobiProfileIdentity :
    ∀ m ∈ M, for a.e. admissible a,

      S_scaled_m(a)
        = ((Theta4_m - Theta0_m)/2) * D_m(a)

with:

  Theta4_m - Theta0_m > 0;

  D_m(a) extracted from the exact 031 Green identity;

  lower boundary term retained and proved zero only from
    a_minus_one = 0
    and
    delta_0 = 0;

  terminal boundary term retained live;

  forcing term, terminal term and normalization written in one
  whole-expression identity.

Do not define D_m by the desired sign.

Failure codes:
  SCALED_JACOBI_COFINAL_LIFT_GAP
  JACOBI_DISCRIMINATOR_OBJECT_MISMATCH
  JACOBI_TERMINAL_BOUNDARY_GAP

────────────────────────────────────────
STEP 2 — SIGN THEOREM
────────────────────────────────────────

Primary jump-target:

  MODE FULL:
    D_m(a) ≥ 0 a.e. on [4/3, m].

  MODE SPLIT:
    D_m(a) ≥ 0 a.e. on [4/3, sqrt(m)]
    plus cofinalOuterLobeGate.

The dual multiplier Y_{m,a} must be fixed by a source-locked
adjoint/Green condition before inspecting the resulting sign.

Forbidden:
  choosing Y or -Y after seeing the sign;
  assuming D_m ≥ 0 to prove forcing sign;
  dropping the terminal boundary term;
  separately bounding terms if cancellation is required.

Failure codes:
  JACOBI_FORCING_SIGN_GAP
  JACOBI_CIRCULAR_ORIENTATION
  ZERO_CONSISTENT_DISCRIMINATOR

PASS direction:
  only from a lower envelope L(D_m) ≥ 0 on the complete domain.

KILL direction:
  only from an admissible interval J of positive measure with
  an upper envelope U(D_m|J) < 0.

Failure of a sufficient estimate is not a KILL.

────────────────────────────────────────
STEP 3 — INTRINSIC TRANSITION OBJECT
────────────────────────────────────────

Define:

  a_intrinsic(m)
    = inf { A ∈ [1,m] :
            S_scaled_m(a) ≥ 0 a.e. on [A,m] }.

The theorem target is:

  a_intrinsic(m) ≤ 4/3.

If an index is useful, define only:

  r_intrinsic(m) = floor(m / a_intrinsic(m)).

Do not assert:

  a_intrinsic(m) = m / r_intrinsic(m)

without a separate transition-at-tooth theorem.

Required discriminator:

  Gamma_m(A)
    = essInf_{a ∈ [A,m]} D_m(a).

Required planted violation:
  Psi(t) = t^2 - 1/3.

For fixed r verify exactly:

  S_r(1/(r+1)) = -r/(6(r+1)) < 0
  S_r(1/r)     = (3r+1)/(6r) > 0.

Therefore the response zero may lie strictly inside one band.
A tooth-aligned transition definition must be rejected.

Failure codes:
  INTRINSIC_TRANSITION_DEFINITION_GAP
  INTRINSIC_TRANSITION_ALIGNMENT_UNPROVED
  TRANSITION_OBJECT_CERTIFICATE_CONTAMINATED

────────────────────────────────────────
STEP 4 — PERMITTED PSI ROUTE
────────────────────────────────────────

Permitted stronger route:

  Psi_m(t) ≥ 0 for t ∈ [4/(3m),1]
    ⇒ S_scaled_m(a) ≥ 0 for a ≥ 4/3.

Its failure returns only:

  PSI_SUFFICIENT_ROUTE_INCONCLUSIVE

It must never return:
  SCALED_OUTER_SIGN_BARRIER_FOUR_THIRDS_KILLED.

Run the exact P3 trap to enforce the direction semantics.

────────────────────────────────────────
STEP 5 — 036 FINITE REHEARSAL
────────────────────────────────────────

Do not execute 036 as an independent bus transaction.

Absorb its engine as:

  finiteSupplierAGreenEngineRehearsal_m257

Purpose:
  validate the exact Green machinery on the finite skeleton:
    179 existing positive controls;
    62 zero-compatible teeth;
    forcing orientation;
    lower boundary zero;
    live terminal boundary;
    source hashes and recurrence.

The rehearsal result is diagnostic only.
It must not be a premise of the cofinal theorem.

Secondary flag on success:
  SUPPLIER_A_REHEARSAL_036_PASSED

Failure:
  SUPPLIER_A_REHEARSAL_ENGINE_MISMATCH

────────────────────────────────────────
MANDATORY PLANTS
────────────────────────────────────────

P038-1 PARAMETRIC_SCOPE:
  replace symbolic m by the m=257 certificate inside the cofinal theorem;
  dependency/scope checker must reject.

P038-2 SCALED_COORDINATE:
  replace a=m*z=lambda*u by a=r/lambda;
  object-lock checker must reject.

P038-3 OUTER_LOBE_SCOPE:
  consume 027 as a cofinal theorem;
  checker must return OUTER_LOBE_SCOPE_PROMOTION.

P038-4 TERMINAL_DROP:
  replace the live terminal Green term by zero;
  exact identity checker must fail.

P038-5 LOWER_BOUNDARY:
  mutate delta_0 or a_minus_one away from zero;
  lower boundary must become visibly nonzero.

P038-6 DUAL_ORIENTATION:
  replace Y by -Y after source lock;
  forcing/terminal identity and sign ledger must detect the change.

P038-7 PSI_TRAP_AND_INTERIOR_TRANSITION:
  Psi=t^2-1/3 must:
    change sign;
    have zero mass;
    preserve the exact P3 sampled semantics;
    exhibit an interior band transition.
  Psi negativity must not kill Supplier A.

P038-8 CERTIFICATE_CONTAMINATION:
  inject rho_033, q=700, tau_response, box width or subdivision
  into a_intrinsic;
  dependency audit must reject.

P038-9 COVERAGE:
  delete one open band, the crossing interval at 4/3,
  or the sqrt(m) junction in MODE SPLIT;
  complete-domain checker must reject.

P038-10 FINITE_TO_COFINAL:
  use m=257 rehearsal or teeth certificate as a ∀m premise;
  scope checker must reject.

P038-11 DIRECTION:
  a zero-straddling interval must return INCONCLUSIVE;
  only L≥0 returns PASS;
  only U<0 on positive-measure J returns KILL.

────────────────────────────────────────
PRIMARY VERDICT — EXACTLY ONE
────────────────────────────────────────

SCALED_OUTER_SIGN_BARRIER_FOUR_THIRDS_PROVED

  iff the full cofinal a.e. statement is proved by MODE FULL
  or MODE SPLIT with a proved cofinalOuterLobeGate.

SCALED_OUTER_SIGN_BARRIER_FOUR_THIRDS_KILLED

  iff a certified admissible cofinal instance contains a
  positive-measure interval J ⊂ [4/3,m] with U(D_m|J) < 0.

SCALED_OUTER_SIGN_BARRIER_FOUR_THIRDS_INCONCLUSIVE

  otherwise.

Secondary flags:
  PARAMETRIC_SCALED_JACOBI_PROFILE_IDENTITY_PROVED
  COFINAL_OUTER_LOBE_GATE_PROVED
  PSI_LAST_ZERO_SUFFICIENT_BARRIER_PROVED
  INTRINSIC_TRANSITION_OBJECT_LOCKED
  SUPPLIER_A_REHEARSAL_036_PASSED

Stop codes:
  SOURCE_HASH_MISMATCH
  SCALED_EDGE_OBJECT_MISMATCH
  SCALED_JACOBI_COFINAL_LIFT_GAP
  JACOBI_DISCRIMINATOR_OBJECT_MISMATCH
  JACOBI_TERMINAL_BOUNDARY_GAP
  JACOBI_FORCING_SIGN_GAP
  JACOBI_CIRCULAR_ORIENTATION
  COFINAL_OUTER_LOBE_UNPROVED
  OUTER_LOBE_SCOPE_PROMOTION
  INTRINSIC_TRANSITION_DEFINITION_GAP
  INTRINSIC_TRANSITION_ALIGNMENT_UNPROVED
  TRANSITION_OBJECT_CERTIFICATE_CONTAMINATED
  COVERAGE_INCOMPLETE
  FINITE_TO_COFINAL_PROMOTION
  ZERO_CONSISTENT_DISCRIMINATOR
  PLANT_NOT_DETECTED
  LEAN_BUILD_FAIL

────────────────────────────────────────
FORBIDDEN SHORTCUTS
────────────────────────────────────────

No new K/depth/precision ladder.
No enumeration over more m-cells.
No 031 finite theorem occupying a cofinal quantifier.
No 027 finite theorem occupying COFINAL_OUTER_LOBE.
No r_cert or epsilon_r as intrinsic transition definitions.
No a_intrinsic=m/r assertion without an alignment theorem.
No tooth sign inside the Lebesgue budget.
No 036 result as a cofinal premise.
No after-the-fact dual orientation.
No dropped terminal boundary.
No failure-of-Psi-positivity kill.
No S1, RH, route promotion, STATE change or Bus 010.
No new sorry/admit/axiom/fake constant/native_decide proof.

────────────────────────────────────────
VALIDATION GATE
────────────────────────────────────────

1. Verify all source SHA-256 values against MANIFEST.
2. Prove complete symbolic domain coverage, including:
     4/3 endpoint;
     every open floor-band;
     all teeth as a finite null set;
     sqrt(m) junction in MODE SPLIT;
     endpoint m.
3. Run all P038 plants and require every plant to fire.
4. Run:
     lake env lean <touched-file>
     lake build
     grep -R "sorry\|admit\|axiom\|native_decide" <touched paths>
     #print axioms scaledOuterSignBarrierFourThirds
5. Emit a scope/verifier ledger for every theorem.
6. Confirm 036 rehearsal is absent from the dependency tree
   of scaledOuterSignBarrierFourThirds.
7. Confirm Route B remains CHALLENGER / NOT_RH and BUS_010_VOID.

If INCONCLUSIVE:
  do not increase precision or enumerate more cells.

  Return both candidate re-representations:

  R1 JACOBI_CONTINUANT_DETERMINANT
     Rewrite the whole Green discriminator as a continuant /
     principal-minor or transfer-matrix expression.
     kill-power: 5
     cost: 3

  R2 DIRECT_SAMPLED_RESPONSE_GENERATING_FUNCTION
     Rewrite S_scaled_m directly through a source-locked generating
     or Euler–Maclaurin identity with coupled endpoint remainder.
     kill-power: 4
     cost: 3

  Name Gamma_m(4/3) as the discriminator and report the exact
  zero-consistent term preventing a verdict.
```

## META CLOSEOUT

**Что стало меньше?**  
`ScaledOuterSignBarrierFourThirds` теперь распался не на неопределённую «положительность снаружи», а на:

\[
\boxed{
\texttt{ParametricScaledJacobiProfileIdentity}
+
\texttt{ParametricScaledJacobiDiscriminatorNonneg}
}
\]

и ровно один domain fork: full interval либо inner interval + настоящий cofinal outer-lobe. `[COFINAL_FAMILY][CONDITIONAL]`

**Что убито?**

- P034-1 / P035-2 radius-driven prediction; `[FINITE_CELL][ARB_INTERVAL]`
- автоматическое равенство \(a_\ast=m/r_\ast\); `[ABSTRACT][PAPER]`
- использование 031 или 027 как готовых cofinal imports; `[COFINAL_FAMILY][PAPER]`
- standalone load-bearing роль tooth goal 036. `[FINITE_CELL][PAPER]`

**Что нельзя пробовать снова?**

- выводить intrinsic cutoff из \(\varepsilon_r\);
- считать стабильность \(r_{\rm cert}=195\) доказательством exact transition;
- убивать Supplier A провалом \(\Psi_m\ge0\);
- занулять terminal Green term;
- заменять кофинальную область тремя finite cells.

**Текущий smallest named gap:**

\[
\boxed{
\texttt{ParametricScaledJacobiDiscriminatorNonneg}
}
\]

при предварительном object lock

\[
\boxed{
\texttt{ParametricScaledJacobiProfileIdentity}.
}
\]

`[COFINAL_FAMILY][CONDITIONAL]`

**Следующий самый дешёвый решающий тест:** generic-\(m\) replay exact 031 identity с живым terminal term, до любой sign estimate и до любой работы с 036. `[COFINAL_FAMILY][CONDITIONAL]`

**Fate of registered predictions:** P034-1 refuted; P034-2 strengthened but open; P034-3 partial; P034-4 half-confirmed with two-wall correction; P034-5 confirmed; P035-1 and P035-3 confirmed; P035-2 missed. Никакой прогноз не переписан задним числом.

```yaml
iteration:
  target: ScaledOuterSignBarrierFourThirds
  status: OPEN
  failed_strategy: radius_driven_certificate_cutoff_and_tooth_aligned_transition
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: ParametricScaledJacobiDiscriminatorNonneg
  invariant_learned: cofinal sign requires parametric identity, complete domain coverage, and live terminal boundary
  forbidden_future_move: promote m257 Jacobi or finite 027 to a cofinal theorem
  next_decisive_test: generic_m_exact_Jacobi_identity_replay_before_sign
  progress_class: FALSIFICATION_PROGRESS_AND_REPRESENTATION_PROGRESS
  route_score: 5
```