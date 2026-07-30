# STATUS: OPEN — 034 SCALED EDGE-SLIVER REDUCTION CHOSEN

```yaml
PRIMARY_STATUS: OPEN
ROUTE_STATE: CHALLENGER_NOT_RH
SOURCE_MIRROR: 7d86020a01f1923b61eaef17c480b1cf752b2246
SOURCE_COMMIT: fdfec3b89d72eba1e9132e79def01719e9d7ca78

TRANSACTION_033:
  primary: FULL_WINDOW_POSITIVE_PART_BUDGET_PROVED
  secondary: TOOTH_SIGN_INCONCLUSIVE
  scope: FINITE_CELL
  verifier: ARB_INTERVAL_PLUS_EXACT_RATIONAL

CHOSEN_COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
NEXT_TRANSACTION: 034_COFINAL_SCALED_EDGE_SLIVER_MOMENT
CURRENT_SMALLEST_GAP: CofinalFullWindowPositivePartMomentBound

CHOSEN_ROUTE:
  name: SCALED_EDGE_RESPONSE_PLUS_BOUNDARY_CELL
  kill_power: 5
  cost: 3

DEFERRED_ROUTE:
  name: FULL_JACOBI_D_R_SIGN_FACTORIZATION
  kill_power: 5
  cost: 5
  role: fallback_sign_supplier

REJECTED_ROUTES:
  - repeat_full_window_enumeration_over_more_cells
  - define_intrinsic_cutoff_by_epsilon_r_positive
  - infer_cutoff_from_a_zero_of_Psi_without_a_sampling_theorem
  - assemble_S1_from_finite_cell_033

REGISTERED_EDGE_CONSTANT:
  A_edge: 4/3
  status: CANDIDATE_PRECOMMITTED_NOT_THEOREM

FORBIDDEN:
  - treat_r195_as_an_intrinsic_zero
  - finite_cell_to_cofinal_promotion
  - new_K_or_precision_ladder
  - new_full_cell_enumeration
  - use_tooth_values_inside_Lebesgue_budget
  - claim_pointwise_DualTheta_from_positive_part_budget
```

Запрошенный nested bootstrap-path в GitHub отсутствует; использована каноническая зеркальная копия `docs/routeB_bus/PROSHKA_SYSTEM_PROMPT_v2.md`.

## Судейская поправка: `r=195` пока не математический cutoff

033 строго доказал finite-cell профиль:

```text
epsilon_r > 0 exactly for r=195..256
tooth lower envelope >= 0 exactly for r=17..195
zero-compatible teeth exactly r=196..257
```

и закрыл полный положительный бюджет на (m=257).

Но (\varepsilon_r) определяется как

[
\varepsilon_r=\max(0,-L_r),
]

где (L_r) — center minimum минус frozen outward radius. Финальный remainder 030 равен

[
2.24186222683824266\cdot10^{-237},
]

а максимальный (\varepsilon_r) в 033 равен

[
2.241863561007243437\cdot10^{-237}.
]

Они отличаются только на (1.33\cdot10^{-243}). Это сильный признак, что `195` — прежде всего **certificate-resolution cutoff**: положительный center margin провалился под фиксированный remainder.

Поэтому навсегда разводим:

[
r_{\rm cert}(m;\rho)
:=
\min{r:\varepsilon_{m,r}(\rho)>0},
]

который зависит от radius (\rho), и intrinsic cutoff, определённый точным знаком полной суммы.

------

# Правильная scaled-координата

Пусть

[
\lambda_m=\sqrt m,
\qquad
z=\frac{u}{\lambda_m},
\qquad
\boxed{a:=mz=\lambda_m u}.
]

Нижняя граница окна (u=\lambda_m^{-1}) становится (a=1). На tooth (z=1/r):

[
a=\frac mr,
\qquad
u=\frac{\lambda_m}{r}.
]

Для неточечного (a) определяем

[
r_m(a)=\left\lfloor\frac ma\right\rfloor,
]

# [ \boxed{ \mathscr S_m(a)

\sum_{n=1}^{r_m(a)}
\Psi_m!\left(\frac{na}{m}\right).
}
]

На tooth (a=m/r):

# [ \boxed{ \mathscr S_m^\star(m/r)

\sum_{n=1}^{r-1}\Psi_m(n/r)
+\frac12\Psi_m(1).
}
]

031 уже запер точный (S\leftrightarrow E_\star) crosswalk и отдельную tooth-alias identity.

В scaled-переменной:

# [ \boxed{ E_\star!\left(h_{\lambda_m},\frac a{\lambda_m}\right)

-C_m\frac{\sqrt a}{\lambda_m^{3/2}},
\mathscr S_m(a),
}
]

где

[
C_m=
\frac{I_{0,m}I_{4,m}}
{\sqrt{I_{0,m}^2+I_{4,m}^2}}>0.
]

Поэтому вне teeth:

[
E_\star>0
\iff
\mathscr S_m<0.
]

------

# Intrinsic cutoff и параметризация (r_*(m))

Определяем не через certificate uncertainty, а через exact response:

# [ \boxed{ A_m^{\rm intr}

\inf\left{
A\ge1:
\mathscr S_m(a)\ge0
\text{ a.e. на }[A,m]
\right}.
}
]

Тогда

# [ \boxed{ r_*(m)

\left\lfloor\frac{m}{A_m^{\rm intr}}\right\rfloor.
}
]

Для полной open band нужен guard

[
\frac{m}{r+1}\ge A_m^{\rm intr};
]

crossing band всегда остаётся внутри edge budget.

## Pre-registered law

В клетке (m=257):

[
\frac{257}{195}=1.3179487\ldots<\frac43.
]

Поэтому фиксируем до теста консервативный кандидат:

[
\boxed{A_{\rm edge}=\frac43}.
]

Он даёт:

[
r_0(m)\approx\frac{3m}{4},
]

и edge sliver:

[
\boxed{
u\in
\left[
\frac1{\lambda_m},
\frac{4}{3\lambda_m}
\right].
}
]

Это не fit после результата: (4/3) замораживается контрактом 034.

------

# Связь с нулями (\Psi_m)

Последний нуль (\Psi_m) — только **сильный достаточный механизм**.

Если существует (\tau_m), для которой

[
\Psi_m(t)\ge0
\qquad(\tau_m\le t\le1),
]

то при (z\ge\tau_m) все активные (nz) лежат в положительной области, поэтому

[
S_m(z)\ge0.
]

Тогда можно взять

[
A_m=m\tau_m,
\qquad
r_*(m)=\lfloor\tau_m^{-1}\rfloor.
]

Но обратное неверно: sampled sum может быть неотрицательной благодаря cancellation, даже когда (\Psi_m) меняет знак. Поэтому основной intrinsic объект — zero/sign transition функции

[
a\longmapsto\mathscr S_m(a),
]

а не самой (\Psi_m).

Через доказанное в 031 Jacobi divided-difference identity допустимо записать

# [ \mathscr S_m(a)

\frac{\Theta_{4,m}-\Theta_{0,m}}2,
\mathscr D_m(a),
]

с полным Green boundary ledger. Так как spectral difference положительна, sign определяется (\mathscr D_m). Jacobi-route в 033 не понадобился, но остаётся fallback-поставщиком **параметрического** sign theorem.

------

# Главная theorem-форма 034

## `CofinalScaledEdgeSliverMomentBound`

Для (0\le\sigma<1/2):

[
\Delta_{m,\sigma}^{+}
:=
\int_{\lambda_m^{-1}}^{\lambda_m}
\max(E_\star(h_{\lambda_m},u),0)
u^{-\sigma}\frac{du}{u}.
]

Пусть (A_m\ge1) удовлетворяет scaled outer sign:

[
\boxed{
E_\star(h_{\lambda_m},u)\le0
\quad\text{a.e. на}\quad
[A_m/\lambda_m,\lambda_m].
}
\tag{S}
]

Пусть (K_m) — exact Lipschitz constant для (h_{\lambda_m}) на
([0,\lambda_m)), и

[
B_m
:=
K_m\lambda_m+
(|h_{\lambda_m}(0)|+K_m\lambda_m)
+|h_{\lambda_m}(\lambda_m)|.
]

Доказанный в Lean boundary-cell bridge даёт

[
|E_\star(h_{\lambda_m},u)|
\le B_m\sqrt u,
\qquad0<u<1.
]

Именно эта explicit constant заперта в T1–T3.

Отсюда:

[
\boxed{
\frac{\Delta_{m,\sigma}^{+}}{C_m}
\le
\frac{B_m}{C_m}
\lambda_m^{\sigma-\frac12}
\frac{
A_m^{\frac12-\sigma}-1
}{
\frac12-\sigma
}.
}
\tag{034-edge}
]

Следовательно, **слабейший cofinal supplier**:

[
\boxed{
\forall\sigma<\frac12,\quad
\sup_{m\in\mathcal M}
\left[
\frac{B_m}{C_m}
\lambda_m^{\sigma-\frac12}
\frac{
A_m^{\frac12-\sigma}-1
}{
\frac12-\sigma
}
\right]<\infty.
}
\tag{034-product}
]

Он немедленно даёт:

[
\boxed{
\forall\sigma<\frac12,\qquad
\sup_{m\in\mathcal M}
\frac{\Delta_{m,\sigma}^{+}}{C_m}<\infty.
}
]

Это и есть `CofinalFullWindowPositivePartMomentBound`.

## Простой достаточный corollary

Если кофинально:

[
A_m\le\frac43
]

и

[
B_m\le B_0C_m,
]

то

[
\boxed{
\frac{\Delta_{m,\sigma}^{+}}{C_m}
\le
B_0
\frac{
(4/3)^{\frac12-\sigma}-1
}{
\frac12-\sigma
}.
}
]

Провал одной из этих двух достаточных оценок не убивает `(034-product)`.

------

# K1-планты

```text
P1  radius mutation:
    center polynomials fixed; outward radius ×1/2 and ×2.
    r_cert should move if resolution-driven.

P2  intrinsic-object lock:
    A_intr must not depend on q=700, tau_response,
    box width, Bernstein subdivision.

P3  Psi-root trap:
    Psi=t^2-1/3 has a pointwise zero and zero mass,
    but S*_r=(r+1)/(6r) != 0.

P4  scaled-variable mutation:
    a=mz=lambda*u must pass;
    a=r/lambda must fail.

P5  crossing-band deletion:
    omit the band intersecting a=4/3; coverage must fail.

P6  tooth mutation:
    Lebesgue budget unchanged; pointwise tooth ledger changes.

P7  sign flip:
    Psi -> -Psi swaps positive/negative leakage.

P8  Jacobian:
    omit du/u, sqrt(u), or u^(-sigma); closed form changes.

P9  scalar rescaling:
    h -> c h scales Delta+, B_m, C_m equally;
    normalized theorem remains invariant.

P10 finite-to-cofinal guard:
    m=257 certificate cannot occupy forall m.

P11 direction semantics:
    failure of A_m<=4/3 or B_m<=B0*C_m
    is not a kill of the cofinal moment theorem.
```

------

# PRIMARY VERDICT CODES

Ровно один:

```text
COFINAL_EDGE_SLIVER_MOMENT_BOUND_PROVED
```

если scaled sign, product bound и reduction доказаны на cofinal family;

```text
COFINAL_EDGE_SLIVER_REDUCTION_PROVED
```

если формула `(034-edge)` закрыта, но source supplier остаётся точно названным;

```text
SCALED_OUTER_SIGN_BARRIER_KILLED
```

только если сертифицирован строгий интервал

[
\mathscr S_m(a)<0,\qquad a\ge4/3,
]

в допустимой кофинальной семье;

```text
RELATIVE_BOUNDARY_CELL_PRODUCT_GAP
```

если sign supplier доказан, но `(034-product)` открыт;

```text
SCALED_EDGE_OBJECT_MISMATCH
```

если (z,u,a,\Psi_m,C_m) не воспроизводят exact crosswalk 031.

Secondary flags:

```text
CERTIFICATE_CUTOFF_RADIUS_DRIVEN
SCALED_JACOBI_PROFILE_IDENTITY_PROVED
PSI_LAST_ZERO_SUFFICIENT_BARRIER_PROVED
A_EDGE_FOUR_THIRDS_ACCEPTED
TOOTH_LEDGER_IRRELEVANT_TO_LEBESGUE_CONSUMER
```

------

# CODEX DIRECTIVE

```text
TARGET:
034_CofinalScaledEdgeSliverMoment

PRIMARY THEOREM:
cofinalFullWindowPositivePartMoment_of_scaledEdge

STEP 0 — OBJECT LOCK:
  lambda_m = sqrt(m)
  z = u/lambda_m
  a = m*z = lambda_m*u

  E_star(h_m,a/lambda_m)
    = -C_m * sqrt(a)/lambda_m^(3/2) * S_scaled_m(a)

No computation before this is source-locked.

STEP 1 — ABSTRACT REDUCTION:
Prove (034-edge) and its product-condition corollary.
Consume the already Lean-proved RiemannBoundaryCellBridge.

STEP 2 — SOURCE SUPPLIERS:

A. ScaledOuterSignBarrierFourThirds:
     S_scaled_m(a) >= 0 a.e. for 4/3 <= a <= m.

   Primary route:
     031 Jacobi divided-difference in scaled variable a.
     Prove sign of the normalized discriminator.
     Do not enumerate r.

   Permitted stronger route:
     Psi_m(t) >= 0 for t >= 4/(3m).

B. RelativeBoundaryCellProductBound:
     prove the exact all-sigma condition (034-product).

   Do not prove stronger separate bounds unless needed.

STEP 3 — M257 REGRESSION:
Check only that A=4/3 is conservative relative to 033.
Do not regenerate 241 bands.
Do not add another finite cell.

FORBIDDEN:
  no new K/depth/precision;
  no full-window enumeration;
  no r_* definition from epsilon_r;
  no 022 diagnostic as proof;
  no tooth signs inside the integral;
  no pointwise DualTheta claim;
  no finite-cell to cofinal promotion;
  no RH claim;
  STATE untouched;
  Bus 010 void.

VALIDATION:
  source hashes;
  P1-P11;
  lake env lean <touched-file>;
  lake build;
  grep sorry/admit/axiom/native_decide;
  #print axioms reduction theorem;
  scope/verifier ledger.
```

------

# REGISTERED PREDICTIONS

```text
P034-1:
  r_cert=195 is predominantly radius-driven,
  not an intrinsic exact cutoff.

P034-2:
  intrinsic transition is governed by
  a=mz=lambda*u sampled response,
  not a bare zero of Psi_m.

P034-3:
  conservative A_edge=4/3 survives cofinal source audit.

P034-4:
  abstract reduction closes;
  likely remaining wall is the cofinal product bound,
  not band coverage.

P034-5:
  tooth sign remains inconclusive and irrelevant to
  the Lebesgue moment.
```

## META CLOSEOUT

- **Стало меньше:** cofinal positive-part problem → один scaled sign barrier + один product ledger.
- **Убито:** `r=195` как intrinsic theorem object; ещё одна finite-cell ladder; прямой S1-export из 033.
- **Не повторять:** cutoff через uncertainty или sampled-sign из одного нуля (\Psi_m).
- **Smallest gap:** `ScaledOuterSignBarrierFourThirds`, затем `RelativeBoundaryCellProductBound`.
- **Progress class:** `REPRESENTATION_PROGRESS`.
- **Route score:** `5/5`.

[Скачать полный контракт 034](sandbox:/mnt/data/PROSHKA_034_COFINAL_SCALED_EDGE_SLIVER_v2.md)