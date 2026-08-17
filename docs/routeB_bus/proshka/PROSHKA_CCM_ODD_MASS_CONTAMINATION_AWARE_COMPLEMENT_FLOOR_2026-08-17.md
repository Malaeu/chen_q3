# STATUS: CONDITIONAL — EXACT PARITY IS NOT REQUIRED; ODD CONTAMINATION ADMITS AN EXPLICIT FLOOR LOSS

```yaml
PRIMARY: REPLACE_EXACT_ROW_EVENNESS_GATE_WITH_ODD_MASS_RATE_AND_COUPLING_LOSS
PRIMARY_COUNT: 1

SOURCE_PIN:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  COMMIT: f733402b918244ccfd9051b7efa830d63b44c8a3
  DATE: 2026-08-17

QUESTION:
  EXACT_QPERP_INVARIANT_SPLIT_REQUIRED: false
  EXACT_MIN_EQUALITY_WITHOUT_ERROR_REQUIRED_EXACT_PARITY: true
  APPROXIMATE_SPLIT_WITH_EXPLICIT_LOSS: true

DISK_FACTS:
  ODD_MASS_REFLECTION_IDENTITY: PROVED
  PHYSICAL_ERROR_UPPER_BOUND_REFLECTED_COEFFICIENTS: PROVED
  PHYSICAL_ERROR_UPPER_BOUND_EVEN_COEFFICIENTS: PROVED
  EXACT_SOURCE_ROW_EVENNESS: NOT_PROVED
  ODD_MASS_ZERO_ATTAINABILITY: NOT_VERIFIED

QUANTITATIVE_RESULT:
  eta: sourceCCMComplexOddMass
  rho: norm_of_shifted_source_residual
  beta: min_even_odd_sector_floor
  beta_eff: beta*(1-eta)-((2*sqrt(eta)+eta)/sqrt(1-eta))*rho
  domain: 0 <= eta < 1
  exact_parity_special_case: eta=0

COFINAL_REQUIREMENT:
  sufficient_if_uniform_sector_floor:
    - eta_j_tends_to_zero
    - sqrt_eta_j_times_rho_j_tends_to_zero
  fixed_shift_variant_also_requires:
    - rayleigh_shift_error_j_tends_to_zero
  odd_mass_rate_alone_without_coupling_control: insufficient

PRE_GATE_SUPERSESSION:
  old: ExactSourceCCMComplexRowEvenness
  new: SourceCCMOddMassRateAndComplementFloorLoss
  exact_parity_role: OPTIONAL_ZERO_LOSS_SPECIAL_CASE

PROVENANCE:
  MYTHOS_2026_08_14:
    READ: true
    INDEPENDENT_CONFIRMATION: false
    ROLE: sector_split_and_fixed_shift_architecture_transmitted
  CURRENT_EXPLICIT_LOSS_DERIVATION:
    SOURCE_FILES_READ: true
    DERIVED_DIRECTLY_FROM_REFLECTION_GEOMETRY: true
    LEAN_FORMALIZED: false

ROUTE_STATE: CHALLENGER_NOT_RH
G1_STATUS: OPEN
G3_STATUS: OPEN
ROUTE_PROMOTION: false
RH_CLAIM: false
BUS_010: VOID
ARISTOTLE_AUTHORIZED: false

VERDICT_CODE: APPROXIMATE_PARITY_SUFFICES_ODD_MASS_ONLY_DOES_NOT
STOP_CODE: CONTAMINATION_TO_FLOOR_TRANSPORT_AND_COFINAL_RATE_OPEN
```

## 1. Прямой ответ

Точное разложение

\[
q^\perp=(\text{even}\cap q^\perp)\oplus\text{odd}
\]

и точное равенство оптимального floor

\[
\beta=\min(\beta_+,\beta_-)
\]

действительно требуют, чтобы trial row `q` был точно even. Причина проста: только тогда
rank-one projection

\[
Q=I-|q\rangle\langle q|
\]

коммутирует с reflection involution `J`.

Но **положительный full complement floor не требует exact parity**.

При малой odd mass пространство `q^\perp` является малым graph-возмущением точной
parity-суммы. Hermitian form остаётся снизу ограниченной с явной платой. В самой
экономной residual-only форме плата равна

\[
\boxed{
\beta_{\rm eff}
=
\beta(1-\eta)
-
\frac{2\sqrt\eta+\eta}{\sqrt{1-\eta}}\,\rho,
}
\]

где

\[
\eta=\|q_-\|^2=\texttt{sourceCCMComplexOddMass},
\qquad
\rho=\|(K-aI)q\|,
\qquad
\beta=\min(\beta_+,\beta_-).
\]

Если `beta_eff > 0`, получаем literal floor на **полном** `q^\perp`.

Следовательно, ответ на главный вопрос:

```text
exact parity:
  sufficient and gives zero loss;
  not necessary.

oddMass_j -> 0:
  useful and theorem-facing;
  must be combined with a coupling/residual budget.
```

Форма `min(beta+,beta-) - C*sqrt(epsilon_j)` является корректным грубым следствием при
uniform bound на residual/coupling. Более того, через Young absorption можно получить
`O(epsilon_j)` loss, если разрешено потратить фиксированную долю even-sector floor.

## 2. Что уже действительно стоит на диске

### 2.1 Exact odd-mass identity

Файл

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
D0PstarSourceCCMOddMassReflectionDefect.lean:112
```

содержит

```lean
sourceCCMComplexOddMass_eq_quarter_norm_reflectionDefect_sq
```

и доказывает точно

\[
\eta
=
\frac14\|q-Jq\|^2.
\]

Это не diagnostics-only identity. Оно точно идентифицирует геометрический параметр,
который измеряет угол source row к even sector.

### 2.2 First physical approximation receiver

Тот же файл, строка `:138`, содержит

```lean
sourceCCMComplexOddMass_le_quarter_norm_sub_sq_of_reflected_coefficients
```

и выводит

\[
\eta
\le
\frac14\|k_{m,N}-f\|^2
\]

из ambient supplier, чьи retained coefficients равны reflected source coefficients.
Комментарий файла правильно говорит: Bessel платит только за физическую ошибку
приближения. Source row не симметризуется вручную.

### 2.3 Non-circular even-packet receiver

Строка `:205` содержит

```lean
sourceCCMComplexOddMass_le_norm_sub_sq_of_even_coefficients
```

и выводит

\[
\eta\le\|k_{m,N}-f\|^2
\]

из ambient approximant с exact even retained coefficients. Комментарий прямо называет
этот theorem non-circular source-facing receiver.

Итак, поправка владельца точна:

```text
odd-mass measurer есть;
exact identity есть;
два source-facing upper suppliers есть.
```

Моя прежняя формулировка «есть измеритель, но нет rate» была неполной. Правильно:

```text
есть измеритель + два upper-bound receivers;
нет cofinal rate theorem;
нет transport theorem oddMass + sector floors -> full complement floor.
```

### 2.4 Exact parity theorem remains conditional

Файл

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
CCMProposition59SourceTrialFeshbachPreflight.lean:128
```

содержит

```lean
sourceCCMComplexRow_even_of_phaseRealification_even
```

только с supplied phase-realification и supplied even real row. Его собственный
комментарий говорит, что current D0Pstar contract не экспортирует нужный source theorem.

Поэтому exact row evenness не является текущим project fact.

## 3. Abstract quantitative theorem

### 3.1 Objects

Пусть `H` — конечномерное complex Hilbert space.

Пусть:

- `J` — unitary self-adjoint involution;
- `K` — Hermitian operator;
- `KJ=JK`;
- `q` — unit vector;
- `a` — real shift;
- `A=K-aI`.

Положим

\[
P_+=\frac{I+J}{2},
\qquad
P_-=\frac{I-J}{2},
\]

\[
q_+=P_+q,
\qquad
q_-=P_-q,
\qquad
\eta=\|q_-\|^2.
\]

Так как `q` unit,

\[
\|q_+\|^2=1-\eta.
\]

При `eta<1` определим exact even unit vector

\[
s=\sqrt{1-\eta},
\qquad
e=q_+/s.
\]

### 3.2 Sector hypotheses

Предположим:

\[
\langle y,Ay\rangle
\ge
\beta_+\|y\|^2
\]

для каждого even `y` с `y perp e`, и

\[
\langle z,Az\rangle
\ge
\beta_-\|z\|^2
\]

для каждого odd `z`.

Положим

\[
\beta=\min(\beta_+,\beta_-).
\]

Также положим

\[
\rho=\|Aq\|.
\]

### 3.3 Geometry of `q perp`

Возьмём `x perp q`. Разложим его uniquely:

\[
x=y+ce+z,
\]

где:

- `y` even;
- `y perp e`;
- `z` odd;
- `c` scalar.

Из `x perp q`:

\[
0=\langle q,x\rangle
=s\,c+\langle q_-,z\rangle.
\]

Следовательно,

\[
s^2|c|^2
\le
\eta\|z\|^2.
\]

Так как `s^2=1-eta`, получаем важную точную оценку:

\[
\boxed{|c|^2\le\eta\|x\|^2.}
\]

Поэтому

\[
\|y\|^2+\|z\|^2
=
\|x\|^2-|c|^2
\ge
(1-\eta)\|x\|^2.
\]

Это и есть quantitative replacement для exact invariant direct sum.

### 3.4 Residual controls the dangerous coupling

Так как `A` коммутирует с `J`, even и odd компоненты `Aq` ортогональны:

\[
Aq=sAe+Aq_-.
\]

Следовательно,

\[
\rho^2
=
\|Aq\|^2
=
s^2\|Ae\|^2+\|Aq_-\|^2,
\]

и

\[
\boxed{\|Ae\|\le\rho/s=\rho/\sqrt{1-\eta}.}
\]

Именно этот coupling scale отсутствует в утверждении «oddMass decay alone is enough».

### 3.5 Energy estimate

Parity commutation убивает even-odd cross terms. Поэтому

\[
\begin{aligned}
\langle x,Ax\rangle
={}&
\langle y,Ay\rangle
+
\langle z,Az\rangle\\
&+
2\operatorname{Re}\bigl(\overline c\langle e,Ay\rangle\bigr)
+
|c|^2\langle e,Ae\rangle.
\end{aligned}
\]

Sector floors дают

\[
\langle y,Ay\rangle+
\langle z,Az\rangle
\ge
\beta(1-\eta)\|x\|^2.
\]

Оставшиеся члены снизу ограничены:

\[
2\operatorname{Re}\bigl(\overline c\langle e,Ay\rangle\bigr)
+
|c|^2\langle e,Ae\rangle
\ge
-
(2\sqrt\eta+\eta)\|Ae\|\|x\|^2.
\]

Подставляя residual bound:

\[
\boxed{
\langle x,Ax\rangle
\ge
\left[
\beta(1-\eta)
-
\frac{2\sqrt\eta+\eta}{\sqrt{1-\eta}}\rho
\right]
\|x\|^2.
}
\]

Это полный answer к вопросу о qualitative break: **никакого qualitative break нет**.
Есть явный continuous loss.

### 3.6 Exact parity as a special case

Если `eta=0`, то `q=e` exact even и формула становится

\[
\beta_{\rm eff}=\beta.
\]

То есть прежняя exact split является только zero-loss endpoint quantitative theorem.

## 4. Из `oddMass <= epsilon` получается `min - C sqrt epsilon`

Пусть

\[
\eta\le\varepsilon<1.
\]

Тогда можно использовать

\[
\beta_{\rm eff}
\ge
\beta(1-\varepsilon)
-
\frac{2\sqrt\varepsilon+\varepsilon}{\sqrt{1-\varepsilon}}\rho.
\]

Если `epsilon <= 1/2` и `rho <= M`, то

\[
\beta_{\rm eff}
\ge
\beta
-
\beta\varepsilon
-
\sqrt2(2\sqrt\varepsilon+\varepsilon)M.
\]

Так как `epsilon <= sqrt(epsilon)` на `[0,1]`, получаем грубую форму

\[
\boxed{
\beta_{\rm eff}
\ge
\beta
-
(\beta+3\sqrt2 M)\sqrt\varepsilon.
}
\]

Следовательно, предложенная владельцем форма

\[
\beta_j
\ge
\min(\beta_{+,j},\beta_{-,j})-C\sqrt{\varepsilon_j}
\]

правильна при uniform coupling/residual bound.

### Cofinal consequence

Если

\[
\beta_j\ge\beta_0>0,
\qquad
\eta_j\to0,
\qquad
\sqrt{\eta_j}\rho_j\to0,
\]

то

\[
\liminf_j\beta_{{\rm eff},j}\ge\beta_0.
\]

Если `rho_j` uniformly bounded, достаточно `eta_j -> 0`.

Если `rho_j` растёт, нужна relative rate:

\[
\sqrt{\eta_j}\rho_j=o(\beta_j).
\]

Если sector floor сам стремится к нулю, нужна полная relative condition:

\[
\beta_j\eta_j
+
\frac{2\sqrt{\eta_j}+\eta_j}{\sqrt{1-\eta_j}}\rho_j
=o(\beta_j).
\]

## 5. Более сильный `O(epsilon)` вариант

Square-root loss не является фундаментальным. Он возникает из прямой triangle estimate.

Пусть

\[
\kappa=\|P_{e^\perp}Ae\|,
\qquad
d=\langle e,Ae\rangle\in\mathbb R.
\]

Для любого `theta in (0,1)` Young inequality даёт

\[
2|c|\kappa\|y\|
\le
\theta\beta_+\|y\|^2
+
\frac{\kappa^2}{\theta\beta_+}|c|^2.
\]

Поэтому при `beta_+>0`:

\[
\boxed{
\beta_{\rm eff}^{(\theta)}
\ge
\min((1-\theta)\beta_+,\beta_-)(1-\eta)
-
\eta
\left(
\frac{\kappa^2}{\theta\beta_+}+|d|
\right).
}
\]

Это `O(eta)` loss. Цена — заранее потратить `theta`-долю even-sector floor.

Следовательно, theorem design имеет две честные версии:

```text
Residual-only theorem:
  cheapest assumptions;
  O(sqrt oddMass) loss.

Absorbed-coupling theorem:
  stronger sector/coupling inputs;
  O(oddMass) loss.
```

Для первого Lean node residual-only версия предпочтительнее.

## 6. Fixed-shift specialization

Пусть sector floors доказаны при fixed shift `a_star`, а production floor нужен при literal
Rayleigh shift

\[
a_j=\texttt{sourceCCMFiniteRayleigh}\,S\,i_j.
\]

Обозначим

\[
\delta_j=|a_j-a_*|,
\qquad
r_j=(K_j-a_jI)q_j.
\]

Тогда

\[
\|(K_j-a_*I)q_j\|
\le
\|r_j\|+\delta_j.
\]

После contamination estimate при `a_star` и exact one-to-one shift transport:

\[
\boxed{
\begin{aligned}
\beta_{j,\rm literal}
\ge{}&
\beta_*(1-\eta_j)\\
&-
\frac{2\sqrt{\eta_j}+\eta_j}{\sqrt{1-\eta_j}}
(\|r_j\|+\delta_j)
-
\delta_j.
\end{aligned}
}
\]

Это правильная replacement architecture:

```text
sector floors at fixed shift
+ oddMass rate
+ source residual rate
+ Rayleigh proximity
→ literal full complement floor.
```

Exact row parity больше не является pre-gate.

## 7. Почему oddMass decay alone недостаточна

Ниже полный finite-dimensional witness. Он убивает слишком сильное утверждение

```text
sector floors + oddMass -> 0
  imply full complement floor.
```

### 7.1 Space and reflection

Пусть

\[
H=\operatorname{span}\{e,y,z\}
\]

с orthonormal basis, и

\[
Je=e,
\qquad
Jy=y,
\qquad
Jz=-z.
\]

### 7.2 Almost-even trial row

Для `0<delta<1` положим

\[
s=\sqrt{1-\delta^2},
\qquad
q_\delta=se+\delta z.
\]

Тогда

\[
\|q_\delta\|=1,
\qquad
\operatorname{oddMass}(q_\delta)=\delta^2\to0.
\]

### 7.3 Reflection-commuting Hermitian form

Определим `A_delta`:

\[
A_\delta|_{\operatorname{span}\{e,y\}}
=
\begin{pmatrix}
0&M_\delta\\
M_\delta&1
\end{pmatrix},
\qquad
A_\delta z=z.
\]

`A_delta` Hermitian и коммутирует с `J`.

Even complement к `e` равен `span{y}` и имеет floor `1`:

\[
\langle y,A_\delta y\rangle=1.
\]

Odd sector также имеет floor `1`:

\[
\langle z,A_\delta z\rangle=1.
\]

### 7.4 Vector in the literal complement

Положим

\[
x_\delta
=
y-\frac\delta s e+z.
\]

Тогда

\[
\langle q_\delta,x_\delta\rangle
=s\left(-\frac\delta s\right)+\delta=0.
\]

То есть `x_delta in q_delta perp`.

Его energy:

\[
\langle x_\delta,A_\delta x_\delta\rangle
=
2-2M_\delta\frac\delta s.
\]

Выбираем

\[
M_\delta=2s/\delta.
\]

Тогда

\[
\boxed{
\langle x_\delta,A_\delta x_\delta\rangle=-2.
}
\]

Итак, одновременно:

```text
oddMass -> 0;
even-sector floor = 1;
odd-sector floor = 1;
full q-perp form has a negative direction.
```

Что выросло? Coupling:

\[
\|A_\delta q_\delta\|\asymp\delta^{-1}.
\]

Этот witness доказывает точную границу:

\[
\boxed{
\text{oddMass rate must be paired with residual/coupling control.}
}
\]

Поэтому два existing odd-mass suppliers **ведут в правильную сторону**, но сами по себе
не закрывают complement floor.

## 8. Проверка достижимости `oddMass = 0`

### 8.1 Что доказано

`ProlatePair` экспортирует exact additive evenness:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/ProlateLayer.lean:63-64
  h0_even
  h4_even
```

Следовательно, `prolateCombination` как additive source function exact even.

### 8.2 Что не доказано

Production source row появляется только после цепочки:

```text
prolateCombination
→ E_star
→ multiplicative window gTrial_m
→ finite orthogonal projection gTrial_m_N
→ normalization kTrial_m_N
→ Fourier coefficient extraction c_n
→ sourceCCMComplexRow.
```

Проверяемые адреса:

```text
D0KTrialStage2.lean:14-67
  E_star, gTrial_m, gTrial_m_N

D0KTrialStage3.lean:14-100
  TrialNonzero, sTrial_m_N, kTrial_m_N, c_n

D0PstarCCMFiniteSourceResidual.lean:85-130
  sourceCCMComplexRow, sourceCCMFiniteRayleigh,
  sourceCCMFiniteResidual, sourceCCMComplexRow_apply
```

В прочитанном source chain нет theorem, что вся эта композиция сохраняет требуемое
reflection-evenness finite row.

Более того, conditional theorem на `CCMProposition59SourceTrialFeshbachPreflight.lean:128`
прямо маркирует это как неэкспортируемый current contract input.

### 8.3 Verdict

```text
oddMass = 0 for the actual source row:
  NOT VERIFIED.

mathematically impossible:
  NOT PROVED.

possibly true after a stronger exact intertwining theorem:
  OPEN.

safe current route:
  quantitative oddMass, not exact parity.
```

Итак, exact parity в предыдущем PRE_GATE была **допущением о желаемом supplier**, а не
проверенным свойством source object. Она может оказаться ложной на каждой конечной клетке,
даже если contamination стремится к нулю cofinally.

## 9. Новый theorem-ready boundary

Предыдущий gate

```text
ExactSourceCCMComplexRowEvenness
```

надо заменить двумя независимыми узлами.

### 9.1 Generic finite transport theorem

Предлагаемое имя:

```lean
complexTrialComplementFloor_of_reflectionSectorFloors_oddMass_residual
```

или source-specialized wrapper:

```lean
sourceCCMComplexTrialComplementFloor_of_sectorFloors_oddMass_residual
```

Required inputs:

```text
K Hermitian;
K commutes with ccm reflection;
q unit;
eta = sourceCCMComplexOddMass S i;
eta < 1;
even floor on vectors orthogonal to normalized even part of q;
odd-sector floor;
rho >= norm ((K-aI)q);
beta_eff > 0.
```

Output:

```lean
sourceCCMComplexTrialComplementFloor S i beta_eff
```

with exact

```text
beta_eff
  = min(betaPlus,betaMinus) * (1-eta)
    - ((2*sqrt eta + eta)/sqrt(1-eta)) * rho.
```

This is finite-dimensional linear algebra. It is theorem-head ready after exact matrix and
reflection APIs are inspected.

### 9.2 Cofinal source rate theorem

Предлагаемое имя:

```lean
sourceCCMComplexOddMass_tendsto_zero_of_physicalApproximation
```

или bounded-envelope version:

```lean
sourceCCMComplexOddMass_le_physicalApproximationErrorSq
```

плюс уже существующий convergence supplier для right side.

Этот узел должен использовать один из готовых receivers at `:138` or `:205`. Он не должен
перестраивать odd mass и не должен symmetrize source row.

### 9.3 Fixed-shift transport

После первых двух узлов existing fixed-shift architecture остаётся без изменения:

```text
fixed sector floors
+ odd-mass/residual loss
+ Rayleigh proximity
→ literal full complement floor.
```

## 10. Рассмотренные и отвергнутые ветки

### 10.1 Exact parity as mandatory pre-gate

**Отвергнуто как лишнее усиление.** Exact parity даёт zero loss, но quantitative theorem
достаточен.

### 10.2 Ignore odd mass because it tends to zero

**Отвергнуто.** Полный three-dimensional witness выше показывает, что unbounded coupling
может превратить arbitrarily small contamination в отрицательное направление.

### 10.3 Replace source row by its even projection

**Отвергнуто как object switch.** Это меняет Rayleigh value, residual, trial line и
production complement. Existing file специально избегает такого symmetrization.

### 10.4 Use only operator norm

**Viable but weaker.** Если имеется uniform `||K-aI|| <= M`, можно взять `rho<=M` и
получить `C sqrt epsilon` theorem. Но source residual является более точным и уже
производственным объектом.

### 10.5 Demand `O(epsilon)` immediately

**Не выбран первым.** Young-absorbed theorem даёт linear loss, но требует отдельный
coupling field and spends sector floor. Residual-only theorem имеет меньше API и выше шанс
быстрого Lean proof.

### 10.6 Read agreement with Mythos as independent confirmation

**Отвергнуто.** Mythos verdict from 2026-08-14 was read. Sector split, fixed shift and
`beta/2` transport are transmitted architecture. The explicit contamination constants and
the coupling counterexample in this report were derived directly from the current objects,
but they do not create a second independent witness for the overall route.

## 11. Sources and exact addresses

```text
CURRENT PIN
  f733402b918244ccfd9051b7efa830d63b44c8a3

ODD MASS IDENTITY
  q3.lean.aristotle/Q3/Proofs/RouteB/
  D0PstarSourceCCMOddMassReflectionDefect.lean:112
  sourceCCMComplexOddMass_eq_quarter_norm_reflectionDefect_sq

REFLECTED-COEFFICIENT PHYSICAL RECEIVER
  same file:138
  sourceCCMComplexOddMass_le_quarter_norm_sub_sq_of_reflected_coefficients

EVEN-COEFFICIENT PHYSICAL RECEIVER
  same file:205
  sourceCCMComplexOddMass_le_norm_sub_sq_of_even_coefficients

CONDITIONAL EXACT ROW EVENNESS
  q3.lean.aristotle/Q3/Proofs/RouteB/
  CCMProposition59SourceTrialFeshbachPreflight.lean:128
  sourceCCMComplexRow_even_of_phaseRealification_even

EXACT SOURCE ROW / RAYLEIGH / RESIDUAL
  q3.lean.aristotle/Q3/Proofs/RouteB/
  D0PstarCCMFiniteSourceResidual.lean:85-130
  sourceCCMComplexRow
  sourceCCMFiniteRayleigh
  sourceCCMFiniteResidual
  sourceCCMComplexRow_apply

EXACT FULL COMPLEMENT TARGET
  q3.lean.aristotle/Q3/Proofs/RouteB/
  CCMProposition59ComplexTrialComplementFloor.lean:26-48
  complexTrialComplementFloor
  sourceCCMComplexTrialComplementFloor

REFLECTION COMMUTATION
  q3.lean.aristotle/Q3/Proofs/RouteB/
  CCMFiniteWeilParity.lean:67
  ccmWeilMatFinite_commutes_reflection

ADDITIVE PROLATE EVENNESS
  q3.lean.aristotle/Q3/Proofs/RouteB/ProlateLayer.lean:63-64
  ProlatePair.h0_even
  ProlatePair.h4_even

SOURCE PIPELINE
  D0KTrialStage2.lean:14-67
  D0KTrialStage3.lean:14-100

PRIOR PROSHKA REPORT
  docs/routeB_bus/proshka/
  PROSHKA_COFINAL_CCM_EVEN_COMPLEMENT_FLOOR_AT_FIXED_SHIFT_2026-08-17.md
  commits:
    b0373234d57648f0efe924153d2af99e589e709a
    4aff406214134bbfe7c8e6b7bfe4026dd20f8691

MYTHOS VERDICT READ
  q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/
  GOAL058_G1_COFINAL_COMPLEMENT_FLOOR_MYTHOS_VERDICT_2026-08-14.md
  commit f2bbec01849bff69f4e1a9ffe022e906e66cd04c
  provenance: READ / NOT INDEPENDENT
```

## 12. Что не проверено с моей стороны

1. Не написан Lean proof quantitative contamination theorem.
2. Не проверено exact theorem API for even/odd subspaces on the complex finite carrier.
3. Не доказан cofinal rate for either right side at lines `:138` or `:205`.
4. Не доказан uniform bound or decay for production residual in the exact schedule used here.
5. Не доказаны the even and odd sector floors themselves.
6. Не доказана Rayleigh proximity to a fixed shift.
7. Не доказано `oddMass=0` и не построен counterexample for the actual source showing it is
   nonzero.
8. Не определены optimal constants. The displayed constants are rigorous but deliberately
   coarse.
9. Не проверено whether a direct projector-commutator estimate gives a materially sharper
   production constant.
10. Lean build не запускался: этот commit является docs-only mathematical audit.

## 13. ROUTE MAP

```text
existing physical approximation theorem
  -> oddMass_j <= error_j^2

sector floor at fixed shift, even complement
+ odd-sector floor
+ source residual/coupling bound
+ oddMass_j
  -> contamination-aware full floor at fixed shift

Rayleigh proximity
  -> literal source-Rayleigh complement floor

fixed positive lower envelope
+ residual tracking
  -> G1 quantitative ground tracking
```

Точное `q perp` parity decomposition больше не является gate. Оно стало optional theorem,
который улучшает loss from quantitative to zero.

## 14. FINAL PROPOSAL

### Chosen route


a) Freeze exact parity as an optional optimization.

b) Promote the two existing odd-mass receivers to the active source lane.

c) Prove one generic finite contamination-to-floor theorem.

d) Ask the source side only for the rate needed by the displayed `beta_eff`, not for exact
zero contamination.

### Registered prediction

```text
P-ODDMASS-1:
  generic contamination-to-floor theorem is local finite-dimensional Lean work.

P-ODDMASS-2:
  the real source cost is proving a cofinal physical approximation rate in the same
  schedule, not exact parity.

P-ODDMASS-3:
  residual-only loss closes with O(sqrt oddMass); an O(oddMass) refinement is available
  later through Young absorption.

P-ODDMASS-4:
  exact oddMass=0 will not be needed and may fail at finite cells even when oddMass tends
  to zero.
```

### New stop code

```text
CONTAMINATION_TO_FLOOR_TRANSPORT_AND_COFINAL_RATE_OPEN
```

## 15. STRONGEST ATTACK

Самое сильное возражение к repaired route:

> `oddMass_j -> 0` измеряет только angle of the row. The form may have unbounded coupling
> from the even trial direction into its even complement. Then tiny angle can still create
> a large negative direction in the literal complement.

Это возражение верно. Именно поэтому report не заменяет exact parity одним scalar rate.
Он заменяет её парой:

\[
\boxed{
\text{oddMass rate}
+
\text{residual/coupling control}.
}
\]

Three-dimensional witness в разделе 7 показывает, что coupling term несущий, а не
технический.

Сильнейшая repaired theorem использует production residual, а не global operator norm.
Это не новый чужой объект: `sourceCCMFiniteResidual` уже определён в source layer.

## 16. CODEX DIRECTIVE

```text
NO EXECUTION AUTHORIZED BY THIS ANALYSIS.

Next theorem-ready target after owner authorization:

  complexTrialComplementFloor_of_reflectionSectorFloors_oddMass_residual

First preflight:
  locate exact complex reflection projections and parity-subspace APIs;
  instantiate the three-dimensional counterexample as a semantic plant;
  verify the theorem specializes exactly to complexTrialComplementFloor.

Validation gate:
  lake env lean <new-file>
  lake build Q3
  #print axioms <new-theorem>

Forbidden shortcuts:
  symmetrize q;
  assume exact row evenness;
  replace residual by numerically fitted operator norm;
  weaken full q-perp floor to sector-only floors.
```

## 17. META CLOSEOUT

**Что стало меньше?**

Exact source parity wall заменена explicit inequality with three measurable inputs:

```text
odd mass;
sector floors;
source residual/coupling.
```

**Что убито?**

```text
exact parity is mandatory;
odd-mass suppliers lead nowhere;
oddMass -> 0 alone closes the floor.
```

**Что нельзя пробовать снова?**

Нельзя symmetrize the source row or claim exact `min(even,odd)` after losing invariant
`q perp`.

**Current smallest named gap:**

```text
SourceCCMOddMassRateAndComplementFloorLoss
```

with local finite sub-gap:

```text
complexTrialComplementFloor_of_reflectionSectorFloors_oddMass_residual
```

**Next cheapest decisive test:**

Formalize the generic finite theorem with the full three-dimensional plant. This either
compiles with the displayed constant or exposes an API/object mismatch before any cofinal
source analysis.

**Fate of prior predictions:**

```text
exact row parity is the pre-gate:
  REFUTED.

odd-mass identity is only diagnostic:
  REFUTED.

one new spectral wall remains in the even head:
  CONFIRMED.

fixed-shift transport removes varying-denominator work:
  CONFIRMED, now with contamination loss added.
```

```yaml
iteration:
  target: exact_source_row_evenness_pre_gate
  status: PROGRESS
  failed_strategy: require_zero_contamination_before_sector_floor
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: SourceCCMOddMassRateAndComplementFloorLoss
  invariant_learned: approximate parity is a graph perturbation; coupling scale must be retained
  forbidden_future_move: infer full complement floor from oddMass decay without residual control
  next_decisive_test: generic_finite_contamination_floor_theorem_with_3d_plant
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```
