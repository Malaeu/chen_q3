# STATUS: FATAL — REQ-2026-08-20-E IS OFF BY THE EXACT FACTOR 4; L73.5 IS REPAIRABLE

```yaml
PRIMARY: KILL_UNSCALED_EXPLICIT_CCM_MELLIN_EQUALS_CENTERED_XI
PRIMARY_COUNT: 1

REQUEST:
  ID: REQ-2026-08-20-E
  QUEUE_HEAD: 8d59cba45343cd3f6d7646b2d8d3e2482c8c4a07
  TARGET_AS_REQUESTED: >-
    mellin (E_star explicitCCMLimitH) (-I*z) = centeredXi z
  TARGET_VERDICT: FATAL_FALSE_NORMALIZATION

SOURCE_LOCK:
  EXPLICIT_PACKET_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarExplicitCCMLimitFourier.lean
  EXPLICIT_PACKET_DEF: Q3.RouteB.D0Pstar.explicitCCMLimitH
  ESTAR_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/D0KTrialStage2.lean
  ESTAR_DEF: Q3.RouteB.D0Pstar.E_star
  MELLIN_PRODUCT_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/EStarWindowedMellinCrosswalk.lean
  MELLIN_PRODUCT_THEOREM: Q3.RouteB.D0Pstar.mellin_E_star_eq_riemannZeta_mul
  XI_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/ClassicalXiInterface.lean
  XI_DEF: Q3.RouteB.centeredXi
  XI_ZERO_NONZERO_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/CenteredXiZeroNonzero.lean
  XI_ZERO_NONZERO_THEOREM: Q3.RouteB.centeredXi_zero_ne_zero

EXACT_NORMALIZATION:
  MELLIN_H_P: "p*(p-1)/8 * pi^(-p/2) * Gamma(p/2)"
  MELLIN_ESTAR_H_S: "1/4 * riemannXi(s+1/2)"
  CENTERED_COORDINATE: "s=-I*z"
  CORRECT_UNSCALED_TARGET: >-
    mellin (E_star explicitCCMLimitH) (-I*z) = (1/4) * centeredXi z
  CORRECT_SCALED_TARGET: >-
    mellin (E_star (4 • explicitCCMLimitH)) (-I*z) = centeredXi z

K1_FALSIFIER:
  POINT: z=0
  EXACT_RATIO: 1/4
  NUMERIC_DIAGNOSTIC_ONLY:
    MELLIN_VALUE: 0.1242801945470785274781934349213494
    CENTERED_XI_VALUE: 0.4971207781883141099127737396853977
  DISCRIMINATOR: MELLIN_ZERO_TO_CENTERED_XI_ZERO_RATIO

SCOPE: ABSTRACT
VERIFIER: PAPER_PLUS_SOURCE_LOCK_AUDIT
LEAN_SOURCE_WRITTEN: false
LEAN_PROVED: false

PROPOSED_TARGET_FATAL: true
ROUTE_FATAL: false
L73_5_REPAIRABLE_BY_FIXED_SCALAR: true
NEW_ANALYTIC_PREMISE_REQUIRED: false

CLOSES:
  - EXPLICIT_CCM_LIMIT_MELLIN_NORMALIZATION_AUDIT
  - FALSE_UNSCALED_EXPLICIT_CCM_LIMIT_TO_CENTERED_XI_TARGET
OPENS: []

NEXT_LOAD_BEARING_GAP: EXPLICIT_CCM_LIMIT_MELLIN_TO_QUARTER_CENTERED_XI_LEAN

ARSENAL_MANDATE: ACCEPTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C10_FUNCTIONAL_NOT_SURROGATE

PROGRESS_CLASS: FALSIFICATION_PROGRESS
COGNITIVE_OPERATOR: UNIT_AUDIT
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

| Узел | Статус | Решающий факт | Tags |
|---|---|---|---|
| Литеральный `explicitCCMLimitH` | **LOCKED** | В проекте это \(\frac\pi2 x^2(2\pi x^2-3)e^{-\pi x^2}\). | `[ABSTRACT][LEAN]` |
| `E_star` | **LOCKED** | \(E_\star h(u)=u^{1/2}\sum_{n\ge1}h(nu)\). Дополнительного множителя `4` нет. | `[ABSTRACT][LEAN]` |
| `centeredXi` | **LOCKED** | Это стандартная \(\xi(\tfrac12+iz)\), а не четверть стандартной функции. | `[ABSTRACT][LEAN]` |
| REQ-E equality | **FATAL** | Литеральный Mellin transform равен \(\frac14\,\mathrm{centeredXi}\). | `[ABSTRACT][PAPER]` |
| L73.5 route | **REPAIRABLE** | Фиксированный ненулевой scalar `4` можно внести в source normalization; новая аналитическая посылка не нужна. | `[ABSTRACT][CONDITIONAL]` |

## EXACT AUDIT

Положим

\[
h(x)=\frac\pi2 x^2(2\pi x^2-3)e^{-\pi x^2}
     =\pi^2x^4e^{-\pi x^2}-\frac{3\pi}{2}x^2e^{-\pi x^2}.
\]

Это буквально `explicitCCMLimitH` в production source. `[ABSTRACT][LEAN]`

Для \(p\) в области абсолютной сходимости Gaussian moment formula даёт

\[
\int_0^\infty x^{p+2m-1}e^{-\pi x^2}\,dx
 =\frac12\pi^{-(p+2m)/2}\Gamma\!\left(\frac{p+2m}{2}\right).
\]

Следовательно,

\[
\begin{aligned}
\mathcal M h(p)
&=\frac12\pi^{-p/2}\Gamma\!\left(\frac p2+2\right)
 -\frac34\pi^{-p/2}\Gamma\!\left(\frac p2+1\right)\\
&=\frac{p(p-1)}8\pi^{-p/2}\Gamma\!\left(\frac p2\right).
\end{aligned}
\]

`[ABSTRACT][PAPER]`

Существующая production theorem
`mellin_E_star_eq_riemannZeta_mul` даёт при \(p=s+\tfrac12\):

\[
\begin{aligned}
\mathcal M(E_\star h)(s)
&=\zeta(p)\,\mathcal Mh(p)\\
&=\frac{p(p-1)}8\pi^{-p/2}\Gamma(p/2)\zeta(p)\\
&=\frac14\,\xi(p).
\end{aligned}
\]

`[ABSTRACT][LEAN]` для zeta–Mellin product в его proven half-plane; `[ABSTRACT][PAPER]` для подстановки явного Gaussian moment.

Уже доказанные Gaussian decay и Poisson inversion

\[
E_\star h(u^{-1})=E_\star h(u)
\]

дают полный Mellin continuation; identity theorem сохраняет тот же scalar `1/4`. При \(s=-iz\) имеем

\[
p=\frac12-iz,
\qquad
\xi(p)=\xi(1-p)=\xi\!\left(\frac12+iz\right)=\operatorname{centeredXi}(z).
\]

Поэтому точная формула:

\[
\boxed{
\mathcal M(E_\star\,\mathrm{explicitCCMLimitH})(-iz)
=\frac14\operatorname{centeredXi}(z).
}
\]

`[ABSTRACT][PAPER]`

### K1 planted point

При \(z=0\):

\[
\mathcal M(E_\star h)(0)=\frac14\operatorname{centeredXi}(0).
\]

Production theorem `centeredXi_zero_ne_zero` доказывает
\(\operatorname{centeredXi}(0)\ne0\). Значит requested equality с coefficient `1` и corrected equality с coefficient `1/4` не могут выполняться одновременно. `[ABSTRACT][LEAN]` для невырожденности anchor; `[ABSTRACT][PAPER]` для exact Mellin coefficient.

Численная квадратура была только независимым instrument check:

```text
Mellin(E_star h)(0) = 0.1242801945470785274781934349213494...
centeredXi(0)       = 0.4971207781883141099127737396853977...
ratio               = 0.25 exactly to 79 checked decimal places
```

Это не используется как доказательство. `[FINITE_CELL][CONDITIONAL]`

## FINAL PROPOSAL

### Primary repair — keep the literal packet

Сохранить source-locked equation-(7.1) packet и доказать:

```lean
theorem mellin_E_star_explicitCCMLimitH_eq_quarter_centeredXi
    (z : ℂ) :
    mellin (E_star explicitCCMLimitH) (-I * z) =
      (1 / 4 : ℂ) * centeredXi z
```

После этого port-level fixed normalization multiplies the selected source family by `4`. Тогда downstream target остаётся буквально `centeredXi`.

```text
kill-power: 10/10
proof cost: 7/10
route fit: 10/10
```

`[ABSTRACT][CONDITIONAL]`

### Runner-up repair — scale the limiting packet in the theorem

Определить theorem-facing packet как

\[
h_\Xi:=4h
=2\pi x^2(2\pi x^2-3)e^{-\pi x^2},
\]

и доказать:

```lean
theorem mellin_E_star_four_smul_explicitCCMLimitH_eq_centeredXi
    (z : ℂ) :
    mellin (E_star ((4 : ℂ) • explicitCCMLimitH)) (-I * z) =
      centeredXi z
```

Это математически эквивалентный ремонт, но хуже сохраняет literal equation-(7.1) naming.

```text
kill-power: 10/10
proof cost: 7/10
route fit: 8/10
```

`[ABSTRACT][CONDITIONAL]`

### Forbidden repair

Не менять определение `centeredXi` на четверть стандартной функции. Этот объект уже связан с project RH interface и используется как canonical target. Не объявлять scalar `4` «convention» без theorem-level crosswalk. `[ABSTRACT][LEAN]` **[C04][C10]**

## STRONGEST ATTACK

> Возможно, статья использует другую нормировку \(\Xi\), поэтому factor `4` допустим без изменений.

Для текущего запроса это не спасение. Consumer — не статья как текст, а production definition `Q3.RouteB.centeredXi`. Она фиксирует стандартную \(\xi(\tfrac12+iz)\). Source packet и `E_star` также фиксированы production definitions. Равенство проверяется в этой exact category; неявная paper normalization не может изменить Lean objects. `[ABSTRACT][LEAN]` **[C04]**

> Возможно, Poisson continuation добавляет factor `4`.

Нет. Analytic continuation сохраняет equality, уже установленную на непустой open half-plane; она не меняет глобальный scalar. `[ABSTRACT][PAPER]`

## CODEX DIRECTIVE

```text
NO SOURCE FOR THE REQUESTED EQUALITY.

The requested theorem is mathematically false under current production definitions.
Do not attempt tactic search for it.

Next admissible local target:
  mellin_E_star_explicitCCMLimitH_eq_quarter_centeredXi

Required route:
  1. prove explicit Gaussian Mellin formula;
  2. reuse mellin_E_star_eq_riemannZeta_mul on a nonempty half-plane;
  3. prove full Mellin analyticity from Gaussian decay + E_star inversion;
  4. extend by identity theorem;
  5. apply completed-zeta and functional-equation crosswalk;
  6. add z=0 plant using centeredXi_zero_ne_zero.

Forbidden:
  - fitted scalar;
  - changing centeredXi;
  - assuming the requested identity;
  - treating numerical quadrature as proof;
  - hiding the factor inside a free sourceScale after the theorem.

Success code:
  EXPLICIT_CCM_LIMIT_MELLIN_TO_QUARTER_CENTERED_XI_LEAN

Failure code:
  EXPLICIT_CCM_LIMIT_MELLIN_NORMALIZATION_FORMALIZATION_GAP
```

## META CLOSEOUT

**What became smaller?**

L73.5 is no longer an unnamed full Mellin wall. Its exact content is one explicit Gaussian Mellin calculation plus analytic continuation, with a locked scalar `1/4`. `[ABSTRACT][PAPER]`

**What was killed?**

```text
mellin (E_star explicitCCMLimitH) (-I*z) = centeredXi z
```

under the current production definitions. `[ABSTRACT][PAPER]`

**What must not be tried again?**

Do not spend Lean tactic cycles on the coefficient-`1` target. Do not repair it by silently changing `centeredXi`, the literal packet, or the transform convention.

**Current smallest named gap:**

```text
EXPLICIT_CCM_LIMIT_MELLIN_TO_QUARTER_CENTERED_XI_LEAN
```

**Next cheapest decisive test:**

Formalize the closed-form Mellin transform of `explicitCCMLimitH`; before the analytic-continuation layer, check the coefficient at one symbolically chosen `p` in the absolute half-plane.

**Fate of prior registered prediction:**

```text
L73.5 requested exact target:
  REFUTED.
  The failure is the exact factor 4; no retroactive repair.
```

**Memory entry:**

```yaml
iteration:
  target: EXPLICIT_CCM_LIMIT_MELLIN_TO_CENTERED_XI
  status: FATAL_AS_STATED_REPAIRABLE
  failed_strategy: UNITS_UNAUDITED_PAPER_PORT
  cognitive_operator_used: UNIT_AUDIT
  new_gap_name: EXPLICIT_CCM_LIMIT_MELLIN_TO_QUARTER_CENTERED_XI_LEAN
  invariant_learned: literal equation-(7.1) packet carries one quarter of project centeredXi
  forbidden_future_move: hide factor 4 in convention or tactic search
  next_decisive_test: formal Gaussian Mellin coefficient in Lean
```
