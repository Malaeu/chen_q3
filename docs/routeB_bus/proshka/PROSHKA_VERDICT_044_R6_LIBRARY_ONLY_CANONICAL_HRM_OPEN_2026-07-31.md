# PROSHKA VERDICT — 044 RATIFIED LOCALLY; CANONICAL hRm NOT YET DISCHARGED
Date received: 2026-07-31
Channel: owner-relayed chat (Proshka has no write access)
Materialized by: conductor-CLI (Claude Code, Linux) on owner's direct order
Timing note: verdict pins HEAD 4a9338a4 — written BEFORE Goal 045 (R6-class hRp
wrapper) closed at ff0045b2. Goal 045 is CLOSED and immutable; per this verdict's
reclassification its ledger meaning is R6-LIBRARY supplier, not canonical discharge.
The verdict's CODEX DIRECTIVE (exact v3-class hRp) is transcribed as Goal 046.
Consumed by: ledger reclassification (hRm/hRp = R6-class PROVED, canonical D0-class
OPEN); Goal 046 issuance; H2b gap FiniteQWTheorem510RealZeroBridge registered;
load-bearing Müntz gap ZeroMassRiemannSumBound_IccZero_IcoLipschitz registered;
crosswalk kill-gates C1–C7 + discriminator D_j(K) registered for the pending card.
Transport artifacts note: payload verbatim as pasted by the owner; escaping and
markdown-rendering artifacts preserved (bracket-fenced display math; the Gate C4
display where "G_win = Z_pole-sub − R_− − R_+" was mangled by chat markdown into
heading lines with equals-signs — preserved as received, not repaired). Semantic
content untouched.

--- VERBATIM PAYLOAD BEGINS ---

# STATUS: OPEN — 044 RATIFIED LOCALLY; CANONICAL `hRm` NOT YET DISCHARGED

```yaml
primary_verdict: RATIFY_044_AS_R6_LIBRARY_SUPPLIER_ONLY

request_1:
  code: CANONICAL_HRM_CLASS_BRIDGE_OPEN
  transaction_044: RATIFIED
  abstract_R6_supplier: PROVED
  canonical_D0_T5_hRm: OPEN_LOAD_BEARING_REPAIRABLE
  route_fatal: false
  casual_witness_class_switch_allowed: false
  next_executable_supplier: HRP_V3CLASS

request_2:
  code: THM510_RATIFIED_AS_CONDITIONAL_H2B_LAYER
  theorem_5_10_import: RATIFIED_PAPER
  H2b_closed_for_project: false
  simple_even_QW: H2A_OPEN
  deltaN_nonvanishing: OPEN
  finite_operator_object_crosswalk: OPEN
  PW_simple_even_citation: UNVERIFIED_IMPORT
  two_limit_convergence: S1_S2_OPEN

request_3:
  code: MUNTZ_ROUTE_CROSSWALK_KILL_PASS_REGISTERED_PENDING_CARD
  card_received: false
  likely_maximal_current_slot: H1_CONDITIONAL
  S2_requires_compact_defect_to_zero: true
  direct_H4_promotion: forbidden

route_state: CHALLENGER_NOT_RH
bus_010: VOID
state_promotion: false
rh_claimed: false
head_verified: 4a9338a41efa194ac90d7d855cba44bbc9430176
```

HEAD `4a9338a4…` действительно закрывает Goal 044 именно с формулировкой `HRM_SUPPLIER_DISCHARGED_UNDER_R6_HYPOTHESES` и оставляет `WITNESS_CLASS_VS_R6_HYPOTHESES_GAP` открытым.  `[ABSTRACT][LEAN]`

## ROUTE MAP

| Объект                                  | Судейский статус                | Что фактически доказано                                                                                                                     | Tags                      |
| --------------------------------------- | ------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------- |
| Goal 044                                | **RATIFIED**                    | Чистый импорт семифайлового R6 closure и 32-строчный wrapper; proof bodies не менялись, build/taint/axioms прошли.                          | `[ABSTRACT][LEAN]`        |
| `rminus_analyticOnNhd_shiftedHalfPlane` | **PROVED ON R6 CLASS**          | `hRm` при `0<a`, support в `Icc a b`, global `LipschitzWith`, zero mass и `1≤Λ`.                                                            | `[ABSTRACT][LEAN]`        |
| Canonical D0 `hTrial_m`                 | **CLASS MATCH OPEN**            | Source-lock фиксирует prolate-комбинацию и нулевую положительную массу, но не даёт support-away-from-zero или global Lipschitz certificate. | `[ABSTRACT][PAPER]`       |
| `hRp`                                   | **CHEAP NEXT SUPPLIER**         | R6 уже доказывает entire `Rplus`, причём zero mass не используется; нужен wrapper/generalization на точном v3-классе.                       | `[ABSTRACT][CONDITIONAL]` |
| Theorem 5.10                            | **RATIFIED AS H2b PAPER LAYER** | При simple-even normalized ground eigenvector Fourier transform имеет только вещественные нули.                                             | `[ABSTRACT][PAPER]`       |
| `SIMPLE_EVEN(QW_λ)`                     | **OPEN H2a**                    | Авторы сами называют это первым missing step.                                                                                               | `[ABSTRACT][PAPER]`       |
| Müntz → Route B                         | **PENDING CARD**                | Текущий shell даёт аналитическое продолжение exact identity; его конкретный roof-consumer ещё не установлен.                                | `[ABSTRACT][CONDITIONAL]` |

---

## ЗАПРОС №1 — KILL-PASS НА GOAL 044

### Вердикт

[
\boxed{
\text{044 корректен как библиотечный supplier, но не закрывает canonical }hRm.
}
]

Goal 044 точно сохранил R6-посылки и честно отказался выводить их из v3-класса. Wrapper использует только half-plane bridge, definitional equality `Rminus` и переход `DifferentiableOn.analyticOnNhd`; его аксиомы — стандартная тройка.  `[ABSTRACT][LEAN]`

Но source-locked D0-функция — конкретная нормированная комбинация prolate-мод (h_{0,\lambda},h_{4,\lambda}), zero-extended на ([-\lambda,\lambda]), с midpoint representative. Lean пока хранит её как свободный `hTrial_m`; положительная половинная масса доказана равной нулю. Source-lock не поставляет ни `0<a` support certificate, ни global `LipschitzWith`.  `[ABSTRACT][PAPER]`

Поэтому правильный ledger:

```text
hRm_R6_library:
  PROVED.

hRm_for_canonical_D0_hTrial:
  OPEN.

"one of four canonical T5 inputs discharged":
  REJECTED.
```

`[ABSTRACT][PAPER]`

### Фатален ли `WITNESS_CLASS_VS_R6_HYPOTHESES_GAP`?

**Для всего маршрута — нет. Для текущего canonical T5-instantiation — да, это load-bearing blocker.**

Его нельзя закрыть простой фразой «выбираем другой witness-класс». PL1 и PL2 — falsifier plants, а не обязательное семейство Route B. Но и произвольно заменить source-locked (hTrial_m) на функцию с support away from zero нельзя: потребуется отдельный theorem, что новая функция сохраняет D0/ALPHA/approximant object, normalization и downstream consumer. Без такого theorem это test-class swap. `[ABSTRACT][PAPER]`

Наиболее слабый честный ремонт — не менять (hTrial_m), а обобщить центральную R6-лемму:

[
\boxed{
\texttt{EstarBoundedBySqrtOfZeroMass_IccZero_IcoLipschitz}
}
]

из точных v3-посылок:

```lean
Measurable h
support h ⊆ Icc 0 b
LipschitzOnWith K h (Ico 0 b)
∫_(0,∞) h = 0
```

После неё почти весь R6 `Rminus`-доказательный хвост переиспользуется. Новый аналитический член — endpoint-aware Riemann-sum estimate: скачок или особое значение в (b) обрабатывается отдельно, а не скрывается global Lipschitz assumption. `[ABSTRACT][CONDITIONAL]`

### Решение по `hRp`

[
\boxed{
\text{Следующий дешёвый supplier — }hRp,\text{ но сразу на exact v3 class.}
}
]

Экспортированный R6 theorem `Rplus_differentiable` не использует zero mass и доказывает entire right tail посредством compact support. Однако его публичный тип всё ещё несёт лишние R6-посылки `0<a` и `LipschitzWith`.  `[ABSTRACT][LEAN]`

Поэтому не нужен ещё один thin wrapper с тем же class mismatch. Нужен exact consumer theorem на классе `MuntzV3Unconditional.lean`.

---

## ЗАПРОС №2 — АУДИТ ИМПОРТА H2b / THEOREM 5.10

### Вердикт

[
\boxed{
\texttt{THM510_RATIFIED_AS_CONDITIONAL_H2B_LAYER}
}
]

Theorem 5.10 действительно является paper-level real-zero engine: при simple smallest eigenvalue и even eigenvector, нормированном условием (\delta_N(\xi)=1), строится self-adjoint (D_{\log}^{(\lambda,N)}), а нули (\widehat\xi) совпадают с его вещественным спектром.  `[ABSTRACT][PAPER]`

Но текущая подпись импорта смешивает три разных слота.

### Правильная классификация

| Утверждение                                                  | Правильный слот              | Статус                                  | Tags                      |
| ------------------------------------------------------------ | ---------------------------- | --------------------------------------- | ------------------------- |
| Lowest eigenvalue simple, eigenvector even                   | **H2a**                      | OPEN для (QW_\lambda)                   | `[ABSTRACT][PAPER]`       |
| Нормировка (\delta_N(\xi)=1) допустима                       | H2a/object lock              | Требуется (\delta_N(\xi)\neq0)          | `[ABSTRACT][CONDITIONAL]` |
| Thm 5.10: transform ground state имеет real zeros            | **H2b**                      | PAPER theorem, project application OPEN | `[ABSTRACT][PAPER]`       |
| (k_\lambda\approx\xi_\lambda)                                | S1/S2 tracking supply        | OPEN                                    | `[COFINAL_FAMILY][PAPER]` |
| (N\to\infty), затем (\lambda\to\infty), convergence to (\Xi) | S1/S2 / strip identification | OPEN                                    | `[COFINAL_FAMILY][PAPER]` |

Сами авторы явно называют двумя missing steps: simple-even для (QW_\lambda) и достаточную близость (k_\lambda) к (\xi_\lambda), обеспечивающую convergence zeros. Theorem 3.6 даёт discrete lower-bounded spectrum, но не simple-even.  `[ABSTRACT][PAPER]`

### Что ещё требуется до project-H2b

Нужен theorem-sized crosswalk:

[
\boxed{
\texttt{FiniteQWTheorem510RealZeroBridge}
}
]

с пятью полями:

```text
1. project finite form/operator = paper QW_λ^N;
2. project finite carrier = paper E_N;
3. selected ground vector = paper ξ;
4. δ_N(ξ) ≠ 0, hence normalization δ_N(ξ)=1 is legal;
5. project approximant =
     nonzero scalar × λ^(−iz) × ξ̂(z),
   where λ^(−iz) is entire and zero-free.
```

Только после этого Theorem 5.10 занимает Lean-интерфейс `Theorem510RealZeroBridge`. В условной крыше Route B этот bridge намеренно отделён и не выводится одной чётностью.  `[ABSTRACT][LEAN]`

### Поправка по prolate simple-even

Фраза «simple-even для (PW_\lambda) — THEOREM по их цитате» пока остаётся `UNVERIFIED_IMPORT`: supplement пересказывает ссылку, но не содержит точного внешнего theorem statement, source и доказательства. До получения cited source это feasibility anchor, не project fact. `[ABSTRACT][CONDITIONAL]`

### Что нельзя писать

```text
Theorem 5.10 closes S2.
```

Неверно. Он закрывает real-zero свойство **конечного объекта** при H2a. S2 — идентификация ненулевого cluster с (c,\Xi,\gamma_0); это другой предел и другой quantifier. `[COFINAL_FAMILY][PAPER]`

---

## ЗАПРОС №3 — KILL-PASS ДЛЯ `MuntzV3_to_RouteBGate_Crosswalk`

Карточка пока не ратифицирована. Судейский контракт зарегистрирован заранее.

### Обязательный маршрутный header

```text
ROUTE_ID:
TARGET_TEST_CLASS:
FINAL_ROOF_THEOREM:
EXACT_ROOF_ARGUMENT_DISCHARGED:
CURRENT_OPEN_SUPPLIERS:
EXACT_CONSUMER_THEOREM:
OBJECT_AND_NORMALIZATION_CROSSWALK:
COFINAL_SEQUENCE:
AXIOM_PROFILE:
WHY_NOT_LEGACY_BROAD_CONE_ROUTE:
```

`EXACT_ROOF_ARGUMENT_DISCHARGED` обязан быть одним из:

```text
H1
H2a
H2b / Theorem510RealZeroBridge
ANCHOR
S1 / MontelAnchorGate
S2
```

Фраза «ведёт в H4» без указания конкретного аргумента `rh_of_canonical_strip_slots` будет отклонена как nonconsuming card. `[ABSTRACT][LEAN]`

### Семь kill-gates

**Gate C1 — Same object.**
`h`, `E_star`, `Gwin`, (m,N,\lambda,\Lambda), midpoint/star convention и normalization должны быть буквально source-locked. `[ABSTRACT][PAPER]`

**Gate C2 — Same class.**
Все четыре входа `hG`, `hRm`, `hRp`, `habs` должны быть доказаны для одной и той же функции. Goal 044 не занимает canonical `hRm`, пока открыт class bridge. `[ABSTRACT][LEAN]`

**Gate C3 — Same family and subsequence.**
Real-zero approximants из H2b и Müntz-analytic approximants должны быть одним `selectedFamily`, а не двумя похожими конструкциями. `[COFINAL_FAMILY][PAPER]`

**Gate C4 — Tail smallness, not tail analyticity.**
T5 имеет точную форму

[
G_{\rm win}
===========

## Z_{\rm pole-sub}

## R_-

R_+.
]

`AnalyticOnNhd(R_\pm)` не даёт (R_\pm\to0). В current wrapper `hG`, `hRm`, `hRp` и `habs` остаются отдельными inputs.  `[ABSTRACT][LEAN]`

**Gate C5 — Xi/gauge identification.**
Нужен exact переход от pole-subtracted zeta–Mellin product к centered (\Xi) с gamma/(\pi)-factors и zero-free gauge. Нули `Mellin h` нельзя молча объявить частью zero-free gauge. `[COFINAL_FAMILY][PAPER]`

**Gate C6 — Quantifiers.**
Finite-window identity 012 является параметрическим и не выбирает concrete `hTrial_m`; она также не даёт tail smallness.  `[ABSTRACT][LEAN]` Любой переход к cofinal family требует отдельного uniform theorem. `[COFINAL_FAMILY][PAPER]`

**Gate C7 — Noncircularity.**
Нельзя использовать отсутствие off-critical zeros, желаемую convergence to (\Xi), S2 или RH для доказательства tail/gauge convergence. `[COFINAL_FAMILY][PAPER]`

### Дискриминатор для S2-карточки

Для каждого компакта (K\Subset S) карточка должна назвать и оценить

[
\boxed{
\mathfrak D_j(K)
:=
\sup_{z\in K}
\left|
H_j(z)-c,\Xi(z)\gamma_0(z)
\right|,
}
]

где:

* (H_j) — **тот же** gauge-normalized finite approximant, у которого H2b даёт real zeros;
* (c\neq0);
* (\gamma_0) фиксирована на выбранной подпоследовательности и zero-free;
* требуется (\mathfrak D_j(K)\to0) для каждого (K\Subset S).

`[COFINAL_FAMILY][CONDITIONAL]`

Без этого Müntz shell может занимать H1, но не S2.

### Зарегистрированные прогнозы до получения карточки

```text
P-X1:
  Müntz continuation честно поставляет H1-type analyticity
  после exact class bridge.

P-X2:
  главный missing fact для S2 будет не analyticity,
  а locally uniform normalized control of Rminus+Rplus
  together with the Mellin/gamma gauge.

P-X3:
  Theorem 5.10 joins the route through H2b independently;
  Müntz and H2b must meet on the same selected family.

P-X4:
  a card phrased only as "Müntz → ALPHA/D0 → H4"
  will require REPAIR because it names no typed roof consumer.
```

`[COFINAL_FAMILY][CONDITIONAL]`

---

## FINAL PROPOSAL

Три решения:

```text
№1:
  RATIFY 044 as a clean R6 library supplier.
  REJECT its promotion as canonical hRm closure.
  Gap is load-bearing but repairable.
  Next cheap goal: hRp on the exact v3 class.

№2:
  RATIFY Theorem 5.10 as paper-level conditional H2b.
  Reclassify SIMPLE_EVEN as H2a.
  Keep normalization and object crosswalk open.
  Keep the two-limit convergence in S1/S2.

№3:
  Do not sign the forthcoming crosswalk by narrative proximity.
  Demand a typed consumer, same-family proof, and compact-defect discriminator.
```

---

## STRONGEST ATTACK

### На 044

> Вы доказали хороший theorem для функций с support away from zero, но ваш source-locked prolate trial не имеет такого certificate. Почему это считается погашением `hRm`?

Сейчас ответа нет. Поэтому canonical promotion запрещена. `[ABSTRACT][PAPER]`

### На H2b import

> Theorem 5.10 assumes the exact finite object, simple-even ground state и допустимую (\delta_N)-нормировку. Где доказано, что project object удовлетворяет этим предпосылкам?

Пока нигде в представленном пакете. `[ABSTRACT][PAPER]`

### На Müntz crosswalk

> Аналитичность (R_-) и (R_+) не означает их исчезновения. Как additive tails превращаются в (c,\Xi,\gamma_0) без остатка?

Это наиболее вероятная настоящая стена карточки. `[COFINAL_FAMILY][PAPER]`

---

## CODEX DIRECTIVE

```text
TARGET:
  045_MuntzV3_Hrp_ExactClass

PRIMARY THEOREM:
  rplus_analyticOnNhd_shiftedHalfPlane_v3Class

FILE:
  new file under
  muntz_v3/RequestProject/

STATEMENT:

theorem rplus_analyticOnNhd_shiftedHalfPlane_v3Class
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal)
    (hmeas : Measurable h)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) b → h u = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    AnalyticOnNhd ℂ (Rplus h Λ) shiftedHalfPlane

INPUTS:
  muntz_v3/RequestProject/Main.lean
  muntz_v3/RequestProject/MellinCompactSupportAnalyticity.lean
  muntz_v3/RequestProject/R6Export/TailAnalyticity.lean
    as proof template only
  Goal 044 answer

PROOF ROUTE:
  1. Preserve exact v3 definitions of Estar and Rplus.
  2. Derive an a.e. finite bound for h on Icc 0 b from
     LipschitzOnWith on Ico 0 b, treating {b} as a null endpoint.
  3. Prove measurability/local integrability of Estar on Ioi Λ.
  4. Prove Estar h u = 0 for u > b.
  5. Rewrite Rplus as the Mellin transform of a function supported
     in the bounded interval (Λ,b].
  6. Prove Differentiable ℂ, then restrict to shiftedHalfPlane
     with .analyticOnNhd.

FORBIDDEN:
  - no hypothesis 0 < a;
  - no support replacement Icc 0 b → Icc a b;
  - no global LipschitzWith;
  - no zero-mass hypothesis;
  - no modification of Main.lean;
  - no mutation of Goal 044;
  - no Aristotle;
  - no sorry/admit/axiom/native_decide/exact?.

MANDATORY PLANTS:
  P045-1:
    instantiate the theorem on the PL1 witness
      h(u)=1_Ioc(0,1)(u)*u;
    it touches zero, has an endpoint jump, and has nonzero mass.
    The theorem must accept it.

  P045-2:
    dependency audit must show no use of hmass,
    positive lower support, or global Lipschitz.

VALIDATION:
  lake env lean <new-file>
  lake build
  taint scan
  #print axioms rplus_analyticOnNhd_shiftedHalfPlane_v3Class
  expected axioms:
    [propext, Classical.choice, Quot.sound]

SUCCESS:
  HRP_SUPPLIER_DISCHARGED_FOR_V3_CLASS

FAILURE:
  HRP_V3CLASS_ESTAR_MEASURABILITY_GAP
  HRP_V3CLASS_ESTAR_LOCAL_INTEGRABILITY_GAP
  HRP_V3CLASS_ENDPOINT_AE_GAP
  HRP_OBJECT_MISMATCH
  PLANT_NOT_DETECTED
  LEAN_BUILD_FAIL
```

После этого следующий load-bearing theorem — не очередной R6 wrapper, а:

```text
EstarBoundedBySqrtOfZeroMass_IccZero_IcoLipschitz
→ canonical-class hRm.
```

---

## META CLOSEOUT

**Что стало меньше?**

```text
"044 закрыл hRm"
```

разложено на два точных факта:

```text
R6-class hRm: PROVED.
Canonical D0-class hRm: OPEN.
```

**Что убито?**

* автоматическое повышение R6-wrapper до canonical supplier;
* использование PL1/PL2 как обязательного route witness class;
* смешение `SIMPLE_EVEN`, Theorem 5.10 и S2 в один H2b-узел;
* переход от tail analyticity к tail smallness.

**Что нельзя повторять?**

Нельзя считать theorem потреблённым, пока его hypotheses не получены для exact source-locked объекта.

**Текущий cheapest executable gap:**

[
\boxed{
\texttt{RplusAnalyticOnNhd_V3Class}
}
]

**Текущий load-bearing Müntz-gap:**

[
\boxed{
\texttt{ZeroMassRiemannSumBound_IccZero_IcoLipschitz}
}
]

**Текущий H2b-gap:**

[
\boxed{
\texttt{FiniteQWTheorem510RealZeroBridge}
}
]

**Текущий crosswalk discriminator:**

[
\boxed{
\mathfrak D_j(K)\to0
\quad\text{on every }K\Subset S.
}
]

**Fate of predictions:**

```text
P044-C1:
  PARTIAL — closure was 7 files, wrapper 32 lines.

P044-C2:
  HIT — normalized proof bodies were unchanged.

New P045:
  registered, untested.

New P-X1..P-X4:
  registered before the crosswalk card.
```

```yaml
iteration:
  target: post_044_supplier_and_route_crosswalk_adjudication
  status: OPEN
  failed_strategy: count_stronger_class_supplier_as_canonical_consumption
  cognitive_operator_used: UNIT_AUDIT
  new_gap_name: ZeroMassRiemannSumBound_IccZero_IcoLipschitz
  invariant_learned: supplier hypotheses must match the exact source-locked family
  forbidden_future_move: promote tail analyticity to tail smallness
  next_decisive_test: prove hRp on the exact v3 class and plant it on PL1
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```

--- VERBATIM PAYLOAD ENDS ---
