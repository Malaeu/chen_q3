# STATUS: OPEN — ЧЁТНАЯ НОГА СЖАТА ДО ОДНОГО НОВОГО SPECTRAL FLOOR, ОДНОГО SOURCE-CONTRACT РЕМОНТА И ДВУХ ПЕРЕНОСОВ

```yaml
PRIMARY: COFINAL_CCM_EVEN_COMPLEMENT_FLOOR_AT_FIXED_SHIFT
PRIMARY_COUNT: 1

AUDIT_BASE:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  SOURCE_PIN: fef398aa75d5ae37012e8a672f80ca5f7d0e5359
  LATE_CONTROL_PLANE_PARENT: eb6558f4f7b61b0761c1339684703adc1b3c9f53
  INITIAL_PROSHKA_COMMIT: b0373234d57648f0efe924153d2af99e589e709a
  DATE: 2026-08-17

TARGET:
  PROPOSED_NAME: CofinalCCMEvenComplementFloorAtFixedShift
  LEAN_DECLARATION_ON_DISK: false
  ROLE: fixed_shift_even_complement_floor_supplier

CURRENT_CLOSED:
  parity_agnostic_single_mode_decay: true
  parity_agnostic_inverse_square_sum: true
  odd_inverse_weighted_correction_leaf: true

FOUR_MISSING_PIECES:
  P1_NONZERO_EVEN_TAIL_ASSEMBLY:
    CLASS: MIXED
    MECHANICAL_PART: generic_decay_inverse_square_sum_and_most_synthesis_wrappers
    NONMECHANICAL_PART: zero_mode_head_nonzero_tail_carrier_lock
  P2_ROW_PARITY_OR_CONTAMINATION:
    CLASS: SOURCE_CONTRACT_REPAIR
    CURRENT_EXACT_EVENNESS_EXPORTED: false
    AVAILABLE_MEASURER: sourceCCMComplexOddMass
  P3_EVEN_HEAD_FLOOR_AT_FIXED_SHIFT:
    CLASS: GENUINE_NEW_MATHEMATICS
    LOAD_BEARING: true
  P4_RAYLEIGH_PROXIMITY_AND_SHIFT_TRANSPORT:
    CLASS: MECHANICAL_AFTER_EXTERNAL_SUPPLY
    SHIFT_IDENTITY: exact
    PROXIMITY_SUPPLIER: open_source_specific

PARITY_LOGIC:
  FORM_FLOOR_SPLIT_REQUIRES:
    - K_commutes_with_J
    - q_exactly_even_or_Q_commutes_with_J
  FORM_FLOOR_SPLIT_REQUIRES_HSIMPLE: false
  PARTICULAR_GROUND_VECTOR_HAS_DEFINITE_PARITY_REQUIRES_HSIMPLE: true
  LATE_PARENT_CLAIM_THAT_MIN_SPLIT_REQUIRES_HSIMPLE: rejected_for_form_floor

PRIMARY_VERDICT: ONE_GENUINE_SPECTRAL_WALL_ONE_SEMANTIC_OBJECT_WALL_TWO_MOSTLY_MECHANICAL_LAYERS
NEXT_PRE_GATE: EVEN_ZERO_MODE_HEAD_NONZERO_TAIL_CARRIER_CROSSWALK
NEXT_LEAN_AFTER_PRE_GATE: sourceWeilEvenNonzeroTailAmbientCoercive_explicit

PROVENANCE:
  MYTHOS_2026_08_14:
    COMMIT: f2bbec01849bff69f4e1a9ffe022e906e66cd04c
    READ: true
    INDEPENDENT_CONFIRMATION: false
    CLASSIFICATION: TRANSMISSION_AND_REUSE
  CURRENT_REPO_SOURCE_AUDIT:
    READ: true
    INDEPENDENT_OF_MYTHOS_TEXT: true
    SCOPE: theorem_types_comments_counterexamples_and_late_parent_correction

ROUTE_STATE: CHALLENGER_NOT_RH
G1_STATUS: OPEN
G3_STATUS: OPEN
ROUTE_PROMOTION: false
RH_CLAIM: false
BUS_010: VOID
```

## 1. Итоговый вердикт

`CofinalCCMEvenComplementFloorAtFixedShift` не является одним механическим портом
`Odd → Even`. Четыре недостающих куска имеют разную природу.

| Кусок | Класс | Вердикт |
|---|---|---|
| Nonzero-even tail assembly | смешанный | два analytic bricks переиспользуются; большинство wrappers механичны только после zero-mode carrier lock |
| Exact row parity либо contamination loss | semantic/source contract | не boilerplate; без него `q⊥` может не сохранять parity |
| Uniform even-head floor при fixed `a*` | новая математика | единственная новая spectral/coercivity стена |
| Rayleigh proximity и перенос к `a_j` | transport | algebraic transfer механичен; proximity supplier остаётся отдельным analytic input |

Фраза «десять odd wrappers механически скопировать» допустима только в следующем
ограниченном смысле:

```text
после точного отделения zero mode
и после определения nonzero-even carrier
большинство assembly proofs повторяют odd pattern.
```

Она неверна как описание полной even leg.

## 2. Срочная поправка к позднему parent commit

Пока этот файл создавался, branch получил commit

```text
eb6558f4f7b61b0761c1339684703adc1b3c9f53
```

с тезисом:

> право раскладывать floor как `min(even, odd)` держится на недоказанной `hsimple`.

Для **floor decomposition** этот тезис неверен. Здесь смешаны два разных утверждения.

### 2.1 Form/floor split

Пусть `J` — self-adjoint involution, `B` — Hermitian operator, `BJ=JB`, а domain
разлагается как

```text
H = H_plus ⊕ H_minus.
```

Тогда `B` block diagonal. Для `x=x_plus+x_minus`:

```text
<x,Bx>
  = <x_plus,Bx_plus> + <x_minus,Bx_minus>,
||x||^2
  = ||x_plus||^2 + ||x_minus||^2.
```

Если sector floors равны `beta_plus`, `beta_minus`, то

```text
<x,Bx>
  >= beta_plus  * ||x_plus||^2
   + beta_minus * ||x_minus||^2
  >= min(beta_plus,beta_minus) * ||x||^2.
```

Обратное неравенство для optimal floor получается выбором вектора в каждом отдельном
sector. Поэтому

```text
beta_full = min(beta_plus,beta_minus)
```

без simplicity.

Для production complement требуется дополнительный факт `Jq=q`, чтобы

```text
Q = I - |q><q|
```

коммутировал с `J` и `q⊥` был `J`-инвариантен. Именно row evenness, а не `hsimple`,
является недостающим structural input для floor split.

### 2.2 Parity of one selected ground vector

Если eigenvalue simple и operator commutes with `J`, тогда `Jxi` лежит в том же
одномерном eigenspace, поэтому `xi` имеет definite parity. Здесь `hsimple` действительно
нужна.

При degeneracy mixed ground vectors возможны. Но это не разрушает block decomposition
и не меняет формулу для floor.

Полный counterexample к late-parent тезису. Пусть

```text
H_plus  = span{e_plus},
H_minus = span{e_minus},
B = 0,
J e_plus = e_plus,
J e_minus = -e_minus.
```

Любая смесь

```text
x = alpha e_plus + gamma e_minus
```

является ground vector и не обязана иметь definite parity. Тем не менее

```text
beta_plus = 0,
beta_minus = 0,
beta_full = 0 = min(0,0).
```

Можно сделать positive-floor вариант:

```text
B = I on H_plus ⊕ H_minus.
```

Ground space снова вырожден и допускает смеси, но

```text
beta_plus = beta_minus = beta_full = 1.
```

Значит late-parent observation корректно предупреждает:

```text
mixed particular ground vector is possible without hsimple.
```

Но его перенос на form floor неверен:

```text
sector floor split does not consume hsimple.
```

Использовать `hsimple` для получения самого floor было бы кругом: complement-floor
receiver как раз должен затем поставить simplicity.

## 3. Точный целевой контракт

На одной precommitted cofinal schedule положим

```text
K_j = sourceCCMFiniteMatrix i_j,
q_j = sourceCCMComplexRow S i_j,
a_j = sourceCCMFiniteRayleigh S i_j,
Q_j = I - |q_j><q_j|.
```

Fixed-shift even supplier должен дать fixed scalars

```text
a_star,
beta_star > 0
```

и `j0`, после которого для каждого even `x`, ортогонального `q_j`, выполнено

```text
beta_star * ||x||^2
  <= Re <x,(K_j-a_star I)x>.
```

Затем отдельный source/G3 supplier должен дать

```text
|a_j-a_star| <= beta_star/2.
```

Тогда literal even floor at Rayleigh shift не меньше `beta_star/2`.

Контракт source-faithful только в одном из двух вариантов.

### Exact parity branch

Доказать и экспортировать

```text
J q_j = q_j.
```

Тогда `Q_jJ=JQ_j`, и even/odd floor split точен.

### Contamination branch

Оставить в theorem explicit quantity

```text
sourceCCMComplexOddMass S i_j
```

и доказать quantitative loss через reflection defect. Наличие measurer не заменяет
loss theorem.

## 4. P1 — nonzero-even tail assembly

### 4.1 Что переиспользуется как есть

`D0PstarSourceLowBandModeDecay.lean` содержит два parity-agnostic theorem:

```text
D0PstarSourceLowBandModeDecay.lean:132
  norm_fourier_logWindowZeroExtendedMode_le_lowBand_inv

D0PstarSourceLowBandModeDecay.lean:368
  sum_support_inv_nat_shift_sq_le
```

Первый работает для arbitrary integer frequency `n`. Второй сворачивает
inverse-square support tail. Эти доказательства не надо повторять.

Odd-specific surface дальше выполняет orthonormal mode construction, Fourier
representative identity, Cauchy–Schwarz, Finsupp synthesis, shift, Parseval и integrated
low-band estimate. После корректного carrier lock это в основном wrapper work.

### 4.2 Zero-mode falsifier

Наивный even carrier содержит frequency `n=0`. Возьмём

```text
n=0,
t=0,
T>=0.
```

Тогда denominator в one-mode route:

```text
|L_m*t - 2*pi*n|
  = |L_m*0 - 2*pi*0|
  = 0.
```

И hypothesis generic theorem

```text
2 * L_m * (T+1) <= |n|
```

невозможна: левая часть строго положительна, правая равна нулю.

Следовательно:

```text
full even sector
  = zero mode in finite head
  ⊕ nonzero-even tail.
```

Законный theorem должен называться и типизироваться как theorem о **nonzero-even tail**.
Только после этого большая часть odd wrappers механична.

### 4.3 Классификация P1

```text
generic decay:                         MECHANICAL REUSE
inverse-square summation:              MECHANICAL REUSE
nonzero-even synthesis wrappers:       MOSTLY MECHANICAL
zero-mode/head carrier split:          SEMANTIC PRE-GATE
blind full EvenTail copy:              REJECTED
```

## 5. P2 — source row parity or contamination

Теорема

```text
CCMProposition59SourceTrialFeshbachPreflight.lean:128
  sourceCCMComplexRow_even_of_phaseRealification_even
```

условна. Её docstring прямо говорит:

```text
the necessary source theorem that the current D0Pstar contract does not export.
```

Поэтому exact evenness нельзя считать production fact.

Полный witness того, почему это важно. Пусть

```text
J = diag(1,-1),
q = (e_plus + eps*e_minus)/sqrt(1+eps^2),
eps != 0,
Q = I - |q><q|.
```

Тогда

```text
Jq != q,
QJ != JQ.
```

Вектор

```text
x = (eps*e_plus - e_minus)/sqrt(1+eps^2)
```

лежит в `q⊥`, но не имеет definite parity. Даже при `KJ=JK` compression
`Q(K-aI)Q` может смешивать sectors через `Q`. Формула `min(even,odd)` тогда неприменима
без quantitative error.

На диске есть exact measurer:

```text
D0PstarSourceCCMOddMassReflectionDefect.lean:112
  sourceCCMComplexOddMass_eq_quarter_norm_reflectionDefect_sq
```

со значением

```text
sourceCCMComplexOddMass S i
  = (1/4) * ||sourceCCMFiniteReflectionDefect S i||^2.
```

Это identity, не smallness result и не floor-loss theorem.

Классификация:

```text
exact evenness from current contract:       NOT AVAILABLE
ignore contamination by intention:          REJECTED
export exact source evenness:                VIABLE, inputs missing
carry odd mass with explicit floor loss:     VIABLE, theorem missing
```

## 6. P3 — even-head floor at fixed shift

После P1 tail theorem обслуживает только high nonzero-even modes. Finite/increasing head
содержит zero mode, trial line, same-parity competitors и head-tail correction.

Tail floor не даёт head floor. Полный witness:

```text
H = span{q,y} ⊕ T,
Kq = 0,
Ky = 0,
K|T = I,
a = <q,Kq> = 0,
y ⟂ q.
```

Tail `T` имеет floor `1`. Но `y∈q⊥` и

```text
<y,(K-aI)y> = 0.
```

Никакого positive complement floor нет.

Требуемая новая математика:

```text
exists fixed a_star beta_star>0 j0,
forall j>=j0,
forall even x with <q_j,x>=0,
  beta_star*||x||^2
    <= Re <x,(K_j-a_star I)x>.
```

Это единственная genuine spectral wall в четырёхчастном разложении. Возможные честные
representations:

```text
cofinal fixed-shift Gram certificate family;
Schur/Feshbach corrected head plus analytic tail;
uniform source coercivity on the even complement;
contamination-aware block theorem if P2 takes the nonexact branch.
```

Нельзя использовать desired ground tracking или RH-side convergence для производства
этого floor.

## 7. P4 — Rayleigh proximity and shift transport

Exact identity:

```text
Q(K-a_j I)Q
  = Q(K-a_star I)Q - (a_j-a_star)Q.
```

Из

```text
Q(K-a_star I)Q >= beta_star Q,
|a_j-a_star| <= beta_star/2
```

следует

```text
Q(K-a_j I)Q
  >= (beta_star-|a_j-a_star|)Q
  >= (beta_star/2)Q.
```

Поэтому можно взять один eventual denominator:

```text
beta_j = beta_star/2.
```

Тогда

```text
||residual_j||/beta_j
  <= (2/beta_star)||residual_j||
  -> 0
```

при independently proved residual convergence.

Shift witness, убивающий silent substitution:

```text
K = diag(0,1),
q=e0,
a=<q,Kq>=0.
```

На `q⊥=span{e1}` floor равен `1`. При подмене shift на `a_star=1`:

```text
<e1,(K-I)e1>=0.
```

Каждая единица shift error съедает одну единицу floor.

Классификация:

```text
shift identity:                         MECHANICAL
beta_star/2 deduction:                  MECHANICAL
source proof of Rayleigh proximity:     OPEN ANALYTIC SUPPLIER
derive proximity from desired floor:    CIRCULAR, FORBIDDEN
one-way G3/source import:                LEGAL
```

## 8. Что рассматривалось и отвергнуто

### Blind `Odd -> Even` rename

Отвергнуто: zero mode makes the inverse-frequency hypothesis impossible. Repair:
nonzero-even carrier plus zero mode in head.

### Все десять wrappers полностью механичны

Отвергнуто в буквальном чтении. Они механичны после carrier theorem. До него можно
доказать theorem о неправильном tail.

### Conditional row-evenness как готовый fact

Отвергнуто: line 128 маркирует missing source export.

### Odd contamination «должна быть мала»

Отвергнуто: exact measurer существует, rate и discriminator отсутствуют.

### Even tail floor заменяет full even floor

Отвергнуто finite witness `K=0` on `span{q,y}`, `K=I` on tail.

### Varying-shift floor в каждой клетке

Отвергнуто как более сильная задача. Fixed `a_star` plus proximity supplies one constant
floor.

### Odd correction leaf всё ещё открыт

Отвергнуто фактом:

```text
D0PstarSourceWeilOddTailCorrectionBound.lean:35
  sourceWeilOddTailInverseWeightedCorrection_quadraticForm_le
```

Файл сам запрещает читать этот theorem как corrected-head sign, even floor или cofinal
floor.

### Mythos совпал с Proshka, значит есть два свидетеля

Отвергнуто. Mythos verdict прочитан. Sector split, fixed shift, `beta_star/2` transport и
queue являются transmission, не independent confirmation.

### `hsimple` нужна для form split

Отвергнуто. `hsimple` нужна для definite parity конкретного eigenvector. Block form split
требует commutation and exact row parity, но не simplicity.

## 9. Развилки

### Exact parity или contamination-aware theorem

Обе ветви остаются открыты:

```text
A1 exact source evenness export;
A2 explicit loss from sourceCCMComplexOddMass.
```

Cheapest decisive test: найти source proof phase-realified row evenness. При miss не
продолжать exact block theorem как будто premise доказана.

### Full even tail или nonzero-even tail

Выбран nonzero-even tail. Zero mode belongs to head.

### Varying shift или fixed shift

Выбран fixed `a_star`. Это отделяет floor from unknown ground location.

### Per-cell certificates или cofinal theorem

Выбран cofinal uniform theorem. Fixed cells могут быть plants/certificates, но не занимают
schedule quantifier без family bridge.

## 10. Источники и независимость

### Прочитано напрямую

```text
q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceLowBandModeDecay.lean
q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilOddTailCorrectionBound.lean
q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean
q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceCCMOddMassReflectionDefect.lean
docs/routeB_bus/ROUTE058_GATE_CONTRACTS.md
docs/Progress_Log.md at eb6558f4...
```

Из Lean files независимо подтверждены theorem names, types, comments and exact identities.
Late-parent parity claim independently проверен и разделён на form-level and eigenvector-level
statements.

### Mythos

```text
commit f2bbec01849bff69f4e1a9ffe022e906e66cd04c
q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/
GOAL058_G1_COFINAL_COMPLEMENT_FLOOR_MYTHOS_VERDICT_2026-08-14.md
```

Прочитан. Не является независимым подтверждением.

### Current owner contract

```text
docs/routeB_bus/ROUTE058_GATE_CONTRACTS.md:112-171
```

Контрольная запись повторяет Mythos architecture, фиксирует line-35 closeout and queue.
Она не является second witness.

## 11. Проверяемые адреса

```text
SOURCE AUDIT PIN
  fef398aa75d5ae37012e8a672f80ca5f7d0e5359

LATE CONTROL-PLANE PARENT
  eb6558f4f7b61b0761c1339684703adc1b3c9f53
  docs/Progress_Log.md:40-112

GENERIC LOW-BAND CORE
  q3.lean.aristotle/Q3/Proofs/RouteB/
  D0PstarSourceLowBandModeDecay.lean:132
  norm_fourier_logWindowZeroExtendedMode_le_lowBand_inv

GENERIC INVERSE-SQUARE CORE
  q3.lean.aristotle/Q3/Proofs/RouteB/
  D0PstarSourceLowBandModeDecay.lean:368
  sum_support_inv_nat_shift_sq_le

CLOSED ODD CORRECTION
  q3.lean.aristotle/Q3/Proofs/RouteB/
  D0PstarSourceWeilOddTailCorrectionBound.lean:35
  sourceWeilOddTailInverseWeightedCorrection_quadraticForm_le
  commit c7257228620b50b9cb10450701655ac0abed7b2b

CONDITIONAL ROW EVENNESS
  q3.lean.aristotle/Q3/Proofs/RouteB/
  CCMProposition59SourceTrialFeshbachPreflight.lean:128
  sourceCCMComplexRow_even_of_phaseRealification_even

ODD CONTAMINATION IDENTITY
  q3.lean.aristotle/Q3/Proofs/RouteB/
  D0PstarSourceCCMOddMassReflectionDefect.lean:112
  sourceCCMComplexOddMass_eq_quarter_norm_reflectionDefect_sq
  commit cd848ba27884226396063bba5f9d943c9efc3b51

CURRENT G1 CONTRACT
  docs/routeB_bus/ROUTE058_GATE_CONTRACTS.md:112-171
  commit fef398aa75d5ae37012e8a672f80ca5f7d0e5359

SOURCE PACKET C1-C3
  q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/
  GOAL058_G1_COFINAL_COMPLEMENT_FLOOR_SOURCE_PACKET_2026-08-14.md:170-258
  commit 570e9f84405baeec110c39a3e11cf26a71cc8c1e

MYTHOS VERDICT
  q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/
  GOAL058_G1_COFINAL_COMPLEMENT_FLOOR_MYTHOS_VERDICT_2026-08-14.md:47-101
  commit f2bbec01849bff69f4e1a9ffe022e906e66cd04c
  provenance READ / NOT INDEPENDENT

SIMPLE-EIGENSPACE PARITY THEOREM
  q3.lean.aristotle/Q3/Proofs/RouteB/
  SimpleEvenGroundSectorCriterion.lean:93
  parity_dichotomy_of_simple_eigenspace
  role: parity of a selected eigenvector, not form-floor decomposition
```

## 12. Что не проверено

1. Exact production theorem supplying row evenness не найден и не доказан.
2. Rate for `sourceCCMComplexOddMass` и floor-loss constant не доказаны.
3. Exact nonzero-even ambient carrier в Lean не построен.
4. Число «десять wrappers» не является обещанным размером patch после carrier split.
5. `sourceWeilEvenNonzeroTailAmbientCoercive_explicit` не доказан.
6. Even-head Gram certificate не построен ни для одной cell.
7. Cofinal uniformity не доказана.
8. Source values `a_star`, `beta_star` не определены.
9. Rayleigh proximity supplier не доказан; проверена только algebra.
10. Lean build не запускался: transaction docs-only.
11. `CofinalCCMEvenComplementFloorAtFixedShift` отсутствует как declaration; это target.
12. Late-parent note не менял source files, но его substantive claim audited here.

## 13. FINAL PROPOSAL

Не начинать с ambiguous theorem

```text
sourceWeilEvenTailAmbientCoercive_explicit
```

до фиксации того, исключает ли `EvenTail` zero mode.

Первый source-lock:

```text
D0PstarSourceEvenZeroModeHeadNonzeroTailCrosswalk
```

Он должен зафиксировать:

```text
exact even mode;
exact zero mode;
zero-head + nonzero-tail decomposition;
first nonzero frequency and index map;
nonzero carrier orthonormality;
reuse points for lines 132 and 368;
compatibility with even-head projection and production row.
```

После него первый Lean target:

```text
sourceWeilEvenNonzeroTailAmbientCoercive_explicit
```

После tail theorem настоящий новый target:

```text
CofinalCCMEvenHeadComplementFloorAtFixedShift
```

Затем:

```text
RayleighProximityAtFixedShift
+ exact shift identity
-> literal even floor beta_star/2.
```

Registered predictions:

```text
P-EVEN-1  generic decay and inverse-square sum reuse unchanged.
P-EVEN-2  most nonzero-even wrappers are routine after carrier lock.
P-EVEN-3  first semantic failure is zero-mode indexing or projector compatibility.
P-EVEN-4  genuine proof difficulty is the uniform even-head floor at fixed a_star.
P-PARITY  degeneracy affects parity of a chosen ground vector, not the min-of-sector floor identity.
```

Stop code:

```text
EVEN_FIXED_SHIFT_FLOOR_OPEN_ZERO_MODE_CARRIER_AND_ROW_PARITY_CONTRACT_MUST_PRECEDE_HEAD_CERTIFICATE
```

## 14. STRONGEST ATTACK

Самое сильное возражение:

> Fixed-shift even-head floor может быть почти такой же сложной задачей, как исходный
> full complement floor; трудность только переименована.

Это возможно. P3 не считается автоматически лёгкой. Сжатие всё же строго полезно:

1. zero mode and infinite tail разделены;
2. shift fixed and does not follow unknown Rayleigh sequence;
3. floor is independent of ground location, so circularity is local and auditable;
4. exact parity premise or contamination loss is explicit rather than hidden.

Если после carrier lock and tail theorem corrected even head не имеет uniform positive
lower envelope, certificate family надо убить кодом

```text
FATAL_FOR_THIS_EVEN_HEAD_CERTIFICATE_FAMILY
```

а не продолжать wrapper splitting.

## 15. META CLOSEOUT

**Что стало меньше?**

Even leg распалась на четыре typed obligations. Только P3 является новой spectral
математикой. P2 — semantic source-object wall. P1 and P4 mostly transport.

**Что убито?**

```text
blind Odd->Even copy;
zero mode inside inverse-frequency tail;
exact parity by intention;
tail floor as full complement floor;
per-cell denominator tracking;
Mythos as an independent second witness;
hsimple as a prerequisite for the form-floor sector split.
```

**Что нельзя повторять?**

Нельзя брать `min(even,odd)` без exact row parity or error theorem. Нельзя считать line 35
open. Нельзя выводить proximity из искомого floor. Нельзя путать parity of one eigenvector
with parity block decomposition of the form.

**Current smallest named gap:**

```text
D0PstarSourceEvenZeroModeHeadNonzeroTailCrosswalk
```

**Next cheapest decisive test:**

Найти exact first nonzero source-even frequency и инстанцировать line-132 theorem. Если
carrier включает `n=0`, proposed tail statement malformed and must be split before proof.

**Fate of registered predictions:**

```text
odd correction open: REFUTED by line 35.
two parity-free bricks: CONFIRMED.
ten blind mechanical copies: REFUTED; only nonzero-carrier version survives.
fixed-shift denominator repair: CONFIRMED algebraically, conditional on floor and proximity.
new mathematics concentrated in even head: CONFIRMED, with separate semantic parity wall.
late claim form split needs hsimple: REFUTED; only eigenvector parity needs hsimple.
```

```yaml
iteration:
  target: CofinalCCMEvenComplementFloorAtFixedShift
  status: OPEN
  failed_strategy: blind_odd_to_even_copy_and_parity_eigenvector_form_conflation
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: D0PstarSourceEvenZeroModeHeadNonzeroTailCrosswalk
  invariant_learned: zero mode belongs to head; form split needs projector parity, not ground simplicity
  forbidden_future_move: infer full floor from tail or consume hsimple to justify the split
  next_decisive_test: instantiate_generic_low_band_at_first_nonzero_even_frequency
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```
