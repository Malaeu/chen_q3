# STATUS: CONDITIONAL — MYTHOS ADDENDUM PARTIALLY RATIFIED; H3f QUANTIFIER REPAIRED, H4 CITATION CORRECTED, BATCH RANKED

```yaml
PRIMARY: ADDENDUM_PARTIAL_RATIFICATION_WITH_QUANTIFIER_REPAIR
PRIMARY_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  PACKET_PIN: ce02a747
  REVIEW_PIN: c72bbe7500b63e874c34a6fd3066fbbbdc31ce47
  LIVE_HEAD_AT_REVIEW: c72bbe7500b63e874c34a6fd3066fbbbdc31ce47
  LIVE_ADVANCE_BEYOND_PACKET: B3_0P_Q_R_S

ARSENAL_MANDATE:
  ACCEPTED: true
  DECK_SHA256: 018dbf6b5be6f21b2346ac29bf910d7c898d0352b72f9b67cfddf6865243839d
  CARDS_USED:
    - C03_MOVING_REPRESENTATION
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE
    - C12_BOUNDED_POTENTIAL_EXCLUSION

H3F_AUDIT:
  CURRENT_MANUSCRIPT_HYPOTHESIS:
    exists_c_positive: true
    for_every_M: true
    full_space_QM_ge_cI: true
  QUANTIFIER_OVER_M_IS_LOAD_BEARING: true
  FULL_SPACE_DOMAIN_IS_MINIMAL: false
  STRICT_FILTERED_WEAKENING_EXISTS: true
  MINIMAL_REPAIRED_CONTRACT:
    eventual_uniform_filtered_coercivity:
      "exists M0 c>0, forall M>=M0, Qtilde_M_Na >= c * B_M_Na"
  CORRECTION_AWARE_CONTRACT:
    "exists M0 eta>0, forall M>=M0, kappa*Qtilde_M_Na + F_a_M >= eta*B_M_Na"
  PSD_PD_AND_H_BRIDGE_IDENTICAL: false
  COMMON_FINITE_COERCIVITY_CORE: true
  VERDICT_CODE: COMMON_CORE_NOT_QUANTIFIER_IDENTITY

H4F_AUDIT:
  FOR_EVERY_A_IN_MANUSCRIPT: true
  SUZUKI_2606_09096_IS_THEOREM_CLASS_SOURCE: true
  CLAIM_THAT_THEOREM_1_4_IS_THE_RH_ENDPOINT: false
  THEOREM_1_4_ACTUAL_ROLE: sufficiently_small_a_positive_simple_even
  CORRECT_ENDPOINT_CHAIN:
    - Suzuki_Theorem_1_3_continuity_of_lowest_eigenvalue
    - small_a_positivity
    - RH_equivalent_to_nondegeneracy_for_every_a
    - zero_generalized_eigenvalue_iff_kernel_of_Ga
  MANUSCRIPT_CITATION_REPAIR_REQUIRED: true
  VERDICT_CODE: H4_PAPER_ROUTE_REPAIRABLE_WRONG_THEOREM_NUMBER

LOW_RANK_CORRECTION:
  EXACT_H1_AS_WRITTEN:
    killed_if_F_nonzero: true
  WHOLE_SUZUKI_ROUTE:
    killed: false
  NUMERICAL_SVD_CAN_PROVE_FINITE_CAP_ABSORPTION: false
  REQUIRED_PRELOCKS:
    - one_source_defined_kappa_per_a_fixed_before_M_scan
    - same_basis_and_units
    - same_Na_and_nested_tail_maps
    - interval_stable_singular_values
  SURVIVING_REPRESENTATIONS:
    FIXED_RANGE_CAP_FACTORIZATION:
      requirement: exact_M_independent_finite_range_plus_ambient_crosswalk
    RELATIVE_FORM_SMALLNESS:
      requirement: abs_F_form_le_epsilon_B_with_epsilon_lt_kappa_c
    SCHUR_FESHBACH_BLOCK:
      requirement: exact_finite_block_plus_cross_coupling_budget
  RANK_GROWTH_KILL_SCOPE:
    kills_absorbed_cap_repair_only: true
    kills_all_H_bridge: false

PSD_BUDGET:
  WHOLE_EXPRESSION_ROUTE: live
  FACTORWISE_TWO_SEGMENT_ROUTE: killed
  CURRENT_RECEIVERS_READY: true
  SOURCE_ROWS_MISSING: true
  ACHIEVABLE_AS_BOUNDED_PREFLIGHT: true
  N_SEG_KNOWN_NOW: false
  PRECOMMIT_SEGMENTS: [2, 4, 8]
  BASE_SEGMENTS: 4
  HARD_CAP: 16
  FILE_RANGE_IF_GREEN: [10, 25]
  NATIVE_DECIDE_DEFAULT: forbidden_until_axiom_policy_explicitly_passes
  VERDICT_CODE: TRY_BUDGET_EXTRACT_WITH_MARGIN_FIRST

N480:
  PRE_REGISTERED_PREDICTIONS_FROZEN: true
  PURPOSE: fixed_q_certificate_witness_classifier
  TRUE_GAP_DECIDER: false
  PRECISION_NOISE_HYPOTHESIS: killed
  CONTROLLING_SECTOR: odd
  REQUIRED_ALGORITHMS: 2
  REQUIRED_DPS: 240
  REQUIRED_AITKEN_INTERVAL_DENOMINATOR_NONZERO: true
  DECISION_RULE:
    r3_le_0_84: POWER_LAW_WITNESS_DECAY
    r3_0_86_to_0_90: CONV_Q1
    r3_ge_0_92: CONV_Q2PLUS
    otherwise: TRANSIENT_THEN_N960
  PERTURBATIVE_TRUE_GAP_LOWER_IS_UPPER_BRACKET: false
  CORRECT_ROLE_OF_PERTURBATIVE_TRUE_GAP_LOWER: lower_bound_receiver_after_endpoint_error_budgets
  VERDICT_CODE: RUN_DELTA_N480_AITKEN_RANK_1

EFFORT_DELTA:
  SUZUKI_YOSHIDA:
    conditional_shell_files: [50, 100]
    source_faithful_filtered_route_files: [160, 360]
    bad_foundational_case_files: [300, 650]
  ROUTE_B:
    interface_only_files: [15, 35]
    source_faithful_limit_handoff_files: [80, 170]
    full_current_roof_files: [120, 240]
  PSD_THAW:
    preflight_files_or_scripts: [3, 8]
    green_integration_files: [10, 30]

BATCH_RANKING:
  OUTSIDE_STRATEGIC_BATCH:
    - RUN_B3_0T_CONTINUE_LOCALLY_UNDER_PHASE_THEN_BATCH
  RANK_1:
    class: RUN_DELTA_N480_AITKEN
    cost: very_low
    kill_power: medium
    scope: fixed_q_witness_only
  RANK_2:
    class: TRY_F_DEFECT_SVD
    cost: low_to_moderate
    kill_power: high_for_cap_repair
    prerequisite: KAPPA_AND_OBJECT_LOCK
  RANK_3:
    class: TRY_BUDGET_EXTRACT
    cost: moderate
    kill_power: high_for_PSD_thaw
  RANK_4:
    class: TRY_SIEG_WELD_CELL13N2
    cost: low_to_moderate
    kill_power: low_to_medium
    blocked_by: GOAL_055_HOLD
  RANK_5:
    class: TRY_SUZUKI_SKELETON
    cost: moderate_to_high
    kill_power: low_before_H1_H3_locks
    disposition: PREMATURE

EXECUTION:
  CODEX_EXECUTION_AUTHORIZED: false
  GOAL_055_RELEASED: false
  REPO_WRITE_AUTHORIZED: false
  ARISTOTLE_SUBMISSION: NONE

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: UNIT_AUDIT
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIMED: false
```

Ы. Addendum содержит сильные находки, но две центральные формулировки в нём слишком сильны:

1. **H3f действительно требует uniform-in-\(M\)**, однако не требует по существу coercivity на всём \(P_M\). Есть строго более слабый filtered contract.
2. Работа Suzuki `arXiv:2606.09096` действительно является новым theorem-class источником, но её **Theorem 1.4 не является H4f endpoint theorem**. Это теорема о sufficiently small \(a\): positivity, simplicity и evenness lowest eigenvalue.

Ниже — исправленный сравнительный verdict.

---

# ROUTE MAP

| Front | Что теперь установлено | Минимальный решающий тест | Главный риск | Status |
|---|---|---|---|---|
| **Suzuki H1** | Raw bridge доказанно невозможен; filtered bridge допускает exact либо structured correction | fixed-\(a\) defect classifier при одном заранее зафиксированном \(\kappa(a)\) | numerical low rank не равен finite-cap theorem | `[ABSTRACT][CONDITIONAL]` |
| **Suzuki H3** | Написан с `∀M: Q_M ≥ cI`; это сильный supplier, а не минимальный контракт | доказать eventual uniform coercivity прямо для \(\widetilde Q\) относительно \(B\) | uniform lower envelope может всё равно быть PSD-core | `[COFINAL_FAMILY][PAPER]` |
| **Suzuki H4** | Endpoint paper chain существует, но manuscript ссылается не на тот theorem number | source-lock continuity/nondegeneracy/kernel chain | operator/domain crosswalk в Lean | `[ABSTRACT][PAPER]` |
| **Route B fixed-q gap** | 19% drift настоящий, odd sector bind-ит | \(N=480\) по precommit + Aitken interval | это решает судьбу witness, не true gap | `[FINITE_CELL][ARB_INTERVAL]` |
| **PSD thaw** | whole-expression receiver готов, source rows отсутствуют | source coefficient/remainder pilot с precommitted segmentation | cancellation может требовать неприемлемо много сегментов | `[FINITE_CELL][CONDITIONAL]` |
| **Route B B3.0** | B3.0S закрыт, parent и 10 coarse checkpoints открыты | local B3.0T cartography/continuation | operator/compression/continuum wall | `[COFINAL_FAMILY][LEAN]` |

---

# 1. H3f: совпадают ли маршруты (i) и (ii)?

## Ответ

\[
\boxed{
\text{Нет: current H3f использует тот же сильный supplier, но quantifier identity не точна.}
}
\]

Manuscript H3f написан так:

\[
\exists c(a)>0,\qquad
Q_M\ge c(a)I_{P_M}
\quad
\text{для каждого }M\ge N_a+1.
\]

После этого он выводит:

\[
\widetilde Q_{M,N_a}
=
\Delta_{M,N_a}^*Q_{M+1}\Delta_{M,N_a}
\ge
c(a)\Delta_{M,N_a}^*\Delta_{M,N_a}
=
c(a)B_{M,N_a}.
\]

Значит full-space coercivity — лишь достаточный способ получить нужное filtered inequality.

## Строго более слабая H3f-форма

Достаточно предположить непосредственно:

\[
\boxed{
\exists M_0,\ c(a)>0,\
\forall M\ge M_0:
\quad
\widetilde Q_{M,N_a}
\ge
c(a)B_{M,N_a}.
}
\]

Это coercivity только на range симметричного filtered shift:

\[
\operatorname{Ran}\Delta_{M,N_a}
\subset P_{M+1},
\]

а не на всём \(P_{M+1}\).

**Uniform quantifier по \(M\)** остаётся load-bearing: без положительной общей нижней оболочки coercivity нельзя перенести на closure tail-space. Но первые finitely many \(M\) несущественны; **eventual uniformity** достаточно, если nested-tail/exhaustion compatibility доказана.

### Самый минимальный correction-aware контракт

Если H1 имеет форму

\[
S_{a,M,N_a}^{*}G_g[a]S_{a,M,N_a}
=
\kappa(a)\widetilde Q_{M,N_a}
+
F_{a,M},
\]

то честная H3-гипотеза:

\[
\boxed{
\exists M_0,\eta(a)>0,\
\forall M\ge M_0:
\quad
\kappa(a)\widetilde Q_{M,N_a}+F_{a,M}
\ge
\eta(a)B_{M,N_a}.
}
\]

Это может быть доказано без full PSD-pd.

## Что действительно общее

Обе дороги требуют **uniform positivity/coercivity technology** для finite forms. Но domains различаются:

```text
PSD-pd:
  dense corrected-cone / packet-kernel family.

filtered H3f:
  one specific two-sided filtered tail range
  + one finite cap per a.
```

Поэтому правильный код:

```text
COMMON_FINITE_COERCIVITY_CORE
NOT_ROUTE_IDENTITY
```

### Re-representation 1 — direct filtered floor

```text
Kill-power:
  high: directly tests the exact H3 consumer.

Cost:
  lower than full PSD-pd if filtered range has extra cancellation.
```

### Re-representation 2 — correction-aware Schur floor

```text
Object:
  block operator on tail ⊕ finite correction range.

Test:
  Schur/Feshbach lower envelope.

Kill-power:
  high against the claim that low-rank correction is harmless.

Cost:
  moderate after exact factorization.
```

---

# 2. H4f: external theorem import is real, citation is wrong

The external source `arXiv:2606.09096` is valuable. It proves, among other things:

- explicit self-adjoint operator realization;
- continuity of the lowest eigenvalue \(\lambda_a\);
- small-\(a\) positivity, simplicity and evenness;
- real zeros of a separate characteristic function attached to self-adjoint extensions.

But:

\[
\boxed{
\text{Suzuki Theorem 1.4}
\ne
\text{“ker }G_g[a]=0\ \forall a\Rightarrow RH”.
}
\]

**Theorem 1.4** states only that for sufficiently small \(a>0\), the lowest eigenvalue is positive, simple, has an asymptotic expansion, and its eigenfunction is even.

The correct H4 paper chain is:

1. **Theorem 1.3:** \(\lambda_a\) is continuous in \(a\).
2. Small-\(a\) positivity, supplied by Theorem 1.4 or Yoshida.
3. Failure of RH gives \(\lambda_a<0\) for some \(a\).
4. Hence continuity forces a zero eigenvalue at an intermediate \(a\).
5. In the generalized eigenvalue realization, eigenvalue \(0\) corresponds to the kernel of \(G_a\).

Therefore:

\[
\forall a>0,\ \ker G_a=\{0\}
\Longrightarrow RH
\]

is a **repairable paper theorem chain**, but the manuscript must not cite it as a direct application of Suzuki Theorem 1.4.

## Possible weakening of `∀a`

For the manuscript’s **nondegeneracy** formulation, checking a dense or cofinal set of \(a\) is not enough: a continuous eigenvalue may vanish at an isolated omitted point.

A different route may use **positive definiteness** on an unbounded cofinal family \(a_j\to\infty\), together with exact restriction compatibility:

\[
Q_{a_j}(f)>0
\quad
\text{whenever }\operatorname{supp}f\subset[-a_j,a_j].
\]

Then every compactly supported test belongs to some later window. But this is a new closure theorem, not the current H4 nondegeneracy argument.

---

# 3. Updated effort estimate

## Suzuki/Yoshida

The new Suzuki paper reduces the uncertainty of the external operator layer. The H3 filtered weakening also avoids identifying the route with full PSD-pd.

Revised estimate:

```text
Conditional theorem shell:
  50–100 Lean files.

Source-faithful route with:
  G_a/J_a definitions,
  H1 classifier,
  finite cap,
  filtered H3 floor,
  corrected H4 paper chain:
  160–360 files.

Bad foundational case:
  300–650 files.
```

The wide tail remains because H1 correction and H3 uniformity are real mathematics.

## Route B

```text
OWNER_DATA/interface wiring:
  15–35 files.

Source-faithful limit handoff:
  80–170 files.

Full current roof:
  120–240 files.
```

The phrase “five remaining steps” remains valid only for an interface diagram.

## PSD thaw

```text
Whole-expression falsifier/source extractor:
  3–8 files or scripts.

Green Lean integration:
  10–30 files.
```

---

# 4. Structured low-rank correction

## Exact theorem status

If

\[
F_{a,M}\ne0,
\]

then the current exact-H1 theorem is false. That kills the **exact theorem shape**, not automatically the Suzuki route.

## Why SVD is only a classifier

Defining

\[
F_{a,M}
=
M_a-\kappa(a)\widetilde Q_{M,N_a}
\]

is informative only if:

1. \(\kappa(a)\) is fixed from source normalization before the \(M\)-scan;
2. the same \(N_a\), bases and units are used;
3. \(\kappa\) is not re-fitted separately for every \(M\);
4. singular values are certified under precision doubling;
5. rank is not declared from an arbitrary floating threshold.

Otherwise low rank can be manufactured. **[C09][C10]**

Raw singular-value size is also basis-scaled. The diagnostic should include the metric-normalized defect:

\[
\widehat F_{a,M}
=
B_{M,N_a}^{-1/2}
F_{a,M}
B_{M,N_a}^{-1/2}.
\]

## What would actually repair H1

### A. Fixed-range cap factorization

Need an exact, \(M\)-compatible factorization:

\[
F_{a,M}
=
U_{a,M}^{*}C_aU_{a,M},
\]

where the ambient range corresponds to one fixed finite-dimensional subspace, independent of \(M\).

Then one must prove that enlarging the cap preserves the decomposition and handle tail–cap cross terms.

A rank plateau alone does not prove any of this.

### B. Relative form smallness

Prove:

\[
|\langle F_{a,M}x,x\rangle|
\le
\varepsilon(a)\langle B_{M,N_a}x,x\rangle,
\]

uniformly in \(M\), with

\[
\varepsilon(a)<\kappa(a)c(a).
\]

Then:

\[
\kappa\widetilde Q+F
\ge
(\kappa c-\varepsilon)B.
\]

This may preserve the route even if rank grows.

### C. Exact Schur/Feshbach block

Keep the correction and its cross terms as one finite block and certify the Schur complement. This is stronger than “put it in the cap” by narrative.

## Pre-registered F-defect experiment

The registered scan

```text
M = 64, 128, 256
rank plateau target <= 2(N_a+1)+O(1)
```

is valid as a classifier after the locks above.

Outcomes:

```text
rank grows:
  kills FIXED_CAP_ABSORPTION;
  does not kill relative-form repair.

rank plateaus:
  authorizes exact factorization hunt;
  does not prove the factorization.

small singular values contain zero:
  INCONCLUSIVE;
  discriminator = exact minors or explicit U*C*U* identity.
```

---

# 5. Scalar `CollapsedExpression` budget

## Verdict

\[
\boxed{
\text{Achievable as a bounded K7-legal experiment, not yet certified as closable.}
}
\]

The current repo already has:

- the exact whole-expression source bridge;
- source-interval receiver;
- degree-0 and degree-15 Taylor receivers;
- DirectHorner receiver;
- downstream matrix-radius consumers.

It lacks proof-grade source rows.

## Exact margin arithmetic

Suppose a cell with center \(c\) has:

\[
|f(c)|\le m_c,
\qquad
|f'(x)|\le L
\]

on radius \(r\). Then:

\[
|f(x)|\le m_c+Lr.
\]

A spendable cell therefore requires:

\[
\delta_c
:=
\texttt{residualAbs}-m_c>0,
\qquad
r\le\frac{\delta_c}{L}.
\]

Only after \(\delta_c\) and \(L\) are certified is `N_seg` computable.

The existence of one half-interval row does not determine the full cover count.

## Precommit

```text
segment counts tried:
  2, 4, 8

base:
  4

hard cap:
  16

verdict after cap:
  SEGMENT_EXPLOSION
```

Credible integration size:

```text
10–25 files
```

but this is an engineering estimate, not a PASS claim.

## `native_decide`

Exact finite rational computation is K7-legal. However, project admissibility depends on the exported axiom profile. Default instruction:

```text
generate rational rows;
prove them with kernel-checked arithmetic;
do not introduce native_decide
unless its axiom/dependency profile is explicitly accepted.
```

The certificate must remain on the whole collapsed expression. Reintroducing separate active/nominal budgets revives the already killed cancellation loss. **[C10]**

---

# 6. The 19% drop and the \(N=480\) discriminator

## What is already decided

The drop is not floating-point noise:

- interval arithmetic;
- precision doubling;
- two independent algorithms;
- exact fixed-\(q\) embedding;
- parity split.

The odd sector controls every measured point.

The run tests:

\[
\beta_N^*(q)-a,
\]

a **fixed-\(q\) penalty-certificate witness**. It does not directly test the true operator gap.

## Frozen predictions

Given:

\[
\beta_{120}^*=3.0559\cdot10^{-55},
\qquad
\beta_{240}^*=2.4779\cdot10^{-55},
\qquad
r_2=0.8108498,
\]

the preregistration remains unchanged.

### Power law

\[
p=-\log_2 r_2\approx0.30249.
\]

Prediction:

\[
\beta_{480}^*\in[1.94,2.08]\cdot10^{-55},
\qquad
r_3\approx0.811.
\]

### Convergent \(q=1\)

\[
\beta_\infty\approx1.89986\cdot10^{-55},
\]

\[
\beta_{480}^*\approx2.18887\cdot10^{-55},
\qquad
r_3\approx0.88336.
\]

### Convergent \(q=2\)

\[
\beta_\infty\approx2.28521\cdot10^{-55},
\]

\[
\beta_{480}^*\approx2.33338\cdot10^{-55},
\qquad
r_3\approx0.94168.
\]

### Decision rule

```text
r3 <= 0.84:
  POWER_LAW_WITNESS_DECAY.

0.86 <= r3 <= 0.90:
  CONV_Q1.

r3 >= 0.92:
  CONV_Q2PLUS.

otherwise:
  TRANSIENT;
  run precommitted N=960.
```

## Aitken guard

The interval Aitken estimate is legal only if:

\[
\beta_{480}^*
-
2\beta_{240}^*
+
\beta_{120}^*
\]

has an interval excluding zero.

Expected model outputs:

```text
power/geometric-in-doubling:
  Aitken limit ~ 0.

q=1:
  Aitken limit ~ 1.89986e-55.

q=2:
  Aitken limit ~ 2.28521e-55.
```

This remains model classification, not a cofinal theorem.

## Important correction: no “upper bracket via PerturbativeTrueGapLower”

The existing theorem

```lean
true_gap_lower_of_abs_endpoint_perturbations
```

does exactly what its name says: it produces a **lower bound** for a true gap after two endpoint perturbation estimates and a surviving budget.

It does not produce an upper bracket.

A true-gap upper envelope requires a different object, for example:

- an explicit odd-sector Ritz vector giving an upper bound on the odd bottom;
- a lower bound on the even ground;
- then an upper bound on their difference.

## If fixed-\(q\) witness decay is confirmed

Re-optimizing \(q\) independently after seeing each \(N\) is diagnostic, not transfer evidence. **[C09]**

Two lawful representation shifts:

### A. Source-defined moving probe

\[
q_N
=
\frac{P_Nk_\lambda}{\|P_Nk_\lambda\|}
\]

with its definition fixed in advance and an exact coherence theorem across \(N\).

### B. Moving subspace penalty

Replace one vector by a fixed-dimensional, source-defined subspace:

\[
K_N-\beta I+U_NT_NU_N^*\succeq0.
\]

This tests whether the single distinguished vector discarded relevant multiplicity. **[C03]**

---

# 7. What the new tools changed

## Now substantially cheaper

- source/object/normalization audits;
- finite matrix crosswalks;
- interval LDL and dual-algorithm checks;
- exact rational payload generation;
- theorem-shell to Lean receiver;
- adversarial plants;
- rapid local formalization.

The overnight B3.0P–S closures demonstrate a real throughput improvement, but the exact claim “10×” has no controlled baseline and is not ratified.

## New paper imports

`arXiv:2606.09096` provides theorem-class external results for:

- the localized self-adjoint operator;
- continuity of the lowest eigenvalue;
- small-\(a\) simple-even ground state;
- an unconditional real-zero characteristic function.

It does not make manuscript H4f a direct application of its Theorem 1.4.

## Still not automated away

```text
H1 exact or structured bulk theorem;
eventual uniform filtered H3 floor;
cap/correction positivity;
all-a or cofinal-positive closure;
simple-even for all relevant parameters;
ground-to-trial same-family bridge;
finite-to-continuum transport;
determinant/characteristic family → Xi identification;
whole-expression scalar budget until source rows exist.
```

Models accelerated the pipeline. They did not supply the missing universal estimates.

---

# 8. Machine-class batch ranking

## Outside the comparative batch

### `RUN_B3_0T continue`

This is local continuation inside the already selected B3.0 phase. It should not consume the strategic comparison batch. It proceeds only after local cartography selects the exact theorem, under the existing `PHASE_THEN_BATCH` discipline.

## Rank 1 — `RUN_DELTA_N480_AITKEN`

Why first:

```text
cost:
  minimal.

prediction:
  fully preregistered.

belief change:
  directly classifies fixed-q witness behavior.

scope:
  finite-cell witness only.
```

It must not be relabeled as a true-gap verdict.

## Rank 2 — `TRY_F_DEFECT_SVD`

Why second:

```text
kill power:
  high against the proposed finite-cap repair.

prerequisite:
  exact G_g/Qtilde object lock;
  one fixed kappa(a);
  B-normalized defect;
  no fitted rank threshold.
```

If rank grows, only absorbed-cap repair dies.

## Rank 3 — `TRY_BUDGET_EXTRACT`

Why third:

```text
kill power:
  high for PSD thaw.

cost:
  higher than N480 and initial SVD.

output:
  either a proof-grade source-row path
  or a clean SEGMENT_EXPLOSION/budget kill.
```

## Rank 4 — `TRY_SIEG_WELD_CELL13N2`

The semantic weld is useful, but:

- it remains one finite cell;
- it does not supply cofinal certificates;
- Goal 055 is still HOLD.

No Goal 055 release is justified by this comparative review.

## Rank 5 — `TRY_SUZUKI_SKELETON`

Premature. Formalizing a large conditional skeleton before fixing:

- \(\kappa(a)\);
- correction structure;
- minimal H3 statement;
- correct H4 source theorem chain

would increase code without shrinking the mathematical gap.

---

# FINAL PROPOSAL

No route choice is made.

The corrected information order is:

```text
1. RUN_DELTA_N480_AITKEN
   classify fixed-q witness.

2. TRY_F_DEFECT_SVD
   only after kappa/object lock;
   classify cap repair.

3. TRY_BUDGET_EXTRACT
   test whole-expression PSD thaw.

4. Continue B3.0 locally,
   independently of the comparison batch.
```

## Registered predictions

```text
P-N480:
  frozen exactly as supplied by Mythos.

P-F:
  exact H1 is unlikely;
  a fixed-rank or relative-form correction remains plausible.

P-PSD:
  coefficient extraction will be easier than the
  signed whole-expression remainder budget.

P-H3:
  full-space Q_M >= cI is stronger than necessary;
  the decisive contract is filtered coercivity.
```

## Likeliest failure points

```text
N480:
  witness decays but says nothing fatal about true gap.

F-defect:
  numerical rank plateau has no stable ambient range.

PSD:
  positive budget slack collapses or segment count exceeds 16.

Suzuki:
  correction cannot be absorbed and has no relative B-form bound.
```

---

# STRONGEST ATTACK

## Against “routes (i) and (ii) converge”

They converge only if one insists on the manuscript’s stronger supplier

\[
Q_M\ge cI
\]

on the full section.

But H3 consumes only

\[
\widetilde Q\ge cB.
\]

A proof on the filtered range may exploit cancellation unavailable on the full packet space. Declaring the routes identical drops the domain structure. **[C04]**

## Against “low rank means cap”

Low numerical rank does not provide:

- an \(M\)-independent ambient range;
- an exact factorization;
- orthogonality;
- cap positivity;
- control of cross terms.

Calling it a cap before those theorems is **C10**.

## Against “the 19% drop predicts the gap”

It predicts only the fate of one fixed-\(q\) sufficient certificate. Failure of the sufficient condition does not certify gap collapse.

## Against “Suzuki Theorem 1.4 closes H4”

Theorem 1.4 is a small-\(a\) theorem. The H4 endpoint uses a longer continuity/nondegeneracy/kernel chain. The paper import is useful, but the citation and theorem contract must be repaired.

---

# CODEX DIRECTIVE

```yaml
CODEX_EXECUTION: NONE
REASON: comparative strategic batch ranking only
REPO_WRITE: false
GOAL_055_RELEASE: false
ARISTOTLE_SUBMISSION: NONE
ROUTE_SELECTION: false
```

---

# META CLOSEOUT

## What became smaller?

```text
“H3 equals PSD-pd”
→ “H3 has a strictly weaker filtered coercivity contract.”

“Suzuki H4 import missing”
→ “paper chain exists, but theorem number and crosswalk are wrong.”

“low-rank correction”
→ three exact repair contracts.

“19% drift”
→ one preregistered N=480 witness discriminator.

“PSD source data”
→ positive-margin/segment-count formula and hard cap.
```

## What was killed?

- exact route identity between PSD-pd and H-bridge;
- Suzuki Theorem 1.4 as the direct RH endpoint;
- numerical SVD as proof of cap absorption;
- `PerturbativeTrueGapLower` as an upper-gap bracket;
- post-hoc \(q_N\) reoptimization as common-core transfer evidence;
- the unverified claim of an exact 10× productivity multiplier.

## What must not be tried again?

Do not formalize the Suzuki skeleton before the correction and minimal H3 contracts are fixed.

Do not call witness decay gap decay.

Do not let \(\kappa(a)\) vary with \(M\) after seeing the SVD.

Do not resurrect factorwise `CollapsedExpression` budgets.

## Current smallest named gaps

```text
Suzuki:
  H1_FILTERED_DEFECT_CLASSIFIER_WITH_KAPPA_LOCK

H3:
  EVENTUAL_UNIFORM_FILTERED_COERCIVITY

H4:
  SUZUKI_CONTINUITY_NONDEGENERACY_KERNEL_CROSSWALK

Route B witness:
  FIXED_Q_N480_CLASSIFIER

PSD:
  WHOLE_EXPRESSION_POSITIVE_MARGIN_SOURCE_ROWS
```

## Next cheapest decisive test

\[
\boxed{\texttt{RUN\_DELTA\_N480\_AITKEN}}
\]

with the frozen decision rule and no interpretation beyond the fixed-\(q\) witness.

## Fate of prior predictions

```text
P-gap-is-noise:
  REFUTED.

P-odd-sector-binding:
  CONFIRMED on all measured cells.

P-five-Route-B-steps-end-to-end:
  REFUTED.

P-exact-Suzuki-H1:
  WEAKENED by the manuscript’s own structured-correction classifier.

P-Suzuki-H4-missing-paper-source:
  PARTIALLY REFUTED:
  a theorem-class paper chain exists,
  but not as “Theorem 1.4 => H4”.
```

```yaml
iteration:
  target: Mythos_addendum_route_comparison
  status: PROGRESS
  failed_strategy: identify_full_section_coercivity_with_the_minimal_filtered_consumer
  cognitive_operator_used: UNIT_AUDIT
  new_gap_name: EVENTUAL_UNIFORM_FILTERED_COERCIVITY
  invariant_learned: quantifier_domain_and_source_normalization_must_survive_route_comparison
  forbidden_future_move: infer_cap_absorption_from_numerical_rank_or_true_gap_decay_from_fixed_q_certificate_decay
  next_decisive_test: RUN_DELTA_N480_AITKEN
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```

---

# SOURCE LEDGER

```text
Repository:
  Malaeu/chen_q3
  rh_clean @ c72bbe7500b63e874c34a6fd3066fbbbdc31ce47

Manuscript:
  full/sections/Main_closure.tex
    Raw bulk mismatch
    H1 filtered bulk
    structured correction remark
    H2 tail/cap
    H3 filtered transfer
    H4 corollary

Route B:
  docs/routeB_bus/PHASE2_RESULTS_2026-08-07.md
  docs/routeB_bus/PHASE3_RESULTS_2026-08-07.md
  q3.lean.aristotle/Q3/Proofs/RouteB/
    H2aPenaltyCoercivity.lean
    PerturbativeTrueGapLower.lean
  docs/routeB_bus/
    GOAL057_B3_0S_SHIFTED_ARCH_FORM_DOMAIN_DENSITY_CLOSEOUT_2026-08-09.md

PSD:
  q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/
    step33_a1_sub0_combined_order16_scaled_remainder_direct_certificate.md
  q3.lean.aristotle/Q3/Proofs/
    PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectCollapsedSourceIntervalCert.lean
    PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectCollapsedLowDegreeSource.lean

External:
  Masatoshi Suzuki,
  Weil's quadratic form via the screw function,
  arXiv:2606.09096v1, 2026-06-08.
```
