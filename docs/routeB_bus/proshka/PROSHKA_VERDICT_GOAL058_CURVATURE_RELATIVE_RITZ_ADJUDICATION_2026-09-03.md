# STATUS: OPEN — RUN_RELATIVE_RITZ_DECISIVE_TEST; CURVATURE–VITALI PRESERVED, FIXED ABSOLUTE-FLOOR INTERFACE REJECTED
```yaml
PRIMARY: RUN_RELATIVE_RITZ_DECISIVE_TEST
PRIMARY_COUNT: 1
STATUS: OPEN
OPERATIVE_CLASS: RUN_RELATIVE_RITZ_DECISIVE_TEST

REQUEST:
  REQUEST_ID: REQ-2026-09-03-CURVRITZ
  RELATED_REQUEST_ID: REQ-2026-09-03-MOVINGNODE
  BOUNDARY_ID: GOAL058_CURVATURE_RELATIVE_RITZ_ADJUDICATION
  REQUEST_COMMIT: f5931f4a75056e66f911747e118a0522a76616e5
  REQUEST_PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_CURVATURE_RELATIVE_RITZ_ADJUDICATION_2026-09-03.txt
  REQUEST_GIT_BLOB: 13ea6a841016fbf89fd7185b3d73bb6dd6a53250
  REQUEST_SHA256: ec333554f2010af4ad4fdccbfba961acdf1cbc4925f614f39ccda4502a81a7ce
  SOURCE_BASE_COMMIT: 860a7438fdaf0e7806d02c989e1fd07ad6bfb887
  VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_CURVATURE_RELATIVE_RITZ_ADJUDICATION_2026-09-03.md

MATERIALIZED_PRIOR_CHAT_VERDICT:
  PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_CURVATURE_VITALI_PRODUCTION_RATE_REPAIR_2026-09-03.md
  GIT_BLOB: 9d504200b9622dd057bf7fdeed6bf93ddec4c5d4
  SHA256: d223590282a439ff1bde4dbc341770e9b3f90d811e2dc83b4542d26f56f1c4f9
  BYTES: 24320
  VERBATIM_COPY: true

DIAGNOSTIC_CHECKPOINT_AT_ADJUDICATION:
  COMMIT: b25c91b54471015bb85cee3eed9c30f70d59b0da
  REPORT_PATH: docs/routeB_bus/phase5_scripts/out/edge_ledger_probe2_probe3.md
  REPORT_GIT_BLOB: c4af0bd8abfbd9df71c8f659410200302fbf3526
  LEDGER_PATH: docs/routeB_bus/phase5_scripts/out/edge_ledger.json
  LEDGER_GIT_BLOB: aea1080362fde652b30eb422fd05729a66ba563d
  SCHEDULE_COMPLETE: false
  KAPPA_PARTIAL: [0.02589626740503931, 0.026263016505022364, 0.025843056802214937]
  RATIO_SIGMA_0_4_PARTIAL: [1.077583772, 1.078128476, 1.077474187]
  FUCHS_FIXED_PRIME_KERNEL_L_VARIATION: REFUTED_WRONG_VARIATION_OBJECT
  INTERPRETATION: DIAGNOSTIC_NEVER_A_PROOF

PHASE_KEY:
  PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
  ROUTE_ID: RouteB_TwoLevelSpectralLadder
  FRONT_ID: GOAL058_G1_G3_COFINAL_GROUND_TRACKING
  SOURCE_OBJECT_FAMILY_ID: PROPOSITION59_CCM_FINITE_BOTTOM_GROUND_FAMILY
  TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
  CHANGED: false

PRIMARY_DECISION:
  CURVATURE_VITALI_LOGIC: PRESERVED
  MOVING_NODE_LOGIC: RATIFIED_WITH_RATE_INTERFACE_REPAIR
  DIRECT_KAPPA_BRANCH: PRIMARY_ANALYTIC_BRANCH
  RELATIVE_RITZ_BRANCH: RUN_AS_INPUT_A_DIAGNOSTIC_AND_INTERFACE_PREFLIGHT

SCOPED_FINDINGS:
  FIXED_ABSOLUTE_COMPLEMENT_FLOOR_COFINAL_INTERFACE: REJECT_TARGET_SHAPE
  INF_ABSOLUTE_GAP_POSITIVE_TARGET: KILL_TARGET_SHAPE_NOT_MATHEMATICAL_NEGATION
  B_K_VIA_CURRENT_FIXED_BETA_R_K: QUARANTINE_AS_REOPENED_TRACKING_RATE
  RELATIVE_RITZ: CORRECT_NEW_INTERFACE_NOT_A_REWRITE
  DIRECT_CURVATURE_FUNCTIONAL: GAP_FREE_AND_NONCIRCULAR_IN_PRINCIPLE
  HUMP_MASS_BOUND: NOT_REQUIRED_BY_THIS_ROUTE

NO_REOPENING_CONDITION_FOR_B_K: >-
  A polylogarithmic B_k bound is not a reopening only if a new source-specific
  theorem proves the exact weighted scalar quotient on the same family and
  schedule before any operator-norm estimate, permits a varying per-cell floor,
  and uses neither a uniform positive absolute floor nor an equivalent bound on
  the inverse shifted complement. Merely replacing the old exponential compact
  weight by L^(5/2) while retaining the same unproved fixed-beta r_k is a reopening.

RELATIVE_CONSUMER:
  projective_error: p_k = 1 - abs(inner(xi_k,q_k))^2
  relative_gap: g_k = lambda2_k / lambda1_k
  relative_excess: epsilon_k = Rayleigh(q_k) / lambda1_k - 1
  supplier_bound: p_k <= epsilon_k / (g_k - 1)
  input_A_sufficient_rate: abs(A_k)^2 * L_k * epsilon_k / (g_k - 1) -> 0
  joint_curvature_fallback: abs(A_k)^2 * L_k^5 * epsilon_k / (g_k - 1) = O(1)
  joint_curvature_fallback_is_necessary: false

SECONDARY_CODES:
  - KILL_FIXED_ABSOLUTE_COMPLEMENT_FLOOR_AS_COFINAL_INTERFACE
  - KILL_ABSOLUTE_GAP_TARGET_SHAPE
  - KILL_B_K_POLYLOG_FALLBACK_AS_CURRENT_INTERFACE
  - PRESERVE_DIRECT_CURVATURE_FUNCTIONAL_WITHOUT_GAP
  - REPAIR_INPUT_A_TO_PROJECTIVE_ERROR_OR_RELATIVE_RITZ_SUPPLIER

CHEAPEST_NEXT_ACTION:
  code: HARVEST_PRECOMMITTED_EDGE_LEDGER_WITH_RELATIVE_RITZ_COLUMNS
  duplicate_run: false
  required_columns:
    - lambda1_k
    - lambda2_k
    - g_k = lambda2_k / lambda1_k
    - Rayleigh(q_k)
    - epsilon_k = Rayleigh(q_k) / lambda1_k - 1
    - eta_k = epsilon_k / (g_k - 1)
    - abs(A_k)^2 * L_k * eta_k
    - abs(A_k)^2 * L_k^5 * eta_k
    - kappa_k
    - kappa_forced_k
  schedule: m = N in [13, 23, 43, 83, 163]
  N_checks: [[13, 26], [43, 86]]
  interpretation: DIAGNOSTIC_NEVER_A_PROOF

FALSIFIERS:
  KAPPA_NEGATIVE:
    condition: a precision-stable certified upper envelope U(kappa_k) < 0
    meaning: object, convention, eigenvector, or real-zero premise mismatch
  RELATIVE_RITZ_DENOMINATOR_INVALID:
    condition: lower envelope L(lambda1_k) <= 0 or L(g_k - 1) <= 0
    meaning: the multiplicative interface is not typed on that cell
  RELATIVE_RITZ_CANCELLATION_UNRESOLVED:
    condition: epsilon_k or eta_k fails precision and N-geometry stability
    meaning: do not promote finite diagnostics into a cofinal supplier
  P59_CURVATURE_DUAL_CERT_REOPENS_ABSOLUTE_GAP:
    condition: every proposed dual certificate first bounds an inverse by 1/(lambda2-lambda1)
    meaning: reject that representation and move to the next scalar representation

PREDICTION_FATES:
  P_ABS_GAP_COLLAPSES:
    probability: 0.80
    fate: UNRESOLVED
    note: partial m <= 83 rows strongly support it; the frozen rule requires m = 163
  P_CURVATURE_SOURCE_1:
    probability: 0.65
    fate: UNRESOLVED
    note: partial m = 13,23,43 rows are positive and flat within factor 1.016; the frozen rule requires the complete schedule and N-checks
  P_FUCHS_IDENTITY_NUMERICALLY_HOLDS:
    probability: 0.55
    fate: REFUTED
    note: refuted only for the tested fixed-prime kernel-parameter-L variation; it is not the domain-only Fuchs/Hadamard variation
  P_GROUND_RATIO_GROWS_AT_SIGMA_0_4:
    probability: 0.60
    fate: UNRESOLVED
    note: partial m = 13,23,43 rows are flat near 1.078 and strongly adverse to growth; the frozen rule requires the complete schedule and N-checks
  P_JOINT_PROJECTIVE_RATE_1:
    probability: 0.38
    fate: UNRESOLVED
    note: severe adverse update; eigenvalue scale alone does not bound the exact residual ratio, but the current fixed-beta cofinal interface is rejected
  P_RELATIVE_RITZ_STRICTLY_WEAKER:
    probability: 0.70
    fate: REFUTED
    note: the relative theorem is not a rewrite of the existing Lean floor interface; its weaker scale-invariant core survives only as a new interface
  P_DIRECT_FUNCTIONAL_BEATS_FULL_TRACKING_1:
    probability: 0.72
    fate: UNRESOLVED
    note: partial flat positive kappa data favor the representation, but no source theorem or complete schedule has closed the claim
  P_MOVING_NODE_STRICTLY_WEAKER_THAN_COMPACT_DECAY:
    probability: 0.70
    fate: CONFIRMED
    note: bounded curvature plus a same-tail lattice rate is logically sufficient and does not imply the old full compact scalar-decay hypothesis

LEAN_EDIT_PERFORMED: false
NUMERICAL_RUN_PERFORMED: false
JUDGE_KERNEL_RERUN: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
HONESTY_STATE: CHALLENGER_NOT_RH
BUS_010: VOID

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5
NEXT_LOAD_BEARING_GAP: P59_CURVATURE_DUAL_ANNIHILATOR_OR_SCALAR_SCHUR_IDENTITY
```

## ROUTE MAP

| Route / object | Verdict | Decisive test | Main risk | Tags |
|---|---|---|---|---|
| Curvature → normality → Vitali → ZeroEscape | **VIABLE, OPEN** | Uniform source bound for \(\kappa_k\) plus same-tail lattice identification | The two-order cancellation in the exact ground row may fail | `[COFINAL_FAMILY][CONDITIONAL]` |
| Relative Ritz supplier for Input A | **VIABLE NEW INTERFACE** | Compute and then prove \(\eta_k=\varepsilon_k/(g_k-1)\) at the exact source scale | A bound for \(\varepsilon_k\) may itself import an absolute denominator | `[COFINAL_FAMILY][CONDITIONAL]` |
| Current fixed-\(\beta\) residual/floor interface | **REJECT AS COFINAL TARGET SHAPE** | A source theorem would have to supply one positive absolute floor for all cells | Collapsing absolute spectrum makes the interface stronger than the consumer needs | `[COFINAL_FAMILY][PAPER]` |
| Direct scalar \(\kappa\) functional | **SELECTED ANALYTIC BRANCH** | Exact dual/Schur identity before taking an operator norm | Hidden use of \((K-\lambda_1)^{-1}\) reintroduces the absolute gap | `[COFINAL_FAMILY][CONDITIONAL]` |

The primary action is **RUN**, not **TRY**, because the production ledger and Probe 4 are already precommitted and running. This verdict does not start a duplicate computation. It only fixes the quantities and interpretation to harvest.

## 1. Source-lock and scope audit

The authoritative request is `REQ-2026-09-03-CURVRITZ`, Git blob
`13ea6a841016fbf89fd7185b3d73bb6dd6a53250`, SHA-256
`ec333554f2010af4ad4fdccbfba961acdf1cbc4925f614f39ccda4502a81a7ce`, at request commit
`f5931f4a75056e66f911747e118a0522a76616e5`.

The previous chat verdict is now frozen verbatim as Git blob
`9d504200b9622dd057bf7fdeed6bf93ddec4c5d4`. Its three predictions are therefore scoreable without reconstructing their wording.

The six-field phase key is unchanged. The source object remains the same Proposition-59 finite bottom-ground family, on the same production schedule and normalization. No object switch, second extraction, new diagonal, route promotion, or RH claim is authorized. `[COFINAL_FAMILY][PAPER]`

## 2. Q1 — the absolute-floor interface

### Ruling

The current Lean ratio is literally

\[
r_k=\frac{\|\operatorname{Residual}_k\|^2}{\beta^2},
\]

where one positive real `beta` is threaded through the selected cofinal family. The predicate `complexTrialComplementFloor` is an absolute lower bound for the shifted trial-complement block. It is not a relative spectral statement. `[FINITE_CELL][LEAN]`

The observed small eigenvalue scale does **not**, by itself, prove that the dimensionless ratio \(r_k\) diverges: an exact source residual could in principle collapse at the same or a faster rate. Therefore this verdict does not claim

\[
B_k\not=O(1)
\]

as a mathematical theorem.

What is killed is the **current target shape**:

```text
one fixed beta > 0
for every cell of the growing production family.
```

That target is stronger than either Input A or curvature normality requires, and the classical/diagnostic evidence points in the opposite scaling direction. `[COFINAL_FAMILY][PAPER]`

The two polylog consumers

\[
|A_k|\sqrt{L_k}\sqrt{r_k}\to0,
\qquad
|A_k|L_k^{5/2}\sqrt{r_k}=O(1)
\]

remain the stopped tracking architecture if `r_k` is supplied only by the same fixed absolute floor. A smaller weight does not change the source of the unproved quotient.

### Exact non-reopening condition

The polylog route is genuinely new only if a source theorem proves the exact weighted scalar quotient directly, before taking a full complement-resolvent norm, with a per-cell floor or no floor at all. The proof must preserve the signed full CCM residual and must not assume:

- `inf_k beta_k > 0`;
- `inf_k (lambda2_k - lambda1_k) > 0`;
- a bound on `||(Q(K-aI)Q)^(-1)||` by an absolute spectral gap;
- the old compact transform-decay conclusion.

Under those restrictions the theorem would be a new cancellation theorem. Without them, \(B_k\) is merely the stopped rate with \(L^{5/2}\) replacing the old complex-strip envelope. `[COFINAL_FAMILY][PAPER]`

## 3. Q2 — exact relative Ritz theorem

Let \(K\) be Hermitian on a finite-dimensional complex Hilbert space. Assume:

1. \(K\xi=\lambda_1\xi\), \(\|\xi\|=1\);
2. \(0<\lambda_1<\lambda_2\);
3. for every \(u\perp\xi\),
   \[
   \langle u,Ku\rangle\ge\lambda_2\|u\|^2;
   \]
4. \(\|q\|=1\), with \(R(q)=\langle q,Kq\rangle\).

Write \(q=d\xi+u\), \(u\perp\xi\). Then

\[
R(q)
\ge
\lambda_1|d|^2+\lambda_2\|u\|^2
=
\lambda_1+(\lambda_2-\lambda_1)\|u\|^2.
\]

Hence

\[
\boxed{
1-|\langle\xi,q\rangle|^2
\le
\frac{R(q)-\lambda_1}{\lambda_2-\lambda_1}
=
\frac{\varepsilon}{\lambda_2/\lambda_1-1},
}
\]

where

\[
\varepsilon=\frac{R(q)}{\lambda_1}-1.
\]

This theorem is correct. `[FINITE_CELL][PAPER]`

It is **not** a rewrite of `complexTrialComplementFloor`. The Lean floor is centered at the trial line and its trial Rayleigh value; the relative theorem is centered at the exact ground eigenpair and assumes an exact lower spectral bound on the ground complement. A new structure or theorem adapter is required. `[FINITE_CELL][LEAN]`

For the current consumer, the clean object is not a gap but the projective error

\[
p_k=1-|\langle\xi_k,q_k\rangle|^2.
\]

Relative Ritz is one supplier:

\[
p_k\le\eta_k,
\qquad
\eta_k:=\frac{\varepsilon_k}{g_k-1},
\qquad
g_k:=\frac{\lambda_{2,k}}{\lambda_{1,k}}.
\]

Then Input A needs only

\[
\boxed{
|A_k|^2L_k\eta_k\to0.
}
\]

The one-rate fallback that also controls the second jet is

\[
\boxed{
|A_k|^2L_k^5\eta_k=O(1),
}
\]

but this is sufficient, not necessary. `[COFINAL_FAMILY][CONDITIONAL]`

### When the absolute rate returns

If \(\varepsilon_k\) is obtained only from the residual

\[
v_k=\|(K_k-R(q_k))q_k\|^2,
\]

Temple's inequality, under \(R(q_k)<\lambda_{2,k}\), gives

\[
R(q_k)-\lambda_{1,k}
\le
\frac{v_k}{\lambda_{2,k}-R(q_k)}.
\]

If additionally

\[
R(q_k)-\lambda_{1,k}\le\theta(\lambda_{2,k}-\lambda_{1,k}),
\qquad \theta<1,
\]

then

\[
\frac{R(q_k)-\lambda_{1,k}}{\lambda_{2,k}-\lambda_{1,k}}
\le
\frac{1}{1-\theta}
\frac{v_k}{(\lambda_{2,k}-\lambda_{1,k})^2}.
\]

So a proof of the relative excess through Temple/residual alone reimports the absolute squared-gap denominator. Conversely, if the normalized spectral width satisfies

\[
\lambda_{\max,k}-\lambda_{1,k}
\le C(\lambda_{2,k}-\lambda_{1,k}),
\]

then

\[
\frac{v_k}{(\lambda_{2,k}-\lambda_{1,k})^2}
\le C
\frac{R(q_k)-\lambda_{1,k}}{\lambda_{2,k}-\lambda_{1,k}}.

\]

Under both side conditions the two interfaces are comparable up to constants. No such spectral-width theorem is currently supplied. Therefore the relative overlap target is genuinely weaker as a consumer, but not a literal replacement theorem for the existing Lean object. `[FINITE_CELL][PAPER]`

## 4. Q3 — ranked noncircular attacks on the curvature cancellation

Define the exact finite functional

\[
\ell_N(\xi)
=
\frac{\xi_0}{12}
+
\frac{1}{2\pi^2}
\sum_{0<|n|\le N}\frac{\xi_n}{n^2}.
\]

The exact normalized curvature is

\[
\kappa_k
=
\frac{L_k^2}{2}\frac{\ell_{N_k}(\xi_k)}{\xi_{k,0}}.
\]

Thus the source theorem must prove

\[
\frac{\ell_{N_k}(\xi_k)}{\xi_{k,0}}=O(L_k^{-2}).
\]

### R1 — `P59_CURVATURE_DUAL_ANNIHILATOR`

Seek an explicit source-defined row \(u_k\), scalar \(c_k=O(L_k^{-2})\), and controlled remainder \(s_k\) such that

\[
\ell_{N_k}-c_ke_0
=
(K_k-\lambda_{1,k}I)^*u_k+s_k.
\]

Pairing with the exact ground row kills the operator term and leaves only

\[
\ell_{N_k}(\xi_k)=c_k\xi_{k,0}+\langle s_k,\xi_k\rangle.
\]

This attacks the requested scalar directly and can preserve exact Arch–Prime cancellation. `[COFINAL_FAMILY][CONDITIONAL]`

First failure point: the only construction of \(u_k\) is numerical inversion or an estimate

\[
\|u_k\|\lesssim(\lambda_{2,k}-\lambda_{1,k})^{-1}.
\]

That would reopen the absolute-gap route.

```yaml
kill_power: 10/10
proof_cost: 3/10
```

### R2 — `P59_CURVATURE_CENTER_SCHUR_STIELTJES`

Split the exact even matrix and ground row at the central coordinate:

\[
K_k=
\begin{pmatrix}
a_k&b_k^*\\
b_k&D_k
\end{pmatrix},
\qquad
\xi_k=\xi_{k,0}
\binom{1}{-(D_k-\lambda_{1,k}I)^{-1}b_k}.
\]

Then the curvature bracket is one scalar resolvent pairing. Seek a continued-fraction, Stieltjes, interlacing, or sign identity for that pairing, not an operator-norm bound. `[COFINAL_FAMILY][CONDITIONAL]`

First failure point: no source sign/interlacing theorem for the full signed CCM block, or the proof immediately estimates the resolvent norm by the absolute complement floor.

```yaml
kill_power: 9/10
proof_cost: 5/10
```

### R3 — `P59_CURVATURE_FUCHS_WINDOW_VARIATION`

The tested variation is now rejected: changing the kernel parameter `L` while freezing the prime set changes the kernel formula internally and is not the domain-only Fuchs/Hadamard variation. Its observed derivative has the wrong sign for the proposed transplant, and the Hellmann–Feynman / finite-difference check does not meet the original identity contract. `[FINITE_CELL][PAPER]`

A source-faithful Fuchs route remains logically possible only after defining a fixed-form, fixed-carrier domain variation and then proving a separate crosswalk back to the production schedule, where the window, prime cutoff, and dimension move together. It remains ranked below R1 and R2. `[COFINAL_FAMILY][CONDITIONAL]`

First failure point: no exact same-object domain-variation family exists, or the crosswalk to the discrete schedule loses the requested two-order cancellation.

```yaml
kill_power: 8/10
proof_cost: 7/10
status: QUARANTINED_PENDING_EXACT_VARIATION_OBJECT
```

### R4 — full reduced resolvent tracking

A direct operator-norm estimate of

\[
(K_k-\lambda_{1,k}I)^{-1}_{\xi_k^\perp}
\]

pays \((\lambda_{2,k}-\lambda_{1,k})^{-1}\) before using the special \(1/n^2\) functional. Reject this representation unless an exact scalar cancellation occurs before the norm is taken. `[COFINAL_FAMILY][PAPER]`

```yaml
kill_power: 10/10
proof_cost: 2/10
status: CHEAP_KILL
```

## 5. Q4 — compatibility with the 2026-08-28 stop rules

The curvature route is compatible with the stop rule

```text
do_not_use_real_zeroness_as_a_global_normality_bound
```

because real-zeroness is not used alone. The argument also requires:

```text
evenness;
order at most one;
real-axis reality;
nonzero central anchor;
a uniform bound on the scalar curvature kappa_k.
```

These hypotheses produce a quantitative product bound. `[ABSTRACT][PAPER]`

The current \(B_k\) fallback is not compatible with

```text
do_not_reopen_the_stopped_tracking_rate
```

while it imports the same fixed-\(\beta\) `r_k`. It stays quarantined unless it satisfies the exact non-reopening condition stated in the machine block. `[COFINAL_FAMILY][PAPER]`

## 6. Q5 — the absolute gap target

Reject the Step-3 target

\[
\inf_k(\lambda_{2,k}-\lambda_{1,k})>0
\]

as the production target shape. This is a strategic kill, not a proof that the infimum is zero. It is stronger than the consumer needs, conflicts with the observed absolute scale, and is disfavored by the classical finite-section picture. `[COFINAL_FAMILY][PAPER]`

Replace it by the multiplicative complement statement

\[
\boxed{
\forall u\perp\xi_k,
\quad
\langle u,K_ku\rangle
\ge
g_k\lambda_{1,k}\|u\|^2,
\qquad g_k>1,
}
\]

plus the source rate

\[
\boxed{
|A_k|^2L_k\,
\frac{\varepsilon_k}{g_k-1}
\longrightarrow0.
}
\]

The most stable consumer interface should expose the projective envelope \(p_k\le\eta_k\); it should not require any particular supplier to be called a gap theorem. Relative Ritz, a direct overlap theorem, or a Schur graph theorem may all feed the same port. `[COFINAL_FAMILY][CONDITIONAL]`

The normality branch remains independent:

\[
\sup_k\kappa_k<\infty.
\]

## 7. Premise → source → consumer → residual-gap matrix

| Premise / object | Exact source or theorem | Downstream consumer | Residual gap | Tags |
|---|---|---|---|---|
| Even, order \(\le1\), real on \(\mathbb R\), real zeros, \(G(0)=1\), bounded \(\kappa\) | Hadamard/Laguerre–Pólya product; prior center-repair verdict | Direct local boundedness, then Vitali | Uniform source bound for \(\kappa_k\) | `[ABSTRACT][PAPER]` |
| P59 removable-pole kernel and exact normalization | `Proposition59EntireTransform.lean`; observer symbolic audit | Exact finite curvature row and Lean checker | Formal second-jet identity and finite norm theorem | `[FINITE_CELL][LEAN]` + `[FINITE_CELL][PAPER]` |
| External lattice zeros \(|j|>N\) | Common sine numerator and absent removable denominator | Schedule admissibility | Lean/source wrapper for the cofinal arithmetic, not a new schedule | `[COFINAL_FAMILY][PAPER]` |
| Relative Ritz | Ground decomposition theorem in §3 above | Projective overlap supplier for Input A | Source bound for \(\varepsilon_k\), exact \(g_k\), and a new interface adapter | `[FINITE_CELL][PAPER]` |
| Direct \(\kappa\) functional | Exact second-jet formula | Normality of the same finite real-zero ground family | Two-order cancellation of \(\ell_N(\xi)/\xi_0\) | `[COFINAL_FAMILY][CONDITIONAL]` |
| Uniform absolute gap | Existing fixed-`beta` complement-floor architecture | Old residual/floor tracking supplier | Target shape rejected; replace by projective/relative port | `[COFINAL_FAMILY][LEAN]` + `[COFINAL_FAMILY][PAPER]` |

## 8. Lean-ready work versus new mathematics

### Lean-ready bookkeeping

The following are source-locked finite or abstract statements and may be formalized without pretending to close the cofinal route:

1. `proposition59RawTransform_secondDerivative_zero`;
2. coefficient-functional norm squared `1/80`, hence norm `1/sqrt(80)`;
3. the finite relative Ritz theorem under an exact ground-complement lower bound;
4. the arithmetic fact \((\log m)^2/m\to0\) on `m=N=k+2`;
5. the abstract even real-zero curvature product bound, or a narrower P59-specific variant if the general entire-function library is too expensive.

These statements are presently `[FINITE_CELL][PAPER]` or `[ABSTRACT][PAPER]`; they are suitable for later Lean formalization but do not supply the cofinal source bounds.

### New analytic work

The load-bearing new mathematics is:

1. a uniform source bound for \(\kappa_k\), preferably through R1 or R2;
2. a source theorem for the multiplicative Rayleigh excess \(\varepsilon_k\), or a direct projective-overlap theorem;
3. the cofinal weighted relative rate for Input A;
4. fixed-carrier window variation if R3 is pursued.

All four are `[COFINAL_FAMILY][CONDITIONAL]`.

## FINAL PROPOSAL

Preserve the Curvature–Vitali route. Do not spend another theorem on a positive uniform absolute gap. The partial checkpoint is favorable to direct curvature: the three landed values of \(\kappa_k\) are positive and flat within a factor about `1.016`, while the moment ratio at \(\sigma=0.4\) is also flat. This is diagnostic support, not a cofinal bound. Harvest the already-running ledger once, with the relative Ritz columns added if they are already available from the same eigenpair data. Use only the frozen Probe-1 and Probe-4 verdict rules; all new relative quantities remain descriptive until separately precommitted. `[FINITE_CELL][ARB_INTERVAL]`

After the ledger lands:

- if `KAPPA_NEGATIVE` fires with a certified upper envelope below zero, stop and audit the object/convention before any proof; it has not fired on the partial checkpoint;
- if \(\kappa_k\) is positive and stable under precision and the \(N\)-checks, attack `P59_CURVATURE_DUAL_ANNIHILATOR` first;
- if the dual identity necessarily pays an absolute reduced-resolvent norm, kill it and move to `P59_CURVATURE_CENTER_SCHUR_STIELTJES`;
- use relative Ritz only for Input A, not as a forced supplier for normality.

No numerical row can prove the cofinal bound. Its job is to select the representation.

## STRONGEST ATTACK

The strongest reviewer objection is:

> The ratio \(\|r_k\|/\beta_k\) and the relative Ritz quotient are both dimensionless. Tiny absolute eigenvalues alone do not prove that the former is mathematically impossible or that the latter is strictly easier to prove.

This objection is correct.

The repair is the central distinction of this verdict:

- the **current Lean interface** demands one fixed positive absolute floor and is the wrong cofinal target shape;
- the **mathematical residual ratio** could still be small through exact source cancellation, so its negation is not certified;
- the **relative Ritz theorem** weakens the consumer because it asks only for Rayleigh excess/projective overlap, but it becomes the old rate again if \(\varepsilon_k\) is supplied only through Temple plus an absolute-gap residual bound.

Therefore the route is not declared solved and the residual route is not declared mathematically false. What is killed is the unnecessarily strong interface and the plan to make it the mainline.

## CODEX DIRECTIVE

No new Codex transaction is authorized by this paper adjudication. Codex may continue its already assigned, nonoverlapping Lean bookkeeping for the abstract curvature bridge and exact P59 second jet. It must not edit `phase5_scripts`, alter the numerical precommit, or promote any finite diagnostic to a cofinal theorem.

## META CLOSEOUT

- **What became smaller?** The former joint `absolute residual / absolute gap` wall split into a gap-free scalar curvature wall and a scale-invariant projective Input-A wall.
- **What was killed?** One fixed positive absolute floor on the cofinal production family, the `inf absolute gap > 0` target shape, and the current `B_k` fallback through fixed-\(\beta\) `r_k`.
- **What must not be tried again?** Bounding the full reduced resolvent before applying the special \(1/n^2\) functional; calling relative Ritz a definitional rewrite of the existing floor object; using finite eigenvalue rows as a universal theorem.
- **Current smallest named gap:** `P59_CURVATURE_DUAL_ANNIHILATOR_OR_SCALAR_SCHUR_IDENTITY`.
- **Next cheapest decisive test:** finish and harvest the frozen Probe-1/Probe-4 schedule at `m=163` and the two \(N\)-geometry checks, then append relative Ritz columns without inventing a post-hoc asymptotic threshold.
- **Fate of prior predictions:** recorded in the machine block without changing any probability.
- **Memory entry:** direct curvature is the normality mainline; relative projective error is an independent Input-A supplier; fixed absolute floor is no longer a cofinal consumer.
