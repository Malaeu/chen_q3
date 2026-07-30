# STATUS: OPEN — 033 FULL-WINDOW BUDGET CHOSEN; MÜNTZ TARGET REPAIRED
```yaml
PRIMARY_STATUS: OPEN
ROUTE_STATE: CHALLENGER_NOT_RH
SOURCE_MIRROR: cb0cdb99b551729c9f03b74af3d1e1416ba9376f

REQUEST_1:
  CHOSEN_ROUTE: A_FULL_WINDOW_COUPLED_POSITIVE_PART
  NEXT_TRANSACTION: 033_FULL_WINDOW_COUPLED_POSITIVE_PART_BUDGET
  SCOPE: FINITE_CELL_m257
  VERIFIER: ARB_INTERVAL_PLUS_EXACT_RATIONAL_PLUS_PAPER
  CURRENT_SMALLEST_GAP: RemainingWindowPositivePartOrSignSupplier
  POST_033_GAP_IF_GREEN: CofinalFullWindowPositivePartMomentBound
  ROUTES:
    A:
      kill_power: 5
      cost: 3
      verdict: CHOSEN
    B:
      kill_power: 5
      cost: 5
      verdict: DEFERRED_UNTIL_033_PROFILE
    C:
      kill_power: 1
      cost: 2
      verdict: REJECTED_INPUTS_NOT_THEOREM_COMPLETE
      failure_code: S1_ASSEMBLY_INPUT_INSUFFICIENT

REQUEST_2:
  STATUS: POLE_SUBTRACTED_TARGET_READY
  NEW_TASK: EStarMuntzZeroMassContinuation_Standalone_v3_PoleSubtracted
  REMOVE_TARGET: raw_pointwise_riemannZeta_times_Mellin_at_w_eq_1
  REPLACEMENT:
    zeta_factor: analytic_extension_of_(w_minus_1)_times_zeta
    mellin_factor: dslope_of_Mellin_at_1
    regularized_product: zeta_factor_times_mellin_factor
  POLE_VALUE: deriv_Mellin_h_at_1
  RAW_PRODUCT_COROLLARY_DOMAIN: w_ne_1_only

FORBIDDEN:
  - use_022_grid_as_continuum_proof
  - finite_cell_to_cofinal_promotion
  - new_K_or_precision_ladder
  - independent_r_times_epsilon_tail_as_decisive_bound
  - raw_zeta_Mellin_value_at_the_pole
  - pointwise_DualTheta_claim_from_Lebesgue_budget
```

## 1. Adjudication of the three 033 routes

| Route | Kill-power / cost | Decision | Reason |
|---|---:|---|---|
| **(a) One full-window coupled budget** | **5 / 3** | **CHOSEN** | The coupled backend and checker already exist. One run can either produce the complete finite-cell positive-part ledger or expose a genuine coverage/backend obstruction. It directly consumes Theorem C. |
| **(b) Jacobi sign factorization \(D_r\)** | **5 / 5** | **DEFERRED** | The divided-difference and Green identities are proved, but no sign of the forcing pairing or terminal boundary ledger is known. A global \(D_r\)-factorization is a new analytic theorem, not a cheap corollary. |
| **(c) Assemble S1 now** | **1 / 2** | **REJECTED** | The two priority bands cover only the bottom sliver. Transaction 022 is a diagnostic grid report, not a continuum theorem, and leaves 51 entries at the error floor. It cannot occupy the missing S1 quantifier. |

The exact Jacobi identity remains the second representation, not discarded. It is used after 033 only on the band class that actually dominates the certified leakage.

---

# GOAL 033 — FULL-WINDOW COUPLED POSITIVE-PART BUDGET

## STATUS

```text
CHALLENGER / NOT_RH
FINITE CELL m=257 ONLY
No cofinal-family claim.
No pointwise sign claim from the integral budget.
```

## PRIMARY TARGET

```text
033_FullWindowCoupledPositivePartBudget
```

## PURPOSE

Complete the finite-cell lower-half window

\[
z\in\left[\frac1{257},\frac1{\sqrt{257}}\right]
\]

by producing one exact lower envelope for every tooth-band portion, then convert those envelopes into a rigorous weighted positive-part budget for

\[
E_\star(h_\lambda,u),\qquad u=\lambda z,\quad \lambda=\sqrt{257}.
\]

This transaction closes the finite-cell instance of

```text
RemainingWindowPositivePartOrSignSupplier
```

by the positive-part branch. It does not prove pointwise `DualThetaDominance`, S1 on a cofinal family, or RH.

## SOURCE LOCKS

Consume, without reconstruction:

```text
026_lambda_bracket_resume.answer.md
LAMBDA_BRACKET_RESUME_AUDIT.json

027_hlambda_outer_lobe_gate.answer.md

030_coupled_full_sum_response.answer.md
COUPLED_FULL_SUM_RESPONSE_CERT.json
coupled_full_sum_response_certificate.py
check_coupled_full_sum_response_certificate.py

031_priority_band_positive_part.answer.md
PRIORITY_BAND_POSITIVE_PART_CERT.json
priority_band_positive_part_certificate.py
check_priority_band_positive_part_certificate.py

032_bridge_reverification.answer.md
RiemannBoundaryCellBridge.lean
```

Required hash locks:

```text
030 certificate:
2e31e67ba9cc9aed78bfed9ed20d052c1917b508958ddff077124e2cf95989da

031 certificate:
86191e9eb8772dd013dbeb7347c1484b910109dbe5a4a2b24562e43211b937c9
```

Keep:

```text
m = 257
lambda = sqrt(257)
canonical phase = '+'
delta_q = (b_(4,q)-b_(0,q))/2
delta_0 = 0 exactly
core_q = 440
tail_q = 700
tau_response = 2^-512
live terminal cone = [0,1/2]
midpoint/star convention unchanged
```

No new depth or precision escalation is authorized.

## EXACT BAND OBJECTS

For every integer \(r\),

\[
S_r(z)=\sum_{q\ge0}\delta_q A_{r,q}(z),
\qquad
A_{r,q}(z)=\sum_{n=1}^{r}P_{2q}(nz).
\]

The required window consists of:

```text
partial top band:
  r=16:
  J_16 = [1/17, 1/sqrt(257)]

full bands:
  r=17,...,256:
  J_r = [1/(r+1), 1/r]
```

Thus the complete lower-half window has 241 band portions. Transactions 030–031 already cover \(r=255,256\); 033 must recompute them as regression controls, not silently import their sign.

### Irrational endpoint guard

`1/sqrt(257)` is not rational.

The exact rational Bernstein cover must therefore do one of:

1. use an algebraic endpoint representation with the relation \(257z^2=1\); or
2. use a rational outer endpoint \(z_{16}^+\) and prove exactly
   \[
   \frac1{\sqrt{257}}\le z_{16}^+<\frac1{16}
   \]
   by integer-square inequalities.

If option 2 is used, the lower envelope is certified on the larger interval
\([1/17,z_{16}^+]\), while the analytic integral is taken only to the true endpoint
\(1/\sqrt{257}\).

Pretending that `1/sqrt(257)` is an exact rational endpoint is a fatal coverage bug.

## COUPLED BACKEND

For every band portion:

1. build one whole-response polynomial containing all coefficient centers through \(q=700\);
2. add outward only:
   - the coefficient-box response uncertainty;
   - the certified infinite response remainder beyond \(q=700\);
3. compute exact rational lower and upper envelopes
   \[
   L_r\le S_r(z)\le U_r
   \quad(z\in J_r);
   \]
4. define
   \[
   \varepsilon_r:=\max(0,-L_r).
   \]

Forbidden final estimate:

\[
r\left(\varepsilon_0/J_0+\varepsilon_4/J_4\right).
\]

The independent mode sup-tail may appear only in the regression plant.

No sign-driven subdivision. A fixed, source-recorded rational subdivision policy may be used for coefficient-size control. Every subcell and every junction must appear in the coverage ledger.

## EXACT POSITIVE-PART CONSUMER

Source-locked Theorem C gives

\[
E_\star(h_\lambda,\lambda z)
=
-\frac{I_0I_4}{D}\sqrt{\frac z\lambda}\,S_\lambda(z),
\qquad
\frac{du}{u}=\frac{dz}{z}.
\]

Put

\[
C_\lambda:=\frac{I_0I_4}{D}>0.
\]

For every \(0\le\sigma<1/2\), prove

\[
\Delta_{257,\sigma}^{+}
:=
\int_{1/\lambda}^{1}
\max(E_\star(h_\lambda,u),0)\,u^{-\sigma}\,\frac{du}{u}
\]

satisfies

\[
\boxed{
\begin{aligned}
\Delta_{257,\sigma}^{+}
\le {}&
C_\lambda\lambda^{-\sigma-\frac12}
\frac{1}{\frac12-\sigma}
\Bigg[
\varepsilon_{16}
\left(
\lambda^{\sigma-\frac12}
-
17^{\sigma-\frac12}
\right)\\
&\quad+
\sum_{r=17}^{256}
\varepsilon_r
\left(
r^{\sigma-\frac12}
-
(r+1)^{\sigma-\frac12}
\right)
\Bigg].
\end{aligned}
}
\]

Output both:

```text
Delta_full_over_C_lambda(sigma)
Delta_full(sigma) with an outward interval for C_lambda
```

Do not treat a stored decimal for \(C_\lambda\) as exact.

The already proved upper-half result \(E_\star\le0\) on \(u\in[1,\lambda]\) is imported from 027. Hence no positive-part contribution is omitted above \(u=1\).

## TEETH LEDGER — SEPARATE FROM THE INTEGRAL

The teeth in the window are exactly

```text
r = 17,...,257
z = 1/r
```

Transaction 031 already covers \(r=255,256,257\); 033 must recompute them as regression controls and certify the remaining 238 teeth.

For each tooth form the exact star response

\[
S_r^\star
=
\sum_{q\ge0}\delta_q
\left(
\sum_{n=1}^{r-1}P_{2q}(n/r)+\frac12P_{2q}(1)
\right).
\]

Teeth have Lebesgue measure zero and do not enter \(\Delta_{257,\sigma}^{+}\).

Return exactly one secondary tooth flag:

```text
ALL_WINDOW_TEETH_NONNEGATIVE_PROVED
```

iff every tooth lower envelope is nonnegative;

```text
POINTWISE_DUALTHETA_KILLED_AT_TOOTH
```

iff some tooth upper envelope is strictly negative;

```text
TOOTH_SIGN_INCONCLUSIVE
```

otherwise.

Likewise, a strict upper envelope \(U<0\) on any predeclared rational band subcell may emit:

```text
POINTWISE_DUALTHETA_KILLED_ON_BAND_SUBCELL
```

This secondary kill does not invalidate the positive-part budget.

## REQUIRED OUTPUTS

For each band portion:

```text
r
exact domain / subcover
center lower and upper
coefficient uncertainty
infinite response remainder
L_r
U_r
epsilon_r = max(0,-L_r)
coverage-complete flag
```

For each tooth:

```text
r
exact star value ball
lower
upper
PASS / KILL / INCONCLUSIVE
```

Aggregate:

```text
vector epsilon_16...epsilon_256
argmax epsilon_r
top 20 band contributions for sigma = 0, 1/10, 1/4, 2/5, 9/20
Delta_full_over_C_lambda at those diagnostic sigma values
symbolic all-sigma formula
```

The diagnostic sigma table is not the theorem. The symbolic formula is.

## K1 PLANTS

### P1 — priority regression

Recomputed \(r=255,256\) lower envelopes and \(\varepsilon_r\) must agree with 031 exactly after source normalization.

### P2 — complete band cover

Delete one band or one rational subcell. The coverage checker must fail.

### P3 — junction mutation

Shift one shared endpoint so that a gap or overlap appears. The exact cover ledger must fail.

### P4 — irrational top endpoint

Replace \(1/\sqrt{257}\) by \(1/16\), or by an uncertified decimal. The partial-band endpoint guard must fail.

### P5 — old independent tail

Replace the coupled response tail by the old \(r\varepsilon_\Psi\) bound. It must reproduce a materially wider 029-style enclosure and must not enter the verdict.

### P6 — terminal ratio zero

Set the live terminal ratio to zero. The response enclosure must change and the plant must fire.

### P7 — source phase

Flip the mode-4 phase. The \(\delta_0\) lock or priority regression must fail.

### P8 — Jacobian / weight

For a symbolic control \(S(z)=-1\), dropping \(du/u=dz/z\) or the factor
\(\lambda^{-\sigma-1/2}\) must give a different closed form.

### P9 — diagnostic is not proof

Attempt to replace a missing exact band envelope by a row from transaction 022. The checker must reject the record because 022 is diagnostic and does not certify a continuum interval.

### P10 — tooth mutation

Change finitely many tooth values. The aggregate Lebesgue budget must remain unchanged, while the tooth ledger must change.

### P11 — coefficient centers as exact

Suppress coefficient-box uncertainty. The certificate must reject the mutation even if the numerical center is tiny.

## PRIMARY VERDICT CODES

Return exactly one:

```text
FULL_WINDOW_POSITIVE_PART_BUDGET_PROVED
```

iff all 241 band portions are covered, every \(\varepsilon_r\) is rigorous, and the all-\(\sigma\) aggregate formula is proved.

```text
FULL_WINDOW_COUPLED_RESPONSE_BACKEND_GAP
```

iff the existing coupled response representation cannot certify one or more band portions without a new depth/precision ladder.

```text
FULL_WINDOW_COVERAGE_GAP
```

iff all band portions or junctions are not exactly covered.

```text
FULL_WINDOW_PARTIAL_ENDPOINT_GAP
```

iff the \(r=16\) algebraic endpoint cannot be source-locked.

```text
FULL_WINDOW_SOURCE_LOCK_MISMATCH
```

iff 030/031 regression controls fail.

## FORBIDDEN

```text
no new K or dps ladder
no r*epsilon_Psi as final tail
no 022 grid rows as continuum proof
no claim that an integral budget proves pointwise sign
no omission of r=16 partial band
no omission of any tooth from the separate pointwise ledger
no finite-cell to cofinal-family promotion
no S1 or RH claim
no modification of Lemma A / 027
no STATE mutation
no Bus 010
```

## ARTIFACTS

```text
033_full_window_positive_part.answer.md
FULL_WINDOW_POSITIVE_PART_CERT.json
full_window_positive_part_certificate.py
check_full_window_positive_part_certificate.py
FULL_WINDOW_BAND_PROFILE.csv
FULL_WINDOW_TOOTH_LEDGER.csv
```

The independent checker must import neither the generator nor Arb/flint. It must rebuild exact rational responses, the cover, the aggregate formula, and P1–P11 from the certificate payload.

## REGISTERED PREDICTIONS

```text
P033-1:
  The coupled backend closes all bands at the frozen q=700 depth.

P033-2:
  The full budget is dominated by interior bands, not r=255,256.

P033-3:
  At least one remaining tooth is negative or zero-compatible; this does not
  affect the Lebesgue budget.

P033-4:
  The finite-cell result exposes a band-profile law but does not itself provide
  a cofinal-family bound.
```

No retroactive changes after the run.

---

# REPAIRED ARISTOTLE TARGET — POLE-SUBTRACTED MÜNTZ CONTINUATION

## TASK

```text
EStarMuntzZeroMassContinuation_Standalone_v3_PoleSubtracted
```

## CONTEXT

Keep all green T1–T3 work and the locally reverified boundary-cell bridge.

The old T4/T5 must not ask for the raw pointwise value

\[
\zeta(1)M_h(1).
\]

Zero mass gives \(M_h(1)=0\), but the punctured product generally has the nonzero removable value \(M_h'(1)\).

The theorem-facing object is a pole-subtracted analytic continuation.

## SETUP

Keep the v2 assumptions and definitions:

```text
h, b, hb, K, hsupp, hlip, hmass, Lambda, hLambda
Estar
Mellin
Gwin
Rminus
Rplus
```

Put

\[
M_h(w):=\operatorname{Mellin}(h)(w),
\qquad
\mathbb H:=\{w\in\mathbb C:0<\Re w\}.
\]

## NEW DEFINITIONS

### 1. Mellin zero quotient

Use Mathlib's derivative-corrected slope:

```lean
noncomputable def MellinDivOne (w : ℂ) : ℂ :=
  dslope (Mellin h) 1 w
```

Required identities:

```text
MellinDivOne 1 = deriv (Mellin h) 1

w != 1 ->
MellinDivOne w
  = (Mellin h w - Mellin h 1) / (w - 1)

hmass ->
w != 1 ->
MellinDivOne w
  = Mellin h w / (w - 1)
```

Prove `MellinDivOne` analytic on \(\mathbb H\).

At \(w=1\), use the analytic `dslope` power-series theorem. Away from \(1\), use the ordinary quotient formula.

### 2. Residue-removed zeta factor

Define an analytic extension, not the raw zeta value:

```lean
noncomputable def ZetaResidueFactor (w : ℂ) : ℂ :=
  Function.update
    (fun z => (z - 1) * riemannZeta z)
    1
    1
```

Required identities:

```text
ZetaResidueFactor 1 = 1

w != 1 ->
ZetaResidueFactor w
  = (w - 1) * riemannZeta w
```

Prove `ZetaResidueFactor` analytic on \(\mathbb H\).

At \(w=1\):

- use `riemannZeta_residue_one` for continuity of the updated factor;
- use differentiability of zeta on the punctured neighborhood;
- apply the removable-singularity theorem.

The task may instead return an existential analytic witness with these three fields if the explicit `Function.update` definition causes avoidable API friction:

```lean
exists Z1,
  AnalyticOnNhd ℂ Z1 H
  and Z1 1 = 1
  and forall w in H, w != 1 ->
        Z1 w = (w-1) * riemannZeta w
```

Do not weaken the mathematical content.

### 3. Pole-subtracted product

```lean
noncomputable def ZetaMellinPoleSub (w : ℂ) : ℂ :=
  ZetaResidueFactor w * MellinDivOne h w
```

Required theorem:

```text
zetaMellinPoleSub_analyticOn :
  AnalyticOnNhd ℂ (ZetaMellinPoleSub h) H
```

Off the pole:

```text
w in H ->
w != 1 ->
ZetaMellinPoleSub h w
  = riemannZeta w * Mellin h w
```

At the pole:

```text
ZetaMellinPoleSub h 1
  = deriv (Mellin h) 1
```

No theorem may identify this value with the raw Mathlib expression
`riemannZeta 1 * Mellin h 1`.

## REPAIRED T4

```text
T4a:
  Mellin h is analytic on H.

T4b:
  Mellin h 1 = 0.

T4c:
  MellinDivOne h is analytic on H.

T4d:
  ZetaResidueFactor is analytic on H.

T4e:
  ZetaMellinPoleSub h is analytic on H.

T4f:
  off-pole equality with riemannZeta * Mellin.

T4g:
  pole value equals deriv (Mellin h) 1.
```

## REPAIRED T5

Assume the already proved absolute-region identity:

\[
G_{\rm win}(s)
=
\zeta(s+\tfrac12)M_h(s+\tfrac12)
-
R^-(s)-R^+(s)
\]

for \(\Re s>1/2\).

Prove, for every \(\Re s>-1/2\),

\[
\boxed{
G_{\rm win}(s)
=
\operatorname{ZetaMellinPoleSub}(s+\tfrac12)
-
R^-(s)-R^+(s).
}
\]

Use the identity theorem on the connected half-plane.

Then derive two separate corollaries.

### Raw-product corollary, punctured only

If \(s\ne1/2\),

\[
G_{\rm win}(s)
=
\zeta(s+\tfrac12)M_h(s+\tfrac12)
-
R^-(s)-R^+(s).
\]

### Pole-value corollary

At \(s=1/2\),

\[
\boxed{
G_{\rm win}(\tfrac12)
=
M_h'(1)
-
R^-(\tfrac12)
-
R^+(\tfrac12).
}
\]

This is the theorem that replaces the false raw pointwise statement.

## PLANTS

### PL1 — mass-carrying source

Keep the triangular positive-mass plant. It must fail the zero-mass bound and display the \(\lambda^\sigma\) pole growth.

### PL2 — raw value mismatch

Keep the zero-mass difference of triangular bumps with

\[
M_h'(1)<0.
\]

Prove:

```text
ZetaMellinPoleSub h 1 = deriv (Mellin h) 1 != 0
```

while the raw pointwise expression at \(w=1\) is not used as the continuation value.

The plant must reject any theorem asserting:

```text
ContinuousAt (fun w => riemannZeta w * Mellin h w) 1
```

with the raw Mathlib point value.

### PL3 — factor cancellation

For \(w\ne1\), mutate either factor:

```text
drop (w-1) from ZetaResidueFactor
or
drop division by (w-1) from MellinDivOne
```

The off-pole equality must fail.

## IMPORTS / EXPECTED MATHLIB API

```text
Mathlib.Analysis.Calculus.DSlope
Mathlib.Analysis.Analytic.IsolatedZeros
Mathlib.Analysis.Complex.RemovableSingularity
Mathlib.NumberTheory.LSeries.RiemannZeta
```

Expected key API:

```text
dslope
dslope_same
HasFPowerSeriesAt.has_fpower_series_dslope_fslope
Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
riemannZeta_residue_one
differentiableAt_riemannZeta
AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
```

Exact theorem names may be adapted to the pinned Mathlib version, but the target semantics may not drift.

## FORBIDDEN

```text
no raw zeta*Mellin value at w=1
no claim raw product is continuous/differentiable at w=1
no replacement of the removable value by 0
no global Lipschitz assumption on the zero extension
no claim Mellin h is entire
no new axiom, sorry, admit, native_decide
no RH or zeta-zero input
no STATE mutation
```

## VALIDATION

```text
lake env lean <touched-file>
lake build
grep sorry/admit/axiom/native_decide <touched-files>

#print axioms:
  MellinDivOne analytic theorem
  ZetaResidueFactor analytic theorem
  ZetaMellinPoleSub analytic theorem
  continued window identity
  punctured raw corollary
  pole-value corollary
  PL1
  PL2
  PL3
```

Required axiom profile:

```text
[propext, Classical.choice, Quot.sound]
```

## RETURN EXACTLY ONE

```text
ESTAR_MUNTZ_POLE_SUBTRACTED_CONTINUATION_PROVED
```

```text
MELLIN_DSLOPE_ANALYTICITY_GAP
```

```text
ZETA_RESIDUE_FACTOR_EXTENSION_GAP
```

```text
IDENTITY_THEOREM_GLUE_GAP
```

```text
RIEMANN_SUM_BOUNDARY_CELL_GAP
```

Do not return the vague code `ZETA_POLE_API_GAP`; the repaired contract separates the two genuine API fronts.

---

# ROUTE MAP

```text
033:
  full finite-cell positive-part budget
  → exact band profile
  → next gap: cofinal full-window moment bound

Jacobi identity:
  held in reserve
  → applied only to dominant/worst band class after 033

Müntz:
  T1–T3 retained
  → dslope Mellin quotient
  + residue-removed zeta factor
  → analytic pole-subtracted product
  → continued window identity
```

# STRONGEST ATTACK

## Against 033

A full finite-cell budget may be numerically impressive but structurally useless for S1 if no uniform law in \(m\) emerges.

Response:

```text
033 is the last authorized full-window finite-cell enumeration.
After it, no cell ladder.
The next theorem must be cofinal/parametric or the route pivots to the Jacobi representation.
```

## Against the Müntz repair

An analytic function that merely agrees with the raw product off \(w=1\) could be introduced as an opaque witness and hide the wrong pole value.

Response:

```text
the witness must carry:
  analyticOn;
  exact off-pole equality;
  exact value at one = deriv Mellin 1;
  uniqueness on the half-plane by the identity theorem.
```

# META CLOSEOUT

- **What became smaller?**  
  The remaining finite-cell S1 supplier is one all-window \(\varepsilon_r\)-ledger. The zeta-pole problem is split into two explicit analytic factors.

- **What was killed?**  
  Immediate S1 assembly from 031+022; raw `ζ·Mellin` at the pole; another depth/precision ladder.

- **What must not be tried again?**  
  Treating 022 diagnostics as continuum proof, using `r*epsilon_Psi`, or assigning the raw product its removable value by declaration.

- **Current smallest named gaps:**  
  `033_FullWindowCoupledPositivePartBudget` and `ZetaResidueFactorExtension`.

- **Next cheapest decisive tests:**  
  Full-window frozen-depth response run; compile `ZetaResidueFactor` and `MellinDivOne` before re-running T5.

- **Fate of prior registered predictions:**  
  R1 confirmed; R2 confirmed; R3 confirmed; R4 confirmed by scope. No retroactive repair.

- **Progress class:**  
  `PROOF_PROGRESS + REPRESENTATION_PROGRESS`.

- **Route score:**  
  `5/5`.
