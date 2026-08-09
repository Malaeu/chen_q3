# STATUS: OPEN — B3.0N EXPLICIT GLOBAL ARCHIMEDEAN LOWER-BOUND PREFLIGHT SELECTED; PRODUCTION FORBIDDEN

```yaml
PRIMARY: TRY_GOAL057_B3_0N_ARCH_SYMBOL_EXPLICIT_GLOBAL_LOWER_BOUND_PREFLIGHT
PRIMARY_COUNT: 1
OPERATIVE_CLASS: TRY_GOAL057_B3_0N_ARCH_SYMBOL_EXPLICIT_GLOBAL_LOWER_BOUND_PREFLIGHT
OPERATIVE_CLASS_COUNT: 1

CLASSIFICATION: SCRATCH_ONLY_EXACT_LEAN_PREFLIGHT
RELEASE_CLASS:
  untracked_preflight: AUTHORIZED
  production_materialization: FORBIDDEN
  repository_write: FORBIDDEN
  route_state_write: FORBIDDEN

NO_PRODUCTION_AUTHORIZATION_IN_THIS_VERDICT: true

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean

  CONTROLLING_REQUEST:
    path: PROSHKA_REQUEST_GOAL057_B3_0_POST_M_NEXT_NODE_ADJUDICATION_2026-08-09.txt
    sha256: f2cdd45f4efe36c27b6546b0e37ca1b674dfe6861e8e12d778b6d05fc51d86c2
    bytes: 15069
    wc_lines: 418
    final_LF: true
    utf8: PASS
    read_byte_for_byte: true

  HEAD:
    expected: 21334efd24c05050ee482426af6dcd8e8f43842c
    observed_pin: 21334efd24c05050ee482426af6dcd8e8f43842c
    origin_rh_clean_equals_head: true
    status: PASS

  EXECUTION_STATE:
    stage: RB-GOAL-057-B3-0M-CLOSED
    obligation: GOAL057_B3_0_POST_M_NEXT_NODE_ADJUDICATION
    successor_previously_authorized: false
    status: PASS

  STAGED_PATCH:
    expected_sha256: 291e2387203c579f3f56bd5994daa7225c575c06a37fb3144b13e04e6d1b4f7b
    must_remain_byte_identical: true

CLOSED_PARENT:
  child: B3_0M
  theorem: sourceWeilFiniteFourierLedger_eq_ccmWeilMatrixForm
  production_sha256: 27cc612c2de2e2da9c7e30e21e9663e96abba7c80a2bc5286d04e02b7c9274a6
  retained: true
  reopened: false
  ambient_form_claim: false
  form_domain_claim: false
  operator_claim: false

ARCHIMEDEAN_SIGN_RULING:
  exact_symbol:
    sourceArchimedeanMultiplier_t:
      -Real.log_Real.pi_plus_re_digamma_one_fourth_plus_I_pi_t
  exact_normalization:
    sourceArchimedeanMultiplier_t_eq_neg_a_star_t_div_two_pi
  large_abs_t_asymptotic:
    log_abs_t_plus_O_t_inverse_square
  eventual_sign: STRICTLY_POSITIVE
  wrong_negative_tail_hypothesis: KILLED

GLOBAL_SHIFT_RULING:
  finite_constant_shift_exists: true
  selected_explicit_shift:
    abs_log_pi_plus_log_4_plus_6
  selected_theorem:
    sourceArchimedeanMultiplier_add_explicitShift_nonneg
  numerical_fitting_used: false
  form_or_operator_premise_used: false

D0_2_SIGN_CROSSWALK:
  source_ledger: W02_MINUS_WR_MINUS_PRIME
  Fourier_ledger: W02_PLUS_ALREADY_NEGATIVE_ARCH_MINUS_POSITIVE_PRIME
  sign_match: PASS
  ambient_sign_repair_required: false

WHOLE_SPACE_BOUNDED_COMPONENTS:
  W02:
    paper_status: BOUNDED_RANK_TWO_POLE_COMPONENT
    production_Lean_extension: MISSING
  Prime:
    paper_status: FINITE_SUM_OF_BOUNDED_SELFADJOINT_SHIFT_OPERATORS
    production_Lean_extension: MISSING

SELECTED_CHILD:
  id: GOAL057_B3_0N_ARCH_SYMBOL_EXPLICIT_GLOBAL_LOWER_BOUND_PREFLIGHT
  scratch_path:
    q3.lean.aristotle/Goal057B3_0N_ArchSymbolLowerBound_Scratch.lean
  future_candidate_production_path_NOT_AUTHORIZED:
    q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarExactArchSymbolLowerBound.lean

  exact_imports:
    - Q3.Proofs.RouteB.D0PstarExactArchSymbolLogDomination

  namespace: Q3.RouteB.D0Pstar

  public_surface_ceiling:
    definitions: 0
    theorems:
      - sourceArchimedeanMultiplier_add_explicitShift_nonneg
    total: 1

  private_surface_ceiling:
    definitions: 0
    theorems:
      - b3_0n_one_fourth_le_norm_sourceArchimedeanArgument
      - b3_0n_sourceArchimedeanStieltjesCorrection_le
      - b3_0n_sourceArchimedeanStieltjesRemainder_le
    total: 3

EXACT_CANDIDATE:
  sha256: ecefe92d6fc0056f92562326944ca040f2eff6a417e59335580925004f0d06e9
  bytes: 4488
  wc_lines: 125
  final_LF: true
  forbidden_token_matches: 0
  judge_reran_Lean: false
  direct_Lean_required_before_any_release: true

PREFLIGHT_STOP:
  GOAL057_B3_0N_ARCH_SYMBOL_EXPLICIT_GLOBAL_LOWER_BOUND_PREFLIGHT_FAILED

PREFLIGHT_SUCCESS:
  GOAL057_B3_0N_ARCH_SYMBOL_EXPLICIT_GLOBAL_LOWER_BOUND_PREFLIGHT_PROVED

SPECIFIC_STOPS:
  - GOAL057_B3_0N_STIELTJES_LOWER_BOUND_API_GAP
  - GOAL057_B3_0N_ARCH_SYMBOL_SIGN_ORIENTATION_MISMATCH
  - GOAL057_B3_0N_FINITE_SHIFT_NOT_PROVED
  - SURROGATE_BY_PREMISE_NOT_SOURCE_CONSTRUCTION
  - ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK

NEXT_GAP_AFTER_PREFLIGHT_SUCCESS:
  GOAL057_B3_0O_SHIFTED_ARCH_MULTIPLIER_FORM_DOMAIN_PRIMITIVE

NEXT_GAP_AUTHORIZED: false

CHECKPOINT_EFFECT:
  current_checkpoint: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
  effect: STRICTLY_ADVANCED_NOT_CLOSED
  coarse_checkpoints_closed: 0
  coarse_checkpoints_remaining: 10

ARSENAL:
  mandate_accepted: true
  cards_applied:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

SCOPE: ABSTRACT
VERIFIER: CONDITIONAL_UNTIL_EXACT_LEAN_PREFLIGHT
PROGRESS_CLASS: REPRESENTATION_PROGRESS
CHILD_PROGRESS_IF_PROVED: PROOF_PROGRESS
COGNITIVE_OPERATOR: UNIT_AUDIT
ROUTE_SCORE: 5

PHASE:
  phase_key_change: false
  reuse_same_living_chat: true
  open_fresh_chat: false

FINAL_BOUNDARY:
  route: CHALLENGER_NOT_RH
  active_bus_goal: 057
  bus_010: VOID
  goal_055: HOLD
  g2_ccm: FROZEN
  h4a1b: OPEN
  Aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
  sole_owner_gate: PX_RH_CLAIM
```

## 1. Source-lock ruling

The attached request was read byte-for-byte and independently rehashed to SHA-256 `f2cdd45f…d86c2`, 15,069 bytes, 418 `wc` lines, with a final LF. It fixes B3.0M as closed, B3.0 as open, the coarse ledger at `0/10`, and forbids production authorization in this adjudication.  `[ABSTRACT][PAPER]`

The live execution state at commit `21334efd24c05050ee482426af6dcd8e8f43842c` independently records:

```text
RB-GOAL-057-B3-0M-CLOSED
GOAL057_B3_0_POST_M_NEXT_NODE_ADJUDICATION
OPEN_ADJUDICATION_REQUIRED_NO_SUCCESSOR_AUTHORIZED
```

and preserves every claimed non-result: no ambient form, form domain, associated graph, operator domain, compression, continuum numerator, H4a1b closure, promotion, or RH claim.  `[ABSTRACT][PAPER]`

B3.0M itself proves only the finite-synthesis Fourier ledger equality against the literal finite CCM matrix. Its source contains no ambient form or domain declaration.  `[FINITE_CELL][LEAN]`

## 2. Operative ruling

[
\boxed{
\texttt{TRY_GOAL057_B3_0N_ARCH_SYMBOL_EXPLICIT_GLOBAL_LOWER_BOUND_PREFLIGHT}
}
]

Candidate **A** is selected, but only as one untracked exact Lean preflight. No production materialization is authorized.

The selected theorem is:

```lean
theorem sourceArchimedeanMultiplier_add_explicitShift_nonneg
    (t : ℝ) :
    0 ≤ sourceArchimedeanMultiplier t +
      (|Real.log Real.pi| + Real.log 4 + 6)
```

`[ABSTRACT][CONDITIONAL]`

This is the smallest lawful child because it settles the first prerequisite on which the proposed shifted-domain and closed-form constructions depend:

```text
Is the exact current multiplier lower bounded by one finite constant?
```

The answer is yes, with an explicit source-derived constant and without importing D0.2 as a premise.

## 3. Answers to the seven mandatory adversarial questions

### 3.1 What is the actual large-(|t|) sign?

The exact production definition is

[
m_{\mathrm{arch}}(t)
====================

-\log\pi+
\Re\psi!\left(\frac14+i\pi t\right),
]

and Lean already proves

[
m_{\mathrm{arch}}(t)
====================

-\frac{a_\star(t)}{2\pi}.
]

`[ABSTRACT][LEAN]`

The primary source gives, in its angular-frequency coordinate,

[
\theta'(s)
==========

\frac12\bigl(\log|s|-\log2-\log\pi\bigr)
-\frac{1}{48s^2}
+O(s^{-4}).
]

It also fixes the project crosswalk

[
m_{\mathrm{arch}}(t)=2\theta'(2\pi t).
]

 `[ABSTRACT][PAPER]`

Therefore

[
m_{\mathrm{arch}}(t)
====================

\log|t|+O(t^{-2})
\qquad (|t|\to\infty).
]

Hence the actual tail sign is:

[
\boxed{\text{positive and divergent to }+\infty.}
]

Equivalently, (a_\star(t)\sim-2\pi\log|t|), so the existing minus sign in `-a_star/(2*pi)` is essential. The hypothesis that the project multiplier tends to (-\infty) is killed. `[ABSTRACT][PAPER]`

### 3.2 Is a finite lower-bound shift possible?

Yes, and no asymptotic compactness argument is needed.

For

[
z=\frac14+i\pi t,
]

the foundational Stieltjes theorem gives

[
\left|
\Re\psi(z)-\log|z|
+\frac{\Re z}{2|z|^2}
\right|
\le
\frac{1}{4|z|^2}.
]

`[ABSTRACT][LEAN]`

Since (|z|\ge1/4),

[
\log|z|\ge-\log4,
]

[
0\le\frac{\Re z}{2|z|^2}\le2,
]

and

[
\frac{1}{4|z|^2}\le4.
]

Thus, globally for every real (t),

[
m_{\mathrm{arch}}(t)
\ge
-|\log\pi|-\log4-6.
]

Therefore the explicit finite shift

[
\boxed{
C_{\mathrm{arch}}
=================

|\log\pi|+\log4+6
}
]

satisfies

[
\boxed{
m_{\mathrm{arch}}(t)+C_{\mathrm{arch}}\ge0
\quad\forall t\in\mathbb R.
}
]

`[ABSTRACT][CONDITIONAL]`

The constant is deliberately coarse. Optimality is irrelevant; finiteness, exactness, and source independence are what the downstream form construction needs.

### 3.3 Is there a D0.2 sign mismatch?

No.

D0.2 fixes the source ledger as

[
\Psi
====

W_{0,2}-W_{\mathbb R}-\sum_pW_p.
]

It also types the resulting window form as lower bounded and lower semicontinuous, not positive.  `[ABSTRACT][PAPER]`

The project’s Fourier multiplier represents

[
W_\infty=-W_{\mathbb R}.
]

Consequently the exact Fourier ledger is

[
+W_{0,2}
+\text{Arch}
-\text{Prime},
]

where `Arch` is already the negative (W_{\mathbb R}) contribution. B3.0M preserves exactly this orientation.  `[FINITE_CELL][LEAN]`

Therefore:

```text
D0.2 sign convention:
  MATCHES.

finite ledger / Fourier orientation:
  MATCHES.

ambient sign repair:
  NOT REQUIRED.
```

A negative logarithmic tail would have contradicted the source’s lower-boundedness mechanism, because bounded pole and prime perturbations cannot repair an archimedean multiplier tending to (-\infty). The actual positive tail removes that contradiction. `[ABSTRACT][PAPER]`

### 3.4 Which of W02 and Prime is bounded on the whole source Hilbert space?

**Both are bounded for each fixed source window**, but neither ambient extension is currently materialized in production Lean.

The primary source writes the prime contribution as a finite sum of bounded self-adjoint operators (T(n)), and the proof of its discrete-spectrum theorem explicitly states that both the non-archimedean contribution and the pole-evaluation contribution are bounded.  `[ABSTRACT][PAPER]`

Their likely Lean construction routes differ:

* **W02:** two bounded endpoint-moment functionals on the compact log window, followed by a rank-two sesquilinear form. The current finite W02 source theorem confirms the correct rank-two ordered shape, but it does not expose an all-(H_m) operator. `[ABSTRACT][LEAN]`
* **Prime:** define each source shift/truncation operator (T(n)) on the whole window Hilbert space and take the finite von-Mangoldt weighted sum. No current Route-B theorem provides those ambient operators. `[ABSTRACT][CONDITIONAL]`

There is no exact current production theorem that can simply be wrapped to create either extension. Candidate C is likely cheaper than D, but both require genuinely new ambient constructions.

### 3.5 Does the current basis isometry imply the arbitrary-vector weighted domain?

No.

B3.0L gives a complex linear isometry

[
\Phi_i:H_m(i)\to L^2(\mathbb R)
]

and identifies (\Phi_i(V_{n,m})) with the literal Fourier transform only on the basis modes. B3.0B3 proves (m_{\mathrm{arch}}\widehat V_n\in L^2) separately for every mode. The request correctly forbids upgrading those statements to all vectors by quantifier drift.  `[ABSTRACT][LEAN]`

An arbitrary-vector form domain requires a new multiplication-domain construction, for example

[
\mathcal D_{\mathrm{arch}}
==========================

\left{
f\in H_m:
\sqrt{m_{\mathrm{arch}}+C_{\mathrm{arch}}},
\Phi_i f\in L^2(\mathbb R)
\right}.
]

Its legality needs:

* measurable nonnegative shifted multiplier;
* a well-defined operation on (L^2) equivalence classes;
* density;
* closedness or closed-multiplication control;
* later proof that this constructed form agrees with D0.2.

Thus Candidate B is a genuine later child, not a corollary of modewise estimates. `[ABSTRACT][CONDITIONAL]`

### 3.6 Does B3.0N materially reduce the wall?

Yes.

Before B3.0N, the ambient-form route had an unresolved binary failure:

```text
Either the current source multiplier has the correct lower-bounded sign,
or the entire shifted-form representation is oriented incorrectly.
```

The selected theorem removes this fork by proving a concrete global inequality:

[
m_{\mathrm{arch}}+C_{\mathrm{arch}}\ge0.
]

That makes a source-faithful shifted multiplier domain mathematically legal. It does **not** claim that the resulting domain equals D0.2; that remains a later wall.

This is proof progress, not naming progress.

### 3.7 What falsifies a surrogate or wrong construction?

The decisive falsifiers are independent:

1. **Sign/orientation plant.** Replace the exact multiplier by its negative or replace `-a_star/(2*pi)` with `+a_star/(2*pi)`. The source tail then tends to (-\infty), so no finite global nonnegative shift can exist.
   Stop: `B3_0N_ARCH_SYMBOL_NORMALIZATION_MISMATCH`.

2. **Finite-shift plant.** Replace the constant by a (t)-dependent logarithmic envelope. That proves only variable domination, not a finite spectral shift.
   Stop: `B3_0N_FINITE_SHIFT_NOT_PROVED`.

3. **Premise-surrogate plant.** Add the desired lower bound as a hypothesis.
   Stop: `SURROGATE_BY_PREMISE_NOT_SOURCE_CONSTRUCTION`.
   **Card:** C10.

4. **Finite-only alias plant.** Prove the inequality only on sampled frequencies, integer modes, or one finite CCM block.
   Stop: `B3_0N_FINITE_ONLY_LOWER_BOUND_ALIAS`.
   **Card:** C04.

5. **Finite-Riesz substitution plant.** Invoke `sourceCCMFiniteRieszOperator` or a finite matrix eigenvalue to infer the multiplier bound.
   Stop: `B3_0N_FINITE_RIESZ_SUBSTITUTED_FOR_SYMBOL_ANALYSIS`.
   **Card:** C04/C10.

6. **Source-parent plant.** Remove direct consumption of the Stieltjes digamma bound.
   Stop: `B3_0N_STIELTJES_SOURCE_PARENT_NOT_CONSUMED`.

## 4. Candidate comparison

| Candidate                                   | Kill power |                                       Cost | Dependency ruling                                                                               | Verdict                    |
| ------------------------------------------- | ---------: | -----------------------------------------: | ----------------------------------------------------------------------------------------------- | -------------------------- |
| **A — explicit global symbol lower bound**  |    **5/5** | Low–medium; exact Lean cost still unproved | No missing ambient object; consumes foundational Stieltjes theorem only                         | **Selected**               |
| **B — shifted multiplier domain primitive** |        5/5 |              Medium–high; API cost unknown | Requires A to know the shift is genuinely nonnegative                                           | Retained, not authorized   |
| **C — bounded whole-space W02 extension**   |        3/5 |                 Medium; exact cost unknown | Independent of A, but requires new endpoint-functional/Riesz construction and restriction proof | Not selected               |
| **D — bounded whole-space Prime extension** |        4/5 |            Medium–high; exact cost unknown | Requires ambient truncated shift operators and a finite operator sum                            | Not selected               |
| **E — closed shifted complete form**        |        5/5 |                   High; exact cost unknown | Depends on A, B, C, D and an equality-to-D0.2 theorem                                           | Killed as a current bundle |
| **F — global coefficient/core bridge**      |        2/5 |                 Medium; exact cost unknown | Not needed before A–D; risks decorative abstraction after B3.0M                                 | Rejected now               |

Candidate A has the highest kill-power per cost and is logically upstream of B and E.

## 5. Exact preflight child

### Scratch-only path

```text
q3.lean.aristotle/Goal057B3_0N_ArchSymbolLowerBound_Scratch.lean
```

### Candidate production path — not authorized

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  D0PstarExactArchSymbolLowerBound.lean
```

### Exact import

```lean
import Q3.Proofs.RouteB.D0PstarExactArchSymbolLogDomination
```

### Exact surface ceiling

```yaml
public:
  definitions: 0
  theorems:
    - sourceArchimedeanMultiplier_add_explicitShift_nonneg

private:
  definitions: 0
  theorems:
    - b3_0n_one_fourth_le_norm_sourceArchimedeanArgument
    - b3_0n_sourceArchimedeanStieltjesCorrection_le
    - b3_0n_sourceArchimedeanStieltjesRemainder_le
```

### Exact byte-pinned candidate

[Exact B3.0N scratch candidate](sandbox:/mnt/data/GOAL057_B3_0N_ARCH_SYMBOL_EXPLICIT_LOWER_BOUND_PREFLIGHT_CANDIDATE_2026-08-09.lean)

```lean
import Q3.Proofs.RouteB.D0PstarExactArchSymbolLogDomination

noncomputable section

open scoped Real

namespace Q3.RouteB.D0Pstar

private lemma b3_0n_one_fourth_le_norm_sourceArchimedeanArgument
    (t : ℝ) :
    (1 / 4 : ℝ) ≤
      ‖(1 / 4 : ℂ) +
        Complex.I * ((Real.pi * t : ℝ) : ℂ)‖ := by
  let z : ℂ :=
    (1 / 4 : ℂ) +
      Complex.I * ((Real.pi * t : ℝ) : ℂ)
  have hre : |z.re| ≤ ‖z‖ := by
    simpa using (RCLike.abs_re_le_norm z)
  simpa [z, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)] using hre

private lemma b3_0n_sourceArchimedeanStieltjesCorrection_le
    (t : ℝ) :
    |(((1 / 4 : ℂ) +
        Complex.I * ((Real.pi * t : ℝ) : ℂ))).re /
        (2 * ‖(1 / 4 : ℂ) +
          Complex.I * ((Real.pi * t : ℝ) : ℂ)‖ ^ 2)| ≤ 2 := by
  let z : ℂ :=
    (1 / 4 : ℂ) +
      Complex.I * ((Real.pi * t : ℝ) : ℂ)
  have hlower : (1 / 4 : ℝ) ≤ ‖z‖ := by
    simpa [z] using
      b3_0n_one_fourth_le_norm_sourceArchimedeanArgument t
  have hnorm_pos : 0 < ‖z‖ :=
    lt_of_lt_of_le (by norm_num) hlower
  have hsq : (1 / 16 : ℝ) ≤ ‖z‖ ^ 2 := by
    nlinarith [sq_nonneg (‖z‖ - 1 / 4)]
  have hden_pos : 0 < 2 * ‖z‖ ^ 2 := by
    positivity
  have hnonneg : 0 ≤ z.re / (2 * ‖z‖ ^ 2) := by
    rw [show z.re = (1 / 4 : ℝ) by simp [z]]
    positivity
  rw [show (((1 / 4 : ℂ) +
      Complex.I * ((Real.pi * t : ℝ) : ℂ))).re = z.re by rfl]
  rw [show ‖(1 / 4 : ℂ) +
      Complex.I * ((Real.pi * t : ℝ) : ℂ)‖ = ‖z‖ by rfl]
  rw [abs_of_nonneg hnonneg,
    show z.re = (1 / 4 : ℝ) by simp [z]]
  apply (div_le_iff₀ hden_pos).2
  nlinarith

private lemma b3_0n_sourceArchimedeanStieltjesRemainder_le
    (t : ℝ) :
    1 / (4 * ‖(1 / 4 : ℂ) +
      Complex.I * ((Real.pi * t : ℝ) : ℂ)‖ ^ 2) ≤ 4 := by
  let z : ℂ :=
    (1 / 4 : ℂ) +
      Complex.I * ((Real.pi * t : ℝ) : ℂ)
  have hlower : (1 / 4 : ℝ) ≤ ‖z‖ := by
    simpa [z] using
      b3_0n_one_fourth_le_norm_sourceArchimedeanArgument t
  have hnorm_pos : 0 < ‖z‖ :=
    lt_of_lt_of_le (by norm_num) hlower
  have hsq : (1 / 16 : ℝ) ≤ ‖z‖ ^ 2 := by
    nlinarith [sq_nonneg (‖z‖ - 1 / 4)]
  have hden_pos : 0 < 4 * ‖z‖ ^ 2 := by
    positivity
  rw [show ‖(1 / 4 : ℂ) +
      Complex.I * ((Real.pi * t : ℝ) : ℂ)‖ = ‖z‖ by rfl]
  apply (div_le_iff₀ hden_pos).2
  nlinarith

/-- The exact source archimedean multiplier has a source-derived uniform
lower bound.  Equivalently, the displayed finite constant shift makes the
multiplier pointwise nonnegative. -/
theorem sourceArchimedeanMultiplier_add_explicitShift_nonneg
    (t : ℝ) :
    0 ≤ sourceArchimedeanMultiplier t +
      (|Real.log Real.pi| + Real.log 4 + 6) := by
  let z : ℂ :=
    (1 / 4 : ℂ) +
      Complex.I * ((Real.pi * t : ℝ) : ℂ)
  have hz : 0 < z.re := by
    simp [z]
  have hrem := Q3.re_digamma_remainder_bound_stieltjes z hz
  let E : ℝ :=
    (Q3.digamma z).re - Real.log ‖z‖ +
      z.re / (2 * ‖z‖ ^ 2)
  have hE : |E| ≤ 1 / (4 * ‖z‖ ^ 2) := by
    simpa [E] using hrem
  have hlower : (1 / 4 : ℝ) ≤ ‖z‖ := by
    simpa [z] using
      b3_0n_one_fourth_le_norm_sourceArchimedeanArgument t
  have hlog_quarter :
      Real.log (1 / 4 : ℝ) ≤ Real.log ‖z‖ :=
    Real.log_le_log (by norm_num) hlower
  have hlog_lower : -Real.log 4 ≤ Real.log ‖z‖ := by
    have hlog_inv : Real.log (1 / 4 : ℝ) = -Real.log 4 := by
      rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, Real.log_inv]
    rw [hlog_inv] at hlog_quarter
    exact hlog_quarter
  have hcorr : |z.re / (2 * ‖z‖ ^ 2)| ≤ 2 := by
    simpa [z] using
      b3_0n_sourceArchimedeanStieltjesCorrection_le t
  have hrem4 :
      1 / (4 * ‖z‖ ^ 2) ≤ 4 := by
    simpa [z] using
      b3_0n_sourceArchimedeanStieltjesRemainder_le t
  have hE4 : |E| ≤ 4 := hE.trans hrem4
  have hdecomp :
      sourceArchimedeanMultiplier t =
        -Real.log Real.pi + Real.log ‖z‖ -
          z.re / (2 * ‖z‖ ^ 2) + E := by
    simp only [sourceArchimedeanMultiplier, z, E]
    ring
  have hpi : -|Real.log Real.pi| ≤ -Real.log Real.pi := by
    exact neg_le_neg (le_abs_self (Real.log Real.pi))
  have hcorr_upper : z.re / (2 * ‖z‖ ^ 2) ≤ 2 :=
    (abs_le.mp hcorr).2
  have hE_lower : -4 ≤ E := (abs_le.mp hE4).1
  rw [hdecomp]
  nlinarith

#print axioms sourceArchimedeanMultiplier_add_explicitShift_nonneg

end Q3.RouteB.D0Pstar
```

The candidate has SHA-256 `ecefe92d…d06e9`, 4,488 bytes, 125 `wc` lines, a final LF, and zero matches for the forbidden-token scan. It has **not** been run through the pinned Lean toolchain by this judge. `[ABSTRACT][CONDITIONAL]`

## 6. Proof route

The proof uses only the existing production definition and the foundational Stieltjes theorem:

1. Set (z=1/4+i\pi t).
2. Prove (|z|\ge1/4).
3. Convert the Stieltjes remainder theorem into the exact decomposition
   [
   m_{\mathrm{arch}}
   =================

   -\log\pi+\log|z|-\frac{\Re z}{2|z|^2}+E.
   ]
4. Bound:
   [
   \log|z|\ge-\log4,\qquad
   \frac{\Re z}{2|z|^2}\le2,\qquad
   E\ge-4.
   ]
5. Combine the bounds by ordered-ring arithmetic.

No finite matrix, numerical approximation, ambient-form premise, or associated operator enters. `[ABSTRACT][CONDITIONAL]`

## 7. Mandatory judges and controls

| ID                               | Mutation or attack                                                                | Required result                                      |
| -------------------------------- | --------------------------------------------------------------------------------- | ---------------------------------------------------- |
| `P057_B3_0N_1_EXACT_SYMBOL`      | Change `1/4 + I*(π*t)` or the leading `-log π`                                    | `B3_0N_ARCH_SYMBOL_NORMALIZATION_MISMATCH`           |
| `P057_B3_0N_2_ASTAR_SIGN`        | Change `-a_star/(2π)` to `+a_star/(2π)` in the independent normalization control  | `B3_0N_ARCH_SYMBOL_SIGN_ORIENTATION_MISMATCH`        |
| `P057_B3_0N_3_FINITE_SHIFT`      | Replace the constant shift by a function of `t`, `i`, `m`, or `N`                 | `B3_0N_FINITE_SHIFT_NOT_PROVED`                      |
| `P057_B3_0N_4_STIELTJES_PARENT`  | Remove direct use of `re_digamma_remainder_bound_stieltjes`                       | `B3_0N_STIELTJES_SOURCE_PARENT_NOT_CONSUMED`         |
| `P057_B3_0N_5_PREMISE_SURROGATE` | Add the desired lower bound as a hypothesis                                       | `SURROGATE_BY_PREMISE_NOT_SOURCE_CONSTRUCTION`       |
| `P057_B3_0N_6_FINITE_ONLY_ALIAS` | Restrict the theorem to sampled frequencies or finite mode data                   | `B3_0N_FINITE_ONLY_LOWER_BOUND_ALIAS`                |
| `P057_B3_0N_7_FINITE_RIESZ`      | Derive the inequality from `sourceCCMFiniteRieszOperator` or a finite eigenvalue  | `B3_0N_FINITE_RIESZ_SUBSTITUTED_FOR_SYMBOL_ANALYSIS` |
| `P057_B3_0N_8_DEPENDENCY`        | Add PrimeCert, Step33, hbox, payload, or Aristotle-output support                 | `ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK`               |
| `P057_B3_0N_9_SCOPE`             | Add a form domain, closed form, graph, operator, compression, or checkpoint claim | `B3_0N_SCOPE_SMUGGLE`                                |

Independent controls:

```text
exact definition:
  -log pi + Re digamma(1/4 + I*pi*t);

exact normalization:
  sourceArchimedeanMultiplier = -a_star/(2*pi);

exact source parent:
  re_digamma_remainder_bound_stieltjes;

tail-sign control:
  sourceArchimedeanMultiplier(t) = log|t| + O(t^-2);

constant-shift control:
  the shift contains no variable and no project index.
```

## 8. Exact preflight validation

Run only the scratch preflight:

```bash
test "$(git rev-parse HEAD)" = \
  "21334efd24c05050ee482426af6dcd8e8f43842c"

test "$(git rev-parse origin/rh_clean)" = \
  "21334efd24c05050ee482426af6dcd8e8f43842c"

test "$(git diff --cached | sha256sum | cut -d' ' -f1)" = \
  "291e2387203c579f3f56bd5994daa7225c575c06a37fb3144b13e04e6d1b4f7b"

sha256sum \
  q3.lean.aristotle/Goal057B3_0N_ArchSymbolLowerBound_Scratch.lean

wc -c -l \
  q3.lean.aristotle/Goal057B3_0N_ArchSymbolLowerBound_Scratch.lean

rg -n \
  'sorry|exact\?|admit|unsafe|native_decide|opaque|axiom |Float' \
  q3.lean.aristotle/Goal057B3_0N_ArchSymbolLowerBound_Scratch.lean

cd q3.lean.aristotle

lake env lean \
  Goal057B3_0N_ArchSymbolLowerBound_Scratch.lean
```

Required result:

```yaml
direct_Lean_exit: 0
imports: 1
public_definitions: 0
public_theorems: 1
private_definitions: 0
private_theorems: 3
axioms:
  - propext
  - Classical.choice
  - Quot.sound
tracked_repository_mutation: false
```

All nine judges must run in temporary copies. Every mutation artifact must be deleted. `routeb_status.py --check`, `git diff --check`, and exact `git status --short` must confirm that the production tree and route state remain untouched.

### Binary outcome

```text
PASS:
  GOAL057_B3_0N_ARCH_SYMBOL_EXPLICIT_GLOBAL_LOWER_BOUND_PREFLIGHT_PROVED
```

Return the exact scratch bytes, direct Lean output, axiom output, dependency fingerprint, and all judge fates to this same chat for a separate production-release ruling.

```text
FAIL:
  GOAL057_B3_0N_ARCH_SYMBOL_EXPLICIT_GLOBAL_LOWER_BOUND_PREFLIGHT_FAILED
```

Return the first exact Lean/API defect. Do not weaken the theorem to a tail-only, sampled, or hypothesis-driven statement.

## 9. Semantic boundary after preflight success

A successful preflight proves only:

[
\boxed{
m_{\mathrm{arch}}(t)
+
\bigl(|\log\pi|+\log4+6\bigr)
\ge0
\quad\forall t\in\mathbb R.
}
]

`[ABSTRACT][LEAN]`

It does not prove:

* that the shifted multiplication form is closed;
* the exact shifted form domain;
* equality of that domain or form with D0.2;
* bounded whole-space W02 or Prime operators;
* an ambient source Weil form;
* an associated graph or operator;
* operator-domain membership;
* compression or invariance;
* the continuum numerator;
* H4a1b;
* a coarse checkpoint.

The exact next gap after success is:

```text
GOAL057_B3_0O_SHIFTED_ARCH_MULTIPLIER_FORM_DOMAIN_PRIMITIVE
```

It is named only and explicitly **not authorized**.

## 10. Meta closeout

**What became smaller?**

The broad ambient-form wall is split. Its first uncertainty is no longer “perhaps the multiplier has the wrong sign.” It is now one exact theorem about a source-derived finite shift.

**What was killed?**

* negative logarithmic tail;
* sign mismatch between D0.2 and B3.0M;
* a variable logarithmic majorant masquerading as a finite shift;
* finite-matrix data as evidence for an ambient multiplier bound;
* a premise-only lower-bound wrapper.

**What must not be tried again?**

Do not define the shifted form domain before the B3.0N preflight passes. Do not call that future domain D0.2 without an equality theorem. Do not substitute the finite Riesz operator for the ambient associated operator.

**Registered prediction**

```text
Prediction:
  the exact 4,488-byte candidate compiles under the pinned toolchain and
  proves the explicit shift with the standard axiom triple.

Status:
  REGISTERED_NOT_YET_TESTED.

Sign-flip prediction:
  a coherently negative archimedean tail cannot admit any finite global shift.

Status:
  SOURCE-CONFIRMED; production plant still required.
```

## CODEX DIRECTIVE

```yaml
OPERATIVE_CLASS:
  TRY_GOAL057_B3_0N_ARCH_SYMBOL_EXPLICIT_GLOBAL_LOWER_BOUND_PREFLIGHT

MODE:
  UNTRACKED_EXACT_LEAN_PREFLIGHT
  PRODUCTION_AUTHORIZED: false
  TRACKED_REPOSITORY_MUTATION: false
  NO_PRODUCTION_AUTHORIZATION_IN_THIS_VERDICT: true

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: 21334efd24c05050ee482426af6dcd8e8f43842c
  require_origin_equal: true
  controlling_request_sha256: f2cdd45f4efe36c27b6546b0e37ca1b674dfe6861e8e12d778b6d05fc51d86c2
  controlling_request_bytes: 15069
  controlling_request_wc_lines: 418
  controlling_request_final_LF: true
  preserve_staged_patch_sha256: 291e2387203c579f3f56bd5994daa7225c575c06a37fb3144b13e04e6d1b4f7b

CREATE_UNTRACKED_ONLY:
  - q3.lean.aristotle/Goal057B3_0N_ArchSymbolLowerBound_Scratch.lean

DO_NOT_CREATE:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarExactArchSymbolLowerBound.lean

EXACT_CANDIDATE:
  source_artifact:
    GOAL057_B3_0N_ARCH_SYMBOL_EXPLICIT_LOWER_BOUND_PREFLIGHT_CANDIDATE_2026-08-09.lean
  method: BYTE_FOR_BYTE_COPY
  sha256: ecefe92d6fc0056f92562326944ca040f2eff6a417e59335580925004f0d06e9
  bytes: 4488
  wc_lines: 125
  final_LF: true
  any_byte_change: STOP_AND_RETURN_CORRECTED_CANDIDATE

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarExactArchSymbolLogDomination

PUBLIC_SURFACE_EXACT:
  definitions: []
  theorems:
    - sourceArchimedeanMultiplier_add_explicitShift_nonneg
  total: 1

PRIVATE_SURFACE_EXACT:
  definitions: []
  theorems:
    - b3_0n_one_fourth_le_norm_sourceArchimedeanArgument
    - b3_0n_sourceArchimedeanStieltjesCorrection_le
    - b3_0n_sourceArchimedeanStieltjesRemainder_le
  total: 3

MANDATORY_SEMANTICS:
  - exact_sourceArchimedeanMultiplier_definition
  - exact_minus_a_star_div_two_pi_orientation
  - direct_Stieltjes_remainder_parent_consumption
  - global_for_all_real_t_quantifier
  - finite_constant_shift_independent_of_t_i_m_N
  - no_numerical_fitting
  - no_form_or_operator_premise
  - no_finite_matrix_or_finite_Riesz_substitution
  - no_D0_2_domain_equality_claim

MANDATORY_JUDGES:
  - P057_B3_0N_1_EXACT_SYMBOL
  - P057_B3_0N_2_ASTAR_SIGN
  - P057_B3_0N_3_FINITE_SHIFT
  - P057_B3_0N_4_STIELTJES_PARENT
  - P057_B3_0N_5_PREMISE_SURROGATE
  - P057_B3_0N_6_FINITE_ONLY_ALIAS
  - P057_B3_0N_7_FINITE_RIESZ
  - P057_B3_0N_8_DEPENDENCY
  - P057_B3_0N_9_SCOPE

VALIDATION:
  - verify_HEAD_equals_origin_rh_clean
  - verify_staged_patch_SHA256_unchanged
  - verify_exact_scratch_SHA256_bytes_wc_lines_and_final_LF
  - forbidden_token_scan
  - direct_lake_env_lean_on_scratch
  - exact_one_import_audit
  - exact_public_surface_0_definitions_1_theorem
  - exact_private_surface_0_definitions_3_theorems
  - print_axioms_for_public_theorem
  - require_axioms_exactly_[propext_Classical.choice_Quot.sound]
  - run_all_nine_judges_in_temporary_copies
  - remove_all_mutation_artifacts
  - routeb_status_check
  - git_diff_check
  - exact_git_status_report
  - prove_no_tracked_repository_mutation
  - preserve_same_living_chat

PREFLIGHT_STOP:
  GOAL057_B3_0N_ARCH_SYMBOL_EXPLICIT_GLOBAL_LOWER_BOUND_PREFLIGHT_FAILED

PREFLIGHT_SUCCESS:
  GOAL057_B3_0N_ARCH_SYMBOL_EXPLICIT_GLOBAL_LOWER_BOUND_PREFLIGHT_PROVED

NEXT_GAP_NOT_AUTHORIZED:
  GOAL057_B3_0O_SHIFTED_ARCH_MULTIPLIER_FORM_DOMAIN_PRIMITIVE

NOT_AUTHORIZED:
  - create_the_B3_0N_production_file
  - select_or_authorize_B3_0O
  - define_sourceWeilSesquilinearForm
  - define_SourceWeilFormDomain
  - define_SourceWeilAssociatedGraph
  - define_SourceWeilOperatorDomain
  - define_sourceWeilAssociatedOperator
  - claim_equality_with_D0_2
  - construct_W02_or_Prime_ambient_extensions_in_this_transaction
  - infer_arbitrary_vector_pointwise_Fourier
  - substitute_sourceCCMFiniteRieszOperator_for_an_ambient_operator
  - assert_selected_kTrial_operator_domain_membership
  - assert_compression_or_invariance
  - claim_continuum_numerator
  - invoke_or_close_H4A1B
  - decrement_the_ten_checkpoint_ledger
  - touch_frozen_parent_extract_schedules
  - create_Bus_010
  - release_Goal_055
  - unfreeze_G2_CCM
  - submit_Aristotle
  - promote_Route_B
  - make_PX_or_RH_claim
  - open_fresh_chat

FINAL_BOUNDARY:
  route: CHALLENGER_NOT_RH
  active_bus_goal: 057
  bus_010: VOID
  goal_055: HOLD
  g2_ccm: FROZEN
  current_checkpoint: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
  coarse_checkpoints_closed: 0
  coarse_checkpoints_remaining: 10
  H4a1b: OPEN
  Aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
```
