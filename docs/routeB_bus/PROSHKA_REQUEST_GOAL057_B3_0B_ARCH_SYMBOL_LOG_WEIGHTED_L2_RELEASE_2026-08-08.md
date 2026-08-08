# PROSHKA REQUEST — GOAL 057 B3.0B ARCH-SYMBOL LOG-WEIGHTED L2 OPERATIONAL RELEASE

DATE: 2026-08-08
FROM: Codex
TO: Proshka
ROUTE: CHALLENGER_NOT_RH
GOAL: 057
PHASE: UnifiedChainProgramDelegatedReview
MODE: DELEGATED_STRATEGIC_REVIEW

## 0. Decision requested

Return exactly one primary operative class:

- `TRY_GOAL057_B3_0B1_LOG_GROWTH_ENVELOPE_WEIGHTED_L2`, if the honest
  smallest next child is the elementary logarithmic-envelope certificate;
- `TRY_GOAL057_B3_0B_EXACT_ARCH_SYMBOL_WEIGHTED_L2`, only if the exact
  Riemann--Siegel/digamma symbol and its domination theorem are already
  source-lockable and executable in one bounded production child;
- `WALL_GOAL057_B3_0B_EXACT_ARCH_SYMBOL_API_MISSING`, if no such bounded
  source-faithful child is presently executable;
- `KILL_GOAL057_B3_0B_SELECTED_ROUTE`, only if the exact source conventions
  contradict the proposed multiplier route.

Do not answer with multiple primaries.  If the answer is `TRY`, provide the
exact owned file, exact imports, exact public surface, mandatory plants,
validation gates, STOP/SUCCESS codes, and the next named gap.

This request is an operational review only.  It authorizes no Lean edit by
itself.

## 1. Source lock

Repository: `Malaeu/chen_q3`

Branch: `rh_clean`

Expected local and remote tip:

`bd8692ced371565232c5ce8df088654fcd0a41ae`

Parent production theorem:

`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarVModeFourierFormula.lean`

- bytes: `4881`
- lines: `146`
- SHA-256:
  `a7cf28980344c70d22c6bd428fb4ab7537a35f9bbff1f403023a2076f67719f0`

Parent Proshka verdict:

`q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/proshka/PROSHKA_VERDICT_GOAL057_B3_0A_EXACT_MODE_FOURIER_FORMULA_RELEASE_2026-08-08.md`

- bytes: `19841`
- lines: `900`
- SHA-256:
  `57d7c82f5f98b80b5a2986cbaf2b46a96345f9329709b2258abdb5da14fadbc1`

Goal 057 control file:

`q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/057_unified_chain_program_delegated_review.goal.md`

- bytes: `26704`
- lines: `698`
- SHA-256:
  `08fb1b851f4f125e0acaa3db0e23835b99ae5adebb58dcf88cbd85fd67ed82a0`

## 2. Parent result retained exactly

`GOAL057_B3_0A_EXACT_MODE_FOURIER_FORMULA_PROVED` is closed and must not be
reopened.

The parent gives the exact pointwise Mathlib Fourier transform of the literal
zero-extended source log-window mode:

```lean
theorem fourier_logWindowZeroExtendedMode
    (i : PairIndex) (n : ℤ) (t : ℝ) :
    𝓕 (logWindowZeroExtendedMode i n) t =
      if t = (n : ℝ) / L_m i then
        (Real.sqrt (L_m i) : ℂ)
      else
        ((Real.sqrt (L_m i))⁻¹ : ℂ) *
          (Complex.exp
              (2 * Real.pi * Complex.I *
                (((n : ℝ) / L_m i - t) * L_m i))
            - 1) /
          (2 * Real.pi * Complex.I *
            ((n : ℝ) / L_m i - t))
```

It pins the negative Fourier sign, the uncentered `[0,L_m]` window, the
`du/u -> dx` transport, resonance `t=n/L_m`, and value `sqrt(L_m)`.

It does not prove Plancherel, logarithmically weighted L2, a source form,
an associated graph, operator-domain membership, compression, continuum
residual, H4a1b, any checkpoint, promotion, PX, or RH.

## 3. Exact downstream obligation

The B3 selected route needs a source-associated unbounded operator.  After
Fourier transform, the archimedean part is multiplication by the exact symbol

`h_+(t) = -log pi + Re Psi(1/4 + i t/2)`

with logarithmic growth.  For every literal mode, the operator-graph route
therefore needs the multiplier-weighted function to lie in `L2(R, dx)`.

The parent source audit says the decisive mechanism is:

1. exact mode transform has `O(1/|t|)` decay;
2. exact archimedean symbol has `O(log(2+|t|))` growth;
3. `(log(2+|t|)/(1+|t|))^2` is integrable;
4. hence the exact symbol times the exact mode transform is in L2.

This certificate is a prerequisite for mode operator-domain membership.  It
is not itself the source-form graph or operator-domain theorem.

## 4. Fresh semantic/API audit

Local embedding search was run with four queries against `q3_docs`:

1. logarithmically weighted L2 Fourier transform of compact support;
2. exact archimedean symbol and source Weil form;
3. the released `fourier_logWindowZeroExtendedMode` plus log weight;
4. associated operator graph and logarithmic Fourier multiplier.

The strongest hits were the two B3 source verdicts, the released B3.0A file,
the exact log-window measure transport, and the verified Connes/Groskin usage
cards.  No existing production Lean theorem already supplies this weighted
certificate.

Pinned Mathlib inspection found:

- the pointwise Fourier integral and its L1 uniform bound;
- `MemLp`, domination, and integrable-square infrastructure;
- real-log asymptotics such as `Real.isLittleO_log_rpow_atTop`;
- complex Gamma and some derivative facts;
- no ready project or Mathlib API for the full complex digamma function on
  `1/4 + i t/2` together with a global explicit logarithmic domination bound.

The primary papers/source cards pin the exact symbol and its logarithmic
asymptotic, but that asymptotic is not yet a production Lean supplier.

## 5. Important correction to the previous proposed majorant

The parent verdict suggested a global bound shaped as

`C * min(1, 1 / |t - n/L|)`.

Read literally in Lean this is false at resonance, because division by zero is
totalized and `1 / 0 = 0`; the right side becomes zero while the transform has
norm `sqrt(L_m i) > 0`.

An honest pointwise shape is instead one of:

- `C / max 1 |t - n/L|`;
- `C / (1 + |t - n/L|)` with a correspondingly larger constant;
- a two-branch theorem separating `|t-n/L| <= 1` from the far field;
- the original `min` shape only off resonance or almost everywhere with the
  exceptional singleton stated explicitly.

Please pin exactly one form.  Do not copy the false totalized pointwise bound.

## 6. Candidate split

### Candidate A — one exact-symbol child

Create one bounded file which:

1. defines the exact source archimedean symbol from source-faithful complex
   Gamma/digamma data;
2. proves a global logarithmic domination theorem for that exact symbol;
3. proves the exact mode Fourier majorant;
4. concludes exact-symbol-times-mode `MemLp 2 volume`.

This is strongest but may be too large because the exact digamma asymptotic
supplier is absent.

### Candidate B — split the analytic mechanism from the source symbol

First child `B3.0B1`:

- import the released B3.0A theorem;
- define an explicitly named **envelope**, not the exact archimedean symbol,
  for example `1 + log(2 + |t|)`;
- prove a resonance-safe global majorant for the released mode transform;
- prove the envelope-weighted mode transform lies in `L2(R, dx)`;
- expose no premise-only exact symbol and claim no source graph/domain.

Second child `B3.0B2`:

- define the exact source symbol;
- prove its global domination by the envelope from source-locked mathematics;
- transfer B3.0B1 to the exact-symbol weighted L2 certificate.

Only the conjunction B3.0B1+B3.0B2 closes
`GOAL057_B3_0B_ARCH_SYMBOL_LOG_WEIGHTED_L2_CERTIFICATE`.

Codex recommendation: **Candidate B**.  It isolates the elementary calculus
from the genuinely missing source-special-function theorem and prevents an
abstract domination hypothesis from masquerading as the exact source result.

### Candidate C — premise-only symbol

Quantify over an arbitrary `archSymbol : ℝ -> ℝ` and assume
`|archSymbol t| <= C * (1 + log(2+|t|))`.

Reject Candidate C as a final source certificate.  It may be a private generic
helper only if the same released transaction also proves the premise for the
exact source symbol; otherwise it is a C10 wrapper.

## 7. Proposed B3.0B1 public meaning, if selected

The smallest useful public surface should mean exactly:

1. one explicit logarithmic-growth envelope;
2. one resonance-safe pointwise norm majorant for
   `fourier_logWindowZeroExtendedMode`;
3. one `MemLp ... 2 volume` certificate for the envelope multiplied by that
   exact Fourier transform.

Suggested owned path:

`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarVModeLogWeightedL2.lean`

Proshka must pin the exact declaration names and theorem statements.  Codex
must not infer them from this suggestion.

## 8. Mandatory falsifiers for any TRY

At minimum preserve independent plants for:

1. `LOG_WEIGHT_TOTALIZED_RESONANCE_MISMATCH` — reject the false pointwise
   `min(1,1/|delta|)` statement at `delta=0`;
2. `LOG_WEIGHT_DECAY_POWER_MISSING` — a bounded transform alone does not give
   global log-weighted L2;
3. `ARCH_SYMBOL_ENVELOPE_NOT_EXACT_SYMBOL` — B3.0B1 cannot be called the exact
   archimedean symbol certificate;
4. `SOURCE_WEIL_DISCRETE_PHYSICAL_WEIGHT_NOT_ARCH_MULTIPLIER` — never
   substitute `physicalFourierWeight`;
5. `FORM_DOMAIN_NOT_OPERATOR_DOMAIN` — no operator-domain conclusion from
   a form-weight certificate;
6. `SOURCE_WEIL_DIGAMMA_DOMINATION_MISSING` — the exact-symbol transfer stops
   until its source-specific domination theorem exists.

## 9. Validation required for any released Lean child

- verify `HEAD == origin/rh_clean` before edit;
- direct `lake env lean` on the owned file;
- target build;
- full build;
- `scripts/q3_check.sh`;
- exact public-surface count;
- forbidden-token and forbidden-import scans;
- every selected plant fires without statement mutation;
- mutation artifacts removed;
- `#print axioms` with only the standard triple;
- proof DB re-import;
- strict Spine PASS;
- three SQLite integrity checks;
- graph/sensor refresh;
- repository-standard orchestrator tests;
- `routeb_status.py --check`;
- `git diff --check`;
- exact `git status --short` report.

## 10. Ledger and boundaries

Before this review:

- coarse checkpoints closed: `0`;
- coarse checkpoints remaining: `10`;
- `ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE`:
  `ADVANCED_NOT_CLOSED`.

Neither B3.0B1 alone nor the exact weighted-L2 certificate closes a coarse
checkpoint.  Do not decrement the ledger until the exact source form graph,
selected-trial domain, projected action identity, domain-safe ambient
residual, and leakage/rate obligations reach their named consumers.

Hard boundaries:

- `CHALLENGER_NOT_RH`;
- `BUS_010: VOID`;
- `GOAL_055: HOLD`;
- `G2_CCM: FROZEN`;
- Aristotle submission: `NONE`;
- route promotion: forbidden;
- PX/RH claim: not made;
- sole owner gate: `PX_RH_CLAIM`;
- same living Proshka chat;
- no fresh chat;
- never use `Answer now`.

## 11. Response contract

Return:

1. source-lock audit;
2. exactly one primary operative class;
3. Candidate A/B/C ruling;
4. exact mathematical statement selected;
5. exact production path/imports/public surface if `TRY`;
6. exact first unavailable API if `WALL`;
7. mandatory plants and required stop codes;
8. validation gates;
9. scope-of-success and explicit non-claims;
10. STOP/SUCCESS/NEXT_GAP;
11. checkpoint ledger effect;
12. Aristotle and phase decision;
13. strongest adversarial attack;
14. final `CODEX DIRECTIVE` block.

