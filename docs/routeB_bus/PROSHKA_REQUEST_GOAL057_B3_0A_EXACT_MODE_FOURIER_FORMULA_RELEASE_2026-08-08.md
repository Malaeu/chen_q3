# PROSHKA REQUEST — GOAL 057 B3.0A EXACT MODE FOURIER FORMULA OPERATIONAL RELEASE

```yaml
MODE: DELEGATED_STRATEGIC_REVIEW
TRANSACTION: GOAL057_B3_0A_EXACT_MODE_FOURIER_FORMULA_RELEASE
CONVERSATION_ID: 6a72e750-dc60-83eb-946b-61d2073c232b
PHASE_KEY: UNCHANGED
HEAD: eb1c5d8cba978b7e7005819641fbabd532e3f97f
ORIGIN_RH_CLEAN: eb1c5d8cba978b7e7005819641fbabd532e3f97f
HEAD_ORIGIN_EQUAL: true
PARENT_PRIMARY: WALL_GOAL057_B3_0_SOURCE_FORM_REPRESENTATION_API_MISSING
PARENT_VERDICT_SHA256: 7106b3629538eeed897914bd930a4f0c35f7c669a95880c969aa594f38acb58c
PARENT_CORRECTIONS_SHA256: 78975e773dfbe1057cb21a4ff44b4d2cc7ef61e364440acc26a95259b2bb3148
REQUESTED_CHILD: GOAL057_B3_0A_EXACT_MODE_FOURIER_FORMULA
OWNER_GATE: PX_RH_CLAIM_ONLY
```

## Why this is now an operational release request

The parent WALL selected this exact smallest replacement transaction but set
`release_in_this_verdict: false`. Codex has now completed the required direct
Lean preflight without touching production Lean.

Attached preflight:

```yaml
path: q3.lean.aristotle/.scratch/Goal057B30APreflight.lean
sha256: a7cf28980344c70d22c6bd428fb4ab7537a35f9bbff1f403023a2076f67719f0
bytes: 4881
lines: 146
command: lake env lean .scratch/Goal057B30APreflight.lean
exit: 0
printed_axioms:
  - propext
  - Classical.choice
  - Quot.sound
sorryAx: absent
```

Release or reject only this already-preflighted two-declaration child. Do not
authorize B3.0B or reconstruct the associated operator graph in this review.

## Corrected source and production pins

The earlier request's nonexistent
`Q3/Proofs/RouteB/D0PstarFiniteProjection.lean` pointer was corrected before
the parent verdict. The exact current carriers are in:

- `Q3/Proofs/RouteB/D0KTrialStage1.lean` for `H_m`, `V_n_m`, `E_m_N`, and
  `P_m_N`;
- `Q3/Proofs/RouteB/D0FiniteProjectionReconstruction.lean` for the finite
  reconstruction API;
- `Q3/Proofs/RouteB/D0LogWindowMeasureTransport.lean` for exact
  `du/u -> dx` transport and the literal log-window modes;
- `Q3/Proofs/RouteB/FplusConstantMode.lean` for the existing exact
  exponential interval-integral proof pattern.

Primary-source text:

```yaml
fulltext_path: q3.lean.aristotle/literature/zotero/H8ULBMAL/fulltext.md
fulltext_sha256: 7ba4b01845df2989cdd763a19c83904e4114e26fc51d5d7f93d09489d52871d4
pdf_path: docs/routeB_bus/litreview/pdfs/2511.22755.pdf
pdf_sha256: c98d89f7fc999d038e15e80a9aaaee2af797c17711c4329ca7ce48ad49cb336b
```

## Exact owned production child

If released, Codex will materialize only:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarVModeFourierFormula.lean
```

Exact minimal imports:

```lean
import Q3.Proofs.RouteB.D0LogWindowMeasureTransport
import Mathlib.Analysis.Fourier.FourierTransform
```

Exact namespace:

```lean
namespace Q3.RouteB.D0Pstar
```

Exact complete public surface:

```lean
def logWindowZeroExtendedMode
    (i : PairIndex) (n : ℤ) : ℝ → ℂ :=
  Set.indicator (Set.Icc 0 (L_m i))
    (fun x =>
      ((Real.sqrt (L_m i))⁻¹ : ℂ) *
        Complex.exp
          (2 * Real.pi * Complex.I * n *
            (x / L_m i)))

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

No public premise, carrier isometry, weighted-L2 claim, form-domain claim, or
operator-domain claim is included.

## Convention lock proved by the preflight

```yaml
mathlib_fourier_kernel: exp(-2*pi*I*x*t)
mode_phase: exp(+2*pi*I*n*x/L_m)
combined_phase: exp(2*pi*I*(n/L_m-t)*x)
window: Set.Icc 0 (L_m i)
measure: volume_dx
resonance: t = n/L_m
resonant_value: sqrt(L_m)
normalization: inverse_sqrt_L_m
```

The preflight proves the formula by rewriting the Mathlib Fourier integral to
the exact zero-extension window, combining the negative Fourier kernel with
the positive mode phase, splitting resonance, and using
`integral_exp_mul_complex` off resonance. It uses `logLength_pos` at the only
division/square-root obligations.

## K6 object precommit

```yaml
OBJECT_CLASS: SOURCE_LOCKED_LOG_WINDOW_ZERO_EXTENDED_MODE
INPUT:
  - PairIndex i
  - integer mode n
OUTPUT:
  - literal function R -> C supported on Icc 0 (L_m i)
  - exact Mathlib Fourier transform formula at every real t
PRESERVED_INVARIANTS:
  - negative Mathlib Fourier sign
  - positive source mode sign
  - interval orientation 0_to_L_m
  - inverse_sqrt_L_m normalization
  - resonance at n/L_m with value sqrt_L_m
EXCLUDED_MEANINGS:
  - no L2 Plancherel carrier
  - no arch-symbol weighted-L2 certificate
  - no source Weil form
  - no associated operator graph
  - no operator-domain membership
  - no compression identity
```

## Mandatory independent plants

```yaml
- id: P057_B3_0A_FOURIER_SIGN
  mutation: replace Mathlib kernel sign - with + or replace n/L_m-t by n/L_m+t
  required_stop: SOURCE_WEIL_FOURIER_SIGN_MISMATCH

- id: P057_B3_0A_WINDOW_ORIENTATION
  mutation: use Icc (-L_m/2) (L_m/2), Icc (-L_m) 0, or omit zero extension
  required_stop: SOURCE_WEIL_ZERO_EXTENSION_WINDOW_PHASE_MISMATCH

- id: P057_B3_0A_MEASURE_TRANSPORT
  mutation: identify dx with du instead of du/u under x=log(lambda_m*u)
  required_stop: SOURCE_WEIL_DSTAR_TO_DX_TRANSPORT_MISMATCH

- id: P057_B3_0A_DISCRETE_WEIGHT_SURROGATE
  mutation: substitute physicalFourierWeight or finite coefficient energy for this continuous Fourier formula
  required_stop: SOURCE_WEIL_DISCRETE_PHYSICAL_WEIGHT_NOT_ARCH_MULTIPLIER
```

Each plant is independent. No mutation is allowed to PASS by changing the
statement.

## Required ruling

Return exactly one operative primary:

```yaml
A: TRY_GOAL057_B3_0A_EXACT_MODE_FOURIER_FORMULA
B: KILL_GOAL057_B3_0A_EXACT_MODE_FOURIER_FORMULA_SOURCE_MISMATCH
C: WALL_GOAL057_B3_0A_EXACT_MODE_FOURIER_FORMULA_RELEASE_DEFECT
```

If A, confirm all of:

1. the exact owned file, two imports, namespace, and two-declaration public
   surface above;
2. the attached preflight is an acceptable direct Lean witness;
3. private helpers may be copied/refactored without changing the statement;
4. all four plants and stop codes are binding;
5. validation: direct file compile, hole scan, `#print axioms`, production
   build, route checks, and observability refresh;
6. success code
   `GOAL057_B3_0A_EXACT_MODE_FOURIER_FORMULA_PROVED`;
7. next gap only
   `GOAL057_B3_0B_ARCH_SYMBOL_LOG_WEIGHTED_L2_CERTIFICATE`;
8. exact ledger effect: this infrastructure child must not be misreported as
   closing the ten-checkpoint numerator bridge;
9. Aristotle remains forbidden;
10. six-field phase key remains unchanged and the same living chat continues.

If B or C, identify the exact first mismatch in the attached proved formula or
the release packet. Do not reopen the already falsified six-declaration B3.0
child and do not return a general research plan.

## Hard boundaries

```yaml
FORBIDDEN:
  - edit any file other than D0PstarVModeFourierFormula.lean if TRY
  - alter the exact public definition or theorem statement
  - introduce sorry, admit, axiom, or public hypothesis
  - treat the pointwise formula as an L2 Plancherel theorem
  - claim arch-symbol weighted-L2 integrability
  - infer form-domain or operator-domain membership
  - define the source Weil form or associated operator graph
  - edit D0PstarCCMCompressedWeilAction.lean
  - close H4a1b
  - decrement the ten-checkpoint ledger without an explicit ruling
  - create Bus_010
  - release Goal_055 or G2_CCM
  - promote Route_B
  - make PX or RH claim
  - open a fresh chat
```

Final boundary remains:

```yaml
route: CHALLENGER_NOT_RH
bus_010: VOID
goal_055: HOLD
g2_ccm: FROZEN
Aristotle_submission: NONE
route_promotion: false
px_rh_claim: NOT_MADE
```
