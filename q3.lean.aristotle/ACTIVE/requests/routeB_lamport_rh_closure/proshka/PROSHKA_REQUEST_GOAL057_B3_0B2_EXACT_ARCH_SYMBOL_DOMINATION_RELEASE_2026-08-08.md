# PROSHKA REQUEST — GOAL 057 B3.0B2 EXACT ARCH-SYMBOL DOMINATION RELEASE

```yaml
REQUEST_CLASS: DELEGATED_STRATEGIC_REVIEW
OPERATIVE_CLASSES_ALLOWED: [TRY_, KILL_, RUN_]
SOURCE_LOCK_COMMIT: c3885e03b67c9cf8c6361d3d451c1404ca565709
SOURCE_LOCK_BRANCH: rh_clean
SOURCE_LOCK_REMOTE: origin/rh_clean
PHASE_KEY_CHANGE: false
REUSE_SAME_LIVING_CHAT: true
ONE_PRIMARY_ONLY: true
OWNER_AUTHORITY_REQUIRED: false
PX_RH_CLAIM: NOT_MADE
```

## 1. Current machine state

Goal 057 remains open on the physical live bus.

```text
ROUTE: CHALLENGER / NOT_RH
ACTIVE_BUS_GOAL: 057
BUS_010: VOID
GOAL_055: HOLD
G2_CCM: FROZEN
ARISTOTLE_SUBMISSION: NONE
H4A1B: OPEN
COARSE_CHECKPOINTS_CLOSED: 0
COARSE_CHECKPOINTS_REMAINING: 10
CURRENT_CHECKPOINT: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
CURRENT_EFFECT: STRICTLY_ADVANCED_NOT_CLOSED
```

The published B3.0B1 transaction is:

```text
COMMIT: c3885e03b67c9cf8c6361d3d451c1404ca565709
SUCCESS: GOAL057_B3_0B1_LOG_GROWTH_ENVELOPE_WEIGHTED_L2_PROVED
LEAN: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarVModeLogWeightedL2.lean
LEAN_SHA256: beb6f951a5b3db4a0b234137a61e9968696f77ba53393419fabdeed239262c87
PUBLIC: 1 definition + 2 theorems
PROOF_DB: 9/9 proven
PLANTS: 6/6 fired
TARGET_BUILD: 7756 jobs PASS
FULL_BUILD: 7817 jobs PASS
Q3_CHECK: PASS
UNIT_TESTS: 80/80 PASS
STRICT_SPINE: P9_STRICT_PASS
ROUTE_CHECK: CHECK OK
NEXT_GAP: GOAL057_B3_0B2_EXACT_ARCH_SYMBOL_DOMINATION_BY_LOG_GROWTH_ENVELOPE
```

No B3.0B2 production file has been written.

## 2. Material correction to the previous source audit

The previous request said that production Lean had no ready complex-digamma
supplier with a global explicit logarithmic bound.  That statement was stale.
The current source tree contains a stronger fact than the audit found.

### 2.1 Exact production definitions

`q3.lean.aristotle/Q3/Basic/Defs.lean:61-67` defines

```lean
def digamma (s : ℂ) : ℂ :=
  deriv Complex.Gamma s / Complex.Gamma s

def a (ξ : ℝ) : ℝ :=
  Real.log Real.pi -
    (digamma (1/4 + Complex.I * Real.pi * ξ)).re

def a_star (ξ : ℝ) : ℝ :=
  2 * Real.pi * a ξ
```

### 2.2 Global sorry-free digamma remainder

`q3.lean.aristotle/Q3/DigammaRemainder.lean:9733` proves

```lean
lemma re_digamma_remainder_bound_stieltjes
    (z : ℂ) (hz : 0 < z.re) :
    |(Q3.digamma z).re - Real.log ‖z‖ +
        z.re / (2 * ‖z‖^2)| ≤
      1 / (4 * ‖z‖^2)
```

This is global on `Re z > 0`, not merely asymptotic.  On the exact source line

```text
z(t) = 1/4 + i*t/2
```

the premise is definitionally `0 < 1/4` for every real `t`.

### 2.3 Existing global a_star envelope, currently in the wrong dependency layer

`q3.lean.aristotle/Q3/Proofs/PSD_CenteredCoeffAnalyticABoundsBackend.lean`
already contains

```lean
def aStarTailArg (t : ℝ) : ℂ :=
  (1 / 4 : ℂ) + Complex.I * Real.pi * t

def aStarStieltjesLogEnvelope (t : ℝ) : ℝ := ...

theorem a_star_abs_le_stieltjesLogEnvelope (t : ℝ) :
  |Q3.a_star t| ≤ aStarStieltjesLogEnvelope t
```

The proof consumes the global Stieltjes theorem above and is sorry-free.
However, that theorem sits inside a 9,107-line Step33 backend importing
generated PSD payload/dictionary/hbox modules.  Route B must not depend on
that backend merely to recover a generic digamma estimate.

Dependency rule for this release:

```text
ALLOWLIST: Q3.DigammaRemainder
EXCLUDE: Q3.Proofs.PSD_CenteredCoeffAnalyticABoundsBackend
EXCLUDE: generated PSD/Step33 suppliers
```

`Q3.DigammaRemainder` is a live foundational supplier.  The PSD backend is a
consumer-specific generated layer.

## 3. Exact scaling crosswalk is already Lean-checked

The source multiplier named by your B3 verdict is

```text
hPlus(t) = -log pi + Re Psi(1/4 + i*t/2).
```

A temporary source-audit file importing only `Q3.DigammaRemainder` and the
published B3.0B1 module compiled this theorem:

```lean
def sourceArchSymbolAudit (t : ℝ) : ℝ :=
  -Real.log Real.pi +
    (Q3.digamma
      ((1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re

example (t : ℝ) :
    sourceArchSymbolAudit t =
      -Q3.a_star (t / (2 * Real.pi)) / (2 * Real.pi) := by
  ...
```

Lean result: **PASS**.  The temporary file was removed.

Thus B3.0B2 is not a new special-function construction.  It is a
source-normalization crosswalk plus a global comparison between the existing
Stieltjes envelope and B3.0B1's elementary envelope.

## 4. Database and semantic-search result

Local semantic search was run with four queries:

1. global exact digamma bound / `a_star` logarithmic envelope;
2. `re_digamma_remainder_bound_stieltjes` / Stieltjes envelope;
3. archimedean symbol / mode Fourier L2 / operator domain;
4. `a_star` absolute log growth for all real `t`.

It found the hidden supplier through the Step33 monitor and backend.

The cartographer `capability` table has 507 rows but returns **zero** rows for
`digamma`, `a_star`, `stieltjes`, `log envelope`, and `logarithmic`.
Therefore the earlier miss is also a capability-index coverage bug.  That bug
must be repaired later, but it does not block this Lean transaction.

The external source check is consistent with this route:

- NIST DLMF §5.11 records the complex digamma/Gamma asymptotic and error-bound
  framework;
- Connes--Consani, *Weil positivity and Trace formula, the archimedean place*,
  is the primary operator/source context;
- proof authority here remains the checked local Stieltjes theorem, not the
  prose asymptotic.

## 5. Exact decision requested

Choose exactly one operative primary for B3.0B2 and pin the smallest public
surface, imports, theorem statement, and plant suite.

### Candidate A — direct minimal Route B derivation (Codex recommendation)

Owned file:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  D0PstarExactArchSymbolLogDomination.lean
```

Proposed exact imports:

```lean
import Q3.Proofs.RouteB.D0PstarVModeLogWeightedL2
import Q3.DigammaRemainder
```

Proposed public definition:

```lean
def sourceArchimedeanMultiplier (t : ℝ) : ℝ :=
  -Real.log Real.pi +
    (Q3.digamma
      ((1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re
```

Proposed public normalization theorem:

```lean
theorem sourceArchimedeanMultiplier_eq_neg_aStar_scaled (t : ℝ) :
    sourceArchimedeanMultiplier t =
      -Q3.a_star (t / (2 * Real.pi)) / (2 * Real.pi)
```

Proposed public domination theorem shape:

```lean
theorem exists_pos_abs_sourceArchimedeanMultiplier_le_logGrowthEnvelope :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      |sourceArchimedeanMultiplier t| ≤
        C * vModeLogGrowthEnvelope t
```

The proof must derive the constant from the Stieltjes estimate.  It may choose
a coarse explicit constant.  It must not accept the domination as a premise,
fit a constant numerically, or restrict the conclusion to a tail.

Question inside Candidate A: should this child stop after the domination
theorem, or also include the immediate exact-multiplier `MemLp 2` corollary
obtained from B3.0B1?  My recommendation is **stop after domination** unless
you determine that the corollary is definitional bookkeeping and belongs in
the same bounded transaction.

### Candidate B — import the Step33 backend and wrap its theorem

This is shorter at the line level but creates an invalid dependency from
Route B into generated PSD/Step33 consumers.  My recommendation: **KILL as the
production dependency**, while retaining the backend theorem as proof-shape
evidence.

### Candidate C — first refactor the generic Stieltjes envelope out of Step33

Create a new generic core module and make both Step33 and Route B import it.
This is architecturally clean but wider than the current source gap.  My
recommendation: park unless direct Candidate A would duplicate substantial
mathematics rather than only a bounded comparison proof.

## 6. Mandatory falsifier plants for any TRY/RUN release

Please repair, replace, or extend these, but do not silently drop their error
classes.

```text
P057_B3_0B2_1_SCALE_PI_TO_HALF
  mutate t/(2*pi) to t/2 in the a_star crosswalk;
  expected: SOURCE_ARCH_SYMBOL_SCALE_MISMATCH

P057_B3_0B2_2_SIGN
  mutate -a_star/(2*pi) to +a_star/(2*pi);
  expected: SOURCE_ARCH_SYMBOL_SIGN_MISMATCH

P057_B3_0B2_3_ONE_SIDED_NOT_ABSOLUTE
  replace |hPlus(t)| domination by hPlus(t) domination;
  expected: ARCH_SYMBOL_ABSOLUTE_DOMINATION_MISSING

P057_B3_0B2_4_TAIL_NOT_GLOBAL
  prove only |t| > T or t > T;
  expected: ARCH_SYMBOL_COMPACT_REGION_MISSING

P057_B3_0B2_5_NUMERIC_OR_PREMISE_CONSTANT
  fit C numerically or assume the desired inequality;
  expected: ARCH_SYMBOL_SOURCE_PROOF_MISSING

P057_B3_0B2_6_HEAVY_BACKEND_IMPORT
  import PSD_CenteredCoeffAnalyticABoundsBackend;
  expected: ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK

P057_B3_0B2_7_ENVELOPE_AS_SYMBOL
  identify vModeLogGrowthEnvelope with hPlus by definition;
  expected: ARCH_SYMBOL_ENVELOPE_NOT_EXACT_SYMBOL

P057_B3_0B2_8_RE_POS_ERASURE
  use Stieltjes without proving Re(1/4+i*t/2)>0;
  expected: DIGAMMA_STIELTJES_DOMAIN_PREMISE_MISSING
```

## 7. Required response schema

```yaml
STATUS: OPEN | CONDITIONAL | CLOSED | KILLED
PRIMARY: exactly one TRY_/KILL_/RUN_ class
TARGET_FILE: exact path or NONE
EXACT_IMPORTS: exact list
PUBLIC_SURFACE: exact declarations
CONSTANT_POLICY: explicit | existential | rejected
IMMEDIATE_MEMLP_COROLLARY: SAME_CHILD | NEXT_CHILD | REJECTED
PLANTS: exact repaired list
SUCCESS_CODE: exact
STOP_CODE: exact
NEXT_GAP_AFTER_SUCCESS: exact
CHECKPOINT_EFFECT: closed integer / advanced only
FORBIDDEN_AFTER_SUCCESS: exact list
```

Answer the real route question: does the newly found global Stieltjes supplier
make Candidate A a bounded executable child, or is there a precise hidden
normalization/API obstruction that still prevents it?

## 8. Non-negotiable boundary

No authorization in this request to:

- edit any Lean file before your release;
- import the generated PSD/Step33 backend into Route B;
- treat `vModeLogGrowthEnvelope` as the exact symbol;
- assume or numerically fit the domination;
- define the source Weil form or associated operator graph;
- infer form-domain or operator-domain membership;
- edit the compressed-action file;
- decrement the ten-checkpoint ledger;
- invoke H4a1b;
- create Bus 010;
- release Goal 055 or unfreeze G2/CCM;
- submit Aristotle;
- promote Route B;
- make PX or RH claims;
- open a fresh chat;
- click `Answer now` / `Antwort jetzt` / `Ответить сейчас`.

The sole owner gate remains `PX_RH_CLAIM`.  This is a delegated strategic
review inside the existing Goal 057 phase.
