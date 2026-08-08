# PROSHKA REQUEST — GOAL 057 B3.0B3 EXACT ARCH-SYMBOL WEIGHTED-MODE L2 RELEASE

```yaml
REQUEST_CLASS: DELEGATED_STRATEGIC_REVIEW
OPERATIVE_CLASSES_ALLOWED: [TRY_, KILL_, RUN_]
SOURCE_LOCK_COMMIT: cb77ae4d011bb1807a88889a4304cb6651fc5a7c
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

The published B3.0B2 transaction is:

```text
COMMIT: cb77ae4d011bb1807a88889a4304cb6651fc5a7c
SUCCESS: GOAL057_B3_0B2_EXACT_ARCH_SYMBOL_DOMINATION_PROVED
LEAN: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarExactArchSymbolLogDomination.lean
LEAN_SHA256: 197daeed0b975bbed63cf59d2f0cfa939ed345661935d258f7e79387815344da
PUBLIC: 1 definition + 2 theorems
PROOF_DB: 9/9 proven
PLANTS: 8/8 fired
TARGET_BUILD: 7760 jobs PASS
FULL_BUILD: 7817 jobs PASS
Q3_CHECK: PASS
UNIT_TESTS: 80/80 PASS
STRICT_SPINE: P9_STRICT_PASS
ROUTE_CHECK: CHECK OK
NEXT_GAP: GOAL057_B3_0B3_EXACT_ARCH_SYMBOL_WEIGHTED_MODE_L2_TRANSFER
```

No B3.0B3 production file has been written.

## 2. Exact parent APIs

B3.0B1 proves the envelope-weighted fixed-mode theorem:

```lean
theorem vModeLogGrowthEnvelope_mul_fourier_logWindowZeroExtendedMode_memLp
    (i : PairIndex) (n : ℤ) :
    MemLp
      (fun t : ℝ =>
        (vModeLogGrowthEnvelope t : ℂ) *
          𝓕 (logWindowZeroExtendedMode i n) t)
      2 volume
```

B3.0B2 proves the exact source normalization and global domination:

```lean
def sourceArchimedeanMultiplier (t : ℝ) : ℝ :=
  -Real.log Real.pi +
    (Q3.digamma
      ((1 / 4 : ℂ) + Complex.I * (Real.pi * t : ℂ))).re

theorem sourceArchimedeanMultiplier_eq_neg_aStar_scaled (t : ℝ) :
    sourceArchimedeanMultiplier t =
      -Q3.a_star t / (2 * Real.pi)

theorem abs_sourceArchimedeanMultiplier_le_logGrowthEnvelope (t : ℝ) :
    |sourceArchimedeanMultiplier t| ≤
      (|Real.log Real.pi| + Real.log 4 + 7) *
        vModeLogGrowthEnvelope t
```

The coordinate correction remains load-bearing:

```text
source angular frequency s = 2*pi*t,
where t is Mathlib Fourier frequency.
The production multiplier at Mathlib coordinate t is hPlus(2*pi*t),
not hPlus(t).
```

## 3. Smallest existing measurability supplier

`q3.lean.aristotle/Q3/Proofs/A_Star_Properties.lean:262` proves:

```lean
theorem a_star_continuous_thm : Continuous Q3.a_star
```

It is sorry-free and has exactly the standard project axiom footprint:

```text
[propext, Classical.choice, Quot.sound]
```

The exact source multiplier is continuous by rewriting through
`sourceArchimedeanMultiplier_eq_neg_aStar_scaled` and applying
`Q3.a_star_continuous_thm.neg.div_const (2 * Real.pi)`.

The B3.0B1 mode-integrability helper is private.  A second private helper can
replay the direct compact-support proof:

```lean
private theorem logWindowZeroExtendedMode_integrable_for_exactArch
    (i : PairIndex) (n : ℤ) :
    Integrable (logWindowZeroExtendedMode i n) := by
  apply IntegrableOn.integrable_indicator
  · apply Continuous.integrableOn_Icc
    fun_prop
  · exact measurableSet_Icc
```

Official Mathlib documentation confirms the two APIs used by the transfer:

- `VectorFourier.fourierIntegral_continuous` gives continuity of the Fourier
  integral from integrability under the standard hypotheses;
- `MemLp` packages a.e. strong measurability with finite `eLpNorm`.

Proof authority remains the production Lean compile, not the documentation.

## 4. Exact Lean stdin preflight

The proposed child was compiled through stdin only.  No production file was
written.  Exact imports:

```lean
import Q3.Proofs.RouteB.D0PstarExactArchSymbolLogDomination
import Q3.Proofs.A_Star_Properties
```

Exact proposed public surface:

```lean
theorem sourceArchimedeanMultiplier_mul_fourier_logWindowZeroExtendedMode_memLp
    (i : PairIndex) (n : ℤ) :
    MemLp
      (fun t : ℝ =>
        (sourceArchimedeanMultiplier t : ℂ) *
          𝓕 (logWindowZeroExtendedMode i n) t)
      2 volume
```

The compiled proof uses exactly:

1. private continuity of `sourceArchimedeanMultiplier` from `a_star_continuous_thm`;
2. the private direct integrability helper above;
3. `VectorFourier.fourierIntegral_continuous` for exact-product measurability;
4. B3.0B1's weighted `MemLp` theorem;
5. B3.0B2's global pointwise absolute domination;
6. `MemLp.of_le_mul` with the explicit constant
   `|log pi| + log 4 + 7`.

Lean result:

```text
PASS
AXIOMS: [propext, Classical.choice, Quot.sound]
```

## 5. Exact decision requested

Choose exactly one operative primary and pin the smallest production surface,
imports, plant suite, success/stop codes, checkpoint effect, and next atom.

### Candidate A — one exact-symbol weighted-mode transfer (Codex recommendation)

Owned file:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  D0PstarExactArchSymbolWeightedModeL2.lean
```

Exact imports:

```lean
import Q3.Proofs.RouteB.D0PstarExactArchSymbolLogDomination
import Q3.Proofs.A_Star_Properties
```

Public surface: exactly the one theorem in section 4.  The two support lemmas
remain private.  No new definition is required.

This is a bounded fixed-`i`, fixed-`n` theorem.  It does not produce a uniform
cofinal-mode bound and must not be interpreted as a source form-domain or
operator-domain theorem.

Question inside Candidate A: is importing the existing sorry-free
`Q3.Proofs.A_Star_Properties` the correct narrow supplier, or should the
continuity proof be rederived directly from the B3.0B2/Digamma layer?  Codex
recommends importing the existing theorem: duplicating its special-function
continuity proof would add mathematical surface without reducing assumptions.

### Candidate B — widen B3.0B1 or B3.0B2 public support APIs first

Export the mode-integrability or multiplier-continuity helper, then make the
transfer file smaller.  This avoids private proof replay but mutates an already
closed child and widens its public API.  Codex recommends **KILL as unnecessary
refactor** unless you identify a concrete downstream reuse obligation.

## 6. Mandatory falsifier plants for any TRY/RUN release

Please repair, replace, or extend these, but do not silently drop their error
classes.

```text
P057_B3_0B3_1_EXACT_MEASURABILITY
  remove exact-symbol/Fourier-product measurability;
  expected: EXACT_ARCH_SYMBOL_MEASURABILITY_MISSING

P057_B3_0B3_2_ENVELOPE_AS_SYMBOL
  replace the exact multiplier by vModeLogGrowthEnvelope in the conclusion;
  expected: ARCH_SYMBOL_ENVELOPE_NOT_EXACT_SYMBOL

P057_B3_0B3_3_SOURCE_SCALE
  use the unscaled angular multiplier hPlus(t) at Mathlib frequency t;
  expected: SOURCE_ARCH_SYMBOL_SCALE_MISMATCH

P057_B3_0B3_4_ONE_SIDED_DOMINATION
  replace global absolute domination by a one-sided inequality;
  expected: ARCH_SYMBOL_ABSOLUTE_DOMINATION_MISSING

P057_B3_0B3_5_DOMAIN_OVERCLAIM
  infer source form-domain or associated-operator-domain membership;
  expected: FORM_DOMAIN_NOT_OPERATOR_DOMAIN

P057_B3_0B3_6_HEAVY_BACKEND_IMPORT
  import generated PSD/Step33 suppliers;
  expected: ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK

P057_B3_0B3_7_UNIFORMITY_OVERCLAIM
  infer a uniform cofinal-mode estimate from the fixed-i fixed-n theorem;
  expected: UNIFORM_COFINAL_MODE_BOUND_MISSING
```

## 7. Required response schema

```yaml
STATUS: OPEN | CONDITIONAL | CLOSED | KILLED
PRIMARY: exactly one TRY_/KILL_/RUN_ class
TARGET_FILE: exact path or NONE
EXACT_IMPORTS: exact list
PRIVATE_SUPPORT: exact declarations
PUBLIC_SURFACE: exact declarations
IMPORT_A_STAR_PROPERTIES: ALLOW | REJECT_WITH_REPLACEMENT
PLANTS: exact repaired list
SUCCESS_CODE: exact
STOP_CODE: exact
NEXT_GAP_AFTER_SUCCESS: exact
PARENT_B3_0B_EFFECT: OPEN | CLOSED
CHECKPOINT_EFFECT: closed integer / advanced only
FORBIDDEN_AFTER_SUCCESS: exact list
```

Answer the real route question: does the compiled bounded transfer correctly
close B3.0B, and if so what is the smallest next source-form/API atom?  Do not
collapse weighted fixed-mode `L2` into a form-domain or operator-domain claim.

## 8. Non-negotiable boundary

No authorization in this request to:

- edit any Lean file before your release;
- change the B3.0B1 or B3.0B2 public surface;
- import generated PSD/Step33 suppliers;
- use the source angular-frequency multiplier at the unscaled Mathlib frequency;
- treat `vModeLogGrowthEnvelope` as the exact symbol;
- assume or numerically fit the domination;
- claim a uniform cofinal-mode bound;
- define the source Weil form or associated operator graph;
- infer form-domain or operator-domain membership;
- edit the compressed-action file;
- decrement the ten-checkpoint ledger unless you explicitly establish closure;
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
