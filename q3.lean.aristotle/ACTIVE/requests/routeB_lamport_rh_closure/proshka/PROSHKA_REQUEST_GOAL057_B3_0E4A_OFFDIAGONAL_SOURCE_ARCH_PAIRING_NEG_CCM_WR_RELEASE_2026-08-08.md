# PROSHKA REQUEST — GOAL 057 B3.0E4A OFF-DIAGONAL SOURCE ARCHIMEDEAN PAIRING / NEGATIVE CCM-WR RELEASE

Date: 2026-08-08
Route: Route B (`CHALLENGER_NOT_RH`)
Goal: 057
Mode: `DELEGATED_STRATEGIC_REVIEW`
Requested decision: one production-release verdict for a compiling untracked
no-`sorry` preflight.

## Source lock

```yaml
repo: Malaeu/chen_q3
branch: rh_clean
head: ce7f7f492cabfa48b5b3628a3842d09508114df8
origin_rh_clean: ce7f7f492cabfa48b5b3628a3842d09508114df8
head_equals_origin: true
parent_production_close: 3df702ead9729e187d3fbdf461452e25bb7c8bae
route_checker: CHECK_OK
active_goal: 057
bus_010: VOID
goal_055: HOLD
g2_ccm: FROZEN
aristotle_submission: NONE
coarse_checkpoints_closed: 0
coarse_checkpoints_remaining: 10
px_rh_claim: NOT_MADE
```

The exact primary source is Connes--Consani--Moscovici,
*Zeta Spectral Triples*, arXiv:2511.22755v1. Equations (2.7)--(2.10) fix the
antilinear-first off-diagonal correlation and sine order; equation (4.4)
fixes the archimedean endpoint constant plus the integral on `[0,L]`.

## Current closed parents

- B3.0D: `sourceArchimedeanModePairing` is the named conjugate-first source
  pairing.
- B3.0E1: `sourceArchimedeanMultiplier` is the exact constant minus twice the
  regularized hyperbolic kernel integral.
- B3.0E2: the literal joint kernel-mode product is integrable on
  `volume.prod (volume.restrict (Set.Ioi 0))`; this is the Fubini carrier.
- B3.0E3: twice the zero-extended cosine correlation equals `ccmQKernel` on
  the log window and zero outside, with the right boundary proved zero.

None of those parents proves the requested negative `ccmWREntry` crosswalk.

## Exact harness

Path:

`q3.lean.aristotle/Goal057B3_0E4A_Scratch.lean`

```yaml
bytes: 12483
lines: 310
sha256: 4a9910f66a31400d244b240514b69dd8eb3f414401bc3226f503fd95385ce79e
direct_lean: PASS
forbidden_tokens: 0
public_definitions: 0
public_theorems: 1
private_definitions: 2
private_theorems: 11
ordered_controls: 2
axioms: [propext, Classical.choice, Quot.sound]
```

Exact imports:

```lean
import Q3.Proofs.RouteB.D0PstarSourceArchModePairingKernel
import Q3.Proofs.RouteB.D0PstarSourceArchKernelModeProductL1
import Q3.Proofs.RouteB.D0PstarSourceModeCosineCCMQKernel
import Mathlib.MeasureTheory.Integral.Prod
```

There is no new Step33, hbox, numeric-payload, generated-PSD or direct
Aristotle-output import. The already audited historical inherited dependency
through the closed parent chain is unchanged.

## Proposed public theorem

```lean
theorem sourceArchimedeanModePairing_eq_neg_ccmWREntry_of_ne
    (i : PairIndex) {n r : ℤ} (hnr : n ≠ r) :
    sourceArchimedeanModePairing i n r =
      -(Q3.RouteB.ccmWREntry (L_m i) n r : ℂ)
```

No public helper or control wrapper is proposed.

## Proof ledger

1. Local Plancherel carriers prove the bare conjugate-first mode product is
   `L1`; multiplying by cosine preserves `L1`.
2. Public B3.0E3 at `x=0` proves the bare product integral is zero when
   `n ≠ r`.
3. Unfolding the exact regularized kernel gives, for `x>0`,

   ```text
   exp(x/2)/den * cosineModeProduct
   - exp(-x)/den * bareModeProduct.
   ```

4. Therefore twice the inner `t`-integral is `ccmWRIntegrand` on
   `x ≤ L_m i` and zero for `x > L_m i`.
5. The proof consumes
   `MeasureTheory.integral_integral_swap` with the public B3.0E2 joint
   carrier. It is not a fiberwise-only exchange.
6. The constant part of `sourceArchimedeanMultiplier` vanishes by the same
   off-diagonal bare-product identity.
7. The piecewise integral on `(0,∞)` is reduced literally to `(0,L]`.
8. `ccmQKernel (L_m i) n r 0 = 0` removes the endpoint term in
   `ccmWREntry`. The outer `-2` cancels the correlation factor `1/2`, leaving
   exactly the negative entry.

## Ordered controls

Both compile from the same public theorem:

```lean
sourceArchimedeanModePairing i 0 1 =
  -(Q3.RouteB.ccmWREntry (L_m i) 0 1 : ℂ)

sourceArchimedeanModePairing i 1 0 =
  -(Q3.RouteB.ccmWREntry (L_m i) 1 0 : ℂ)
```

Thus symmetry is not being used to hide an index reversal.

## Mandatory attacks

```yaml
P057_B3_0E4A_1_OFFDIAGONAL_ZERO_CONSTANT:
  stop: SOURCE_OFFDIAGONAL_CCM_QKERNEL_ZERO_CONSTANT_MISSING
P057_B3_0E4A_2_FUBINI:
  stop: SOURCE_ARCH_JOINT_FUBINI_CARRIER_NOT_CONSUMED
P057_B3_0E4A_3_SIGN:
  stop: SOURCE_ARCH_CCM_WR_FINAL_SIGN_MISMATCH
P057_B3_0E4A_4_SUPPORT:
  stop: SOURCE_MODE_ZERO_EXTENSION_SUPPORT_MISMATCH
P057_B3_0E4A_5_ORIENTATION:
  stop: SOURCE_FORM_ANTILINEAR_FIRST_ORIENTATION_MISMATCH
P057_B3_0E4A_6_ORDERED_CONTROLS:
  stop: SOURCE_ARCH_OFFDIAGONAL_INDEX_ORDER_MISMATCH
P057_B3_0E4A_7_DEPENDENCY:
  stop: ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK
```

## Requested verdict

Please decide:

1. Does the compiling harness close the exact B3.0E4A discriminator, or is
   there a first source/sign/Fubini/coercion defect?
2. If accepted, release exactly one production file and name its exact path,
   import list, public surface and private ceiling.
3. Should the two ordered controls remain harness-only, become private named
   controls, or be omitted from production after preflight?
4. Does successful production validation close B3.0E4A only, leaving B3.0E
   and the ten-checkpoint ledger open?
5. Is the next atom B3.0E4B (diagonal endpoint constant), or is a smaller
   source-locked assembly required first?

Return exactly one operative class `TRY_*`, `KILL_*`, or `RUN_*`, the first
load-bearing attack, exact production boundary, next smallest gap and
forbidden moves.

## Hard boundary

- Do not release or infer B3.0E4B in this transaction.
- Do not define the full source Weil form or associated operator graph.
- Do not decrement the coarse checkpoint ledger.
- Do not invoke H4a1b.
- Do not promote Route B.
- Do not make or request `PX_RH_CLAIM`.
- Do not claim RH.
