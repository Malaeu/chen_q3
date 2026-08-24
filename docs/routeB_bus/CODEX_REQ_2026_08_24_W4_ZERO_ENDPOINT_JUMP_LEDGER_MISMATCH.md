# CODEX_REQ — W4 zero-endpoint jump-ledger mismatch

```yaml
REQUEST_SCHEMA: q3_codex_request.v1
CODEX_REQ: REQ-2026-08-24-W4-ZERO-ENDPOINT-JUMP-LEDGER
ELIGIBILITY: FATAL
CODEX_SESSION_ID: 01a022d7-0d31-7951-b6e4-e1ab983a1e83
PHASE_KEY_HASH: 1c0914e2e93a49defedf2c8a8497fbdc22de993b7404e0426e4b2d6c131f9aae
BLOCKER_FINGERPRINT: 0aabc895314f59028e540621af5e8382478aa7dbb6b010e04f779c8545a6ae04
SOURCE_OBJECT: selectedFerrersAbelLogZeroExtension of the exact full-endpoint selectedFerrersAbelLimit representative
TERMINAL_CONSUMER: fixed-k ordinary Fourier decay required by W4 shifted form-domain assembly
WALL: The frozen lower-endpoint budget uses the norm of the full value g(0), but piecewise integration by parts uses the right limit; x=0 is itself the omitted n=k+2 production seam, whose endpoint term is not present in the internal sum n=2..k+1.
TRIED:
  - The authorized packet absolute-continuity theorem and the complex derivative interval-integrability theorem were proved and accepted by Lean with the standard axiom triple.
  - Lean accepted the exact finite-comb decomposition showing that the n=k+2 endpoint term is present at x=0.
  - Lean accepted that the same n=k+2 term is identically zero immediately to the right of x=0 because its packet argument is strictly larger than lambda.
  - The complete ask.sh shelf was queried for a packet endpoint-zero theorem or a right-limit norm inequality; no exact supplier was found.
ASK_SHELF_RECEIPT: ASK_SH_2026_08_24_SELECTED_FERRERS_PACKET_LAMBDA_ENDPOINT_ZERO_NO_EXACT_SUPPLIER
CHEAPEST_KILLER_RUN: Decide whether the exact packet supplies either h_k(lambda_k)=0 or norm(rightLimit(g_k,0))<=norm(g_k(0)); otherwise repair the frozen jump ledger by adding the n=k+2 lower-endpoint seam or by naming the right-limit representative explicitly.
PROGRESS_DELTAS:
  - kind: BLOCKER_DECOMPOSED
    scope: ABSTRACT
    verifier: LEAN
    subject_id: W4_LOG_COORDINATE_FINITE_JUMP_FOURIER_DECAY
    before: The frozen ledger classified only n=2..k+1 as production seams and treated x=0 solely as a zero-extension jump.
    after: The exact lower endpoint is proved to carry both the full value and a separate n=k+2 point-to-right seam term.
    decision_effect: BLOCKER_STRICTLY_SHRUNK
    evidence: Direct Lean exit 0 for w4_zeroEndpoint_is_productionSeam, w4_zeroEndpoint_core_decomposition, and w4_zeroEndpointTopTerm_zero_of_pos in the authorized local source.
NEED: Independently adjudicate the exact lower-endpoint ledger and freeze the smallest corrected public budget and Fourier-decay theorem without changing the production packet or endpoint convention.
BLOCKS: H2A_4_1B_3C_1_13A_W4_PIECEWISE_AC_DERIVATIVE_INTEGRABILITY_LEAN
REQUEST_BLOB: 38791b1ab648beb4b5682d55cd1984576747dc3e179d32260dbeb264f697dbbc
SOURCE_COMMIT: 76f523dcd4167053ecc2772f5344b58fe7e23392
```

<!-- REQUEST_PAYLOAD_UTF8_BEGIN -->
PROSHKA OPERATIVE REVIEW — W4 LOWER-ENDPOINT JUMP-LEDGER MISMATCH

Branch: rh_clean
Request ID: REQ-2026-08-24-W4-ZERO-ENDPOINT-JUMP-LEDGER
Source commit: 76f523dcd4167053ecc2772f5344b58fe7e23392
Same living phase chat: 6a8c3e2a-df50-83eb-b53d-dd4cc46f646f
Phase key hash: 1c0914e2e93a49defedf2c8a8497fbdc22de993b7404e0426e4b2d6c131f9aae
Blocker fingerprint: 0aabc895314f59028e540621af5e8382478aa7dbb6b010e04f779c8545a6ae04

Read these committed artifacts in full:

1. docs/routeB_bus/proshka/PROSHKA_VERDICT_CODEX_REQ_2026_08_24_W4_PIECEWISE_AC_AUTHORIZATION_2026-08-24.md
2. q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersAbelPoissonL2.lean
3. q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersPacketVariation.lean
4. q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarActualProlateEStarMemLp.lean

The first half of the authorized Lean node is kernel-green.  The exact
complex packet is absolutely continuous on its closed physical window, the
exact additive-log representative is absolutely continuous on every
seam-free compact interval, and its complex derivative is interval-integrable
there.  All three printed public surfaces have exactly:

  [propext, Classical.choice, Quot.sound]

The hand-written piecewise integration-by-parts step exposes an exact defect
in the frozen lower-endpoint jump budget.

Put

  lambda = lambda_m (selectedFerrersPreAnchorIndex k) = sqrt(k+2),
  h = selectedFerrersLemma73SourcePacket k,
  S = sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k),
  N = k+2.

Then N belongs to S and Lean accepts the exact identity

  N * exp(0) / lambda = lambda.

Consequently the full finite comb at x=0 decomposes as

  finiteEStarCore S h (1/lambda)
    = sum_{n in S erase N} h(n/lambda) + h(lambda).

For every x>0, the N-term has argument

  N * exp(x) / lambda = lambda * exp(x) > lambda

and is therefore exactly zero by the production closed-window support
theorem.  The half-center shadow is continuous.  Thus, writing g for the
exact additive-log representative and J0 for the omitted endpoint term,

  g(0) = rightLimit(g,0) + J0,
  J0 = sqrt(1/lambda) * h(lambda).

Piecewise integration by parts on the first open component uses
rightLimit(g,0), not the isolated full value g(0).  The frozen budget is

  norm(g(0))
  + norm(g(L))
  + sum_{n=2}^{k+1} norm(sqrt(lambda/n) * h(lambda)).

It contains neither norm(rightLimit(g,0)) as such nor the missing N=k+2 seam
term norm(J0).  The triangle inequality only gives

  norm(rightLimit(g,0)) <= norm(g(0)) + norm(J0),

not the bound by norm(g(0)) required by the frozen ledger.  The project shelf
contains no theorem that h(lambda)=0 and no theorem proving
norm(rightLimit(g,0))<=norm(g(0)).  The production endpoint value is not
allowed to be silently changed to a midpoint or zero value.

This is not an API inconvenience.  It is an exact endpoint-ledger mismatch.
The smallest evident sufficient repair is one of:

1. retain norm(g(0)) and extend the seam sum through n=k+2, so triangle
   inequality pays the missing J0 term; or
2. replace the lower endpoint entry by the norm of the explicit right-limit
   representative and keep the internal seam range n=2..k+1; or
3. provide and bind an exact existing supplier proving the stronger endpoint
   cancellation or norm inequality.

Adjudicate the mathematical statement.  Return exactly one operative class:

  TRY_W4_ZERO_ENDPOINT_JUMP_LEDGER_REPAIR
  RUN_W4_ZERO_ENDPOINT_CANCELLATION_IDENTITY
  KILL_W4_FROZEN_FOURIER_DECAY_BOUND

If TRY, freeze all of:

  - the corrected exact public jump-budget definition;
  - the corrected off-zero Fourier-decay theorem;
  - the exact interpretation of the lower one-sided representative;
  - whether n=k+2 is paid separately or absorbed by a proved inequality;
  - the unchanged complex/full-endpoint/fixed-k conventions;
  - the existing authorized Lean path and validation commands;
  - CLOSES, OPENS, and NEXT_LOAD_BEARING_GAP.

Write and commit the independent verdict to rh_clean under:

  docs/routeB_bus/proshka/
  PROSHKA_VERDICT_CODEX_REQ_2026_08_24_W4_ZERO_ENDPOINT_JUMP_LEDGER_REPAIR_2026-08-24.md

Do not start the downstream shifted-form-domain assembly.  Do not modify any
historical pushed artifact.  Do not promote Route B and do not make an RH
claim.
<!-- REQUEST_PAYLOAD_UTF8_END -->
