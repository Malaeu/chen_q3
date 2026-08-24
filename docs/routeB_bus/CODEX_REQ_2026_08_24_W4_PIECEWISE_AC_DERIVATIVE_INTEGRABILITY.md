# CODEX_REQ — W4 piecewise-AC derivative integrability authorization

```yaml
REQUEST_SCHEMA: q3_codex_request.v1
CODEX_REQ: REQ-2026-08-24-W4-PIECEWISE-AC
ELIGIBILITY: OPERATIVE_REVIEW_GATE
CODEX_SESSION_ID: 01a022d7-0d31-7951-b6e4-e1ab983a1e83
PHASE_KEY_HASH: 1c0914e2e93a49defedf2c8a8497fbdc22de993b7404e0426e4b2d6c131f9aae
BLOCKER_FINGERPRINT: 85280424cfb0e1bd5693d79ee77d9c3fcee1fe43691b30ee5c5dbfac4be76200
SOURCE_OBJECT: selectedFerrersAbelLimit additive-log zero extension under sourceLogWindowFourierL2Isometry
TERMINAL_CONSUMER: sourceArchimedeanShiftedFormDomain for each fixed selectedFerrersPreAnchorIndex k
WALL: The pinned global Fourier derivative theorem requires everywhere differentiability, while the exact production representative has two endpoint jumps and finitely many full-endpoint seams; W4 therefore needs a piecewise absolute-continuity and derivative-integrability assembly plus hand-written piecewise integration by parts.
TRIED:
  - Exact downstream consumer, additive-log source object, finite seam ledger, and symbol weight crosswalk were audited in the committed W4 preflight.
  - The ask.sh shelf was queried for W4_PIECEWISE_AC_DERIVATIVE_INTEGRABILITY_LEMMA; it found the preflight but no existing exact supplier.
  - Mathlib fourier_deriv was checked and rejected because it assumes Differentiable on all of R.
  - Mathlib AbsolutelyContinuousOnInterval algebra was pinned as the local assembly surface.
ASK_SHELF_RECEIPT: ASK_SH_2026_08_24_W4_PIECEWISE_AC_NO_EXACT_SUPPLIER_1_OF_9_STORES
CHEAPEST_KILLER_RUN: Check whether the exact selected Ferrers packet derivative majorant and selected_weighted_summable assemble into absolute continuity with an integrable derivative on every seam-free compact interval; failure kills Candidate A before the larger W4 theorem.
PROGRESS_DELTAS:
  - kind: BLOCKER_DECOMPOSED
    scope: ABSTRACT
    verifier: PAPER
    subject_id: W4_FIXED_K_SHIFTED_ROOT_ENERGY
    before: W4 fixed-k root-energy route not source- or API-locked
    after: One exact missing piecewise-AC derivative-integrability lemma; all other source, seam, Fourier crosswalk, and symbol-weight inputs identified
    decision_effect: BLOCKER_STRICTLY_SHRUNK
    evidence: docs/routeB_bus/H2A_4_1B_3C_1_13_W4_FIXED_K_SHIFTED_ROOT_ENERGY_PREFLIGHT_2026-08-24.md at commits 82aa3ed8 and 698e6252
NEED: Independently decide whether Candidate A is mathematically honest and non-surrogate, and if viable freeze and authorize one small Lean node W4_PIECEWISE_AC_DERIVATIVE_INTEGRABILITY_LEMMA before W4 assembly.
BLOCKS: H2A_4_1B_3C_1_13 W4_FIXED_K_SHIFTED_ROOT_ENERGY
REQUEST_BLOB: c8dd8046526f600cb5d4b4cf95aaac5119f18acef62066bbbf6e20c3218f3883
SOURCE_COMMIT: 698e62522fafcb758e737643b1ec03cc2184b0b3
```

<!-- REQUEST_PAYLOAD_UTF8_BEGIN -->
PROSHKA OPERATIVE REVIEW — W4 MINIMAL LEMMA AUTHORIZATION

Branch: rh_clean
Request ID: REQ-2026-08-24-W4-PIECEWISE-AC
Source commit: 698e62522fafcb758e737643b1ec03cc2184b0b3
Same living phase chat: 6a7afc0e-2aec-83eb-a9ca-469b44c84f83
Phase key hash: 1c0914e2e93a49defedf2c8a8497fbdc22de993b7404e0426e4b2d6c131f9aae
Blocker fingerprint: 85280424cfb0e1bd5693d79ee77d9c3fcee1fe43691b30ee5c5dbfac4be76200

Read these committed artifacts in full:

1. docs/routeB_bus/H2A_4_1B_3C_1_13_W4_FIXED_K_SHIFTED_ROOT_ENERGY_PREFLIGHT_2026-08-24.md
2. docs/routeB_bus/proshka/PROSHKA_VERDICT_REQ_2026_08_24_X_W3_ABEL_POISSON_L2_SEMANTIC_ADMISSION_2026-08-24.md
3. q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersAbelPoissonL2.lean

The read-only preflight completed the exact consumer lock, source-object lock,
finite discontinuity ledger, ordinary-Fourier/synthesized-isometry crosswalk,
and exact logarithmic arch-symbol domination. Candidate A is viable on paper:
piecewise absolute continuity plus finitely many jumps gives

  |Fourier(g_k)(t)| <= C_k / (1 + |t|)

for each fixed k, which is enough for the exact logarithmically weighted L2
consumer. No uniform-in-k bound is claimed.

One load-bearing gap remains:

  W4_PIECEWISE_AC_DERIVATIVE_INTEGRABILITY_LEMMA

On every seam-free component of the exact selected window, assemble the
kernel-green packet derivative majorant and weighted coefficient summability
into absolute continuity of the exact complex-valued packet/log-coordinate
representative with an integrable derivative. Then perform integration by
parts piecewise and retain the finite full-endpoint jump ledger.

Pinned API wall: Mathlib fourier_deriv is inapplicable because it requires
everywhere Differentiable, while g_k is discontinuous at the two zero-extension
endpoints and at finitely many production seams. The proof must be piecewise;
the global smooth theorem cannot be applied to this object.

Required audit:

1. Decide whether this minimal lemma is true for the exact production packet,
   not merely for a midpoint or continuous surrogate.
2. Freeze the exact Lean theorem packet: source object, interval quantifiers,
   absolute-continuity predicate, derivative-integrability conclusion, and the
   downstream theorem that spends it.
3. State whether the piecewise integration-by-parts theorem belongs in the
   same small node or the subsequent W4 assembly node.
4. Preserve complex-valuedness, full endpoint convention, a.e. Fourier
   crosswalk, exact selected window, and fixed-k-only scope.
5. Forbid any inference W3 L2 convergence => shifted form-domain membership.
6. Keep W5 cofinal-rate work entirely outside this transaction.

Return exactly one operative decision class:

  TRY_W4_PIECEWISE_AC_DERIVATIVE_INTEGRABILITY_LEMMA
  KILL_W4_LOG_COORDINATE_FINITE_JUMP_FOURIER_DECAY
  RUN_W4_EXACT_PACKET_DERIVATIVE_AC_KILLER

If TRY, provide all of:

  TASK_ID
  MODE
  exact Lean file path
  exact public theorem statements
  required imports and already-existing suppliers
  proof order
  mandatory plants
  validation commands
  CLOSES and OPENS
  semantic-admission scope and required provenance objects
  forbidden shortcuts
  NEXT_LOAD_BEARING_GAP

Write and commit the independent verdict to rh_clean under:

  docs/routeB_bus/proshka/
  PROSHKA_VERDICT_CODEX_REQ_2026_08_24_W4_PIECEWISE_AC_AUTHORIZATION_2026-08-24.md

Do not modify historical pushed artifacts. Do not promote Route B and do not
make an RH claim.
<!-- REQUEST_PAYLOAD_UTF8_END -->
