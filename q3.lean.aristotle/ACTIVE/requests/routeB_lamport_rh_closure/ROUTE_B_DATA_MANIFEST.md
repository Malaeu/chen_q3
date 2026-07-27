# ROUTE B DATA MANIFEST — canonical object -> type -> file -> key

Status: `CONTROL_PLANE_ARTIFACT / H2A_CERT_PILOT_REGISTERED / NOT_RH`
Purpose: kill the re-discovery tax. Every named frozen-glossary object that has
a persisted numerical carrier is listed here with its TYPE, file path, JSON
key, and sha256. Rule for all agents (Codex, Mythos, Proshka):

- TYPE_CHECK_BEFORE_FORMULA: before applying an operator, norm, or inner
  product to a named object, verify its type in THIS file. A mismatch between
  a spec and this manifest is reported as stop code `TYPE_MISMATCH_IN_SPEC`
  (spec-side defect), never silently repaired. Shadow-runs with an explicit
  substitution are allowed and must name the substitution.
- Codex appends/updates rows as the LAST step of any gate that creates or
  moves persisted data (same discipline as ROUTE_B_STATE.md).
- sha256 column is mandatory for new rows; V1 skeleton rows marked TODO_SHA
  must be filled by Codex on first touch.
- `AGENT_ANALYTIC_NOTE_PROTOCOL`: an agent analytic note exists for project
  use only when all five fields are materialized: (1) a physical repo file,
  (2) exact input/output and object types, (3) planted falsifiers with explicit
  execution states, (4) a physical V1 adjudication path and verdict, and (5) a
  sha256 registry row in this manifest.  If any field is absent, the note is
  `AGENT_ANALYTIC_NOTE_NOT_MATERIALIZED` and MUST NOT be cited as a source.

Base dir (data): `q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/out/`
Base dir (certs): `q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/`

| object (glossary) | TYPE | file | key(s) | sha256 |
|---|---|---|---|---|
| kTrial_(m,N) (= k1), locked cells | VECTOR complex, unit | out/portable_k_coeffs_lambda_sq_{m}_N_{N}.json | coefficients[{n,re,im}] | (13,90) `ca8f8b083b86da86d0c3716af6614cfc57007c33884d95352710ea2977b5671e`; (13,120) `0e5239355c54103859b22d7f753d8cd6765c2c41bcd3ec7f86b20beccc907a88`; (14,120) `f2ecc3e794728dceff933f2ced8b7e91593fc5d956a3a4d4a7522dda892bfecf` |
| kTrial diagnostic OffAxis (53,120) | VECTOR complex, unit; `DIAGNOSTIC_ONLY_NOT_CANONICAL_SOURCE`; float64 | out/off_axis_k1_coeffs_lambda_sq_53_N_120_float64.json | coefficients[{n,re,im}], convergence, primes_le_m, prime_powers_le_m | `da8b2b09b0cd50f63edb1914754efe78bfa80681054d935e4a2f4006acff17a5` |
| kTrial diagnostic OffAxis (101,120) | VECTOR complex, unit; `DIAGNOSTIC_ONLY_NOT_CANONICAL_SOURCE`; float64 | out/off_axis_k1_coeffs_lambda_sq_101_N_120_float64.json | coefficients[{n,re,im}], convergence, primes_le_m, prime_powers_le_m | `982ed566debe856764770f429924b806dba22b3322f05dd92f63235fc707f626` |
| sTrial_(m,N) | SCALAR positive (norm normalizer, D0.7b) | derived: 1/||gTrial|| | — | n/a |
| xi_k eigenvector cache | VECTOR complex (per mu); full xi1..xi3 only at (13,120) among battery cells | out/nconv_anchor_lambda_sq_13_N_120.json | xi_m_y_cache[].xi_vector | `cbc556ef7c73c9aefa9f177bb59aeca5867ed6628e3f1cca6edb270bfc13e7f0` |
| mu1, mu2, mu3 | SCALAR real; diagnostic pilot namespace | out/lambda_sq_{m}_N_{N}.json | mu1, mu3 (a1, eta1 companions) | (13,90) `467c64f92c369b5098b28df3a9d4cc75aff34ddc9433a5bc2b7d0cf6dd2a1062`; (13,120) `3c18c63faf3eff8ce0665acddb5a9f80d0e0bcd0bd8e38f60a55767a266c70c7`; (14,120) `27ce0daf64816ecfee92aaf7ec186528bc5f9cdaab8777db0942dbd9661ddda6` |
| parity even 2x2 block S0 | MATRIX complex 2x2; diagnostic Schur, not Mfin | out/parity_block_lambda_sq_{m}_N_{N}.json | even.S0 | (13,90) `883dc39f80fa191826f263730db0721e6cc83abdc17a504763e51de2fd6eaca1`; (13,120) `684d8720a13b0db18d53bb3ea26016f3b1f8ba81320d2e91ea1ee3eb4832e3aa`; (14,120) `510aad475b5a9bfb8a7aa9fecac4aa2aa7b46405e29e676f716433b43ba7e722` |
| ground_alignment_with_k1_p | SCALAR real; same diagnostic Schur files | out/parity_block_lambda_sq_{m}_N_{N}.json | ground_alignment_with_k1_p | same three hashes as preceding S0 row |
| bDet_(m,N) (= bCal) | SCALAR real (midpoint) | D0_7E_JUDGE_CERTIFICATES.json | cells[].bDet.midpoint_value | a74dc58741d6fb6faf1a56ff00747c9cbd2c85d57714108ffabec4332c437800 |
| zeta(1/2) pinned constant | SCALAR real = -1.4603545088095868... (abs used as Z) | D0_7E_CENTRAL_MELLIN_CALIBRATION.md | pinned in text | `524565589a228788039c6853e7919d6bf4f0f916e42493c6119372d637eb9b1d` |
| H3e calibration raw | TABLE csv | H3E_TRACKING_CALIBRATION_RAW.csv | rows NOT_RUN_INPUT_MISSING | 03026b8f91737426521cb8657773f461f013e7a9840baeb1379500f060c35215 |
| OffAxisGrowthProbe raw table | TABLE csv; float64 | OFF_AXIS_GROWTH_PROBE.csv | five cells, R(0.1..0.4), argmax x | `99b61c80567e0e0d8c3a5be8e52a22d35376d0a05c4b7051eb70fa0e0fb55c90` |
| OffAxisGrowthProbe machine record | RECORD json; nondecisive falsifier diagnostic | OFF_AXIS_GROWTH_PROBE.json | cells, fit, interpretation_lock, next_normalization_policy, guards | `8f64af40215bc773ec611956cc7de7bf9209e6978fc9a58dda3e3f3bcffc82dc` |
| SOFT gamma completion lock | SOURCE LOCK json; analytic unit only | SOFT_GAMMA_COMPLETION_SOURCE_LOCK.json | gamma_soft, operand_lock, DLMF/H8 pins, S2 firewall | `96b603cf40fa11ff8535dcfb1b73ca67ee84e3f350c28f4d1001a1e0584bd75b` |
| SOFT_0 paper theorem | PAPER PROOF md; conditional closure | SOFT_0_ROOF_AND_S2_TYPECHECK_2026-07-12.md | SoftSubsequenceZeroEscape, roof audit, probe recode, mint R3 | `078309f42aa547f17264b93888e1b996edd2f25f727c5984d8d58ad496f18417` |
| SOFT_0 certificate | CERTIFICATE json | SOFT_0_ROOF_AND_S2_TYPECHECK_CERTIFICATE.json | output_code, roof, gamma, probe, mint, guards | `ccf0cc8b323013253443dc1894484a4e5b7d201cbfcb72ae2a0874747c2f12fa` |
| zeta(1/4) nonzero lock | SOURCE LOCK json; no RH | SOFT_ZETA_ONE_QUARTER_SOURCE_LOCK.json | eta positivity, eta-zeta continuation, completion consequence | `954f70aa21e3de86226d2c6df36db098f50d0158ad6431dcf498c45ccda7fc0d` |
| SOFT_1 paper gate | PAPER AUDIT md; stopped at G4 | SOFT_1_ZERO_FREE_GAUGE_AND_DISTRIBUTIONAL_IDENTIFICATION_2026-07-13.md | gauge theorem, orientation, anchors, linear pairing, joint limit, firewall | `1f611065b80a0d51a90c19770903f0ae0fcaf29661006bcf214e86fc9fc1d20b` |
| SOFT_1 certificate | CERTIFICATE json | SOFT_1_ZERO_FREE_GAUGE_AND_DISTRIBUTIONAL_IDENTIFICATION_CERTIFICATE.json | G1--G7, output code, pins, scheduler guards | `0732eadd0521e90004b556fc1e8c76e6dd90d3a3164c60af1d681a49067c31b4` |
| SOFT_2 planted falsifiers | CERTIFICATE json; all judges live | SOFT_2_PLANTED_FALSIFIERS.json | A moving shell, B critical-line replacement, C grid aliasing, clean controls | `d25928106855d9ef192a35059d16c370c90b0fb2ebf72dd04597569b1db18681` |
| SOFT_2 phase probe | DIAGNOSTIC json; float64/complex128 | PHASE_STRUCTURE_PROBE.json | four cells, axial phase SD, drift fits, verdict C2_PHASE_FREE | `ac95deb55c3df420de336325cda258ee848a494d34e86562eb4be15bb054760e` |
| SOFT_2 symmetry audit | PAPER AUDIT md | SOFT_2_KTRIAL_SYMMETRY_AUDIT_2026-07-13.md | exact conjugation symmetry, absent inversion/pointwise reality | `d8a139a46e29f8d9f58941aad922de67a72c5df795363924be91c63081e7380a` |
| SOFT_2 fork certificate | CERTIFICATE json | SOFT_2_LINEARITY_CROSSWALK_FORK_CERTIFICATE.json | pins, plants, phase cells, fork decision, guards | `a5511103da852206a21327ceffe83662af4df7927426aab1659173b45a3762a8` |
| SOFT_L2 Pro verdict round 11 parity | EXTERNAL VERDICT md; verbatim clipboard materialization | SOFT_L2_PRO_VERDICT_ROUND11_PARITY_2026-07-13.md | parity gauge lock, source-continuity firewall, UREL, scale/degree audit | `0085deb371e37dd319a850c66db4c2d7ecf9702af61d0ad68879c9d77ad959a9` |
| SOFT_L2 Pro verdict round 12 | EXTERNAL VERDICT md; verbatim clipboard materialization | SOFT_L2_PRO_VERDICT_ROUND12_2026-07-13.md | V1 source-injectivity adjudication, half-shift/sharp guard, residual ground-to-canonical-A gap | `912c12bfc5f0ec3e9c513caf5864de3e5e92c47a7e53d2ac1bbcd2bd8df041d7` |
| SOFT_L2 Pro verdict round 13 | EXTERNAL VERDICT md; verbatim clipboard materialization | SOFT_L2_PRO_VERDICT_ROUND13_2026-07-13.md | H2a-cofinal absorption, same-subsequence guard, global-distributional L2.2 ruling, optional source-compactness bridge | `71f4e1276c774c5a857afea2d511f0c5e45cc31710f4689666b417f75b69b9dd` |
| Codex analytic note 001 | AGENT ANALYTIC NOTE md; protocol-complete; no plant execution | CODEX_ANALYTIC_NOTE_001_2026-07-13.md | typed O2 crosswalk, exact centering unitary, plants and states, Round-12 V1 adjudication | `ec5cd0b56b34dd3b3658fd5a971a221f92d93d82d931e5ec29f89009eb70aaa6` |
| SOFT_L2 RigidityFreeze theorem/report | PAPER THEOREM + GOAL REPORT md; main core Lean-checked; reconstruction analytic proof/type freeze | SOFT_L2_RIGIDITY_FREEZE_THEOREM_2026-07-13.md, SOFT_L2_RIGIDITY_FREEZE_REPORT_2026-07-13.md | source injectivity, global-root contract, O2 intertwiner, provenance verdict | theorem `7998c3f4a3fe1a214d66d555cd7a416ab7c62ac3ed86bc3ef43a5c4f2ce7e6fb`; report `2c43084ad2e7733839a3a3afda50c984e0e6b52d39c3232dd81db061a817c749` |
| SOFT_L2 RigidityFreeze plants | EXECUTABLE FALSIFIER RECORD json + Python replay/validator | SOFT_L2_RIGIDITY_FREEZE_PLANTS.json, soft_l2_rigidity_freeze_plants.py, validate_soft_l2_rigidity_freeze.py | PL1--PL4 plus Proshka P5 refusal; ALL_PLANTS_LIVE | json `97538967ebed6375a3c47e743db7e7413eb76fb2dbef0edd191e8df01e2cee46`; replay `21dd317f3055ef8924556c1983ba2998a72b9e7074705b2ce0788a25806f846a`; validator `050f17c2c8372ea42822f4725b01981934b6ef2f1e61307df93b0443f36bcd71` |
| SOFT_L2 RigidityFreeze Lean | LEAN SOURCE; main theorem proved, reconstruction contract typed; zero holes | ../../../../Q3/Proofs/RouteB/EvenRealAutocorrelationRigidity.lean, ../../../../Q3/Proofs/RouteB/AutocorrelationSquareRootReconstruction.lean | difference-of-squares rigidity, positive anchor, certified reconstruction input/output types | rigidity `af3881dd0be7df726b9bc19975f833d410aeddb2b9740e7d9c0dffd72b67b077`; root type `c1e55f9fc0e1a0a0003b8e0cc6f6026fb7f2f85504227bb3190bfe3614e4db10` |
| SOFT_L2 lag ledger (12,120) | TABLE csv + RECORD json; high-precision `portable_k1/mu1` diagnostic proxy, not persisted full ground | SOFT_L2_LAG_LEDGER_12_120.csv, SOFT_L2_LAG_LEDGER_12_120.json | 13 lag rows; LHS, muA, residual, window `D_(a,L)`, aggregate remainder, outer cancellation judge | csv `2738ecfd4f101a6f9250ba57de56b1b5b7142511983beb0d47269478a3627c4c`; json `66ca8eb9cb8b8489dbc084d1889a6d599e8e6864ea4fe7d24e3e984a4a434c0e` |
| SOFT_L2 lag ledger (14,120) | TABLE csv + RECORD json; high-precision `portable_k1/mu1` diagnostic proxy, not persisted full ground | SOFT_L2_LAG_LEDGER_14_120.csv, SOFT_L2_LAG_LEDGER_14_120.json | 13 lag rows; LHS, muA, residual, window `D_(a,L)`, aggregate remainder, outer cancellation judge | csv `02c259a528fff60e18859ff8044822b6fd544b05acd18eac6129a427d2c63bb6`; json `acd652b8bbd58a5d63a610484937e46d29161ba6a6781d30a8ded7951dcde820` |
| SOFT_L2 GroundSignProbe | TABLE csv + RECORD json + REPORT md; 4096-point all-carrier diagnostic, six trial/diagnostic rows plus one persisted finite ground row | SOFT_L2_GROUND_SIGN_PROBE.csv, SOFT_L2_GROUND_SIGN_PROBE.json, SOFT_L2_GROUND_SIGN_PROBE_REPORT_2026-07-13.md | interior depth `0.05L`; opposite-extremum ratio threshold `1e-6`; all seven `SIGN_CONSTANT`; trial/ground guard | csv `37139b7cbd0102a843fdfbe9ab1785c2de5d6481ddb85f525f1e149a350f8156`; json `3223d8e6548cd4b9f96b5bafe5a39b41f807c2e9397142641a54ef39bb98b55c`; report `0c728e0e1c4687fc07c87a98b10a4026987f84adf5e05b6b24ae242dcf3bc3e2` |
| SOFT_L2 AutocorrelationTailCheck (13,120) | TABLE csv + RECORD json + LOG-PLOT png + REPORT md; persisted finite ground diagnostic | SOFT_L2_AUTOCORRELATION_TAIL_CHECK_13_120.csv, SOFT_L2_AUTOCORRELATION_TAIL_CHECK_13_120.json, SOFT_L2_AUTOCORRELATION_TAIL_CHECK_13_120_LOG.png, SOFT_L2_AUTOCORRELATION_TAIL_CHECK_REPORT_2026-07-13.md | `TAIL_DOMINATED`; Round-13 role `OPTIONAL_SOURCE_COMPACTNESS_SPATIAL_TIGHTNESS_DIAGNOSTIC`; not L2.2 input; `FALSE_WALL_REMOVED_ROUND13` | csv `419f0c737ee92092a0a6e200e8ae103860ff2531193f1621d4918ea257ae6ca4`; json `3a6c0d7548574d247d0776e3d1b9dba41cf2dc573fdb402db393b35b13872f0e`; png `bf2dab9619c69e9a0c3f718cbcc7a94dffc97123373a06380ca51e6f04d9ce0d`; report `71a02e60249aed522b9d1fbf41168accf8457e55a598d669b7c6941d82f7902d` |
| SOFT_L2 Round-13 measurement replay | PYTHON replay + fail-closed validator | soft_l2_round13_measurements.py, validate_soft_l2_round13_measurements.py | deterministic sign/tail records; Round-13 tail role firewall; `SOFT_L2_ROUND13_MEASUREMENTS_VALIDATED` | replay `fabb63a98ead9c6e5fc5823b226898b4f769629d3afe79187430150fb6f51511`; validator `9c516cf8c390fd4aa451979ba413384ff68e59b313577072d1d1e0ad32750a0a` |
| SOFT_L2 Round13Integration contract | PAPER/TYPE CONTRACT md + CERTIFICATE json + fail-closed validator; L2.2 remains OPEN | SOFT_L2_ROUND13_INTEGRATION_2026-07-14.md, SOFT_L2_ROUND13_INTEGRATION_CERTIFICATE.json, validate_soft_l2_round13_integration.py, SOFT_1_GATE_CONTRACT.md | same-cofinal guard, H2a derived corollary, five-input `GlobalPositiveDefiniteUniqueness`, optional source leaf, false-wall removal | contract `cf0b1966c434d56706b750c2246abad7a8606f8ff9286d7db2957ff2af8128cc`; certificate `866a4a7dd5148e88f911dac1ce01f7fd3748c9fa9b53deb8fda35eb83db4797e`; validator `605fd6810ae9594643a9e83664db9a800801bf9abbcf3912fab073f70bcbf634`; SOFT_1 overlay `8598b335f3b2b570a4e2a9a1ab70cecb3ddeda9eb83ae9d365713ab3a073f615` |
| SOFT_L2 Round13Integration Lean | LEAN SOURCE; phase corollary proved, quantifier/L2.2/optional-leaf types frozen; zero holes | ../../../Q3/Proofs/RouteB/SoftL2Round13Integration.lean | `SoftSameCofinalSubsequence`, `simpleGround_canonicalPhaseIndependentAutocorrelation`, `GlobalPositiveDefiniteUniqueness`, `SourceCompactnessToFullAutocorrelation` | `10bb78e28abc8309b2aad50ed87046cb6b4d80405e1c8c8a37eca5fc749aa43b` |
| SOFT_L2 optional source-compactness plants | EXECUTABLE VALIDATOR RECORD json + Python replay; all three live | SOFT_L2_ROUND13_SOURCE_COMPACTNESS_PLANTS.json, soft_l2_round13_source_compactness_plants.py | shift, `a^(1/2)q(a u)`, `A0 cos(beta t)`; `SOFT_L2_SOURCE_COMPACTNESS_PLANTS_ALL_LIVE`; not L2.2 evidence | json `68dc06ec468d26b71c3b3f83d922fbf75695f02ee02d8d0025bbcbbd37fbfedd`; replay `32ad00d46090629180233620ee8550c4a3791ae8d8260abd8e80d890a38d9b51` |
| H2a `cert.pilot` split | BINARY64 DIAGNOSTIC RECORD json + REPORT md + Python replay/validator; not an exact certificate | H2A_CERT_SPLIT_PILOT.json, H2A_CERT_SPLIT_PILOT_REPORT_2026-07-25.md, h2a_cert_split_pilot.py, validate_h2a_cert_split_pilot.py | nine registered cells; `beta=(lambda1+lambda2)/2`; `tau=lambda2-lambda1`; certificate minimum eigenvalue; `PSD_ACHIEVABLE_ON_REGISTERED_SMALL_GRID`; exact leaf `ExactSectorOrdering` remains open | json `a6e33d6f21301d123d979909c240a7f04ed2cdcfe1f445f198461039aca68731`; report `942d981c18e53c89c3312fc04312a97f60d5ac62d1b12ea161bb69a1a64193e7`; replay `b7f4c30dc843bdb51b06e3637c1ce87c05812b5904325fe26a48be06425cf2f0`; validator `cdc295dfee20f42f94532dfacf3a711fece9e3eb047f08c8b3ee1aef001a2852` |
| B0 value probe | BINARY64 DIAGNOSTIC TABLE + RECORD + REPORT; no uniform lower-bound theorem | B0_VALUE_PROBE.csv, B0_VALUE_PROBE.json, B0_VALUE_PROBE.md, b0_value_probe.py | eight cells through `(257,120)`; `|B(0)|=sqrt(log m)|c0|`; log-log fit; `SAMPLED_INF_GT_DELTA_NO_COMPENSATION_DIAGNOSTIC`; `FIT_NOT_LAW` | csv `723a9d8f7fb93a4c8b8e31df1487b17d7cc7f5df15c59f153f9692bf556a9ba3`; json `c720bf2e8010be12662296a638bb0c8cdf53ac21072f337fac0d749f2cc4c7e4`; report `652d7d5451a31f5d497cfa80afb6692faa1e5829d935374c51f85052f606765c`; replay `f1ac0675d90dee786bf11880e712382bdd8f64a66469286c8beff9df4fa2deba` |
| centeredXi zero anchor contract queue | STATEMENTS-ONLY NOTE; not active | CENTERED_XI_ZERO_NONZERO_CONTRACT_NOTE_2026-07-26.md | eta pairing; DLMF 25.2.3; `riemannXi_eq_zero_iff_riemannZeta_eq_zero`; stop `ZETA_HALF_ETA_CONTINUATION_BRIDGE_MISSING` | `2b3e0bcb37059297c63c99d8a1be9699a6b289546a53143e0545b29fdf90b374` |
| gamma_soft Lean proof | LEAN SOURCE; zero holes | ../../../../Q3/Proofs/RouteB/GammaSoftZeroFree.lean | gammaC_centered_ne_zero, gammaSoft_ne_zero | `615548873f1c12dfd5f5e047c74135cd1f0fc454614c3fdc9d685472f3934c4b` |
| D0.7e.5a mint menu R3 | OWNER DRAFT HISTORY; menu falsified | D0_7E_5A_OWNER_MINT_DRAFT_WPRIME_CONSUMER.md | MINT_MENU_FALSIFIED, A exact-equality miss, B SLOT_VACUITY | `1ef06c3050bfd7042af97bb7fd07f5c5c987da9bbbc21f32fee1a36e22722980` |
| persisted cells set | INDEX | this file | locked: (13,90),(13,120),(14,120); diagnostic float64: (53,120),(101,120); (17,120) vector MISSING | n/a |

Known gaps (as of 2026-07-12): (17,120) coefficient vector not persisted
(T1 stop `T1_LAMBDA17_PERSISTED_COEFFICIENT_VECTOR_MISSING`); canonical
WPrime/delta_dict tables absent (T2 stop). New cells (53,120),(101,120) are
registered only as float64 diagnostics: no canonical promotion, asymptotic
claim, or `N(lambda)` selector follows.

EXTERNAL VERDICT MATERIALIZATION RULE: any goal referencing a Pro/Proshka/
Mythos verdict MUST cite a repo file path; external verdicts are written to
disk BEFORE the goal is issued (naming: `<GATE>_PRO_VERDICT_<CHANNEL>_<DATE>.md`).
Browser/chat transcripts are NOT a valid source for gate execution. Entries:
SOFT_0_PRO_VERDICT_PROSHKA_2026-07-12.md (V1, authority for SOFT_0);
SOFT_1_PRO_VERDICT_PROSHKA_GAUGE_2026-07-12.md (V1, round 2, SOFT_1);
SOFT_2Q_PRO_VERDICT_PROSHKA_QUADRATIC_2026-07-13.md (V1, round 4, quadratic
  divisor roof + Codex directive; authority for QuadraticDivisorTransfer);
SOFT_3_PRO_VERDICT_PROSHKA_TAILS_2026-07-13.md (V1, round 3, tails/target);
SOFT_3Q1_PRO_VERDICT_PROSHKA_KERNEL_2026-07-13.md (V1, round 5, kernel
  pairing + SharpLock; authority for SOFT_3Q1 gate);
SOFT_L2_PRO_VERDICT_ROUND9_2026-07-13.md, SOFT_L2_PRO_VERDICT_ROUND10_2026-07-13.md,
SOFT_L2_PRO_VERDICT_ROUND11_PARITY_2026-07-13.md,
SOFT_L2_PRO_VERDICT_ROUND12_2026-07-13.md,
SOFT_L2_PRO_VERDICT_ROUND13_2026-07-13.md
  (V1, authority for SOFT_L2 exact projection ledger, parity/edge-profile,
  projection-defect scale/degree continuation, and source-injectivity
  adjudication, H2a-cofinal absorption, same-subsequence guard, and the
  global-distributional L2.2/source-compactness split);
CODEX_ANALYTIC_NOTE_001_2026-07-13.md
  (Codex O2 crosswalk; protocol-complete analytic note, plants not run);
D0_7E_5A_PRO_VERDICT.md (V2).
PENDING MATERIALIZATION (owner-chat only, to be written next session; goals
MUST NOT cite them until on disk): V1 round 6 (minimal D'(I) topology,
translation/polynomial counterexamples, theorems A/B/C); V1 round 7
(translated-bump kill of the variational branch, lag-tail closure V1–V3);
V1 round 8 (rotten planks: moments vs values, log-rational lags, c>0 lemmas).

NOT_RH.
