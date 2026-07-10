# Route B TwoLevelSpectralLadder Proshka Route Review

Status: route review only. Not a proof of RH. Not a Route B kill.

## Sent to Proshka

Codex reported the local `N_LIMIT_NOT_STABLE` audit:

- Phase 1 was run for `lambda_sq=12,13,14` and `N=60,90,120`.
- C1-C4 calibration passed.
- Phase 2 was not run.
- Slopes were not refit.
- Mathematical definitions and QW formulas were not changed.
- Local primary diagnosis was `NUMERICAL_FLOOR_IN_NU`.
- Secondary visible issue was `BASIS_TRUNCATION_NOT_STABLE` for
  `mu1`, `mu2`, `Delta`, `eta1`, `LB_3D`, and `W_actual`.

Codex asked whether the next gate should be:

- A: repair `nu` by computing the tail eigenvalue on an explicit high-precision
  complement basis for `M^perp`;
- B: audit packet/prolate/E-map precision first;
- C: add a larger-N Phase 1 spot after A/B is decided.

## Proshka Verdict

Proshka selected A first:

```text
Next gate: A.

Record:
FAILURE_CODE = N_LIMIT_NOT_STABLE
PRIMARY_DIAGNOSIS = NUMERICAL_FLOOR_IN_NU
SECONDARY_DIAGNOSIS = BASIS_TRUNCATION_NOT_STABLE_PENDING_PACKET_PRECISION

Route B status:
NOT KILLED.
Instrument tail test invalid until high-precision complement-basis nu is recomputed.
```

## Required A-Only Repair

Patch only the `nu` computation:

- remove the full singular projection eigensolve as the authoritative tail test;
- build an explicit high-precision orthonormal basis `U_perp` for `M^perp`;
- compute `T_tail = U_perp^* T U_perp`;
- set `nu` to the smallest eigenvalue of `T_tail`;
- validate only `lambda_sq=14,N=120` at current `dps` and `dps+80`;
- do not run Phase 2;
- do not rerun the full ladder;
- do not change QW formulas or packet definitions.

Required output:

- `ACTIVE/requests/routeB_twolevel_spectral_ladder/nu_complement_audit.md`

Allowed A-only verdicts:

- `NU_FLOOR_FIXED_TAIL_PASS`
- `NU_FLOOR_FIXED_TAIL_FAIL`
- `NU_PRECISION_UNSTABLE`
- `COMPLEMENT_BASIS_CONDITIONING_FAIL`

## Follow-Up After A-Only Diagnostic

Codex reported the completed A-only diagnostic:

```text
VERDICT = NU_FLOOR_FIXED_TAIL_FAIL

old full-projection float64 nu:
  dps197: -4.0049875337510944e-15
  dps277: -4.535840335640321e-15

repaired restricted complement nu:
  dps197: 3.296093549548185e-53
  dps277: 3.296093549548170e-53

lambda3_G:
  dps197: 1.1552588608928484e-27
  dps277: 1.1552642872984288e-27

tail_margin:
  dps197: -1.1552588608928484e-27
  dps277: -1.1552642872984288e-27
```

Proshka confirmed the next gate:

```text
STATUS: YES - next gate is rogue tail eigenvector audit

FAILURE_CODE = N_LIMIT_NOT_STABLE
PRIMARY_DIAGNOSIS = NU_FLOOR_FIXED_TAIL_FAIL
SECONDARY_DIAGNOSIS = BASIS_TRUNCATION_NOT_STABLE_PENDING_PACKET_PRECISION
NEXT_GATE = RogueTailEigenvectorAudit
```

Interpretation:

- the old `-1e-15` floor was an instrument bug;
- after repair, the current 3-vector prolate packet still fails the tail-gap
  test in this pilot;
- this does not globally kill Route B;
- it may kill only the current 3D ladder packet model, depending on the rogue
  vector audit.

Required next output:

- `ACTIVE/requests/routeB_twolevel_spectral_ladder/rogue_tail_audit.md`
- `ACTIVE/requests/routeB_twolevel_spectral_ladder/out/rogue_tail_*.json`

Allowed rogue-audit verdicts:

- `ROGUE_NUMERICAL_ARTIFACT`
- `ROGUE_BASIS_TRUNCATION_ARTIFACT`
- `ROGUE_BOUNDARY_ADMISSIBILITY_LEAK`
- `ROGUE_IS_MISSING_PROLATE_MODE`
- `ROGUE_STATE_BELOW_LADDER_CONFIRMED`
- `MISSING_PROLATE_COMPARISON_BASIS`
- `ROGUE_AUDIT_BLOCKED`

## Follow-Up After RogueTailLevelPlacementAudit

Codex reported the completed level-placement audit:

```text
VERDICT = ROGUE_BELOW_SECOND_LEVEL_CONFIRMED

lambda_sq=14, N=120, base dps=197:
lambda1_G = 3.9285077482964378234005407361846759791247416851200922263791098777128270823251073e-28
lambda2_G = 7.5110032640263442408588918481367677993404755977336349973856903773509738386175771e-28
lambda3_G = 1.1552588608928484370318667777805945411432515263325018627033866381285154081209062e-27
nu_tail  = 3.2960935495481850719138529050771074433659529435430161949242288195308989982566486e-53

actual mu1 = 1.4598129516305608574358609264922179071797113743878582206556358479950433608366779e-64
actual mu2 = 1.6680022583588869596654056727736096522590303309993518433644085253282379668077549e-60
actual mu3 = 9.3843336472943064927066176234582865627823597812140712761977363506071252695875636e-57

nu_tail < lambda2_G
nu_tail > actual mu2
actual order: mu1 < mu2 < mu3 < nu_tail << lambda1_G < lambda2_G < lambda3_G
```

Codex asked whether the next gate should be boundary/admissibility plus missing
prolate-branch comparison, or whether the observed actual full-matrix low levels
should be audited first.

Proshka selected the full low-eigenvector audit first:

```text
Do not continue tail-only rogue comparison first.
The chosen prolate packet does not hit the first spectral levels at all.
The next audit should be a block ledger for actual low eigenvectors.
```

Required next gate:

```text
NEXT_GATE = FullLowEigenvectorBlockLedgerAudit
```

Required next output:

- `ACTIVE/requests/routeB_twolevel_spectral_ladder/full_low_eigenvector_audit.md`
- `ACTIVE/requests/routeB_twolevel_spectral_ladder/out/full_low_eig_*.json`

Audit targets:

- actual full-matrix eigenvectors `xi1`, `xi2`, `xi3` for `lambda_sq=14,N=120`;
- eigenvalues, residuals, norms, parity, packet projections, overlaps with
  `k1`, `k2_odd`, `k2_even`, rogue-tail overlap, block energy ledger,
  Schur/Feshbach cross-term signal, Fourier localization, admissibility if a
  boundary map exists, and missing prolate branch comparison if available;
- do not run Phase 2;
- do not rerun the full ladder;
- do not change formulas;
- do not change packet definitions;
- do not claim Route B killed.

Allowed full-low-eigenvector verdicts:

- `FULL_LOW_EIGENVECTORS_NUMERICAL_ARTIFACT`
- `FULL_LOW_EIGENVECTORS_BOUNDARY_LEAK`
- `FULL_LOW_EIGENVECTORS_PACKET_HYBRIDIZATION`
- `FULL_LOW_EIGENVECTORS_MISSING_PROLATE_BRANCH`
- `FULL_LOW_EIGENVECTORS_VALID_BELOW_PACKET`
- `BOUNDARY_OPERATOR_MISSING`
- `MISSING_PROLATE_COMPARISON_BASIS`
- `FULL_LOW_EIGENVECTOR_AUDIT_BLOCKED`
