# Exact residual/gap ground-to-trial control cell

Date: 2026-08-12

Scope: `[FINITE_CELL][CONDITIONAL]` · Goal 058 / G3 M1B

Outcome: `M1_EXACT_RESIDUAL_GAP_CONTROL_CELL_CLASSIFIED`

## Decision

The precommitted classification is **WEAK**.  The valid bound is the isolation-gap Rayleigh bound; its square root is `[0.00797476164420490927498209596664853634377391624722367045010358504309880493368052216350508013 +/- 1.94e-93]`.  The residual bound is valid but numerically useless because the literal persisted trial carries a tiny nonzero parity defect.

No parity symmetrization was applied after inspecting the spectrum.  Doing so would change the M1 source object and violate C09.

## Source lock and preflight

Knowledge query: `./ask.sh "M1SourceResidualGapControlCell persisted source matvec ccmWeilMatFinite 13 120 residual spectral gap parity"` → `HITS_EXISTING_M1_AND_SOURCE_OBJECTS_NO_EXTERNAL_SEARCH`.

The matrix is rebuilt from the literal source decomposition `ccmWeilMatFinite 13 120 = W02 - WR - Prime` in mode order `-120,…,120`.  The ground packet is not read by either matvec implementation.

| object | SHA-256 |
|---|---|
| `trial` | `0e5239355c54103859b22d7f753d8cd6765c2c41bcd3ec7f86b20beccc907a88` |
| `ground` | `cbc556ef7c73c9aefa9f177bb59aeca5867ed6628e3f1cca6edb270bfc13e7f0` |
| `block_cache` | `17bf89f62dd5c512f0e75a283809f09ad703edd6dd54d127e9f371e0f4231928` |
| `pilot` | `b1b609da86456425200190c17bf2be7573f27f2135c4cc061915b9067b9868c5` |
| `lean_n1` | `f2f9d248a6f2ad703428c624ccbaf5a75b340655e4b4ebbbe3f1d77355523815` |
| `lean_finite` | `282dc31c9bc558aefe8ab0b105fe844da017defdaaec4c2048d147327b72df89` |
| `directive` | `48d10524b400ea0aa1e0050dd5fa3b3fd03fed451045f21207516c4da5b96aeb` |

## Load-bearing oddity

Literal persisted parity check: `Jq=q` is `False` with `||q-Jq|| = [3.43840115087025170462657398990859657541220366321383900375812185202997328227584167805553698e-30 +/- 4.81e-120]`.  `JK=KJ` is source-exact, but both checks are required for the even-only denominator.  Therefore the audit uses `Delta_iso`, not `Delta_even`.

A float64 eigensolve was rejected before this report: it returned spurious eigenvalues of order `-10^-15` where the outward-rounded source calculation brackets positive levels of order `10^-59`, `10^-55`, and `10^-51`.

## Certified spectrum and theorem-facing scalars

The eigenvalue brackets use outward-rounded python-flint Arb entries.  At each endpoint Arb validates regularity of the complete shifted ball matrix; a symmetric diagonally-pivoted midpoint LDL then supplies the invariant inertia count.  Cached eigenvalues are seeds only; the count transition certifies the index.

- `epsilon0_even = [3.5e-59 +/- 5.09e-61]`
- `epsilon1_even = [1.3e-51 +/- 2.50e-53]`
- `epsilon0_odd = [3.1e-55 +/- 7.47e-57]`
- `a = [5.37295373544202335868687414196622456333894394054268905623759843902656270338945779951086700e-59 +/- 9.21e-150]`
- `nu = [4.85150217458604220384062964353518022864918520189678824469827823598149352882019648607486227e-30 +/- 4.58e-120]`
- `Delta_even = [1.3e-51 +/- 2.50e-53]`
- `Delta_odd = [3.1e-55 +/- 7.50e-57]`
- `Delta_iso = [3.1e-55 +/- 7.50e-57]`
- `alpha = [1.9e-59 +/- 4.59e-61]`
- `separation_iso = [3.1e-55 +/- 7.52e-57]`

## Two bounds

- Rayleigh: `U_rayleigh = [6.35968232818817879892961232140853899461495230704934753959454894263209208193087163944226075e-5 +/- 4.29e-95]`; `sqrt(U_rayleigh) = [0.00797476164420490927498209596664853634377391624722367045010358504309880493368052216350508013 +/- 1.94e-93]`; bound/observed-defect ratio `[13554.6494621529743823096410994813016703649101551956528944517572482091895162668038749878164 +/- 3.45e-86]`.
- Residual: `U_residual = [257249334315281811109699241297495061983881605775900.101802393477138466261539926557324424787 +/- 3.79e-40]`; `sqrt(U_residual) = [16038994180287048508350317.4028631301537177280344733675874643053134400645715607697021095426 +/- 2.71e-65]`.  It is mathematically valid with the isolation separation and numerically unusable.

The existing M1 identity `sqrt(projective_defect)=distance` was replayed: `True`.

## Independent matvecs and precision

A direct dense mpmath matvec was run at three decimal precisions.  An independent outward-rounded Arb implementation accumulated `W02q`, `WRq`, and `Primeq` without using the dense product.  The mpmath path contains one numerical scalar quadrature, so cross-backend agreement uses the declared absolute tolerance; the Arb dense/component identity itself is enclosure-exact.

Agreement: `{'max_absolute_coordinate_difference': '1.319818276748367010434601137926727365980144525074106269669767505478590552620844429143954370886049393e-131', 'worst_mode': -1, 'tolerance': '1.0e-90', 'pass': True}`; Arb dense/component: `True`.

## Plants

- `posthoc_q` → `M1_SOURCE_TRIAL_PRECOMMIT_VIOLATION` (`PASS`).
- `mode_order` → `M1_SOURCE_MFIN_MODE_ORDER_MISMATCH` (`PASS`).
- `parity_denominator` → `M1_TRACKING_GAP_PARITY_UNJUSTIFIED` (`PASS`).
- `interval_direction` → `M1_RESIDUAL_GAP_ENVELOPE_DIRECTION_ERROR` (`PASS`).
- `ground_oracle` → `M1_MATVEC_GROUND_ORACLE_SURROGATE` (`PASS`).

## Registered prediction fate

- `P058_M1R_1`: `REFUTED_FOR_LITERAL_PERSISTED_Q: selected certified distance bound exceeds 1e-3`.
- `P058_M1R_2`: `REFUTED_AT_LITERAL_DECIMAL_OBJECT: Jq=q is false; JK=KJ passes`.
- `P058_M1R_3`: `CONFIRMED: dense and independent source-component matvecs agree inside Arb balls`.
- `P058_M1R_4`: `CONFIRMED_BY_WEAK_CLASSIFICATION: a later Feshbach proposal is selected, not executed`.

## Evidence boundary

This is one finite-cell, conditional numerical certificate.  It does not close G1 or G3, does not establish a cofinal family, does not promote Route B, and makes no RH claim.  A WEAK result selects a later Schur/Feshbach representation proposal; this transaction does not authorize that next run.

`ARSENAL_USED: C04 · C07 · C09 · C10`

`M1_EXACT_RESIDUAL_GAP_CONTROL_CELL_CLASSIFIED`
