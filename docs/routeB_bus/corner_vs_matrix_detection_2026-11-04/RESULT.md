# Corner versus matrix detection; two-core addendum

DIAGNOSTIC_NEVER_A_PROOF. Route B = CHALLENGER / NOT_RH. No RH claim, proof admission, D0 change, or route-state change.

The full even matrix detects every added off-line quartet before its constant-mode corner does on this finite experiment. Weakening the primes to u=0.9 makes the pole-null detector negative even WITHOUT an added quartet. Thus that weakened detector is not specific to off-line zeros. DH also triggers the raw matrix detector while its corner remains positive through m=3000.

## Main thresholds

The raw matrix threshold is lambda_min < -1e-6; the corner threshold is strictly below zero. `>3000` is a censored corner threshold, not a measured crossing. Matrix entries/eigenvectors use the physical orthonormal cosine basis, j=0..m, dimension m+1.

|a|gamma|first admitted m|first matrix m|first corner m|peak mode|peak frequency|within one bin of gamma|
|---|---:|---:|---:|---:|---:|---:|---|
|1/20|14|16|16|>3000|5|11.330900|no|
|1/20|50|21|31|>3000|25|45.742638|no|
|1/20|200|139|162|>3000|157|193.895118|no|
|1/20|800|762|862|>3000|854|793.850807|no|
|1/10|14|16|16|>3000|7|15.863260|yes|
|1/10|50|21|29|>3000|24|44.782655|no|
|1/10|200|139|162|>3000|161|198.835121|yes|
|1/10|800|762|861|>3000|854|793.987158|no|
|1/3|14|16|16|208|7|15.863260|yes|
|1/3|50|21|23|>3000|23|46.089469|no|
|1/3|200|139|157|>3000|153|190.126704|no|
|1/3|800|762|857|>3000|851|791.743518|no|

Admissibility is strict T_m > gamma, with T_m=(1+(1+log L)/(4L))*2pi*m/L and L=log m, exactly as fixed before execution. The carrier frequency Omega=2pi*m/L is recorded separately. No replacement of T by Omega was made. See [thresholds.csv](thresholds.csv) for values, delays, bins and above-band flags; per-cell files include centroids and the ten largest mode energies.

D1 (P=.80): supported in all12 cases, with11 censored corners. D2 (P=.60): universal conditional flatness fails; only4/12 admission-adjusted delays meet the preregistered bound max(2,.05*m_admit). Corner growth with gamma cannot be fully ordered because11 thresholds are censored. D3 (P=.75): only3/12 peaks meet the original one-bin tolerance; the universal prediction fails. No tolerance was changed after seeing the vectors.

All integers from each admission through each first detection were evaluated for the relevant case: no missing predecessors. A separate fresh assembly/eigensolve rechecks all9 later-than-admission predecessors in [predecessor_recheck.json](predecessor_recheck.json). Every predecessor remains above -1e-6. Fresh fixed-vector Rayleigh evaluations using the unchanged pinned source at296 working bits (about89 decimal digits) confirm all12 negative detections. These are high-precision negative witnesses, not complete high-precision eigenvalue orderings or interval certificates. The first-threshold claims are finite float64 eigensolver observations with these independent sign checks.

## B+1: generalized core constants

Let W=I+X and S=W^(-1/2). The physical constraint z perpendicular to p becomes y perpendicular to S p after y=W^(1/2)z. We restrict S B S to (S p)-perp. For the planted A+Q, H and p stay fixed, so B_eff=B-Q. The original-prime B itself is unchanged; its C* equals the unplanted zeta value. DH has its own conductor5 odd gamma and signed full Dirichlet coefficients, and p_D=0; its restriction is the full carrier.

|quantity|m=512|m=3000|raw log-log tail slope|
|---|---:|---:|---:|
|DH C*|0.15357153|0.10834576|-0.0717661|
|plant a=1/3, gamma14 C*_eff|0.0438264|0.0978121|0.4633817|
|plant a=1/3, gamma50 C*_eff|0.00540259|0.00700511|0.0882055|

The maximum original-zeta C* on the25 tested m is0.005633406, well below16. K1 (P=.97) is not falsified on this grid; this does not assert every integer or a cofinal bound. K2 (P=.70) passes its preregistered raw-power test for gamma14, but fails for gamma50: slopes0.46338 and0.08821 respectively. Ratios C*(3000)/C*(512) are2.23181 and1.29662. The fitted points are the actual nine tested m>=512; no baseline subtraction was used.

K4 (P=.60) fails its finite-budget growth test for DH: the endpoint ratio is0.705507, below the required2, and the tail slope is negative rather than at least0.1. No DH C*>16 is observed. Thus raw DH matrix negativity here does not require growth of this Sobolev-normalized core constant. Complete constants, residuals and constraints are in [CSTAR_SUMMARY.csv](CSTAR_SUMMARY.csv) and [core/core_results.json](core/core_results.json).

## B+2: weakened primes, u=9/10

Every weak corner stays positive on all eligible integers16..3000, for unplanted zeta and all six plants at gamma14/50. Every pole-null Sobolev detector fires at its first admitted m:

|case|first admitted/core m|corner|
|---|---:|---:|
|unplanted|16|>3000|
|all three a, gamma14|16|>3000|
|all three a, gamma50|21|>3000|

The physical pole-null minimum without a plant at m16 is -0.0105744622229521. The separately reported literal normalized-coordinate p-perp convention gives -0.0117075441698190; that second convention is not physical pole-null. Both conventions trigger at admission in every case. All14 saved witnesses were reevaluated at296 working bits, including independently integrated physical shifted-cosine prime forms and projection onto the exact MP constraint. See [weak_thresholds.csv](weak_thresholds.csv), [weak_confirmation_summary.json](weak_confirmation_summary.json).

K3 (P=.85) is supported as a finite conjunction of corner silence and core firing. Since the unplanted changed form already fires, this conjunction is not a specific discriminator of an off-line quartet. Original-zeta positivity controls concern u=1, not u=.9.

## B+3: DH

The DH raw matrix first crosses the specified -1e-6 threshold at m55: float minimum -0.6639206460810501; fresh MP Rayleigh witness -0.6639206460810497916771954863. Its peak is mode54, frequency84.6677805175. The immediately preceding m54 has a small negative float minimum -3.5530711e-11, which does not reach the detector threshold. Every integer16..55 was checked. An earlier historical report of a tiny negative sign is not the same threshold as this experiment. DH corner is positive through3000. Later raw DH checkpoints and core constants are retained, with no zeta pole inserted.

## Gates, precision and actual coverage

Both quartet constructions pass at m80: all12 positive-a cases and4 a=0 controls, worst physical-kernel quadrature discrepancy2.0028e-14 <1e-12. The unchanged original source is pinned by Git blob27bbaabbc5938b3157b5bc20f5e6db2f882122c0 and SHA2564e26ed90c8ef7305699802c02490bb0cea0da26be49891c98d387b5210eb8f63. All three selected verdicts, full commit pins and hashes are transported in inputs/ and SOURCE_INPUTS.json.

The scale builder was compared against fresh pinned256-bit matrices at m80,160,300 (zeta), and both worlds at80,160 for component assembly; max final component discrepancy3.11e-15 and main zeta matrix discrepancy4.45e-15. Every coefficient through3000 was independently compared at high precision. All prime powers, DH non-prime-power coefficients, gamma terms, endpoint corrections, analytic tails and source-native poles are retained.

An initial pure-float prime reduction violated the requested -1e-12 control at large m. Its failed evidence is preserved in builder/. Promoting intermediate prime phases/reductions to longdouble resolved that failure without clipping eigenvalues or changing the form. Final original-zeta controls pass on all147 actual matrix-grid m: worst unplanted minimum -1.40721e-14; all528 admitted a=0 matrix controls are nontriggering (minimum -2.37893e-14). All a=0 scalar corners are nonnegative. These tiny negative matrix numbers remain unresolved float noise.

Coverage is deliberately explicit: main and B+ scalar corners cover every eligible integer through3000; matrix calculations use consecutive prefixes until detection plus checkpoints through3000, not all integers through3000; C* uses the25-point declared grid augmented by observed thresholds/admission. The dense m16 generalized normalization gate agrees within2.78e-17. Larger core Ritz computations retain solver residuals, maximum4.86e-14 and normalized constraint residual6.05e-16. No interval or cofinal assertion follows.

The original preregistration was committed before runs at bc9204929faccc66f952ff9df9273e0b94afed4e; the append-only B+ preregistration at44e89c1277dde897816b35c637fa7c926ed5d2c6. The historical pre-addendum bytes remain in producer_history/. Intermediate producer summaries saying MP confirmation is pending are historical snapshots; confirmation_summary.json and weak_confirmation_summary.json are the completed authoritative receipts. All final diagnostics join this results commit; unrelated concurrent branch history is preserved.

## Replay and inventory

Run `python3 analyze_results.py` for saved-data scoring only; `gate/verify_existing_gate.py` checks transported historical gate integrity. Numerical drivers are corner_scan.py, matrix_prefix.py / matrix_probe.py, confirm_firsts.py, recheck_predecessors.py, core/core_diagnostic.py, core/scalar_corners.py and auxiliary_checks.py. MP replay needs gmpy2/python-flint plus NumPy/SciPy/mpmath/threadpoolctl; plots use matplotlib. Historical absolute paths in producer metadata are provenance; source inputs are transported under inputs/.

SCORES.json is machine-readable scoring; SHA256SUMS covers the published packet except itself. Independent read-only review is under review/. This computation calibrates detectors only and never occupies a mathematical quantifier.
