# SCREW_LINE_v1

DIAGNOSTIC_NEVER_A_PROOF. Route B = CHALLENGER / NOT_RH. No route-state or RH export is changed.

Pinned numerical base: `1c91c4c86ef6987782c08c84e22707d1b7324646`; native κ=1.1, N=m, L=log m. All 221 integer m=20,…,240 are evaluated for each world: 442 compressed forms, without a full-carrier eigensystem. The preceding EDGE_CAPACITY packet is a separate commit.

## Outcome

The finite inverse-kernel proxy is not monotone on the requested moving sequence. A source-aligned geometric alternative does discriminate these finite controls: fixed-mesh screw-increment innovation variances remain positive and decrease for ζ, while DH has independently replayed negative increment-Gram witnesses. This is finite geometry, not a proof of global positivity or RH.

The requested actual Weyl-radius identification remains a **GAP**. Suzuki's map is a derivative-test pullback, not direct sampling of the screw curve. An actual canonical-system/kernel normalization has not been supplied. We therefore report `r_proxy=1/(Im z K_z)` explicitly as a formal proxy. Its square cannot become negative for a real nonzero K_z; inertia of the full compressed form detects indefiniteness.

## Source and evaluation map

Suzuki arXiv:2209.04658v3 (1.10) relates the Weil form to the screw kernel through derivatives of test functions. Zero-extended windows have endpoint masses in those derivatives. The constant-window normalization is `g(L)=−k[χ_(0,L)]/2`, agreeing with arXiv:2206.03682v4 (1.1). The full BV extension is guarded in source_audit/SOURCE_AUDIT.md. Global positive screw geometry is RH-equivalent and is not assumed here.

Both Fourier evaluation at z=i/2,i,2i and the distinct analytic continuation of the interior cosine are retained and labeled. The latter does not analytically continue the zero-extended indicator. Fourier evaluation is the relevant spectral-variable interpretation, but neither finite evaluation metric is automatically Suzuki's canonical kernel.

With E the actual low-zero evaluation rows and S=range(E*)=J-perp, the basis-independent formula is `K_z=(E e_z)* (E A E*)^−1 (E e_z)`. For the physical endpoint, `e_b=(1,√2,…,√2)/√L`. Independent QR/capacity comparisons validate this congruence calculation. In indefinite cells these expressions are algebraic inverse forms, not positive RKHS kernels.

## Kernel series and DH failure

Every cell retains the endpoint kernel, both evaluation gauges at all three points, endpoint cross-kernels, raw-congruence inertia, solve residuals and finite arch-tail bounds. kernels/RESULT.md, kernels.csv and the per-cell records give the complete series.

| m | ζ K(b,b) | DH K(b,b) | ζ r_proxy(i) | DH r_proxy(i) | DH negative levels |
|---:|---:|---:|---:|---:|---:|
| 20 | 6.38190 | 29.59384 | 9.59552 | 2.30427e−6 | 0 |
| 40 | 31.52272 | 81.75971 | 0.775819 | 2.80167e−13 | 0 |
| 55 | 72.24013 | 121.18439 | 1.14459e−3 | 2.57862e−16 | 1 |
| 80 | 121.40094 | 229.64610 | 1.01014e−5 | 5.56567e−26 | 2 |
| 120 | 209.05700 | 387.79121 | 1.74536e−8 | 1.17333e−33 | 2 |
| 160 | 366.44097 | 613.85053 | 6.85564e−14 | 5.15161e−45 | 4 |
| 200 | 569.15267 | 894.84805 | 3.68589e−20 | 3.18130e−56 | 4 |
| 240 | 700.69632 | 1167.00465 | 4.81760e−22 | 2.63649e−66 | 5 |

The first native DH complement failure is **m=52**, so the registered [50,56] prediction passes. Counts at m51,52,53,54 are 0,1,0,1. The γ≈85.69935 off-line quartet first enters the native cutoff at m49, so entry and loss of positivity are separate events. The full-carrier onset at m51 from the earlier packet is a different test. Recovery at m53 is possible because these moving complements are not nested. All 221 ζ compressed forms are numerically positive; 188 DH forms are indefinite.

At DH52 all three Fourier point kernels are negative, while K(b,b) stays positive. Later many point kernels are positive despite indefinite forms (e.g. DH55). Across all cells r_proxy² is never negative. No scalar diagonal substitutes for inertia.

On the discrete ζ schedule, each Fourier r_proxy has 93 increases and 127 decreases. At prime-power arrivals alone it has 20 increases and 34 decreases. Thus homogeneous fixed-threshold kicks do not imply monotone sampled radii. The separate interior-cosine gauge has different counts; all are retained in the transition tables.

## Smooth slopes versus arithmetic kinks

g is continuous. Its arithmetic derivative jump at log n is exactly `b(n)/√n`. For ζ this is Λ(n)/√n. There are 54 prime-power thresholds in the range, all with positive ζ weights. DH weights on those thresholds have 25 positive, 27 negative and 2 exact zeros; another 75 non-prime-power DH atoms are nonzero. Exact rational-polynomial coefficient checks distinguish true zeros from cancellation noise.

For τ defined by L_τ=L exp τ, with N and active zero nodes fixed, write `h_z=e_b* U G^−1 U*e_z`. The source derivative kink gives

`jump dot K_z=2[b(n)/√n] L |h_z|²`,

`jump dot r_proxy=−2[b(n)/√n] L |h_z|²/(Im z K_z²)`.

Hence ζ local K-slope kicks are nonnegative and proxy-radius slope kicks nonpositive, with strict sign requiring nonzero coupling. This is rank-one inverse algebra, not a new positivity theorem. DH permits both signs. Derivatives in L divide these formulas by L.

transitions/ contains every magnitude and its normalized arithmetic coefficient, every discrete increment, and independent fixed-N/frozen-head smooth derivative calculations for all 54 prime powers in both worlds and all six evaluations. The latter exclude the birth atom on both sides of the central difference; the right derivative is the smooth left derivative plus the exact kink. At h=1e−30, the inverse chain-rule check has maximum relative discrepancy 9.73e−53; h=1e−35 anchor repetitions agree within 5.88e−53. Changes of N or active-head cardinality are not called prime-power kinks. For example ζ81 at z=i has smooth left slope +0.00819346, kink −0.00200083, and right slope +0.00619263: even the local total slope need not decrease.

The registered homogeneous-sign idea is confirmed for the local arithmetic derivative kinks; it fails for discrete Fourier-radius increments at prime-power arrivals. No ambiguity between these two interpretations is hidden in prediction scoring.

## Alternative geometry on the curve itself

At fixed mesh Δ, the actual source g gives increment covariances `h_k=2g(kΔ)−g((k−1)Δ)−g((k+1)Δ)`. Their principal prefixes are nested. For positive prefixes, the innovation Schur complement is a squared distance and is nonincreasing by the stationary Toeplitz recursion.

| Δ | ζ positive decreasing prefixes | First DH negative prefix | Length | exp(length) |
|---|---:|---:|---:|---:|
| 1/64 | 350/350 | 275 | 4.296875 | 73.46984 |
| 1/128 | 701/701 | 484 | 3.78125 | 43.87085 |

See geometry/innovation.svg. The DH negative normalized quadratic witnesses are −7.94653e−6 and −1.92529e−5. Independent direct Toeplitz evaluation reproduces the signed Schur pivots to relative error below 3.50e−70. Source-integral checks and 100/160-digit replay pass; matching stored values means agreement at the stored 70-digit precision. Continuing the recursion after a negative pivot is signed algebra, not positive prediction geometry.

This variable meets the finite discrimination goal on both tested meshes. Its failure location is strongly mesh-dependent and is not a continuum onset. exp(length) is only a length label, not the literal CCM carrier index. The last grid points lie just below log240. General Schur-complement monotonicity under positive prefixes is not evidence of cofinal ζ positivity.

## Reproduction and limits

The source form is unchanged; its faster analytic archimedean evaluation is checked against pinned source matrices and saved compressed energies, not just against full-matrix norms. The zero census is pinned numerical input. Midpoint Arb/FLINT arithmetic, LDL pivots and finite differences here are numerical diagnostics, not interval eigenvalue certificates; increasing working precision does not certify the input zeros.

Raw CSVs and per-cell numeric records are losslessly archived to keep the commit compact. Run `python verify_packet.py`, then `python restore_data.py`, then `python verify_packet.py` to validate committed bytes and every restored member. DATA_MANIFEST.json pins member hashes. Recompute kernels with `PYTHONPATH=/path/to/python-flint python kernels/screw_kernels.py --input-root source_inputs`; python-flint 0.9.0 and mpmath are used. Subdirectory reports document derivative, coefficient and geometry reproduction. No source eigensystem or zero search is needed.
