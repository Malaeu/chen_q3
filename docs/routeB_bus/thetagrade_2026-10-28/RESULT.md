# Parity gap table on the literal CCM matrix (THETAGRADE Q2 first fact), 2026-10-28

DIAGNOSTIC_NEVER_A_PROOF. 15 cells m = 2..16, m = N, literal `matrix_K` and selected reference row from
`../fokas_k_sign_2026-09-25/`. Script `parity_gap_table.py`; raw rows `table_dps120.jsonl`, `table_dps170.jsonl`.
Precision check: dps 120 and dps 170 agree in all 20 printed digits on every cell.
Cross-check: alpha_4, alpha_8, alpha_13 = 0.0309 / 0.0553 / 0.0605 match PAPER_CHAIN G3 diagnostics 0.03089 / 0.05534 / 0.06052.

| m | λ_even | λ_odd | D_m | λ_odd/λ_even | ‖r_m‖ | δ_m | α_m | (a_m−λ₁)/D_m | cos²(ξ,η)/λ₁ |
|---|---|---|---|---|---|---|---|---|---|
| 2 | 3.06e-3 | 0.126 | 0.123 | 41 | 1.99e-2 | 0.122 | 0.020 | 0.0032 | 1.50 |
| 4 | 1.70e-9 | 3.03e-7 | 3.02e-7 | 179 | 5.29e-5 | 2.23e-7 | 0.031 | 0.26 | 1.59 |
| 5 | 3.55e-12 | 1.03e-9 | 1.02e-9 | 288 | 3.11e-5 | −7.81e-9 | 0.043 | 8.7 | 1.61 |
| 8 | 1.02e-19 | 3.34e-17 | 3.33e-17 | 326 | 2.97e-6 | −1.14e-11 | 0.055 | 3.4e5 | 1.31 |
| 12 | 6.79e-29 | 4.15e-26 | 4.14e-26 | 611 | 4.98e-9 | −6.32e-17 | 0.060 | 1.5e9 | 1.17 |
| 16 | 5.46e-38 | 6.85e-35 | 6.85e-35 | 1256 | 7.70e-10 | −7.35e-19 | 0.058 | 1.1e16 | 1.29 |
All 15 cells are in the jsonl files; the rows shown follow the same trend.

## Findings
1. Parity: on all 15 cells the ground state is simple and even, and λ₂ = λ_odd, so the simplicity gap equals D_m > 0.
   The relative gap λ_odd/λ_even grows from 41 to 1256. No sign of a parity collapse. Observer prediction "D_m > 0 on all cells" (0.85): hit.
2. Residual side of G1 fails on cells 5..16: δ_m < 0. Mechanism (exact): q_m is even (parity defect 0), so every odd y is orthogonal to q_m and
   δ_m ≤ λ_odd − a_m. Here a_m − λ₁ exceeds D_m by 8.7 (m=5) up to 1.1e16 (m=16), so a_m > λ_odd and δ_m < 0.
   With a = a_m, the literal odd floor hoddEv (λ_odd − a_m ≥ β₀ > 0) fails on the same cells.
3. Cause: α_m does not decay; it sits at 0.055–0.060 for m ≥ 8. The selected row is not close to the ground state, and a_m carries its weight on high eigenvalues.
   So the residual part of G1 is the tracking problem (G3) in another form, and it needs far more than a polynomial rate: a_m − λ₁ < D_m.
4. The ratio D_m/‖r_m‖ collapses (6.2 → 8.9e-26). This is NOT a parity collapse: ‖r_m‖ measures the distance of q_m from the ground state.
   The observer's branch wording ("D/r falls ⇒ parity collapse") was a poor discriminator; withdrawn.
5. Symptom: cos²(ξ, η)/λ₁ stays between 1.17 and 1.85 on all cells. So η·ξ ≍ √λ_min: the overlap of the ground state with the constant vector
   is tied to λ_min itself. Readings: (a) λ_min is the pole-term energy of a near-null vector of the remaining form; (b) coincidence of scales. Not explained.
6. Symptom: the selected row is conjugate-symmetric (z_{−n} = conj z_n) with an odd imaginary part 3.9e-3 (m=2) falling to 1.5e-41 (m=16). Source not checked.

## Consequence for G1 (split)
G1a — simple and even ground state: holds on all cells with a growing relative gap. Candidate for proof without zero input (Proshka's candidate B, parity-block Schur).
G1b — cellwise floor δ_m > 0 and ‖r_m‖/δ_m → 0 for the selected row, and hoddEv with a = a_m: false on cells 5..16.
Theorem shape to test: a_m > λ_min(K_m|odd) eventually. If proved, G1b and literal hoddEv are killed cofinally.

## Residue closed form and Stieltjes weights (observer, 2026-10-29)
Tool: `parity_residue_probe.py` (extended), outputs `residue_dps120.jsonl`, `residue_dps170.jsonl`; all fields agree between the two precisions on m = 2..16.
1. Closed form of Proshka's residue (4.13): R_m = ∏_i(λ_i(E) − μ) / ∏_{j≥2}(μ_j − μ), relative error ≤ 8.6e-88. So sign R_m = (−1)^{#even levels below μ}.
   The residue test counts levels; it is not a cheaper object. Count is 1 on every cell.
2. v0·y = (A0 − μ)(d·y) − (B^{-2}β_o)·y is a difference of two terms equal to 6+ digits from m = 6 (rule 18: not a usable sign representation).
   The bracket (4.16) holds on every cell but ε_m/(μ − λ_min(E)) falls from 0.17 (m=2) to 1.9e-46 (m=16): C_m carries 1/g_o.
3. f_m(t) = 1/g_m(t), g_m(t) = ⟨η,(K_m − t)^{-1}e_0⟩ = h^T(E − t)^{-1}e_0 = det(O − t)/det(E − t); |f g − 1| ≤ 3.8e-87.
   g_m = Σ_i w_i/(λ_i − t), w_i = (η·ξ_i)ξ_i(0), Σ w_i = 1 exactly. Poles = even levels, zeros = odd levels.
4. G1a ⟺ w_0 > 0 and g_m has no zero below λ_0(E). Sufficient (Abel): all bottom-up partial sums W_k > 0. On every cell min_k W_k = W_0 = w_0 > 0.
   Negative w_i occur only at even levels ≥ 8 (m = 9, 10, 12..15), total negative mass ≤ 0.048.
5. Parity pattern of the full spectrum: strict alternation E,O,E,... on m = 2..8, 11, 16; on m = 9, 10, 12..15 the first break is at level ≥ 14 of 2m+1 (top third).
   Eigenvector sign changes (m ≤ 8): over the lower half of the spectrum each level has one sign change fewer than the level below it.
Status: DIAGNOSTIC_NEVER_A_PROOF. Batch: `../proshka/PROSHKA_REQUEST_STIELTJES_2026-10-29.txt`.

## Off-diagonal probe (2026-10-29, after STIELTJES was sent)

Question: are G1a, w_0 > 0 and all Abel sums W_k > 0 an artefact of our diagonal N = lambda^2 = m?
`offdiag_w0_probe.py` builds the literal CCM matrix with N (modes -N..N) and lambda^2
(prime cutoff, L = log lambda^2) independent; on N = lambda^2 = m it equals
`full_center_probe.matrix_K` exactly (max |diff| = 0.0 on m = 3, 7).

Grid: N in {2,3,4,6,8,10,12,16} x lambda^2 in {1.5,2,3,5,8,13,20,30,50} = 72 cells, dps 60 and 100
(`offdiag_dps60.jsonl`, `offdiag_dps100.jsonl`).

- All 72 cells: G1a (lambda_min(E) < lambda_min(O)), w_0 > 0, every W_k > 0. Failures: 0.
- Minimum of W_k is always W_0 = w_0 (argmin 0 in every cell), as on the diagonal.
- Negative individual weights occur in 15 cells, never enough to make a partial sum negative.
- Smallest w_0 = 2.88e-24 at N = 16, lambda^2 = 50 (lambda_min(E) = 5.2e-49, mu = 8.9e-46).
- dps 60 vs 100: w_0, lambda_min(E), min W_k identical to 10 printed digits in all cells.

Reading: the STIELTJES sign pattern is not a feature of the diagonal schedule; it holds on the
two-parameter (lambda, N) family on this grid. w_0 shrinks fast with N and lambda, so a proof
needs a lower bound for w_0 that is relative (e.g. against the parity gap), not absolute.
DIAGNOSTIC_NEVER_A_PROOF. Observer prediction "w_0 <= 0 somewhere off-diagonal" (0.15) did not occur.

## After STIELTJES: three cheap bracket probes (2026-10-29), all negative

Goal: a source-defined tau with lambda_min(E) <= tau < mu = lambda_min(O) (Proshka (4.6)-(4.7)), using mu/lambda >= 41.

1. w0 against the parity gap (`residue_dps170.jsonl`, `offdiag_dps100.jsonl`). w0/(mu - lambda) grows only because
   the energy scale shrinks (dimensional). Scale-free w0/((mu - lambda)/mu): 0.14 (m=2) -> 8.3e-19 (m=16);
   off-diagonal min 2.9e-24. w0 is not bounded by a relative gap. Observer prediction 0.4 failed.
2. Theta-Gaussian trial plane span{bs, ds} from `full_center_probe.gaussian_plane` (`trial_vector_probe.py`,
   `trial_vector_dps80.jsonl`): U/lambda = 1.12, 15.4, 19.3, 110, 1071 on m = 2..6; U < mu holds for m <= 5 and
   fails at m = 6 (mu/U = 0.34). Observer prediction 0.35 (U within x5) failed.
3. Previous-cell bottom at fixed lambda^2 (E_N is a principal submatrix of E_N'; Cauchy interlacing, 0 violations):
   tau = lambda_min(E_N) < mu(N') in only 30/63 pairs; worst tau/lambda(N') = 1.4e9 (N 12 -> 16, lambda^2 = 50).

Reading: lambda_min(E) falls by ~10^2.4 per added mode; cheap explicit even vectors overshoot it by more than the
mu/lambda margin from m = 6 on. An upper bracket for lambda needs a trial vector close to the true ground state
(candidate: prolate/PSWF coefficients at bandwidth c = 2 pi m), or Proshka's direct route (12.1).
DIAGNOSTIC_NEVER_A_PROOF.

## CCM prolate packet k1 as trial vector (2026-10-29): negative, and why every trial vector fails

`k1_packet_rayleigh_probe.py` on the cached diagonal cell m = 13 (`k1_packet_m13.json`): overlap with the true even
ground |cos| = 0.99817, yet Rayleigh U = 4.2e-16 against lambda = 7.9e-31 and mu = 6.4e-28 (U/lambda = 5.3e14, U > mu).
Spectrum at m = 13: even 7.9e-31, 2.8e-25, 1.4e-20, 3.1e-16, 1.3e-12, ..., 3.3; odd 6.4e-28, 8.0e-23, 2.1e-18, ..., 3.1.
Levels span 31 orders and alternate E, O, E, O over the whole low spectrum. A Rayleigh bound U < mu needs the leaked
mass sin^2 to be below ~mu/||K|| ~ 1e-28, i.e. a trial vector correct to ~14 digits. k1 has sin^2 = 3.7e-3.
Kill reason (with number): an upper bracket for lambda from any source trial vector requires exponentially accurate
agreement with the ground state; no cheap vector can supply it. Trial-vector route for (4.6)-(4.7) closed.
Observer prediction 0.3 failed. DIAGNOSTIC_NEVER_A_PROOF.

Follow-up the same day: the E, O, E, O alternation suggested a Gantmacher-Krein mechanism (a centrosymmetric
oscillation matrix has a simple top eigenvalue with a symmetric vector and alternating parities). Test: all minors of
K^{-1} and of D K^{-1} D, D = diag((-1)^n), on m = 2, 3, 4 (dps 80). Negative minors: 108/251 and 116/251 (m=2),
1672/3431 and 1696/3431 (m=3), 24218/48619 and 23530/48619 (m=4). K^{-1} is far from totally positive in mode
coordinates in either gauge; the theorem does not apply here. Any oscillation mechanism must live in another basis.

## Perron-Frobenius probe (2026-10-29): the bulk G = K - W02 behaves like a positivity-improving operator

Hypothesis (literature agent 29.10, own derivation, not from a source): archimedean part = Levy-Khintchine generator
with positive jump measure, prime part = negative shifts by log n; both give nonpositive cross pairing of disjoint
nonnegative functions (Beurling-Deny), so exp(-tG) would be positivity improving on the window. Only the rank-2 pole
term W02 = kappa(u u^T - v v^T) (u even, v odd) breaks it.
`pf_probe.py`, `pf_probe_dps120.jsonl`, m = 2, 3, 4, 5, 6, 8, 10, 12 (interior grid, 2% margin):

| m | bottom of G | sector | sign changes | min/max | lam_O(G) | bottom of K | K sign changes |
|---|---|---|---|---|---|---|---|
| 2 | -1.279 | E | 0 | 0.59 | 0.135 | 3.1e-3 | 0 |
| 4 | -2.831 | E | 0 | 0.78 | 4.5e-4 | 1.7e-9 | 0 |
| 6 | -3.797 | E | 0 | 0.90 | 1.7e-8 | 8.0e-15 | 0 |
| 8 | -4.510 | E | 0 | 0.83 | 3.7e-13 | 1.0e-19 | 0 |
| 10 | -5.116 | E | 0 | 0.84 | 3.4e-17 | 1.3e-24 | 0 |
| 12 | -5.622 | E | 0 | 0.85 | 1.6e-21 | 6.8e-29 | 0 |

Reading: the bottom of G is even, simple, strongly negative (about -2.2 log m) and its function is strictly positive
and flat (min/max 0.59-0.90): the PF picture. The odd block of G is positive. The pole term adds +kappa u u^T to the
even block (lifts the one negative level to the tiny positive bottom of K) and -kappa v v^T to the odd block.
So window positivity and G1a for K become rank-two secular questions over a PF bulk.
Not repeated: the 10.09 kill (Progress_Log 2026-09-10) is the ODD half-line semigroup (reflected +log2/sqrt2);
this probe is the full window without the pole term. DIAGNOSTIC_NEVER_A_PROOF.

### Two secular scalars and the limit of the PF picture (same day)

`pf_secular_probe.py`, `pf_secular_dps120.jsonl`. Split K = G + kappa(u u^T - v v^T) reproduces matrix_K's W02 to 1.8e-62.
On m = 2..12 (8 cells): G_E has exactly ONE negative eigenvalue (about -2.2 log m), the rest positive; G_O has none.
Then window positivity is exactly: K_E >= 0 <=> s_E = 1 + kappa u^T G^-1 u <= 0, K_O >= 0 <=> s_O = 1 - kappa v^T G^-1 v >= 0.

| m | s_E | lam0(K_E) | s_E / lam0(K_E) | s_O | lam0(G_O) |
|---|---|---|---|---|---|
| 2 | -2.79e-3 | 3.06e-3 | -0.913 | 0.927 | 0.135 |
| 4 | -1.18e-9 | 1.70e-9 | -0.693 | 1.02e-5 | 4.5e-4 |
| 6 | -5.13e-15 | 8.00e-15 | -0.642 | 7.76e-11 | 1.7e-8 |
| 8 | -6.39e-20 | 1.02e-19 | -0.624 | 8.23e-16 | 3.7e-13 |
| 10 | -8.24e-25 | 1.34e-24 | -0.613 | 2.00e-20 | 3.4e-17 |
| 12 | -4.12e-29 | 6.79e-29 | -0.607 | 9.41e-25 | 1.6e-21 |

LIMIT (observer, after advisor): Perron-Frobenius for G, if proved, gives unconditionally only: simple even strictly
positive bottom of G, nonzero overlap <u, ground>. The resolvent (G - t)^-1 is a positive kernel only for t BELOW
the bottom of G. The signs s_E <= 0 and s_O >= 0 live at t = 0, above the negative bottom, where PF says nothing.
So PF does not give the sign of s_E or s_O, and these two scalars are still the whole of window positivity (RH-hard).
"Exactly one negative even level of G" and "G_O >= 0" are also not given by PF.
Novelty check: Suzuki 2606.09096 Thm 1.4 (§5, Dirichlet form + irreducibility, Fukushima-Oshima-Takeda) proves the
PF mechanism only for small windows a < log(2)/2 (no primes) via the a -> 0 limit; he does not split off the pole term.
Extension to all windows with primes as positive jumps plus bounded potential: observer derivation, unverified.

## "Entropy" probe: is alpha/T ~ 0.35 a smooth law? (2026-10-29, owner's Perelman question)

`alpha_over_T_scan.py` (flint arb via r2_second_jet.ground_full, dps = max(400, 9m), same as 04.09; m = 83
reproduces 0.348). All diagonal cells m = N = 40..120: `alpha_over_T_m40_120.jsonl`, 81 rows.
- alpha/T is NOT a smooth constant: 0.328 (m = 44) .. 0.351 (m = 119), slow rise, and a step-to-step jitter of
  about 1e-3 at EVERY m (mean |jump| 1.03e-3 at prime-power m, 1.04e-3 at other m).
- Prime-power steps (a new prime enters the matrix): 16/21 jumps positive, mean +3.9e-4; other even m 22/39
  positive, mean +2.4e-4; other odd m 9/20, mean +1.5e-4. Against the drifting baseline this is weak evidence
  (fair-coin tail 0.013, baseline-corrected about 0.04).
- Reading: strict reading A (one smooth zero-free constant) is refuted at the 1e-3 level. Reading B (a clean prime
  signature) is not confirmed either: composite steps jitter as much as prime steps. On the diagonal each step changes
  three things at once (one more mode N, L = log m, and possibly one more prime), so this design cannot separate
  arithmetic from mode truncation. A clean test needs fixed N and lambda^2 moved across a single prime
  (CCMArbBuilder L_override; check its z = 1/m^2 term first). DIAGNOSTIC_NEVER_A_PROOF.

## After MARKOV verdict (2026-10-30): pf_probe fix, bracket (5.4), identity (6.8)

Audit: `docs/routeB_bus/proshka/MARKOV_AUDIT_2026-10-30.md`.
- pf_probe.py defect (verdict §2.5): `mp.re` erased an odd (imaginary) bottom function. Fixed with a common phase and an
  assert; planted odd bottom now reads sector O. Rerun `pf_probe_dps120_fixed.jsonl` (m = 2..12): old rows identical,
  m = 7, 9, 11 added, all even, no sign change.
- `bracket_probe.py` (dps 120, m = 2..12): bracket (5.4) exists on every cell (automatic between the two roots), but
  Phi_E(tau) ~ 0.6 tau and Phi_O(tau) ~ 500 tau, e.g. 9.8e-28 and 9.0e-25 at m = 12. Same cancellation as s_E, s_O.
  Phi_E root = lam0(K_E) at m = 12 (no untouched level).
- Pole-free odd block: lam0(G_O) = 0.135 (m = 2) -> 1.6e-21 (m = 12). By verdict (4.19) G_O >= 0 cofinally <=> RH.
  Removing the pole leaves the margin as small as for K.
- `theta_jump_identity_check.py` (float64): identity (6.8) k[hF] = E_h[F] - 8(Var_mu F + (int tanh(x/2) F dmu)^2)
  holds to 9.7e-10 and 1.9e-10 on two smooth F; Weil-form code ties to matrix K to 1.4e-9 (m = 3, 5).
  Second F: E_h = 0.01960 vs 8(...) = 0.01958, inequality (6.9) within 0.1% of saturation. DIAGNOSTIC_NEVER_A_PROOF.

## SHAKE (2026-10-30): how sharply does the window sign depend on where the primes sit?

`shake_probe.py` (dps 80, m = 3..12), Hellmann-Feynman on literal K_m, control by finite difference (agrees to 6 digits,
m = 12 E to 1.5e-4 relative because the step 1e-26 is near the margin). Shift log p -> log p + eps (powers by j eps,
Beurling-style generalized prime) and c_{p^j} -> (1 + delta) c_{p^j}.

| m | lam0(K_E) | d lam0_E / d eps (p=2) | lam0(K_O) | d lam0_O / d eps (p=2) | allowed eps window for log 2 |
|---|---|---|---|---|---|
| 3 | 1.0e-6 | +0.269 | 1.2e-4 | -1.559 | (-3.7e-6, +7.5e-5) |
| 6 | 8.0e-15 | +0.576 | 2.9e-12 | -1.288 | (-1.4e-14, +2.2e-12) |
| 8 | 1.0e-19 | +0.627 | 3.3e-17 | -1.188 | (-1.6e-19, +2.8e-17) |
| 12 | 6.8e-29 | +0.673 | 4.1e-26 | -1.082 | (-1.0e-28, +3.8e-26) |

- Branch A of the prediction (0.85) holds: the derivative is O(1) while the margin is 1e-29; ratio up to 1e28.
- Strange, recorded when seen: the pin is TWO-SIDED. Moving log 2 left breaks the even sector, moving it right breaks the
  odd sector; the weight c_2 is pinned the same way (d/d delta: E -0.097, O +0.382 at m = 12). No first-order direction of
  moving the prime 2 keeps both sectors positive. Window width shrinks like lam0 (about e^{-6.5 m}).
- Other primes: p = 3 O-sector -0.37 at m = 12; even p = 11 (log 11 near L) has 1.1e-20, still 1.6e8 times lam0_E.
- Reading: on this object the Weil sign at m = 12 requires log 2 to about 28 digits. Any argument that sees primes only up to an
  error (sieve bounds, averages, density theorems, Beurling-type generalized primes) cannot give the sign. This is the
  Beurling / DMV barrier made quantitative on our matrix. Limit: any generic perturbation of K of the same size would also break
  the sign (the margin is tiny); the arithmetic content is the two-sided pin, not the size alone. DIAGNOSTIC_NEVER_A_PROOF.

### SHAKE control (same day): the two-sided pin is NOT arithmetic — retraction

`shake_fake_atom.py` (dps 60, m = 6, 8, 12): a fake atom at any shift a in (0, L), speed of each sector bottom when it moves.
Two-sided pin (E speed > 0, O speed < 0) holds for every grid point with a above a threshold a* in (0.54, 0.59) (absolute
shift, the same for m = 6, 8, 12); below a* it fails. log 2 = 0.693 > a*, so every prime position is in the pinned zone
automatically. The pin is a shape property of the bottom vectors (positive even bump: autocorrelation decreasing; odd bottom:
autocorrelation increasing for a > a*), not a property of the primes.
Retraction (observer): "the arithmetic content is the two-sided pin" above is wrong. Error: I read a sign pattern on the
prime positions without the control at non-prime positions (rule 12, table before claim). What stands: the size statement
(O(1) speed vs 1e-29 margin) and its limit (any perturbation of that size breaks the sign).
Recorded as strange, unexplained: the threshold a* ~ 0.56 does not move with m. Readings: (A) it is a property of the
limiting near-null (prolate-type) functions and has a closed form; (B) grid artefact. Discriminator: finer grid in a and
more m. Note: shake_probe.py now has a __main__ guard (importing it ran its main loop).

## PINGEOM (2026-10-30): the pin threshold a* is fixed by the odd bottom, and the odd bottom looks like h'

Owner's word: «это геометрия, это уже Перельман, добить». `pingeom_probe.py` (dps 60, 200-point grid in a, m = 4..16),
`pingeom_limit.py` (dps 30). Output `pingeom_dps60.jsonl`.
- Even speed never changes sign on (0, L) for any m: the even sector is pinned from the left for an atom at ANY shift.
- Odd speed changes sign exactly once, at a*(m) = 0.542 (6), 0.556 (8), 0.570 (10), 0.578 (12), 0.574 (14), 0.575 (16).
  So the threshold of the two-sided pin is a property of the odd bottom alone.
- Shape: even bottom vs h (MARKOV (4.3), h-hat = 4 Xi): cosine 0.99999821 (m=6) .. 0.99921845 (m=16).
  Odd bottom vs h': 0.99996806 (6) .. 0.99799026 (16); best of {h', x h, tanh(x/2) h, sinh(x/2) h}.
  h and h' are exact null vectors of the global Weil form (their transforms carry the factor xi, which vanishes at every zero).
- If the odd bottom were exactly h', the threshold would be the minimum of the autocorrelation of h':
  R(a) ~ int_0^inf t^2 Xi(t)^2 cos(t a) dt (Riemann Xi). Two independent routes (x-space quadrature of h', and the Xi integral)
  give the same root a*_h' = 0.547636729746 (12 digits). (Route-2 normalisation is off by a factor 2: R(0) 26.11 vs 52.22; the root
  does not depend on it.)
- Strange, recorded when seen: measured a*(m) sits at 0.574-0.578 for m = 12..16, 0.027 above a*_h', more than the grid step
  (0.012). And the cosines with h and h' DECREASE as m grows. Readings: (A) the window bottoms are not converging to h, h' but to
  other members of the radical (even: h, h'', h''''...; odd: h', h''', ...), selected by the window; then a*(m) has a different
  limit. (B) finite-m transient, a*(m) -> 0.5476 for larger m. Discriminator: least-squares fit of the bottoms in
  span{h', h''', h^(5)} (odd) and span{h, h'', h''''} (even) for m = 6..24, plus a*(m) for m up to 24.
  Link: the even part is the G3 question (does the ground track a fixed trial vector?). DIAGNOSTIC_NEVER_A_PROOF.

### PINGEOM fit (same day): the window selects a FIXED element of the xi-radical family, not h

`pingeom_fit.py` (dps 100, m = 6..24): least squares of the sector bottoms in span{h, h'', h''''} (even) and
span{h', h''', h^(5)} (odd), weights normalised as c_i ||D_i||. Relative residual 2e-6 .. 2.4e-4 at every m: the bottoms
lie in the radical family to 4-6 digits. Weights converge to a plateau:
even (h, h'', h'''') = (0.99999, -0.0045, -0.0025) m=6; (0.9990, 0.044, 0.0017) m=12; (0.9986, 0.0532, 0.0035) m=20;
(0.9986, 0.0533, 0.0036) m=24. Odd (h', h''', h^(5)) = (0.9997, -0.022, -0.007) m=6; (0.996, 0.089, 0.004) m=12;
(0.9938, 0.1106, 0.0087) m=20; (0.9938, 0.1108, 0.0090) m=24. Threshold a*(m) = 0.547, 0.558, 0.576, 0.578, 0.574, 0.577.
Reading A of the previous entry holds: the limit is not h, h' but a fixed radical vector; the plateau a* ~ 0.576 belongs to it.
Selection rule: `pingeom_select.py` tested minimisers of int w f^2 / int f^2 in the same 3-dim spans for w = x^2, x^4, cosh x,
e^{2|x|}: all give the h'' weight about -0.19 (even) and -0.24 .. -0.30 (odd), opposite sign to the window (+0.053, +0.111).
The window bottom is BROADER than h; "most concentrated radical vector" is refuted. Rule unknown: question for Proshka (CONFINE Q1).

### Odd bottom = derivative of even bottom (translation mode); one smoothing parameter for both sectors (2026-10-30)

- `odd_is_derivative.py` (dps 60, model-free): cosine between the odd bottom f_O and the x-derivative of the even bottom f_E,
  both synthesized from the literal K_m: 1 - cos = 9.3e-5 (m=4), 2.6e-5 (6), 1.9e-5 (8), 4.6e-6 (12), 1.5e-6 (16). Monotone to 0.
- `heatsmooth_check.py`: plateau weights read as f = h + s h'' + c2 h'''' (Fourier 4 xi (1 - s z^2 + ...)) give the SAME s in both
  sectors: even s = 0.003082 (m=24), 0.003079 (m=20); odd s = 0.003007 (24), 0.003001 (20). Second order: c2 / (s^2/2) = 0.75 .. 0.81,
  so a pure Gaussian smoothing xi e^{-s z^2} is only a first-order match (c2 still drifts 4% between m = 20 and 24).
- Geometric reading (observer, to be checked by Proshka): the radical of the global Weil form is translation invariant
  (a shift multiplies the transform by e^{-i delta z}; the factor xi stays). The window breaks translation and pins the radical
  object at the centre; the odd bottom is the translation (Goldstone-type) mode of the even bottom. G1a then reads: moving the
  confined object off-centre costs energy. Caveat: a Rayleigh quotient of f_E' only gives an UPPER bound for lam0(K_O)
  (spectrum spans ~30 orders), so this picture does not yet bound the parity gap from below. DIAGNOSTIC_NEVER_A_PROOF.

### Geometry breaks together with the sign (2026-10-30)

`break_sign_keep_shape.py` (dps 80, m = 12): shift log 2 and its powers by eps (Beurling-style), even sector.
| eps | lam0_E | 1-|cos| old vs new bottom | radical-family residual (span h, h'', h'''') |
|---|---|---|---|
| 0 | +6.79e-29 | 0 | 1.95e-6 |
| -1e-26 | -6.67e-27 | 3.0e-7 | — |
| -1e-20 | -1.15e-20 | 6.4e-2 | 9.45e-4 |
| -1e-12 | -7.19e-12 | 0.978 | 0.392 |
| -1e-6 | -1.09e-5 | 0.996 | — |
Observer prediction REFUTED (I expected: sign flips, shape stays). The clean xi-geometry of the bottom (heat-smoothed h, odd = its
derivative) exists only for the exact primes; perturbing log 2 destroys the sign and the geometry together, at the same scale.
Reading: the radical family is defined by xi, i.e. by the exact arithmetic (theta function, Poisson summation, Euler product inside
zeta); the window positivity and the window geometry are one phenomenon: "the bottom is a confined xi-radical vector".
Owner's reading 30.10: «геометрия не ломается, физика тоже, а у арифметики нет модели». Observer: the model exists, it is the
theta function h (heat kernel on the circle, modular symmetry); what is missing is a proof that the confined object stays the bottom.

### CONFINE probes (2026-10-30): no confinement law, no de Bruijn-Newman deformation

`confine_probe.py` (dps 100, m = 4..24), output `confine_probe_dps100.jsonl`.
- lam0_E / T1 (T1 = tail energy of the plateau radical vector beyond L/2): 2.1e-4 (m=4), 7.8e-6 (6), 1.4e-6 (8), 4.3e-7 (10),
  7.7e-7 (12), 1.6e-6 (14), 1.8e-6 (16), 5.0e-5 (20), 5.1e-3 (24). Flat-ish only on m = 10..16; lam0 decays like e^{-4.6 m}
  (log-slope -5.38 on 12..16, -4.65 on 16..20, -4.58 on 20..24) while the tail decays much faster. Confinement law refuted.
  lam0 values: E 5.46e-38 (16), 2.58e-46 (20), 2.69e-54 (24); O 6.85e-35, 4.30e-43, 4.55e-51.
- Heat-flow (de Bruijn-Newman) fit e^{t x^2} h of the even bottom: best t runs to the search edge 0.5, residual 1.3e-3 .. 2.5e-2
  versus 2e-6 .. 2e-4 for the radical-family fit. Rejected. The Fourier-side smoothing xi e^{-s z^2} (s ~ 0.003) stays the
  first-order description (heatsmooth_check.py).
Recorded as strange: the decay rate of lam0 per unit m tends to about 4.6 and is not the tail rate. DIAGNOSTIC_NEVER_A_PROOF.
