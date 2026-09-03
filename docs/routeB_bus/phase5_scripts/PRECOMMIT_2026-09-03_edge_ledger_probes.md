# PRECOMMIT — edge-ledger probes (Goal 058), 2026-09-03

Written BEFORE any run. Thresholds below are frozen; they are not to be edited after
data exist. Author: Linux-Claude (observer), on owner instruction «го». Executors:
subagents (Sonnet). Verifier: none — DIAGNOSTIC_NEVER_A_PROOF.

## Object (production, no substitutes)

- Finite CCM Weil matrix exactly as built by `docs/routeB_bus/phase1_scripts/ccm_control_cell_penalty.py`
  (matched the Zenodo 21146461 archimedean reference to 8.5e-20 in Phase 0). Same
  kernel, same prime cutoff, same mode indexing. Any deviation is a stop, not a fix.
- Even sector only (J-even), consistent with `IsSimpleEvenGround`.
- λ₁ = smallest eigenvalue, ξ = its unit-ℓ² even eigenvector, λ₂ = next eigenvalue
  in the even sector. Coefficient row ξ_n, |n| ≤ N, ξ_{−n} = ξ_n.
- Window: L = log m. Schedule (production `m = N = k+2` after cofinal reindex):
  m ∈ {13, 23, 43, 83, 163}, N = m. Secondary N-check at m ∈ {13, 43}: N ∈ {m, 2m}.
- Precision: 120 dps then 240 dps (project standard); a result that moves between
  the two is INSUFFICIENT_PRECISION, not a verdict.

## Probe 1 — absolute gap Δ_m = λ₂ − λ₁ along the schedule

Prediction (K6, registered 2026-09-03 in CHAT_DIGESTS): `P_ABS_GAP_COLLAPSES` p=0.80.
- CONFIRMED: Δ_{163}/Δ_{13} ≤ 1/10 and Δ_m monotone non-increasing over the schedule.
- REFUTED: max Δ_m / min Δ_m ≤ 2 over the schedule.
- else UNRESOLVED. Also report relative gap λ₂/λ₁ and (λ₂−λ₁)/|λ₁|; these are
  descriptive, no threshold.

## Probe 2 — window-variation (Fuchs/Hadamard) identity, numerically

Hold the prime set fixed (primes ≤ m), vary the continuous kernel parameter L around
L₀ = log m: central difference with h = 10⁻⁶·L₀, and independently the
Hellmann–Feynman value ξᵀ(∂Q/∂L)ξ with ∂Q/∂L by the same central difference on the
matrix. Define edge² := ξ_N² + ξ_{−N}² and c_m := −(dλ₁/dL)/edge².
Prediction: `P_FUCHS_IDENTITY_NUMERICALLY_HOLDS` p=0.55.
- CONFIRMED: c_m > 0 for every m in the schedule and max c_m / min c_m ≤ 3.
- REFUTED: sign of c_m changes across the schedule, or max/min ≥ 100.
- else UNRESOLVED. Sanity: finite-difference and Hellmann–Feynman values must agree
  to 6 significant digits; otherwise STOP with `HF_FD_MISMATCH`.
- Same for λ₂ and its eigenvector: c₂_m; report sign of dΔ/dL.

## Probe 3 — ratio kill-test of wall B

q_m(t) := L^{−1/2} Σ_{|n|≤N} (−1)^n ξ_n e^{2πint/L}, t ∈ [−L/2, L/2].
M_m(σ) := ∫_{−L/2}^{L/2} |q_m(t)| e^{σ|t|} dt, computed by adaptive quadrature with
≥ 200 nodes per period 2π/L·… (verify by doubling nodes: change < 10⁻⁸ relative).
R_m(σ) := M_m(σ) / (√L·|ξ_0|). The ratio is scale-invariant, so the A_n-normalization
question does not affect it. σ ∈ {0.10, 0.15, 0.20, 0.25, 0.30, 0.35, 0.40, 0.45}.
Prediction (K6, registered 2026-09-03): `P_GROUND_RATIO_GROWS_AT_SIGMA_0_4` p=0.60.
- GROWS (confirmed): R_m(0.40) monotone increasing over the schedule and
  R_{163}(0.40)/R_{13}(0.40) ≥ 3.
- BOUNDED: max/min of R_m(0.40) over the schedule ≤ 1.5.
- GEOMETRY_FIRST: at fixed m the N-check changes R_m(0.40) by a factor ≥ 2.
- else UNRESOLVED. Store numerator, denominator and ratio separately for every
  (m, N, σ, precision).

## Outputs

`docs/routeB_bus/phase5_scripts/`: `edge_ledger_build.py` (eigenpairs → JSON),
`edge_ledger_fuchs.py`, `edge_ledger_ratio.py`, results as JSON + one Markdown report
`REPORT_2026-09-03_edge_ledger_probes.md` with the three verdict lines quoted from
this file. Register every script in `docs/cartographer/TOOLS.yaml`. Progress bars:
plain print + `\r`, only when `sys.stdout.isatty()`.

## Boundaries

No Lean. No route promotion. No RH claim. `PX_RH_CLAIM: NOT_MADE`. Numbers are
diagnostic; a numerical PASS is not a theorem about the ∀m quantifier.

## ADDENDUM (2026-09-03, after Probe 1 partial rows m ≤ 83 were seen; before any κ was computed) — Probe 4, normalized curvature

Source: Proshka verdict `TRY_GROUND_REALZERO_CURVATURE_VITALI_WITH_PRODUCTION_RATE_REPAIR`
(owner-relayed chat paste, 2026-09-03), which registered BEFORE any run:
`P_CURVATURE_SOURCE_1` p=0.65: "exact normalized curvature remains bounded or stabilizes
on the production schedule even if the old exponential moment ratio grows."
Observer's independent check of the formula (sympy, 2026-09-03): K_n''(0) = −2L/x_n²,
K_0''(0) = −L³/12, functional norm² = 1/144 + 1/180 = 1/80.

Definition (per cell, from the λ₁ eigenvector ξ in ±N indexing, Σξ_n² = 1):
  F(0)   = √L · ξ_0
  F''(0) = −L^{5/2} · [ ξ_0/12 + (1/(2π²)) · Σ_{n≠0, |n|≤N} ξ_n / n² ]
  κ      = −F''(0) / (2 F(0)) = (L²/2) · [ 1/12 + (1/(2π² ξ_0)) · Σ_{n≠0} ξ_n/n² ]
  κ_forced_lower = (L²/(4π²)) · Σ_{j>N} 1/j²   (forced lattice zeros |j|>N)
Reference scale: Σ_γ 1/γ² over zeta zeros ≈ 0.0231 (report κ/0.0231 descriptively).
Also report the bracket [·] itself and its relative cancellation (bracket·12).

Frozen rule for `P_CURVATURE_SOURCE_1` on the schedule m = N ∈ {13,23,43,83,163}:
- CONFIRMED: κ_m > 0 for every m and max κ_m / min κ_m ≤ 2 over the schedule.
- REFUTED: κ_m grows monotonically with κ_163/κ_13 ≥ 10, or κ_m < 0 for some m
  (a negative κ contradicts the real-zero product and is a STOP: `KAPPA_NEGATIVE`).
- else UNRESOLVED. N-check pairs are descriptive.

## AMENDMENT 2 (2026-09-03 12:25, after the first ledger checkpoint m ∈ {13,23,43}) — HF/FD stop is Probe-2-local; Probe 2 finding recorded

Observed (checkpoint cells, 120 and 240 dps identical to 8 digits):
  m=13: dλ₁/dL_fd = +1.5328e-01, hf = +1.5308e-01, rel diff 1.3e-3, λ₁ = 7.9e-31
  m=23: fd = +8.6775e-02, hf = +8.6675e-02, rel diff 1.2e-3, λ₁ = 7.3e-52
  m=43: fd = +4.6464e-02, hf = +4.6436e-02, rel diff 6.0e-4, λ₁ = 1.0e-90
Reading, written before any explanation is confirmed: the derivative of λ₁ with
respect to the kernel parameter L at FIXED prime set is O(1) while λ₁ itself is
1e-31 … 1e-90. So the super-small bottom eigenvalue is a feature of the consistent
point L = log m only; detuning L by h = 1e-6·L moves λ₁ by ~1e-7. The CCM kernel
depends on L inside the entries (2(L−x)/L·cos(2πnx/L)), so this is not a pure
domain (window) variation of a fixed form, and the Fuchs/Hadamard identity is
not expected to apply to it as written. The 6-significant-digit FD/HF agreement
demanded above was unattainable by construction: both estimates carry O(h²·λ'''/λ')
truncation error, and λ''' is huge relative to λ' on a function that changes by
30 orders of magnitude across the schedule.
Rules, amended:
- `HF_FD_MISMATCH` is a Probe-2-only flag; it no longer stops Probes 3 and 4.
- Probe 2 verdict is taken from the SIGN and stability rule as frozen: the
  observed sign of dλ₁/dL is POSITIVE at every checkpoint cell, hence
  c_m = −(dλ₁/dL)/edge² < 0 and `P_FUCHS_IDENTITY_NUMERICALLY_HOLDS` scores
  REFUTED on this variation (fixed primes, kernel parameter L). This does not
  test the domain-only variation of the continuous form Q_W^a; that remains a
  question for the judge (Q9-1).
- Thresholds for Probes 1, 3, 4 are unchanged.

## ADDENDUM 3 (2026-09-03 13:15, after verdict 0c0a2b37, before any spectral decomposition of ℓ_N was computed) — Probe 5, does the dual annihilator pay the absolute gap?

Judge falsifier `P59_CURVATURE_DUAL_CERT_REOPENS_ABSOLUTE_GAP`: "every proposed dual
certificate first bounds an inverse by 1/(λ₂−λ₁)". Attack R1 seeks u with
ℓ_N − c·e_0 = (K − λ₁)*u + s. The minimal-norm exact solution on ξ⊥ is
u = Σ_{j≥2} ⟨ℓ_N, v_j⟩/(λ_j − λ₁) · v_j (even-sector eigenbasis v_j, λ_j ascending).
Definitions per cell (even block, unit eigenvectors, arb):
  a_j := ⟨ℓ_N, v_j⟩ for j = 1..min(6, dim);  ℓ_N = e_0/12 + Σ_{n≠0} e_n/(2π² n²) in the
  same even-basis coordinates as ξ (respect the √2 scaling of n = 0);
  w_j := a_j/(λ_j − λ₁) for j ≥ 2;  ‖u‖² = Σ_{j≥2} w_j²;
  gap_share := w_2² / ‖u‖²;   pay := ‖u‖·(λ₂−λ₁)/‖P⊥ℓ_N‖  (∈ (0,1]; 1 = all mass on v₂).
  Also a_1/ξ_0 (must reproduce 2κ/L², sanity), and a_2/v_{2,0}.
Prediction (K6, registered here): `P_DUAL_CERT_PAYS_GAP` p=0.75 — on the schedule
m = N ∈ {13,23,43,83} the minimal-norm certificate is dominated by the second
eigenpair: gap_share ≥ 0.5 at every cell.
- CONFIRMED: gap_share ≥ 0.5 at every cell of the schedule → R1 in its minimal-norm form
  pays 1/(λ₂−λ₁); move to R2 (Schur–Stieltjes) per the judge's ordered rule.
- REFUTED: gap_share ≤ 0.05 at every cell (the functional nearly annihilates v₂ as well;
  a bounded certificate is not excluded by the spectrum).
- else UNRESOLVED. m = 163 excluded (no full spectrum); descriptive only if computed.
Needs the full even spectrum for m ≤ 83 (dims ≤ 84, acb_mat.eig already used by the
builder). DIAGNOSTIC_NEVER_A_PROOF.

## ADDENDUM 4 (2026-09-03 13:22, after Probe 5 CONFIRMED, before any Schur-pairing residue was computed) — Probe 6, sign structure of the center Schur pairing (attack R2)

Judge attack R2: split the even block at the central coordinate, K = [[a, bᵀ],[b, D]],
ξ = ξ_0·(1, −(D − λ₁)⁻¹ b). Then ℓ_N(ξ)/ξ_0 = 1/12 − ⟨c, (D − λ₁)⁻¹ b⟩ with c the
n≠0 part of ℓ_N (c_n = 1/(2π² n²)) in the same even-basis coordinates. The two-order
cancellation is 1/12 − ⟨c,(D−λ₁)⁻¹b⟩ = O(L⁻²). Judge's decisive gate for R2: one-sign
residues or exact pole-zero interlacing of the scalar function
f(z) = ⟨c, (D − z)⁻¹ b⟩ = Σ_j r_j/(μ_j − z), r_j = ⟨c, w_j⟩⟨w_j, b⟩ (eigenpairs (μ_j, w_j) of D).
Definitions per cell (m = N ∈ {13,23,43,83}, arb, same basis mapping as Probe 5):
  r_j for all j; S_+ = Σ_{r_j>0} r_j, S_− = Σ_{r_j<0} |r_j|; minority_mass = min(S_+,S_−)/(S_+ + S_−);
  f(λ₁) and the cancellation digits: 1/12 − f(λ₁) vs 2κ/L² (sanity, must match Probe 5's a_1/ξ_0);
  interlacing check: number of sign changes of f on (μ_j, μ_{j+1}) between consecutive poles.
Prediction (K6, registered here): `P_SCHUR_RESIDUES_ONE_SIGN` p=0.35 (i.e. I expect mixed signs).
- CONFIRMED (one sign): at every cell minority_mass ≤ 1e-6 → f is a Stieltjes-type function
  on this cell; R2's sign gate is numerically open.
- REFUTED: at every cell minority_mass ≥ 0.05 → no one-sign structure; R2 needs a different
  identity (interlacing or exact Loewner inverse), not positivity.
- else UNRESOLVED. Also descriptive: the Loewner structure of the off-diagonal entries
  τ_{ij} = (b_i − b_j)/(i − j) (CCM Lemma 5.1) — report whether the sequence b_i is monotone
  on 1..N at each cell. DIAGNOSTIC_NEVER_A_PROOF.

## AMENDMENT 5 (2026-09-03 13:48, before any m=163 Probe 3/4 value existed) — working precision for single-900-dps cells

The m=163 cell exists only at 900 dps (inverse iteration). Running the Probe 3 quadrature
and the Probe 4 functional at 900 dps is not required by any threshold: the quadrature
acceptance is 1e-8 relative on grid doubling, and κ needs the ground row to ~1e-12 relative.
Rule: for cells whose only record is above 300 dps, Probes 3 and 4 run at 240 dps working
precision on the ball-rounded row; the report records `working_dps=240 (record 900)`.
Thresholds unchanged. This is a cost decision, not a data decision.

## AMENDMENT 6 (2026-09-03 15:00, before any m=163 Probe 3 value existed) — quadrature tolerance and progress reporting

The piecewise `acb.integral` in Probe 3 was integrating every piece to 10^-(dps+5) (245 digits
at 240 dps) while the verdict consumes a 1e-8 relative grid-doubling change. Rule: each piece is
integrated to 10^-40 (env `EDGE_LEDGER_QUAD_TOL_DIGITS`, default 40), i.e. 32 orders beyond the
acceptance criterion. Thresholds unchanged; this is a cost decision. The script now prints one
progress line per minute (stage, pieces done/total, rate, ETA) to stderr, per the project's
Python rule; runs are launched with a log file so the observer can read progress.

## AMENDMENT 7 (2026-09-03 15:05, after the m=163 Probe 3 run crashed on 2004 pieces, before any m=163 value existed) — noise crossings

The float64 sign scan that places quadrature breakpoints found 2004 sign changes at m=163
(and hundreds at m=83) where |q_m| is super-exponentially small and the 327-term sum is pure
cancellation noise. Rule: a crossing counts only if the larger neighbour exceeds
1e-13·max|q| (env `EDGE_LEDGER_CROSSING_FLOOR_REL`); stretches below the floor contribute
at most 1e-13·max|q|·L·e^{σL/2} ≈ 3e-13·M_m, far under the 1e-8 acceptance. With the floor
the interior has no genuine sign change at any cell (q_m > 0, as the transform of a
positive Φ-like density): 2 pieces per cell. Thresholds unchanged; cost decision with a
stated error bound. Result: the m=163 cell computes in seconds instead of hours.

## ADDENDUM 8 (2026-09-03 evening, after verdict d7c7df36, before any split of S was computed) — Probe 7, which part of b carries the 1/12 cancellation

Object: `S(λ1) = ⟨c,(D−λ1)⁻¹b⟩` with `b = b_pole + b_AP` (pole part of the central coupling
column along `C_L`; Arch−Prime remainder). `S_pole`, `S_AP` as in the Codex task Part C.
Prediction (K6, observer): `P_POLE_PART_CARRIES_ONE_TWELFTH` p=0.60 — `S_pole` accounts for the
leading `1/12`: `|1/12 − S_pole| ≤ 0.5·(1/12)` at every cell m = N ∈ {13,23,43,83}, and
`|S_AP| ≤ 0.5·(1/12)`.
- CONFIRMED: both inequalities at every cell.
- REFUTED: `|S_pole| ≤ 0.1·(1/12)` at every cell (the pole part is negligible; the cancellation
  lives in the Arch−Prime part).
- else UNRESOLVED (mixed). Descriptive: `(1/12 − S_pole)·L²` per cell.
Executor: Codex (owner's numerics channel), script under `docs/routeB_bus/phase5_codex/`.
DIAGNOSTIC_NEVER_A_PROOF.

## ADDENDUM 9 (2026-09-03 night, after verdict 3dc82357, before any odd-sector number existed) — Probe 8, reciprocal-mode odd-Gram defect and the odd-sector floor

Judge's C5 (verdict 3dc82357 §6): on the noncentral modes n ≠ 0 (±N row indexing, NOT the
folded even basis), X = diag(n), R = X⁻¹, η = 1, r = Rη (r_n = 1/n, odd), β = X b,
D R − R D = b rᵀ − r bᵀ, A = (D − λ₁)⁻¹ with λ₁ the even bottom eigenvalue of K,
parity ⇒ ⟨r, A b⟩ = 0, Schur root ⟨b, A b⟩ = a₀ − λ₁, and
  κ = (L²/(4π²))·E,  E = ½‖r‖² − ⟨r, A(Rb)⟩ + (a₀ − λ₁)⟨r, A r⟩ + Σ_{n>N} 1/n².
Definitions per cell (m = N ∈ {13,23,43,83}, arb 240 dps, 360 for 83), all on the full
(2N)-dimensional noncentral block D (both parities), b the central column, a₀ = K_00:
  T1 = ½‖r‖²,  T2 = ⟨r, A(Rb)⟩,  T3 = (a₀−λ₁)⟨r, A r⟩,  T4 = Σ_{n>N} 1/n²,  E = T1 − T2 + T3 + T4;
  checks: ⟨r, A b⟩ (must be 0 to working precision), ⟨b, A b⟩ − (a₀−λ₁) (must be 0),
  commutator residual ‖DR − RD − (brᵀ − rbᵀ)‖ (must be 0 to working precision),
  sanity κ_probe4 = (L²/4π²)E to ≥ 8 digits (STOP `ODD_GRAM_SANITY_MISMATCH` otherwise);
  odd sector: smallest eigenvalue μ_odd,min of the odd block of D (and of K restricted to
  odd modes), and the even second eigenvalue λ₂ for comparison; ratio μ_odd,min/λ₂.
Predictions (K6, observer):
  `P_ODD_SECTOR_FLOOR_NONCOLLAPSING` p=0.55 — μ_odd,min(83)/μ_odd,min(13) ≥ 1e-6 (no
    super-exponential collapse in the odd sector, unlike λ₂ even: 2.8e-25 → 1.3e-154).
  `P_E_TERMS_NOT_GAP_INFLATED` p=0.50 — max(|T2|, |T3|)·L² ≤ 10 at every cell (no 1/λ₂-scale
    cancellation inside E, unlike Probe 7's split).
- CONFIRMED / REFUTED per prediction by the stated inequality at every cell; else UNRESOLVED.
Executor: observer's numerics channel. DIAGNOSTIC_NEVER_A_PROOF.

## ADDENDUM 10 (2026-09-03 21:20, before any Δ_n was computed) — Probe 9, lattice error against Ξ and the alternating curvature form

Observer's rewrite of E-CLOSED (verdict 3dc82357 §6 + agent preflight): with
f_k(x_n) := F_k(x_n)/F_k(0) = (−1)^n ξ_n/ξ_0 (exact P59 sampling, even row) and the arithmetic
identity Σ_{n≥1} (1 + 2(−1)^n)/n² = π²/6 − π²/6 = 0,
  κ_k = 2 Σ_{n=1}^{N} (−1)^n (f_k(x_n) − 1)/x_n²  −  (L²/(2π²)) Σ_{n>N} (−1)^n/n²,   x_n = 2πn/L.
Let f(x) := centeredXi(x)/centeredXi(0) (= Ξ(x)/Ξ(0) in the centered coordinate, Ξ(x) = ξ(1/2+ix)
with ξ(s) = ½ s(s−1) π^{−s/2} Γ(s/2) ζ(s)), Δ_n := f_k(x_n) − f(x_n). Then
  κ_k = 2 Σ_{n≤N} (−1)^n (f(x_n) − 1)/x_n² + 2 Σ_{n≤N} (−1)^n Δ_n/x_n² + tail,
and |2 Σ (−1)^n Δ_n/x_n²| ≤ (L²/(2π²)) Σ_{n≤N} |Δ_n|/n² ≤ (L²/12) sup_n |Δ_n|.
Definitions per cell (m = N ∈ {13,23,43,83,163}, ξ from the ledger, Ξ in arb at 60 dps):
  f_k(x_n), f(x_n), Δ_n for n = 1..N;  W_k := Σ_{n≤N} |Δ_n|/n²;  W_k·L²;  sup_n |Δ_n|·L²;
  S_Ξ := 2 Σ_{n≤N} (−1)^n (f(x_n) − 1)/x_n² (the Ξ-part) and the check κ_k = S_Ξ + S_Δ + tail to ≥ 8 digits
  (STOP `ALTERNATING_FORM_MISMATCH` otherwise); also the reference κ_Ξ := −Ξ''(0)/(2Ξ(0)) in arb.
Predictions (K6, observer):
  `P_WEIGHTED_LATTICE_ERROR_POLYLOG` p=0.65 — W_k·L² ≤ 10 at every cell (weighted lattice
    error already at the 1/L² scale on the production schedule).
  `P_SUP_LATTICE_ERROR_POLYLOG` p=0.45 — sup_{n≤N}|Δ_n|·L² ≤ 10 at every cell.
- CONFIRMED / REFUTED per prediction by the inequality at every cell; else UNRESOLVED.
DIAGNOSTIC_NEVER_A_PROOF.

## ADDENDUM 11 (2026-09-04 00:50, before any lattice-equation term was computed) — Probe 10, normalized-ξ lattice equation: identities, term sizes, diagonal defect

Source: agent preflight `docs/routeB_bus/AGENT_REPORT_2026-09-04_GOAL058_NORMALIZED_XI_LATTICE_EIGEN_EQUATION_PREFLIGHT.md`
(code `P59_XI_LATTICE_EQUATION_REIMPORTS_DENSE_TAIL_OR_GAP`; §3 identities LATTICE-1/2/3, §6 remainder
ρ_n(n₀), §7 new object `P59_ARCH_PRIME_DIAGONAL_DEFECT_NONDEGENERACY`, §8 S6 prediction, §9 measurement list).
Objects per cell (m = N ∈ {13,23,43,83,163}; unmodified `CCMArbBuilder` + parity_blocks; ground pair from
the ledger or one precond solve; y = ξ/ξ_0; n = 1..8; cuts n₀ ∈ {⌊L⌋, ⌊L²⌋}):
  (i)  residuals of LATTICE-1 and LATTICE-2 (must vanish to working precision; STOP `LATTICE_IDENTITY_MISMATCH`
       if any residual exceeds 1e-30 relative);
  (ii) the four terms of LATTICE-2 separately: D_n y_n, κ_n Ŝ, √2[W_ℝ(0,0)+Prime(0,0)+a_n+λ₁], Ω_n^{ap},
       with Ω_n^{ap} split at n₀ into head and tail ρ_n(n₀);
  (iii) ratios |ρ_n(n₀)|/|D_n y_n| and |κ_n Ŝ|/|D_n y_n|;
  (iv) min_{n≤8} |D_n| and its trend in L;  (v) Ŝ against −1/(√2 L²);  (vi) Σ_{j>n₀}|y_j|/j², Σ_{j>n₀} y_j/j²;
  (vii) x_n against −d_n/(2L²).
Predictions (K6, observer, registered before the run):
  `P_LATTICE_IDENTITIES_EXACT` p=0.90 — all LATTICE-1/2 residuals ≤ 1e-30 relative at every cell.
  `P_TAIL_COUPLING_IS_LEADING` p=0.60 — |ρ_n(⌊L⌋)|/|D_n y_n| ≥ 1 for n = 1..3 at every cell
    (the j>n₀ coupling is not a remainder but the leading term: the equation is a fixed point, as the preflight says).
  `P_DIAGONAL_DEFECT_NONDEGENERATE` p=0.60 — min_{n≤8}|D_n| / max_{n≤8}|D_n| ≥ 1e-3 at every cell and does
    not decrease by more than a factor 10 between m=13 and m=163 (the new object is not collapsing).
  `P_SHAT_SHARP` p=0.50 — |Ŝ + 1/(√2 L²)| ≤ 0.5·|1/(√2 L²)| at every cell (agent's S6 prediction).
- CONFIRMED / REFUTED per prediction by the inequality at every cell; else UNRESOLVED.
Executor: observer's numerics channel (Opus agent), new script `docs/routeB_bus/phase5_codex/lattice_equation.py`,
output `phase5_codex/out/lattice_equation.{json,md}`, registered in TOOLS.yaml. DIAGNOSTIC_NEVER_A_PROOF.

## ADDENDUM 12 (2026-09-04 02:20, before any odd-block entry, q_ap or ρ_stab was computed) — Probe 11, odd-sector floor scale and the S7 cancellation

Source: energy preflight `docs/routeB_bus/AGENT_REPORT_2026-09-04_GOAL058_RECIPROCAL_MODE_XI_LATTICE_ENERGY_SOURCE_PREFLIGHT.md`
(§3.3 identity MAIN/MAIN-P; §5 contraction: `q_ap = ‖diag(D)⁻¹ Off^{ap}‖`, `q_pole`; §9 measurement list; §10 S7/S8).
Objects per cell (m = N ∈ {13,23,43,83,163}; unmodified builder + parity_blocks; y = Ξ-sample row; Δ = x − y; n ≤ 8):
  (i)   residual of (MAIN) and (MAIN-P) to working precision (STOP `ENERGY_IDENTITY_MISMATCH` if > 1e-30 rel);
  (ii)  odd-block entries `D^odd_{nm} = (D−λ₁)|_odd` for n,m ≤ 8: diagonal δ_n and off-diagonal, especially `D^odd_{12}`;
        pole part of `D^odd_{12}` separately (S7 distinguishing measurement);
  (iii) `min_n δ_n`, `λ_min((D−λ₁)|_odd)` on the 8×8 and on the full block (arb eig, DIAGNOSTIC);
  (iv)  `q_ap = ‖diag(D)⁻¹ Off^{ap}‖₂`, `q_pole`, and the stability ratio `ρ_stab = ‖RΔ‖ / ‖R𝓡(y)‖`;
  (v)   `b_n` for n ≤ 8: relative variation `max_{n≤8}|b_n − b_1|/|b_1|`.
Predictions (K6, observer, registered before the run):
  `P_ENERGY_IDENTITY_EXACT` p=0.90 — (MAIN) residual ≤ 1e-30 relative at every cell.
  `P_S7_ODD_OFFDIAG_SMALL` p=0.55 — |D^odd_{12}| ≤ 1e-3 at every cell while its pole part alone is O(1) (reading A of S7).
  `P_ODD_FLOOR_FLAT` p=0.45 — λ_min((D−λ₁)|_odd, full block)·L² ∈ [1e-4, 1e-1] at every cell (polylog, not collapsing).
  `P_Q_AP_LT_1` p=0.35 — q_ap < 1 at every cell.
  `P_RHO_STAB_FLAT` p=0.50 — ρ_stab ≤ 1e4 at every cell and varies by < ×10 across the schedule.
- CONFIRMED / REFUTED per prediction by the inequality at every cell; else UNRESOLVED.
Executor: Opus agent; new script `docs/routeB_bus/phase5_codex/odd_floor.py`, output `phase5_codex/out/odd_floor.{json,md}`,
registered in TOOLS.yaml by the ORCHESTRATOR after the run (agents do not edit the registry, lesson 2026-09-04). DIAGNOSTIC_NEVER_A_PROOF.
