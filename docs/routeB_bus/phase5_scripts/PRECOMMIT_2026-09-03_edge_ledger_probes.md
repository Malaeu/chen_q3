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
