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
