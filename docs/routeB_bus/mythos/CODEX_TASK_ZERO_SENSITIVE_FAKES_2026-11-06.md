# CODEX TASK — zero-sensitive fakes: addition vs multiplication — 2026-11-06

Repo: https://github.com/Malaeu/chen_q3 · branch `rh_clean`
Predecessor: commit `67268da714e31a903e6653781cd39ff569c5150b`,
`docs/routeB_bus/diag/PRIME_PROPERTY_ABLATION_2026-11-06/` (reuse its sieve, Kahan W, grids, analyze/verify scripts).
Dictionary: `claude`-mirror blob `8462d827e01dd83fef22f750936f3d84ad238e1d` (prime properties vs zeros).
Output dir: `docs/routeB_bus/diag/ZERO_SENSITIVE_FAKES_2026-11-06/`

## Why

The ablation fakes S1–S3 were not RH-false by design, so they could not tell whether exact integer structure
(addition × multiplication, "block B") is what separates the true system from RH-false systems.
Known landscape:
- Diamond–Montgomery–Vorhauer: Beurling systems with N(x)=ρx+O(x^θ), any θ∈(1/2,1), RH false.
- Hilberdink: every [α,β]-system has max{α,β} ≥ 1/2; no unconditional system with β<1/2 is known
  (Broucke–Debruyne–Révész, arXiv 2309.01567). True integers: β=0.
- Davenport–Heilbronn: functional equation (additive/modular structure mod 5) but no Euler product, zeros off the line.

This run builds one world per side: multiplication without ℤ, addition without multiplication, and two true worlds,
and asks which finite probes see a planted off-line zero first.

## Systems (coefficient sequence b, Mertens-type sum M_b(x)=Σ_{n≤x} b(n))

| ID | Definition | Euler product | exact ℤ / modularity | RH status |
|---|---|---|---|---|
| T0 | μ(n) (reuse S0) | yes | yes | RH-world |
| T1 | μ(n)χ₄(n), χ₄ the non-principal character mod 4 | yes | yes | GRH-world |
| T2 | Dirichlet inverse of τ(n)/n^{11/2} (Ramanujan τ, Δ weight 12) | yes (degree 2) | yes (SL₂(ℤ)) | GRH-world |
| F1 | Dirichlet inverse of DH coefficients a(n): a≡1:1, a≡2:κ, a≡3:−κ, a≡4:−1, a≡0:0 (mod 5), κ=(√(10−2√5)−2)/(√5−1)=0.284079043840412… | no | yes (functional equation) | false |
| F2(a) | Beurling generalized primes p_k = min{x : Π_a(x) ≥ k}, Π_a(x)=Li(x) − 2a·Re Li(x^{ρ₀}), ρ₀=0.75+10i; generalized integers with multiplicity; b=μ_F | yes | no | false for a>0 |
| F3(a) | F2(a) generators rounded to nearest integer, products as integer multiset (collisions add multiplicity and μ, as in the ablation) | yes | integers, not ℕ | false for a>0 (expected) |

Amplitudes a ∈ {0, 0.05, 0.2}. a=0 is the control fake (same construction, nothing planted).
Check positivity of the target density on the whole range and record it.

Ranges: T0, T1 to 10⁸; T2, F1 to 10⁷ (state memory/time); F2, F3 to 10⁷.

## Measurements per system

1. W(X) = (1/log X)∫₁^X M_b(t)²/t² dt, exact step integration with Kahan (as in the ablation), log grid 100/decade, OLS slope on [10³,Xmax].
   For T2 and F1 also report the same with M_b normalized by the natural scale if the raw slope is dominated by a constant bias; state which.
2. Block-B probes (only where defined):
   - P1 counting: N(x) − ρ̂x over √x and over x^{0.75}, with ρ̂ fixed from [10⁴,10⁵] (not endpoint-fit). F2, F3.
   - P2 residues: generators mod 3, 4, 5, 6 — imbalance normalized by √(count). F3 (and T0 reference).
   - P3 unit shift: Σ_{n≤x} b(n)b(n+1)/x and fraction of n with both n, n+1 in the support. Integer-supported systems T0, T1, T2, F1, F3.
   - P4 ℕ-deviation for F3: missing integers and multiplicity excess up to x, normalized.
   - P5 multiplicativity defect for F1: mean |a(mn) − a(m)a(n)| over coprime pairs up to x.
3. Detection time. For each probe and for W: the smallest X_det at which F2(0.05) [resp. F3(0.05)] differs from a=0 by >5 noise units, where noise is estimated from a=0 over shifted windows (preregister the noise rule).

## Judges (run before production)

- J1: F1 — mpmath confirms zeros of the DH function at 0.808517182456637…+85.699348485377592…i and
  0.650830080609737…+114.163342730756980…i (|f|<1e−20 after findroot). T2 — τ(n) for n≤30 against OEIS A000594.
- J2: T0 reproduces the ablation's M(10ᵏ) and W at 10⁷ to all printed digits; T1 M(10ᵏ) cross-checked by independent trial factorization to 5·10⁴.
- J3: F2(0) vs F2(0.2): the analytic leading term of W for the planted case is computed before running (as in the ablation planted control) and the measured slope on [10⁵,10⁷] lies within the preregistered band.
- J4: For F3 independent brute-force enumeration to 500 matches the C++ enumeration (multiplicities, μ).

## Preregistration

Commit and push PREREGISTRATION.json (noise rule, bands, thresholds, X_det definition, file list) before any production run.

Owner predictions registered by Mythos before sending:
- B1: T1 and T2 have max W ≤ 1 on the grid and slope ≤ 0.1 — 0.75
- B2: F2(0.2) W slope ≥ 0.3 — 0.85
- B3: some block-B probe detects F3(0.05) vs F3(0) at X_det at least 10× smaller than W does — 0.35
- B4: F1 W slope ≥ 0.3 — 0.8
- B5: T2 W within a factor 5 of T0 W at common X — 0.5

## Deliverables

REPORT.md (verdicts B1–B5 HIT/MISS by the preregistered criteria, X_det table probe × system, all W curves on one plot,
probe plots), CSV per system, scripts, ANALYSIS.json, ARTIFACT_BLOBS.json, independent REVIEW.md.
Commit and push to `rh_clean`; update docs/Codex/NEXT.md.
