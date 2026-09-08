# Near-null probe of the Sonin square and the scalar floor (Theorem 1, SCALARFLOOR) — 2026-09-08

Status: DIAGNOSTIC_NEVER_A_PROOF. Floating point on the existing Euler-Gram grids (k₂ lower/upper bounds from
`phase5_codex/euler_gram/out/k2_G.npz`, ℓ₂ from `phase5_codex/mellin_d2/d_two.npz`), |ĝ_k|² evaluated with mpmath.
Owner's «go» on the VOI probe: before scanning the four pole gauges on the plus channel, test whether the Sonin square
of Theorem 1 vanishes on the unconditional near-null family of ALIGN (A22)–(A28), g_k = (∂²−¼)∂^kΦ, |ĝ_k(ξ)|² =
ξ^{2k}(ξ²+¼)²Ξ(ξ)², Q(g_k) = 0, pole moments 0.

## Instrument
𝔪(v) = L₂(v) − n₂(v), L₂(v) = (1/2π)∫|v̂|²q₂ (the {∞,2}-semilocal form: q₂ = q_∞ − 2a Σ_j r^j cos(jaξ)), n₂(v) = ∫|v̂|²k₂
(the Sonin square ‖T_vS₂‖²), scalar floor Q_sc = 𝓕 = −∫|v̂|²ℓ₂, HS square ‖T_vD₂‖² = 𝔪 − 𝓕 (Theorem 1). The pole gauges
act only through pole terms, so on pole-null tests every number below is gauge-invariant.

## Numbers (per unit ‖g‖²; k₂ ≥ k₂^lo gives 𝔪 ≤ 𝔪_up)
| k | L₂ (semilocal {2} form) | n₂ (Sonin square) | 𝔪 = L₂ − n₂ | 𝓕 = Q_sc | HS square 𝔪 − 𝓕 | full Q | Π/‖g‖² | 𝒟/‖g‖² |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 0 | +0.0790 | +0.0025 | +0.0765 | −0.4081 | +0.4845 | −1.6e−16 | −0.017 | 5.355 |
| 1 | −0.0450 | +0.0071 | −0.0521 | −0.6878 | +0.6357 | 0 | +0.165 | 5.537 |
| 2 | −0.1348 | +0.0172 | −0.1519 | −0.9159 | +0.7640 | −5.6e−17 | +0.289 | 5.661 |
| 3 | −0.1001 | +0.0375 | −0.1375 | −0.9759 | +0.8383 | −6.1e−16 | +0.387 | 5.759 |
Reference, plus channel v₊ at T = 120 (EULER_GRAM report): 𝔪 = −0.0080, 𝓕 = −0.0591, HS square = +0.0491.
The instrument reproduces Q(g_k) = 0 to 1e−16 (archimedean by q_∞, primes by the correlations), the same as the
ALIGN checker's two channels.

## Readings
1. **The Sonin square does not annihilate the near-null tests.** n₂(g_k) = 0.0025 … 0.037 > 0 and growing with k
   (k₂ ≥ 0 is a density; it cannot vanish where Ξ ≠ 0). On the full form Q(g_k) = 0, so any reservoir minorant of the
   shape Q ≥ ‖T_vS_S‖² with a FINITE prime set S fails on g_k by exactly n_S(g_k) > 0. This is unconditional and
   explicit; the plus-channel −0.008 is the same phenomenon seen on a narrower test (T·|𝔪| ≈ 1 as T grows: the
   plus-channel tests approach null directions while the finite-S square stays positive).
2. **The scalar floor is not slightly negative, it is negative by O(1).** 𝓕(g_k) = −0.41 … −0.98 per unit norm,
   paid back by an HS square of +0.48 … +0.84. The identity 𝔪 = 𝓕 + ‖T_vD₂‖² holds; the mechanism «𝓕 ≥ 0» is dead on
   the full class, not by a gauge defect (gauge-invariant here) but by structure.
3. **ЕСЛИ_B.** The four-gauge scan of the plus channel is cancelled. Reopening SCALARFLOOR/GAUGE on the plus channel
   cannot yield the all-n mechanism.
4. **The constructive requirement, sharpened.** A representation Q = ‖Xf‖² + R with R ≥ 0 on all pole-null tests must
   have X g_k = 0 for every k, i.e. ker X ⊇ {f : f̂ divisible by Ξ}. A square built from a finite prime set S sees no
   zeros and cannot have this kernel; the square must be built from ξ itself (the full Euler product or the zero
   ideal). This is the exact reason every finite-S reservoir (SCALARFLOOR, GAUGE, the semilocal Sonin space) can only
   close windows below the first missing prime and never all n. Under RH the zero-side Gram Σ_ρ|f̂(γ_ρ)|² is such an X;
   a primes-side X with the same kernel is the object the atom asks for.
5. Side fact: the {∞,2}-semilocal form L₂ is negative on g₁, g₂, g₃ (wide tests; the missing primes ≥ 3 carry the
   compensation). No theorem is contradicted; semilocal positivity holds only on windows.
