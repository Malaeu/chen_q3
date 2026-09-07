# Six-centre fixed-width assembly of the Weil form — the first offset geometry and the fixed-width curve (2026-09-07)

Status: DIAGNOSTIC_NEVER_A_PROOF. Floating point (numpy/scipy), not arb. Script and raw outputs:
`docs/routeB_bus/phase5_codex/six_centre/sc_build.py`, `docs/routeB_bus/phase5_codex/six_centre/out/*.json`.

## What was assembled
The form (C1) = Arch + Prime + Pole on the class v = Σ_i U_{x_i} h_i, centres x = {0} ∪ {log p : p ≤ P},
profiles h_i = Legendre polynomials P_k(x/δ), k < K, on the FULL allowed width (−δ, δ), δ = (log 3 − log 2)/8,
ℓ = 2δ = 0.10137. Both total pole moments imposed (M_c = M_s = 0). Archimedean part by the Fourier symbol
Ω(ξ) = Re ψ(¼ + iξ/2) − log π (independent of the spatial three_lobe route); prime part EXACT (polynomial
overlaps, every active prime power incl. 4, 8, 9, 16, 25; every pair of centres; both shift signs); pole part
by quadrature. Gauge: three lobes, K = 6, reproduce the INVARIANT checker's class floor 0.96635 (18 dims:
0.966348) and the exact mean-sector prime value log(4/3)/6 = 0.0479470120752968 to 15 digits; the pole term
vanishes on the constraint kernel to 1e−17. Convergence: h = 0.01, Ξ = 40000 changes the six-centre floor by
3e−7; K = 4 → 6 changes it by 2.4e−4.

## The fixed-width curve (K = 4)
| centres | P | class floor (per unit ‖f‖²) | unconstrained min | mean-sector Q floor | most adverse PRIME direction on the mean kernel (per unit norm) |
|---:|---:|---:|---:|---:|---:|
| 3 | 3 | 0.9663 | 0.392 | 1.045 | +0.0479 (= log(4/3)/6) |
| 4 | 5 | 0.9290 | 0.265 | 1.007 | −0.0027 |
| 5 | 7 | 0.7088 | 0.173 | 0.992 | −0.0070 |
| 6 | 11 | 0.5366 | 0.140 | 0.897 | −0.0264 |
| 7 | 13 | 0.4320 | 0.094 | 0.813 | −0.121 |
| 8 | 17 | 0.3316 | 0.077 | 0.724 | −0.184 |
| 10 | 23 | 0.1844 | 0.043 | 0.615 | −0.219 |
| 12 | 31 | 0.1397 | 0.039 | 0.478 | −0.366 |
| 14 | 41 | 0.1104 | 0.027 | 0.406 | −0.587 |
| 16 | 47 | 0.0727 | 0.020 | 0.375 | −0.630 |

Readings.
1. The class floor is POSITIVE at every P tested and DECAYS toward 0⁺ as primes accumulate at fixed width.
   No uniform constant c > 0 exists for the fixed-width class as P → ∞ (the data, not a theorem). This is the
   owner's objection («логов до бесконечности») made numerical: a fixed-geometry class theorem, however many
   centres, is not the all-n mechanism.
2. Under RH the floor can never be negative (Weil criterion); the curve flattens accordingly (0.184 → 0.140 →
   0.110 → 0.073 for P = 23, 31, 41, 47). A negative value would have been a bug, not a discovery.
3. The mean sector decays too (1.045 → 0.375), driven by the adverse prime direction of INVARIANT (19):
   +0.048 at three lobes, sign change at four (as INVARIANT (21)–(24) predicted), −0.63 at P = 47.
   The archimedean value on that direction stays ≈ 1.0–1.2 per unit norm (𝒟 ≈ 6.3, c_A = 5.37).
4. The OFFSET blocks (first at log 11: 5↔11 via 2, 3↔11 via 4, 2↔11 via 5 — exactly these three, as the
   INVARIANT checker enumerated) are SMALL and here FAVOURABLE: six-centre floor 0.5366 with offsets vs 0.5220
   without (+2.8%); adverse prime direction −0.0264 vs −0.0189.
5. THE SCALAR COMPENSATION (35) OF INVARIANT IS DEAD FROM FOUR CENTRES ON. Test: with B⁺ = 𝒟 + 2|M_c|²,
   A⁻ = −c_A‖·‖² − primes − 2|M_s|² (INVARIANT (34)), a common δ with A⁻ ⪰ −δG and B⁺ ⪰ δG exists iff
   λ_min(B⁺, G) ≥ λ_max(−A⁻, G) on the constraint kernel:
   | centres | λ_min(B⁺) | λ_max(−A⁻) | (35) |
   |---:|---:|---:|---|
   | 3 | 6.292 | 6.174 | holds (2% margin) |
   | 4 | 6.225 | 6.449 | FAILS |
   | 6 | 6.179 | 6.943 | FAILS |
   | 10 | 5.958 | 7.425 | FAILS |
   | 16 | 5.443 | 7.890 | FAILS |
   Q itself stays positive, so the RELATIVE domination B⁺ ⪰ −A⁻ holds trivially; what dies is the Gram-relative
   scalar form with one constant per n — the form INVARIANT wrote in (35). This is the discriminator INVARIANT
   §6.3 itself specified («a negative upper witness for the proposed residual refutes that mechanism»).

## What this closes and opens
CLOSES (diagnostically): the fixed-width road as a source of a uniform constant; the scalar (35) as the all-n
compensation. OPENS nothing new: the object that must carry the all-n sign is the same as before — a
source-defined representation whose positive part grows with the support (owner's rule 18: B₀ + ΣC_k, C_k ⪰ 0).
Consumer: REQ-2026-09-07-COMPENSATE, delivered as an addendum.

## Verification debt
Floating point throughout; the qualitative statements (positivity, decay, (35) failure with gaps ≥ 0.22) are far
above the numerical error (≤ 1e−6 on floors), but nothing here is an enclosure. Legendre profiles have jumps at
±δ: they lie in the form domain (𝒟 finite: ∫A(t)·t dt converges) but not in C_c^∞; the floors are those of the
closure of the class. A finite-subspace minimum is an UPPER bound on the class infimum; the K = 4 → 6 change
(2.4e−4) indicates convergence.
