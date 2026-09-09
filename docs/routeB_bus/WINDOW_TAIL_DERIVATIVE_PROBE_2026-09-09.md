# Window floor vs theta tail: λ_a falls like the SQUARE of the tail mass (2026-09-09, owner's «Ok go»)

Status: DIAGNOSTIC_NEVER_A_PROOF, floating point. Tool: `phase5_codex/six_centre/window_derivative.py` (single centre 0,
half-width a, Legendre degrees < K, full Weil form Q = Arch + primes + pole, Gram G; λ_a = min generalised eigenvalue).
Raw: `phase5_codex/six_centre/out/window_derivative_K{24,36,48}.json`. Follows WINDOW_GROUND_STATE_PROBE_2026-09-08 (its
«cheapest next probe»). Bug fixed on the way: the theta series Φ evaluated at negative arguments with 8 terms is garbage
(needs ~e^{−x} terms); Φ is even, so Φ(|x|) is used — first run's tail mass 0.78 was that bug.

Objects. Φ(x) = Σ_n (2π²n⁴e^{9x/2} − 3πn²e^{5x/2}) e^{−πn²e^{2x}} (Titchmarsh 10.1), F_Φ(it) = Ξ(t), Q[Φ] = 0.
T(a) = ∫_{|x|>a}Φ² / ∫Φ² (relative tail mass); R(a) = Q[Φ·1_{(−a,a)}]/‖Φ·1_{(−a,a)}‖² (Rayleigh of the cut null test).

## Numbers (K = 36; K = 24 agrees to 3 digits for a ≤ 0.65)
| a | λ₁ | λ₁ (K=24) | T | T² | λ₁/T² | R/T | 1 − overlap² (ground, cut Φ) | λ₂/λ₁ | active atoms |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| 0.35 | 1.194e−3 | 1.195e−3 | 2.363e−2 | 5.58e−4 | 2.14 | 1.02 | 2.8e−2 | 55 | 2 |
| 0.40 | 1.816e−4 | 1.821e−4 | 9.025e−3 | 8.15e−5 | 2.23 | 1.03 | 2.6e−2 | 81 | 2 |
| 0.45 | 1.622e−5 | 1.630e−5 | 2.992e−3 | 8.95e−6 | 1.81 | 0.97 | 2.2e−2 | 149 | 2 |
| 0.50 | 9.38e−7 | 9.45e−7 | 8.486e−4 | 7.20e−7 | 1.30 | 0.83 | 1.8e−2 | 208 | 2 |
| 0.55 | 5.37e−8 | 5.43e−8 | 2.026e−4 | 4.10e−8 | 1.31 | 1.35 | 1.4e−2 | 268 | 2,3 |
| 0.60 | 1.64e−9 | 1.81e−9 | 3.998e−5 | 1.60e−9 | 1.03 | 1.38 | 1.1e−2 | 369 | 2,3 |
| 0.65 | 4.06e−11 | 4.31e−11 | 6.397e−6 | 4.09e−11 | 0.99 | 1.31 | 8.6e−3 | 463 | 2,3 |
| 0.70 | 4.37e−13 | 3.99e−12 (K-limited) | 8.118e−7 | 6.59e−13 | 0.66 | 1.58 | 6.8e−3 | 628 | 2,3,4 |
| 0.75 | 3.87e−15 | 2.68e−13 (K-limited) | 7.975e−8 | 6.36e−15 | 0.61 | 1.47 | 5.3e−3 | 959 | 2,3,4 |
| 0.80 | −4e−16 (roundoff) | 2.7e−14 (K-limited) | 5.905e−9 | 3.49e−17 | — | 1.50 | 4.1e−3 | — | 2,3,4 |

Log-derivatives (finite differences, K = 36): d log λ₁/da ≈ 2 × d log T/da on the whole resolvable range —
(−37.7, −48.3, −57.0, −57.2, −69.8, −74.0, −90.7, −94.5) against (−19.2, −22.1, −25.2, −28.6, −32.5, −36.7, −41.3, −46.4);
d log R/da tracks d log T/da (−19.1 … −51.6). Least squares on a ∈ [0.35, 0.70]: log λ₁ = 2.11·log T + 1.22;
with a linear term: 2.09·log T − 0.84·a + 1.43. The prefactor c = λ₁/T² drifts 2.2 → 0.6 (polynomial-scale, not exponential).

## Readings
1. **ЕСЛИ_B, and sharper than either branch anticipated.** The window floor is NOT «how much of Φ sticks out»
   (that is R ≈ T, the cut-off theta test). The window finds a better combination: the first-order tail cancels and
   **λ_a ≍ T(a)²** up to a slowly varying factor — the exponent of the double exponential DOUBLES.
   [CORRECTED 09.09 after DISTANCE (D15), verified numerically: T(a) ~ (2π³/I)e^{7a}e^{−2πe^{2a}} (ratio 0.86 → 0.95 on
   a = 0.5 → 1.0), so T² ~ e^{−4πe^{2a}}. The first version of this line wrote e^{−2πe^{2a}} for T², inheriting the 08.09
   probe's wrong «e^{−πe^{2a}}» for T; Φ² ~ e^{9x}e^{−2πe^{2x}}.] The ground vector stays 99–99.9 % cut-off Φ (overlap 0.986 → 0.998); the correction is small in
   norm but removes the whole first-order energy.
2. **Exact reformulation behind the number (observer's; unconditional for w in the (K16) class, see caveat).** Write
   Φ = v_in + v_out with v_in = Φ·1_{(−a,a)}, v_out = Φ·1_{|x|>a}. F_Φ vanishes at every zero (F_Φ = ξ(½+z)), so by the
   signed explicit formula (K16) Q(Φ, w) = 0 for every admissible w — with or without RH. For f in the window space W,
   put w = v_in − f ∈ W; then Q[f] = Q[v_in − w] = Q[Φ − v_out − w] = Q[v_out + w] (the cross terms with Φ vanish), hence
     **λ_a = min_{w∈W} Q[v_out + w] / ‖v_in − w‖²  — the window floor is the Q-distance² of the theta TAIL to the window
     (W is linear, so the sign of w is immaterial for the distance), normalised by the cut mass.**
   Under RH, Q ⪰ 0 and this is a genuine (semi)distance; the finding says W approximates the tail in Q-metric to
   relative error ~√T: Q[v_out] ≈ T·‖Φ‖² (R/T ≈ 1–1.5 confirms) and min_w Q[v_out − w] ≈ c·T²·‖Φ‖². Under ¬RH the
   minimum is −∞ for large a (SCREW dichotomy), consistent. This is the rule-15 object: an explicitly computable,
   positive-by-construction part (a Q-distance) plus nothing hidden — the sign question «λ_a > 0 ∀a» becomes
   «v_out ∉ Q-closure(W) for every a», and «λ_∞ = 0 under RH» becomes «the tails of Φ are Q-approximable by windows».
   Caveat: (K16) is proved for C_c^∞-type tests; the Legendre windows are discontinuous at ±a, so the identity holds on
   the closure and the numerics see the projected version (the K-stability to a = 0.65 is the evidence it survives).
3. **Certification wall, recomputed.** Extrapolating c ≈ 0.61–0.66 from a = 0.70/0.75 gives λ_{0.8} ≈ 2.1–2.3e−17.
   Zhu's certified floor at a = 0.8 is 8.9e−18: **his certificate is sharp to a factor ≈ 2.5**, not loose by 5–9 orders
   as the 08.09 estimate (T ≈ 6e−9) suggested. And L = 1.19 would need λ ~ T² ~ e^{−4π e^{2.38}} ≈ e^{−136} ≈ 10^{−59} [CORRECTED 09.09, was e^{−68}]:
   the withdrawn claim was ~450 bits away from its own floor.
4. **Numerical limits.** K = 24 is K-limited from a = 0.70 (10× off). K = 48 reproduces K = 36: 4.00e−11 vs 4.06e−11
   (a = 0.65), 4.27e−13 vs 4.37e−13 (0.70), 4.23e−15 vs 3.87e−15 (0.75, 9 %); so K = 36 is trusted to a = 0.70 and
   to ±10 % at 0.75; a = 0.80 is roundoff (−4e−16). No sign
   statement anywhere: DIAGNOSTIC_NEVER_A_PROOF.

## Consequence for the candidate (rule 19)
The «first-touch» lemma has a new exact form: λ_a > 0 ⇔ dist_Q(v_out, W_a) > 0. What is needed is a LOWER bound on
the Q-distance of the theta tail to the window — and T² is its size. Candidate (p = 0.3): the T² law is the square of
a first-order matching, i.e. there is w* ∈ W with F_{w*}(λ) = F_{v_out}(λ) + O(T) at all zeros, and the residual is
what the window cannot reach — the object to name is the Q-orthogonal complement of W in the (K16) closure. Cheapest
probe (minutes): compute the minimiser w* explicitly (it is v_in − f_ground), and test whether Q[v_out − w*] ≈ λ_a‖v_in‖²
holds on a SEPARATE build that contains the tail support (centres 0 and ±2a, same half-width a: supports (−3a,3a) contiguous), which checks the identity in reading 2
directly instead of through its consequence. ЕСЛИ_A (identity holds to 1e−6): the reformulation is the working object,
batch to Prošhka «lower-bound the Q-distance of the theta tail to the window». ЕСЛИ_B (fails): the T² law is a
Legendre artefact and reading 2 needs the (K16) closure made explicit first.

## Direct check of reading 2 (three contiguous blocks, centres −2a, 0, 2a; `window_identity_check.py`; K = 36)
Left side Q[v_out + w] uses the tail blocks, right side λ_a‖v_in − w‖² uses block 0 only (w = v_in − f_ground).
| a | λ_a | Q[v_out + w] | λ_a‖v_in − w‖² | rel. err | Q[Φ]/‖Φ‖² (build residual of the null test) | max_j |Q(Φ, e_j)| | Q[v_out]/‖Φ‖² vs T |
|---:|---:|---:|---:|---:|---:|---:|---|
| 0.35 | 1.194e−3 | 1.1995e−3 | 1.1937e−3 | 0.5 % | 1.2e−4 | 3.8e−5 | 2.37e−2 vs 2.36e−2 |
| 0.40 | 1.816e−4 | 1.847e−4 | 1.816e−4 | 1.7 % | 5.4e−5 | 2.5e−5 | 9.2e−3 vs 9.0e−3 |
| 0.45 | 1.622e−5 | 1.758e−5 | 1.622e−5 | 8 % | 2.0e−5 | 1.5e−5 | 2.9e−3 vs 3.0e−3 |
| 0.50 | 9.38e−7 | 1.43e−6 | 9.38e−7 | 52 % | 6.6e−6 | 8.7e−6 | 7.0e−4 vs 8.5e−4 |
| 0.60 | 1.64e−9 | 3.30e−8 | 1.64e−9 | ×20 | 4.0e−7 | 2.1e−6 | 5.5e−5 vs 4.0e−5 |
Verdict: **ЕСЛИ_A where the build can see it.** The identity holds to 0.5–8 % for a ≤ 0.45 and the error grows exactly
with the ratio (build residual of Q(Φ,·)) / λ_a: the three-block build represents Φ as a null vector of Q only to ~1e−5
(cross-centre archimedean tails beyond XI = 20000 are not corrected; single-block Q is), so below λ ~ 1e−6 the check is
blind, not failed. The T² law itself rests on the single-block eigenvalue, which does not involve Φ and is K-stable.
Q[v_out]/‖Φ‖² ≈ T is confirmed independently (first-order energy of the tail = its mass). Scale of Q: 0.13.

## Direct check, second pass (2026-09-09, after the adjacent-block tail correction in sc_build.py)
The ~1e−5 residual had a cause, and it was ours: for blocks at shift |D| = 2δ the product j_k(ξδ)j_l(ξδ)·e^{iξD} has a
NON-oscillatory tail −½cos((k+l)π/2)/(2ξ²δ²) (and ½sgn(D)sin((k+l)π/2)/(2ξ²δ²) for the imaginary part) beyond XI, of size
≈ 6e−5 at XI = 20000; only the D = 0 tail had been corrected. Fixed in `sc_build.py` (regressions unchanged: set 3 K4
0.9674536916, set 3 K6 0.9663482407; no earlier multi-centre set has adjacent blocks at exactly 2δ, so no earlier number moves).
| a | λ_a | Q[v_out + w] | λ_a‖v_in − w‖² | rel. err | Q[Φ]/‖Φ‖² | max_j |Q(Φ, e_j)| |
|---:|---:|---:|---:|---:|---:|---:|
| 0.50 | 9.3823e−7 | 9.3823e−7 | 9.3823e−7 | 2.0e−10 | −2.4e−16 | 8.3e−16 |
| 0.60 | 1.6398e−9 | 1.6398e−9 | 1.6398e−9 | 3.4e−7 | −1.2e−15 | 3.7e−16 |
| 0.70 | 4.3676e−13 | 4.3822e−13 | 4.3676e−13 | 3.3e−3 | −1.5e−15 | 3.8e−15 |
| 0.75 | 3.87e−15 | 4.48e−15 | 3.87e−15 | 16 % | −7.5e−17 | 1.7e−14 |
Verdict: **ЕСЛИ_A at machine precision.** Φ is a null vector of the discretised Q to 1e−16 (Q(Φ, e_j) = 0 for every window
basis vector — the Legendre closure of Q(Φ,·) = 0 holds numerically), and the identity λ_a = Q[v_out + w]/‖v_in − w‖²
holds to 2e−10 (a = 0.5), 3e−7 (0.6) and 3e−3 (0.7); the ABSOLUTE error is ≈ 1e−15 at every a (roundoff on a form of
scale 0.14), so at a = 0.75, where λ = 3.9e−15, the check reaches its floor (16 %). Raw:
`out/window_identity_K36_corrected_a0.5_0.6.json`, `…_a0.7_0.75.json`. The T² law and the distance reading now stand on two channels.

## Prošhka's verdict (DISTANCE, c71fd48c) and its next_decisive_test D37 — executed 09.09 from the cache alone
Verdict header: OVERALL PARTIAL_WITH_PRECISE_REMAINDER; Q1 PROVED_ON_CLASS (D7–D10: the affine identity holds on the full
ℰ-closure V_a = {f ∈ ℰ : f = 0 a.e. outside (−a,a)}, sharp cuts included, for EVERY radical element); Q2: the literal
«positive Q-distance» reading is dead (D11–D13: the unnormalised infimum is 0 under RH — w = v_in reconstructs Φ — or −∞;
the displayed (D1) with its denominator is the normalised Rayleigh problem, and that is the only surviving object);
projection mechanism dead (D19: Q(h, v_out + w_a) = −λ_a⟨h, v_in − w_a⟩, a constrained eigenproblem); unconditional upper
bound proved only at polynomial×T (D17), the normalised T² rate neither proved nor refuted (D24 is the unpaid inequality:
Schur response); Q3: explicit off-line window a₀(λ) = 1 + 4 log max{1, 3000B/r} with λ_a ≤ −(r/D)e^{δ(a−1)/2} (D25–D33);
D14 finite lower bound on every window (so «−∞ on a finite window» is dead too); D36 unconditional coercivity for 2a < log 2.
Exponent correction D15 accepted (above). Independent check: DISTANCE_INDEPENDENT_CHECK_2026-09-09.md (agent, pending at
time of writing).
D37 (cache-only; input blob 021d8e401d81dec35070bccf0b526d6750a325ed): E = 1 − c², μ⊥ = (R − λ₁c²)/E, H = μ⊥/λ₂.
| a | E | μ⊥ | λ₂ | H | pass |
|---:|---:|---:|---:|---:|---|
| 0.35 | 2.78e−2 | 8.29e−1 | 6.55e−2 | 12.7 | no |
| 0.40 | 2.62e−2 | 3.48e−1 | 1.47e−2 | 23.6 | no |
| 0.45 | 2.20e−2 | 1.31e−1 | 2.41e−3 | 54.3 | no |
| 0.50 | 1.83e−2 | 3.85e−2 | 1.95e−4 | 197 | yes |
| 0.55 | 1.41e−2 | 1.93e−2 | 1.44e−5 | 1341 | yes |
| 0.60 | 1.11e−2 | 4.99e−3 | 6.05e−7 | 8242 | yes |
| 0.65 | 8.58e−3 | 9.78e−4 | 1.88e−8 | 51964 | yes |
| 0.70 | 6.79e−3 | 1.89e−4 | 2.74e−10 | 688124 | yes |
Registered threshold (E > 1e−8, λ₂ > 0, H ≥ 100 at a = 0.60, 0.65, 0.70): **PASSES**, by 2–4 orders. ЕСЛИ_A of the verdict:
the removed correction is high-energy relative to the first excited mode (its Rayleigh value μ⊥ sits 10³–10⁶ above λ₂,
and 10⁶–10⁹ above λ₁); the source-directional Schur response D22–D24 is the next proof target, not the lowest-gap norm.
Observer's reading of the same numbers: μ⊥ ≈ R (the cut-Φ energy is carried almost entirely by the component orthogonal
to the ground), so the ground state absorbs the tail's first-order energy into a direction whose own energy is ~R/E ≈
30·T — the cancellation is between a mass-2 % direction with energy 30T and the tail's energy T; that is the object D24
must bound.

## Schur response (Prošhka D22–D24, his §9(c) ask), evaluated from the saved matrices — 09.09
`schur_response.py` on `out/window_derivative_K36_vec_matrices.npz` (Q, G, eigenpairs, cut-Φ coefficients per a; K = 36). p = v_in/‖v_in‖_G,
complement = G-orthogonal complement of p, r = Q[p], b = Q(·,p), C = Q|complement, y = C⁻¹b, s₀ = r − b*C⁻¹b. Independent of the eigen routine
(Cholesky + QR + solve), the eigenvalue enters only in the secular check.
| a | r = Q[p] | b*C⁻¹b | s₀ = r − b*C⁻¹b | ‖y‖²_G | s₀/(1+‖y‖²) | λ₁ (eig) | min spec C | D23 residual | 1 − b*C⁻¹b/r |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 0.35 | 2.42e−2 | 2.30e−2 | 1.23e−3 | 2.85e−2 | 1.1938e−3 | 1.1937e−3 | 6.55e−2 | 2e−16 | 5.1e−2 |
| 0.50 | 7.04e−4 | 7.03e−4 | 9.56e−7 | 1.86e−2 | 9.3823e−7 | 9.3823e−7 | 1.95e−4 | 1e−16 | 1.4e−3 |
| 0.60 | 5.52e−5 | 5.52e−5 | 1.66e−9 | 1.12e−2 | 1.6398e−9 | 1.6398e−9 | 6.05e−7 | 6e−18 | 3.0e−5 |
| 0.70 | 1.28e−6 | 1.28e−6 | 4.41e−13 | 6.83e−3 | 4.3752e−13 | 4.3676e−13 | 2.74e−10 | 8e−16 | 3.4e−7 |
Findings. (i) C ≻ 0 on every window, min spec C = λ₂ (the complement's bottom is the first excited mode), so C⁻¹ is legitimate and D22 is exact
here. (ii) The Schur trial p − y is an upper bound tight to 4 digits (s₀/(1+‖y‖²) vs λ₁), and the secular equation D23 holds to roundoff. (iii)
The signed cancellation D24: b*C⁻¹b eats r to relative accuracy 1 − b*C⁻¹b/r ≈ λ₁(1+‖y‖²)/r ≈ (λ₁/T)·(T/R) — i.e. exactly the T-scale, since
λ₁ ≍ T² and R ≍ T. The response y has mass ‖y‖² ≈ 1–3 % (= E/(1−E) of D37) and lives above λ₂. So the unpaid inequality D24 is, in these
coordinates, «b*C⁻¹b = r(1 − O(T))» with the O(T) explicit — the numbers say the source pays it; the proof does not exist yet.
